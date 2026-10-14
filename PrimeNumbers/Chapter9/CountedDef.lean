import PrimeNumbers.Chapter9.Counted

/-!
# `counted_def`: write an algorithm once, in plain Lean

```
counted_def powMod (x n m : ℕ) : ℕ :=
  if n = 0 then 1 % m
  else if n % 2 = 0 then
    let y := powMod x (n / 2) m
    y * y % m
  else …
termination_by n
```

From this one body the command produces

* `powMod` — the plain definition, exactly as written (so existing proofs are unaffected);
* `powMod.counted` — the same body run in the counting monad: before each operation is
  used, a charge is recorded for every `a * b` and `a % b` (on its plain operands, in
  evaluation order — including inside `if` conditions and `let` values), and every
  recursive call is charged by running `powMod.counted` on the same arguments.  All values,
  conditions and termination measures are the original plain expressions;
* `powMod.counted_val : CostM.val C (powMod.counted …) = powMod …`, proved automatically.

Multiplication or remainder by a numeric literal (`n % 2`, `2 * k`) is a shift or mask and
is not charged; `/` is allowed only by a literal.  Arithmetic or recursive calls inside a
nested binding form (`fun`, `match`, an `if` inside an expression, …) cannot be charged in
place and are rejected with an error asking to lift them to the top level of a branch — so
nothing can be silently left out of the count.

Running-time theorems are proved about `CostM.cost C (f.counted …)`; `cost_simp` unfolds
the bookkeeping.
-/

namespace PrimeNumbers.Chapter9

open Lean Elab Command Term Meta

/-- Is `t` a numeric literal? -/
private def isNumLit (t : Term) : Bool := t.raw.isNatLit?.isSome

/-- Does the syntax contain a charged operator (`*` or `%` not by a literal, or `/` at all
except by a literal)? -/
private partial def hasCharged (stx : Syntax) : Bool :=
  match stx with
  | `($a * $b) | `($a % $b) =>
      !(isNumLit a || isNumLit b) || hasCharged a || hasCharged b
  | `($a / $b) => !isNumLit b || hasCharged a || hasCharged b
  | `($a ∣ $b) => !isNumLit a || hasCharged a || hasCharged b
  | _ => stx.getArgs.any hasCharged

/-- Does the syntax mention the identifier `self` (a recursive call)? -/
private partial def mentions (self : Name) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId == self) || stx.getArgs.any (mentions self)

/-- Binding forms: arithmetic under them cannot be evaluated outside them. -/
private def isBinding (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.fun || stx.isOfKind ``Lean.Parser.Term.match ||
    stx.isOfKind ``Lean.Parser.Term.let || stx.isOfKind ``Lean.Parser.Term.have ||
    stx.isOfKind ``Lean.Parser.Term.do || stx.isOfKind ``termDepIfThenElse ||
    stx.isOfKind ``termIfThenElse

/-- **Charging.**  Walk an expression in evaluation order (innermost first, left to right).
Every charged operation records a charge (`NatArith.chargeMul` / `chargeMod`) on its plain
operands; every recursive call is bound to a fresh variable.  The residual expression is
the original one with the recursive calls replaced by those variables — so values, `if`
conditions and termination measures stay the original plain expressions. -/
private partial def hoist (self : Name) (e : Syntax) :
    StateT (Array (Option Ident × Term)) MacroM Syntax := do
  match e with
  | `($a * $b) =>
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨a⟩ || isNumLit ⟨b⟩ do
        modify (·.push (none, ← `(NatArith.chargeMul $(⟨ra⟩) $(⟨rb⟩))))
      `($(⟨ra⟩) * $(⟨rb⟩))
  | `($a % $b) =>
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨b⟩ do
        modify (·.push (none, ← `(NatArith.chargeMod $(⟨ra⟩) $(⟨rb⟩))))
      `($(⟨ra⟩) % $(⟨rb⟩))
  | `($a / $b) =>
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨b⟩ do
        modify (·.push (none, ← `(NatArith.chargeMod $(⟨ra⟩) $(⟨rb⟩))))
      `($(⟨ra⟩) / $(⟨rb⟩))
  | `($a ∣ $b) =>
      -- a divisibility test computes `b mod a`
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨a⟩ do
        modify (·.push (none, ← `(NatArith.chargeMod $(⟨rb⟩) $(⟨ra⟩))))
      `($(⟨ra⟩) ∣ $(⟨rb⟩))
  | `($f:ident $args*) =>
      if f.getId == self then
        let args' ← args.mapM fun a => do return (⟨← hoist self a.raw⟩ : Term)
        -- charge the recursive call by running its counted version; its *value* is the plain
        -- call, so the counted and plain versions agree by unfolding once
        modify (·.push (none, ← `($(mkIdent (self ++ `counted)) $args'*)))
        `($f $args'*)
      else generic e
  | _ =>
      if isBinding e && (hasCharged e || mentions self e) then
        Macro.throwErrorAt e "counted_def: arithmetic or a recursive call inside a nested \
          binding form (`fun`, `match`, `let`, `if`, … inside an expression) cannot be \
          counted in place; lift it to the top level of a branch"
      generic e
where
  generic (e : Syntax) : StateT (Array (Option Ident × Term)) MacroM Syntax :=
    match e with
    | .node info kind args => do return .node info kind (← args.mapM (hoist self))
    | _ => pure e

/-- Put the recorded charges and recursive calls in front of `body`, in order. -/
private def wrap (binds : Array (Option Ident × Term)) (body : Term) : MacroM Term := do
  let mut r := body
  for (x?, comp) in binds.reverse do
    r ← match x? with
      | some x => `(bind $comp fun $x => $r)
      | none => `(bind $comp fun _ => $r)
  return r

/-- Translate a plain function body into a computation in the counting monad.  At the top
level of each branch, `if` and `let` structure the computation; every charged operation and
recursive call in an expression (including in `if` conditions and `let` values) is
evaluated, left to right, before it is used. -/
private partial def translate (self : Name) (e : Term) : MacroM Term := do
  -- `match d₁, …, dₖ with | pats => rhs | …`: charge the discriminants, translate each rhs
  -- (node layout: "match" generalizing? motive? discriminants "with" matchAlts)
  if e.raw.isOfKind ``Lean.Parser.Term.match then
    let (discrs', binds) ← (hoist self e.raw[3]).run #[]
    let alts := e.raw[5][0].getArgs
    let alts' ← alts.mapM fun alt => do
      return alt.setArg 3 (← translate self ⟨alt[3]⟩)
    let m := (e.raw.setArg 3 discrs').setArg 5 (e.raw[5].setArg 0 (mkNullNode alts'))
    return ← wrap binds ⟨m⟩
  match e with
  | `(($e)) => translate self e
  | `(if $c then $a else $b) => do
      let (c', binds) ← (hoist self c).run #[]
      let ta ← translate self a
      let tb ← translate self b
      wrap binds (← `(if $(⟨c'⟩) then $ta else $tb))
  | `(let $x:ident := $v; $b) => do
      let (v', binds) ← (hoist self v).run #[]
      let tb ← translate self b
      wrap binds (← `(let $x := $(⟨v'⟩); $tb))
  | _ => do
      let (r, binds) ← (hoist self e).run #[]
      wrap binds (← `(pure $(⟨r⟩)))

/-- Generate the plain definition, the counted one and the value lemma. -/
private def expandCounted (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (f : Ident) (bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (suff : TSyntax ``Lean.Parser.Termination.suffix) : MacroM Syntax := do
  let counted := mkIdent (f.getId ++ `counted)
  let tbody ← translate f.getId body
  let mut args : Array Ident := #[]
  for b in bs do
    match b with
    | `(bracketedBinder| ($xs:ident* : $_)) => args := args ++ xs
    | _ => Macro.throwErrorAt b "counted_def: use explicit binders `(x y : ℕ)`"
  let mo := mkIdent `countedMonad
  let c₁ ← `(command| $[$doc?:docComment]?
    def $f $bs* : $ty := $body
    $suff:suffix)
  let c₂ ← `(command| $[$doc?:docComment]?
    def $counted {$mo : Type → Type} [Monad $mo] [NatArith $mo] $bs* : $mo $ty := $tbody
    $suff:suffix)
  let valName := mkIdent (f.getId ++ `counted_val)
  let fCall := Syntax.mkApp f (args.map fun a => ⟨a.raw⟩)
  let cCall := Syntax.mkApp counted (args.map fun a => ⟨a.raw⟩)
  let eqDef := mkIdent (f.getId ++ `eq_def)
  let ceqDef := mkIdent (f.getId ++ `counted ++ `eq_def)
  let c₃ ← `(command|
    /-- Counting does not change the value. -/
    theorem $valName (C : CostModel) $bs* : CostM.val C $cCall = $fCall := by
      rw [$ceqDef:ident]; conv_rhs => rw [$eqDef:ident]
      repeat' (first | split_ifs | split) <;> cost_simp)
  return mkNullNode #[c₁, c₂, c₃]

/-- `counted_def f binders : τ := body [termination_by …] [decreasing_by …]` -/
syntax (name := countedDef) (docComment)? "counted_def " ident bracketedBinder* " : " term
  " := " term Lean.Parser.Termination.suffix : command

/-- `counted_def f binders : A₁ → ⋯ → τ | pats => rhs | …` (equation style) -/
syntax (name := countedDefEqns) (docComment)? "counted_def " ident bracketedBinder* " : " term
  Lean.Parser.Command.declValEqns : command

macro_rules
  | `($[$doc?:docComment]? counted_def $f:ident $bs:bracketedBinder* : $ty := $body
      $suff:suffix) => expandCounted doc? f bs ty body suff

macro_rules
  | `($[$doc?:docComment]? counted_def $f:ident $bs:bracketedBinder* : $ty
      $eqns:declValEqns) => do
    -- `declValEqns` is `matchAlts terminationSuffix whereDecls?`
    let alts := eqns.raw[0][0]
    let suff : TSyntax ``Lean.Parser.Termination.suffix := ⟨eqns.raw[0][1]⟩
    -- the number of pattern columns, and the types they range over
    let altArr := alts[0].getArgs
    let some alt₀ := altArr[0]? | Macro.throwError "counted_def: no equations"
    let ncols := alt₀[1][0].getSepArgs.size
    let mut argTys : Array Term := #[]
    let mut res : Term := ty
    for _ in [0:ncols] do
      match res with
      | `($a → $b) => argTys := argTys.push a; res := b
      | _ => Macro.throwErrorAt ty "counted_def: the type must have one arrow per pattern column"
    let mut newBs := bs
    let mut discrs : Array Term := #[]
    for h : i in [0:argTys.size] do
      let x := mkIdent (← Macro.addMacroScope (Name.mkSimple s!"eqnArg{i}"))
      newBs := newBs.push (← `(bracketedBinder| ($x : $(argTys[i]))))
      discrs := discrs.push x
    let altsArr : Array (TSyntax ``Lean.Parser.Term.matchAlt) := altArr.map (⟨·⟩)
    let ds ← discrs.mapM fun x => `(Lean.Parser.Term.matchDiscr| $x:term)
    let body ← `(match $[$ds],* with $altsArr:matchAlt*)
    expandCounted doc? f newBs res body suff

end PrimeNumbers.Chapter9
