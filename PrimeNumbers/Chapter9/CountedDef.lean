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

/-- Elaborate a call `g a₁ … aₖ`; if its head is a constant `g` with a counted version,
return `g.counted` and the elaborated arguments. -/
private def countedCallee? (call : Syntax) : TermElabM (Expr × Option (Name × Array Expr)) := do
  let e ← elabTerm call none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some c := e.getAppFn.constName? | return (e, none)
  let cc := c ++ `counted
  return (e, if (← getEnv).contains cc then some (cc, e.getAppArgs) else none)

/-- `counted_call% (g a₁ … aₖ)`: the cost of a call — `g.counted a₁ … aₖ` when `g` has a
counted version, otherwise nothing (`pure ()`). -/
syntax (name := countedCall) "counted_call% " term:max : term

@[term_elab countedCall] private def elabCountedCall : TermElab := fun stx ety? => do
  match (← countedCallee? stx[1]).2 with
  | some (cc, args) =>
      let args ← args.mapM fun a => exprToSyntax a
      elabTerm (← `($(mkCIdent cc) $args*)) ety?
  | none => elabTerm (← `(pure ())) ety?

/-- `no_counted% (g a₁ … aₖ)`: the call itself, but an error if `g` has a counted version —
used for calls under a binder, whose cost cannot be charged in place. -/
syntax (name := noCounted) "no_counted% " term:max : term

@[term_elab noCounted] private def elabNoCounted : TermElab := fun stx ety? => do
  let call := stx[1]
  let (e, cc?) ← countedCallee? call
  if let some (cc, _) := cc? then
    throwErrorAt call "counted_def: the call of `{cc.getPrefix}` inside a nested binding \
      form (`fun`, `match`, `if` inside an expression, …) cannot be counted in place; lift \
      it to the top level of a branch"
  if let some ety := ety? then discard <| isDefEq (← inferType e) ety
  return e

/-- `charge% (a ∘ b)`: the charge for one primitive operation, on its operands *as
elaborated* (so with any coercions inserted): `chargeMul a b` for `a * b`, `chargeMod a b`
for `a % b` and `a / b`, `chargeMod b a` for `a ∣ b`. -/
syntax (name := chargeOp) "charge% " term:max : term

@[term_elab chargeOp] private def elabChargeOp : TermElab := fun stx ety? => do
  let e ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let args := e.getAppArgs
  let (prim, x, y) ← match e.getAppFn.constName?, args.size with
    | some ``HMul.hMul, 6 => pure (``NatArith.chargeMul, args[4]!, args[5]!)
    | some ``HMod.hMod, 6 => pure (``NatArith.chargeMod, args[4]!, args[5]!)
    | some ``HDiv.hDiv, 6 => pure (``NatArith.chargeMod, args[4]!, args[5]!)
    | some ``Dvd.dvd, 4 => pure (``NatArith.chargeMod, args[3]!, args[2]!)
    | _, _ => throwErrorAt stx[1] "counted_def: cannot charge {e}"
  elabTerm (← `($(mkCIdent prim) $(← exprToSyntax x) $(← exprToSyntax y))) ety?

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
  | `($a ^ $k) => !(isNumLit a && isNumLit k) || hasCharged a || hasCharged k
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
        modify (·.push (none, ← `(charge% ($(⟨ra⟩) * $(⟨rb⟩)))))
      `($(⟨ra⟩) * $(⟨rb⟩))
  | `($a % $b) =>
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨b⟩ do
        modify (·.push (none, ← `(charge% ($(⟨ra⟩) % $(⟨rb⟩)))))
      `($(⟨ra⟩) % $(⟨rb⟩))
  | `($a / $b) =>
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨b⟩ do
        modify (·.push (none, ← `(charge% ($(⟨ra⟩) / $(⟨rb⟩)))))
      `($(⟨ra⟩) / $(⟨rb⟩))
  | `($a ^ $k) =>
      let ra ← hoist self a; let rk ← hoist self k
      match k.raw.isNatLit? with
      | some n => unless isNumLit a do
          -- `a ^ n` is computed as `((a * a) * a) ⋯`: charge each product
          for i in [1:n] do
            let lit := Syntax.mkNumLit (toString i)
            modify (·.push (none, ← `(charge% ($(⟨ra⟩) ^ $lit * $(⟨ra⟩)))))
      | none =>
          unless a.raw.isNatLit? == some 2 do
            Macro.throwErrorAt e "counted_def: a power with a variable exponent is not a \
              primitive operation; compute it with a counted function such as `powMod`"
      `($(⟨ra⟩) ^ $(⟨rk⟩))
  | `($a ∣ $b) =>
      -- a divisibility test computes `b mod a`
      let ra ← hoist self a; let rb ← hoist self b
      unless isNumLit ⟨a⟩ do
        modify (·.push (none, ← `(charge% ($(⟨ra⟩) ∣ $(⟨rb⟩)))))
      `($(⟨ra⟩) ∣ $(⟨rb⟩))
  | `($f:ident $args*) =>
      if f.getId == self then
        let args' ← args.mapM fun a => do return (⟨← hoist self a.raw⟩ : Term)
        -- charge the recursive call by running its counted version; its *value* is the plain
        -- call, so the counted and plain versions agree by unfolding once
        modify (·.push (none, ← `($(mkIdent (self ++ `counted)) $args'*)))
        `($f $args'*)
      else
        -- a call of another function: charge its counted version, if it has one
        let args' ← args.mapM fun a => do return (⟨← hoist self a.raw⟩ : Term)
        let call ← `($f $args'*)
        modify (·.push (none, ← `(counted_call% ($call))))
        return call
  | _ =>
      if isBinding e then
        if hasCharged e || mentions self e then
          Macro.throwErrorAt e "counted_def: arithmetic or a recursive call inside a nested \
            binding form (`fun`, `match`, `let`, `if`, … inside an expression) cannot be \
            counted in place; lift it to the top level of a branch"
        return ← guardCalls e
      generic e
where
  generic (e : Syntax) : StateT (Array (Option Ident × Term)) MacroM Syntax :=
    match e with
    | .node info kind args => do return .node info kind (← args.mapM (hoist self))
    | _ => pure e
  /-- Under a binder nothing is hoisted; calls are checked not to need counting. -/
  guardCalls (e : Syntax) : StateT (Array (Option Ident × Term)) MacroM Syntax := do
    if let `($f:ident $args*) := e then
      let args' ← args.mapM fun a => do return (⟨← guardCalls a.raw⟩ : Term)
      return ← `(no_counted% ($f $args'*))
    match e with
    | .node info kind args => return .node info kind (← args.mapM guardCalls)
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
      repeat' (first | split_ifs | split | cost_simp))
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
    -- peel `A → B` and named `(x y : A) → B` arrows; named arguments keep their names
    let mut args : Array (Option Ident × Term) := #[]
    let mut res : Term := ty
    while args.size < ncols do
      match res with
      | `(($xs:ident* : $a) → $b) => args := args ++ xs.map (fun x => (some x, a)); res := b
      | `($a → $b) => args := args.push (none, a); res := b
      | _ => Macro.throwErrorAt ty "counted_def: the type must have one arrow per pattern column"
    if args.size != ncols then
      Macro.throwErrorAt ty "counted_def: the type must have one arrow per pattern column"
    let mut newBs := bs
    let mut discrs : Array Term := #[]
    for h : i in [0:args.size] do
      let (x?, a) := args[i]
      let x ← match x? with
        | some x => pure x
        | none => pure (mkIdent (← Macro.addMacroScope (Name.mkSimple s!"eqnArg{i}")))
      newBs := newBs.push (← `(bracketedBinder| ($x : $a)))
      discrs := discrs.push x
    let altsArr : Array (TSyntax ``Lean.Parser.Term.matchAlt) := altArr.map (⟨·⟩)
    let ds ← discrs.mapM fun x => `(Lean.Parser.Term.matchDiscr| $x:term)
    let body ← `(match $[$ds],* with $altsArr:matchAlt*)
    expandCounted doc? f newBs res body suff

end PrimeNumbers.Chapter9
