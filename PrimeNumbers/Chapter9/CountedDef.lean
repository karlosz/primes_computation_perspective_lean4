import PrimeNumbers.Chapter9.Counted

/-!
# `counted_def`: write an algorithm once, in plain Lean

```
counted_def powMod (x n M : ℕ) : ℕ :=
  if n = 0 then 1 % M
  else if n % 2 = 0 then
    let y := powMod x (n / 2) M
    y * y % M
  else …
termination_by n
```

The command elaborates **two** definitions from this one body:

* `powMod.counted : ∀ {m} [Monad m] [NatArith m], … → m ℕ` — the body translated
  mechanically: every `a * b` and `a % b` becomes a charged primitive (`NatArith.mul`,
  `NatArith.mod`), every recursive call becomes a call of `powMod.counted`, and the
  evaluation order of the original expression is kept;
* `powMod : … → ℕ := Id.run (powMod.counted …)` — the plain executable function.

Nothing has to be kept in sync by hand, and nothing can be forgotten:

* **every** `*` and `%` in the body is charged, except multiplication or remainder by a
  numeric literal (`n % 2`, `2 * k`), which is a shift or mask and costs linear time;
* `/` is allowed only by a numeric literal (a shift);
* any construct the translation does not understand (`match`, `fun`, `do`, …) that
  contains arithmetic is **rejected with an error**, so arithmetic can never be hidden
  from the count;
* conditions of `if` may only contain uncharged operations (they are evaluated plainly);
  a charged operation in a condition is rejected.

Running-time theorems are stated about `CostM.cost C (f.counted …)`;
`CostM.val C (f.counted …) = f …` is proved once per algorithm (see `Chapter2.powMod'`).
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
  | `($a / $b) => !isNumLit b || hasCharged a
  | _ => stx.getArgs.any hasCharged

/-- Does the syntax mention the identifier `self` (a recursive call)? -/
private partial def mentions (self : Name) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId == self) || stx.getArgs.any (mentions self)

/-- Translate a plain term into a computation in the counting monad.  `self` is the name of
the function being defined (its recursive calls go to `self.counted`). -/
private partial def translate (self : Name) (e : Term) : MacroM Term := do
  -- fast path: a subterm with no charged operation and no recursive call is a plain value
  if !hasCharged e && !mentions self e then return ← `(pure $e)
  match e with
  | `(($e)) => translate self e
  | `(if $c then $a else $b) => do
      if hasCharged c then
        Macro.throwErrorAt c "counted_def: a charged operation (`*`, `%`, `/`) inside an \
          `if` condition is not counted; bind it with `let` before the `if`"
      let ta ← translate self a
      let tb ← translate self b
      `(if $c then $ta else $tb)
  | `(let $x:ident := $v; $b) => do
      `(bind $(← translate self v) fun $x => $(← translate self b))
  | `($a * $b) =>
      if isNumLit a || isNumLit b then pureOp e a b fun x y => `($x * $y)
      else binop a b fun x y => `(NatArith.mul $x $y)
  | `($a % $b) =>
      if isNumLit b then pureOp e a b fun x y => `($x % $y)
      else binop a b fun x y => `(NatArith.mod $x $y)
  | `($a / $b) =>
      if isNumLit b then pureOp e a b fun x y => `($x / $y)
      else Macro.throwErrorAt e "counted_def: division is only allowed by a numeric literal"
  | `($a + $b) => pureOp e a b fun x y => `($x + $y)
  | `($a - $b) => pureOp e a b fun x y => `($x - $y)
  | `($f:ident $args*) => do
      -- arguments with charged operations or recursive calls are evaluated first (left to
      -- right) and bound to fresh names; other arguments are passed as they are, which also
      -- keeps termination proofs about them intact
      let mut binds : Array (Term × Ident) := #[]
      let mut callArgs : Array Term := #[]
      for h : i in [0:args.size] do
        let a : Term := ⟨args[i].raw⟩
        if hasCharged a || mentions self a then
          let x := mkIdent (← Macro.addMacroScope (Name.mkSimple s!"arg{i}"))
          binds := binds.push (a, x)
          callArgs := callArgs.push x
        else
          callArgs := callArgs.push a
      let mut body ← if f.getId == self then
          `($(mkIdent (self ++ `counted)) $callArgs*)
        else `(pure ($f $callArgs*))
      for (a, x) in binds.reverse do
        body ← `(bind $(← translate self a) fun $x => $body)
      pure body
  | _ =>
      if hasCharged e then
        Macro.throwErrorAt e "counted_def: this construct is not supported by the cost \
          translation and contains arithmetic; rewrite it with `if`/`let`"
      `(pure $e)
where
  /-- A charged binary operation: evaluate `a`, then `b`, then the primitive. -/
  binop (a b : Term) (k : Term → Term → MacroM Term) : MacroM Term := do
    let x := mkIdent (← Macro.addMacroScope `x)
    let y := mkIdent (← Macro.addMacroScope `y)
    `(bind $(← translate self a) fun $x => bind $(← translate self b) fun $y => $(← k x y))
  /-- An uncharged binary operation on the values of `a` and `b`. -/
  pureOp (_e a b : Term) (k : Term → Term → MacroM Term) : MacroM Term := do
    let x := mkIdent (← Macro.addMacroScope `x)
    let y := mkIdent (← Macro.addMacroScope `y)
    `(bind $(← translate self a) fun $x => bind $(← translate self b) fun $y =>
        pure $(← k x y))

/-- `counted_def f binders : τ := body [termination_by …] [decreasing_by …]` -/
syntax (name := countedDef) (docComment)? "counted_def " ident bracketedBinder* " : " term
  " := " term Lean.Parser.Termination.suffix : command

macro_rules
  | `($[$doc?:docComment]? counted_def $f:ident $bs:bracketedBinder* : $ty := $body
      $suff:suffix) => do
    let counted := mkIdent (f.getId ++ `counted)
    let tbody ← translate f.getId body
    let mut args : Array Ident := #[]
    for b in bs do
      match b with
      | `(bracketedBinder| ($xs:ident* : $_)) => args := args ++ xs
      | _ => Macro.throwErrorAt b "counted_def: use explicit binders `(x y : ℕ)`"
    let mo := mkIdent `countedMonad
    let c₁ ← `(command| $[$doc?:docComment]?
      def $counted {$mo : Type → Type} [Monad $mo] [NatArith $mo] $bs* : $mo $ty := $tbody
      $suff:suffix)
    let callId ← `($counted (countedMonad := Id))
    let call := Syntax.mkApp callId (args.map fun a => ⟨a.raw⟩)
    let c₂ ← `(command| $[$doc?:docComment]?
      def $f $bs* : $ty := Id.run $call)
    return mkNullNode #[c₁, c₂]

end PrimeNumbers.Chapter9
