import Mathlib.Tactic.Basic

/-!
# The lemma sets of the cost tactics

* `@[cost_simps]`: the bookkeeping lemmas of counted computations (`Counted.lean`); the
  `cost_simp` and `cost_unfold` tactics simplify with exactly this set.
* `@[cost_le]`: bounds `costOf C (g …) ≤ B` on the cost of a call (the running time of an
  algorithm), or `h … ≤ B` on another cost (`gcdCost school k ≤ …`); `cost_bound`
  instantiates them at the costs of the goal.
* `@[val_le]`: bounds `g … < B` or `g … ≤ B` on the value of a function (a residue below its
  modulus, `rhoF n a x < n`); `cost_bound` uses them for the bit lengths of operands and for
  the hypotheses of the cost lemmas.

The last two are indexed by the head constant of the bounded term (for a call, its counted
version `g.counted`).  (An attribute must be declared in a file before the one that first
uses it.)
-/

register_simp_attr cost_simps

namespace PrimeNumbers.Chapter9

open Lean Meta

/-- The conclusion `l ≤ r` or `l < r` of a lemma, after its hypotheses. -/
def lemmaConcl? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let (_, _, concl) ← forallMetaTelescopeReducing ty
  let concl ← instantiateMVars concl
  match_expr concl with
  | LE.le _ _ l r => return some (l, r)
  | LT.lt _ _ l r => return some (l, r)
  | _ => return none

/-- The key of a cost: the callee `g.counted` of `CostM.cost C α (g.counted …)`, or the head
`h` of another cost `h …` (e.g. `gcdCost C k`). -/
def costKey? (l : Expr) : Option Name :=
  if l.isAppOfArity `PrimeNumbers.Chapter9.CostM.cost 3 then l.appArg!.getAppFn.constName?
  else l.getAppFn.constName?

/-- The key of the cost that a lemma bounds. -/
def costLemmaKey? (ty : Expr) : MetaM (Option Name) := do
  let some (l, _) ← lemmaConcl? ty | return none
  return costKey? l

/-- The head of the term `g …` whose value a lemma bounds. -/
def valLemmaKey? (ty : Expr) : MetaM (Option Name) := do
  let some (l, _) ← lemmaConcl? ty | return none
  return l.getAppFn.constName?

/-- Lemmas indexed by a head constant. -/
abbrev LemmaIndex := NameMap (Array Name)

def LemmaIndex.addEntry (m : LemmaIndex) (e : Name × Name) : LemmaIndex :=
  m.insert e.1 (((m.get? e.1).getD #[]).push e.2)

def LemmaIndex.find (m : LemmaIndex) (k : Name) : Array Name := (m.get? k).getD #[]

initialize costLeExt : SimpleScopedEnvExtension (Name × Name) LemmaIndex ←
  registerSimpleScopedEnvExtension { addEntry := LemmaIndex.addEntry, initial := {} }

initialize valLeExt : SimpleScopedEnvExtension (Name × Name) LemmaIndex ←
  registerSimpleScopedEnvExtension { addEntry := LemmaIndex.addEntry, initial := {} }

initialize registerBuiltinAttribute {
  name := `cost_le
  descr := "a bound on the cost of a call, instantiated by `cost_bound`"
  add := fun decl _ kind => MetaM.run' do
    let some k ← costLemmaKey? (← getConstVal decl).type
      | throwError "@[cost_le]: `{decl}` does not conclude `costOf C (f …) ≤ B`"
    costLeExt.add (k, decl) kind
}

initialize registerBuiltinAttribute {
  name := `val_le
  descr := "a bound on the value of a function, used by `cost_bound` for bit lengths"
  add := fun decl _ kind => MetaM.run' do
    let some k ← valLemmaKey? (← getConstVal decl).type
      | throwError "@[val_le]: `{decl}` does not conclude `f … < B` or `f … ≤ B`"
    valLeExt.add (k, decl) kind
}

end PrimeNumbers.Chapter9
