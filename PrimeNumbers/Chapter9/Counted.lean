import PrimeNumbers.Chapter9.BitCost

/-!
# Costs derived from the code: algorithms written once, run plain or counted

Instead of writing a separate cost function next to each algorithm (which has to be kept in
sync by hand), an algorithm is written **once**, generically over a monad `m` that supplies
the big-number primitives (`NatArith`):

* run in `Id`, it is the ordinary executable algorithm (no overhead);
* run in `CostM C`, the very same code returns its result *and* the number of bit
  operations it performed under the cost model `C` — every primitive call is charged at
  the bit lengths of its actual operands.

So a running-time theorem is a statement about `(alg (m := CostM C) …).cost`, and the cost
cannot drift away from the algorithm.  A per-algorithm lemma `(alg (m := CostM C) …).val =
alg (m := Id) …` (proved once, by unfolding) says counting does not change the answer.

This file is the framework; it depends only on the cost model.  Algorithms are not written
against it by hand: the `counted_def` command (`CountedDef.lean`) generates the counted
version from plain code.
-/

namespace PrimeNumbers.Chapter9

/-- A value together with a cost. -/
@[ext]
structure Counted (α : Type*) where
  /-- the result -/
  val : α
  /-- the cost of computing it -/
  cost : ℕ

instance : Monad Counted where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

@[simp] theorem Counted.pure_val {α} (a : α) : (pure a : Counted α).val = a := rfl
@[simp] theorem Counted.pure_cost {α} (a : α) : (pure a : Counted α).cost = 0 := rfl
@[simp] theorem Counted.bind_val {α β} (x : Counted α) (f : α → Counted β) :
    (x >>= f).val = (f x.val).val := rfl
@[simp] theorem Counted.bind_cost {α β} (x : Counted α) (f : α → Counted β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl

/-- The big-number primitives an algorithm may use.  Everything else (comparisons,
additions, shifts) is free, as in the cost model. -/
class NatArith (m : Type → Type) where
  /-- multiplication -/
  mul : ℕ → ℕ → m ℕ
  /-- remainder -/
  mod : ℕ → ℕ → m ℕ

/-- Plain execution. -/
instance : NatArith Id where
  mul a b := pure (a * b)
  mod a b := pure (a % b)

/-- Counted execution under the cost model `C`. -/
def CostM (_C : CostModel) (α : Type) : Type := Counted α

instance (C : CostModel) : Monad (CostM C) := inferInstanceAs (Monad Counted)

instance (C : CostModel) : NatArith (CostM C) where
  mul a b := (⟨a * b, C.mul a.size b.size⟩ : Counted ℕ)
  mod a b := (⟨a % b, C.divMod a.size b.size⟩ : Counted ℕ)

section
variable (C : CostModel)

/-- Run a counted computation: its result. -/
def CostM.val {α} (x : CostM C α) : α := Counted.val x
/-- Run a counted computation: its cost. -/
def CostM.cost {α} (x : CostM C α) : ℕ := Counted.cost x

@[simp] theorem CostM.pure_val {α} (a : α) : CostM.val C (pure a) = a := rfl
@[simp] theorem CostM.pure_cost {α} (a : α) : CostM.cost C (pure a) = 0 := rfl
@[simp] theorem CostM.bind_val {α β} (x : CostM C α) (f : α → CostM C β) :
    CostM.val C (x >>= f) = CostM.val C (f (CostM.val C x)) := rfl
@[simp] theorem CostM.bind_cost {α β} (x : CostM C α) (f : α → CostM C β) :
    CostM.cost C (x >>= f) = CostM.cost C x + CostM.cost C (f (CostM.val C x)) := rfl
@[simp] theorem CostM.mul_val (a b : ℕ) : CostM.val C (NatArith.mul a b) = a * b := rfl
@[simp] theorem CostM.mul_cost (a b : ℕ) :
    CostM.cost C (NatArith.mul a b) = C.mul a.size b.size := rfl
@[simp] theorem CostM.mod_val (a b : ℕ) : CostM.val C (NatArith.mod a b) = a % b := rfl
@[simp] theorem CostM.mod_cost (a b : ℕ) :
    CostM.cost C (NatArith.mod a b) = C.divMod a.size b.size := rfl

end

/-- Unfold the bookkeeping of a counted computation: what is left is its result and the
sum of the charges of its primitive calls. -/
macro "cost_simp" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in
    simp only [CostM.bind_cost, CostM.bind_val, CostM.pure_cost, CostM.pure_val, CostM.mul_cost,
      CostM.mul_val, CostM.mod_cost, CostM.mod_val, zero_add, add_zero] at *))

end PrimeNumbers.Chapter9
