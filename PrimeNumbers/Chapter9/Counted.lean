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

/-- The cost of multiplying two values of type `α` (for residues: including the reduction). -/
class MulCost (α : Type) where
  /-- bit operations to multiply `a` and `b` under the cost model `C` -/
  mulCost : CostModel → α → α → ℕ

/-- The cost of a division with remainder on values of type `α`. -/
class DivCost (α : Type) where
  /-- bit operations to divide `a` by `b` with remainder under the cost model `C` -/
  divCost : CostModel → α → α → ℕ

instance : MulCost ℕ := ⟨fun C a b => C.mul a.size b.size⟩
instance : DivCost ℕ := ⟨fun C a b => C.divMod a.size b.size⟩
/-- Integers are multiplied and divided as their absolute values (signs are free). -/
instance : MulCost ℤ := ⟨fun C a b => C.mul a.natAbs.size b.natAbs.size⟩
instance : DivCost ℤ := ⟨fun C a b => C.divMod a.natAbs.size b.natAbs.size⟩
/-- A product of residues modulo `n`: a multiplication of two numbers `< n` and a reduction.
(There is no `DivCost (ZMod n)`: division of residues is an inversion, which must be written
out — e.g. with `modInv` — so that it is charged.) -/
instance (n : ℕ) : MulCost (ZMod n) := ⟨fun C _ _ => C.mulMod n.size⟩

/-- The big-number primitives an algorithm may use: charges for a multiplication and for a
division with remainder.  Everything else (comparisons, additions, shifts) is free, as in
the cost model. -/
class NatArith (m : Type → Type) where
  /-- record the cost of multiplying `a` and `b` -/
  chargeMul {α : Type} [MulCost α] : α → α → m Unit
  /-- record the cost of dividing `a` by `b` with remainder -/
  chargeMod {α : Type} [DivCost α] : α → α → m Unit

/-- Plain execution. -/
instance : NatArith Id where
  chargeMul _ _ := pure ()
  chargeMod _ _ := pure ()

/-- Counted execution under the cost model `C`. -/
def CostM (_C : CostModel) (α : Type) : Type := Counted α

instance (C : CostModel) : Monad (CostM C) := inferInstanceAs (Monad Counted)

instance (C : CostModel) : NatArith (CostM C) where
  chargeMul a b := (⟨(), MulCost.mulCost C a b⟩ : Counted Unit)
  chargeMod a b := (⟨(), DivCost.divCost C a b⟩ : Counted Unit)

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
@[simp] theorem CostM.chargeMul_cost {α} [MulCost α] (a b : α) :
    CostM.cost C (NatArith.chargeMul a b) = MulCost.mulCost C a b := rfl
@[simp] theorem CostM.chargeMod_cost {α} [DivCost α] (a b : α) :
    CostM.cost C (NatArith.chargeMod a b) = DivCost.divCost C a b := rfl
@[simp] theorem mulCost_nat (a b : ℕ) : MulCost.mulCost C a b = C.mul a.size b.size := rfl
@[simp] theorem divCost_nat (a b : ℕ) : DivCost.divCost C a b = C.divMod a.size b.size := rfl
@[simp] theorem mulCost_int (a b : ℤ) :
    MulCost.mulCost C a b = C.mul a.natAbs.size b.natAbs.size := rfl
@[simp] theorem divCost_int (a b : ℤ) :
    DivCost.divCost C a b = C.divMod a.natAbs.size b.natAbs.size := rfl
@[simp] theorem mulCost_zmod {n : ℕ} (a b : ZMod n) : MulCost.mulCost C a b = C.mulMod n.size :=
  rfl

end

/-- Unfold the bookkeeping of a counted computation: what is left is its result and the
sum of the charges of its primitive calls. -/
macro "cost_simp" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in
    simp only [CostM.bind_cost, CostM.bind_val, CostM.pure_cost, CostM.pure_val,
      CostM.chargeMul_cost, CostM.chargeMod_cost, mulCost_nat, divCost_nat, mulCost_int,
      divCost_int, mulCost_zmod, zero_add, add_zero] at *))

theorem ite_of_pos {α} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]
theorem ite_of_neg {α} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- `cost_unfold f.counted`: unfold a counted algorithm one step, take the branches its
conditions select (decided from the hypotheses, by `assumption` or `omega`), and unfold the
bookkeeping. -/
macro "cost_unfold " ids:ident,+ : tactic => `(tactic|
  (rw [$[$ids:ident],*]
   try (set_option linter.unusedSimpArgs false in
    simp (disch := first | assumption | omega) only [ite_of_pos, ite_of_neg, CostM.bind_cost,
      CostM.bind_val, CostM.pure_cost, CostM.pure_val, CostM.chargeMul_cost,
      CostM.chargeMod_cost, mulCost_nat, divCost_nat, mulCost_int, divCost_int, mulCost_zmod,
      zero_add, add_zero])))

end PrimeNumbers.Chapter9
