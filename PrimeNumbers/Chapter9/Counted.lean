import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter9.CostAttr

/-!
# Costs derived from the code: the counting monad

An algorithm is written once, as plain code, with `counted_def` (`CountedDef.lean`), which
also produces a *counted* version of it: the same computation, run in a monad with the
primitives of `NatArith` — charges for a multiplication, a division with remainder, a power
and a number of plain bit operations.  Run in `CostM C`, the counted version accumulates the
bit operations of the algorithm under the cost model `C`; its value is the plain value.

This file holds the monad, the cost classes (`MulCost`, `DivCost`, `PowCost`) saying what
an operation costs on each type, the bookkeeping lemmas (simp set `cost_simps`, tactics
`cost_simp` and `cost_unfold`), and counted versions of library functions that algorithms
use: `List.prod`, the list combinators, array writes.
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

/-- The cost of a power `a ^ e` computed by repeated multiplication. -/
class PowCost (α : Type) where
  /-- bit operations to compute `a ^ e` under the cost model `C` -/
  powCost : CostModel → α → ℕ → ℕ

/-- `a ^ e = ((a · a) · a) ⋯`: the `i`-th product multiplies `a^i` by `a`. -/
instance : PowCost ℕ := ⟨fun C a e => ∑ i ∈ Finset.range (e - 1), C.mul (a ^ (i + 1)).size a.size⟩
instance : PowCost ℤ :=
  ⟨fun C a e => ∑ i ∈ Finset.range (e - 1), C.mul (a.natAbs ^ (i + 1)).size a.natAbs.size⟩
instance (n : ℕ) : PowCost (ZMod n) := ⟨fun C _ e => (e - 1) * C.mulMod n.size⟩

/-- The big-number primitives an algorithm may use: charges for a multiplication and for a
division with remainder.  Everything else (comparisons, additions, shifts) is free, as in
the cost model. -/
class NatArith (m : Type → Type) where
  /-- record the cost of multiplying `a` and `b` -/
  chargeMul {α : Type} [MulCost α] : α → α → m Unit
  /-- record the cost of dividing `a` by `b` with remainder -/
  chargeMod {α : Type} [DivCost α] : α → α → m Unit
  /-- record the cost of the power `a ^ e` -/
  chargePow {α : Type} [PowCost α] : α → ℕ → m Unit
  /-- record `k` bit operations (e.g. `k` memory writes) -/
  charge : ℕ → m Unit

/-- Plain execution. -/
instance : NatArith Id where
  chargeMul _ _ := pure ()
  chargeMod _ _ := pure ()
  chargePow _ _ := pure ()
  charge _ := pure ()

/-- Counted execution under the cost model `C`. -/
def CostM (_C : CostModel) (α : Type) : Type := Counted α

instance (C : CostModel) : Monad (CostM C) := inferInstanceAs (Monad Counted)

instance (C : CostModel) : NatArith (CostM C) where
  chargeMul a b := (⟨(), MulCost.mulCost C a b⟩ : Counted Unit)
  chargeMod a b := (⟨(), DivCost.divCost C a b⟩ : Counted Unit)
  chargePow a e := (⟨(), PowCost.powCost C a e⟩ : Counted Unit)
  charge k := (⟨(), k * C.unit⟩ : Counted Unit)

section
variable (C : CostModel)

/-- Run a counted computation: its result. -/
def CostM.val {α} (x : CostM C α) : α := Counted.val x
/-- Run a counted computation: its cost. -/
def CostM.cost {α} (x : CostM C α) : ℕ := Counted.cost x

@[simp, cost_simps] theorem CostM.pure_val {α} (a : α) : CostM.val C (pure a) = a := rfl
@[simp, cost_simps] theorem CostM.pure_cost {α} (a : α) : CostM.cost C (pure a) = 0 := rfl
@[simp, cost_simps] theorem CostM.bind_val {α β} (x : CostM C α) (f : α → CostM C β) :
    CostM.val C (x >>= f) = CostM.val C (f (CostM.val C x)) := rfl
@[simp, cost_simps] theorem CostM.bind_cost {α β} (x : CostM C α) (f : α → CostM C β) :
    CostM.cost C (x >>= f) = CostM.cost C x + CostM.cost C (f (CostM.val C x)) := rfl
@[cost_simps] theorem CostM.ite_cost {α} (c : Prop) [Decidable c] (x y : CostM C α) :
    CostM.cost C (if c then x else y) = if c then CostM.cost C x else CostM.cost C y := by
  split_ifs <;> rfl
@[cost_simps] theorem CostM.ite_val {α} (c : Prop) [Decidable c] (x y : CostM C α) :
    CostM.val C (if c then x else y) = if c then CostM.val C x else CostM.val C y := by
  split_ifs <;> rfl
@[simp, cost_simps] theorem CostM.chargeMul_cost {α} [MulCost α] (a b : α) :
    CostM.cost C (NatArith.chargeMul a b) = MulCost.mulCost C a b := rfl
@[simp, cost_simps] theorem CostM.chargeMod_cost {α} [DivCost α] (a b : α) :
    CostM.cost C (NatArith.chargeMod a b) = DivCost.divCost C a b := rfl
@[simp, cost_simps] theorem CostM.chargePow_cost {α} [PowCost α] (a : α) (e : ℕ) :
    CostM.cost C (NatArith.chargePow a e) = PowCost.powCost C a e := rfl
@[simp, cost_simps] theorem CostM.charge_cost (k : ℕ) :
    CostM.cost C (NatArith.charge k) = k * C.unit := rfl
@[simp, cost_simps] theorem mulCost_nat (a b : ℕ) : MulCost.mulCost C a b = C.mul a.size b.size := rfl
@[simp, cost_simps] theorem divCost_nat (a b : ℕ) : DivCost.divCost C a b = C.divMod a.size b.size := rfl
@[simp, cost_simps] theorem mulCost_int (a b : ℤ) :
    MulCost.mulCost C a b = C.mul a.natAbs.size b.natAbs.size := rfl
@[simp, cost_simps] theorem divCost_int (a b : ℤ) :
    DivCost.divCost C a b = C.divMod a.natAbs.size b.natAbs.size := rfl
@[simp, cost_simps] theorem mulCost_zmod {n : ℕ} (a b : ZMod n) : MulCost.mulCost C a b = C.mulMod n.size :=
  rfl

end

/-- `List.prod` multiplies from the right, `[a, b, c].prod = a * (b * (c * 1))`: a call of
`List.prod` in a `counted_def` is charged with these products. -/
def _root_.List.prod.counted {m : Type → Type} [Monad m] [NatArith m] {α : Type} [Mul α]
    [One α] (l : List α) [MulCost α] : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do List.prod.counted l; NatArith.chargeMul a l.prod

/-! ### Counted list combinators

A call of one of these in a `counted_def` is charged with the charges of the function it
applies (its *charge function*), at every element it is applied to — and only there:
`all`, `any` and `find?` stop where the plain functions stop. -/

section ListCombinators
variable {m : Type → Type} [Monad m] [NatArith m] {α β : Type}

def _root_.List.foldl.counted (f : α → β → α) (init : α) (l : List β)
    (f_charge : α → β → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | b :: l => do f_charge init b; List.foldl.counted f (f init b) l f_charge

def _root_.List.foldr.counted (f : α → β → β) (init : β) (l : List α)
    (f_charge : α → β → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do List.foldr.counted f init l f_charge; f_charge a (l.foldr f init)

def _root_.List.map.counted (f : α → β) (l : List α) (f_charge : α → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do f_charge a; List.map.counted f l f_charge

def _root_.List.all.counted (l : List α) (p : α → Bool) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do p_charge a; if p a then List.all.counted l p p_charge else pure ()

def _root_.List.any.counted (l : List α) (p : α → Bool) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do p_charge a; if p a then pure () else List.any.counted l p p_charge

def _root_.List.filter.counted (p : α → Bool) (l : List α) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do p_charge a; List.filter.counted p l p_charge

def _root_.List.find?.counted (p : α → Bool) (l : List α) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => pure ()
  | a :: l => do p_charge a; if p a then pure () else List.find?.counted p l p_charge

end ListCombinators

/-! ### Arrays

Arrays are used for the sieve, whose work is its memory writes: each written entry costs
one bit operation. -/

/-- Writing one entry. -/
def _root_.Array.setIfInBounds.counted {m : Type → Type} [Monad m] [NatArith m] {α : Type}
    (_xs : Array α) (_i : ℕ) (_v : α) : m Unit := NatArith.charge 1

/-- Allocating and filling `n` entries. -/
def _root_.Array.replicate.counted {m : Type → Type} [Monad m] [NatArith m] {α : Type}
    (n : ℕ) (_v : α) : m Unit := NatArith.charge n

section
variable (C : CostModel) {α β : Type}

@[cost_simps] theorem CostM.setIfInBounds_cost (xs : Array α) (i : ℕ) (v : α) :
    CostM.cost C (Array.setIfInBounds.counted xs i v) = C.unit := by
  simp [Array.setIfInBounds.counted, CostM.cost, NatArith.charge]
@[cost_simps] theorem CostM.replicate_cost (n : ℕ) (v : α) :
    CostM.cost C (Array.replicate.counted n v) = n * C.unit := rfl

/-- `filter` pays the charge of its predicate at every element. -/
@[cost_simps] theorem CostM.filter_cost (p : α → Bool) (l : List α) (pc : α → CostM C Unit) :
    CostM.cost C (List.filter.counted p l pc) = (l.map fun a => CostM.cost C (pc a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter.counted, List.map_cons, List.sum_cons, ← ih]; rfl

/-- `map` pays the charge of its function at every element. -/
@[cost_simps] theorem CostM.map_cost (f : α → β) (l : List α) (fc : α → CostM C Unit) :
    CostM.cost C (List.map.counted f l fc) = (l.map fun a => CostM.cost C (fc a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map.counted, List.map_cons, List.sum_cons, ← ih]; rfl

/-- `foldl` pays the charge of its function at every step; with an invariant `P` of the
accumulator, each step's charge is bounded by `K` of the element. -/
theorem CostM.foldl_cost_le {f : α → β → α} {fc : α → β → CostM C Unit} (P : α → Prop)
    (K : β → ℕ) (hf : ∀ a b, P a → P (f a b)) (l : List β)
    (hK : ∀ a b, P a → b ∈ l → CostM.cost C (fc a b) ≤ K b) {init : α} (h : P init) :
    CostM.cost C (List.foldl.counted f init l fc) ≤ (l.map K).sum := by
  induction l generalizing init with
  | nil => simp [List.foldl.counted, CostM.cost]; rfl
  | cons b l ih =>
    have h₁ := hK init b h (by simp)
    have h₂ := ih (fun a b' ha hb' ↦ hK a b' ha (by simp [hb'])) (hf init b h)
    simp only [List.foldl.counted, List.map_cons, List.sum_cons]
    change CostM.cost C (fc init b) + CostM.cost C (List.foldl.counted f (f init b) l fc) ≤ _
    omega

@[cost_simps] theorem sum_map_zero (l : List α) : (l.map fun _ => (0 : ℕ)).sum = 0 := by
  induction l <;> simp_all

end

attribute [cost_simps] zero_add add_zero ite_self mul_one one_mul zero_mul mul_zero
  mulCount_mul mulCount_divMod divCount_mul divCount_divMod opCount_mul opCount_divMod
  writeCount_mul writeCount_divMod mulCount_unit divCount_unit opCount_unit writeCount_unit
  school_unit mulCount_mulMod divCount_mulMod

/-- Unfold the bookkeeping of a counted computation: what is left is its result and the
sum of the charges of its primitive calls (simp set `cost_simps`). -/
macro "cost_simp" : tactic => `(tactic| simp only [cost_simps, ↓reduceIte] at *)

theorem ite_of_pos {α} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]
theorem ite_of_neg {α} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- `cost_unfold f.counted`: unfold a counted algorithm one step, take the branches its
conditions select (decided from the hypotheses, by `assumption` or `omega`), and unfold the
bookkeeping. -/
macro "cost_unfold " ids:ident,+ : tactic => `(tactic|
  (rw [$[$ids:ident],*]
   try simp (disch := first | assumption | omega) only [ite_of_pos, ite_of_neg, cost_simps, ↓reduceIte, zero_mul, mul_zero,
      Nat.zero_le]))

/-- `cost_induction f a₁ … aₙ`: induction following the recursion of the algorithm `f`
(`fun_induction`), with one step of its counted version unfolded in every case
(`cost_unfold f.counted`).  Cases that this closes disappear; the others remain, named
`case1`, `case2`, … as by `fun_induction`. -/
syntax "cost_induction " term : tactic

macro_rules
  | `(tactic| cost_induction $f:ident $args*) => do
    let fc := Lean.mkIdentFrom f (f.getId ++ `counted)
    `(tactic| fun_induction $f $args* <;> cost_unfold $fc:ident)

/-- `cost_unfold_both f.counted`: unfold one step of `f.counted` on each side of an equation
or inequality (e.g. a bit cost and the matching operation count), then as `cost_unfold`. -/
macro "cost_unfold_both " ids:ident,+ : tactic => `(tactic|
  ((conv_lhs => rw [$[$ids:ident],*])
   (conv_rhs => rw [$[$ids:ident],*])
   try simp (disch := first | assumption | omega) only [ite_of_pos, ite_of_neg, cost_simps,
     ↓reduceIte, zero_mul, mul_zero, Nat.zero_le]))

end PrimeNumbers.Chapter9
