import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter9.CostAttr
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Defs

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

/-- The cost of an addition or subtraction of values of type `α` — and of the other
linear-time operations: shifts, multiplication or division by a power of two. -/
class AddCost (α : Type) where
  /-- bit operations to add or subtract `a` and `b` under the cost model `C` -/
  addCost : CostModel → α → α → ℕ

instance : AddCost ℕ := ⟨fun C a b => C.add a.size b.size⟩
instance : AddCost ℤ := ⟨fun C a b => C.add a.natAbs.size b.natAbs.size⟩
/-- A sum of residues modulo `n`: an addition and a conditional subtraction of `n`. -/
instance (n : ℕ) : AddCost (ZMod n) := ⟨fun C _ _ => 2 * C.add n.size n.size⟩

/-- The cost of a comparison (`=`, `≠`, `<`, `≤`) of values of type `α`. -/
class CmpCost (α : Type) where
  /-- bit operations to compare `a` and `b` under the cost model `C` -/
  cmpCost : CostModel → α → α → ℕ

/-- Numbers compare first by length, then digit by digit: the shorter length counts. -/
instance : CmpCost ℕ := ⟨fun C a b => C.add (min a.size b.size) (min a.size b.size)⟩
instance : CmpCost ℤ :=
  ⟨fun C a b => C.add (min a.natAbs.size b.natAbs.size) (min a.natAbs.size b.natAbs.size)⟩
instance (n : ℕ) : CmpCost (ZMod n) := ⟨fun C _ _ => C.add n.size n.size⟩
/-- Booleans and the unit type compare in one step (counted by the enclosing call). -/
instance : CmpCost Bool := ⟨fun _ _ _ => 0⟩
instance : CmpCost Unit := ⟨fun _ _ _ => 0⟩

/-- Lists compare entry by entry, one step per entry, up to the first difference. -/
def listCmpCost {α : Type} [CmpCost α] [DecidableEq α] (C : CostModel) : List α → List α → ℕ
  | a :: l, b :: l' => C.unit + CmpCost.cmpCost C a b + if a = b then listCmpCost C l l' else 0
  | _, _ => C.unit

instance {α : Type} [CmpCost α] [DecidableEq α] : CmpCost (List α) := ⟨listCmpCost⟩

instance {α β : Type} [CmpCost α] [CmpCost β] : CmpCost (α × β) :=
  ⟨fun C a b => CmpCost.cmpCost C a.1 b.1 + CmpCost.cmpCost C a.2 b.2⟩

instance {α : Type} [CmpCost α] : CmpCost (Option α) := ⟨fun C a b => match a, b with
  | some x, some y => CmpCost.cmpCost C x y
  | _, _ => 0⟩

/-- The arithmetic of a coefficient type, for generic code (polynomials, matrices): products,
sums and comparisons. -/
class ArithCost (α : Type) extends MulCost α, AddCost α, CmpCost α

instance : ArithCost ℕ := {}
instance : ArithCost ℤ := {}
instance (n : ℕ) : ArithCost (ZMod n) := {}

/-- Every operation on `α` costs at most `s` bit operations under `C`: the hypothesis under
which generic code (polynomials over `α`) is analysed. -/
def ArithCost.Bounded (α : Type) [ArithCost α] (C : CostModel) (s : ℕ) : Prop :=
  ∀ x y : α, MulCost.mulCost C x y ≤ s ∧ AddCost.addCost C x y ≤ s ∧ CmpCost.cmpCost C x y ≤ s

/-- Residues modulo `n`: a modular product, or two linear operations, at most. -/
theorem ArithCost.bounded_zmod (C : CostModel) (n : ℕ) :
    ArithCost.Bounded (ZMod n) C (C.mulMod n.size + 2 * C.add n.size n.size) :=
  fun _ _ ↦ ⟨Nat.le_add_right _ _, Nat.le_add_left _ _, by
    show C.add n.size n.size ≤ _; omega⟩

/-- The cost of an inverse in a field (e.g. by the extended Euclid algorithm in `ZMod p`). -/
class InvCost (α : Type) where
  invCost : CostModel → α → ℕ

/-- The cost of converting a natural number into `α`: for residues, a reduction. -/
class CastCost (α : Type) where
  castCost : CostModel → ℕ → ℕ

instance (n : ℕ) : CastCost (ZMod n) := ⟨fun C x => C.divMod x.size n.size⟩
instance : CastCost ℤ := ⟨fun C x => C.add x.size x.size⟩
instance : CastCost ℕ := ⟨fun _ _ => 0⟩

/-- The cost of hashing a key. -/
class HashCost (α : Type) where
  hashCost : CostModel → α → ℕ

instance : HashCost ℕ := ⟨fun C a => C.add a.size a.size⟩

/-- The primitives of the machine: charges for each arithmetic operation, by its operands,
and for `k` steps. -/
class NatArith (m : Type → Type) where
  /-- record the cost of multiplying `a` and `b` -/
  chargeMul {α : Type} [MulCost α] : α → α → m Unit
  /-- record the cost of dividing `a` by `b` with remainder -/
  chargeMod {α : Type} [DivCost α] : α → α → m Unit
  /-- record the cost of the power `a ^ e` -/
  chargePow {α : Type} [PowCost α] : α → ℕ → m Unit
  /-- record `k` bit operations (e.g. `k` memory writes) -/
  charge : ℕ → m Unit
  /-- record the cost of adding or subtracting `a` and `b` -/
  chargeAdd {α : Type} [AddCost α] : α → α → m Unit
  /-- record the cost of comparing `a` and `b` -/
  chargeCmp {α : Type} [CmpCost α] : α → α → m Unit
  /-- record the cost of hashing the key `a` -/
  chargeHash {α : Type} [HashCost α] : α → m Unit
  /-- record the cost of inverting `a` -/
  chargeInv {α : Type} [InvCost α] : α → m Unit
  /-- record the cost of converting the natural number `x` into `α` -/
  chargeCast (α : Type) [CastCost α] : ℕ → m Unit

/-- Plain execution. -/
instance : NatArith Id where
  chargeMul _ _ := pure ()
  chargeMod _ _ := pure ()
  chargePow _ _ := pure ()
  charge _ := pure ()
  chargeAdd _ _ := pure ()
  chargeCmp _ _ := pure ()
  chargeHash _ := pure ()
  chargeInv _ := pure ()
  chargeCast _ _ _ := pure ()

/-- Counted execution under the cost model `C`. -/
def CostM (_C : CostModel) (α : Type) : Type := Counted α

instance (C : CostModel) : Monad (CostM C) := inferInstanceAs (Monad Counted)

instance (C : CostModel) : NatArith (CostM C) where
  chargeMul a b := (⟨(), MulCost.mulCost C a b⟩ : Counted Unit)
  chargeMod a b := (⟨(), DivCost.divCost C a b⟩ : Counted Unit)
  chargePow a e := (⟨(), PowCost.powCost C a e⟩ : Counted Unit)
  charge k := (⟨(), k * C.unit⟩ : Counted Unit)
  chargeAdd a b := (⟨(), AddCost.addCost C a b⟩ : Counted Unit)
  chargeCmp a b := (⟨(), CmpCost.cmpCost C a b⟩ : Counted Unit)
  chargeHash a := (⟨(), HashCost.hashCost C a⟩ : Counted Unit)
  chargeInv a := (⟨(), InvCost.invCost C a⟩ : Counted Unit)
  chargeCast α _ x := (⟨(), CastCost.castCost (α := α) C x⟩ : Counted Unit)

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
@[simp, cost_simps] theorem CostM.chargeAdd_cost {α} [AddCost α] (a b : α) :
    CostM.cost C (NatArith.chargeAdd a b) = AddCost.addCost C a b := rfl
@[simp, cost_simps] theorem CostM.chargeCmp_cost {α} [CmpCost α] (a b : α) :
    CostM.cost C (NatArith.chargeCmp a b) = CmpCost.cmpCost C a b := rfl
@[simp, cost_simps] theorem addCost_nat (a b : ℕ) :
    AddCost.addCost C a b = C.add a.size b.size := rfl
@[simp, cost_simps] theorem addCost_int (a b : ℤ) :
    AddCost.addCost C a b = C.add a.natAbs.size b.natAbs.size := rfl
@[simp, cost_simps] theorem addCost_zmod {n : ℕ} (a b : ZMod n) :
    AddCost.addCost C a b = 2 * C.add n.size n.size := rfl
@[simp, cost_simps] theorem cmpCost_nat (a b : ℕ) :
    CmpCost.cmpCost C a b = C.add (min a.size b.size) (min a.size b.size) := rfl
@[simp, cost_simps] theorem cmpCost_int (a b : ℤ) :
    CmpCost.cmpCost C a b =
      C.add (min a.natAbs.size b.natAbs.size) (min a.natAbs.size b.natAbs.size) := rfl
@[simp, cost_simps] theorem cmpCost_zmod {n : ℕ} (a b : ZMod n) :
    CmpCost.cmpCost C a b = C.add n.size n.size := rfl
@[simp, cost_simps] theorem cmpCost_bool (a b : Bool) : CmpCost.cmpCost C a b = 0 := rfl
@[simp, cost_simps] theorem CostM.chargePow_cost {α} [PowCost α] (a : α) (e : ℕ) :
    CostM.cost C (NatArith.chargePow a e) = PowCost.powCost C a e := rfl
@[simp, cost_simps] theorem CostM.chargeHash_cost {α} [HashCost α] (a : α) :
    CostM.cost C (NatArith.chargeHash a) = HashCost.hashCost C a := rfl
@[simp, cost_simps] theorem CostM.chargeInv_cost {α} [InvCost α] (a : α) :
    CostM.cost C (NatArith.chargeInv a) = InvCost.invCost C a := rfl
@[simp, cost_simps] theorem CostM.chargeCast_cost (α) [CastCost α] (x : ℕ) :
    CostM.cost C (NatArith.chargeCast α x) = CastCost.castCost (α := α) C x := rfl
@[simp, cost_simps] theorem castCost_zmod (n x : ℕ) :
    CastCost.castCost (α := ZMod n) C x = C.divMod x.size n.size := rfl
@[simp, cost_simps] theorem castCost_int (x : ℕ) :
    CastCost.castCost (α := ℤ) C x = C.add x.size x.size := rfl
@[simp, cost_simps] theorem castCost_nat (x : ℕ) : CastCost.castCost (α := ℕ) C x = 0 := rfl
@[simp, cost_simps] theorem cmpCost_nil_right {α : Type} [CmpCost α] [DecidableEq α]
    (l : List α) : CmpCost.cmpCost C l [] = C.unit := by
  cases l <;> rfl
@[simp, cost_simps] theorem cmpCost_nil_left {α : Type} [CmpCost α] [DecidableEq α]
    (l : List α) : CmpCost.cmpCost C [] l = C.unit := by
  cases l <;> rfl
@[simp, cost_simps] theorem hashCost_nat (a : ℕ) : HashCost.hashCost C a = C.add a.size a.size :=
  rfl
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

/-! ## Counted library functions

Every library function an algorithm calls is charged for the steps it takes: one `unit`
per list cell visited (and one for the end of the list), one per array access, and the
charges of the functions it applies.  A library function without a counted version cannot
be called from a `counted_def`, unless it takes constant time (`CountedDef.constTime`). -/

section ListFunctions
variable {m : Type → Type} [Monad m] [NatArith m] {α β : Type}

/-- `List.prod` multiplies from the right, `[a, b, c].prod = a * (b * (c * 1))`. -/
def _root_.List.prod.counted [Mul α] [One α] (l : List α) [MulCost α] : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do List.prod.counted l; NatArith.chargeMul a l.prod; NatArith.charge 1

/-- `List.sum` adds from the right. -/
def _root_.List.sum.counted [Add α] [Zero α] (l : List α) [AddCost α] : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do List.sum.counted l; NatArith.chargeAdd a l.sum; NatArith.charge 1

def _root_.List.foldl.counted (f : α → β → α) (init : α) (l : List β)
    (f_charge : α → β → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | b :: l => do NatArith.charge 1; f_charge init b; List.foldl.counted f (f init b) l f_charge

def _root_.List.foldr.counted (f : α → β → β) (init : β) (l : List α)
    (f_charge : α → β → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do NatArith.charge 1; List.foldr.counted f init l f_charge; f_charge a (l.foldr f init)

def _root_.List.map.counted (f : α → β) (l : List α) (f_charge : α → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do NatArith.charge 1; f_charge a; List.map.counted f l f_charge

def _root_.List.zipWith.counted {γ : Type} (f : α → β → γ) (l : List α) (l' : List β)
    (f_charge : α → β → m Unit) : m Unit :=
  match l, l' with
  | a :: l, b :: l' => do NatArith.charge 1; f_charge a b; List.zipWith.counted f l l' f_charge
  | _, _ => NatArith.charge 1

def _root_.List.all.counted (l : List α) (p : α → Bool) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do
    NatArith.charge 1; p_charge a; if p a then List.all.counted l p p_charge else pure ()

def _root_.List.any.counted (l : List α) (p : α → Bool) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do
    NatArith.charge 1; p_charge a; if p a then pure () else List.any.counted l p p_charge

def _root_.List.filter.counted (p : α → Bool) (l : List α) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do NatArith.charge 1; p_charge a; List.filter.counted p l p_charge

def _root_.List.find?.counted (p : α → Bool) (l : List α) (p_charge : α → m Unit) : m Unit :=
  match l with
  | [] => NatArith.charge 1
  | a :: l => do
    NatArith.charge 1; p_charge a; if p a then pure () else List.find?.counted p l p_charge

/-! Traversals that apply no function: their steps. -/

def _root_.List.length.counted (l : List α) : m Unit := NatArith.charge (l.length + 1)
def _root_.List.getD.counted (l : List α) (i : ℕ) (_d : α) : m Unit :=
  NatArith.charge (min i l.length + 1)
def _root_.List.append.counted (l _l' : List α) : m Unit := NatArith.charge (l.length + 1)
def _root_.List.take.counted (n : ℕ) (l : List α) : m Unit := NatArith.charge (min n l.length + 1)
def _root_.List.drop.counted (n : ℕ) (l : List α) : m Unit := NatArith.charge (min n l.length + 1)
def _root_.List.reverse.counted (l : List α) : m Unit := NatArith.charge (l.length + 1)
def _root_.List.dropLast.counted (l : List α) : m Unit := NatArith.charge (l.length + 1)
def _root_.List.getLast?.counted (l : List α) : m Unit := NatArith.charge (l.length + 1)
def _root_.List.replicate.counted (n : ℕ) (_a : α) : m Unit := NatArith.charge (n + 1)
def _root_.List.range.counted (n : ℕ) : m Unit := NatArith.charge (n + 1)
def _root_.List.toArray.counted (l : List α) : m Unit := NatArith.charge (l.length + 1)

end ListFunctions

/-! ### Numbers: conversions, lengths, maxima

Converting between `ℤ` and `ℕ` copies the number; its length and logarithm read it: each
is a linear-time operation.  A maximum or minimum is a comparison. -/

section NumberFunctions
variable {m : Type → Type} [Monad m] [NatArith m]

def _root_.Int.toNat.counted (a : ℤ) : m Unit := NatArith.chargeAdd a a
def _root_.Int.natAbs.counted (a : ℤ) : m Unit := NatArith.chargeAdd a a
def _root_.Nat.size.counted (a : ℕ) : m Unit := NatArith.chargeAdd a a
def _root_.Nat.log2.counted (a : ℕ) : m Unit := NatArith.chargeAdd a a
def _root_.Max.max.counted {α : Type} [Max α] [CmpCost α] (a b : α) : m Unit :=
  NatArith.chargeCmp a b
def _root_.Min.min.counted {α : Type} [Min α] [CmpCost α] (a b : α) : m Unit :=
  NatArith.chargeCmp a b

/-- A conversion of a natural number into another type. -/
def _root_.Nat.cast.counted {R : Type} [NatCast R] [CastCost R] (x : ℕ) : m Unit :=
  NatArith.chargeCast R x

end NumberFunctions

/-! ### Arrays and hash maps

An array access or write is one step (writes assume the array is used linearly, so that
it is updated in place).  A hash-map operation is *assumed* to take one step and the
hashing of its key: its expected cost, for a good hash function. -/

section ArrayFunctions
variable {m : Type → Type} [Monad m] [NatArith m] {α : Type}

def _root_.Array.setIfInBounds.counted (_xs : Array α) (_i : ℕ) (_v : α) : m Unit :=
  NatArith.charge 1
def _root_.Array.set!.counted (_xs : Array α) (_i : ℕ) (_v : α) : m Unit := NatArith.charge 1
def _root_.Array.getD.counted (_xs : Array α) (_i : ℕ) (_d : α) : m Unit := NatArith.charge 1
def _root_.Array.push.counted (_xs : Array α) (_v : α) : m Unit := NatArith.charge 1
def _root_.Array.size.counted (_xs : Array α) : m Unit := NatArith.charge 1
def _root_.Array.replicate.counted (n : ℕ) (_v : α) : m Unit := NatArith.charge (n + 1)
def _root_.Array.toList.counted (xs : Array α) : m Unit := NatArith.charge (xs.size + 1)

def _root_.Std.HashMap.insert.counted {β : Type} [BEq α] [Hashable α] [HashCost α]
    (_m : Std.HashMap α β) (a : α) (_b : β) : m Unit := do
  NatArith.charge 1; NatArith.chargeHash a
def _root_.Std.HashMap.get?.counted {β : Type} [BEq α] [Hashable α] [HashCost α]
    (_m : Std.HashMap α β) (a : α) : m Unit := do
  NatArith.charge 1; NatArith.chargeHash a

end ArrayFunctions

section
variable (C : CostModel) {α β : Type}

@[cost_simps] theorem CostM.setIfInBounds_cost (xs : Array α) (i : ℕ) (v : α) :
    CostM.cost C (Array.setIfInBounds.counted xs i v) = C.unit := by
  simp [Array.setIfInBounds.counted, CostM.cost, NatArith.charge]
@[cost_simps] theorem CostM.replicate_cost (n : ℕ) (v : α) :
    CostM.cost C (Array.replicate.counted n v) = (n + 1) * C.unit := rfl

/-- `filter` pays one step and the charge of its predicate at every element. -/
@[cost_simps] theorem CostM.filter_cost (p : α → Bool) (l : List α) (pc : α → CostM C Unit) :
    CostM.cost C (List.filter.counted p l pc) =
      (l.length + 1) * C.unit + (l.map fun a => CostM.cost C (pc a)).sum := by
  induction l with
  | nil => simp [List.filter.counted, CostM.cost, NatArith.charge]
  | cons a l ih =>
    simp only [List.filter.counted, List.map_cons, List.sum_cons, List.length_cons]
    change 1 * C.unit + (CostM.cost C (pc a) + CostM.cost C (List.filter.counted p l pc)) = _
    rw [ih]; ring

/-- `zipWith` pays one step and the charge of its function at every pair. -/
@[cost_simps] theorem CostM.zipWith_cost {γ : Type} (f : α → β → γ) (l : List α) (l' : List β)
    (fc : α → β → CostM C Unit) :
    CostM.cost C (List.zipWith.counted f l l' fc) =
      (min l.length l'.length + 1) * C.unit +
        (List.zipWith (fun a b => CostM.cost C (fc a b)) l l').sum := by
  induction l generalizing l' with
  | nil => simp [List.zipWith.counted, CostM.cost, NatArith.charge]
  | cons a l ih =>
    cases l' with
    | nil => simp [List.zipWith.counted, CostM.cost, NatArith.charge]
    | cons b l' =>
      simp only [List.zipWith.counted, List.zipWith_cons_cons, List.sum_cons, List.length_cons]
      change 1 * C.unit + (CostM.cost C (fc a b) + CostM.cost C (List.zipWith.counted f l l' fc)) = _
      rw [ih, Nat.add_min_add_right]; ring

/-- `map` pays one step and the charge of its function at every element. -/
@[cost_simps] theorem CostM.map_cost (f : α → β) (l : List α) (fc : α → CostM C Unit) :
    CostM.cost C (List.map.counted f l fc) =
      (l.length + 1) * C.unit + (l.map fun a => CostM.cost C (fc a)).sum := by
  induction l with
  | nil => simp [List.map.counted, CostM.cost, NatArith.charge]
  | cons a l ih =>
    simp only [List.map.counted, List.map_cons, List.sum_cons, List.length_cons]
    change 1 * C.unit + (CostM.cost C (fc a) + CostM.cost C (List.map.counted f l fc)) = _
    rw [ih]; ring

/-- `foldl` pays one step and the charge of its function at every step; with an invariant
`P` of the accumulator, each step's charge is bounded by `K` of the element. -/
theorem CostM.foldl_cost_le {f : α → β → α} {fc : α → β → CostM C Unit} (P : α → Prop)
    (K : β → ℕ) (hf : ∀ a b, P a → P (f a b)) (l : List β)
    (hK : ∀ a b, P a → b ∈ l → CostM.cost C (fc a b) ≤ K b) {init : α} (h : P init) :
    CostM.cost C (List.foldl.counted f init l fc) ≤ (l.length + 1) * C.unit + (l.map K).sum := by
  induction l generalizing init with
  | nil => simp [List.foldl.counted, CostM.cost, NatArith.charge]
  | cons b l ih =>
    have h₁ := hK init b h (by simp)
    have h₂ := ih (fun a b' ha hb' ↦ hK a b' ha (by simp [hb'])) (hf init b h)
    simp only [List.foldl.counted, List.map_cons, List.sum_cons, List.length_cons]
    change 1 * C.unit + (CostM.cost C (fc init b) +
      CostM.cost C (List.foldl.counted f (f init b) l fc)) ≤ _
    nlinarith

/-- A sum of naturals: a step and an addition of numbers at most the total per element. -/
theorem CostM.sum_cost_le_nat {k : ℕ} (l : List ℕ) (h : l.sum.size ≤ k) :
    CostM.cost C (List.sum.counted l) ≤ (l.length + 1) * (C.unit + C.add k k) := by
  induction l with
  | nil => simp [List.sum.counted, CostM.cost, NatArith.charge]
  | cons a l ih =>
    have ha : a.size ≤ k := (Nat.size_le_size (by simp)).trans h
    have hl : l.sum.size ≤ k := (Nat.size_le_size (by simp)).trans h
    have := ih hl
    have hadd : C.add a.size l.sum.size ≤ C.add k k := C.add_mono ha hl
    simp only [List.sum.counted, List.length_cons]
    change CostM.cost C (List.sum.counted l) + (C.add a.size l.sum.size + 1 * C.unit) ≤ _
    nlinarith

/-- Per-element charges bounded by `s` sum to at most `length · s`. -/
theorem sum_map_le_length_mul (l : List α) (f : α → ℕ) {s : ℕ} (h : ∀ x ∈ l, f x ≤ s) :
    (l.map f).sum ≤ l.length * s := by
  simpa using List.sum_le_card_nsmul (l.map f) s (by simpa using h)

@[cost_simps] theorem sum_map_zero (l : List α) : (l.map fun _ => (0 : ℕ)).sum = 0 := by
  induction l <;> simp_all

end

attribute [cost_simps] List.length.counted List.getD.counted List.append.counted
  List.take.counted List.drop.counted List.reverse.counted List.dropLast.counted
  List.getLast?.counted List.replicate.counted List.range.counted List.toArray.counted
  Array.set!.counted Array.getD.counted Array.push.counted Array.size.counted
  Array.toList.counted Std.HashMap.insert.counted Std.HashMap.get?.counted
  Int.toNat.counted Int.natAbs.counted Nat.cast.counted Nat.size.counted Nat.log2.counted Max.max.counted
  Min.min.counted
attribute [cost_simps] Nat.size_zero Nat.size_one zero_min min_zero max_self List.map_nil List.sum_nil
attribute [cost_simps] zero_add add_zero ite_self mul_one one_mul zero_mul mul_zero
  mulCount_mul mulCount_divMod divCount_mul divCount_divMod opCount_mul opCount_divMod
  writeCount_mul writeCount_divMod mulCount_unit divCount_unit opCount_unit writeCount_unit
  school_unit school_add mulCount_add divCount_add opCount_add writeCount_add mulCount_mulMod
  divCount_mulMod

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
      Nat.zero_le, List.length_nil, List.length_cons]
   try omega))

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
