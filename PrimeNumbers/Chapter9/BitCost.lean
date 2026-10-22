import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# §9.1 Bit complexity: the cost model

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 9.1
("Tour of grammar-school methods").

The book measures running time in *bit operations*.  This file sets up that measure once.
It depends on nothing else in the project; every algorithm file imports it and states its
running time next to its correctness theorem, in a final section "Running time".

## The layer of abstraction

* `Nat.size n` is the number of bits of `n` (`size_mul_le`, `log_two_le_size`, …).
* A `CostModel` says how many bit operations a multiplication and a division with
  remainder take, as functions of the *bit lengths* of the operands.  It is the book's
  `M(n)` made precise.  Analyses are proved for an arbitrary cost model where possible, so
  they survive a change of multiplication algorithm (Karatsuba, FFT, … of §9.5), and the
  plain operation counts they rest on are kept as theorems of their own.
* `school` is the "grammar-school" model of §9.1: multiplying an `a`-bit by a `b`-bit
  number costs `a b`; dividing an `a`-bit number by a `b`-bit number costs
  `(a - b + 1) b` (one row of work per quotient bit — the book's `O((1 + ln q) ln x)` of
  Exercise 2.6).

## How an algorithm is analysed

For an algorithm `f` we define `fCost C …`, which follows the recursion of `f` branch by
branch and adds up `C.mul`/`C.divMod` at the bit lengths of the *actual operands* of each
big-number operation `f` performs.  Additions, comparisons and shifts are linear in the
bit length and dominated by the multiplications and divisions next to them; they are not
counted.
-/

namespace PrimeNumbers.Chapter9

/-! ## Bit lengths -/

/-- The product of an `a`-bit and a `b`-bit number has at most `a + b` bits. -/
theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_le_of_lt {a b : ℕ} (h : a < b) : a.size ≤ b.size := Nat.size_le_size h.le

/-- `⌊log₂ n⌋ ≤` the bit length of `n` (indeed it is one less, for `n ≠ 0`). -/
theorem log_two_le_size (n : ℕ) : Nat.log 2 n ≤ n.size := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')).le

theorem size_le_self (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

/-- A sum has at most one bit more than the longer summand. -/
theorem size_add_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h₁ : 2 ^ a.size ≤ 2 ^ max a.size b.size :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h₂ : 2 ^ b.size ≤ 2 ^ max a.size b.size :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  omega

/-- A sum has at most as many bits as its summands together (a bound without `max`). -/
theorem size_add_le_add (a b : ℕ) : (a + b).size ≤ a.size + b.size := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h₁ := size_add_le a b
  have : 0 < a.size := Nat.size_pos.mpr ha
  have : 0 < b.size := Nat.size_pos.mpr hb
  omega

/-- A product plus a carry stays below the product of the bounds: `p q + c < A B`.  (So the
operand `x y + c` of a modular multiplication with `x, y, c < n` has at most `2 size n`
bits.) -/
theorem mul_add_lt_mul_of_lt_left {p q c A B : ℕ} (hp : p < A) (hq : q < B) (hc : c < A) :
    p * q + c < A * B := by
  obtain ⟨A, rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  have := Nat.mul_le_mul (Nat.lt_succ_iff.mp hp) (Nat.lt_succ_iff.mp hq)
  nlinarith

theorem mul_add_lt_mul_of_lt_right {p q c A B : ℕ} (hp : p < A) (hq : q < B) (hc : c < B) :
    p * q + c < A * B := by
  rw [Nat.mul_comm p, Nat.mul_comm A]; exact mul_add_lt_mul_of_lt_left hq hp hc

/-! ## Cost models -/

/-- A cost model: what each primitive of the machine costs.  Nothing an algorithm does is
free: every call of a function costs one `unit` (its constructors, matches and branches
included), list and array steps are charged by the library's counted functions, and every
arithmetic operation is charged by the bit lengths of its operands. -/
structure CostModel where
  /-- bit operations to multiply an `a`-bit number by a `b`-bit number -/
  mul : ℕ → ℕ → ℕ
  /-- bit operations to divide an `a`-bit number by a `b`-bit number, with remainder -/
  divMod : ℕ → ℕ → ℕ
  /-- bit operations per bit of a linear-time operation (an addition, a subtraction, a
  comparison, a shift, a multiplication or division by a power of two): such an operation
  on an `a`-bit and a `b`-bit number costs `addRate · (max a b + 1)` (`CostModel.add`) -/
  addRate : ℕ
  /-- the cost of one step: a function call, a list cell visited, an array access -/
  unit : ℕ
  /-- multiplying longer numbers costs at least as much -/
  mul_mono : ∀ {a a' b b' : ℕ}, a ≤ a' → b ≤ b' → mul a b ≤ mul a' b'
  /-- dividing a longer number (by the same divisor length) costs at least as much -/
  divMod_mono : ∀ {a a' : ℕ} (b : ℕ), a ≤ a' → divMod a b ≤ divMod a' b

/-- A linear-time operation on an `a`-bit and a `b`-bit number. -/
def CostModel.add (C : CostModel) (a b : ℕ) : ℕ := C.addRate * (max a b + 1)

theorem CostModel.add_mono (C : CostModel) {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    C.add a b ≤ C.add a' b' :=
  Nat.mul_le_mul_left _ (by omega)

/-- A linear operation on `w n`-bit numbers costs at most `n` operations on `w`-bit ones. -/
theorem CostModel.add_mul_le (C : CostModel) {w n : ℕ} (hn : 1 ≤ n) :
    C.add (w * n) (w * n) ≤ n * C.add w w := by
  unfold CostModel.add
  simp only [max_self]
  nlinarith [Nat.zero_le C.addRate, Nat.zero_le w]

/-- **The grammar-school cost model (§9.1).**  Long multiplication of an `a`-bit by a
`b`-bit number takes `a b` bit operations; long division of an `a`-bit number by a `b`-bit
number produces at most `a - b + 1` quotient bits, each costing a `b`-bit subtraction; an
addition (ripple carry) or comparison takes `max a b + 1`; a step takes one. -/
def school : CostModel where
  mul a b := a * b
  divMod a b := (a - b + 1) * b
  addRate := 1
  unit := 1
  mul_mono h₁ h₂ := Nat.mul_le_mul h₁ h₂
  divMod_mono b h := Nat.mul_le_mul_right b (by omega)

/-! ### Worst cases over the inputs of a given bit length -/

/-- The largest value of `g` on the numbers of at most `k` bits. -/
def maxOnBits (k : ℕ) (g : ℕ → ℕ) : ℕ := (Finset.range (2 ^ k)).sup g

theorem le_maxOnBits {k x : ℕ} (g : ℕ → ℕ) (hx : x.size ≤ k) : g x ≤ maxOnBits k g :=
  Finset.le_sup (f := g) (Finset.mem_range.mpr (Nat.size_le.mp hx))

theorem maxOnBits_mono (g : ℕ → ℕ) : Monotone (maxOnBits · g) := fun _ _ h ↦
  Finset.sup_mono (Finset.range_subset_range.mpr (Nat.pow_le_pow_right (by norm_num) h))

theorem maxOnBits_le {k B : ℕ} {g : ℕ → ℕ} (h : ∀ x, x.size ≤ k → g x ≤ B) :
    maxOnBits k g ≤ B :=
  Finset.sup_le fun x hx ↦ h x (Nat.size_le.mpr (Finset.mem_range.mp hx))

/-- The largest value of `g` on pairs of numbers of at most `k` bits. -/
def maxOnBits₂ (k : ℕ) (g : ℕ → ℕ → ℕ) : ℕ := maxOnBits k fun x ↦ maxOnBits k (g x)

theorem le_maxOnBits₂ {k x y : ℕ} (g : ℕ → ℕ → ℕ) (hx : x.size ≤ k) (hy : y.size ≤ k) :
    g x y ≤ maxOnBits₂ k g :=
  (le_maxOnBits (g x) hy).trans (le_maxOnBits (fun x ↦ maxOnBits k (g x)) hx)

theorem maxOnBits₂_le {k B : ℕ} {g : ℕ → ℕ → ℕ}
    (h : ∀ x y, x.size ≤ k → y.size ≤ k → g x y ≤ B) : maxOnBits₂ k g ≤ B :=
  maxOnBits_le fun x hx ↦ maxOnBits_le fun y hy ↦ h x y hx hy

theorem maxOnBits₂_mono (g : ℕ → ℕ → ℕ) : Monotone (maxOnBits₂ · g) := fun _ _ h ↦
  maxOnBits₂_le fun _ _ hx hy ↦ le_maxOnBits₂ g (hx.trans h) (hy.trans h)

/-- The worst cost of a division of numbers of at most `k` bits (a division is not more
expensive for a longer dividend, but may be for a shorter divisor). -/
def CostModel.divBound (C : CostModel) (k : ℕ) : ℕ := (Finset.range (k + 1)).sup (C.divMod k)

theorem CostModel.divMod_le_divBound (C : CostModel) {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    C.divMod a b ≤ C.divBound k :=
  (C.divMod_mono b ha).trans (Finset.le_sup (f := C.divMod k) (Finset.mem_range.mpr (by omega)))

theorem CostModel.divBound_mono (C : CostModel) : Monotone C.divBound := fun a b h ↦
  Finset.sup_le fun c hc ↦ C.divMod_le_divBound (Nat.le_refl a |>.trans h)
    (by have := Finset.mem_range.mp hc; omega)

theorem CostModel.mul_le_mul_bound (C : CostModel) {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    C.mul a b ≤ C.mul k k := C.mul_mono ha hb

theorem school_divBound_le (k : ℕ) : school.divBound k ≤ (k + 1) * k :=
  Finset.sup_le fun b hb ↦ by
    have := Finset.mem_range.mp hb
    show (k - b + 1) * b ≤ _
    exact Nat.mul_le_mul (by omega) (by omega)

/-! ### Counting models

An *operation count* is the cost under a model that charges `1` for the operations counted
and `0` for the rest: so the number of multiplications, divisions or writes an algorithm
performs is derived from its code exactly like its bit complexity. -/

/-- Counts multiplications (a product of residues — multiply and reduce — counts once). -/
def mulCount : CostModel where
  mul _ _ := 1
  divMod _ _ := 0
  addRate := 0
  unit := 0
  mul_mono _ _ := le_rfl
  divMod_mono _ _ := le_rfl

/-- Counts divisions with remainder. -/
def divCount : CostModel where
  mul _ _ := 0
  divMod _ _ := 1
  addRate := 0
  unit := 0
  mul_mono _ _ := le_rfl
  divMod_mono _ _ := le_rfl

/-- Counts multiplications and divisions. -/
def opCount : CostModel where
  mul _ _ := 1
  divMod _ _ := 1
  addRate := 0
  unit := 0
  mul_mono _ _ := le_rfl
  divMod_mono _ _ := le_rfl

/-- Counts elementary steps (memory writes). -/
def writeCount : CostModel where
  mul _ _ := 0
  divMod _ _ := 0
  addRate := 0
  unit := 1
  mul_mono _ _ := le_rfl
  divMod_mono _ _ := le_rfl

@[simp] theorem school_mul (a b : ℕ) : school.mul a b = a * b := rfl
@[simp] theorem school_divMod (a b : ℕ) : school.divMod a b = (a - b + 1) * b := rfl
theorem school_divMod_self (k : ℕ) : school.divMod k k = k := by simp

@[simp] theorem mulCount_mul (a b : ℕ) : mulCount.mul a b = 1 := rfl
@[simp] theorem mulCount_divMod (a b : ℕ) : mulCount.divMod a b = 0 := rfl
@[simp] theorem divCount_mul (a b : ℕ) : divCount.mul a b = 0 := rfl
@[simp] theorem divCount_divMod (a b : ℕ) : divCount.divMod a b = 1 := rfl
@[simp] theorem opCount_mul (a b : ℕ) : opCount.mul a b = 1 := rfl
@[simp] theorem opCount_divMod (a b : ℕ) : opCount.divMod a b = 1 := rfl
@[simp] theorem writeCount_mul (a b : ℕ) : writeCount.mul a b = 0 := rfl
@[simp] theorem writeCount_divMod (a b : ℕ) : writeCount.divMod a b = 0 := rfl
@[simp] theorem mulCount_unit : mulCount.unit = 0 := rfl
@[simp] theorem divCount_unit : divCount.unit = 0 := rfl
@[simp] theorem opCount_unit : opCount.unit = 0 := rfl
@[simp] theorem writeCount_unit : writeCount.unit = 1 := rfl
@[simp] theorem school_unit : school.unit = 1 := rfl
@[simp] theorem school_addRate : school.addRate = 1 := rfl
@[simp] theorem school_add (a b : ℕ) : school.add a b = max a b + 1 := by
  simp [CostModel.add, school]
@[simp] theorem mulCount_add (a b : ℕ) : mulCount.add a b = 0 := by simp [CostModel.add, mulCount]
@[simp] theorem divCount_add (a b : ℕ) : divCount.add a b = 0 := by simp [CostModel.add, divCount]
@[simp] theorem opCount_add (a b : ℕ) : opCount.add a b = 0 := by simp [CostModel.add, opCount]
@[simp] theorem writeCount_add (a b : ℕ) : writeCount.add a b = 0 := by
  simp [CostModel.add, writeCount]

/-- One "multiply two residues and reduce" modulo a `k`-bit modulus: the unit of work of
all modular algorithms. -/
def CostModel.mulMod (C : CostModel) (k : ℕ) : ℕ := C.mul k k + C.divMod (2 * k) k

/-- One step on numbers of at most `k` bits: a call (or a list or array step) and one
linear-time operation (an addition, a comparison, a shift).  The unit of the bookkeeping
around the multiplications and divisions. -/
def CostModel.lin (C : CostModel) (k : ℕ) : ℕ := C.unit + C.add k k

@[simp] theorem school_lin (k : ℕ) : school.lin k = k + 2 := by
  simp only [CostModel.lin, school_add, max_self]; rw [show school.unit = 1 from rfl]; omega

/-- In the grammar-school model a modular multiplication costs `2k² + k ≤ 2 (k + 1)²`. -/
@[simp] theorem mulCount_mulMod (k : ℕ) : mulCount.mulMod k = 1 := rfl
@[simp] theorem divCount_mulMod (k : ℕ) : divCount.mulMod k = 1 := rfl

theorem school_mulMod (k : ℕ) : school.mulMod k = 2 * k ^ 2 + k := by
  simp only [CostModel.mulMod, school]
  rw [show 2 * k - k + 1 = k + 1 by omega]
  ring

/-- Multiplying two residues modulo `m` and reducing costs at most `C.mulMod (size m)`. -/
theorem mul_add_divMod_le (C : CostModel) {a b m : ℕ} (ha : a < m) (hb : b < m) :
    C.mul a.size b.size + C.divMod (a * b).size m.size ≤ C.mulMod m.size := by
  refine Nat.add_le_add (C.mul_mono (size_le_of_lt ha) (size_le_of_lt hb))
    (C.divMod_mono _ ?_)
  have := size_mul_le a b
  have := size_le_of_lt ha
  have := size_le_of_lt hb
  omega

end PrimeNumbers.Chapter9
