import Mathlib

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

/-! ## Cost models -/

/-- A cost model for big-number arithmetic: the number of bit operations for one
multiplication and for one division with remainder, in terms of operand bit lengths. -/
structure CostModel where
  /-- bit operations to multiply an `a`-bit number by a `b`-bit number -/
  mul : ℕ → ℕ → ℕ
  /-- bit operations to divide an `a`-bit number by a `b`-bit number, with remainder -/
  divMod : ℕ → ℕ → ℕ
  /-- multiplying longer numbers costs at least as much -/
  mul_mono : ∀ {a a' b b' : ℕ}, a ≤ a' → b ≤ b' → mul a b ≤ mul a' b'
  /-- dividing a longer number (by the same divisor length) costs at least as much -/
  divMod_mono : ∀ {a a' : ℕ} (b : ℕ), a ≤ a' → divMod a b ≤ divMod a' b

/-- **The grammar-school cost model (§9.1).**  Long multiplication of an `a`-bit by a
`b`-bit number takes `a b` bit operations; long division of an `a`-bit number by a `b`-bit
number produces at most `a - b + 1` quotient bits, each costing a `b`-bit subtraction. -/
def school : CostModel where
  mul a b := a * b
  divMod a b := (a - b + 1) * b
  mul_mono h₁ h₂ := Nat.mul_le_mul h₁ h₂
  divMod_mono b h := Nat.mul_le_mul_right b (by omega)

/-- One "multiply two residues and reduce" modulo a `k`-bit modulus: the unit of work of
all modular algorithms. -/
def CostModel.mulMod (C : CostModel) (k : ℕ) : ℕ := C.mul k k + C.divMod (2 * k) k

/-- In the grammar-school model a modular multiplication costs `2k² + k ≤ 2 (k + 1)²`. -/
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
