import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.Complexity
import PrimeNumbers.Chapter2.Jacobi

/-!
# §9.1 Bit complexity: the cost model, and the costs of Euclid and powering

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 9.1
("Tour of grammar-school methods"), applied to the algorithms of Chapter 2.

The book measures running time in *bit operations*.  This file sets up that measure once,
for use by every complexity analysis in the project.

## The layer of abstraction

* `Nat.size n` is the number of bits of `n` (`size_mul_le`, `log_two_lt_size`, …).
* A `CostModel` says how many bit operations a multiplication and a division with
  remainder take, as functions of the *bit lengths* of the operands.  It is the book's
  `M(n)` made precise.  Analyses are proved for an arbitrary cost model, so they survive a
  change of multiplication algorithm (Karatsuba, FFT, … of §9.5).
* `school` is the "grammar-school" model of §9.1: multiplying an `a`-bit by a `b`-bit
  number costs `a b`; dividing an `a`-bit number by a `b`-bit number costs
  `(a - b + 1) b` (one row of work per quotient bit — this is the book's
  `O((1 + ln q) ln x)` of Exercise 2.6).

## How an algorithm is analysed

For an algorithm `f` we define `fCost C …`, which follows the recursion of `f` branch by
branch and adds up `C.mul`/`C.divMod` at the bit lengths of the *actual operands* of each
big-number operation `f` performs.  Additions, comparisons and shifts are linear in the
bit length and dominated by the multiplications and divisions next to them; they are not
counted.

## Results here

* `powModCost_le`, `powModCost_school_le` — Algorithm 2.1.5 computes `xⁿ mod m` in
  `O(ln n · ln² m)` bit operations (Exercise 2.17: cubic when `n ≈ m`).
* `euclidBitCost_school_le'` — Algorithm 2.1.2 runs in `O(ln² N)` bit operations
  (Exercise 2.6), as claimed after Theorem 2.1.3.
* `jacobiBitCost_school_le'` — Algorithm 2.3.5 runs in `O(ln² m)` bit operations, as
  claimed after the algorithm.
-/

namespace PrimeNumbers.Chapter9

open PrimeNumbers.Chapter2

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

/-! ## Powering (Algorithm 2.1.5) -/

/-- The bit operations spent by `powMod x n m`, following its recursion: each
"multiply, then reduce mod `m`" is charged at the bit lengths of its operands. -/
def powModCost (C : CostModel) (x n m : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then C.divMod x.size m.size
  else if n % 2 = 0 then
    let y := powMod x (n / 2) m
    powModCost C x (n / 2) m + (C.mul y.size y.size + C.divMod (y * y).size m.size)
  else
    let y := powMod x ((n - 1) / 2) m
    let z := y * y % m
    powModCost C x ((n - 1) / 2) m + (C.mul y.size y.size + C.divMod (y * y).size m.size) +
      (C.mul x.size z.size + C.divMod (x * z).size m.size)
termination_by n
decreasing_by all_goals omega

/-- **Bit complexity of Algorithm 2.1.5.**  For `x < m`, computing `xⁿ mod m` costs at
most `2 ⌊log₂ n⌋` modular multiplications (plus the initial reduction of `x`). -/
theorem powModCost_le (C : CostModel) {x m : ℕ} (hx : x < m) (n : ℕ) :
    powModCost C x n m ≤
      C.divMod m.size m.size + Nat.log 2 n * (2 * C.mulMod m.size) := by
  have hm : 0 < m := by omega
  fun_induction powModCost C x n m with
  | case1 => omega
  | case2 => simpa using C.divMod_mono _ (size_le_of_lt hx)
  | case3 n h0 h1 heven y ih =>
    have hy : y < m := powMod_lt _ _ hm
    have hstep := mul_add_divMod_le C hy hy
    have hlog : Nat.log 2 n = Nat.log 2 (n / 2) + 1 := by
      have := Nat.log_div_base 2 n
      have := Nat.log_pos (b := 2) (by norm_num) (by omega : 2 ≤ n)
      omega
    rw [hlog, add_mul]
    omega
  | case4 n h0 h1 hodd y z ih =>
    have hy : y < m := powMod_lt _ _ hm
    have hz : z < m := Nat.mod_lt _ hm
    have hstep₁ := mul_add_divMod_le C hy hy
    have hstep₂ := mul_add_divMod_le C hx hz
    have hlog : Nat.log 2 n = Nat.log 2 ((n - 1) / 2) + 1 := by
      have := Nat.log_div_base 2 n
      have := Nat.log_pos (b := 2) (by norm_num) (by omega : 2 ≤ n)
      rw [show (n - 1) / 2 = n / 2 by omega]
      omega
    rw [hlog, add_mul]
    omega

/-- **Exercise 2.17.**  With grammar-school arithmetic, `xⁿ mod m` costs at most
`(4 log₂ n + 1)(k + 1)²` bit operations, `k` the bit length of `m`: that is
`O(ln n · ln² m)`, cubic in the number of bits when `n` is of the size of `m`. -/
theorem powModCost_school_le {x m : ℕ} (hx : x < m) (n : ℕ) :
    powModCost school x n m ≤ (4 * Nat.log 2 n + 1) * (m.size + 1) ^ 2 := by
  refine (powModCost_le school hx n).trans ?_
  rw [school_mulMod]
  have : school.divMod m.size m.size = m.size := by simp [school]
  rw [this]
  nlinarith [Nat.zero_le (Nat.log 2 n), Nat.zero_le m.size,
    Nat.zero_le (Nat.log 2 n * m.size)]

/-! ## Euclid (Algorithms 2.1.2 and 2.1.4) -/

/-- The bit operations spent by `euclid x y`: one division `x mod y` per loop pass. -/
def euclidBitCost (C : CostModel) (x y : ℕ) : ℕ :=
  if 0 < y then C.divMod x.size y.size + euclidBitCost C y (x % y) else 0
termination_by y
decreasing_by exact Nat.mod_lt _ ‹0 < y›

/-- The key estimate of Exercise 2.6: with long division, the quotient bits of all the
divisions of a Euclid run together number at most `size x + (number of steps)`, because
the bit lengths telescope.  Hence the total cost is at most
`size y · (size x + steps)`. -/
theorem euclidBitCost_school_le {x y : ℕ} (hyx : y ≤ x) :
    euclidBitCost school x y ≤ y.size * (x.size + euclidSteps x y) := by
  fun_induction euclidBitCost school x y with
  | case1 x y hy ih =>
    have ih := ih (Nat.mod_lt _ hy).le
    have hsteps : euclidSteps x y = euclidSteps y (x % y) + 1 := by
      rw [euclidSteps]; simp [hy]
    have h₁ : (x % y).size ≤ y.size := size_le_of_lt (Nat.mod_lt _ hy)
    have h₂ : y.size ≤ x.size := Nat.size_le_size hyx
    have h₃ : (x % y).size * (y.size + euclidSteps y (x % y)) ≤
        y.size * (y.size + euclidSteps y (x % y)) := Nat.mul_le_mul_right _ h₁
    have h₄ : school.divMod x.size y.size = (x.size - y.size + 1) * y.size := rfl
    rw [hsteps, h₄]
    calc (x.size - y.size + 1) * y.size + euclidBitCost school y (x % y)
        ≤ (x.size - y.size + 1) * y.size + y.size * (y.size + euclidSteps y (x % y)) := by
          omega
      _ = y.size * (x.size - y.size + 1 + y.size + euclidSteps y (x % y)) := by ring
      _ = y.size * (x.size + (euclidSteps y (x % y) + 1)) := by
          rw [show x.size - y.size + 1 + y.size = x.size + 1 by omega]; ring
  | case2 x y hy => simp

/-- **Bit complexity of the Euclid algorithm (Exercise 2.6).**  For `y < x ≤ N`, with `N`
of `k` bits, Algorithm 2.1.2 takes at most `k (3k + 1)` bit operations in the
grammar-school model: the `O(ln² N)` stated after Theorem 2.1.3. -/
theorem euclidBitCost_school_le' {x y N : ℕ} (hxy : y < x) (hN : x ≤ N) :
    euclidBitCost school x y ≤ N.size * (3 * N.size + 1) := by
  refine (euclidBitCost_school_le hxy.le).trans ?_
  have h₁ : y.size ≤ N.size := Nat.size_le_size (hxy.le.trans hN)
  have h₂ : x.size ≤ N.size := Nat.size_le_size hN
  have h₃ := euclidSteps_le hxy hN
  have h₄ := log_two_le_size N
  exact Nat.mul_le_mul h₁ (by omega)

/-! ## Jacobi symbol (Algorithm 2.3.5) -/

/-- The bit operations spent by `jacobiLoop a m t`: one division `m mod a'` per pass of
the outer loop.  (The halvings `a = a/2` and the tests modulo 4 and 8 are shifts and
look-ups of the low bits.) -/
def jacobiBitCost (C : CostModel) (a m : ℕ) (t : ℤ) : ℕ :=
  if a = 0 then 0
  else
    let r := jacobiHalve a m t
    C.divMod m.size r.1.size +
      jacobiBitCost C (m % r.1) r.1 (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2)
termination_by a
decreasing_by
  have := jacobiHalve_fst_le a m t
  have := Nat.mod_lt m (Nat.pos_of_ne_zero (jacobiHalve_fst_pos ‹a ≠ 0› m t))
  omega

/-- As for Euclid, the quotient bits of all the divisions telescope: the total cost is at
most `size a · (size m + passes)`. -/
theorem jacobiBitCost_school_le (a m : ℕ) (t : ℤ) (ham : a < m) :
    jacobiBitCost school a m t ≤ a.size * (m.size + jacobiSteps a m t) := by
  fun_induction jacobiBitCost school a m t with
  | case1 m t => simp
  | case2 a m t ha r ih =>
    have hr_le : r.1 ≤ a := jacobiHalve_fst_le a m t
    have hr_pos : 0 < r.1 := Nat.pos_of_ne_zero (jacobiHalve_fst_pos ha m t)
    have hlt : m % r.1 < r.1 := Nat.mod_lt _ hr_pos
    have ih := ih hlt
    have hsteps : jacobiSteps a m t =
        jacobiSteps (m % r.1) r.1 (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2) + 1 := by
      rw [jacobiSteps]; simp [ha, r]
    simp only [dite_eq_ite] at ih
    generalize jacobiSteps (m % r.1) r.1 (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2) = s
      at ih hsteps
    generalize jacobiBitCost school (m % r.1) r.1
      (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2) = c at ih
    have h₁ : (m % r.1).size ≤ r.1.size := size_le_of_lt hlt
    have h₂ : r.1.size ≤ a.size := Nat.size_le_size hr_le
    have h₃ : r.1.size ≤ m.size := Nat.size_le_size (hr_le.trans ham.le)
    have h₄ : school.divMod m.size r.1.size = (m.size - r.1.size + 1) * r.1.size := rfl
    rw [hsteps, h₄]
    calc (m.size - r.1.size + 1) * r.1.size + c
        ≤ (m.size - r.1.size + 1) * r.1.size + r.1.size * (r.1.size + s) :=
          Nat.add_le_add_left (ih.trans (Nat.mul_le_mul_right _ h₁)) _
      _ = r.1.size * (m.size - r.1.size + 1 + r.1.size + s) := by ring
      _ = r.1.size * (m.size + (s + 1)) := by
          rw [show m.size - r.1.size + 1 + r.1.size = m.size + 1 by omega]; ring
      _ ≤ a.size * (m.size + (s + 1)) := Nat.mul_le_mul_right _ h₂

/-- **Bit complexity of the Jacobi symbol algorithm.**  For `a < m`, with `m` of `k` bits,
Algorithm 2.3.5 spends at most `k (3k + 1)` bit operations on its divisions in the
grammar-school model: `O(ln² m)`, "about as hard as taking a gcd". -/
theorem jacobiBitCost_school_le' (a m : ℕ) (t : ℤ) (ham : a < m) :
    jacobiBitCost school a m t ≤ m.size * (3 * m.size + 1) := by
  refine (jacobiBitCost_school_le a m t ham).trans ?_
  have h₁ : a.size ≤ m.size := size_le_of_lt ham
  have h₂ := jacobiSteps_le a m t ham
  have h₃ : jacobiSteps a m t ≤ 2 * m.size + 1 := by
    split_ifs at h₂ with h0
    · omega
    · have := log_two_le_size (a * m)
      have := size_mul_le a m
      omega
  exact Nat.mul_le_mul h₁ (by omega)

end PrimeNumbers.Chapter9
