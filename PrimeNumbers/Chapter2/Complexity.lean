import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.Jacobi

/-!
# Operation counts for the algorithms of Chapter 2

The book states running times in bit operations, e.g. `O(ln² N)` for Euclid and
`O(ln³ m)` for modular powering.  Each of those is "(number of loop passes) × (cost of
one big-number operation)".  This file proves the first factor: for each algorithm we
define a cost function that follows the algorithm's own recursion branch by branch and
counts the arithmetic operations performed, and we bound it by a logarithm of the input.

* `euclidSteps_le`  — Algorithm 2.1.2/2.1.4 perform at most `2 log₂ N + 1` divisions
                      (Theorem 2.1.3 in logarithmic form).
* `powCost_le`      — Algorithm 2.1.5 performs at most `2 log₂ n` multiplications.
* `jacobiSteps_le`  — Algorithm 2.3.5 performs at most `log₂ (a m) + 1` passes of its
                      outer loop, and `jacobiHalveSteps_le`: each inner loop at most `log₂ a`.

These step counts are the input to the bit-complexity bounds of
`PrimeNumbers/Chapter9/BitCost.lean`, which charges each step at the bit lengths of its
operands.
-/

namespace PrimeNumbers.Chapter2

/-! ## Euclid (Algorithms 2.1.2 and 2.1.4) -/

/-- Fibonacci numbers grow at least like `√2ⁿ`: `2^k ≤ F_{2k+1}`. -/
theorem two_pow_le_fib (k : ℕ) : 2 ^ k ≤ Nat.fib (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ : Nat.fib (2 * k + 1) ≤ Nat.fib (2 * k + 2) := Nat.fib_le_fib_succ
    have h₂ : Nat.fib (2 * (k + 1) + 1) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) :=
      Nat.fib_add_two
    rw [pow_succ]
    omega

/-- **Theorem 2.1.3 (Lamé), logarithmic form.**  For `y < x ≤ N` the Euclid loop runs at
most `2 log₂ N + 1` times. -/
theorem euclidSteps_le {x y N : ℕ} (hxy : y < x) (hN : x ≤ N) :
    euclidSteps x y ≤ 2 * Nat.log 2 N + 1 := by
  have h := lame hxy hN
  set s := euclidSteps x y
  have h₁ : 2 ^ (s / 2) ≤ N :=
    (two_pow_le_fib (s / 2)).trans ((Nat.fib_mono (by omega)).trans h)
  have h₂ : s / 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) h₁
  omega

/-- The number of passes of the loop of Algorithm 2.1.4, following `extEuclidLoop`. -/
def extEuclidSteps (g w : ℕ) : ℕ :=
  if 0 < w then extEuclidSteps w (g - g / w * w) + 1 else 0
termination_by w
decreasing_by
  have := Nat.mod_lt g ‹0 < w›
  have := Nat.div_add_mod' g w
  omega

/-- The extended Euclid algorithm makes exactly as many passes as the plain one. -/
theorem extEuclidSteps_eq (g w : ℕ) : extEuclidSteps g w = euclidSteps g w := by
  fun_induction extEuclidSteps g w with
  | case1 g w hw ih =>
    have : g - g / w * w = g % w := by
      have := Nat.div_add_mod' g w
      omega
    rw [ih, this, eq_comm, euclidSteps]
    simp [hw]
  | case2 g w hw => rw [euclidSteps]; simp [hw]

/-! ## Powering (Algorithm 2.1.5) -/

/-- The number of multiplications performed by `pow x n` (and of multiply-and-reduce
steps performed by `powMod x n m`): one squaring in the even branch, a squaring and a
multiplication in the odd branch. -/
def powCost (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else if n % 2 = 0 then powCost (n / 2) + 1
  else powCost ((n - 1) / 2) + 2
termination_by n
decreasing_by all_goals omega

/-- Algorithm 2.1.5 uses at most `2 log₂ n` multiplications. -/
theorem powCost_le (n : ℕ) : powCost n ≤ 2 * Nat.log 2 n := by
  fun_induction powCost n with
  | case1 n h => omega
  | case2 n h heven ih =>
    have h₁ : Nat.log 2 (n / 2) = Nat.log 2 n - 1 := Nat.log_div_base 2 n
    have h₂ : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
    omega
  | case3 n h hodd ih =>
    have h₁ : Nat.log 2 (n / 2) = Nat.log 2 n - 1 := Nat.log_div_base 2 n
    have h₂ : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
    rw [show (n - 1) / 2 = n / 2 by omega] at ih ⊢
    omega

/-! ## Jacobi symbol (Algorithm 2.3.5) -/

/-- The number of passes of the inner loop of Algorithm 2.3.5, following `jacobiHalve`. -/
def jacobiHalveSteps (a : ℕ) : ℕ :=
  if a ≠ 0 ∧ a % 2 = 0 then jacobiHalveSteps (a / 2) + 1 else 0
termination_by a
decreasing_by omega

theorem jacobiHalveSteps_le (a : ℕ) : jacobiHalveSteps a ≤ Nat.log 2 a := by
  fun_induction jacobiHalveSteps a with
  | case1 a h ih =>
    have h₁ : Nat.log 2 (a / 2) = Nat.log 2 a - 1 := Nat.log_div_base 2 a
    have h₂ : 0 < Nat.log 2 a := Nat.log_pos (by norm_num) (by omega)
    omega
  | case2 a h => omega

/-- The number of passes of the outer loop of Algorithm 2.3.5, following `jacobiLoop`. -/
def jacobiSteps (a m : ℕ) (t : ℤ) : ℕ :=
  if a = 0 then 0
  else
    let r := jacobiHalve a m t
    jacobiSteps (m % r.1) r.1 (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2) + 1
termination_by a
decreasing_by
  have := jacobiHalve_fst_le a m t
  have := Nat.mod_lt m (Nat.pos_of_ne_zero (jacobiHalve_fst_pos ‹a ≠ 0› m t))
  omega

/-- Algorithm 2.3.5 makes at most `log₂ (a m) + 1` passes of its outer loop when `a < m`
(as is the case after the initial `a = a mod m`): the product `a m` at least halves in
each pass. -/
theorem jacobiSteps_le (a m : ℕ) (t : ℤ) (ham : a < m) :
    jacobiSteps a m t ≤ if a = 0 then 0 else Nat.log 2 (a * m) + 1 := by
  fun_induction jacobiSteps a m t with
  | case1 m t => simp
  | case2 a m t ha r ih =>
    have hr_le : r.1 ≤ a := jacobiHalve_fst_le a m t
    have hr_pos : 0 < r.1 := Nat.pos_of_ne_zero (jacobiHalve_fst_pos ha m t)
    have hlt : m % r.1 < r.1 := Nat.mod_lt _ hr_pos
    have ih' : jacobiSteps (m % r.1) r.1 (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2) ≤
        if m % r.1 = 0 then 0 else Nat.log 2 (m % r.1 * r.1) + 1 := by
      simpa only [dite_eq_ite] using ih hlt
    simp only [ha, ↓reduceIte]
    by_cases h0 : m % r.1 = 0
    · rw [ite_eq_left h0] at ih'
      omega
    · rw [ite_eq_right h0] at ih'
      -- `m ≥ r + m mod r ≥ 2 (m mod r)`, so the new product is at most half the old one
      have hdm : r.1 * (m / r.1) + m % r.1 = m := Nat.div_add_mod m r.1
      have hq : r.1 ≤ r.1 * (m / r.1) :=
        Nat.le_mul_of_pos_right _ (Nat.div_pos (by omega) hr_pos)
      have h2 : m % r.1 * r.1 * 2 ≤ a * m :=
        calc m % r.1 * r.1 * 2 = r.1 * (2 * (m % r.1)) := by ring
          _ ≤ r.1 * m := Nat.mul_le_mul_left _ (by omega)
          _ ≤ a * m := Nat.mul_le_mul_right _ hr_le
      have hpos : m % r.1 * r.1 ≠ 0 := Nat.mul_ne_zero h0 hr_pos.ne'
      have hlog : Nat.log 2 (m % r.1 * r.1) + 1 ≤ Nat.log 2 (a * m) := by
        rw [← Nat.log_mul_base (by norm_num) hpos]
        exact Nat.log_mono_right h2
      omega

end PrimeNumbers.Chapter2
