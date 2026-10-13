import PrimeNumbers.Chapter9.BitCost
import Mathlib

/-!
# §2.1.1 Greatest common divisor and inverse

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.1.1.

* `theorem_2_1_1`      — Theorem 2.1.1, the linear relation `a x + b y = gcd(x, y)`.
* `euclid`             — Algorithm 2.1.2, the Euclid algorithm; `euclid_eq_gcd`.
* `euclidSteps`        — the number of loop iterations of Algorithm 2.1.2, with
                         `lame`, the worst-case half of Theorem 2.1.3 (Lamé).
* `extEuclid`          — Algorithm 2.1.4, the extended Euclid algorithm; `extEuclid_spec`.
* `modInv`             — the inverse `x⁻¹ mod m` obtained from Algorithm 2.1.4.

All algorithms are ordinary compiled Lean functions on `ℕ`/`ℤ` (arbitrary precision,
GMP-backed) and the theorems are about exactly these functions.
-/

namespace PrimeNumbers.Chapter2

/-- **Theorem 2.1.1 (Linear relation for gcd).**  If `x, y` are integers, not both `0`,
then there are integers `a, b` with `a x + b y = gcd(x, y)`.
(The hypothesis "not both 0" is not actually needed.) -/
theorem theorem_2_1_1 (x y : ℤ) : ∃ a b : ℤ, a * x + b * y = Int.gcd x y :=
  ⟨Int.gcdA x y, Int.gcdB x y, by rw [Int.gcd_eq_gcd_ab]; ring⟩

/-! ## Algorithm 2.1.2 (Euclid algorithm for greatest common divisor) -/

/-- **Algorithm 2.1.2.**
```
while (y > 0) (x, y) = (y, x mod y);
return x;
```
-/
def euclid (x y : ℕ) : ℕ :=
  if 0 < y then euclid y (x % y) else x
termination_by y
decreasing_by exact Nat.mod_lt _ ‹0 < y›

/-- Algorithm 2.1.2 returns `gcd(x, y)`.  (The book's precondition `x ≥ y`, `x > 0`
is not needed for correctness.) -/
theorem euclid_eq_gcd (x y : ℕ) : euclid x y = Nat.gcd x y := by
  fun_induction euclid x y with
  | case1 x y hy ih => rw [ih, Nat.gcd_comm x y, Nat.gcd_rec y x, Nat.gcd_comm]
  | case2 x y hy => rw [Nat.eq_zero_of_not_pos hy, Nat.gcd_zero_right]

/-! ## Theorem 2.1.3 (Lamé) -/

/-- The number of iterations of the loop in Algorithm 2.1.2 on input `(x, y)`. -/
def euclidSteps (x y : ℕ) : ℕ :=
  if 0 < y then euclidSteps y (x % y) + 1 else 0
termination_by y
decreasing_by exact Nat.mod_lt _ ‹0 < y›

/-- Key lemma behind Lamé's theorem: if the Euclid loop runs `n` steps on `x > y`, then
`y ≥ F_n` and `x ≥ F_{n+1}`, where `F` is the Fibonacci sequence. -/
theorem fib_le_of_euclidSteps (x y : ℕ) (hxy : y < x) :
    Nat.fib (euclidSteps x y) ≤ y ∧ Nat.fib (euclidSteps x y + 1) ≤ x := by
  fun_induction euclidSteps x y with
  | case1 x y hy ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (Nat.mod_lt _ hy)
    refine ⟨ih₂, ?_⟩
    -- `x = q y + (x mod y)` with `q ≥ 1`, so `x ≥ y + x mod y ≥ F_{n+1} + F_n`
    have hq : 1 ≤ x / y := Nat.div_pos hxy.le hy
    have hx : y * (x / y) + x % y = x := Nat.div_add_mod x y
    have : y ≤ y * (x / y) := Nat.le_mul_of_pos_right y hq
    rw [Nat.fib_add_two]
    omega
  | case2 x y hy => simp; omega

/-- **Theorem 2.1.3 (Lamé), worst case.**  Let `x > y` be integers in `[1, N]`.  If the
loop of the Euclid algorithm 2.1.2 runs `n` steps then `F_{n+1} ≤ N`.

Since `F_{n+1} ≥ φ^{n-1}` with `φ = (1+√5)/2`, this is the book's bound
`n ≤ ⌈ln(N√5)/ln φ⌉ - 2` up to the conversion from Fibonacci numbers to logarithms.
The average-case assertion of Theorem 2.1.3 (Dixon, Heilbronn) is not formalized. -/
theorem lame {x y N : ℕ} (hxy : y < x) (hN : x ≤ N) :
    Nat.fib (euclidSteps x y + 1) ≤ N :=
  (fib_le_of_euclidSteps x y hxy).2.trans hN

/-! ## Algorithm 2.1.4 (Euclid's algorithm extended, for gcd and inverse) -/

/-- The loop of Algorithm 2.1.4:
```
while (w > 0) {
  q = ⌊g/w⌋;
  (a, b, g, u, v, w) = (u, v, w, a - q u, b - q v, g - q w);
}
return (a, b, g);
```
-/
def extEuclidLoop (a b : ℤ) (g : ℕ) (u v : ℤ) (w : ℕ) : ℤ × ℤ × ℕ :=
  if 0 < w then
    let q := g / w
    extEuclidLoop u v w (a - q * u) (b - q * v) (g - q * w)
  else (a, b, g)
termination_by w
decreasing_by
  have := Nat.mod_lt g ‹0 < w›
  have := Nat.div_add_mod' g w
  omega

/-- **Algorithm 2.1.4.**  Returns `(a, b, g)` with `a x + b y = g = gcd(x, y)`. -/
def extEuclid (x y : ℕ) : ℤ × ℤ × ℕ :=
  extEuclidLoop 1 0 x 0 1 y

/-- Loop invariant of Algorithm 2.1.4: the relations `a x + b y = g` and `u x + v y = w`
are preserved, and the loop ends with `g = gcd(g, w)`. -/
theorem extEuclidLoop_spec (x y : ℤ) (a b : ℤ) (g : ℕ) (u v : ℤ) (w : ℕ)
    (h₁ : a * x + b * y = g) (h₂ : u * x + v * y = w) :
    let r := extEuclidLoop a b g u v w
    r.1 * x + r.2.1 * y = r.2.2 ∧ r.2.2 = Nat.gcd g w := by
  fun_induction extEuclidLoop a b g u v w with
  | case1 a b g u v w hw q ih =>
    have hq : q * w ≤ g := Nat.div_mul_le_self g w
    have hmod : g - q * w = g % w := by
      have : g / w * w + g % w = g := Nat.div_add_mod' g w
      have : q * w = g / w * w := rfl
      omega
    obtain ⟨ih₁, ih₂⟩ := ih h₂ (by push_cast [Nat.cast_sub hq]; linear_combination h₁ - q * h₂)
    exact ⟨ih₁, by rw [ih₂, hmod, Nat.gcd_comm g w, Nat.gcd_rec w g, Nat.gcd_comm]⟩
  | case2 a b g u v w hw =>
    exact ⟨h₁, by rw [Nat.eq_zero_of_not_pos hw, Nat.gcd_zero_right]⟩

/-- **Correctness of Algorithm 2.1.4.**  For `(a, b, g) = extEuclid x y` we have
`a x + b y = g = gcd(x, y)`. -/
theorem extEuclid_spec (x y : ℕ) :
    (extEuclid x y).1 * x + (extEuclid x y).2.1 * y = (extEuclid x y).2.2 ∧
      (extEuclid x y).2.2 = Nat.gcd x y :=
  extEuclidLoop_spec x y 1 0 x 0 1 y (by ring) (by ring)

/-! ## Modular inverse -/

/-- The inverse `x⁻¹ mod m`, read off from Algorithm 2.1.4 as "`a mod m`". -/
def modInv (x m : ℕ) : ℕ :=
  ((extEuclid x m).1 % m).toNat

theorem modInv_lt (x : ℕ) {m : ℕ} (hm : 0 < m) : modInv x m < m := by
  have h₀ : 0 ≤ (extEuclid x m).1 % m := Int.emod_nonneg _ (by positivity)
  have h₁ : (extEuclid x m).1 % m < m := Int.emod_lt_of_pos _ (by positivity)
  unfold modInv
  omega

/-- When `gcd(x, m) = 1`, `modInv x m` is an inverse of `x` modulo `m`. -/
theorem mul_modInv_modEq {x m : ℕ} (h : Nat.Coprime x m) : x * modInv x m ≡ 1 [MOD m] := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp_all [modInv, extEuclid, extEuclidLoop, Nat.ModEq]
  obtain ⟨h₁, h₂⟩ := extEuclid_spec x m
  rw [h] at h₂
  rw [← Int.natCast_modEq_iff]
  have hcast : ((modInv x m : ℕ) : ℤ) = (extEuclid x m).1 % m :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  push_cast
  rw [hcast]
  calc (x : ℤ) * ((extEuclid x m).1 % m)
      ≡ x * (extEuclid x m).1 [ZMOD m] := (Int.mod_modEq _ _).mul_left _
    _ ≡ x * (extEuclid x m).1 + (extEuclid x m).2.1 * m [ZMOD m] := by
        simp
    _ = 1 := by rw [← Nat.cast_one, ← h₂, ← h₁]; ring
/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Number of loop passes -/

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

/-! ### Bit operations -/

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

end RunningTime

end PrimeNumbers.Chapter2
