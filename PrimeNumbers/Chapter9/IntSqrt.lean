import PrimeNumbers.Chapter9.CountedLib

/-!
# §9.2.2 Integer square root by Newton's method

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Algorithm 9.2.11.

* `isqrt`            — Algorithm 9.2.11 (integer part of a square root).
* `isqrt_eq`         — it returns `⌊√N⌋` (Mathlib's `Nat.sqrt N`).
* `isqrtSteps_le`    — the Newton iteration runs at most `⌈k/2⌉ + 1` times, `k` the bit
                       length of `N`: each pass at least halves the distance to `⌊√N⌋`.
* `isqrtCost_le`, `isqrtCost_school_le` — hence at most `((k + 1)/2 + 2)(k + 1)²` bit
                       operations with grammar-school division.

The book states that `O(ln ln N)` iterations suffice (the convergence is quadratic), which
would give `O(ln² N · ln ln N)`; only the linear rate, giving `O(ln³ N)`, is proved here.
-/

namespace PrimeNumbers.Chapter9

/-- **Algorithm 9.2.11, step 2 [Perform Newton iteration]**:
```
y = ⌊(x + ⌊N/x⌋)/2⌋;
if (y ≥ x) return x;
x = y;
```
-/
counted_def isqrtLoop (N x : ℕ) : ℕ :=
  let y := (x + N / x) / 2
  if y < x then isqrtLoop N y else x
termination_by x

/-- **Algorithm 9.2.11 (Integer part of square root).**  Returns `⌊√N⌋`, starting the
Newton iteration from `x = 2^⌈B(N)/2⌉`, `B(N)` the number of bits of `N`. -/
counted_def isqrt (N : ℕ) : ℕ :=
  isqrtLoop N (2 ^ ((N.size + 1) / 2))

/-- One Newton step from any `x > 0` lands at or above `⌊√N⌋`: `N < (y + 1)²`. -/
theorem lt_newton_succ_sq (N : ℕ) {x : ℕ} (hx : 0 < x) :
    N < ((x + N / x) / 2 + 1) * ((x + N / x) / 2 + 1) := by
  have h₁ : N < x * (N / x + 1) := Nat.lt_mul_div_succ N hx
  have h₂ : x + (N / x + 1) ≤ 2 * ((x + N / x) / 2 + 1) := by omega
  -- AM–GM: `x (q + 1) ≤ ((x + q + 1)/2)²`
  have amgm : ∀ a b m : ℕ, a + b ≤ 2 * m → a * b ≤ m * m := by
    intro a b m hab
    zify at hab ⊢
    nlinarith [sq_nonneg ((a : ℤ) - b), mul_self_le_mul_self (by positivity) hab]
  have h₃ := amgm x (N / x + 1) ((x + N / x) / 2 + 1) h₂
  omega

theorem isqrtLoop_eq (N x : ℕ) (hx : 0 < x) (h : N < (x + 1) * (x + 1)) :
    isqrtLoop N x = Nat.sqrt N := by
  fun_induction isqrtLoop N x with
  | case1 x y hlt ih =>
    rcases Nat.eq_zero_or_pos y with h0 | hpos
    · -- the next iterate is `0`: then `N = 0`
      have hN : N = 0 := by
        have := lt_newton_succ_sq N hx
        simp only [y] at h0
        rw [h0] at this
        omega
      rw [h0, isqrtLoop]
      simp [hN]
    · exact ih hpos (lt_newton_succ_sq N hx)
  | case2 x y hge =>
    -- on exit `⌊N/x⌋ ≥ x`, so `x² ≤ N < (x + 1)²`
    have hq : x ≤ N / x := by simp only [y] at hge; omega
    have hsq : x * x ≤ N := (Nat.mul_le_mul_left x hq).trans (Nat.mul_div_le N x)
    exact Nat.eq_sqrt.mpr ⟨hsq, h⟩

/-- **Correctness of Algorithm 9.2.11**: `isqrt N = ⌊√N⌋`. -/
theorem isqrt_eq (N : ℕ) : isqrt N = Nat.sqrt N := by
  refine isqrtLoop_eq N _ (by positivity) ?_
  -- `N < 2^k ≤ (2^⌈k/2⌉)²`
  have h₁ : N < 2 ^ N.size := Nat.lt_size_self N
  have h₂ : 2 ^ N.size ≤ 2 ^ ((N.size + 1) / 2) * 2 ^ ((N.size + 1) / 2) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith [Nat.zero_le (2 ^ ((N.size + 1) / 2))]

/-- `Nat.sqrt` is computed by Algorithm 9.2.11: a call of `Nat.sqrt` in a `counted_def` is
charged as `isqrt`. -/
def _root_.Nat.sqrt.counted {m : Type → Type} [Monad m] [NatArith m] (N : ℕ) : m ℕ :=
  isqrt.counted N

/-! ## Running time -/

/-- The number of Newton steps taken by `isqrtLoop N x` (each pass makes one division). -/
def isqrtSteps (N x : ℕ) : ℕ :=
  if (x + N / x) / 2 < x then isqrtSteps N ((x + N / x) / 2) + 1 else 0
termination_by x

theorem size_div_two_add_one_le {d : ℕ} (hd : 0 < d) : (d / 2).size + 1 ≤ d.size := by
  have hpos : 0 < d.size := Nat.size_pos.mpr hd
  have h₁ : d < 2 ^ d.size := Nat.lt_size_self d
  have h₂ : d / 2 < 2 ^ (d.size - 1) := by
    have : 2 ^ d.size = 2 * 2 ^ (d.size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have := Nat.size_le.mpr h₂
  omega

/-- Each Newton step at least halves the distance to `s = ⌊√N⌋`, so there are at most
`size (x - s)` steps. -/
theorem isqrtSteps_le_size (N x : ℕ) (hx : 0 < x) (h : N < (x + 1) * (x + 1)) :
    isqrtSteps N x ≤ (x - Nat.sqrt N).size := by
  fun_induction isqrtSteps N x with
  | case1 x hlt ih =>
    -- here `x > s`: otherwise `N/x ≥ x` and the step would not decrease
    have hxs : Nat.sqrt N < x := by
      by_contra hle
      have h₁ : x * x ≤ N := (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.sqrt_le N)
      have h₂ : x ≤ N / x := (Nat.le_div_iff_mul_le hx).mpr h₁
      omega
    -- `⌊N/x⌋ ≤ s`
    have hq : N / x ≤ Nat.sqrt N := by
      have h₁ : N < (Nat.sqrt N + 1) * x :=
        (Nat.lt_succ_sqrt N).trans_le (Nat.mul_le_mul_left _ hxs)
      have := (Nat.div_lt_iff_lt_mul hx).mpr h₁
      omega
    have hhalf : (x + N / x) / 2 - Nat.sqrt N ≤ (x - Nat.sqrt N) / 2 := by omega
    have hstep := size_div_two_add_one_le (d := x - Nat.sqrt N) (by omega)
    rcases Nat.eq_zero_or_pos ((x + N / x) / 2) with h0 | hpos
    · rw [h0, isqrtSteps]
      simp only [Nat.zero_div, Nat.zero_add, Nat.div_zero, lt_self_iff_false, ↓reduceIte]
      omega
    · have ih := ih hpos (lt_newton_succ_sq N hx)
      have := Nat.size_le_size hhalf
      omega
  | case2 x hge => exact Nat.zero_le _

/-- **Algorithm 9.2.11 makes at most `⌈k/2⌉ + 1` Newton steps**, `k` the bit length of `N`. -/
theorem isqrtSteps_le (N : ℕ) : isqrtSteps N (2 ^ ((N.size + 1) / 2)) ≤ (N.size + 1) / 2 + 1 := by
  have h₁ : N < 2 ^ N.size := Nat.lt_size_self N
  have h₂ : 2 ^ N.size ≤ 2 ^ ((N.size + 1) / 2) * 2 ^ ((N.size + 1) / 2) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (isqrtSteps_le_size N _ (by positivity)
    (by nlinarith [Nat.zero_le (2 ^ ((N.size + 1) / 2))])).trans ?_
  refine (Nat.size_le_size (Nat.sub_le _ _)).trans ?_
  rw [Nat.size_pow]

/-- Each pass costs one division by a number no longer than the starting value. -/
theorem isqrtCost_le (C : CostModel) {N X B : ℕ}
    (hB : ∀ b ≤ X.size, C.divMod N.size b ≤ B) (x : ℕ) (hx : x ≤ X) :
    costOf C (isqrtLoop N x) ≤ (isqrtSteps N x + 1) * B := by
  induction x using Nat.strong_induction_on with | _ x ih =>
  have := hB x.size (Nat.size_le_size hx)
  rw [isqrtSteps]
  by_cases hlt : (x + N / x) / 2 < x
  · have ih := ih _ hlt (by omega)
    cost_unfold isqrtLoop.counted
    simp only [hlt, ↓reduceIte, add_mul, one_mul] at ih ⊢; omega
  · cost_unfold isqrtLoop.counted
    simp only [hlt, ↓reduceIte] at *; omega

/-- **Bit complexity of Algorithm 9.2.11, grammar-school division**: at most
`((k + 1)/2 + 2)(k + 1)²` bit operations for a `k`-bit `N`. -/
theorem isqrtCost_school_le (N : ℕ) :
    costOf school (isqrtLoop N (2 ^ ((N.size + 1) / 2))) ≤
      ((N.size + 1) / 2 + 2) * (N.size + 1) ^ 2 := by
  have hsteps := isqrtSteps_le N
  have hX : (2 ^ ((N.size + 1) / 2)).size = (N.size + 1) / 2 + 1 := Nat.size_pow
  refine (isqrtCost_le school (X := 2 ^ ((N.size + 1) / 2)) (B := (N.size + 1) ^ 2)
    (fun b hb ↦ ?_) _ le_rfl).trans (Nat.mul_le_mul_right _ (by omega))
  rw [hX] at hb
  change (N.size - b + 1) * b ≤ (N.size + 1) ^ 2
  rw [sq]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The cost charged for a call of `Nat.sqrt` in a counted algorithm. -/
theorem sqrt_counted_cost (C : CostModel) (N : ℕ) :
    CostM.cost C (Nat.sqrt.counted N) = costOf C (isqrtLoop N (2 ^ ((N.size + 1) / 2))) := by
  simp only [Nat.sqrt.counted, isqrt.counted]; cost_simp

/-- The bound of `isqrtCost_school_le` as a function of the bit length `k`: a valid
"square root cost" for analyses that use integer square roots. -/
def schoolSqrt (k : ℕ) : ℕ := ((k + 1) / 2 + 2) * (k + 1) ^ 2

theorem schoolSqrt_mono : Monotone schoolSqrt := fun a b h ↦
  Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)

/-- In the grammar-school model a call of `Nat.sqrt` on a `k`-bit number costs at most
`schoolSqrt k`. -/
theorem sqrt_counted_cost_school_le (N : ℕ) :
    CostM.cost school (Nat.sqrt.counted N) ≤ schoolSqrt N.size := by
  rw [sqrt_counted_cost]; exact isqrtCost_school_le N

end PrimeNumbers.Chapter9
