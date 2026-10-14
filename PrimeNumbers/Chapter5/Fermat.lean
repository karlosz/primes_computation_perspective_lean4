import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter9.IntSqrt
import Mathlib

/-!
# §5.1.1 Fermat method

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.1.1.

* `fermat`            — Algorithm 5.1.1 (Fermat method): look for `a` with `a² - n` a square.
* `fermat_sound`      — a returned `d` is a nontrivial divisor of `n` (for `n > 3`);
* `fermat_none_prime` — if the algorithm returns nothing, the odd number `n` is prime.

Together: for odd `n > 3` the algorithm "either produces a nontrivial divisor of `n` or
proves `n` prime".  (For `n = 3` the loop as printed returns the trivial divisor `1`.)
-/

namespace PrimeNumbers.Chapter5

/-- `⌈√n⌉`. -/
counted_def ceilSqrt (n : ℕ) : ℕ :=
  let s := Nat.sqrt n
  if s * s = n then s else s + 1

theorem le_ceilSqrt_mul_self (n : ℕ) : n ≤ ceilSqrt n * ceilSqrt n := by
  unfold ceilSqrt; dsimp only
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt n).le

theorem ceilSqrt_le {n a : ℕ} (h : n ≤ a * a) : ceilSqrt n ≤ a := by
  have h₁ : Nat.sqrt n ≤ a := by
    have := Nat.sqrt_le_sqrt h
    rwa [Nat.sqrt_eq] at this
  unfold ceilSqrt; dsimp only
  split_ifs with hsq
  · exact h₁
  · rcases Nat.lt_or_ge (Nat.sqrt n) a with hlt | hge
    · exact hlt
    · obtain rfl : a = Nat.sqrt n := by omega
      exact absurd (le_antisymm (Nat.sqrt_le n) h) hsq

/-- The loop of Algorithm 5.1.1, for `a, a + 1, …` (`fuel` values):
```
if b = √(a² - n) is an integer return a - b;
```
-/
counted_def fermatLoop (n a : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    let t := a * a - n
    let b := Nat.sqrt t
    if b * b = t then some (a - b) else fermatLoop n (a + 1) fuel

/-- **Algorithm 5.1.1 (Fermat method).**  Given an odd integer `n > 1`, either produces a
nontrivial divisor of `n` (`some d`) or proves `n` prime (`none`).
```
for (⌈√n⌉ ≤ a ≤ (n + 9)/6) { if b = √(a² - n) is an integer return a - b; }
return "n is prime";
```
-/
counted_def fermat (n : ℕ) : Option ℕ :=
  let a := ceilSqrt n
  fermatLoop n a ((n + 9) / 6 + 1 - a)

theorem fermatLoop_some {n a fuel d : ℕ} (h : fermatLoop n a fuel = some d) :
    ∃ a' b, a ≤ a' ∧ a' < a + fuel ∧ a' * a' - n = b * b ∧ d = a' - b := by
  induction fuel generalizing a with
  | zero => simp [fermatLoop] at h
  | succ fuel ih =>
    simp only [fermatLoop] at h
    split_ifs at h with hsq
    · exact ⟨a, Nat.sqrt (a * a - n), le_rfl, by omega, hsq.symm, (Option.some.inj h).symm⟩
    · obtain ⟨a', b, h₁, h₂, h₃, h₄⟩ := ih h
      exact ⟨a', b, by omega, by omega, h₃, h₄⟩

theorem fermatLoop_isSome {n a fuel : ℕ}
    (h : ∃ a' b, a ≤ a' ∧ a' < a + fuel ∧ a' * a' - n = b * b) :
    (fermatLoop n a fuel).isSome := by
  induction fuel generalizing a with
  | zero => obtain ⟨a', b, h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    simp only [fermatLoop]
    split_ifs with hsq
    · rfl
    · obtain ⟨a', b, h₁, h₂, h₃⟩ := h
      have hne : a' ≠ a := by
        rintro rfl
        exact hsq (by rw [h₃, Nat.sqrt_eq])
      exact ih ⟨a', b, by omega, by omega, h₃⟩

/-- **Soundness of Algorithm 5.1.1**: for `n > 3`, a returned `d` is a nontrivial divisor
of `n`.  Indeed `d = a - b` where `n = a² - b² = (a - b)(a + b)` and `a ≤ (n + 9)/6`. -/
theorem fermat_sound {n d : ℕ} (hn : 3 < n) (h : fermat n = some d) :
    d ∣ n ∧ 1 < d ∧ d < n := by
  obtain ⟨a, b, h₁, h₂, h₃, rfl⟩ := fermatLoop_some h
  have hna : n ≤ a * a := (le_ceilSqrt_mul_self n).trans (Nat.mul_le_mul h₁ h₁)
  have ha : a ≤ (n + 9) / 6 := by omega
  -- `n = a² - b² = (a + b)(a - b)`
  have hsq : a * a = n + b * b := by omega
  have hba : b ≤ a := by
    by_contra hlt
    have : a * a < b * b := Nat.mul_lt_mul'' (by omega) (by omega)
    omega
  have hfac : n = (a + b) * (a - b) := by
    rw [← Nat.mul_self_sub_mul_self_eq]; omega
  have hd0 : a - b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfac
    omega
  refine ⟨⟨a + b, by rw [mul_comm]; exact hfac⟩, ?_, by omega⟩
  -- `a - b = 1` would force `a = (n + 1)/2 > (n + 9)/6`
  by_contra hd1
  have h1 : a - b = 1 := by omega
  rw [h1, mul_one] at hfac
  omega

/-- For odd `3 ≤ u ≤ v`, the loop stops on `n = u v`: `a = (u + v)/2` satisfies
`a² - n = ((v - u)/2)²` and `⌈√n⌉ ≤ a ≤ (n + 9)/6`. -/
theorem fermat_isSome_mul {u v : ℕ} (hu : 3 ≤ u) (hu2 : u % 2 = 1) (hv2 : v % 2 = 1)
    (huv : u ≤ v) : (fermat (u * v)).isSome := by
  -- `u = 2x + 1`, `v = 2x + 2e + 1` with `x ≥ 1`
  obtain ⟨x, rfl⟩ : ∃ x, u = 2 * (x + 1) + 1 := ⟨(u - 3) / 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, v = 2 * (x + 1) + 2 * e + 1 := ⟨(v - (2 * (x + 1) + 1)) / 2, by omega⟩
  have hkey : (2 * (x + 1) + e + 1) * (2 * (x + 1) + e + 1) -
      (2 * (x + 1) + 1) * (2 * (x + 1) + 2 * e + 1) = e * e :=
    Nat.sub_eq_of_eq_add (by ring)
  have hge : (2 * (x + 1) + 1) * (2 * (x + 1) + 2 * e + 1) ≤
      (2 * (x + 1) + e + 1) * (2 * (x + 1) + e + 1) := by nlinarith
  have hbound : 6 * (2 * (x + 1) + e + 1) ≤
      (2 * (x + 1) + 1) * (2 * (x + 1) + 2 * e + 1) + 9 := by nlinarith
  have hceil := ceilSqrt_le hge
  exact fermatLoop_isSome ⟨2 * (x + 1) + e + 1, e, hceil, by omega, hkey⟩

/-- **Completeness of Algorithm 5.1.1**: if it returns nothing, the odd number `n > 1` is
prime. -/
theorem fermat_none_prime {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (h : fermat n = none) :
    n.Prime := by
  by_contra hnp
  obtain ⟨u, v, hu, hv, rfl⟩ := (Nat.not_prime_iff_exists_mul_eq hn).mp hnp
  have odd_of : ∀ a b : ℕ, (a * b) % 2 = 1 → a % 2 = 1 := by
    intro a b hab
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · rw [Nat.mul_mod, h0] at hab; simp at hab
    · exact h1
  have hu2 : u % 2 = 1 := odd_of u v hodd
  have hv2 : v % 2 = 1 := odd_of v u (by rwa [mul_comm])
  have hu3 : 3 ≤ u := by
    have : u ≠ 1 := by rintro rfl; omega
    omega
  have hv3 : 3 ≤ v := by
    have : v ≠ 1 := by rintro rfl; omega
    omega
  have hsome : (fermat (u * v)).isSome := by
    rcases le_total u v with huv | hvu
    · exact fermat_isSome_mul hu3 hu2 hv2 huv
    · rw [mul_comm]; exact fermat_isSome_mul hv3 hv2 hu2 hvu
  rw [h] at hsome
  exact absurd hsome (by simp)

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-- Each pass costs two multiplications of numbers `≤ A` and a square root of a number of at
most `2 size A` bits; the cost of a square root of a `k`-bit number is bounded by `sq k`. -/
theorem fermatCost_le (C : CostModel) {sq : ℕ → ℕ} (hsq : Monotone sq)
    (hS : ∀ t, CostM.cost C (Nat.sqrt.counted t) ≤ sq t.size) {n a A : ℕ} (fuel : ℕ)
    (h : a + fuel ≤ A + 1) :
    costOf C (fermatLoop n a fuel) ≤ fuel * (2 * C.mul A.size A.size + sq (2 * A.size)) := by
  induction fuel generalizing a with
  | zero => cost_unfold fermatLoop.counted
  | succ fuel ih =>
    have haA : a ≤ A := by omega
    have ih := ih (a := a + 1) (by omega)
    have hb : Nat.sqrt (a * a - n) ≤ a := by
      have := Nat.sqrt_le_sqrt (Nat.sub_le (a * a) n)
      rwa [Nat.sqrt_eq] at this
    have h₁ : C.mul a.size a.size ≤ C.mul A.size A.size :=
      C.mul_mono (Nat.size_le_size haA) (Nat.size_le_size haA)
    have h₂ : C.mul (Nat.sqrt (a * a - n)).size (Nat.sqrt (a * a - n)).size ≤
        C.mul A.size A.size :=
      C.mul_mono (Nat.size_le_size (hb.trans haA)) (Nat.size_le_size (hb.trans haA))
    have h₃ : sq (a * a - n).size ≤ sq (2 * A.size) := hsq (by
      have := Nat.size_le_size (Nat.sub_le (a * a) n)
      have := size_mul_le a a
      have := Nat.size_le_size haA
      omega)
    have h₄ := hS (a * a - n)
    cost_unfold fermatLoop.counted
    simp only [add_mul, one_mul]
    split_ifs <;> omega

/-- **Bit complexity of the Fermat method.**  Algorithm 5.1.1 makes at most
`(n + 9)/6 + 1 - ⌈√n⌉` passes, each costing two multiplications and one integer square
root of numbers no longer than `n` squared: `O(n)` passes in the worst case — "much more
tedious than trial division", as the book says. -/
theorem fermatCost_le' (C : CostModel) {sq : ℕ → ℕ} (hsq : Monotone sq)
    (hS : ∀ t, CostM.cost C (Nat.sqrt.counted t) ≤ sq t.size) {n : ℕ} (hn : 2 ≤ n) :
    costOf C (fermatLoop n (ceilSqrt n) ((n + 9) / 6 + 1 - ceilSqrt n)) ≤
      ((n + 9) / 6 + 1 - ceilSqrt n) * (2 * C.mul n.size n.size + sq (2 * n.size)) := by
  rcases Nat.lt_or_ge ((n + 9) / 6 + 1) (ceilSqrt n) with hlt | hge
  · rw [show (n + 9) / 6 + 1 - ceilSqrt n = 0 by omega]
    cost_unfold fermatLoop.counted
  · refine (fermatCost_le C hsq hS (A := (n + 9) / 6) _ (by omega)).trans
      (Nat.mul_le_mul_left _ ?_)
    have hA : ((n + 9) / 6).size ≤ n.size := Nat.size_le_size (by omega)
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (C.mul_mono hA hA)) (hsq (by omega))

/-- **Bit complexity of the Fermat method, grammar-school arithmetic**, with the integer
square roots computed by Algorithm 9.2.11 (`isqrtCost_school_le`): at most
`((n + 9)/6 + 1 - ⌈√n⌉) · (2k² + schoolSqrt (2k))` bit operations, `k` the bit length of
`n` — that is `O(n ln³ n)` in the worst case. -/
theorem fermatCost_school_le {n : ℕ} (hn : 2 ≤ n) :
    costOf school (fermatLoop n (ceilSqrt n) ((n + 9) / 6 + 1 - ceilSqrt n)) ≤
      ((n + 9) / 6 + 1 - ceilSqrt n) * (2 * (n.size * n.size) + schoolSqrt (2 * n.size)) :=
  fermatCost_le' school schoolSqrt_mono sqrt_counted_cost_school_le hn

end RunningTime

end PrimeNumbers.Chapter5
