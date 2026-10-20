import PrimeNumbers.Chapter9.FastMul

/-!
# §9.6.2 Fast polynomial inversion (Newton iteration)

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Algorithm 9.6.2.

Given `a(t)` whose constant term is invertible (with inverse `u`), Newton's iteration
`h ↦ h (2 - a h) mod t^(2K)` doubles the number of correct coefficients of `1/a` at each
step: `invNewton` returns `h` with `a h ≡ 1 (mod t^(2^k))` after `k` steps
(`invNewton_spec`).  Each step uses two multiplications, done by any multiplication
routine `mulF` that is proved correct (`MulCorrect`) — e.g. binary segmentation
(`mulMod`, Algorithm 9.6.1), so the whole inversion costs `O(M(D))`.

This is the ingredient of the fast remainder of Algorithm 9.6.4 (next step).
-/

namespace PrimeNumbers.Chapter9

open Polynomial PrimeNumbers.Chapter2 PrimeNumbers.Chapter2.Poly

variable {R : Type} [CommRing R]

/-- A multiplication routine on coefficient lists that computes the polynomial product. -/
def MulCorrect (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R) : Prop :=
  ∀ f g, toPolynomial (mulF f g) = toPolynomial f * toPolynomial g

theorem mulCorrect_mul : MulCorrect (Chapter2.Poly.mul (F := R)) := fun f g ↦ toPolynomial_mul f g

theorem mulCorrect_mulMod (n : ℕ) [NeZero n] : MulCorrect (mulMod n) :=
  fun f g ↦ toPolynomial_mulMod f g

/-- Truncation `L mod t^k` is `take k`. -/
theorem X_pow_dvd_sub_take (L : Chapter2.Poly R) (k : ℕ) :
    X ^ k ∣ toPolynomial L - toPolynomial (L.take k) := by
  have hL := congrArg toPolynomial (List.take_append_drop k L)
  rw [toPolynomial_append] at hL
  rw [← hL, add_sub_cancel_left]
  rcases Nat.lt_or_ge L.length k with h | h
  · rw [List.drop_eq_nil_of_le h.le]; simp
  · rw [List.length_take, min_eq_left h]
    exact dvd_mul_right _ _

/-- **Algorithm 9.6.2 (Newton iteration for `1/a mod t^(2^k)`)**, starting from the inverse
`u` of the constant term:
```
h = u;
for (1 ≤ i ≤ k) { K = 2^i;  h = h (2 - a h) mod t^K; }
```
-/
counted_def invNewton [ArithCost R] (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (a : Chapter2.Poly R)
    (u : R) : ℕ → Chapter2.Poly R
  | 0 => [u]
  | k + 1 =>
    let h := invNewton mulF a u k
    let e := (mulF a h).take (2 ^ (k + 1))
    (sub (smul 2 h) (mulF h e)).take (2 ^ (k + 1))

/-- **Correctness of Newton inversion**: `a h ≡ 1 (mod t^(2^k))`.  The step is the identity
`1 - a h (2 - a h) = (1 - a h)²`. -/
theorem invNewton_spec {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (hmul : MulCorrect mulF) (a : Chapter2.Poly R) {u : R} (hu : a.getD 0 0 * u = 1) (k : ℕ) :
    X ^ (2 ^ k) ∣ toPolynomial a * toPolynomial (invNewton mulF a u k) - 1 := by
  induction k with
  | zero =>
    rw [pow_zero, pow_one, X_dvd_iff]
    simp only [invNewton, toPolynomial_cons, toPolynomial_nil, mul_zero, add_zero,
      coeff_sub, mul_coeff_zero, coeff_C_zero, coeff_one_zero]
    rw [coeff_toPolynomial, hu, sub_self]
  | succ k ih =>
    simp only [invNewton]
    set H := toPolynomial (invNewton mulF a u k)
    set A := toPolynomial a
    obtain ⟨Q, hQ⟩ := ih
    obtain ⟨R₁, h₁⟩ := X_pow_dvd_sub_take (mulF a (invNewton mulF a u k)) (2 ^ (k + 1))
    obtain ⟨R₂, h₂⟩ := X_pow_dvd_sub_take
      (sub (smul 2 (invNewton mulF a u k))
        (mulF (invNewton mulF a u k) ((mulF a (invNewton mulF a u k)).take (2 ^ (k + 1)))))
      (2 ^ (k + 1))
    rw [hmul] at h₁
    rw [toPolynomial_sub, toPolynomial_smul, hmul] at h₂
    set E := toPolynomial ((mulF a (invNewton mulF a u k)).take (2 ^ (k + 1)))
    set H' := toPolynomial ((sub (smul 2 (invNewton mulF a u k))
      (mulF (invNewton mulF a u k) ((mulF a (invNewton mulF a u k)).take (2 ^ (k + 1))))).take
        (2 ^ (k + 1)))
    have hK : (X : R[X]) ^ 2 ^ (k + 1) = X ^ 2 ^ k * X ^ 2 ^ k := by
      rw [← pow_add, pow_succ]; ring_nf
    refine ⟨A * H * R₁ - A * R₂ - Q ^ 2, ?_⟩
    rw [hK] at h₁ h₂ ⊢
    simp only [map_ofNat] at h₂
    linear_combination (-A) * h₂ + (A * H) * h₁ -
      (2 * X ^ 2 ^ k * Q + (A * H - 1 - X ^ 2 ^ k * Q)) * hQ

/-! ## Running time -/

theorem length_invNewton_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (a : Chapter2.Poly R) (u : R) (k : ℕ) : (invNewton mulF a u k).length ≤ 2 ^ k := by
  cases k with
  | zero => simp [invNewton]
  | succ k => simp [invNewton]

/-- **Cost of Newton inversion (Algorithm 9.6.2)**: `k` iterations, each with two products
(by the routine `mulF`, whose charge `mc` is at most `M` on inputs of length `≤ D`), a
scaling, a subtraction and two truncations of polynomials of length `O(D)` (each
coefficient operation at most `s`), and a power of two, as long as `2^k ≤ D`. -/
theorem invNewton_cost_le [ArithCost R] (C : CostModel)
    {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (mc : Chapter2.Poly R → Chapter2.Poly R → CostM C Unit) {M s D : ℕ}
    (hM : ∀ f g : Chapter2.Poly R, f.length ≤ D → g.length ≤ D → CostM.cost C (mc f g) ≤ M)
    (hlen : ∀ f g : Chapter2.Poly R, (mulF f g).length ≤ f.length + g.length)
    (hs : ArithCost.Bounded R C s)
    (a : Chapter2.Poly R) (ha : a.length ≤ D) (u : R) (k : ℕ) (hk : 2 ^ k ≤ D) :
    CostM.cost C (invNewton.counted mulF a u k mc) ≤
      k * (2 * M + (11 * D + 9) * (C.unit + s) + 4 * C.lin (D.size + 2)) + C.unit := by
  induction k with
  | zero => cost_unfold invNewton.counted
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have ih := ih (by omega)
    cost_unfold invNewton.counted
    set h := invNewton mulF a u k
    have hh : h.length ≤ 2 ^ k := length_invNewton_le mulF a u k
    have hm₁ := hM a h ha (by omega)
    set e := (mulF a h).take (2 ^ (k + 1))
    have he : e.length ≤ 2 * D := by simp only [e, List.length_take]; omega
    have hm₂ := hM h e (by omega) (by simp only [e, List.length_take]; omega)
    have hl := hlen h e
    have hs₁ := Chapter2.Poly.smul_cost_le C hs 2 h
    have hs₂ := Chapter2.Poly.sub_cost_le C hs (Chapter2.Poly.smul 2 h) (mulF h e)
    simp only [Chapter2.Poly.length_smul] at hs₂
    -- the lengths, and the power of two, of at most `size D + 2` bits
    have hkD : k < D.size := Nat.lt_size.2 (by omega)
    have hp : (2 ^ (k + 1)).size ≤ D.size + 2 := by rw [Nat.size_pow]; omega
    have hk1 : (k + 1).size ≤ D.size + 2 := (Nat.size_le.2 Nat.lt_two_pow_self).trans (by omega)
    have hks : k.size ≤ D.size + 2 := (Nat.size_le.2 Nat.lt_two_pow_self).trans (by omega)
    have hDs : ∀ m, m ≤ 3 * D + 3 → m.size ≤ D.size + 2 := fun m hm ↦ Nat.size_le.2 (by
      have := Nat.lt_size_self D; rw [pow_add]; omega)
    have := hlen a h
    have := hDs h.length (by omega); have := hDs (mulF a h).length (by omega)
    have := hDs (mulF h e).length (by omega)
    have := hDs e.length (by omega); have := hDs (2 ^ (k + 1)) (by omega)
    have u₁ : (min (2 ^ (k + 1)) (mulF a h).length + 1) * C.unit ≤ (2 * D + 1) * C.unit :=
      Nat.mul_le_mul_right _ (by omega)
    have u₂ : (min (2 ^ (k + 1)) (Chapter2.Poly.sub (Chapter2.Poly.smul 2 h) (mulF h e)).length + 1)
        * C.unit ≤ (2 * D + 1) * C.unit := Nat.mul_le_mul_right _ (by omega)
    have v₁ : (h.length + 2) * (C.unit + s) ≤ (D + 2) * (C.unit + s) :=
      Nat.mul_le_mul_right _ (by omega)
    have v₂ : (max h.length (mulF h e).length + 1) * (C.unit + s) + ((mulF h e).length + 3) *
        (C.unit + s) ≤ (6 * D + 4) * (C.unit + s) := by
      have : max h.length (mulF h e).length + 1 + ((mulF h e).length + 3) ≤ 6 * D + 4 := by omega
      nlinarith
    cost_bound

end PrimeNumbers.Chapter9
