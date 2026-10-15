import PrimeNumbers.Chapter9.Newton
import PrimeNumbers.Chapter9.Multipoint

/-!
# §9.6.4 Fast polynomial remainder

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Algorithm 9.6.4.

To reduce `f` (`N` coefficients) modulo a monic `g` of degree `m`, reverse the
coefficient lists: the reversed quotient is `rev f · (rev g)⁻¹ mod t^(N-m)`, and
`(rev g)⁻¹` comes from Newton iteration (Algorithm 9.6.2) because `rev g` has constant term
`1`.  Then `f mod g = f - q g`.  With a fast multiplication this costs `O(M(N))` instead
of the `O(N m)` of long division.

* `fastModMonic` — Algorithm 9.6.4, for any proved-correct multiplication `mulF`.
* `toPolynomial_fastModMonic` — it computes Mathlib's `%ₘ`, like `Poly.modMonic`.

The proof uses Mathlib's `Polynomial.reflect` (`reflect_mul`, `reflect_sub`): reversing
`f - q g` gives `rev f - rev q · rev g`, which vanishes modulo `t^(N-m)`, so the top
`N - m` coefficients of `f - q g` vanish.
-/

namespace PrimeNumbers.Chapter9

open Polynomial PrimeNumbers.Chapter2 PrimeNumbers.Chapter2.Poly

variable {R : Type} [CommRing R]

theorem natDegree_toPolynomial_le (L : Chapter2.Poly R) :
    (toPolynomial L).natDegree ≤ L.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPolynomial, List.getD_eq_default _ _ (by
    have : L.length - 1 < N := by exact_mod_cast hN
    omega)]

/-- Reversing the coefficient list is `reflect (len - 1)`. -/
theorem toPolynomial_reverse (L : Chapter2.Poly R) :
    toPolynomial L.reverse = reflect (L.length - 1) (toPolynomial L) := by
  ext i
  rw [coeff_reflect, coeff_toPolynomial, coeff_toPolynomial]
  rcases Nat.lt_or_ge i L.length with h | h
  · rw [revAt_le (by omega), List.getD_eq_getElem?_getD, List.getElem?_reverse h,
      List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    rcases Nat.eq_zero_or_pos L.length with h0 | hpos
    · rw [List.length_eq_zero_iff.mp h0]; simp
    · rw [revAt_eq_self_of_lt (by omega), List.getD_eq_default _ _ (by omega)]

theorem toPolynomial_replicate_zero (j : ℕ) :
    toPolynomial (List.replicate j (0 : R)) = 0 := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, ih]

theorem coeff_toPolynomial_take (L : Chapter2.Poly R) (m j : ℕ) :
    (toPolynomial (L.take m)).coeff j = if j < m then (toPolynomial L).coeff j else 0 := by
  rw [coeff_toPolynomial, coeff_toPolynomial, List.getD_eq_getElem?_getD,
    List.getElem?_take, List.getD_eq_getElem?_getD]
  split_ifs <;> simp

/-- **Algorithm 9.6.4 (Fast polynomial remainder)** by a monic `g`:
```
k = N - m;
q = rev( rev(f) · rev(g)⁻¹ mod t^k );      // inverse by Newton iteration
return f - q g;
```
-/
counted_def fastModMonic [MulCost R] (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (f g : Chapter2.Poly R) : Chapter2.Poly R :=
  if f.length ≤ g.length - 1 then f
  else
    let k := f.length - (g.length - 1)
    let inv := invNewton mulF g.reverse 1 (Nat.clog 2 k)
    let rq := (mulF f.reverse inv).take k
    let q := (rq ++ List.replicate (k - rq.length) 0).reverse
    (sub f (mulF q g)).take (g.length - 1)

/-- **Correctness of Algorithm 9.6.4**: it computes the remainder `f %ₘ g`. -/
theorem toPolynomial_fastModMonic [Nontrivial R]
    {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R} (hmul : MulCorrect mulF)
    (f : Chapter2.Poly R) {g : Chapter2.Poly R} (hg : lead g = 1) :
    toPolynomial (fastModMonic mulF f g) = toPolynomial f %ₘ toPolynomial g := by
  have hgne : g ≠ [] := by rintro rfl; simp [lead] at hg
  have hmon := Poly.monic_toPolynomial hg
  have hdegG := Poly.natDegree_toPolynomial_of_lead hg
  set m := g.length - 1 with hm
  set F := toPolynomial f
  set G := toPolynomial g
  unfold fastModMonic
  split_ifs with hNm
  · -- `deg f < m`: nothing to do
    refine ((modByMonic_eq_self_iff hmon).mpr ?_).symm
    rw [degree_eq_natDegree hmon.ne_zero, hdegG]
    exact (degree_toPolynomial_lt f).trans_le (by exact_mod_cast hNm)
  · set N := f.length
    set k := N - m with hk
    have hk1 : 1 ≤ k := by omega
    set inv := invNewton mulF g.reverse 1 (Nat.clog 2 k)
    set rq := (mulF f.reverse inv).take k
    set q := (rq ++ List.replicate (k - rq.length) 0).reverse
    set Q := toPolynomial q
    -- reversed polynomials
    have hrqlen : rq.length ≤ k := by simp [rq]
    have hq_len : q.length = k := by simp [q]; omega
    have hRQ : reflect (k - 1) Q = toPolynomial rq := by
      have := toPolynomial_reverse q
      rw [hq_len] at this
      rw [← this]
      simp only [q, List.reverse_reverse, toPolynomial_append, toPolynomial_replicate_zero,
        mul_zero, add_zero]
    have hRF : reflect (N - 1) F = toPolynomial f.reverse := (toPolynomial_reverse f).symm
    have hRG : reflect m G = toPolynomial g.reverse := (toPolynomial_reverse g).symm
    have hQdeg : Q.natDegree ≤ k - 1 := hq_len ▸ natDegree_toPolynomial_le q
    -- `rev g · inv ≡ 1` and `rev q ≡ rev f · inv` modulo `t^k`
    have hconst : g.reverse.getD 0 0 * 1 = 1 := by
      rw [mul_one, List.getD_eq_getElem?_getD, List.getElem?_reverse
        (List.length_pos_iff.mpr hgne)]
      simpa [lead, List.getD_eq_getElem?_getD] using hg
    have hinv : X ^ k ∣ toPolynomial g.reverse * toPolynomial inv - 1 :=
      (pow_dvd_pow X (Nat.le_pow_clog (by norm_num) k)).trans
        (invNewton_spec hmul g.reverse hconst _)
    have hrq : X ^ k ∣ toPolynomial f.reverse * toPolynomial inv - toPolynomial rq := by
      have := X_pow_dvd_sub_take (mulF f.reverse inv) k
      rwa [hmul] at this
    -- so `rev (f - q g) = rev f - rev q · rev g` vanishes modulo `t^k`
    have hrefl : reflect (N - 1) (F - Q * G) = toPolynomial f.reverse -
        toPolynomial rq * toPolynomial g.reverse := by
      rw [reflect_sub, hRF, show N - 1 = (k - 1) + m by omega, reflect_mul Q G hQdeg
        (le_of_eq hdegG), hRQ, hRG]
    have hS : X ^ k ∣ reflect (N - 1) (F - Q * G) := by
      rw [hrefl]
      have : toPolynomial f.reverse - toPolynomial rq * toPolynomial g.reverse =
          -(toPolynomial f.reverse) * (toPolynomial g.reverse * toPolynomial inv - 1) +
            toPolynomial g.reverse *
              (toPolynomial f.reverse * toPolynomial inv - toPolynomial rq) := by ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right hinv _) (dvd_mul_of_dvd_right hrq _)
    -- hence `deg (f - q g) < m`
    have hdeg : (F - Q * G).degree < m := by
      rw [degree_lt_iff_coeff_zero]
      intro j hj
      rcases Nat.lt_or_ge j N with hjN | hjN
      · obtain ⟨W, hW⟩ := hS
        have := congrArg (fun p ↦ p.coeff (N - 1 - j)) hW
        simp only [coeff_reflect, coeff_X_pow_mul'] at this
        simp only [show ¬k ≤ N - 1 - j by omega, ↓reduceIte] at this
        rwa [revAt_le (by omega), show N - 1 - (N - 1 - j) = j by omega] at this
      · have h₁ : F.coeff j = 0 := by
          rw [coeff_toPolynomial, List.getD_eq_default _ _ hjN]
        have h₂ : (Q * G).coeff j = 0 := by
          refine coeff_eq_zero_of_natDegree_lt ((natDegree_mul_le).trans_lt ?_)
          omega
        rw [coeff_sub, h₁, h₂, sub_zero]
    -- the computed list is `f - q g` truncated to `m` coefficients, i.e. `f - q g` itself
    have hres : toPolynomial ((sub f (mulF q g)).take m) = F - Q * G := by
      ext j
      rw [coeff_toPolynomial_take, toPolynomial_sub, hmul]
      split_ifs with hj
      · rfl
      · exact ((degree_lt_iff_coeff_zero _ _).mp hdeg j (by exact_mod_cast not_lt.mp hj)).symm
    rw [hres]
    exact ((div_modByMonic_unique Q (F - Q * G) hmon ⟨by ring,
      by rw [degree_eq_natDegree hmon.ne_zero, hdegG]; exact hdeg⟩).2).symm

/-! ## Running time -/

/-- `2^⌈log₂ k⌉ < 2k` for `k ≥ 1`. -/
theorem two_pow_clog_le {k : ℕ} (hk : 1 ≤ k) : 2 ^ Nat.clog 2 k ≤ 2 * k := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk
  · simp
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hk
    have hpos : 0 < Nat.clog 2 k := Nat.clog_pos (by norm_num) hk
    rw [← Nat.succ_pred_eq_of_pos hpos, pow_succ]
    omega

/-- The charge for `⌈log₂ k⌉`, `k ≤ N`. -/
theorem clog_cost_le (C : CostModel) {k N : ℕ} (hk : k ≤ N) :
    costOf C (Nat.clog 2 k) ≤
      (N.size + 1) * (C.mul (2 * N.size) (2 * N.size) + 2 * C.divBound (2 * N.size)) := by
  have hs := Nat.size_le_size hk
  refine (iclog_cost_le C k).trans (Nat.mul_le_mul (by omega) (Nat.add_le_add
    (C.mul_mono (by omega) (by omega)) (Nat.mul_le_mul_left 2 (C.divBound_mono (by omega)))))

/-- **Cost of the fast remainder (Algorithm 9.6.4)**: Newton inversion with `⌈log₂ k⌉`
iterations (`k ≤ len f` the length of the quotient), two more products and one scaling —
at most `(⌈log₂ (len f)⌉ + 1)` times (two products and `2D` scalar products), plus the
computation of `⌈log₂ k⌉`; products by `mulF` cost at most `M` on inputs of length `≤ D`,
with `D ≥ 2 len f`. -/
theorem fastModMonic_cost_le [MulCost R] (C : CostModel)
    {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (mc : Chapter2.Poly R → Chapter2.Poly R → CostM C Unit) {M s D : ℕ}
    (hM : ∀ f g : Chapter2.Poly R, f.length ≤ D → g.length ≤ D → CostM.cost C (mc f g) ≤ M)
    (hlen : ∀ f g : Chapter2.Poly R, (mulF f g).length ≤ f.length + g.length)
    (hs : ∀ x y : R, MulCost.mulCost C x y ≤ s)
    (f g : Chapter2.Poly R) (hD : 2 * f.length ≤ D) :
    CostM.cost C (fastModMonic.counted mulF f g mc) ≤
      (Nat.clog 2 f.length + 1) * (2 * M + 2 * D * s) +
        (f.length.size + 1) * (C.mul (2 * f.length.size) (2 * f.length.size) +
          2 * C.divBound (2 * f.length.size)) := by
  cost_unfold fastModMonic.counted
  split_ifs with h
  · exact Nat.zero_le _
  · set k := f.length - (g.length - 1) with hkdef
    have hk1 : 1 ≤ k := by omega
    have hkf : k ≤ f.length := by omega
    have hgf : g.length ≤ f.length := by omega
    have hpow := two_pow_clog_le hk1
    have hcl := Nat.clog_mono_right 2 hkf
    have h₀ := clog_cost_le C hkf
    have h₁ := invNewton_cost_le C mc hM hlen hs g.reverse (by simp; omega) 1 (Nat.clog 2 k)
      (by omega)
    have hinv := length_invNewton_le mulF g.reverse 1 (Nat.clog 2 k)
    have h₂ := hM f.reverse (invNewton mulF g.reverse 1 (Nat.clog 2 k)) (by simp; omega)
      (by omega)
    set rq := (mulF f.reverse (invNewton mulF g.reverse 1 (Nat.clog 2 k))).take k
    have hrq : rq.length ≤ k := by simp [rq]
    set q := (rq ++ List.replicate (k - rq.length) 0).reverse
    have hq : q.length = k := by simp [q]; omega
    have h₃ := hM q g (by omega) (by omega)
    have hl := hlen q g
    have h₄ := smul_cost_le C hs (-1) (mulF q g)
    cost_unfold Chapter2.Poly.sub.counted
    have : (mulF q g).length * s ≤ D * s := Nat.mul_le_mul_right s (by omega)
    have : Nat.clog 2 k * (2 * M + 2 * D * s) ≤ Nat.clog 2 f.length * (2 * M + 2 * D * s) :=
      Nat.mul_le_mul_right _ hcl
    rw [add_mul, one_mul]
    nlinarith

end PrimeNumbers.Chapter9
