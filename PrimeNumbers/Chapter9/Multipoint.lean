import PrimeNumbers.Chapter2.Poly

/-!
# §9.6 Polynomial arithmetic: evaluation at many points

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 9.6.

This file starts §9.6, working over an arbitrary commutative ring `R` (so that it applies
to `Z_n` for composite `n`, as the Pollard–Strassen method of §5.5 needs):

* `Poly.eval`          — Horner evaluation; `eval_eq`.
* `Poly.divModMonic`   — division with remainder by a *monic* divisor, which needs no
                         inverses; `toPolynomial_modMonic` identifies it with Mathlib's
                         `%ₘ`.
* `Poly.lead_mul`, `length_mul` — products of monic lists are monic.
* `prodLinear`         — `∏ (t - u)` over a list of points.
* `multipointEval`     — **Algorithm 9.6.7** (evaluation of a polynomial at arbitrary
                         points): split the points in halves, reduce modulo the two
                         half-products, recurse; `multipointEval_eq` proves it returns all
                         the values.

The algorithm uses the multiplication and remainder of `Chapter2/Poly.lean`, which are
the grammar-school ones.  The book's running time `O(D ln² D)` needs the fast
multiplication and fast remainder of Algorithms 9.6.1–9.6.4 in their place; those, and the
running-time analysis, are the next steps.
-/

namespace PrimeNumbers.Chapter9

open Polynomial PrimeNumbers.Chapter2 PrimeNumbers.Chapter2.Poly

namespace Poly

variable {R : Type} [CommRing R]

/-- Horner's rule: `f(x) = c₀ + x (c₁ + x (c₂ + ⋯))`. -/
def eval : Chapter2.Poly R → R → R
  | [], _ => 0
  | c :: f, x => c + x * eval f x

theorem eval_eq (f : Chapter2.Poly R) (x : R) : eval f x = (toPolynomial f).eval x := by
  induction f with
  | nil => simp [eval]
  | cons c f ih => simp [eval, ih]

/-- **Division with remainder by a monic divisor** (`lead g = 1`): the same recursion as
`Poly.divMod`, without the inverse of the leading coefficient. -/
def divModMonic : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R × Chapter2.Poly R
  | [], _ => ([], [])
  | a :: f, g =>
    let qr := divModMonic f g
    let s := a :: qr.2
    if s.length < g.length then (0 :: qr.1, s)
    else
      let c := lead s
      (c :: qr.1, (sub s (smul c g)).dropLast)

/-- The remainder `f mod g` for monic `g`. -/
def modMonic (f g : Chapter2.Poly R) : Chapter2.Poly R := (divModMonic f g).2

theorem length_divModMonic_snd_lt (f : Chapter2.Poly R) {g : Chapter2.Poly R} (hg : g ≠ []) :
    (divModMonic f g).2.length < g.length := by
  have hpos : 0 < g.length := List.length_pos_iff.mpr hg
  induction f with
  | nil => simpa [divModMonic] using hpos
  | cons a f ih =>
    rw [divModMonic]
    split_ifs with h
    · exact h
    · simp only [List.length_dropLast, length_sub, length_smul, List.length_cons] at h ⊢
      omega

theorem divModMonic_spec (f : Chapter2.Poly R) {g : Chapter2.Poly R} (hg : lead g = 1)
    (hgne : g ≠ []) :
    toPolynomial f =
      toPolynomial (divModMonic f g).1 * toPolynomial g + toPolynomial (divModMonic f g).2 := by
  induction f with
  | nil => simp [divModMonic]
  | cons a f ih =>
    have hlen := length_divModMonic_snd_lt f hgne
    rw [divModMonic]
    split_ifs with h
    · simp only [toPolynomial_cons, C_0, zero_add, ih]; ring
    · set s := a :: (divModMonic f g).2 with hs
      have hsl : s.length = g.length := by simp only [hs, List.length_cons] at h ⊢; omega
      have hdl : (sub s (smul (lead s) g)).length = g.length := by simp [length_sub, hsl]
      have htop : lead (sub s (smul (lead s) g)) = 0 := by
        rw [lead, hdl, ← coeff_toPolynomial, toPolynomial_sub, toPolynomial_smul, coeff_sub,
          coeff_C_mul, coeff_toPolynomial, coeff_toPolynomial]
        have h₁ : s.getD (g.length - 1) 0 = lead s := by rw [lead, hsl]
        have h₂ : g.getD (g.length - 1) 0 = lead g := rfl
        rw [h₁, h₂, hg, mul_one, sub_self]
      have hdrop := toPolynomial_dropLast_add (sub s (smul (lead s) g))
      rw [htop, C_0, zero_mul, add_zero, toPolynomial_sub, toPolynomial_smul] at hdrop
      simp only [toPolynomial_cons, hdrop]
      rw [hs]
      simp only [toPolynomial_cons, ih]
      ring

/-- A list whose top coefficient is `1` denotes a monic polynomial of degree `length - 1`. -/
theorem natDegree_toPolynomial_of_lead [Nontrivial R] {g : Chapter2.Poly R} (hg : lead g = 1) :
    (toPolynomial g).natDegree = g.length - 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_
    (by rw [coeff_toPolynomial]; change lead g ≠ 0; rw [hg]; exact one_ne_zero)
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPolynomial, List.getD_eq_default _ _ (by
    have : g.length - 1 < N := by exact_mod_cast hN
    omega)]

theorem monic_toPolynomial [Nontrivial R] {g : Chapter2.Poly R} (hg : lead g = 1) :
    (toPolynomial g).Monic := by
  rw [Monic, leadingCoeff, natDegree_toPolynomial_of_lead hg, coeff_toPolynomial]
  exact hg

/-- `modMonic` computes Mathlib's remainder `%ₘ` by a monic polynomial. -/
theorem toPolynomial_modMonic [Nontrivial R] (f : Chapter2.Poly R) {g : Chapter2.Poly R}
    (hg : lead g = 1) : toPolynomial (modMonic f g) = toPolynomial f %ₘ toPolynomial g := by
  have hgne : g ≠ [] := by rintro rfl; simp [lead] at hg
  have hmon := monic_toPolynomial hg
  refine ((div_modByMonic_unique (toPolynomial (divModMonic f g).1) _ hmon ⟨?_, ?_⟩).2).symm
  · rw [divModMonic_spec f hg hgne, modMonic]; ring
  · rw [degree_eq_natDegree hmon.ne_zero, natDegree_toPolynomial_of_lead hg]
    refine (degree_toPolynomial_lt _).trans_le ?_
    have := length_divModMonic_snd_lt f hgne
    exact_mod_cast Nat.le_sub_one_of_lt this

/-! ## Products of monic lists -/

theorem length_mul {f g : Chapter2.Poly R} (hf : f ≠ []) (hg : g ≠ []) :
    (mul f g).length = f.length + g.length - 1 := by
  induction f with
  | nil => exact absurd rfl hf
  | cons a f ih =>
    have hgl := List.length_pos_iff.mpr hg
    rcases f with _ | ⟨b, f⟩
    · simp [mul, length_add]; omega
    · have := ih (by simp)
      simp only [mul, length_add, length_smul, List.length_cons] at this ⊢
      omega

/-- A product of lists with top coefficient `1` has top coefficient `1`. -/
theorem lead_mul_of_lead_eq_one [Nontrivial R] {f g : Chapter2.Poly R} (hf : lead f = 1)
    (hg : lead g = 1) : lead (mul f g) = 1 := by
  have hfne : f ≠ [] := by rintro rfl; simp [lead] at hf
  have hgne : g ≠ [] := by rintro rfl; simp [lead] at hg
  have hfl := List.length_pos_iff.mpr hfne
  have hgl := List.length_pos_iff.mpr hgne
  have h := coeff_mul_degree_add_degree (toPolynomial f) (toPolynomial g)
  rw [natDegree_toPolynomial_of_lead hf, natDegree_toPolynomial_of_lead hg,
    (monic_toPolynomial hf).leadingCoeff, (monic_toPolynomial hg).leadingCoeff, mul_one,
    ← toPolynomial_mul, coeff_toPolynomial] at h
  rw [lead, length_mul hfne hgne, show f.length + g.length - 1 - 1 =
    (f.length - 1) + (g.length - 1) by omega]
  exact h

end Poly

/-! ## Algorithm 9.6.7 -/

section Multipoint

variable {R : Type} [CommRing R]

/-- `∏_{u ∈ us} (t - u)`, as a coefficient list (step [Assemble half-polynomials]). -/
def prodLinear : List R → Chapter2.Poly R
  | [] => [1]
  | u :: us => Chapter2.Poly.mul [-u, 1] (prodLinear us)

theorem lead_prodLinear [Nontrivial R] (us : List R) : lead (prodLinear us) = 1 := by
  induction us with
  | nil => simp [prodLinear, lead]
  | cons u us ih =>
    rw [prodLinear]
    exact Poly.lead_mul_of_lead_eq_one (by simp [lead]) ih

theorem eval_prodLinear (us : List R) (t : R) :
    (toPolynomial (prodLinear us)).eval t = (us.map fun u ↦ t - u).prod := by
  induction us with
  | nil => simp [prodLinear]
  | cons u us ih => simp [prodLinear, ih]; ring

/-- **Algorithm 9.6.7 (Evaluation of a polynomial at arbitrary points).**  Returns
`(x(t₀), …, x(t_{D-1}))`.  `δ ≥ 1` is the breakover threshold below which the values are
computed directly.
```
eval(x, T) {
  if (len(T) ≤ δ) return (x(t₀), x(t₁), …);
  u = L(T);  v = H(T);                                  // the two halves
  w(t) = ∏ (t - u_m);  z(t) = ∏ (t - v_m);
  a(t) = x(t) mod w(t);  b(t) = x(t) mod z(t);
  return eval(a, u) ∪ eval(b, v);
}
```
-/
def multipointEval (δ : ℕ) (x : Chapter2.Poly R) (T : List R) : List R :=
  if T.length ≤ max δ 1 then T.map (Poly.eval x)
  else
    let u := T.take (T.length / 2)
    let v := T.drop (T.length / 2)
    multipointEval δ (Poly.modMonic x (prodLinear u)) u ++
      multipointEval δ (Poly.modMonic x (prodLinear v)) v
termination_by T.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

/-- Reducing modulo a monic `w` does not change the values at the roots of `w`. -/
theorem eval_modMonic_of_root [Nontrivial R] (x : Chapter2.Poly R) (us : List R) {t : R}
    (ht : t ∈ us) :
    (toPolynomial (Poly.modMonic x (prodLinear us))).eval t = (toPolynomial x).eval t := by
  rw [Poly.toPolynomial_modMonic x (lead_prodLinear us)]
  have h := modByMonic_add_div (toPolynomial x) (toPolynomial (prodLinear us))
  have hroot : (toPolynomial (prodLinear us)).eval t = 0 := by
    rw [eval_prodLinear]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨t, ht, sub_self t⟩)
  conv_rhs => rw [← h]
  simp [hroot]

/-- **Correctness of Algorithm 9.6.7**: it returns exactly the values `x(t)`, `t ∈ T`. -/
theorem multipointEval_eq [Nontrivial R] (δ : ℕ) (x : Chapter2.Poly R) (T : List R) :
    multipointEval δ x T = T.map fun t ↦ (toPolynomial x).eval t := by
  fun_induction multipointEval δ x T with
  | case1 x T h => simp [Poly.eval_eq]
  | case2 x T h u v ih₁ ih₂ =>
    have hT : T = u ++ v := (List.take_append_drop _ T).symm
    rw [ih₁, ih₂]
    conv_rhs => rw [hT, List.map_append]
    congr 1
    · exact List.map_congr_left fun t ht ↦ eval_modMonic_of_root x u ht
    · exact List.map_congr_left fun t ht ↦ eval_modMonic_of_root x v ht

end Multipoint

end PrimeNumbers.Chapter9
