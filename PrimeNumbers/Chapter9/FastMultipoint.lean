import PrimeNumbers.Chapter9.FastMod

/-!
# Algorithm 9.6.7 with fast multiplication and fast remainder

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Algorithm 9.6.7, run
with the fast operations of Algorithms 9.6.1 (binary segmentation) and 9.6.4 (fast
remainder), as the book intends ("the intent is that the product must be performed with a
fast multiply").

* `monicOfDegree`, `prodTree` — the half-products `∏ (t - u)` built as a balanced product
  tree with any correct multiplication, normalized to a monic coefficient list.
* `multipointEvalWith` — Algorithm 9.6.7 parametrized by the product and remainder
  routines; `multipointEvalWith_eq` proves it correct for *any* routines that are proved
  correct.
* `multipointEvalFast` — the instance over `Z_n` with `mulMod` and `fastModMonic`;
  `multipointEvalFast_eq`.
-/

namespace PrimeNumbers.Chapter9

open Polynomial PrimeNumbers.Chapter2 PrimeNumbers.Chapter2.Poly

variable {R : Type} [CommRing R]

/-- Force the coefficient list of a polynomial known to be monic of degree `d` into the
shape `[c₀, …, c_{d-1}, 1]`, so that its last entry is visibly `1`. -/
@[cost_free] def monicOfDegree (d : ℕ) (L : Chapter2.Poly R) : Chapter2.Poly R := L.take d ++ [1]

theorem lead_monicOfDegree (d : ℕ) (L : Chapter2.Poly R) : lead (monicOfDegree d L) = 1 := by
  simp [monicOfDegree, lead]

theorem toPolynomial_monicOfDegree [Nontrivial R] {d : ℕ} {L : Chapter2.Poly R}
    (hmon : (toPolynomial L).Monic) (hd : (toPolynomial L).natDegree = d) :
    toPolynomial (monicOfDegree d L) = toPolynomial L := by
  have hlen : d < L.length := by
    by_contra hge
    have : (toPolynomial L).coeff d = 0 := by
      rw [coeff_toPolynomial, List.getD_eq_default _ _ (by omega)]
    rw [← hd, coeff_natDegree, hmon.leadingCoeff] at this
    exact one_ne_zero this
  rw [monicOfDegree, Chapter9.toPolynomial_append, List.length_take, min_eq_left hlen.le]
  ext j
  rw [coeff_add, coeff_toPolynomial_take, coeff_X_pow_mul']
  simp only [toPolynomial_cons, toPolynomial_nil, mul_zero, add_zero]
  rcases Nat.lt_trichotomy j d with h | rfl | h
  · simp [h, show ¬d ≤ j by omega]
  · simp only [lt_irrefl, ↓reduceIte, le_refl, Nat.sub_self, coeff_C_zero, zero_add]
    rw [← hd, coeff_natDegree, hmon.leadingCoeff]
  · simp only [show ¬j < d by omega, ↓reduceIte, show d ≤ j by omega, zero_add, coeff_C,
      show j - d ≠ 0 by omega]
    exact (coeff_eq_zero_of_natDegree_lt (hd ▸ h)).symm

theorem length_prodLinear (us : List R) : (prodLinear us).length = us.length + 1 := by
  induction us with
  | nil => simp [prodLinear]
  | cons u us ih =>
    rw [prodLinear, Poly.length_mul (by simp) (by intro h; rw [h] at ih; simp at ih), ih]
    simp; omega

theorem toPolynomial_prodLinear_append (a b : List R) :
    toPolynomial (prodLinear (a ++ b)) =
      toPolynomial (prodLinear a) * toPolynomial (prodLinear b) := by
  induction a with
  | nil => simp [prodLinear]
  | cons u a ih => simp only [List.cons_append, prodLinear, toPolynomial_mul, ih]; ring

/-- The product `∏ (t - u)` as a balanced product tree, multiplying with `mulF`. -/
counted_def prodTree [MulCost R] (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (us : List R) :
    Chapter2.Poly R :=
  if us.length ≤ 1 then prodLinear us
  else monicOfDegree us.length
    (mulF (prodTree mulF (us.take (us.length / 2))) (prodTree mulF (us.drop (us.length / 2))))
termination_by us.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem prodTree_spec [Nontrivial R] {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (hmul : MulCorrect mulF) (us : List R) :
    toPolynomial (prodTree mulF us) = toPolynomial (prodLinear us) ∧
      lead (prodTree mulF us) = 1 := by
  fun_induction prodTree mulF us with
  | case1 us h => exact ⟨rfl, lead_prodLinear us⟩
  | case2 us h ih₁ ih₂ =>
    refine ⟨?_, lead_monicOfDegree _ _⟩
    have hprod : toPolynomial (mulF (prodTree mulF (us.take (us.length / 2)))
        (prodTree mulF (us.drop (us.length / 2)))) = toPolynomial (prodLinear us) := by
      rw [hmul, ih₁.1, ih₂.1, ← toPolynomial_prodLinear_append, List.take_append_drop]
    have hmon := Poly.monic_toPolynomial (lead_prodLinear us)
    have hdeg : (toPolynomial (prodLinear us)).natDegree = us.length := by
      rw [Poly.natDegree_toPolynomial_of_lead (lead_prodLinear us), length_prodLinear]; simp
    rw [toPolynomial_monicOfDegree (hprod ▸ hmon) (hprod ▸ hdeg), hprod]

/-- **Algorithm 9.6.7** with the half-products computed by `prodF` and the reductions by
`modF`. -/
counted_def multipointEvalWith [MulCost R] (prodF : List R → Chapter2.Poly R)
    (modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R) (δ : ℕ)
    (x : Chapter2.Poly R) (T : List R) : List R :=
  if T.length ≤ max δ 1 then T.map (Poly.eval x)
  else
    let u := T.take (T.length / 2)
    let v := T.drop (T.length / 2)
    multipointEvalWith prodF modF δ (modF x (prodF u)) u ++
      multipointEvalWith prodF modF δ (modF x (prodF v)) v
termination_by T.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

/-- **Correctness of Algorithm 9.6.7 for any correct product and remainder routines.** -/
theorem multipointEvalWith_eq [Nontrivial R] {prodF : List R → Chapter2.Poly R}
    {modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (hprod : ∀ us, toPolynomial (prodF us) = toPolynomial (prodLinear us) ∧ lead (prodF us) = 1)
    (hmod : ∀ f g, lead g = 1 → toPolynomial (modF f g) = toPolynomial f %ₘ toPolynomial g)
    (δ : ℕ) (x : Chapter2.Poly R) (T : List R) :
    multipointEvalWith prodF modF δ x T = T.map fun t ↦ (toPolynomial x).eval t := by
  have hroot : ∀ (x : Chapter2.Poly R) (us : List R) (t : R), t ∈ us →
      (toPolynomial (modF x (prodF us))).eval t = (toPolynomial x).eval t := by
    intro x us t ht
    rw [hmod x _ (hprod us).2, (hprod us).1, ← Poly.toPolynomial_modMonic x (lead_prodLinear us)]
    exact eval_modMonic_of_root x us ht
  fun_induction multipointEvalWith prodF modF δ x T with
  | case1 x T h => simp [Poly.eval_eq]
  | case2 x T h u v ih₁ ih₂ =>
    have hT : T = u ++ v := (List.take_append_drop _ T).symm
    rw [ih₁, ih₂]
    conv_rhs => rw [hT, List.map_append]
    congr 1
    · exact List.map_congr_left fun t ht ↦ hroot x u t ht
    · exact List.map_congr_left fun t ht ↦ hroot x v t ht

/-- **Algorithm 9.6.7 over `Z_n` with fast multiplication (Algorithm 9.6.1) and fast
remainder (Algorithm 9.6.4).** -/
counted_def multipointEvalFast (n δ : ℕ) (x : Chapter2.Poly (ZMod n)) (T : List (ZMod n)) :
    List (ZMod n) :=
  multipointEvalWith (prodTree (mulMod n)) (fastModMonic (mulMod n)) δ x T

theorem multipointEvalFast_eq {n : ℕ} [NeZero n] [Nontrivial (ZMod n)] (δ : ℕ)
    (x : Chapter2.Poly (ZMod n)) (T : List (ZMod n)) :
    multipointEvalFast n δ x T = T.map fun t ↦ (toPolynomial x).eval t :=
  multipointEvalWith_eq (prodTree_spec (mulCorrect_mulMod n))
    (fun f _ hg ↦ toPolynomial_fastModMonic (mulCorrect_mulMod n) f hg) δ x T

/-! ## Running time of Algorithm 9.6.7: the recursion has `⌈log₂ D⌉ + 1` levels

The cost of Algorithm 9.6.7 is that of its nodes: at a node with `d` points, two
half-products and two remainders (charged through the charge functions `pc`, `mc` of the
routines passed for them), or, at a leaf, direct evaluation by Horner's rule. -/

/-- **The level count of Algorithm 9.6.7.**  Suppose the work at a node with `d` points
(two products, two remainders, or the direct evaluation at a leaf) is at most `S d`,
whenever the polynomial being evaluated has at most `d + 1` coefficients — which the
remainders guarantee below the root (`hmodLen`).  If `S` is monotone and superadditive
(`S a + S b ≤ S (a + b)`, true for `S d = M(d) log d` and the like), then the whole
algorithm costs at most `(⌈log₂ D⌉ + 1) · S D` for `D` points.  With `S d = O(M(d) log d)`
for the fast routines this is the book's `O(M(D) log² D)`. -/
theorem multipointEval_cost_le [MulCost R] (C : CostModel) {prodF : List R → Chapter2.Poly R}
    {modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (pc : List R → CostM C Unit) (mc : Chapter2.Poly R → Chapter2.Poly R → CostM C Unit)
    (δ : ℕ) {S : ℕ → ℕ} (hS : Monotone S) (hsup : ∀ a b, S a + S b ≤ S (a + b))
    (hmodLen : ∀ x us, (modF x (prodF us)).length ≤ us.length + 1)
    (hnode : ∀ x (T : List R), x.length ≤ T.length + 1 → 2 ≤ T.length →
      CostM.cost C (pc (T.take (T.length / 2))) + CostM.cost C (pc (T.drop (T.length / 2))) +
        CostM.cost C (mc x (prodF (T.take (T.length / 2)))) +
        CostM.cost C (mc x (prodF (T.drop (T.length / 2)))) ≤ S T.length)
    (hleaf : ∀ x (T : List R), x.length ≤ T.length + 1 → T.length ≤ max δ 1 →
      (T.map fun (t : R) ↦ costOf C (Poly.eval x t)).sum ≤ S T.length)
    (x : Chapter2.Poly R) (T : List R) (hx : x.length ≤ T.length + 1) :
    CostM.cost C (multipointEvalWith.counted prodF modF δ x T pc mc) ≤
      (Nat.clog 2 T.length + 1) * S T.length := by
  fun_induction multipointEvalWith prodF modF δ x T with
  | case1 x T h =>
    have := hleaf x T hx h
    cost_unfold multipointEvalWith.counted
    nlinarith
  | case2 x T h u v ih₁ ih₂ =>
    have hu : u.length = T.length / 2 := by simp [u]; omega
    have hv : v.length = T.length - T.length / 2 := by simp [v]
    have ih₁ := ih₁ (by have := hmodLen x u; omega)
    have ih₂ := ih₂ (by have := hmodLen x v; omega)
    have hn := hnode x T hx (by omega)
    -- each half has at most `⌈D/2⌉` points, hence one level fewer
    have hclog : ∀ m, m ≤ (T.length + 1) / 2 → Nat.clog 2 m + 1 ≤ Nat.clog 2 T.length := by
      intro m hm
      have h2 : 2 ≤ T.length := by omega
      have := Nat.clog_mono_right 2 hm
      have hc : Nat.clog 2 T.length = Nat.clog 2 ((T.length + 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) h2
      omega
    have hcu := hclog u.length (by omega)
    have hcv := hclog v.length (by omega)
    have hsplit : S u.length + S v.length ≤ S T.length := by
      have := hsup u.length v.length
      exact this.trans (hS (by omega))
    cost_unfold multipointEvalWith.counted
    simp only [u, v] at *
    calc _ ≤ S T.length + (Nat.clog 2 u.length + 1) * S u.length +
          (Nat.clog 2 v.length + 1) * S v.length := by simp only [u, v]; omega
      _ ≤ S T.length + Nat.clog 2 T.length * S u.length + Nat.clog 2 T.length * S v.length := by
          gcongr
      _ = S T.length + Nat.clog 2 T.length * (S u.length + S v.length) := by ring
      _ ≤ S T.length + Nat.clog 2 T.length * S T.length := by gcongr
      _ = (Nat.clog 2 T.length + 1) * S T.length := by ring

/-! ### The length hypothesis holds for the fast routines -/

theorem length_fastModMonic_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (f g : Chapter2.Poly R) : (fastModMonic mulF f g).length ≤ g.length - 1 := by
  unfold fastModMonic
  split_ifs with h
  · exact h
  · simp only [List.length_take]; omega

theorem length_prodTree_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (us : List R) : (prodTree mulF us).length ≤ us.length + 1 := by
  rw [prodTree]
  split_ifs
  · rw [length_prodLinear]
  · simp only [monicOfDegree, List.length_append, List.length_take, List.length_singleton]
    omega

/-- In the fast instance, every remainder has at most as many coefficients as there are
points: the hypothesis `hmodLen` of `multipointCost_le`. -/
theorem length_fastModMonic_prodTree_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (x : Chapter2.Poly R) (us : List R) :
    (fastModMonic mulF x (prodTree mulF us)).length ≤ us.length + 1 := by
  have h₁ := length_fastModMonic_le mulF x (prodTree mulF us)
  have h₂ := length_prodTree_le mulF us
  omega

/-! ### The product tree -/

/-- A leaf of the product tree, `t - u`, costs two scalar products. -/
theorem prodLinear_cost_le [MulCost R] (C : CostModel) {s : ℕ}
    (hs : ∀ x y : R, MulCost.mulCost C x y ≤ s) (us : List R) (h : us.length ≤ 1) :
    costOf C (prodLinear us) ≤ us.length * (2 * s) := by
  match us, h with
  | [], _ => cost_unfold prodLinear.counted
  | [u], _ =>
    have h₁ := hs (-u) 1
    have h₂ := hs 1 1
    cost_unfold prodLinear.counted
    cost_unfold prodLinear.counted
    cost_unfold Chapter2.Poly.mul.counted
    cost_unfold Chapter2.Poly.smul.counted
    cost_unfold Chapter2.Poly.mul.counted
    cost_unfold Chapter2.Poly.smul.counted
    have h₀ : CostM.cost C (Chapter2.Poly.mul.counted ([] : Chapter2.Poly R) [1]) = 0 := by
      cost_unfold Chapter2.Poly.mul.counted
    simp only [prodLinear, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_singleton, h₀]
    omega

/-- **Cost of the product tree**: if a product of inputs of length `≤ m` costs at most
`Mf m`, with `Mf` monotone and superadditive, the tree over `d` points costs at most
`(⌈log₂ d⌉ + 1) · Mf d` for the products and `2s` for each leaf. -/
theorem prodTree_cost_le [MulCost R] (C : CostModel)
    {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (mc : Chapter2.Poly R → Chapter2.Poly R → CostM C Unit) {Mf : ℕ → ℕ} {s : ℕ}
    (hMf : Monotone Mf) (hsup : ∀ a b, Mf a + Mf b ≤ Mf (a + b))
    (hM : ∀ (m : ℕ), 1 ≤ m → ∀ (f g : Chapter2.Poly R), f.length ≤ m → g.length ≤ m →
      CostM.cost C (mc f g) ≤ Mf m)
    (hs : ∀ x y : R, MulCost.mulCost C x y ≤ s) (us : List R) :
    CostM.cost C (prodTree.counted mulF us mc) ≤
      (Nat.clog 2 us.length + 1) * Mf us.length + us.length * (2 * s) := by
  fun_induction prodTree mulF us with
  | case1 us h =>
    cost_unfold prodTree.counted
    have := prodLinear_cost_le C hs us h
    omega
  | case2 us h ih₁ ih₂ =>
    set u := us.take (us.length / 2)
    set v := us.drop (us.length / 2)
    have hu : u.length = us.length / 2 := by simp [u]; omega
    have hv : v.length = us.length - us.length / 2 := by simp [v]
    have hnode := hM us.length (by omega) (prodTree mulF u) (prodTree mulF v)
      ((length_prodTree_le mulF u).trans (by omega))
      ((length_prodTree_le mulF v).trans (by omega))
    have hclog : ∀ m, m ≤ (us.length + 1) / 2 → Nat.clog 2 m + 1 ≤ Nat.clog 2 us.length := by
      intro m hm
      have := Nat.clog_mono_right 2 hm
      have hc : Nat.clog 2 us.length = Nat.clog 2 ((us.length + 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) (by omega)
      omega
    have hcu := hclog u.length (by omega)
    have hcv := hclog v.length (by omega)
    have hsplit : Mf u.length + Mf v.length ≤ Mf us.length :=
      (hsup _ _).trans (hMf (by omega))
    have e₁ : (Nat.clog 2 u.length + 1) * Mf u.length ≤ Nat.clog 2 us.length * Mf u.length :=
      Nat.mul_le_mul_right _ hcu
    have e₂ : (Nat.clog 2 v.length + 1) * Mf v.length ≤ Nat.clog 2 us.length * Mf v.length :=
      Nat.mul_le_mul_right _ hcv
    have e₃ : Nat.clog 2 us.length * (Mf u.length + Mf v.length) ≤
        Nat.clog 2 us.length * Mf us.length := Nat.mul_le_mul_left _ hsplit
    cost_unfold prodTree.counted
    rw [add_mul, one_mul, show us.length * (2 * s) = u.length * (2 * s) + v.length * (2 * s) by
      rw [← add_mul]; congr 1; omega]
    nlinarith

end PrimeNumbers.Chapter9
