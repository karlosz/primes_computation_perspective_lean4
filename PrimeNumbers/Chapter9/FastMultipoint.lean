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
def monicOfDegree (d : ℕ) (L : Chapter2.Poly R) : Chapter2.Poly R := L.take d ++ [1]

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
def prodTree (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R) (us : List R) :
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
def multipointEvalWith (prodF : List R → Chapter2.Poly R)
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
def multipointEvalFast (n δ : ℕ) (x : Chapter2.Poly (ZMod n)) (T : List (ZMod n)) :
    List (ZMod n) :=
  multipointEvalWith (prodTree (mulMod n)) (fastModMonic (mulMod n)) δ x T

theorem multipointEvalFast_eq {n : ℕ} [NeZero n] [Nontrivial (ZMod n)] (δ : ℕ)
    (x : Chapter2.Poly (ZMod n)) (T : List (ZMod n)) :
    multipointEvalFast n δ x T = T.map fun t ↦ (toPolynomial x).eval t :=
  multipointEvalWith_eq (prodTree_spec (mulCorrect_mulMod n))
    (fun f _ hg ↦ toPolynomial_fastModMonic (mulCorrect_mulMod n) f hg) δ x T

/-! ## Running time of Algorithm 9.6.7: the recursion has `⌈log₂ D⌉ + 1` levels

The cost of Algorithm 9.6.7 is that of its nodes: at a node with `d` points, two
half-products and two remainders (or, at a leaf, direct evaluation).  We count it with
cost functions `costProd`, `costMod`, `costLeaf` for those routines (measured in whatever
unit — ring operations or bit operations), following the recursion exactly. -/

/-- The cost of `multipointEvalWith`, node by node. -/
def multipointCost (prodF : List R → Chapter2.Poly R)
    (modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (costProd : List R → ℕ) (costMod : Chapter2.Poly R → Chapter2.Poly R → ℕ)
    (costLeaf : Chapter2.Poly R → List R → ℕ) (δ : ℕ) (x : Chapter2.Poly R) (T : List R) : ℕ :=
  if T.length ≤ max δ 1 then costLeaf x T
  else
    let u := T.take (T.length / 2)
    let v := T.drop (T.length / 2)
    costProd u + costProd v + costMod x (prodF u) + costMod x (prodF v) +
      multipointCost prodF modF costProd costMod costLeaf δ (modF x (prodF u)) u +
      multipointCost prodF modF costProd costMod costLeaf δ (modF x (prodF v)) v
termination_by T.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

omit [CommRing R] in
/-- **The level count of Algorithm 9.6.7.**  Suppose the work at a node with `d` points
(two products, two remainders, or the direct evaluation at a leaf) is at most `S d`,
whenever the polynomial being evaluated has at most `d + 1` coefficients — which the
remainders guarantee below the root (`hmodLen`).  If `S` is monotone and superadditive
(`S a + S b ≤ S (a + b)`, true for `S d = M(d) log d` and the like), then the whole
algorithm costs at most `(⌈log₂ D⌉ + 1) · S D` for `D` points.  With `S d = O(M(d) log d)`
for the fast routines this is the book's `O(M(D) log² D)`. -/
theorem multipointCost_le {prodF : List R → Chapter2.Poly R}
    {modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    {costProd : List R → ℕ} {costMod : Chapter2.Poly R → Chapter2.Poly R → ℕ}
    {costLeaf : Chapter2.Poly R → List R → ℕ} {S : ℕ → ℕ} (hS : Monotone S)
    (hsup : ∀ a b, S a + S b ≤ S (a + b))
    (hmodLen : ∀ x us, (modF x (prodF us)).length ≤ us.length + 1)
    (hnode : ∀ x (T : List R), x.length ≤ T.length + 1 → 2 ≤ T.length →
      costProd (T.take (T.length / 2)) + costProd (T.drop (T.length / 2)) +
        costMod x (prodF (T.take (T.length / 2))) + costMod x (prodF (T.drop (T.length / 2)))
        ≤ S T.length)
    (hleaf : ∀ x (T : List R), x.length ≤ T.length + 1 → costLeaf x T ≤ S T.length)
    (δ : ℕ) (x : Chapter2.Poly R) (T : List R) (hx : x.length ≤ T.length + 1) :
    multipointCost prodF modF costProd costMod costLeaf δ x T ≤
      (Nat.clog 2 T.length + 1) * S T.length := by
  fun_induction multipointCost prodF modF costProd costMod costLeaf δ x T with
  | case1 x T h => have := hleaf x T hx; nlinarith
  | case2 x T h u v ih₁ ih₂ =>
    have hu : u.length = T.length / 2 := by simp [u]; omega
    have hv : v.length = T.length - T.length / 2 := by simp [v]
    have ih₁ := ih₁ (by have := hmodLen x u; omega)
    have ih₂ := ih₂ (by have := hmodLen x v; omega)
    have hn : costProd u + costProd v + costMod x (prodF u) + costMod x (prodF v) ≤
        S T.length := hnode x T hx (by omega)
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
    have hSu : S u.length ≤ S T.length := hS (by omega)
    have hSv : S v.length ≤ S T.length := hS (by omega)
    have hsplit : S u.length + S v.length ≤ S T.length := by
      have := hsup u.length v.length
      exact this.trans (hS (by omega))
    calc _ ≤ S T.length + (Nat.clog 2 u.length + 1) * S u.length +
          (Nat.clog 2 v.length + 1) * S v.length := by omega
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

end PrimeNumbers.Chapter9
