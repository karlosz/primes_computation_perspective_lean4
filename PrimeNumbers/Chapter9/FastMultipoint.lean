import PrimeNumbers.Chapter9.FastMod
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Defs

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
counted_def monicOfDegree (d : ℕ) (L : Chapter2.Poly R) : Chapter2.Poly R := L.take d ++ [1]

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
  rw [monicOfDegree, Chapter2.Poly.toPolynomial_append, List.length_take, min_eq_left hlen.le]
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
counted_def prodTree [ArithCost R] (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (us : List R) :
    Chapter2.Poly R :=
  let n := us.length
  if n ≤ 1 then prodLinear us
  else
    let h := n / 2
    monicOfDegree n (mulF (prodTree mulF (us.take h)) (prodTree mulF (us.drop h)))
termination_by us.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem prodTree_spec [Nontrivial R] {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (hmul : MulCorrect mulF) (us : List R) :
    toPolynomial (prodTree mulF us) = toPolynomial (prodLinear us) ∧
      lead (prodTree mulF us) = 1 := by
  fun_induction prodTree mulF us with
  | case1 us n hn => exact ⟨rfl, lead_prodLinear us⟩
  | case2 us n hn h ih₁ ih₂ =>
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
counted_def multipointEvalWith [ArithCost R] (prodF : List R → Chapter2.Poly R)
    (modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R) (δ : ℕ)
    (x : Chapter2.Poly R) (T : List R) : List R :=
  let n := T.length
  if n ≤ max δ 1 then T.map (Poly.eval x)
  else
    let h := n / 2
    let u := T.take h
    let v := T.drop h
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
  | case1 x T n hn => simp [Poly.eval_eq]
  | case2 x T n hn h u v ih₁ ih₂ =>
    have hT : T = u ++ v := (List.take_append_drop _ T).symm
    rw [ih₁, ih₂]
    conv_rhs => rw [hT, List.map_append]
    congr 1
    · exact List.map_congr_left fun t ht ↦ hroot x u t ht
    · exact List.map_congr_left fun t ht ↦ hroot x v t ht

theorem length_multipointEvalWith [ArithCost R] (prodF : List R → Chapter2.Poly R)
    (modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R) (δ : ℕ)
    (x : Chapter2.Poly R) (T : List R) :
    (multipointEvalWith prodF modF δ x T).length = T.length := by
  fun_induction multipointEvalWith prodF modF δ x T with
  | case1 x T n hn => simp
  | case2 x T n hn h u v ih₁ ih₂ =>
    rw [List.length_append, ih₁, ih₂]
    simp only [u, v, List.length_take, List.length_drop]; omega

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
(two products, two remainders, or the direct evaluation at a leaf), together with the
bookkeeping around it (`6 d` steps on lengths of at most `K` bits), is at most `S d`,
whenever the polynomial being evaluated has at most `d + 1` coefficients — which the
remainders guarantee below the root (`hmodLen`).  If `S` is monotone and superadditive
(`S a + S b ≤ S (a + b)`, true for `S d = M(d) log d` and the like), then the whole
algorithm costs at most `(⌈log₂ D⌉ + 1) · S D` for `D` points (and a few steps for `D = 0`).
With `S d = O(M(d) log d)` for the fast routines this is the book's `O(M(D) log² D)`. -/
theorem multipointEval_cost_le [ArithCost R] (C : CostModel) {prodF : List R → Chapter2.Poly R}
    {modF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (pc : List R → CostM C Unit) (mc : Chapter2.Poly R → Chapter2.Poly R → CostM C Unit)
    (δ : ℕ) {S : ℕ → ℕ} {K : ℕ} (hsup : Superadditive S)
    (h2K : 2 ≤ K) (hδK : δ.size ≤ K)
    (hmodLen : ∀ x us, (modF x (prodF us)).length ≤ us.length + 1)
    (hnode : ∀ x (T : List R), x.length ≤ T.length + 1 → 2 ≤ T.length → T.length.size ≤ K →
      CostM.cost C (pc (T.take (T.length / 2))) + CostM.cost C (pc (T.drop (T.length / 2))) +
        CostM.cost C (mc x (prodF (T.take (T.length / 2)))) +
        CostM.cost C (mc x (prodF (T.drop (T.length / 2)))) + 6 * T.length * C.lin K ≤
          S T.length)
    (hleaf : ∀ x (T : List R), x.length ≤ T.length + 1 → T.length ≤ max δ 1 → 1 ≤ T.length →
      (T.map fun (t : R) ↦ costOf C (Poly.eval x t)).sum + 6 * T.length * C.lin K ≤ S T.length)
    (x : Chapter2.Poly R) (T : List R) (hx : x.length ≤ T.length + 1) (hTK : T.length.size ≤ K) :
    CostM.cost C (multipointEvalWith.counted prodF modF δ x T pc mc) ≤
      (Nat.clog 2 T.length + 1) * S T.length + 6 * C.lin K := by
  rcases Nat.eq_zero_or_pos T.length with h0 | h0
  · have hδ1 : (max δ 1).size ≤ K := by
      rcases le_total δ 1 with h | h
      · rw [max_eq_right h]; simp; omega
      · rw [max_eq_left h]; exact hδK
    rw [List.length_eq_zero_iff.mp h0]
    cost_unfold multipointEvalWith.counted
    cost_bound
  -- a node splits the points in halves, with the remainders of `x` by their products
  refine (halving_master (fun p : Chapter2.Poly R × List R ↦ p.2.length)
    (fun p ↦ p.1.length ≤ p.2.length + 1 ∧ 1 ≤ p.2.length ∧ p.2.length ≤ T.length)
    (fun p ↦ CostM.cost C (multipointEvalWith.counted prodF modF δ p.1 p.2 pc mc))
    (L := max δ 1) (d := 0) (e := 0) (le_max_right _ _) hsup hsup ?_ ?_ (x, T) ⟨hx, h0, le_rfl⟩
    h0).trans (by simp only [mul_zero, add_zero]; nlinarith)
  · rintro ⟨x, T'⟩ ⟨hx, h1, hT'⟩ h
    dsimp only at hx h1 hT' h ⊢
    have := hleaf x T' hx h h1
    have hu : (T'.length + 1 + (T'.length + 1) + 1) * C.unit ≤ 6 * T'.length * C.unit :=
      Nat.mul_le_mul_right _ (by omega)
    cost_unfold multipointEvalWith.counted
    cost_bound
  · rintro ⟨x, T'⟩ ⟨hx, h1, hT'⟩ h
    dsimp only at hx h1 hT' h ⊢
    refine ⟨(modF x (prodF (T'.take (T'.length / 2))), T'.take (T'.length / 2)),
      (modF x (prodF (T'.drop (T'.length / 2))), T'.drop (T'.length / 2)),
      ⟨(hmodLen _ _), by simp; omega, by simp; omega⟩, ⟨(hmodLen _ _), by simp; omega, by simp; omega⟩,
      by simp; omega, by simp, ?_⟩
    have hK := (Nat.size_le_size hT').trans hTK
    have := hnode x T' hx (by omega) hK
    have := length_multipointEvalWith prodF modF δ (modF x (prodF (T'.take (T'.length / 2))))
      (T'.take (T'.length / 2))
    rw [List.length_take, min_eq_left (Nat.div_le_self _ 2)] at this
    cost_unfold multipointEvalWith.counted
    cost_bound

/-! ### The length hypothesis holds for the fast routines -/

@[val_le] theorem length_fastModMonic_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (f g : Chapter2.Poly R) : (fastModMonic mulF f g).length ≤ g.length - 1 := by
  unfold fastModMonic
  split_ifs with h
  · exact h
  · simp only [List.length_take]; omega

@[val_le] theorem length_prodTree_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (us : List R) : (prodTree mulF us).length ≤ us.length + 1 := by
  rw [prodTree]
  split_ifs
  · rw [length_prodLinear]
  · simp only [monicOfDegree, List.length_append, List.length_take, List.length_singleton]
    omega

/-- In the fast instance, every remainder has at most as many coefficients as there are
points: the hypothesis `hmodLen` of `multipointCost_le`. -/
@[val_le] theorem length_fastModMonic_prodTree_le (mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R)
    (x : Chapter2.Poly R) (us : List R) :
    (fastModMonic mulF x (prodTree mulF us)).length ≤ us.length + 1 := by
  have h₁ := length_fastModMonic_le mulF x (prodTree mulF us)
  have h₂ := length_prodTree_le mulF us
  omega

/-! ### The product tree -/

/-- A leaf of the product tree, `t - u`: a schoolbook product of tiny polynomials. -/
@[cost_le] theorem prodLinear_cost_le [ArithCost R] (C : CostModel) {s : ℕ} (hs : ArithCost.Bounded R C s)
    (us : List R) (h : us.length ≤ 1) : costOf C (prodLinear us) ≤ 40 * (C.unit + s) := by
  match us, h with
  | [], _ => cost_unfold prodLinear.counted
  | [u], _ =>
    have h₁ := Chapter2.Poly.mul_cost_le C hs [-u, 1] (prodLinear [])
    have h₂ : costOf C (prodLinear ([] : List R)) = C.unit := by cost_unfold prodLinear.counted
    have h₃ := (hs u u).2.1
    rw [length_prodLinear] at h₁
    simp only [List.length_cons, List.length_nil] at h₁
    cost_unfold prodLinear.counted

@[cost_le] theorem monicOfDegree_cost_le (C : CostModel) (n : ℕ) (L : Chapter2.Poly R) :
    costOf C (monicOfDegree n L) ≤ (2 * n + 3) * C.unit := by
  cost_unfold monicOfDegree.counted
  simp only [List.length_take]
  cost_bound

/-- **Cost of the product tree**: if a product of inputs of length `≤ m` costs at most
`Mf m`, with `Mf` monotone and superadditive, the tree over `d ≥ 1` points costs at most
`(⌈log₂ d⌉ + 1) · (Mf d + 8 d steps)` for the products and the bookkeeping, and `40`
coefficient operations for each leaf. -/
theorem prodTree_cost_le [ArithCost R] (C : CostModel)
    {mulF : Chapter2.Poly R → Chapter2.Poly R → Chapter2.Poly R}
    (mc : Chapter2.Poly R → Chapter2.Poly R → CostM C Unit) {Mf : ℕ → ℕ} {s K : ℕ}
    (hsup : Superadditive Mf)
    (hM : ∀ (m : ℕ), 1 ≤ m → ∀ (f g : Chapter2.Poly R), f.length ≤ m → g.length ≤ m →
      CostM.cost C (mc f g) ≤ Mf m)
    (hs : ArithCost.Bounded R C s) (h2K : 2 ≤ K) :
    ∀ us : List R, 1 ≤ us.length → us.length.size ≤ K →
      CostM.cost C (prodTree.counted mulF us mc) ≤
        (Nat.clog 2 us.length + 1) * (Mf us.length + 8 * us.length * C.lin K) +
          us.length * (40 * (C.unit + s)) := by
  intro us₀ h1 hK
  -- a node multiplies the trees of the halves: `Mf n` and `8 n` steps on each level
  refine (halving_master List.length (fun us ↦ 1 ≤ us.length ∧ us.length ≤ us₀.length)
    (fun us ↦ CostM.cost C (prodTree.counted mulF us mc)) (F := fun m ↦ Mf m + 8 * m * C.lin K)
    (G := fun m ↦ 8 * m * C.lin K) (L := 1) (d := 0) (e := 40 * (C.unit + s)) le_rfl
    (hsup.add fun _ _ _ _ ↦ le_of_eq (by ring)) (fun _ _ _ _ ↦ le_of_eq (by ring))
    ?_ ?_ us₀ ⟨h1, le_rfl⟩ h1).trans (by simp only [mul_zero, add_zero]; nlinarith)
  · rintro us ⟨h1, -⟩ hn
    have := prodLinear_cost_le C hs us hn
    have h1' : us.length = 1 := by omega
    cost_unfold prodTree.counted
    rw [h1'] at *
    cost_bound
  · rintro us ⟨h1, hn₀⟩ hn
    refine ⟨us.take (us.length / 2), us.drop (us.length / 2), ⟨by simp; omega, by simp; omega⟩,
      ⟨by simp; omega, by simp; omega⟩, by simp; omega, by simp, ?_⟩
    have := (Nat.size_le_size hn₀).trans hK
    have := hM us.length (by omega) (prodTree mulF (us.take (us.length / 2)))
      (prodTree mulF (us.drop (us.length / 2)))
      ((length_prodTree_le mulF _).trans (by simp; omega))
      ((length_prodTree_le mulF _).trans (by simp; omega))
    cost_unfold prodTree.counted
    cost_bound

end PrimeNumbers.Chapter9
