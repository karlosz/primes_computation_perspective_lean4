import PrimeNumbers.Chapter9.FastMultipoint

/-!
# Running time of fast multipoint evaluation over `Z_n` (Algorithms 9.6.1–9.6.7)

The derived cost of `multipointEvalFast` — Algorithm 9.6.7 with the product tree and the fast
remainder (Algorithms 9.6.2, 9.6.4), all products by binary segmentation (Algorithm 9.6.1) —
is at most `(⌈log₂ D⌉ + 1) · S(D)` for `D` points, where the per-node bound `S(d)` is
`O(log d)` products of polynomials of length `O(d)` plus lower-order terms
(`multipointEvalFast_cost_le`).  A product of length-`m` polynomials over `Z_n` costs one
multiplication of `O(m (log n + log m))`-bit integers (`polyMulBound`), so with a
quasi-linear integer multiplication the whole evaluation is quasi-linear in `D log n`, up to
`log² D` factors: the book's `O(M(D) log² D)`.

The level argument needs the multiplication cost to be *superadditive*,
`C.mul a a + C.mul b b ≤ C.mul (a + b) (a + b)` — true for the grammar-school and Karatsuba
models, and for every cost growing at least linearly.
-/

namespace PrimeNumbers.Chapter9

open PrimeNumbers.Chapter2

/-- The multiplication cost grows at least linearly: `M(a) + M(b) ≤ M(a + b)`. -/
def CostModel.SuperadditiveMul (C : CostModel) : Prop :=
  ∀ a b, C.mul a a + C.mul b b ≤ C.mul (a + b) (a + b)

theorem school_superadditiveMul : school.SuperadditiveMul := fun a b ↦ by
  simp only [school_mul]; nlinarith

theorem length_mul_le {R : Type} [CommSemiring R] (f g : Chapter2.Poly R) :
    (Chapter2.Poly.mul f g).length ≤ f.length + g.length := by
  induction f with
  | nil => simp [Chapter2.Poly.mul]
  | cons a f ih =>
    simp only [Chapter2.Poly.mul, Chapter2.Poly.length_add, Chapter2.Poly.length_smul, List.length_cons]
    omega

theorem length_mulMod_le (n : ℕ) (f g : Chapter2.Poly (ZMod n)) :
    (mulMod n f g).length ≤ f.length + g.length := by
  rw [mulMod, List.length_map, mulNatAuto_eq]
  simpa using length_mul_le (f.map ZMod.val) (g.map ZMod.val)

section Bounds

variable (C : CostModel) (n : ℕ)

/-- **The cost of a product in `Z_n[t]`** of polynomials of length `≤ m` by binary
segmentation (`mulMod_cost_le`, for `m ≥ 1`): one multiplication of
`segWidth n m · m`-bit integers and `8m` small ones. -/
def polyMulBound (m : ℕ) : ℕ :=
  C.mul (segWidth n m * m) (segWidth n m * m) +
    8 * m * C.mul (2 * segWidth n m) (2 * segWidth n m)

theorem segWidth_mono : Monotone (segWidth n) := fun a b h ↦ by
  have := Nat.size_le_size h; unfold segWidth; omega

theorem polyMulBound_mono : Monotone (polyMulBound C n) := fun a b h ↦ by
  have hw := segWidth_mono n h
  unfold polyMulBound
  exact Nat.add_le_add (C.mul_mono (Nat.mul_le_mul hw h) (Nat.mul_le_mul hw h))
    (Nat.mul_le_mul (by omega) (C.mul_mono (by omega) (by omega)))

theorem polyMulBound_superadditive (hC : C.SuperadditiveMul) (a b : ℕ) :
    polyMulBound C n a + polyMulBound C n b ≤ polyMulBound C n (a + b) := by
  have ha := segWidth_mono n (Nat.le_add_right a b)
  have hb := segWidth_mono n (Nat.le_add_left b a)
  set w := segWidth n (a + b)
  have h₁ : C.mul (segWidth n a * a) (segWidth n a * a) ≤ C.mul (w * a) (w * a) :=
    C.mul_mono (Nat.mul_le_mul_right a ha) (Nat.mul_le_mul_right a ha)
  have h₂ : C.mul (segWidth n b * b) (segWidth n b * b) ≤ C.mul (w * b) (w * b) :=
    C.mul_mono (Nat.mul_le_mul_right b hb) (Nat.mul_le_mul_right b hb)
  have h₃ := hC (w * a) (w * b)
  rw [← mul_add] at h₃
  have h₄ : C.mul (2 * segWidth n a) (2 * segWidth n a) ≤ C.mul (2 * w) (2 * w) :=
    C.mul_mono (by omega) (by omega)
  have h₅ : C.mul (2 * segWidth n b) (2 * segWidth n b) ≤ C.mul (2 * w) (2 * w) :=
    C.mul_mono (by omega) (by omega)
  unfold polyMulBound
  nlinarith

theorem mulMod_cost_le' [NeZero n] {m : ℕ} (hm : 1 ≤ m) (f g : Chapter2.Poly (ZMod n))
    (hf : f.length ≤ m) (hg : g.length ≤ m) : costOf C (mulMod n f g) ≤ polyMulBound C n m := by
  refine (mulMod_cost_le C f g hf hg).trans ?_
  unfold polyMulBound
  have : (6 * m + 2) * C.mul (2 * segWidth n m) (2 * segWidth n m) ≤
      8 * m * C.mul (2 * segWidth n m) (2 * segWidth n m) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The cost of the `⌈log₂⌉` computations on numbers of `z` bits. -/
def clogBound (z : ℕ) : ℕ := C.mul (2 * z) (2 * z) + 2 * C.divBound (2 * z)

theorem clogBound_mono : Monotone (clogBound C) := fun a b h ↦
  Nat.add_le_add (C.mul_mono (by omega) (by omega)) (Nat.mul_le_mul_left 2 (C.divBound_mono (by omega)))

/-- **The per-node bound of fast multipoint evaluation** at a node with `d` points: the two
half-products (product trees) and the two fast remainders, or at a leaf (at most
`max δ 1` points) direct evaluation. -/
def nodeBound (δ d : ℕ) : ℕ :=
  (Nat.clog 2 d + 2) *
      (polyMulBound C n d + 4 * polyMulBound C n (4 * d) + 18 * d * C.mulMod n.size) +
    6 * d * clogBound C (2 * d).size + (δ + 2) * d * C.mulMod n.size

theorem clog_succ_le (d : ℕ) : Nat.clog 2 (d + 1) ≤ Nat.clog 2 d + 1 :=
  Nat.clog_le_of_le_pow (by
    have := Nat.le_pow_clog (b := 2) (by norm_num) d
    have := Nat.one_le_two_pow (n := Nat.clog 2 d)
    rw [pow_succ]; omega)

theorem size_le_self' (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

theorem nodeBound_mono (δ : ℕ) : Monotone (nodeBound C n δ) := fun a b h ↦ by
  unfold nodeBound
  have h₁ := Nat.clog_mono_right 2 h
  have h₂ := polyMulBound_mono C n h
  have h₃ := polyMulBound_mono C n (Nat.mul_le_mul_left 4 h)
  have h₄ := clogBound_mono C (Nat.size_le_size (Nat.mul_le_mul_left 2 h))
  gcongr

theorem nodeBound_superadditive (hC : C.SuperadditiveMul) (δ a b : ℕ) :
    nodeBound C n δ a + nodeBound C n δ b ≤ nodeBound C n δ (a + b) := by
  unfold nodeBound
  have ha := Nat.clog_mono_right 2 (Nat.le_add_right a b)
  have hb := Nat.clog_mono_right 2 (Nat.le_add_left b a)
  have p₁ := polyMulBound_superadditive C n hC a b
  have p₂ := polyMulBound_superadditive C n hC (4 * a) (4 * b)
  rw [← mul_add] at p₂
  have c₁ := clogBound_mono C (Nat.size_le_size (Nat.mul_le_mul_left 2 (Nat.le_add_right a b)))
  have c₂ := clogBound_mono C (Nat.size_le_size (Nat.mul_le_mul_left 2 (Nat.le_add_left b a)))
  set G := fun d ↦ polyMulBound C n d + 4 * polyMulBound C n (4 * d) + 18 * d * C.mulMod n.size
  have hG : G a + G b ≤ G (a + b) := by simp only [G]; nlinarith
  have e₁ : (Nat.clog 2 a + 2) * G a + (Nat.clog 2 b + 2) * G b ≤
      (Nat.clog 2 (a + b) + 2) * G (a + b) := by
    calc (Nat.clog 2 a + 2) * G a + (Nat.clog 2 b + 2) * G b
        ≤ (Nat.clog 2 (a + b) + 2) * G a + (Nat.clog 2 (a + b) + 2) * G b := by gcongr
      _ = (Nat.clog 2 (a + b) + 2) * (G a + G b) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hG
  simp only [G] at e₁
  nlinarith

end Bounds

/-- **Running time of fast multipoint evaluation over `Z_n` (Algorithm 9.6.7 with
Algorithms 9.6.1, 9.6.2, 9.6.4)**, for any cost model with superadditive multiplication: for
`D` points, at most `(⌈log₂ D⌉ + 1) · nodeBound D` bit operations — `O(log D)` levels, each
costing `O(log D)` products of polynomials of length `O(D)` (`polyMulBound`). -/
theorem multipointEvalFast_cost_le (C : CostModel) {n : ℕ} [NeZero n] (hC : C.SuperadditiveMul)
    (δ : ℕ) (x : Chapter2.Poly (ZMod n)) (T : List (ZMod n)) (hx : x.length ≤ T.length + 1) :
    costOf C (multipointEvalFast n δ x T) ≤
      (Nat.clog 2 T.length + 1) * nodeBound C n δ T.length := by
  have hs : ∀ a b : ZMod n, MulCost.mulCost C a b ≤ C.mulMod n.size := fun _ _ ↦ le_rfl
  -- a product by binary segmentation, as charged inside the fast routines
  have hMul : ∀ m, 1 ≤ m → ∀ f g : Chapter2.Poly (ZMod n), f.length ≤ m → g.length ≤ m →
      CostM.cost C (bind (mulMod.counted (countedMonad := CostM C) n f g) fun _ ↦ pure ()) ≤
        polyMulBound C n m := fun m hm f g hf hg ↦ by
    have := mulMod_cost_le' C n hm f g hf hg
    cost_simp
    exact this
  cost_unfold multipointEvalFast.counted
  refine multipointEval_cost_le C _ _ δ (nodeBound_mono C n δ) (nodeBound_superadditive C n hC δ)
    (fun x us ↦ length_fastModMonic_prodTree_le (mulMod n) x us) ?_ ?_ x T hx
  · -- a node: two product trees and two fast remainders
    intro x T hx hT
    set d := T.length
    set u := T.take (d / 2)
    set v := T.drop (d / 2)
    have hu : u.length = d / 2 := by simp [u, d]; omega
    have hv : v.length = d - d / 2 := by simp [v, d]
    have pt := fun (us : List (ZMod n)) ↦
      prodTree_cost_le C (mulF := mulMod n) _ (polyMulBound_mono C n)
        (polyMulBound_superadditive C n hC) hMul hs us
    have pu := pt u
    have pv := pt v
    have hlenM := length_mulMod_le n
    have fm := fun (w : Chapter2.Poly (ZMod n)) ↦
      fastModMonic_cost_le C (mulF := mulMod n) _ (M := polyMulBound C n (4 * d))
        (D := 4 * d) (fun f g hf hg ↦ hMul (4 * d) (by omega) f g hf hg) hlenM hs x w
        (by omega)
    have fu := fm (prodTree (mulMod n) u)
    have fv := fm (prodTree (mulMod n) v)
    simp only [cost_simps] at pu pv fu fv ⊢
    -- the sizes
    have hcu : Nat.clog 2 u.length + 1 ≤ Nat.clog 2 d + 2 :=
      by have := Nat.clog_mono_right 2 (show u.length ≤ d by omega); omega
    have hcv : Nat.clog 2 v.length + 1 ≤ Nat.clog 2 d + 2 :=
      by have := Nat.clog_mono_right 2 (show v.length ≤ d by omega); omega
    have hcx : Nat.clog 2 x.length + 1 ≤ Nat.clog 2 d + 2 := by
      have := Nat.clog_mono_right 2 hx; have := clog_succ_le d; omega
    have hsx : x.length.size + 1 ≤ 3 * d := by
      have := size_le_self' x.length; omega
    have hbx : clogBound C x.length.size ≤ clogBound C (2 * d).size :=
      clogBound_mono C (Nat.size_le_size (by omega))
    have hsplit := polyMulBound_superadditive C n hC u.length v.length
    rw [show u.length + v.length = d by omega] at hsplit
    have hmu := polyMulBound_mono C n (show u.length ≤ d by omega)
    unfold clogBound at hbx
    set cl := Nat.clog 2 d
    set sm := C.mulMod n.size
    set M4 := polyMulBound C n (4 * d)
    have a₁ : (Nat.clog 2 u.length + 1) * polyMulBound C n u.length ≤
        (cl + 2) * polyMulBound C n u.length := Nat.mul_le_mul_right _ hcu
    have a₂ : (Nat.clog 2 v.length + 1) * polyMulBound C n v.length ≤
        (cl + 2) * polyMulBound C n v.length := Nat.mul_le_mul_right _ hcv
    have a₃ : (cl + 2) * (polyMulBound C n u.length + polyMulBound C n v.length) ≤
        (cl + 2) * polyMulBound C n d := Nat.mul_le_mul_left _ hsplit
    have a₄ : (Nat.clog 2 x.length + 1) * (2 * M4 + 2 * (4 * d) * sm) ≤
        (cl + 2) * (2 * M4 + 2 * (4 * d) * sm) := Nat.mul_le_mul_right _ hcx
    have a₅ : (x.length.size + 1) * (C.mul (2 * x.length.size) (2 * x.length.size) +
        2 * C.divBound (2 * x.length.size)) ≤
        3 * d * (C.mul (2 * (2 * d).size) (2 * (2 * d).size) +
          2 * C.divBound (2 * (2 * d).size)) := Nat.mul_le_mul hsx hbx
    have a₆ : u.length * (2 * sm) + v.length * (2 * sm) = 2 * d * sm := by
      rw [← add_mul, show u.length + v.length = d by omega]; ring
    have a₇ : 2 * d * sm ≤ (cl + 2) * (2 * d * sm) := Nat.le_mul_of_pos_left _ (by omega)
    unfold nodeBound clogBound
    nlinarith
  · -- a leaf: Horner's rule at each point
    intro x T hx hT
    have : (T.map fun (t : ZMod n) ↦ costOf C (Poly.eval x t)).sum ≤ T.length * (x.length * C.mulMod n.size) :=
      sum_map_le_length_mul _ _ fun t _ ↦ Poly.eval_cost_le C hs x t
    unfold nodeBound
    have hxl : x.length ≤ δ + 2 := by omega
    have : T.length * (x.length * C.mulMod n.size) ≤ (δ + 2) * T.length * C.mulMod n.size := by
      calc T.length * (x.length * C.mulMod n.size) = x.length * T.length * C.mulMod n.size := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hxl)
    omega



end PrimeNumbers.Chapter9
