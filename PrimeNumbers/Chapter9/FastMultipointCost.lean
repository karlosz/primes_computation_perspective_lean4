import PrimeNumbers.Chapter9.FastMultipoint
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic

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

@[val_le] theorem length_mul_le {R : Type} [CommSemiring R] (f g : Chapter2.Poly R) :
    (Chapter2.Poly.mul f g).length ≤ f.length + g.length := by
  induction f with
  | nil => simp [Chapter2.Poly.mul]
  | cons a f ih =>
    simp only [Chapter2.Poly.mul, Chapter2.Poly.length_add, Chapter2.Poly.length_smul, List.length_cons]
    omega

@[val_le] theorem length_mulMod_le (n : ℕ) (f g : Chapter2.Poly (ZMod n)) :
    (mulMod n f g).length ≤ f.length + g.length := by
  rw [mulMod, List.length_map, mulNatAuto_eq]
  simpa using length_mul_le (f.map ZMod.val) (g.map ZMod.val)

section Bounds

variable (C : CostModel) (n : ℕ)

/-- The cost of an operation on residues modulo `n` (`ArithCost.bounded_zmod`). -/
def zcost : ℕ := C.mulMod n.size + 2 * C.add n.size n.size

/-- **The cost of a product in `Z_n[t]`** of polynomials of length `≤ m` by binary
segmentation (`mulMod_cost_le`, for `m ≥ 1`): one multiplication of `segWidth n m · m`-bit
integers, the packings and the unpacking, and `O(m)` small operations. -/
def polyMulBound (m : ℕ) : ℕ :=
  C.mul (segWidth n m * m) (segWidth n m * m) +
    3 * halvingBound (2 * C.unit + 6 * C.add (2 * segWidth n m) (2 * segWidth n m))
      (4 * C.unit + 4 * C.add (2 * segWidth n m) (2 * segWidth n m) +
        C.mul (segWidth n m).size (2 * segWidth n m)) (2 * m) +
    m * (2 * C.mul (2 * segWidth n m) (2 * segWidth n m) + 22 * C.lin (2 * segWidth n m) +
      2 * C.divMod (segWidth n m) n.size + 9 * C.unit)

theorem segWidth_mono : Monotone (segWidth n) := fun a b h ↦ by
  have := Nat.size_le_size h; unfold segWidth; omega

/-- The parts of `polyMulBound` that depend on the width only. -/
private theorem width_parts_mono {w w' : ℕ} (h : w ≤ w') :
    2 * C.unit + 6 * C.add (2 * w) (2 * w) ≤ 2 * C.unit + 6 * C.add (2 * w') (2 * w') ∧
    4 * C.unit + 4 * C.add (2 * w) (2 * w) + C.mul w.size (2 * w) ≤
      4 * C.unit + 4 * C.add (2 * w') (2 * w') + C.mul w'.size (2 * w') ∧
    2 * C.mul (2 * w) (2 * w) + 22 * C.lin (2 * w) + 2 * C.divMod w n.size + 9 * C.unit ≤
      2 * C.mul (2 * w') (2 * w') + 22 * C.lin (2 * w') + 2 * C.divMod w' n.size + 9 * C.unit := by
  have h₁ := C.add_mono (show 2 * w ≤ 2 * w' by omega) (show 2 * w ≤ 2 * w' by omega)
  have h₂ := C.mul_mono (Nat.size_le_size h) (show 2 * w ≤ 2 * w' by omega)
  have h₃ := C.mul_mono (show 2 * w ≤ 2 * w' by omega) (show 2 * w ≤ 2 * w' by omega)
  have h₄ := C.lin_mono (show 2 * w ≤ 2 * w' by omega)
  have h₅ := C.divMod_mono n.size h
  omega

theorem polyMulBound_superadditive (hC : C.SuperadditiveMul) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    polyMulBound C n a + polyMulBound C n b ≤ polyMulBound C n (a + b) := by
  have wa := segWidth_mono n (Nat.le_add_right a b)
  have wb := segWidth_mono n (Nat.le_add_left b a)
  set w := segWidth n (a + b)
  obtain ⟨a₁, a₂, a₃⟩ := width_parts_mono C n wa
  obtain ⟨b₁, b₂, b₃⟩ := width_parts_mono C n wb
  have h₁ : C.mul (segWidth n a * a) (segWidth n a * a) ≤ C.mul (w * a) (w * a) :=
    C.mul_mono (Nat.mul_le_mul_right a wa) (Nat.mul_le_mul_right a wa)
  have h₂ : C.mul (segWidth n b * b) (segWidth n b * b) ≤ C.mul (w * b) (w * b) :=
    C.mul_mono (Nat.mul_le_mul_right b wb) (Nat.mul_le_mul_right b wb)
  have h₃ := hC (w * a) (w * b)
  rw [← mul_add] at h₃
  have hA := halvingBound_le a₁ a₂ (le_refl (2 * a))
  have hB := halvingBound_le b₁ b₂ (le_refl (2 * b))
  have hS := halvingBound_superadditive (2 * C.unit + 6 * C.add (2 * w) (2 * w))
    (4 * C.unit + 4 * C.add (2 * w) (2 * w) + C.mul w.size (2 * w))
    (show 1 ≤ 2 * a by omega) (show 1 ≤ 2 * b by omega)
  rw [show 2 * a + 2 * b = 2 * (a + b) by ring] at hS
  have l₁ := Nat.mul_le_mul_left a a₃
  have l₂ := Nat.mul_le_mul_left b b₃
  unfold polyMulBound
  nlinarith

@[cost_le] theorem mulMod_cost_le' [NeZero n] {m : ℕ} (hm : 1 ≤ m) (f g : Chapter2.Poly (ZMod n))
    (hf : f.length ≤ m) (hg : g.length ≤ m) : costOf C (mulMod n f g) ≤ polyMulBound C n m := by
  refine (mulMod_cost_le C f g hf hg).trans ?_
  unfold mulModBound mulNatBound polyMulBound
  set w := segWidth n m
  have e₁ : (5 * m + 8) * C.lin (2 * w) + (3 * m + 6) * C.lin (2 * w) ≤ m * (22 * C.lin (2 * w)) := by
    nlinarith
  have e₂ : 2 * C.mul (2 * w) (2 * w) ≤ m * (2 * C.mul (2 * w) (2 * w)) := by nlinarith
  have e₃ : 2 * m * C.divMod w n.size = m * (2 * C.divMod w n.size) := by ring
  have e₄ : (4 * m + 5) * C.unit ≤ m * (9 * C.unit) := by nlinarith
  have e₅ : m * (2 * C.mul (2 * w) (2 * w) + 22 * C.lin (2 * w) + 2 * C.divMod w n.size +
      9 * C.unit) = m * (2 * C.mul (2 * w) (2 * w)) + m * (22 * C.lin (2 * w)) +
      m * (2 * C.divMod w n.size) + m * (9 * C.unit) := by ring
  omega

/-- The cost of the `⌈log₂⌉` computations on numbers of `z` bits (`clog_cost_le`). -/
def clogBound (z : ℕ) : ℕ := C.mul (2 * z) (2 * z) + 2 * C.divBound (2 * z) + 4 * C.lin (2 * z + 1)

theorem clogBound_mono : Monotone (clogBound C) := fun a b h ↦ by
  unfold clogBound
  have := C.mul_mono (show 2 * a ≤ 2 * b by omega) (show 2 * a ≤ 2 * b by omega)
  have := C.divBound_mono (show 2 * a ≤ 2 * b by omega)
  have := C.lin_mono (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  omega

/-- The part of the per-node bound multiplied by the number of levels of the subroutines. -/
def nodeInner (K d : ℕ) : ℕ :=
  polyMulBound C n d + 4 * polyMulBound C n (4 * d) +
    d * (16 * C.lin K + 106 * (C.unit + zcost C n) + 8 * C.lin ((4 * d).size + 2))

/-- **The per-node bound of fast multipoint evaluation** at a node with `d` points: the two
half-products (product trees) and the two fast remainders, or at a leaf (at most `max δ 1`
points) direct evaluation, with the bookkeeping on lengths of at most `K` bits. -/
def nodeBound (δ K d : ℕ) : ℕ :=
  (Nat.clog 2 d + 2) * nodeInner C n K d +
    d * (6 * clogBound C (2 * d).size + 248 * (C.unit + zcost C n) + 16 * C.lin ((4 * d).size + 2) +
      6 * C.lin K + (δ + 3) * (C.unit + 2 * zcost C n))

theorem clog_succ_le (d : ℕ) : Nat.clog 2 (d + 1) ≤ Nat.clog 2 d + 1 :=
  Nat.clog_le_of_le_pow (by
    have := Nat.le_pow_clog (b := 2) (by norm_num) d
    have := Nat.one_le_two_pow (n := Nat.clog 2 d)
    rw [pow_succ]; omega)

theorem nodeInner_superadditive (hC : C.SuperadditiveMul) (K : ℕ) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : nodeInner C n K a + nodeInner C n K b ≤ nodeInner C n K (a + b) := by
  unfold nodeInner
  have p₁ := polyMulBound_superadditive C n hC ha hb
  have p₂ := polyMulBound_superadditive C n hC (show 1 ≤ 4 * a by omega) (show 1 ≤ 4 * b by omega)
  rw [← mul_add] at p₂
  have la := C.lin_mono (show (4 * a).size + 2 ≤ (4 * (a + b)).size + 2 by have := Nat.size_le_size (show 4 * a ≤ 4 * (a + b) by omega); omega)
  have lb := C.lin_mono (show (4 * b).size + 2 ≤ (4 * (a + b)).size + 2 by have := Nat.size_le_size (show 4 * b ≤ 4 * (a + b) by omega); omega)
  have l₁ := Nat.mul_le_mul_left a (show 16 * C.lin K + 106 * (C.unit + zcost C n) +
    8 * C.lin ((4 * a).size + 2) ≤ 16 * C.lin K + 106 * (C.unit + zcost C n) +
      8 * C.lin ((4 * (a + b)).size + 2) by omega)
  have l₂ := Nat.mul_le_mul_left b (show 16 * C.lin K + 106 * (C.unit + zcost C n) +
    8 * C.lin ((4 * b).size + 2) ≤ 16 * C.lin K + 106 * (C.unit + zcost C n) +
      8 * C.lin ((4 * (a + b)).size + 2) by omega)
  nlinarith

theorem nodeBound_superadditive (hC : C.SuperadditiveMul) (δ K : ℕ) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : nodeBound C n δ K a + nodeBound C n δ K b ≤ nodeBound C n δ K (a + b) := by
  unfold nodeBound
  have ca := Nat.clog_mono_right 2 (Nat.le_add_right a b)
  have cb := Nat.clog_mono_right 2 (Nat.le_add_left b a)
  have hG := nodeInner_superadditive C n hC K ha hb
  have e₁ : (Nat.clog 2 a + 2) * nodeInner C n K a + (Nat.clog 2 b + 2) * nodeInner C n K b ≤
      (Nat.clog 2 (a + b) + 2) * nodeInner C n K (a + b) := by
    calc _ ≤ (Nat.clog 2 (a + b) + 2) * nodeInner C n K a +
          (Nat.clog 2 (a + b) + 2) * nodeInner C n K b := by gcongr
      _ = (Nat.clog 2 (a + b) + 2) * (nodeInner C n K a + nodeInner C n K b) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hG
  have c₁ := clogBound_mono C (Nat.size_le_size (Nat.mul_le_mul_left 2 (Nat.le_add_right a b)))
  have c₂ := clogBound_mono C (Nat.size_le_size (Nat.mul_le_mul_left 2 (Nat.le_add_left b a)))
  have la := C.lin_mono (show (4 * a).size + 2 ≤ (4 * (a + b)).size + 2 by have := Nat.size_le_size (show 4 * a ≤ 4 * (a + b) by omega); omega)
  have lb := C.lin_mono (show (4 * b).size + 2 ≤ (4 * (a + b)).size + 2 by have := Nat.size_le_size (show 4 * b ≤ 4 * (a + b) by omega); omega)
  set Z := 248 * (C.unit + zcost C n) + 6 * C.lin K + (δ + 3) * (C.unit + 2 * zcost C n)
  have l₁ := Nat.mul_le_mul_left a (show 6 * clogBound C (2 * a).size + Z + 16 * C.lin ((4 * a).size + 2) ≤
    6 * clogBound C (2 * (a + b)).size + Z + 16 * C.lin ((4 * (a + b)).size + 2) by omega)
  have l₂ := Nat.mul_le_mul_left b (show 6 * clogBound C (2 * b).size + Z + 16 * C.lin ((4 * b).size + 2) ≤
    6 * clogBound C (2 * (a + b)).size + Z + 16 * C.lin ((4 * (a + b)).size + 2) by omega)
  have : ∀ x y, 6 * x + 248 * (C.unit + zcost C n) + 16 * y + 6 * C.lin K +
      (δ + 3) * (C.unit + 2 * zcost C n) = 6 * x + Z + 16 * y := fun x y ↦ by simp only [Z]; ring
  rw [this, this, this]
  nlinarith

end Bounds

/-- A product by binary segmentation, as charged inside the fast routines. -/
theorem mulMod_charge_le (C : CostModel) (n : ℕ) [NeZero n] (m : ℕ) (hm : 1 ≤ m)
    (f g : Chapter2.Poly (ZMod n)) (hf : f.length ≤ m) (hg : g.length ≤ m) :
    CostM.cost C (bind (mulMod.counted (countedMonad := CostM C) n f g) fun _ ↦ pure ()) ≤
      polyMulBound C n m := by
  have := mulMod_cost_le' C n hm f g hf hg
  cost_simp
  exact this

/-- **Running time of fast multipoint evaluation over `Z_n` (Algorithm 9.6.7 with
Algorithms 9.6.1, 9.6.2, 9.6.4)**, for any cost model with superadditive multiplication: for
`D` points, at most `(⌈log₂ D⌉ + 1) · nodeBound D` bit operations — `O(log D)` levels, each
costing `O(log D)` products of polynomials of length `O(D)` (`polyMulBound`) — plus the
bookkeeping on lengths, of `K = size (D + δ + 2)` bits. -/
@[cost_le] theorem multipointEvalFast_cost_le (C : CostModel) {n : ℕ} [NeZero n] (hC : C.SuperadditiveMul)
    (δ : ℕ) (x : Chapter2.Poly (ZMod n)) (T : List (ZMod n)) (hx : x.length ≤ T.length + 1) :
    costOf C (multipointEvalFast n δ x T) ≤
      (Nat.clog 2 T.length + 1) * nodeBound C n δ (T.length + δ + 2).size T.length +
        7 * C.lin (T.length + δ + 2).size := by
  set K := (T.length + δ + 2).size
  have hs : ArithCost.Bounded (ZMod n) C (zcost C n) := ArithCost.bounded_zmod C n
  have h2K : 2 ≤ K := by
    have := Nat.size_le_size (show 2 ≤ T.length + δ + 2 by omega)
    rw [Nat.size_two] at this; omega
  have hTK : T.length.size ≤ K := Nat.size_le_size (by omega)
  have hδK : δ.size ≤ K := Nat.size_le_size (by omega)
  have hMul := mulMod_charge_le C n
  cost_unfold multipointEvalFast.counted
  refine (Nat.add_le_add_left (multipointEval_cost_le C _ _ δ
    (fun a b ↦ nodeBound_superadditive C n hC δ K) h2K hδK
    (fun x us ↦ length_fastModMonic_prodTree_le (mulMod n) x us) ?node ?leaf x T hx hTK)
      C.unit).trans (by unfold CostModel.lin; omega)
  case node =>
    -- a node: two product trees and two fast remainders
    intro x T hx hT hTK
    set d := T.length
    set u := T.take (d / 2)
    set v := T.drop (d / 2)
    have hu : u.length = d / 2 := by simp [u, d]; omega
    have hv : v.length = d - d / 2 := by simp [v, d]
    have pt := fun (us : List (ZMod n)) ↦
      prodTree_cost_le C (mulF := mulMod n) _
        (fun a b ↦ polyMulBound_superadditive C n hC) hMul hs h2K us
    have pu := pt u (by omega) ((Nat.size_le_size (by omega)).trans hTK)
    have pv := pt v (by omega) ((Nat.size_le_size (by omega)).trans hTK)
    have hlenM := length_mulMod_le n
    have fm := fun (w : Chapter2.Poly (ZMod n)) (hw : w.length ≤ 4 * d) ↦
      fastModMonic_cost_le C (mulF := mulMod n) _ (M := polyMulBound C n (4 * d))
        (D := 4 * d) (fun f g hf hg ↦ hMul (4 * d) (by omega) f g hf hg) hlenM hs x w
        (by omega) hw
    have fu := fm (prodTree (mulMod n) u) (by have := length_prodTree_le (mulMod n) u; omega)
    have fv := fm (prodTree (mulMod n) v) (by have := length_prodTree_le (mulMod n) v; omega)
    simp only [cost_simps] at pu pv fu fv ⊢
    unfold nodeBound nodeInner
    set cl := Nat.clog 2 d
    set P := polyMulBound C n
    set W := C.unit + zcost C n
    set L4 := C.lin ((4 * d).size + 2)
    set LK := C.lin K
    -- the product trees, on the two halves
    have hcu := Nat.clog_mono_right 2 (show u.length ≤ d by omega)
    have hcv := Nat.clog_mono_right 2 (show v.length ≤ d by omega)
    have hsplit := polyMulBound_superadditive C n hC (a := u.length) (b := v.length)
      (by omega) (by omega)
    rw [show u.length + v.length = d by omega] at hsplit
    have A : (Nat.clog 2 u.length + 1) * (P u.length + 8 * u.length * LK) +
        u.length * (40 * W) + ((Nat.clog 2 v.length + 1) * (P v.length + 8 * v.length * LK) +
        v.length * (40 * W)) ≤ (cl + 1) * (P d + 8 * d * LK) + d * (40 * W) := by
      calc _ ≤ (cl + 1) * (P u.length + 8 * u.length * LK) + u.length * (40 * W) +
            ((cl + 1) * (P v.length + 8 * v.length * LK) + v.length * (40 * W)) := by gcongr
        _ = (cl + 1) * (P u.length + P v.length + 8 * (u.length + v.length) * LK) +
            (u.length + v.length) * (40 * W) := by ring
        _ ≤ _ := by rw [show u.length + v.length = d by omega]; gcongr
    -- the remainders
    have hcx : Nat.clog 2 x.length + 1 ≤ cl + 2 := by
      have := Nat.clog_mono_right 2 hx; have := clog_succ_le d; omega
    have hsx : x.length.size + 2 ≤ 3 * d := by have := size_le_self x.length; omega
    have hbx : clogBound C x.length.size ≤ clogBound C (2 * d).size :=
      clogBound_mono C (Nat.size_le_size (by omega))
    set CB := clogBound C (2 * d).size
    have B : (Nat.clog 2 x.length + 1) * (2 * P (4 * d) + (11 * (4 * d) + 9) * W + 4 * L4) +
        (x.length.size + 2) * (C.mul (2 * x.length.size) (2 * x.length.size) +
          2 * C.divBound (2 * x.length.size) + 4 * C.lin (2 * x.length.size + 1)) ≤
        (cl + 2) * (2 * P (4 * d) + (11 * (4 * d) + 9) * W + 4 * L4) + 3 * d * CB := by
      gcongr; exact hbx
    have e₁ : (cl + 2) * W ≤ (cl + 2) * (d * W) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    have e₂ : (cl + 2) * L4 ≤ (cl + 2) * (d * L4) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    have e₃ : W ≤ d * W := Nat.le_mul_of_pos_left _ (by omega)
    have e₄ : L4 ≤ d * L4 := Nat.le_mul_of_pos_left _ (by omega)
    have e₅ : (cl + 1) * (8 * d * LK) ≤ (cl + 2) * (d * (16 * LK)) := by
      rw [show 8 * d * LK = d * (8 * LK) by ring]; gcongr <;> omega
    have e₆ : (cl + 1) * P d ≤ (cl + 2) * P d := by gcongr; omega
    have e₇ := Nat.zero_le (d * ((δ + 3) * (C.unit + 2 * zcost C n)))
    have e₈ := Nat.zero_le (d * (6 * LK))
    have e₉ := Nat.zero_le ((cl + 2) * (4 * P (4 * d)))
    calc _ ≤ (cl + 1) * (P d + 8 * d * LK) + d * (40 * W) +
          2 * ((cl + 2) * (2 * P (4 * d) + (11 * (4 * d) + 9) * W + 4 * L4) + 3 * d * CB +
            (16 * (4 * d) + 20) * W + 8 * L4) + 6 * d * LK := by
          clear hMul fm pt; linarith
      _ ≤ _ := by
          clear hMul fm pt pu pv fu fv A B
          linarith
  case leaf =>
    -- a leaf: Horner's rule at each point
    intro x T hx hT hT1
    have hxl : x.length ≤ δ + 2 := by have : max δ 1 ≤ δ + 1 := max_le (by omega) (by omega); omega
    have := sum_map_le_length_mul _ _ fun t (_ : t ∈ T) ↦ Poly.eval_cost_le C hs x t
    have : T.length * ((x.length + 1) * (C.unit + 2 * zcost C n)) ≤
        T.length * ((δ + 3) * (C.unit + 2 * zcost C n)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    unfold nodeBound
    nlinarith

end PrimeNumbers.Chapter9
