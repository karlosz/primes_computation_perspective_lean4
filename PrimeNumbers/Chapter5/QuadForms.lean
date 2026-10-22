import PrimeNumbers.Chapter9.CountedLib
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Size
import Mathlib.RingTheory.Coprime.Basic

/-!
# §5.6 Binary quadratic forms

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.6.

* `QF`, `QF.subst`, `QF.Equiv` — forms `(a, b, c)`, unimodular changes of variables (5.1)
  and the equivalence they generate (Exercise 5.10); equivalent forms have the same
  discriminant and represent the same numbers.
* `QF.Reduced` — the reduced forms (5.2); `Reduced.eq_of_equiv` and
  `existsUnique_reduced_equiv`: **Theorem 5.6.1**, every form of negative discriminant with
  `a > 0` is equivalent to exactly one reduced form.
* `reduce` — **Algorithm 5.6.2** (Gauss reduction): `reduce_reduced`, `reduce_equiv`; its
  running time `reduce_cost_le` (at most `2A + 2` passes on numbers of `O(log N)` bits,
  `N = |A| + |B| + |C|`), with grammar-school arithmetic `O((A + 1) log² N)`
  (`reduceCost_school`).
* `sumTwoSquares_factor` — §5.6.2: two representations `n = x₁² + y₁² = x₂² + y₂²` give the
  proper factor `gcd(x₁ y₂ - y₁ x₂, n)`; `mckee_factor` — McKee's observation behind
  Algorithm 5.6.3: two square roots of `D` modulo `n` other than `±` each other split `n`.
* `eval_mul_eval` — §5.6.3: the product of numbers represented by `(a₁, b, a₂ e)` and
  `(a₂, b, a₁ e)` is represented by `(a₁ a₂, b, e)`; `disc_ambiguous` — §5.6.4: the
  ambiguous forms `(a, 0, c)`, `(a, a, c)`, `(a, b, a)` factor the discriminant.

**Not yet formalized:** Algorithm 5.6.3 (McKee's test) and its running time
`O(n^{1/3 + ε})` (Theorem 5.6.4), the class group (Lemmas 5.6.5, 5.6.6) and Algorithm 5.6.7
(composition), and the class-number estimates of §5.6.3–5.6.4.
-/

namespace PrimeNumbers.Chapter5

/-- A binary quadratic form `a x² + b x y + c y²`, as the triple `(a, b, c)`. -/
@[ext] structure QF where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

namespace QF

/-- The value `a x² + b x y + c y²`. -/
def eval (f : QF) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- The discriminant `b² - 4ac`. -/
def disc (f : QF) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- `f` represents `n`: `a x² + b x y + c y² = n` for some integers `x, y`. -/
def Represents (f : QF) (n : ℤ) : Prop := ∃ x y, f.eval x y = n

/-- The form after the change of variables `x = αX + βY, y = γX + δY` (5.1). -/
def subst (f : QF) (α β γ δ : ℤ) : QF :=
  ⟨f.eval α γ, 2 * f.a * α * β + f.b * (α * δ + β * γ) + 2 * f.c * γ * δ, f.eval β δ⟩

theorem eval_subst (f : QF) (α β γ δ X Y : ℤ) :
    (f.subst α β γ δ).eval X Y = f.eval (α * X + β * Y) (γ * X + δ * Y) := by
  simp only [subst, eval]; ring

theorem disc_subst (f : QF) (α β γ δ : ℤ) :
    (f.subst α β γ δ).disc = (α * δ - β * γ) ^ 2 * f.disc := by
  simp only [subst, disc, eval]; ring

theorem subst_subst (f : QF) (α β γ δ α' β' γ' δ' : ℤ) :
    (f.subst α β γ δ).subst α' β' γ' δ' =
      f.subst (α * α' + β * γ') (α * β' + β * δ') (γ * α' + δ * γ') (γ * β' + δ * δ') := by
  ext <;> simp only [subst, eval] <;> ring

theorem subst_one (f : QF) : f.subst 1 0 0 1 = f := by
  ext <;> simp only [subst, eval] <;> ring

/-- Equivalent forms: related by a unimodular change of variables (determinant `+1`). -/
def Equiv (f g : QF) : Prop := ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ g = f.subst α β γ δ

/-! ### Exercise 5.10: equivalence is an equivalence relation -/

theorem Equiv.refl (f : QF) : Equiv f f := ⟨1, 0, 0, 1, by ring, f.subst_one.symm⟩

theorem Equiv.symm {f g : QF} (h : Equiv f g) : Equiv g f := by
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h
  refine ⟨δ, -β, -γ, α, by linarith, ?_⟩
  rw [subst_subst]
  convert f.subst_one.symm using 2 <;>
    first | ring1 | linear_combination hdet

theorem Equiv.trans {f g h : QF} (h₁ : Equiv f g) (h₂ : Equiv g h) : Equiv f h := by
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h₁
  obtain ⟨α', β', γ', δ', hdet', rfl⟩ := h₂
  refine ⟨_, _, _, _, ?_, subst_subst ..⟩
  linear_combination (α' * δ' - β' * γ') * hdet + hdet'

/-- Exercise 5.12: equivalent forms have the same discriminant. -/
theorem Equiv.disc_eq {f g : QF} (h : Equiv f g) : g.disc = f.disc := by
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h
  rw [disc_subst, hdet, one_pow, one_mul]

/-- Equivalent forms represent the same numbers. -/
theorem Equiv.represents {f g : QF} (h : Equiv f g) {n : ℤ} (hn : g.Represents n) :
    f.Represents n := by
  obtain ⟨α, β, γ, δ, -, rfl⟩ := h
  obtain ⟨X, Y, rfl⟩ := hn
  exact ⟨_, _, (eval_subst ..).symm⟩

/-! ### Reduced forms -/

/-- A form is **reduced** (5.2) if its discriminant is negative and `-a < b ≤ a < c` or
`0 ≤ b ≤ a = c`. -/
def Reduced (f : QF) : Prop :=
  f.disc < 0 ∧ ((-f.a < f.b ∧ f.b ≤ f.a ∧ f.a < f.c) ∨ (0 ≤ f.b ∧ f.b ≤ f.a ∧ f.a = f.c))

theorem Reduced.bounds {f : QF} (h : f.Reduced) :
    0 < f.a ∧ -f.a < f.b ∧ f.b ≤ f.a ∧ f.a ≤ f.c := by
  obtain ⟨hD, ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩⟩ := h
  · omega
  · have : 0 < f.a := by
      by_contra h0
      have ha : f.a = 0 := by omega
      have hb : f.b = 0 := by omega
      simp [disc, ha, hb, ← h₃] at hD
    omega

/-- `a X² - |b| X Y + c Y² ≥ c` for `|b| ≤ a ≤ c`, `X ≥ 0`, `Y ≥ 1`. -/
private theorem c_le_of_reduced {a b c X Y : ℤ} (h0 : 0 < a) (hb : |b| ≤ a) (hac : a ≤ c)
    (hX : 0 ≤ X) (hY : 1 ≤ Y) : c ≤ a * X ^ 2 - |b| * (X * Y) + c * Y ^ 2 := by
  have hc : 0 ≤ c := by linarith
  rcases le_or_gt Y X with hl | hl
  · nlinarith [mul_le_mul_of_nonneg_right hb (mul_nonneg hX (by linarith : (0:ℤ) ≤ Y)),
      mul_nonneg h0.le (mul_nonneg hX (sub_nonneg.2 hl)),
      mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ Y ^ 2 by nlinarith) hc]
  · nlinarith [mul_le_mul_of_nonneg_right (hb.trans hac)
      (mul_nonneg hX (by linarith : (0:ℤ) ≤ Y)),
      mul_nonneg hc (mul_nonneg (by linarith : (0:ℤ) ≤ Y) (by linarith : (0:ℤ) ≤ Y - X - 1)),
      mul_le_mul_of_nonneg_left hY hc, mul_nonneg h0.le (sq_nonneg X)]

/-- A reduced form takes at least the value `c` at every `(x, y)` with `y ≠ 0`. -/
theorem Reduced.c_le_eval {f : QF} (h : f.Reduced) {x y : ℤ} (hy : y ≠ 0) :
    f.c ≤ f.eval x y := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h.bounds
  have hxy : -(|f.b| * (|x| * |y|)) ≤ f.b * x * y := by
    have := neg_abs_le (f.b * x * y)
    rw [abs_mul, abs_mul] at this; linarith [mul_assoc |f.b| |x| |y|]
  have := c_le_of_reduced h₀ (abs_le.2 ⟨by omega, h₂⟩) h₃ (abs_nonneg x) (Int.one_le_abs hy)
  simp only [eval, ← sq_abs x, ← sq_abs y] at *
  linarith

/-- A reduced form takes at least the value `a` away from `(0, 0)`. -/
theorem Reduced.a_le_eval {f : QF} (h : f.Reduced) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    f.a ≤ f.eval x y := by
  obtain ⟨h₀, -, -, h₃⟩ := h.bounds
  by_cases hy : y = 0
  · subst hy
    have : 1 ≤ x ^ 2 := by
      have := Int.one_le_abs (hxy.resolve_right (by simp)); nlinarith [sq_abs x]
    simp only [eval]; nlinarith
  · exact h₃.trans (h.c_le_eval hy)

/-- Two reduced forms related by a change `x = αX + βY, y = δY` (so `α = δ = ±1`) are
equal: `b` moves by the multiple `2aαβ` of `2a`, and stays in `(-a, a]`. -/
private theorem Reduced.eq_of_subst_lower {f : QF} (hf : f.Reduced) {α β δ : ℤ}
    (hdet : α * δ = 1) (hg : (f.subst α β 0 δ).Reduced) : f = f.subst α β 0 δ := by
  obtain ⟨f₀, f₁, f₂, -⟩ := hf.bounds
  obtain ⟨-, g₁, g₂, -⟩ := hg.bounds
  have hα : α ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;> simp [h]
  have ha : (f.subst α β 0 δ).a = f.a := by simp only [subst, eval]; rw [hα]; ring
  have hb : (f.subst α β 0 δ).b = f.b + 2 * f.a * (α * β) := by
    simp only [subst]; linear_combination f.b * hdet
  rw [ha, hb] at g₁ g₂
  have hk : α * β = 0 := by
    by_contra hk
    rcases lt_or_gt_of_ne hk with hk | hk <;> nlinarith
  have hD := disc_subst f α β 0 δ
  simp only [mul_zero, sub_zero, hdet, one_pow, one_mul] at hD
  simp only [disc, ha, hb, hk, mul_zero, add_zero] at hD
  refine QF.ext ha.symm (by rw [hb, hk]; ring) ?_
  have := f₀.ne'; apply mul_left_cancel₀ (show (4 : ℤ) * f.a ≠ 0 by positivity); linarith

/-- **Theorem 5.6.1 (Gauss), uniqueness.**  No two different reduced forms are
equivalent. -/
theorem Reduced.eq_of_equiv {f g : QF} (hf : f.Reduced) (hg : g.Reduced) (h : Equiv f g) :
    f = g := by
  obtain ⟨α', β', γ', δ', hdet', hfg⟩ := h.symm
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h
  have hne : ∀ p q r s : ℤ, p * s - q * r = 1 → p ≠ 0 ∨ r ≠ 0 := fun p q r s h ↦ by
    by_contra hc; push Not at hc; rw [hc.1, hc.2] at h; simp at h
  by_cases hγ : γ = 0
  · subst hγ; exact hf.eq_of_subst_lower (by linarith) hg
  by_cases hγ' : γ' = 0
  · subst hγ'
    exact ((hg.eq_of_subst_lower (by linarith) (hfg ▸ hf)).trans hfg.symm).symm
  -- otherwise both changes reach `y ≠ 0`: then `a = c` for both forms, and `b ≥ 0`
  set g := f.subst α β γ δ with hgdef
  obtain ⟨f₀, -, -, f₃⟩ := hf.bounds
  obtain ⟨g₀, -, -, g₃⟩ := hg.bounds
  have h₁ : f.a ≤ g.a := hf.a_le_eval (hne α β γ δ hdet)
  have h₂ : f.c ≤ g.a := hf.c_le_eval hγ
  have h₃ : g.a ≤ f.a := by rw [hfg]; exact hg.a_le_eval (hne α' β' γ' δ' hdet')
  have h₄ : g.c ≤ f.a := by rw [hfg]; exact hg.c_le_eval hγ'
  have hfb : 0 ≤ f.b := by rcases hf.2 with h | h <;> omega
  have hgb : 0 ≤ g.b := by rcases hg.2 with h | h <;> omega
  have hD : g.disc = f.disc := Equiv.disc_eq ⟨α, β, γ, δ, hdet, rfl⟩
  have hac : g.a = f.a ∧ g.c = f.c := by omega
  simp only [disc, hac.1, hac.2] at hD
  exact QF.ext hac.1.symm (by nlinarith) hac.2.symm


/-! ### Algorithm 5.6.2: reduction -/

/-- The type (1) move of Algorithm 5.6.2: `(A, B, C) ↦ (C, -B, A)` if `A > C`. -/
counted_def swapMove (A B C : ℤ) : ℤ × ℤ × ℤ :=
  if C < A then (C, -B, A) else (A, B, C)

/-- The type (2) move of Algorithm 5.6.2: if `B ∉ (-A, A]`, move to `B* = B + 2Ak ∈ (-A, A]`
(`k = ⌊(A - B)/2A⌋`, so `B* = A - ((A - B) mod 2A)`) and `C* = C + k (B + A k)`, which keeps
the discriminant. -/
counted_def shiftMove (A B C : ℤ) : ℤ × ℤ × ℤ :=
  if A < B ∨ B ≤ -A then
    let k := (A - B) / (2 * A)
    (A, B + 2 * A * k, C + k * (B + A * k))
  else (A, B, C)

/-- One pass of the replacement loop of Algorithm 5.6.2. -/
counted_def reduceStep (A B C : ℤ) : ℤ × ℤ × ℤ :=
  let (A, B, C) := swapMove A B C
  shiftMove A B C

/-- The replacement loop of Algorithm 5.6.2,
`while (A > C or B > A or B ≤ -A) { … }`, for at most `fuel` passes. -/
counted_def reduceLoop : (A B C : ℤ) → ℕ → ℤ × ℤ × ℤ
  | A, B, C, 0 => (A, B, C)
  | A, B, C, fuel + 1 =>
    if C < A ∨ A < B ∨ B ≤ -A then
      let (A, B, C) := reduceStep A B C
      reduceLoop A B C fuel
    else (A, B, C)

/-- **Algorithm 5.6.2 (Reduction for negative discriminant).**  Given `(A, B, C)` with
`B² - 4AC < 0` and `A > 0`, a reduced form equivalent to it (`reduce_reduced`,
`reduce_equiv`).
```
1. while (A > C or B > A or B ≤ -A) {
     if (A > C) (A, B, C) = (C, -B, A);                       // type (1)
     if (A ≤ C and (B > A or B ≤ -A)) (A, B, C) = (A, B*, C*);  // type (2)
   }
2. if (A == C and -A < B < 0) (A, B, C) = (A, -B, C);
   return (A, B, C);
```
(After a type (1) move `A ≤ C` holds, so the test `A ≤ C` of the type (2) move is implied.)
The loop needs at most `2A + 1` passes (`reduceLoop_final`): a type (1) move lowers `A`, and
two type (2) moves never follow each other. -/
counted_def reduce (A B C : ℤ) : ℤ × ℤ × ℤ :=
  let (A, B, C) := reduceLoop A B C (2 * A.toNat + 2)
  if A = C ∧ -A < B ∧ B < 0 then (A, -B, C) else (A, B, C)

/-- The form of a triple. -/
def ofTriple (t : ℤ × ℤ × ℤ) : QF := ⟨t.1, t.2.1, t.2.2⟩

/-- The type (1) move is the change `x = -Y, y = X`. -/
theorem equiv_swap (A B C : ℤ) : Equiv ⟨A, B, C⟩ ⟨C, -B, A⟩ :=
  ⟨0, -1, 1, 0, by ring, by ext <;> simp only [subst, eval] <;> ring⟩

/-- The type (2) move is the change `x = X + kY, y = Y`. -/
theorem equiv_shift (A B C k : ℤ) :
    Equiv ⟨A, B, C⟩ ⟨A, B + 2 * A * k, C + k * (B + A * k)⟩ :=
  ⟨1, k, 0, 1, by ring, by ext <;> simp only [subst, eval] <;> ring⟩

theorem swapMove_equiv (A B C : ℤ) : Equiv ⟨A, B, C⟩ (ofTriple (swapMove A B C)) := by
  unfold swapMove; split_ifs
  · exact equiv_swap A B C
  · exact Equiv.refl _

theorem shiftMove_equiv (A B C : ℤ) : Equiv ⟨A, B, C⟩ (ofTriple (shiftMove A B C)) := by
  unfold shiftMove; split_ifs
  · exact equiv_shift A B C _
  · exact Equiv.refl _

/-- After a type (2) move, `B ∈ (-A, A]`. -/
theorem shiftMove_spec {A B C : ℤ} (hA : 0 < A) :
    (shiftMove A B C).1 = A ∧ -A < (shiftMove A B C).2.1 ∧ (shiftMove A B C).2.1 ≤ A := by
  unfold shiftMove
  split_ifs with h
  · have h₁ := Int.emod_add_mul_ediv (A - B) (2 * A)
    have h₂ := Int.emod_nonneg (A - B) (show 2 * A ≠ 0 by omega)
    have h₃ := Int.emod_lt_of_pos (A - B) (show 0 < 2 * A by omega)
    refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> linarith
  · refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> omega

theorem reduceStep_eq (A B C : ℤ) :
    reduceStep A B C = shiftMove (swapMove A B C).1 (swapMove A B C).2.1 (swapMove A B C).2.2 :=
  rfl

theorem reduceStep_equiv (A B C : ℤ) : Equiv ⟨A, B, C⟩ (ofTriple (reduceStep A B C)) :=
  (swapMove_equiv A B C).trans (by rw [reduceStep_eq]; exact shiftMove_equiv ..)

/-- The discriminant is negative, and `A > 0`. -/
def Pos (t : ℤ × ℤ × ℤ) : Prop := (ofTriple t).disc < 0 ∧ 0 < t.1

theorem Pos.c_pos {t : ℤ × ℤ × ℤ} (h : Pos t) : 0 < t.2.2 := by
  obtain ⟨hD, hA⟩ := h
  simp only [disc, ofTriple] at hD
  nlinarith [sq_nonneg t.2.1]

/-- After a pass: still `Pos`, `B ∈ (-A, A]`, and `A` lower if there was a type (1) move,
the same otherwise. -/
theorem reduceStep_spec {A B C : ℤ} (h : Pos (A, B, C)) :
    let r := reduceStep A B C
    Pos r ∧ -r.1 < r.2.1 ∧ r.2.1 ≤ r.1 ∧ (if C < A then r.1 < A else r.1 = A) := by
  intro r
  have hC := h.c_pos
  have hD : (ofTriple r).disc = (ofTriple (A, B, C)).disc := (reduceStep_equiv A B C).disc_eq
  obtain ⟨hD₀, hA⟩ := h
  simp only at hA hC
  have hsw : 0 < (swapMove A B C).1 ∧
      (if C < A then (swapMove A B C).1 < A else (swapMove A B C).1 = A) := by
    by_cases h : C < A
    · simp [swapMove, h, hC]
    · simp [swapMove, h, hA]
  obtain ⟨e₁, e₂, e₃⟩ := shiftMove_spec (B := (swapMove A B C).2.1) (C := (swapMove A B C).2.2)
    hsw.1
  rw [← reduceStep_eq] at e₁ e₂ e₃
  refine ⟨⟨hD ▸ hD₀, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [r, e₁]
  · exact hsw.1
  · exact e₂
  · exact e₃
  · exact hsw.2


theorem reduceLoop_succ (A B C : ℤ) (fuel : ℕ) :
    reduceLoop A B C (fuel + 1) = if C < A ∨ A < B ∨ B ≤ -A then
      reduceLoop (reduceStep A B C).1 (reduceStep A B C).2.1 (reduceStep A B C).2.2 fuel
    else (A, B, C) := by
  rw [reduceLoop]

theorem reduceLoop_equiv (A B C : ℤ) (fuel : ℕ) :
    Equiv ⟨A, B, C⟩ (ofTriple (reduceLoop A B C fuel)) := by
  induction fuel generalizing A B C with
  | zero => exact Equiv.refl _
  | succ fuel ih =>
    rw [reduceLoop_succ]; split_ifs
    · exact (reduceStep_equiv A B C).trans (ih ..)
    · exact Equiv.refl _

/-- The loop ends with `-A < B ≤ A ≤ C`, still `Pos`, after at most `2A + 2` passes (with the
potential `2A + [B ∉ (-A, A]]`, which every pass lowers). -/
theorem reduceLoop_final {A B C : ℤ} (h : Pos (A, B, C)) {fuel : ℕ}
    (hf : 2 * A + (if -A < B ∧ B ≤ A then 1 else 2) ≤ fuel) :
    let r := reduceLoop A B C fuel
    Pos r ∧ -r.1 < r.2.1 ∧ r.2.1 ≤ r.1 ∧ r.1 ≤ r.2.2 := by
  induction fuel generalizing A B C with
  | zero => have := h.2; split_ifs at hf <;> simp only at this <;> omega
  | succ fuel ih =>
    intro r
    simp only [r, reduceLoop_succ]
    split_ifs with hc
    · obtain ⟨hP, h₁, h₂, h₃⟩ := reduceStep_spec h
      refine ih hP ?_
      have hA := h.2; simp only at hA
      simp only [h₁, h₂, and_self, ↓reduceIte]
      split_ifs at h₃ hf <;> omega
    · refine ⟨h, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

theorem reduce_eq (A B C : ℤ) :
    reduce A B C = let r := reduceLoop A B C (2 * A.toNat + 2)
      if r.1 = r.2.2 ∧ -r.1 < r.2.1 ∧ r.2.1 < 0 then (r.1, -r.2.1, r.2.2) else r := by
  rw [reduce]

theorem reduce_equiv (A B C : ℤ) : Equiv ⟨A, B, C⟩ (ofTriple (reduce A B C)) := by
  rw [reduce_eq]; dsimp only
  have h := reduceLoop_equiv A B C (2 * A.toNat + 2)
  generalize reduceLoop A B C (2 * A.toNat + 2) = r at h ⊢
  obtain ⟨a, b, c⟩ := r
  dsimp only
  split_ifs with hc
  · refine h.trans ?_
    simp only [ofTriple]; rw [hc.1]
    exact equiv_swap c b c
  · exact h

theorem reduce_reduced {A B C : ℤ} (h : Pos (A, B, C)) : (ofTriple (reduce A B C)).Reduced := by
  have hA := h.2; simp only at hA
  obtain ⟨⟨hD, -⟩, h₁, h₂, h₃⟩ := reduceLoop_final h (fuel := 2 * A.toNat + 2) (by
    split_ifs <;> omega)
  rw [reduce_eq]; dsimp only
  have hD' := (reduce_equiv A B C).disc_eq
  generalize reduceLoop A B C (2 * A.toNat + 2) = r at *
  obtain ⟨a, b, c⟩ := r
  simp only [ofTriple, disc] at hD h₁ h₂ h₃
  split_ifs with hc <;> dsimp only at hc <;> simp only [Reduced, ofTriple, disc]
  · exact ⟨by nlinarith, Or.inr ⟨by omega, by omega, hc.1⟩⟩
  · refine ⟨hD, ?_⟩
    rcases lt_or_eq_of_le h₃ with h₃ | h₃
    · exact Or.inl ⟨h₁, h₂, h₃⟩
    · exact Or.inr ⟨by omega, h₂, h₃⟩

/-- **Theorem 5.6.1 (Gauss).**  Every form of negative discriminant with `a > 0` is
equivalent to exactly one reduced form — computed by Algorithm 5.6.2. -/
theorem existsUnique_reduced_equiv {f : QF} (hD : f.disc < 0) (ha : 0 < f.a) :
    ∃! g : QF, g.Reduced ∧ Equiv f g :=
  ⟨ofTriple (reduce f.a f.b f.c), ⟨reduce_reduced ⟨hD, ha⟩, reduce_equiv ..⟩,
    fun _ ⟨hg, hfg⟩ ↦ (Reduced.eq_of_equiv (reduce_reduced ⟨hD, ha⟩) hg
      ((reduce_equiv ..).symm.trans hfg)).symm⟩


/-! ### §5.6.2–5.6.4: factoring with forms -/

/-- A nontrivial factor from a zero product: if `n ∣ A B` but `n ∤ A` and `n ∤ B`, then
`gcd(A, n)` is a proper factor of `n`. -/
theorem one_lt_gcd_lt_of_dvd_mul {n : ℕ} {A B : ℤ} (h : (n : ℤ) ∣ A * B)
    (hA : ¬ (n : ℤ) ∣ A) (hB : ¬ (n : ℤ) ∣ B) : 1 < Int.gcd A n ∧ Int.gcd A n < n := by
  have hn : n ≠ 0 := by
    rintro rfl; simp only [Nat.cast_zero, zero_dvd_iff, mul_eq_zero] at h hA hB; tauto
  refine ⟨?_, ?_⟩
  · by_contra h1
    have hg : Int.gcd A n = 1 := by
      have : Int.gcd A n ≠ 0 := by rw [Ne, Int.gcd_eq_zero_iff]; omega
      omega
    exact hB (Int.dvd_of_dvd_mul_right_of_gcd_one h (by rwa [Int.gcd_comm]))
  · have hle : Int.gcd A n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (by have := Int.gcd_dvd_right (a := A) (b := n); exact_mod_cast this)
    rcases lt_or_eq_of_le hle with h' | h'
    · exact h'
    · exact absurd (h' ▸ Int.gcd_dvd_left (a := A) (b := n)) hA

/-- **§5.6.2: two representations as a sum of two squares factor `n`.**  If
`n = x₁² + y₁² = x₂² + y₂²` with `x₂ ≥ y₂ ≥ 0` and `x₁ > x₂`, then `gcd(x₁ y₂ - y₁ x₂, n)` is
a proper factor of `n`: with `A = x₁ y₂ - y₁ x₂` and `B = x₁ y₂ + y₁ x₂`, `n ∣ A B` and
`0 < A ≤ B < n`.  (The book's `x₁ ≥ y₁` is not needed.) -/
theorem sumTwoSquares_factor {n x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ ^ 2 + y₁ ^ 2 = n)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = n) (hy₂ : y₂ ≤ x₂) (hx : x₂ < x₁) :
    1 < Int.gcd (x₁ * y₂ - y₁ * x₂ : ℤ) n ∧ Int.gcd (x₁ * y₂ - y₁ * x₂ : ℤ) n < n := by
  have hy : y₁ < y₂ := by nlinarith
  have hn : (n : ℤ) = x₁ ^ 2 + y₁ ^ 2 := by exact_mod_cast h₁.symm
  have hn' : (n : ℤ) = x₂ ^ 2 + y₂ ^ 2 := by exact_mod_cast h₂.symm
  have hA : (0 : ℤ) < x₁ * y₂ - y₁ * x₂ := by
    have : (x₂ : ℤ) * y₁ ≤ x₂ * y₂ := by exact_mod_cast Nat.mul_le_mul_left _ hy.le
    have : (x₂ : ℤ) * y₂ < x₁ * y₂ := by
      have : 0 < y₂ := by omega
      exact_mod_cast Nat.mul_lt_mul_of_pos_right hx this
    linarith
  have hB : (x₁ * y₂ + y₁ * x₂ : ℤ) < n := by
    have : (0 : ℤ) < (x₁ - y₂) ^ 2 := by
      have : (y₂ : ℤ) < x₁ := by exact_mod_cast (show y₂ < x₁ by omega)
      positivity
    nlinarith [sq_nonneg ((y₁ : ℤ) - x₂)]
  refine one_lt_gcd_lt_of_dvd_mul (B := x₁ * y₂ + y₁ * x₂) ⟨x₁ ^ 2 - x₂ ^ 2, ?_⟩ ?_ ?_
  · rw [hn] at hn' ⊢; linear_combination (-(x₁ : ℤ) ^ 2) * hn'
  · intro ⟨k, hk⟩
    have : 0 < k := by nlinarith
    nlinarith
  · intro ⟨k, hk⟩
    have : 0 < k := by nlinarith
    nlinarith

/-- **§5.6.2 (McKee): two square roots of `D` modulo `n` not `±` each other factor `n`.**
If `(u₁, v₁), (u₂, v₂)` satisfy `uᵢ² ≡ D vᵢ² (mod n)` and `uᵢ ≡ vᵢ hᵢ (mod n)`, with
`v₁ v₂` coprime to `n` and `h₁ ≢ ±h₂ (mod n)`, then `gcd(u₁ v₂ - u₂ v₁, n)` is a proper
factor of `n`. -/
theorem mckee_factor {n : ℕ} {D u₁ v₁ u₂ v₂ h₁ h₂ : ℤ}
    (hu₁ : (n : ℤ) ∣ u₁ ^ 2 - D * v₁ ^ 2) (hu₂ : (n : ℤ) ∣ u₂ ^ 2 - D * v₂ ^ 2)
    (hh₁ : (n : ℤ) ∣ u₁ - v₁ * h₁) (hh₂ : (n : ℤ) ∣ u₂ - v₂ * h₂)
    (hv : IsCoprime (v₁ * v₂) n) (hne : ¬ (n : ℤ) ∣ h₁ - h₂) (hne' : ¬ (n : ℤ) ∣ h₁ + h₂) :
    1 < Int.gcd (u₁ * v₂ - u₂ * v₁) n ∧ Int.gcd (u₁ * v₂ - u₂ * v₁) n < n := by
  refine one_lt_gcd_lt_of_dvd_mul (B := u₁ * v₂ + u₂ * v₁) ?_ ?_ ?_
  · have : u₁ * v₂ * (u₁ * v₂) - u₂ * v₁ * (u₂ * v₁) =
        v₂ ^ 2 * (u₁ ^ 2 - D * v₁ ^ 2) - v₁ ^ 2 * (u₂ ^ 2 - D * v₂ ^ 2) := by ring
    have h := dvd_sub (dvd_mul_of_dvd_right hu₁ (v₂ ^ 2)) (dvd_mul_of_dvd_right hu₂ (v₁ ^ 2))
    rw [← this] at h
    convert h using 1; ring
  · intro h
    -- `u₁ v₂ - u₂ v₁ ≡ v₁ v₂ (h₁ - h₂)`
    have e : (n : ℤ) ∣ v₁ * v₂ * (h₁ - h₂) := by
      have := dvd_add (dvd_sub h (dvd_mul_of_dvd_left hh₁ v₂)) (dvd_mul_of_dvd_left hh₂ v₁)
      convert this using 1; ring
    exact hne (hv.symm.dvd_of_dvd_mul_left e)
  · intro h
    have e : (n : ℤ) ∣ v₁ * v₂ * (h₁ + h₂) := by
      have := dvd_sub (dvd_sub h (dvd_mul_of_dvd_left hh₁ v₂)) (dvd_mul_of_dvd_left hh₂ v₁)
      convert this using 1; ring
    exact hne' (hv.symm.dvd_of_dvd_mul_left e)

/-- **§5.6.3: composition of forms with the same middle coefficient.**  A number represented
by `(a₁, b, a₂ e)` times one represented by `(a₂, b, a₁ e)` is represented by
`(a₁ a₂, b, e)`, at `x₃ = x₁ x₂ - e y₁ y₂`, `y₃ = a₁ x₁ y₂ + a₂ x₂ y₁ + b y₁ y₂`. -/
theorem eval_mul_eval (a₁ a₂ b e x₁ y₁ x₂ y₂ : ℤ) :
    (⟨a₁, b, a₂ * e⟩ : QF).eval x₁ y₁ * (⟨a₂, b, a₁ * e⟩ : QF).eval x₂ y₂ =
      (⟨a₁ * a₂, b, e⟩ : QF).eval (x₁ * x₂ - e * y₁ * y₂)
        (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + b * y₁ * y₂) := by
  simp only [eval]; ring

/-- **§5.6.4: ambiguous forms factor the discriminant.**  `(a, 0, c)` has `-D = 4ac`,
`(a, a, c)` has `-D = a (4c - a)`, and `(a, b, a)` has `-D = (2a - b)(2a + b)`. -/
theorem disc_ambiguous (a b c : ℤ) :
    -(⟨a, 0, c⟩ : QF).disc = 4 * a * c ∧ -(⟨a, a, c⟩ : QF).disc = a * (4 * c - a) ∧
      -(⟨a, b, a⟩ : QF).disc = (2 * a - b) * (2 * a + b) := by
  simp only [disc]; refine ⟨by ring, by ring, by ring⟩

section RunningTime

open Chapter9

theorem natAbs_le_of_abs_le {e : ℤ} {M : ℕ} (h : |e| ≤ M) : e.natAbs ≤ M := by
  rw [← Int.ofNat_le, Int.natCast_natAbs]; exact h

/-- The bit operations of a type (2) move on numbers of at most `K` bits. -/
def moveBound (C : CostModel) (K : ℕ) : ℕ := 3 * C.mul K K + C.divBound K + 12 * C.lin K

@[cost_le] theorem swapMove_cost_le (C : CostModel) {K : ℕ} {A B D : ℤ}
    (hA : A.natAbs.size ≤ K) (hB : B.natAbs.size ≤ K) (hD : D.natAbs.size ≤ K) :
    costOf C (swapMove A B D) ≤ 3 * C.lin K := by
  cost_unfold swapMove.counted
  split_ifs <;> cost_bound

@[cost_le] theorem shiftMove_cost_le (C : CostModel) {N : ℕ} {A B D : ℤ} (hN : 1 ≤ N)
    (hA : 0 < A) (hAN : A ≤ N) (hB : |B| ≤ N) (hD : |D| ≤ N ^ 2) :
    costOf C (shiftMove A B D) ≤ moveBound C (8 * N ^ 3).size := by
  set k := (A - B) / (2 * A)
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hN2 : (N : ℤ) ≤ N ^ 2 := by nlinarith
  have hN23 : (N : ℤ) ^ 2 ≤ N ^ 3 := by nlinarith
  have hN3 : (N : ℤ) ≤ N ^ 3 := hN2.trans hN23
  have hA' : |A| ≤ N := by rw [abs_of_pos hA]; exact hAN
  have hk : |k| ≤ 2 * N := by
    have := Int.natAbs_ediv_le_natAbs (A - B) (2 * A)
    have h' : |A - B| ≤ 2 * N := (abs_sub _ _).trans (by linarith)
    rw [← Int.natCast_natAbs] at h' ⊢; exact_mod_cast this.trans (by exact_mod_cast h')
  have hAk : |A * k| ≤ 2 * N ^ 2 := by
    rw [abs_mul]; nlinarith [mul_le_mul hA' hk (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)]
  have hBAk : |B + A * k| ≤ 3 * N ^ 2 := (abs_add_le _ _).trans (by nlinarith)
  have h₁ : (A).natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by push_cast; linarith)
  have h₂ : (B).natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by push_cast; linarith)
  have h₃ : (-A).natAbs ≤ 8 * N ^ 3 := by rw [Int.natAbs_neg]; exact h₁
  have h₄ : (A - B).natAbs ≤ 8 * N ^ 3 :=
    natAbs_le_of_abs_le (by push_cast; linarith [abs_sub A B])
  have h₅ : (2 * A).natAbs ≤ 8 * N ^ 3 :=
    natAbs_le_of_abs_le (by push_cast; rw [abs_mul]; norm_num; linarith)
  have h₆ : k.natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by push_cast; linarith)
  have h₇ : (2 * A * k).natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by
    push_cast; rw [mul_assoc, abs_mul]; norm_num; linarith [abs_mul A k])
  have h₈ : (A * k).natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by push_cast; linarith)
  have h₉ : (B + A * k).natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by push_cast; linarith)
  have h₁₀ : (k * (B + A * k)).natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by
    push_cast; rw [abs_mul]
    nlinarith [mul_le_mul hk hBAk (abs_nonneg _) (by positivity : (0:ℤ) ≤ 2 * N)])
  have h₁₁ : D.natAbs ≤ 8 * N ^ 3 := natAbs_le_of_abs_le (by push_cast; linarith)
  have hK : 4 ≤ (8 * N ^ 3).size := by
    have := Nat.size_le_size (show 8 ≤ 8 * N ^ 3 by nlinarith [Nat.one_le_pow 3 N hN])
    rwa [show Nat.size 8 = 4 by decide] at this
  have h2 : (Int.natAbs 2).size = 2 := by decide
  unfold moveBound
  cost_unfold shiftMove.counted
  split_ifs <;> cost_bound

/-- The size of the numbers during the reduction of a form with `|A| + |B| + |C| ≤ N`:
`0 < A ≤ N`, `|B| ≤ N`, `C ≤ N²`, and the discriminant `D` with `-D ≤ N²`. -/
def Small (N : ℕ) (D : ℤ) (t : ℤ × ℤ × ℤ) : Prop :=
  (ofTriple t).disc = D ∧ D < 0 ∧ -D ≤ N ^ 2 ∧ 0 < t.1 ∧ t.1 ≤ N ∧ |t.2.1| ≤ N ∧ t.2.2 ≤ N ^ 2

theorem Small.pos {N : ℕ} {D : ℤ} {t : ℤ × ℤ × ℤ} (h : Small N D t) : Pos t :=
  ⟨h.1 ▸ h.2.1, h.2.2.2.1⟩

theorem Small.one_le {N : ℕ} {D : ℤ} {t : ℤ × ℤ × ℤ} (h : Small N D t) : 1 ≤ N := by
  have := h.2.2.2.1; have := h.2.2.2.2.1; omega

theorem swapMove_small {N : ℕ} {D A B C : ℤ} (h : Small N D (A, B, C)) :
    let s := swapMove A B C
    0 < s.1 ∧ s.1 ≤ N ∧ |s.2.1| ≤ N ∧ |s.2.2| ≤ N ^ 2 := by
  have hC := h.pos.c_pos
  obtain ⟨-, -, -, hA, hAN, hB, hCN⟩ := h
  have hN : (N : ℤ) ≤ N ^ 2 := by nlinarith
  simp only at hA hAN hB hCN hC ⊢
  unfold swapMove; split_ifs with hs
  · exact ⟨hC, by omega, by rw [abs_neg]; exact hB, by rw [abs_of_pos hA]; linarith⟩
  · exact ⟨hA, hAN, hB, by rw [abs_of_pos hC]; exact hCN⟩

theorem reduceStep_small {N : ℕ} {D A B C : ℤ} (h : Small N D (A, B, C)) :
    Small N D (reduceStep A B C) := by
  obtain ⟨hP, h₁, h₂, h₃⟩ := reduceStep_spec h.pos
  have hD : (ofTriple (reduceStep A B C)).disc = D :=
    ((reduceStep_equiv A B C).disc_eq).trans h.1
  obtain ⟨-, hD0, hDN, hA, hAN, -, -⟩ := h
  simp only at hA hAN
  have hA' : (reduceStep A B C).1 ≤ A := by split_ifs at h₃ <;> omega
  have hB2 : (reduceStep A B C).2.1 ^ 2 ≤ (reduceStep A B C).1 ^ 2 :=
    sq_le_sq' (by omega) h₂
  refine ⟨hD, hD0, hDN, hP.2, by omega, abs_le.2 ⟨by omega, by omega⟩, ?_⟩
  simp only [ofTriple, disc] at hD
  have : (reduceStep A B C).1 ^ 2 ≤ (N : ℤ) ^ 2 := by
    have := hP.2; nlinarith
  nlinarith [hP.2]

/-- The bit operations of a pass of the loop, on numbers of at most `K` bits. -/
def passBound (C : CostModel) (K : ℕ) : ℕ := moveBound C K + 10 * C.lin K

@[cost_le] theorem reduceStep_cost_le (C : CostModel) {N : ℕ} {D A B C₀ : ℤ}
    (h : Small N D (A, B, C₀)) :
    costOf C (reduceStep A B C₀) ≤ passBound C (8 * N ^ 3).size := by
  have hN := h.one_le
  have hC := h.pos.c_pos
  obtain ⟨s₁, s₂, s₃, s₄⟩ := swapMove_small h
  obtain ⟨-, -, -, hA, hAN, hB, hCN⟩ := h
  simp only at hA hAN hB hCN
  have hN3 : N ^ 2 ≤ 8 * N ^ 3 := by nlinarith [Nat.one_le_pow 2 N hN]
  have hs : ∀ x : ℤ, |x| ≤ N ^ 2 → x.natAbs.size ≤ (8 * N ^ 3).size := fun x hx ↦
    Nat.size_le_size ((natAbs_le_of_abs_le (by push_cast; exact hx)).trans hN3)
  have hN2 : (N : ℤ) ≤ N ^ 2 := by have : (1 : ℤ) ≤ N := by exact_mod_cast hN
                                   nlinarith
  have h₁ := swapMove_cost_le C (K := (8 * N ^ 3).size) (A := A) (B := B) (D := C₀)
    (hs A (by rw [abs_of_pos hA]; linarith)) (hs B (by linarith))
    (hs C₀ (by rw [abs_of_pos hC]; exact hCN))
  have h₂ := shiftMove_cost_le C hN s₁ s₂ s₃ s₄
  unfold passBound
  cost_unfold reduceStep.counted
  cost_bound

/-- A form of negative discriminant with `A > 0`, with `N = |A| + |B| + |C|`. -/
theorem small_init {A B C : ℤ} (h : Pos (A, B, C)) :
    Small (A.natAbs + B.natAbs + C.natAbs) (ofTriple (A, B, C)).disc (A, B, C) := by
  have hC := h.c_pos
  obtain ⟨hD, hA⟩ := h
  simp only [ofTriple, disc] at hD hA hC ⊢
  have e₁ : ((A.natAbs + B.natAbs + C.natAbs : ℕ) : ℤ) = A + |B| + C := by
    push_cast; rw [abs_of_pos hA, abs_of_pos hC]
  have hB := abs_nonneg B
  refine ⟨rfl, hD, ?_, hA, ?_, ?_, ?_⟩ <;> rw [e₁]
  · nlinarith [sq_nonneg (A - C), sq_abs B]
  · linarith
  · linarith
  · nlinarith

theorem Small.sizes {N : ℕ} {D : ℤ} {t : ℤ × ℤ × ℤ} (h : Small N D t) :
    t.1.natAbs.size ≤ (8 * N ^ 3).size ∧ t.2.1.natAbs.size ≤ (8 * N ^ 3).size ∧
      t.2.2.natAbs.size ≤ (8 * N ^ 3).size ∧ (-t.1).natAbs.size ≤ (8 * N ^ 3).size := by
  have hN := h.one_le
  have hC := h.pos.c_pos
  obtain ⟨-, -, -, hA, hAN, hB, hCN⟩ := h
  have hN3 : N ^ 2 ≤ 8 * N ^ 3 := by nlinarith [Nat.one_le_pow 2 N hN]
  have hN2 : (N : ℤ) ≤ N ^ 2 := by
    have : (1 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hs : ∀ x : ℤ, |x| ≤ N ^ 2 → x.natAbs.size ≤ (8 * N ^ 3).size := fun x hx ↦
    Nat.size_le_size ((natAbs_le_of_abs_le (by push_cast; exact hx)).trans hN3)
  refine ⟨hs _ (by rw [abs_of_pos hA]; linarith), hs _ (by linarith),
    hs _ (by rw [abs_of_pos hC]; exact hCN), hs _ (by rw [abs_neg, abs_of_pos hA]; linarith)⟩

theorem reduceLoop_small {N : ℕ} {D : ℤ} (fuel : ℕ) :
    ∀ {A B C : ℤ}, Small N D (A, B, C) → Small N D (reduceLoop A B C fuel) := by
  induction fuel with
  | zero => intro A B C h; exact h
  | succ fuel ih =>
    intro A B C h
    rw [reduceLoop_succ]; split_ifs
    · exact ih (A := (reduceStep A B C).1) (B := (reduceStep A B C).2.1)
        (C := (reduceStep A B C).2.2) (reduceStep_small h)
    · exact h

/-- The bit operations of a pass with its test, on numbers of at most `K` bits. -/
def loopBound (C : CostModel) (K : ℕ) : ℕ := passBound C K + 4 * C.lin K

@[cost_le] theorem reduceLoop_cost_le (C : CostModel) {N : ℕ} {D : ℤ} (fuel : ℕ) :
    ∀ {A B C₀ : ℤ}, Small N D (A, B, C₀) →
      costOf C (reduceLoop A B C₀ fuel) ≤ fuel * loopBound C (8 * N ^ 3).size + C.unit := by
  induction fuel with
  | zero => intro A B C₀ _; cost_unfold reduceLoop.counted
  | succ fuel ih =>
    intro A B C₀ h
    obtain ⟨s₁, s₂, s₃, s₄⟩ := h.sizes
    simp only at s₁ s₂ s₃ s₄
    cost_unfold reduceLoop.counted
    have h₁ := reduceStep_cost_le C h
    have h₂ := ih (A := (reduceStep A B C₀).1) (B := (reduceStep A B C₀).2.1)
      (C₀ := (reduceStep A B C₀).2.2) (reduceStep_small h)
    unfold loopBound at h₂ ⊢
    split_ifs <;> cost_bound

/-- **Running time of Algorithm 5.6.2**: for a form of negative discriminant with `A > 0`
and `N = |A| + |B| + |C|`, at most `2A + 2` passes, each a few operations on numbers of
`O(log N)` bits.  (The count of passes is crude: a type (1) move lowers `A` by at least
one.) -/
@[cost_le] theorem reduce_cost_le (C : CostModel) {A B C₀ : ℤ} (h : Pos (A, B, C₀)) :
    costOf C (reduce A B C₀) ≤ (2 * A.toNat + 2) *
      loopBound C (8 * (A.natAbs + B.natAbs + C₀.natAbs) ^ 3).size +
        10 * C.lin (8 * (A.natAbs + B.natAbs + C₀.natAbs) ^ 3).size := by
  have h₀ := small_init h
  have hA := h.2; simp only at hA
  obtain ⟨s₁, -, -, -⟩ := h₀.sizes
  obtain ⟨r₁, r₂, r₃, r₄⟩ := (reduceLoop_small (2 * A.toNat + 2) h₀).sizes
  set N := A.natAbs + B.natAbs + C₀.natAbs
  have hT : A.toNat = A.natAbs := by omega
  have hN : 1 ≤ N := by omega
  have h2A : 2 * A.toNat + 2 ≤ 8 * N ^ 3 := by
    have := Nat.le_self_pow (show 3 ≠ 0 by norm_num) N; omega
  have t₁ : A.toNat.size ≤ (8 * N ^ 3).size := Nat.size_le_size (by omega)
  have t₂ : (2 * A.toNat).size ≤ (8 * N ^ 3).size := Nat.size_le_size (by omega)
  have t₃ : (2 : ℕ).size ≤ (8 * N ^ 3).size := Nat.size_le_size (by omega)
  cost_unfold reduce.counted
  have h₁ := reduceLoop_cost_le C (2 * A.toNat + 2) h₀
  split_ifs <;> cost_bound

theorem size_eight_cube_le (N : ℕ) : (8 * N ^ 3).size ≤ 3 * N.size + 4 := by
  rw [Nat.size_le]
  have := Nat.lt_size_self N
  calc 8 * N ^ 3 < 8 * (2 ^ N.size) ^ 3 := by gcongr
    _ ≤ 2 ^ (3 * N.size + 4) := by rw [← pow_mul, pow_add]; ring_nf; omega

theorem loopBound_school_le (K : ℕ) : loopBound school K ≤ 60 * (K + 1) ^ 2 := by
  have := school_divBound_le K
  simp only [loopBound, passBound, moveBound, CostModel.lin, CostModel.add, school_mul,
    school_unit, school_addRate, max_self] at *
  nlinarith

/-- **Algorithm 5.6.2 with grammar-school arithmetic**: `O((A + 1) log² N)` bit operations,
`N = |A| + |B| + |C|`. -/
theorem reduceCost_school : ∀ᴼ (A B C : ℤ), Pos (A, B, C) →
    costOf school (reduce A B C) ≤
      O((A.toNat + 1) * ((A.natAbs + B.natAbs + C.natAbs).size + 1) ^ 2) := by
  cost_O [size_eight_cube_le (A.natAbs + B.natAbs + C.natAbs),
    loopBound_school_le (8 * (A.natAbs + B.natAbs + C.natAbs) ^ 3).size]

end RunningTime

end QF

end PrimeNumbers.Chapter5
