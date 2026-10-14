import PrimeNumbers.Chapter9.CountedLib
import Mathlib

/-!
# §2.2.1 Computable polynomial arithmetic

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.2.1.

Mathlib's `Polynomial` is designed for proofs and cannot be executed.  This file provides
the executable counterpart used by the algorithms of §2.2 and §2.3.3:

* `Poly F` — a polynomial `c₀ + c₁ x + ⋯` as its coefficient list `[c₀, c₁, …]`, with
  `Poly.toPolynomial` giving its meaning as a Mathlib polynomial;
* `Poly.add`, `Poly.smul`, `Poly.sub`, `Poly.mul`, `Poly.trim` and, over a field,
  `Poly.divMod` ("divide with remainder", relation (2.4));
* for each operation a theorem that it computes the corresponding Mathlib operation, e.g.
  `toPolynomial_mul`, and `toPolynomial_mod` for the remainder `%`.
-/

namespace PrimeNumbers.Chapter2

open Polynomial

/-- A polynomial `c₀ + c₁ x + c₂ x² + ⋯`, as its list of coefficients `[c₀, c₁, c₂, …]`.
Trailing zeros are allowed; `Poly.trim` removes them. -/
abbrev Poly (F : Type*) := List F

namespace Poly

section Semiring

variable {F : Type} [CommSemiring F]

/-- The Mathlib polynomial denoted by a coefficient list. -/
noncomputable def toPolynomial : Poly F → F[X]
  | [] => 0
  | c :: f => C c + X * toPolynomial f

@[simp] theorem toPolynomial_nil : toPolynomial ([] : Poly F) = 0 := rfl

@[simp] theorem toPolynomial_cons (c : F) (f : Poly F) :
    toPolynomial (c :: f) = C c + X * toPolynomial f := rfl

/-- The coefficient of `xⁱ` is the `i`-th list entry. -/
theorem coeff_toPolynomial (f : Poly F) (i : ℕ) : (toPolynomial f).coeff i = f.getD i 0 := by
  induction f generalizing i with
  | nil => simp
  | cons c f ih => cases i <;> simp [ih, coeff_C]

/-- A list of length `n` denotes a polynomial of degree `< n`. -/
theorem degree_toPolynomial_lt (f : Poly F) : (toPolynomial f).degree < f.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPolynomial, List.getD_eq_default _ _ hm]

/-- The top coefficient of the list (which is the leading coefficient once trimmed). -/
@[cost_free] def lead (f : Poly F) : F := f.getD (f.length - 1) 0

/-- Addition, coefficientwise. -/
@[cost_free] def add : Poly F → Poly F → Poly F
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => (a + b) :: add f g

/-- Multiplication by a scalar. -/
counted_def smul [Chapter9.MulCost F] (c : F) (f : Poly F) : Poly F := f.map (c * ·)

/-- Multiplication (schoolbook): `(a + x f) g = a g + x (f g)`. -/
counted_def mul [Chapter9.MulCost F] : Poly F → Poly F → Poly F
  | [], _ => []
  | a :: f, g => add (smul a g) (0 :: mul f g)

@[simp] theorem toPolynomial_add (f g : Poly F) :
    toPolynomial (add f g) = toPolynomial f + toPolynomial g := by
  induction f generalizing g with
  | nil => simp [add]
  | cons a f ih =>
    cases g with
    | nil => simp [add]
    | cons b g => simp [add, ih]; ring

@[simp] theorem toPolynomial_smul (c : F) (f : Poly F) :
    toPolynomial (smul c f) = C c * toPolynomial f := by
  induction f with
  | nil => simp [smul]
  | cons a f ih =>
    rw [smul] at ih ⊢
    simp only [List.map_cons, toPolynomial_cons, ih, C_mul]
    ring

@[simp] theorem toPolynomial_mul (f g : Poly F) :
    toPolynomial (mul f g) = toPolynomial f * toPolynomial g := by
  induction f with
  | nil => simp [mul]
  | cons a f ih => simp [mul, ih, add_mul, mul_assoc]

theorem length_add (f g : Poly F) : (add f g).length = max f.length g.length := by
  induction f generalizing g with
  | nil => simp [add]
  | cons a f ih =>
    cases g with
    | nil => simp [add]
    | cons b g => simp [add, ih]

@[simp] theorem length_smul (c : F) (f : Poly F) : (smul c f).length = f.length := by
  simp [smul]

/-- Dropping the top coefficient subtracts the top term. -/
theorem toPolynomial_dropLast_add (f : Poly F) :
    toPolynomial f.dropLast + C (lead f) * X ^ (f.length - 1) = toPolynomial f := by
  induction f with
  | nil => simp [lead]
  | cons a f ih =>
    cases f with
    | nil => simp [lead]
    | cons b f =>
      have hl : lead (a :: b :: f) = lead (b :: f) := by simp [lead]
      rw [List.dropLast_cons_cons, toPolynomial_cons, hl, toPolynomial_cons a, ← ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [pow_succ]
      ring

variable [DecidableEq F]

/-- Remove trailing zero coefficients. -/
@[cost_free] def trim : Poly F → Poly F
  | [] => []
  | a :: f =>
    let t := trim f
    if t = [] ∧ a = 0 then [] else a :: t

@[simp] theorem toPolynomial_trim (f : Poly F) : toPolynomial (trim f) = toPolynomial f := by
  induction f with
  | nil => rfl
  | cons a f ih =>
    rw [trim]
    split_ifs with h
    · rw [toPolynomial_cons, ← ih, h.1, h.2]; simp
    · rw [toPolynomial_cons, toPolynomial_cons, ih]

theorem length_trim_le (f : Poly F) : (trim f).length ≤ f.length := by
  induction f with
  | nil => simp [trim]
  | cons a f ih =>
    rw [trim]
    split_ifs <;> simp; omega

/-- A trimmed list is empty or has nonzero top coefficient. -/
theorem lead_trim_ne_zero (f : Poly F) (h : trim f ≠ []) : lead (trim f) ≠ 0 := by
  induction f with
  | nil => simp [trim] at h
  | cons a f ih =>
    rw [trim] at h ⊢
    split_ifs at h ⊢ with hc
    · exact absurd rfl h
    · by_cases ht : trim f = []
      · have ha : a ≠ 0 := fun ha ↦ hc ⟨ht, ha⟩
        simpa [ht, lead] using ha
      · obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil ht
        have := ih ht
        rw [hbt] at this ⊢
        simpa [lead] using this

/-- A trimmed list denotes `0` only if it is empty. -/
theorem trim_eq_nil_iff (f : Poly F) : trim f = [] ↔ toPolynomial f = 0 := by
  constructor
  · intro h; rw [← toPolynomial_trim, h]; rfl
  · intro h
    by_contra hne
    apply lead_trim_ne_zero f hne
    rw [lead, ← coeff_toPolynomial, toPolynomial_trim, h, coeff_zero]

end Semiring

section Ring

variable {F : Type} [CommRing F]

/-- Subtraction. -/
counted_def sub [Chapter9.MulCost F] (f g : Poly F) : Poly F := add f (smul (-1) g)

@[simp] theorem toPolynomial_sub (f g : Poly F) :
    toPolynomial (sub f g) = toPolynomial f - toPolynomial g := by
  simp [sub, sub_eq_add_neg]

theorem length_sub (f g : Poly F) : (sub f g).length = max f.length g.length := by
  simp [sub, length_add]

end Ring

section Field

variable {F : Type} [Field F]

/-- **Divide with remainder, relation (2.4).**  For `g` with nonzero top coefficient,
returns `(q, r)` with `f = q g + r` and `r` shorter than `g`.

The recursion is Horner's rule read as a division: if `f = q' g + r'` then
`a + x f = (x q') g + (a + x r')`, and `a + x r'` needs at most one reduction by `g`.
This is the "grammar-school" method: `O(deg f · deg g)` field operations. -/
def divMod : Poly F → Poly F → Poly F × Poly F
  | [], _ => ([], [])
  | a :: f, g =>
    let qr := divMod f g
    let s := a :: qr.2
    if s.length < g.length then (0 :: qr.1, s)
    else
      let c := lead s * (lead g)⁻¹
      (c :: qr.1, (sub s (smul c g)).dropLast)

/-- The remainder `f mod g`. -/
def mod (f g : Poly F) : Poly F := (divMod f g).2

theorem length_divMod_snd_lt (f : Poly F) {g : Poly F} (hg : g ≠ []) :
    (divMod f g).2.length < g.length := by
  have hpos : 0 < g.length := List.length_pos_iff.mpr hg
  induction f with
  | nil => simpa [divMod] using hpos
  | cons a f ih =>
    rw [divMod]
    split_ifs with h
    · exact h
    · simp only [List.length_dropLast, length_sub, length_smul, List.length_cons] at h ⊢
      omega

/-- **Correctness of division with remainder (2.4)**: `f = q g + r`. -/
theorem divMod_spec (f : Poly F) {g : Poly F} (hg : lead g ≠ 0) :
    toPolynomial f =
      toPolynomial (divMod f g).1 * toPolynomial g + toPolynomial (divMod f g).2 := by
  have hgne : g ≠ [] := by rintro rfl; simp [lead] at hg
  induction f with
  | nil => simp [divMod]
  | cons a f ih =>
    have hlen := length_divMod_snd_lt f hgne
    rw [divMod]
    split_ifs with h
    · simp only [toPolynomial_cons, C_0, zero_add, ih]; ring
    · -- one reduction step: the top coefficient of `s - c g` vanishes
      set s := a :: (divMod f g).2 with hs
      set c := lead s * (lead g)⁻¹ with hc
      have hsl : s.length = g.length := by simp only [hs, List.length_cons] at h ⊢; omega
      have hdl : (sub s (smul c g)).length = g.length := by simp [length_sub, hsl]
      have htop : lead (sub s (smul c g)) = 0 := by
        rw [lead, hdl, ← coeff_toPolynomial, toPolynomial_sub, toPolynomial_smul, coeff_sub,
          coeff_C_mul, coeff_toPolynomial, coeff_toPolynomial]
        have h₁ : s.getD (g.length - 1) 0 = lead s := by rw [lead, hsl]
        have h₂ : g.getD (g.length - 1) 0 = lead g := rfl
        rw [h₁, h₂, hc, mul_assoc, inv_mul_cancel₀ hg, mul_one, sub_self]
      have hdrop := toPolynomial_dropLast_add (sub s (smul c g))
      rw [htop, C_0, zero_mul, add_zero, toPolynomial_sub, toPolynomial_smul] at hdrop
      simp only [toPolynomial_cons, hdrop]
      rw [hs]
      simp only [toPolynomial_cons, ih]
      ring

/-- A nonempty list with nonzero top coefficient denotes a polynomial of degree
`length - 1`. -/
theorem degree_toPolynomial {g : Poly F} (hg : lead g ≠ 0) :
    (toPolynomial g).degree = ((g.length - 1 : ℕ) : WithBot ℕ) := by
  have hgne : g ≠ [] := by rintro rfl; simp [lead] at hg
  have hpos : 0 < g.length := List.length_pos_iff.mpr hgne
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).mpr fun m hm ↦ ?_)
    (le_degree_of_ne_zero (by rwa [coeff_toPolynomial]))
  have : g.length - 1 < m := by exact_mod_cast hm
  rw [coeff_toPolynomial, List.getD_eq_default _ _ (by omega)]

/-- `Poly.mod` computes Mathlib's polynomial remainder. -/
theorem toPolynomial_mod (f : Poly F) {g : Poly F} (hg : lead g ≠ 0) :
    toPolynomial (mod f g) = toPolynomial f % toPolynomial g := by
  have hgne : g ≠ [] := by rintro rfl; simp [lead] at hg
  set G := toPolynomial g
  have hG0 : G ≠ 0 := fun h ↦ hg (by
    rw [lead, ← coeff_toPolynomial]; simp [show toPolynomial g = 0 from h])
  have hlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG0
  have hmonic : (G * C G.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hG0
  have hdeg : (toPolynomial (mod f g)).degree < (G * C G.leadingCoeff⁻¹).degree := by
    rw [degree_mul, degree_C (inv_ne_zero hlc), add_zero, degree_toPolynomial hg]
    refine (degree_toPolynomial_lt _).trans_le ?_
    have := length_divMod_snd_lt f hgne
    exact_mod_cast Nat.le_sub_one_of_lt this
  rw [mod_def]
  refine ((div_modByMonic_unique (C G.leadingCoeff * toPolynomial (divMod f g).1) _ hmonic
    ⟨?_, hdeg⟩).2).symm
  rw [divMod_spec f hg, mod]
  have : C G.leadingCoeff⁻¹ * C G.leadingCoeff = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hlc, C_1]
  linear_combination (toPolynomial g * toPolynomial (divMod f g).1) * this

end Field

end Poly

end PrimeNumbers.Chapter2
