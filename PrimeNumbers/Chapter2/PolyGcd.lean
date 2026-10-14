import PrimeNumbers.Chapter2.Poly

/-!
# §2.2.1 Greatest common divisor for polynomials

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.2.1.

* `Poly.gcd`   — Algorithm 2.2.1 (gcd for polynomials); `toPolynomial_gcd` identifies the
                 result with Mathlib's `EuclideanDomain.gcd`, made monic.
* `Poly.xgcd`  — Algorithm 2.2.2 (extended gcd for polynomials); `xgcd_spec` gives
                 `s f + t g = gcd(f, g)`.
* `Poly.coprime` — the test "`gcd(f, g) = 1`" used by the irreducibility tests;
                 `coprime_iff`.
-/

namespace PrimeNumbers.Chapter2

open Polynomial

namespace Poly

variable {F : Type} [Field F] [DecidableEq F]

/-- A coefficient list is *trimmed* if it is empty or its top coefficient is nonzero. -/
def Trimmed (f : Poly F) : Prop := f = [] ∨ lead f ≠ 0

theorem trimmed_trim (f : Poly F) : Trimmed (trim f) := by
  by_cases h : trim f = []
  · exact Or.inl h
  · exact Or.inr (lead_trim_ne_zero f h)

omit [DecidableEq F] in
theorem Trimmed.lead_ne_zero {f : Poly F} (h : Trimmed f) (hne : f ≠ []) : lead f ≠ 0 :=
  h.resolve_left hne

/-! ## Algorithm 2.2.1 (gcd for polynomials) -/

/-- **Algorithm 2.2.1, step 2 [Euclid loop]**:
```
while (v(x) ≠ 0) (u(x), v(x)) = (v(x), u(x) mod v(x));
```
-/
def gcdLoop (u v : Poly F) : Poly F :=
  if v = [] then u else gcdLoop v (trim (mod u v))
termination_by v.length
decreasing_by exact (length_trim_le _).trans_lt (length_divMod_snd_lt u ‹_›)

/-- **Algorithm 2.2.1, step 3 [Make monic]**: `d(x) = c⁻¹ u(x)`, `c` the leading
coefficient. -/
def makeMonic (u : Poly F) : Poly F := smul (lead u)⁻¹ u

/-- **Algorithm 2.2.1 (gcd for polynomials).**  For `f, g ∈ F[x]` returns the monic
`d(x) = gcd(f(x), g(x))`. -/
def gcd (f g : Poly F) : Poly F := makeMonic (gcdLoop (trim f) (trim g))

theorem gcdLoop_trimmed {u v : Poly F} (hu : Trimmed u) (hv : Trimmed v) :
    Trimmed (gcdLoop u v) := by
  fun_induction gcdLoop u v with
  | case1 u => exact hu
  | case2 u v h ih => exact ih hv (trimmed_trim _)

/-- The Euclid loop computes Mathlib's (un-normalized) Euclidean gcd. -/
theorem toPolynomial_gcdLoop {u v : Poly F} (hv : Trimmed v) :
    toPolynomial (gcdLoop u v) = EuclideanDomain.gcd (toPolynomial v) (toPolynomial u) := by
  fun_induction gcdLoop u v with
  | case1 u => simp [EuclideanDomain.gcd_zero_left]
  | case2 u v h ih =>
    rw [ih (trimmed_trim _), toPolynomial_trim, toPolynomial_mod u (hv.lead_ne_zero h),
      ← EuclideanDomain.gcd_val]

omit [DecidableEq F] in
/-- For a trimmed list, `lead` is the leading coefficient. -/
theorem lead_eq_leadingCoeff {f : Poly F} (h : Trimmed f) :
    lead f = (toPolynomial f).leadingCoeff := by
  rcases h with rfl | h
  · simp [lead]
  · rw [leadingCoeff, natDegree_eq_of_degree_eq_some (degree_toPolynomial h), coeff_toPolynomial,
      lead]

/-- **Correctness of Algorithm 2.2.1**: `gcd f g` denotes the Euclidean gcd of `f` and
`g`, divided by its leading coefficient (so it is monic unless `f = g = 0`). -/
theorem toPolynomial_gcd (f g : Poly F) :
    toPolynomial (gcd f g) =
      C (EuclideanDomain.gcd (toPolynomial g) (toPolynomial f)).leadingCoeff⁻¹ *
        EuclideanDomain.gcd (toPolynomial g) (toPolynomial f) := by
  have h := toPolynomial_gcdLoop (u := trim f) (trimmed_trim g)
  simp only [toPolynomial_trim] at h
  rw [gcd, makeMonic, toPolynomial_smul,
    lead_eq_leadingCoeff (gcdLoop_trimmed (trimmed_trim f) (trimmed_trim g)), h]

/-- "`gcd(f, g) = 1`": the Euclid loop ends in a nonzero constant. -/
def coprime (f g : Poly F) : Bool := (gcdLoop (trim f) (trim g)).length = 1

theorem coprime_iff (f g : Poly F) :
    coprime f g = true ↔ IsCoprime (toPolynomial f) (toPolynomial g) := by
  have h := toPolynomial_gcdLoop (u := trim f) (trimmed_trim g)
  simp only [toPolynomial_trim] at h
  have ht := gcdLoop_trimmed (trimmed_trim f) (trimmed_trim g)
  rw [isCoprime_comm, ← EuclideanDomain.gcd_isUnit_iff, ← h, isUnit_iff_degree_eq_zero, coprime,
    decide_eq_true_iff]
  generalize gcdLoop (trim f) (trim g) = d at ht
  rcases ht with rfl | hd
  · simp
  · rw [degree_toPolynomial hd]
    have : d ≠ [] := by rintro rfl; simp [lead] at hd
    have := List.length_pos_iff.mpr this
    constructor
    · intro h1; rw [h1]; rfl
    · intro h0
      have : d.length - 1 = 0 := by exact_mod_cast h0
      omega

/-! ## Algorithm 2.2.2 (Extended gcd for polynomials) -/

/-- **Algorithm 2.2.2, step 2 [Extended Euclid loop]**:
```
while (w ≠ 0) {
  q = (d - (d mod w))/w;                        // q is the quotient of d ÷ w.
  (s, t, d, u, v, w) = (u, v, w, s - qu, t - qv, d - qw);
}
```
-/
def xgcdLoop (s t d u v w : Poly F) : Poly F × Poly F × Poly F :=
  if w = [] then (s, t, d)
  else
    let qr := divMod d w
    xgcdLoop u v w (sub s (mul qr.1 u)) (sub t (mul qr.1 v)) (trim qr.2)
termination_by w.length
decreasing_by exact (length_trim_le _).trans_lt (length_divMod_snd_lt d ‹_›)

/-- **Algorithm 2.2.2 (Extended gcd for polynomials).**  Returns `(s, t, d)` with
`d = gcd(f, g)` monic and `s f + t g = d`. -/
def xgcd (f g : Poly F) : Poly F × Poly F × Poly F :=
  let r := xgcdLoop [1] [] (trim f) [] [1] (trim g)
  let c := (lead r.2.2)⁻¹
  (smul c r.1, smul c r.2.1, smul c r.2.2)

/-- The third component of the extended loop is the plain Euclid loop. -/
theorem xgcdLoop_snd_snd (s t d u v w : Poly F) : (xgcdLoop s t d u v w).2.2 = gcdLoop d w := by
  fun_induction xgcdLoop s t d u v w with
  | case1 s t d u v => rw [gcdLoop]; simp
  | case2 s t d u v w h qr ih => rw [ih, gcdLoop.eq_def d w]; simp [h, mod, qr]

/-- Loop invariant of Algorithm 2.2.2: `s f + t g = d` and `u f + v g = w`. -/
theorem xgcdLoop_spec (A B : F[X]) (s t d u v w : Poly F) (hw : Trimmed w)
    (h₁ : toPolynomial s * A + toPolynomial t * B = toPolynomial d)
    (h₂ : toPolynomial u * A + toPolynomial v * B = toPolynomial w) :
    toPolynomial (xgcdLoop s t d u v w).1 * A + toPolynomial (xgcdLoop s t d u v w).2.1 * B =
      toPolynomial (xgcdLoop s t d u v w).2.2 := by
  fun_induction xgcdLoop s t d u v w with
  | case1 s t d u v => exact h₁
  | case2 s t d u v w h qr ih =>
    refine ih (trimmed_trim _) h₂ ?_
    have hdiv := divMod_spec d (hw.lead_ne_zero h)
    simp only [toPolynomial_sub, toPolynomial_mul, toPolynomial_trim, qr]
    linear_combination h₁ - toPolynomial (divMod d w).1 * h₂ + hdiv

/-- **Correctness of Algorithm 2.2.2**: for `(s, t, d) = xgcd f g` we have
`s f + t g = d`, and `d` is the output `gcd f g` of Algorithm 2.2.1. -/
theorem xgcd_spec (f g : Poly F) :
    toPolynomial (xgcd f g).1 * toPolynomial f + toPolynomial (xgcd f g).2.1 * toPolynomial g =
        toPolynomial (xgcd f g).2.2 ∧
      (xgcd f g).2.2 = gcd f g := by
  have h := xgcdLoop_spec (toPolynomial f) (toPolynomial g) [1] [] (trim f) [] [1] (trim g)
    (trimmed_trim g) (by simp) (by simp)
  refine ⟨?_, ?_⟩
  · simp only [xgcd, toPolynomial_smul]
    rw [← h]; ring
  · simp only [xgcd, xgcdLoop_snd_snd, gcd, makeMonic]

end Poly

end PrimeNumbers.Chapter2
