import PrimeNumbers.Chapter2.Euclid

/-!
# §2.3.3 Finding polynomial roots: Hensel lifting

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.3.3.

* `IntPoly`, `IntPoly.evalBoth` — integer polynomials as coefficient lists, with a Horner
  scheme computing `f(x)` and `f'(x)` together; tied to Mathlib's `Polynomial ℤ` by
  `IntPoly.evalBoth_eq`.
* `henselStep`, `hensel`       — Algorithm 2.3.11 (Hensel lifting); `hensel_spec`.

(Algorithm 2.3.10, root finding over `F_p`, needs computable polynomial arithmetic over
`F_p` (§2.2) and is not formalized yet.)
-/

namespace PrimeNumbers.Chapter2

open Polynomial

/-! ## Computable integer polynomials -/

/-- A polynomial `c₀ + c₁ x + c₂ x² + ⋯` in `ℤ[x]`, as its list of coefficients
`[c₀, c₁, c₂, …]`. -/
abbrev IntPoly := List ℤ

namespace IntPoly

/-- The Mathlib polynomial denoted by a coefficient list. -/
noncomputable def toPolynomial : IntPoly → ℤ[X]
  | [] => 0
  | c :: f => C c + X * toPolynomial f

/-- Horner's rule for the pair `(f(x), f'(x))`. -/
def evalBoth : IntPoly → ℤ → ℤ × ℤ
  | [], _ => (0, 0)
  | c :: f, x =>
    let vd := evalBoth f x
    (c + x * vd.1, vd.1 + x * vd.2)

theorem evalBoth_eq (f : IntPoly) (x : ℤ) :
    f.evalBoth x = (f.toPolynomial.eval x, (derivative f.toPolynomial).eval x) := by
  induction f with
  | nil => simp [evalBoth, toPolynomial]
  | cons c f ih => simp [evalBoth, toPolynomial, ih]

end IntPoly

/-! ## Algorithm 2.3.11 (Hensel lifting) -/

/-- **Algorithm 2.3.11, the function `newr()`**, with `q = p^(2^i)`:
```
x = f(rᵢ) q⁻¹;
z = (f'(rᵢ))⁻¹ mod q;                              // Via Algorithm 2.1.4.
y = -x z mod q;
rᵢ₊₁ = rᵢ + y q;
```
-/
def henselStep (f : IntPoly) (q : ℕ) (r : ℤ) : ℤ :=
  let vd := f.evalBoth r
  let x := vd.1 / q
  let z := modInv (vd.2 % q).toNat q
  let y := -x * z % q
  r + y * q

/-- **Algorithm 2.3.11 (Hensel lifting).**  Starting from a root `r₀ = r` of `f` modulo
`p`, returns `(rᵢ, p^(2^i))`. -/
def hensel (f : IntPoly) (p : ℕ) (r : ℤ) : ℕ → ℤ × ℕ
  | 0 => (r, p)
  | i + 1 =>
    let rq := hensel f p r i
    (henselStep f rq.2 rq.1, rq.2 * rq.2)

/-- One Hensel step: a root `r` of `f` modulo `q` with `f'(r)` invertible modulo `q` is
lifted to a root `r'` modulo `q²` with `r' ≡ r (mod q)` and `f'(r')` still invertible.
The proof is the book's, via the expansion (2.13)
`f(r + h) = f(r) + h f'(r) + h² g(h)`. -/
theorem henselStep_spec (f : IntPoly) {q : ℕ} (hq : 0 < q) {r : ℤ}
    (hroot : (q : ℤ) ∣ f.toPolynomial.eval r)
    (hunit : IsCoprime ((derivative f.toPolynomial).eval r) (q : ℤ)) :
    ((q : ℤ) ^ 2 ∣ f.toPolynomial.eval (henselStep f q r)) ∧
      henselStep f q r ≡ r [ZMOD q] ∧
      IsCoprime ((derivative f.toPolynomial).eval (henselStep f q r)) ((q : ℤ) ^ 2) := by
  simp only [henselStep, IntPoly.evalBoth_eq]
  set F := f.toPolynomial
  set d := (derivative F).eval r with hd
  obtain ⟨x, hx⟩ := hroot
  have hq0 : (q : ℤ) ≠ 0 := by positivity
  rw [hx, Int.mul_ediv_cancel_left _ hq0]
  -- `z` inverts `f'(r)` modulo `q`
  set z := modInv (d % q).toNat q
  have hz : d * z ≡ 1 [ZMOD q] := by
    have hnn : ((d % q).toNat : ℤ) = d % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq0)
    have hcop : Nat.Coprime (d % q).toNat q := by
      rw [Nat.Coprime, ← Int.gcd_natCast_natCast, hnn, ← Int.isCoprime_iff_gcd_eq_one, Int.emod_def,
        sub_eq_add_neg, ← mul_neg]
      exact hunit.add_mul_left_left _
    have := Int.natCast_modEq_iff.mpr (mul_modInv_modEq hcop)
    push_cast [hnn] at this
    exact ((Int.mod_modEq d q).mul_right _).symm.trans this
  -- `y ≡ -x z`, so `x + f'(r) y ≡ 0 (mod q)`
  set y := -x * z % q
  have hy : x + d * y ≡ 0 [ZMOD q] :=
    calc x + d * y ≡ x + d * (-x * z) [ZMOD q] := ((Int.mod_modEq _ _).mul_left _).add_left _
      _ = x + -x * (d * z) := by ring
      _ ≡ x + -x * 1 [ZMOD q] := (hz.mul_left _).add_left _
      _ = 0 := by ring
  obtain ⟨c, hc⟩ := Int.modEq_zero_iff_dvd.mp hy
  refine ⟨?_, ?_, ?_⟩
  · -- (2.13): `f(r + yq) = f(r) + yq f'(r) + (yq)² k = q (x + f'(r) y) + q² y² k`
    obtain ⟨k, hk⟩ := F.binomExpansion r (y * q)
    exact ⟨c + k * y ^ 2, by rw [hk, hx, ← hd]; linear_combination (q : ℤ) * hc⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-y, by ring⟩
  · -- `f'(r') ≡ f'(r) (mod q)`
    obtain ⟨m, hm⟩ := (derivative F).sub_dvd_eval_sub (r + y * q) r
    have : (derivative F).eval (r + y * q) = d + q * (y * m) := by
      rw [hd]; linear_combination hm
    rw [this]
    exact (hunit.add_mul_left_left _).pow_right

/-- **Correctness of Algorithm 2.3.11.**  Let `f ∈ ℤ[x]`, and let `r` satisfy
`f(r) ≡ 0 (mod p)` with `f'(r)` invertible modulo `p` (for prime `p`: `f'(r) ≢ 0`).
Then for the sequence `r₀, r₁, …` computed by `hensel`:
`f(rᵢ) ≡ 0 (mod p^(2^i))` and `rᵢ₊₁ ≡ rᵢ (mod p^(2^i))`. -/
theorem hensel_spec (f : IntPoly) {p : ℕ} (hp : 0 < p) {r : ℤ}
    (hroot : (p : ℤ) ∣ f.toPolynomial.eval r)
    (hunit : IsCoprime ((derivative f.toPolynomial).eval r) (p : ℤ)) (i : ℕ) :
    (hensel f p r i).2 = p ^ 2 ^ i ∧
      ((p : ℤ) ^ 2 ^ i ∣ f.toPolynomial.eval (hensel f p r i).1) ∧
      (hensel f p r (i + 1)).1 ≡ (hensel f p r i).1 [ZMOD (p : ℤ) ^ 2 ^ i] := by
  -- strengthen the statement with the invertibility of `f'(rᵢ)`, and induct
  have key : ∀ i, (hensel f p r i).2 = p ^ 2 ^ i ∧
      (((hensel f p r i).2 : ℤ) ∣ f.toPolynomial.eval (hensel f p r i).1) ∧
      IsCoprime ((derivative f.toPolynomial).eval (hensel f p r i).1)
        ((hensel f p r i).2 : ℤ) := by
    intro i
    induction i with
    | zero => simpa [hensel] using ⟨hroot, hunit⟩
    | succ i ih =>
      obtain ⟨hq, hdvd, hcop⟩ := ih
      obtain ⟨h₁, -, h₃⟩ := henselStep_spec f (by rw [hq]; positivity) hdvd hcop
      refine ⟨?_, ?_, ?_⟩
      · simp only [hensel, hq]; ring
      · simpa [hensel, sq] using h₁
      · simpa [hensel, sq] using h₃
  obtain ⟨hq, hdvd, hcop⟩ := key i
  obtain ⟨-, h₂, -⟩ := henselStep_spec f (by rw [hq]; positivity) hdvd hcop
  rw [hq] at hdvd h₂
  exact ⟨hq, by exact_mod_cast hdvd, by simpa [hensel, hq] using h₂⟩

end PrimeNumbers.Chapter2
