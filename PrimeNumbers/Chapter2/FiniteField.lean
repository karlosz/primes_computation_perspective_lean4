import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.PolyGcd

/-!
# §2.2.2 Finite fields

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.2.2.

* `theorem_2_2_3`   — `F[x]/(f)` is a field iff `f` is irreducible.
* `theorem_2_2_5_*` — basic results on finite fields (from Mathlib).
* `theorem_2_2_7`   — test for primitive root.
* `theorem_2_2_8`   — `f` of degree `k` is irreducible iff `gcd(f, x^(p^j) - x) = 1` for
                      `j = 1, …, ⌊k/2⌋` (statements (1) ⇔ (2) of the book's theorem).
* `Poly.powMod`     — powering modulo `f(x)` by Algorithm 2.1.5.
* `isIrreducible`   — Algorithm 2.2.9 (Irreducibility test 1); `isIrreducible_iff`.

Not yet formalized: statement (3) of Theorem 2.2.8 and Algorithm 2.2.10 (test 2),
parts (4), (5) of Theorem 2.2.5, and the counting formula (2.5).
-/

namespace PrimeNumbers.Chapter2

open Polynomial

/-- **Theorem 2.2.3.**  If `F` is a field and `f ∈ F[x]` has positive degree, then
`F[x]/(f)` is a field if and only if `f` is irreducible. -/
theorem theorem_2_2_3 {F : Type*} [Field F] {f : F[X]} (hf : 0 < f.natDegree) :
    IsField (F[X] ⧸ Ideal.span {f}) ↔ Irreducible f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact ⟨fun h ↦ ((Ideal.span_singleton_prime hf0).mp h.isPrime).irreducible,
    PrincipalIdealRing.isMaximal_of_irreducible⟩

/-! ## Theorem 2.2.5 (Basic results on finite fields) -/

section FiniteFields

variable (K : Type*) [Field K] [Finite K]

/-- **Theorem 2.2.5 (1).**  A finite field has nonzero characteristic, which is prime. -/
theorem theorem_2_2_5_1 : ∃ p : ℕ, p.Prime ∧ CharP K p := by
  obtain ⟨p, hp⟩ := CharP.exists K
  exact ⟨p, CharP.char_is_prime K p, hp⟩

omit [Finite K] in
/-- **Theorem 2.2.5 (2).**  In characteristic `p`, `(a + b)^p = a^p + b^p`. -/
theorem theorem_2_2_5_2 (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) :
    (a + b) ^ p = a ^ p + b ^ p :=
  add_pow_char a b p

omit [Finite K] in
/-- **Theorem 2.2.5 (3).**  A finite field of characteristic `p` has `p^k` elements for
some positive integer `k`. -/
theorem theorem_2_2_5_3 [Fintype K] (p : ℕ) [CharP K p] :
    ∃ k : ℕ, 0 < k ∧ Fintype.card K = p ^ k := by
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  exact ⟨n, n.pos, hn⟩

/-- **Theorem 2.2.5 (6).**  The multiplicative group of a finite field is cyclic. -/
theorem theorem_2_2_5_6 : IsCyclic Kˣ := inferInstance

variable {K}

omit [Finite K] in
/-- **Theorem 2.2.7 (Test for primitive root).**  An element `g` of `F*` (with
`#F = p^k`) is a primitive root, i.e. has order `p^k - 1`, if and only if
`g^((p^k - 1)/q) ≠ 1` for every prime `q` dividing `p^k - 1`. -/
theorem theorem_2_2_7 [Fintype K] (g : Kˣ) :
    orderOf g = Fintype.card K - 1 ↔
      ∀ q : ℕ, q.Prime → q ∣ Fintype.card K - 1 → g ^ ((Fintype.card K - 1) / q) ≠ 1 := by
  classical
  have hcard : Fintype.card Kˣ = Fintype.card K - 1 := Fintype.card_units K
  have hpos : 0 < Fintype.card K - 1 := hcard ▸ Fintype.card_pos
  constructor
  · intro hord q hq hdvd h1
    have := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos hdvd) hq.pos)
      (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    exact absurd this (not_le.mpr (Nat.div_lt_self hpos hq.one_lt))
  · exact orderOf_eq_of_pow_and_pow_div_prime hpos (hcard ▸ pow_card_eq_one)

end FiniteFields

/-! ## Theorem 2.2.8 -/

/-- **Theorem 2.2.8, (1) ⇔ (2).**  Let `f ∈ K[x]` have positive degree `k`, `K` a finite
field with `q` elements.  Then `f` is irreducible if and only if
`gcd(f(x), x^(q^j) - x) = 1` for each `j = 1, 2, …, ⌊k/2⌋`.

The proof uses that an irreducible `g` divides `x^(q^j) - x` exactly when `deg g ∣ j`:
a reducible `f` has an irreducible factor of degree `j ≤ k/2`, which then divides
`x^(q^j) - x`; an irreducible `f` cannot divide `x^(q^j) - x` for `j < k`. -/
theorem theorem_2_2_8 {K : Type*} [Field K] [Finite K] {f : K[X]} (hk : 0 < f.natDegree) :
    Irreducible f ↔
      ∀ j, 0 < j → j ≤ f.natDegree / 2 → IsCoprime f (X ^ Nat.card K ^ j - X) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hk
  have hfu : ¬IsUnit f := fun h ↦ by
    have := natDegree_eq_zero_of_isUnit h
    omega
  constructor
  · intro hirr j hj hjk
    rw [hirr.coprime_iff_not_dvd]
    intro hdvd
    have := Nat.le_of_dvd hj (hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd)
    omega
  · intro h
    by_contra hirr
    -- a reducible `f` is a product `a b` of non-units; say `deg a ≤ deg b`
    obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b, f = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
      by_contra hcon
      push Not at hcon
      exact hirr (irreducible_iff.mpr ⟨hfu, fun a b hab ↦ by
        by_contra hc
        push Not at hc
        exact hc.2 (hcon a b hab hc.1)⟩)
    wlog hle : a.natDegree ≤ b.natDegree generalizing a b
    · exact this b a (by rw [hab, mul_comm]) hb ha (by omega)
    have ha0 : a ≠ 0 := by rintro rfl; exact hf0 (by rw [hab, zero_mul])
    have hb0 : b ≠ 0 := by rintro rfl; exact hf0 (by rw [hab, mul_zero])
    have hdeg : f.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
    -- take an irreducible factor `g` of `a`; its degree `j` is at most `k/2`
    obtain ⟨g, hg, hga⟩ := WfDvdMonoid.exists_irreducible_factor ha ha0
    have hgdeg : g.natDegree ≤ a.natDegree := natDegree_le_of_dvd hga ha0
    have hcop := h g.natDegree hg.natDegree_pos (by omega)
    exact hg.not_isUnit (hcop.isUnit_of_dvd' (hga.trans ⟨b, hab⟩)
      (hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp dvd_rfl))

/-! ## Powering modulo a polynomial -/

namespace Poly

variable {F : Type*} [Field F] [DecidableEq F]

/-- Multiplication in `F[x]/(f)`: multiply, then reduce modulo `f`. -/
def mulMod (f a b : Poly F) : Poly F := trim (mod (mul a b) f)

/-- Coefficient lists, with multiplication modulo `f`: the semigroup in which
Algorithm 2.1.5 is run. -/
def ModPoly (_f : Poly F) : Type _ := Poly F

instance (f : Poly F) : Mul (ModPoly f) := ⟨mulMod f⟩

/-- `x(t)ⁿ mod f(t)`, "powering by Algorithm 2.1.5". -/
def powMod (f x : Poly F) (n : ℕ) : Poly F := pow (M := ModPoly f) x n

/-- `powMod f x n ≡ xⁿ (mod f)`. -/
theorem dvd_powMod_sub {f : Poly F} (hf : lead f ≠ 0) (x : Poly F) {n : ℕ} (hn : 0 < n) :
    toPolynomial f ∣ toPolynomial (powMod f x n) - toPolynomial x ^ n := by
  refine pow_rel (M := ModPoly f) (fun a A ↦ toPolynomial f ∣ toPolynomial a - A) ?_
    (x := x) (by simp) hn
  intro (a : Poly F) (b : Poly F) A B ⟨c, hc⟩ ⟨d, hd⟩
  change toPolynomial f ∣ toPolynomial (mulMod f a b) - A * B
  rw [show mulMod f a b = trim (mod (mul a b) f) from rfl, toPolynomial_trim,
    toPolynomial_mod _ hf, toPolynomial_mul,
    EuclideanDomain.mod_eq_sub_mul_div]
  exact ⟨toPolynomial a * d + B * c - toPolynomial a * toPolynomial b / toPolynomial f, by
    linear_combination toPolynomial a * hd + B * hc⟩

end Poly

/-! ## Algorithm 2.2.9 (Irreducibility test 1) -/

section Irreducibility

open PrimeNumbers.Chapter2.Poly

variable (p : ℕ) [Fact p.Prime]

/-- **Algorithm 2.2.9, step 2 [Testing loop]** (`n` passes remaining):
```
g(x) = g(x)^p mod f(x);              // Powering by Algorithm 2.1.5.
d(x) = gcd(f(x), g(x) - x);          // Polynomial gcd by Algorithm 2.2.1.
if (d(x) ≠ 1) return NO;
```
-/
def irreducibleLoop (f g : Poly (ZMod p)) : ℕ → Bool
  | 0 => true
  | n + 1 =>
    let g' := Poly.powMod f g p
    if coprime f (sub g' [0, 1]) then irreducibleLoop f g' n else false

/-- **Algorithm 2.2.9 (Irreducibility test 1).**  Given a prime `p` and `f ∈ F_p[x]` of
degree `k ≥ 2` (as a trimmed coefficient list), decides whether `f` is irreducible. -/
def isIrreducible (f : Poly (ZMod p)) : Bool :=
  irreducibleLoop p f [0, 1] ((f.length - 1) / 2)

variable {p}

/-- Loop invariant of Algorithm 2.2.9: entering pass `i + 1` we have
`g ≡ x^(p^i) (mod f)`; the loop answers YES iff all the remaining gcd's are `1`. -/
theorem irreducibleLoop_iff {f : Poly (ZMod p)} (hf : lead f ≠ 0) (g : Poly (ZMod p)) (i n : ℕ)
    (hg : toPolynomial f ∣ toPolynomial g - X ^ p ^ i) :
    irreducibleLoop p f g n = true ↔
      ∀ j, i < j → j ≤ i + n → IsCoprime (toPolynomial f) (X ^ p ^ j - X) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction n generalizing g i with
  | zero => simp only [irreducibleLoop, true_iff]; intro j h₁ h₂; omega
  | succ n ih =>
    -- the new `g' = g^p mod f` is `≡ x^(p^(i+1))`
    have hg' : toPolynomial f ∣ toPolynomial (Poly.powMod f g p) - X ^ p ^ (i + 1) := by
      have h₁ := dvd_powMod_sub hf g hp
      have h₂ := hg.trans (sub_dvd_pow_sub_pow (toPolynomial g) (X ^ p ^ i) p)
      rw [← pow_mul, ← pow_succ] at h₂
      simpa using dvd_add h₁ h₂
    -- so the gcd test is about `x^(p^(i+1)) - x`
    have htest : coprime f (sub (Poly.powMod f g p) [0, 1]) = true ↔
        IsCoprime (toPolynomial f) (X ^ p ^ (i + 1) - X) := by
      obtain ⟨c, hc⟩ := hg'
      rw [coprime_iff, toPolynomial_sub]
      have : toPolynomial (Poly.powMod f g p) - toPolynomial ([0, 1] : Poly (ZMod p)) =
          X ^ p ^ (i + 1) - X + toPolynomial f * c := by
        simp only [toPolynomial_cons, toPolynomial_nil, C_0, C_1]
        linear_combination hc
      rw [this, IsCoprime.add_mul_left_right_iff]
    simp only [irreducibleLoop]
    split_ifs with hc
    · refine (ih _ (i + 1) hg').trans ?_
      constructor
      · intro h j h₁ h₂
        rcases Nat.lt_or_ge (i + 1) j with hlt | hge
        · exact h j hlt (by omega)
        · obtain rfl : j = i + 1 := by omega
          exact htest.mp hc
      · intro h j h₁ h₂
        exact h j (by omega) (by omega)
    · simp only [false_iff]
      exact fun h ↦ hc (htest.mpr (h (i + 1) (by omega) (by omega)))

/-- **Correctness of Algorithm 2.2.9.**  For `f ∈ F_p[x]` of degree `≥ 1`, given as a
coefficient list with nonzero top coefficient, the test answers YES exactly when `f` is
irreducible over `F_p`. -/
theorem isIrreducible_iff {f : Poly (ZMod p)} (hf : lead f ≠ 0) (hk : 2 ≤ f.length) :
    isIrreducible p f = true ↔ Irreducible (toPolynomial f) := by
  have hdeg : (toPolynomial f).natDegree = f.length - 1 :=
    natDegree_eq_of_degree_eq_some (degree_toPolynomial hf)
  rw [theorem_2_2_8 (by omega), isIrreducible,
    irreducibleLoop_iff hf [0, 1] 0 _ (by simp), hdeg, Nat.card_zmod]
  simp only [zero_add]

end Irreducibility

end PrimeNumbers.Chapter2
