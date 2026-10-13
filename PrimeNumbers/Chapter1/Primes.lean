import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Chapter 1 — Primes!

Crandall & Pomerance, *Prime Numbers: A Computational Perspective* (2nd ed.), Chapter 1.

Chapter 1 is a survey chapter.  Almost every result in it that is within reach of
today's Mathlib is already *in* Mathlib, so this file is mostly a dictionary: each
theorem is stated the way the book states it and then proved by pointing at the
corresponding Mathlib result.  The exceptions, proved here following the book, are
Theorem 1.3.2 (Euler's theorem on the prime factors of Mersenne numbers) and the
packaging of Theorem 1.3.5.

Results that are out of reach (the prime number theorem 1.1.4, Brun's theorem 1.2.1,
Mertens' theorem 1.4.2, …) are listed at the end of the file.
-/

namespace PrimeNumbers.Chapter1

open Nat

/-! ## §1.1 Problems and progress -/

/-- **Theorem 1.1.1 (Fundamental theorem of arithmetic).**
For each natural number `n` there is a unique factorization `n = p₁^a₁ ⋯ pₖ^aₖ` into
prime powers.  A factorization is modelled as a finitely supported function `f` from
primes to exponents; the unique one is `Nat.factorization n`. -/
theorem theorem_1_1_1 {n : ℕ} (hn : n ≠ 0) :
    ∃! f : ℕ →₀ ℕ, (∀ p ∈ f.support, p.Prime) ∧ f.prod (· ^ ·) = n := by
  refine ⟨n.factorization, ⟨fun p hp ↦ prime_of_mem_primeFactors (by simpa using hp),
    prod_factorization_pow_eq_self hn⟩, ?_⟩
  rintro f ⟨hf, hprod⟩
  exact (eq_factorization_iff hn hf).mpr hprod

/-- **Theorem 1.1.2 (Euclid).** There exist infinitely many primes. -/
theorem theorem_1_1_2 : {p : ℕ | p.Prime}.Infinite :=
  infinite_setOfPred_prime

/-- **Theorem 1.1.3 (Chebyshev), upper bound.**  `π(x) ≤ B x / ln x` for all large `x`,
for any constant `B > ln 4`. -/
theorem theorem_1_1_3_upper {B : ℝ} (hB : Real.log 4 < B) :
    ∀ᶠ x : ℝ in Filter.atTop, (primeCounting ⌊x⌋₊ : ℝ) ≤ B * x / Real.log x := by
  simpa using Chebyshev.eventually_primeCounting_le (sub_pos.mpr hB)

/-- **Theorem 1.1.3 (Chebyshev), lower bound**, in the explicit form
`(n ln 2 - ln (n+1)) / ln n ≤ π(n)`. -/
theorem theorem_1_1_3_lower (n : ℕ) :
    (n * Real.log 2 - Real.log (n + 1)) / Real.log n ≤ primeCounting n :=
  Chebyshev.pi_ge n

/-- **Theorem 1.1.5 (Dirichlet).**  If `a, d` are coprime and `d > 0`, the arithmetic
progression `a, a + d, a + 2d, …` contains infinitely many primes. -/
theorem theorem_1_1_5 {a d : ℕ} (hd : d ≠ 0) (had : a.Coprime d) :
    {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}.Infinite :=
  infinite_setOfPred_prime_and_modEq hd had

/-! ## §1.3 Primes of special form -/

/-- **Theorem 1.3.1.**  If `M_q = 2^q - 1` is prime, then `q` is prime. -/
theorem theorem_1_3_1 {q : ℕ} (h : (2 ^ q - 1).Prime) : q.Prime :=
  Nat.Prime.of_mersenne h

/-- **Theorem 1.3.2 (Euler).**  For a prime `q > 2`, any prime factor `r` of
`M_q = 2^q - 1` is `≡ 1 (mod q)` and `≡ ±1 (mod 8)`.

The proof is the book's: `2` has multiplicative order exactly `q` modulo `r`, so
`q ∣ r - 1`; as `q` is odd even `q ∣ (r-1)/2`, hence `2^((r-1)/2) ≡ 1`, so `2` is a
square mod `r` by Euler's criterion (2.6), which by (2.10) forces `r ≡ ±1 (mod 8)`. -/
theorem theorem_1_3_2 {q r : ℕ} (hq : q.Prime) (hq2 : 2 < q) (hr : r.Prime)
    (hdvd : r ∣ 2 ^ q - 1) :
    r ≡ 1 [MOD q] ∧ (r % 8 = 1 ∨ r % 8 = 7) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  -- `2^q ≡ 1 (mod r)`
  have hpow : (2 : ZMod r) ^ q = 1 := by
    have h : ((2 ^ q - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow] at h
    simpa [sub_eq_zero] using h
  -- `r` is odd, since it divides the odd number `2^q - 1`
  have hr2 : r ≠ 2 := by
    rintro rfl
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_pow hq.ne_zero] at hpow
    exact zero_ne_one hpow
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne_zero] at hpow
    exact zero_ne_one hpow
  have h2ne1 : (2 : ZMod r) ≠ 1 := by
    intro h
    have : (1 : ZMod r) = 0 := by linear_combination h
    exact one_ne_zero this
  -- the order of `2` is exactly `q`, hence `q ∣ r - 1`
  have hord : orderOf (2 : ZMod r) = q := orderOf_eq_prime hpow h2ne1
  have hq_dvd : q ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one h2ne
  have hr_odd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
  refine ⟨?_, ?_⟩
  · exact ((Nat.modEq_iff_dvd' hr.one_le).mpr hq_dvd).symm
  · -- `q` is odd, so in fact `q ∣ (r-1)/2`
    have hq_dvd' : q ∣ r / 2 := by
      have h2 : r - 1 = 2 * (r / 2) := by omega
      rw [h2] at hq_dvd
      exact (Nat.Coprime.dvd_mul_left
        ((Nat.coprime_primes hq prime_two).mpr (by omega))).mp hq_dvd
    -- Euler's criterion
    have hsq : IsSquare (2 : ZMod r) := by
      rw [ZMod.euler_criterion r h2ne]
      obtain ⟨c, hc⟩ := hq_dvd'
      rw [hc, pow_mul, hpow, one_pow]
    exact (ZMod.exists_sq_eq_two_iff hr2).mp hsq

/-- **Theorem 1.3.3 (Euclid–Euler).**  An even number `n` is perfect if and only if it
is of the form `n = 2^(q-1) M_q` with `M_q = 2^q - 1` prime.  (Here `q = k + 1`.) -/
theorem theorem_1_3_3 {n : ℕ} :
    Even n ∧ n.Perfect ↔ ∃ k, (2 ^ (k + 1) - 1).Prime ∧ n = 2 ^ k * (2 ^ (k + 1) - 1) :=
  Theorems100.Nat.even_and_perfect_iff

/-- **Theorem 1.3.4.**  If `p = 2^m + 1` is an odd prime, then `m` is a power of two. -/
theorem theorem_1_3_4 {m : ℕ} (hodd : Odd (2 ^ m + 1)) (hp : (2 ^ m + 1).Prime) :
    ∃ k, m = 2 ^ k := by
  refine pow_of_pow_add_prime one_lt_two ?_ hp
  rintro rfl
  exact absurd hodd (by decide)

/-- **Theorem 1.3.5 (Euler, Lucas).**  For `n ≥ 2`, any prime factor `p` of the Fermat
number `F_n = 2^(2^n) + 1` satisfies `p ≡ 1 (mod 2^(n+2))`. -/
theorem theorem_1_3_5 {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hdvd : p ∣ 2 ^ 2 ^ n + 1) :
    p ≡ 1 [MOD 2 ^ (n + 2)] := by
  obtain ⟨k, rfl⟩ := fermat_primeFactors_one_lt n p hn hp hdvd
  simp [Nat.ModEq]

/-- **Theorem 1.3.6 (Wilson–Lagrange).**  An integer `p > 1` is prime if and only if
`(p - 1)! ≡ -1 (mod p)`. -/
theorem theorem_1_3_6 {p : ℕ} (hp : 1 < p) : p.Prime ↔ ((p - 1)! : ZMod p) = -1 :=
  prime_iff_fac_equiv_neg_one hp.ne'

/-! ## §1.4 Analytic number theory -/

/-- **Theorem 1.4.1 (Euler).**  For `Re s > 1`, `ζ(s) = ∏_p (1 - p^{-s})⁻¹`. -/
theorem theorem_1_4_1 {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ :=
  (riemannZeta_eulerProduct_tprod hs).symm

/-- **Conjecture 1.4.1 (Riemann hypothesis).**  All zeros of `ζ` in the critical strip
lie on the line `Re s = 1/2`.  This is only the *statement*, as formulated in Mathlib. -/
def conjecture_1_4_1 : Prop := RiemannHypothesis

/-!
## Not formalized

The following numbered results of Chapter 1 are stated in the book without proof and
are not (yet) available in Mathlib; they are deliberately left out rather than assumed:

* Theorem 1.1.4 (prime number theorem), Theorem 1.4.3 and the RH-equivalent error terms;
* Theorem 1.2.1 (Brun), Theorem 1.2.2 (prime-producing formulae);
* Theorem 1.4.2 (Mertens), Theorems 1.4.5–1.4.7 (ERH bound, Siegel–Walfisz,
  Brun–Titchmarsh), Theorem 1.4.9 (Dickman).
-/

end PrimeNumbers.Chapter1
