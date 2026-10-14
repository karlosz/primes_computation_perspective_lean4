import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.SquareRoot
import PrimeNumbers.Chapter3.TrialDivision
import PrimeNumbers.Chapter3.ProbablePrime

/-!
# §4.1 The `n - 1` test

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 4.1.

* `theorem_4_1_1`   — the Lucas theorem; `lucasTest` is the resulting primality *proof*
                      procedure (it factors `n - 1` by trial division), `prime_of_lucasTest`.
* `theorem_4_1_2`   — the Pepin test for Fermat numbers, both directions; `pepin` is the
                      executable test, `pepin_iff`.
* `theorem_4_1_3`   — Pocklington's theorem; `corollary_4_1_4`; `pocklingtonCheck` checks
                      a certificate based on a partial factorization of `n - 1`,
                      `prime_of_pocklingtonCheck`.

Not formalized: Theorems 4.1.5 (Brillhart–Lehmer–Selfridge), 4.1.6 (Konyagin–Pomerance)
and Algorithm 4.1.7 built on them.
-/

namespace PrimeNumbers.Chapter4

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3

/-- `a^k ≡ 1 (mod n)`, as an equation in `ZMod n`. -/
theorem pow_modEq_one_iff (a k n : ℕ) : a ^ k ≡ 1 [MOD n] ↔ (a : ZMod n) ^ k = 1 := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-! ## Theorem 4.1.1 (Lucas theorem) -/

/-- **Theorem 4.1.1 (Lucas theorem).**  If `a, n` are integers with `n > 1`, and
`a^(n-1) ≡ 1 (mod n)` but `a^((n-1)/q) ≢ 1 (mod n)` for every prime `q ∣ n - 1`,
then `n` is prime. -/
theorem theorem_4_1_1 {a n : ℕ} (h1 : a ^ (n - 1) ≡ 1 [MOD n])
    (hq : ∀ q : ℕ, q.Prime → q ∣ n - 1 → ¬a ^ ((n - 1) / q) ≡ 1 [MOD n]) : n.Prime :=
  lucas_primality n a ((pow_modEq_one_iff ..).mp h1)
    fun q hq₁ hq₂ h ↦ hq q hq₁ hq₂ ((pow_modEq_one_iff ..).mpr h)

/-- The check (4.1) for a given list `qs` of primes:
`a^(n-1) mod n = 1` and `a^((n-1)/q) mod n ≠ 1` for each `q` in the list. -/
counted_def lucasCheck (n a : ℕ) (qs : List ℕ) : Bool :=
  powMod a (n - 1) n = 1 && qs.all fun q ↦ powMod a ((n - 1) / q) n ≠ 1

/-- A primality proof by the Lucas theorem: factor `n - 1` by trial division
(Algorithm 3.1.1) and check (4.1) for the base `a`. -/
counted_def lucasTest (n a : ℕ) : Bool :=
  lucasCheck n a (trialDivision (n - 1))

/-- If `lucasCheck` succeeds with a list containing every prime factor of `n - 1`, then
`n` is prime. -/
theorem prime_of_lucasCheck {n a : ℕ} (hn : 1 < n) {qs : List ℕ}
    (hqs : ∀ q : ℕ, q.Prime → q ∣ n - 1 → q ∈ qs) (h : lucasCheck n a qs = true) : n.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, powMod_eq,
    ne_eq] at h
  have h1n : 1 % n = 1 := Nat.mod_eq_of_lt hn
  refine theorem_4_1_1 (a := a) (by rw [Nat.ModEq, h.1, h1n]) fun q hq₁ hq₂ hmod ↦ ?_
  exact h.2 q (hqs q hq₁ hq₂) (by rw [hmod, h1n])

/-- **`lucasTest` proves primality**: if it returns `true` then `n` is prime. -/
theorem prime_of_lucasTest {n a : ℕ} (hn : 2 < n) (h : lucasTest n a = true) : n.Prime := by
  refine prime_of_lucasCheck (by omega) (fun q hq₁ hq₂ ↦ ?_) h
  rw [(trialDivision_perm (n := n - 1) (by omega)).mem_iff]
  exact (Nat.mem_primeFactorsList (by omega)).mpr ⟨hq₁, hq₂⟩

/-! ## Theorem 4.1.2 (Pepin test) -/

/-- For `k ≥ 1`: `F_k ≡ 1 (mod 4)` and `F_k ≡ 2 (mod 3)`. -/
theorem fermatNumber_mod {k : ℕ} (hk : 1 ≤ k) :
    Nat.fermatNumber k % 4 = 1 ∧ Nat.fermatNumber k % 3 = 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h : 2 ^ 2 ^ (j + 1) = 4 ^ 2 ^ j := by rw [pow_succ', pow_mul]; norm_num
  have h4 : 4 ^ 2 ^ j % 4 = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ j = m + 1 :=
      ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
    rw [hm, pow_succ]; simp
  have h3 : 4 ^ 2 ^ j % 3 = 1 := by rw [Nat.pow_mod]; simp
  rw [Nat.fermatNumber, h]
  omega

/-- **Theorem 4.1.2 (Pepin test).**  For `k ≥ 1`, the number `F_k = 2^(2^k) + 1` is prime
if and only if `3^((F_k - 1)/2) ≡ -1 (mod F_k)`.

Sufficiency is the Lucas theorem with `a = 3` (Mathlib); necessity is, as in the book,
quadratic reciprocity: `F_k ≡ 1 (mod 4)` and `F_k ≡ 2 (mod 3)`, so `3` is a nonresidue. -/
theorem theorem_4_1_2 {k : ℕ} (hk : 1 ≤ k) :
    (Nat.fermatNumber k).Prime ↔
      (3 : ZMod (Nat.fermatNumber k)) ^ ((Nat.fermatNumber k - 1) / 2) = -1 := by
  refine ⟨fun hp ↦ ?_, Nat.pepin_primality' k⟩
  have h23 : ∀ r : ZMod 3, (2 : ZMod 3) ≠ r * r := by decide
  have : Fact (Nat.fermatNumber k).Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h4, h3⟩ := fermatNumber_mod hk
  -- `3` is a square mod `F_k` iff `F_k ≡ 2` is a square mod `3`, which it is not
  have hns : ¬IsSquare ((3 : ℕ) : ZMod (Nat.fermatNumber k)) := by
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h4 (by norm_num)]
    have h2 : ((Nat.fermatNumber k : ℕ) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, h3]; rfl
    rw [h2]
    rintro ⟨r, hr⟩
    exact h23 r hr
  have := pow_half_eq_neg_one hns
  rw [show (Nat.fermatNumber k - 1) / 2 = Nat.fermatNumber k / 2 by omega]
  exact_mod_cast this

/-- The Pepin test, executably: `3^((F_k - 1)/2) mod F_k == F_k - 1`. -/
counted_def pepin (k : ℕ) : Bool :=
  let F := 2 ^ 2 ^ k + 1
  powMod 3 ((F - 1) / 2) F = F - 1

/-- **The Pepin test decides the primality of Fermat numbers** `F_k`, `k ≥ 1`. -/
theorem pepin_iff {k : ℕ} (hk : 1 ≤ k) : pepin k = true ↔ (2 ^ 2 ^ k + 1).Prime := by
  have hF : 0 < 2 ^ 2 ^ k + 1 := by positivity
  change _ ↔ (Nat.fermatNumber k).Prime
  rw [theorem_4_1_2 hk, pepin, decide_eq_true_iff,
    ← natCast_eq_neg_one_iff hF (powMod_lt _ _ hF), cast_powMod]
  rfl

/-! ## Theorem 4.1.3 (Pocklington) -/

/-- **Theorem 4.1.3 (Pocklington).**  Suppose `n - 1 = F R` (4.2), and `a` is such that
`a^(n-1) ≡ 1 (mod n)` and `gcd(a^((n-1)/q) - 1, n) = 1` for each prime `q ∣ F` (4.3).
Then every prime factor of `n` is congruent to `1 (mod F)`.

Proof, as in the book: for a prime `p ∣ n`, the order of `a^R` in `Z_p^*` divides `F`
and is not a proper divisor of `F`, so equals `F`; hence `F ∣ p - 1`. -/
theorem theorem_4_1_3 {n F a : ℕ} (hn : 1 < n) (hF : F ∣ n - 1)
    (h1 : a ^ (n - 1) ≡ 1 [MOD n])
    (hq : ∀ q : ℕ, q.Prime → q ∣ F → IsCoprime ((a : ℤ) ^ ((n - 1) / q) - 1) (n : ℤ))
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) : p ≡ 1 [MOD F] := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := hF
  have hFpos : 0 < F := Nat.pos_of_ne_zero (by rintro rfl; omega)
  -- `x = a^R` satisfies `x^F = 1` in `Z_p`
  have hx : ((a : ZMod p) ^ R) ^ F = 1 := by
    rw [← pow_mul, mul_comm, ← hR]
    exact (pow_modEq_one_iff ..).mp (h1.of_dvd hpn)
  -- and `x^(F/q) ≠ 1` for each prime `q ∣ F`
  have hd : ∀ q : ℕ, q.Prime → q ∣ F → ((a : ZMod p) ^ R) ^ (F / q) ≠ 1 := by
    intro q hq₁ hq₂ h
    have hexp : R * (F / q) = (n - 1) / q := by
      obtain ⟨c, rfl⟩ := hq₂
      rw [hR, Nat.mul_div_cancel_left _ hq₁.pos, mul_assoc, Nat.mul_div_cancel_left _ hq₁.pos,
        mul_comm]
    rw [← pow_mul, hexp] at h
    -- then `p` would divide both `a^((n-1)/q) - 1` and `n`
    have hdvd : (p : ℤ) ∣ (a : ℤ) ^ ((n - 1) / q) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h, sub_self]
    have hunit := (hq q hq₁ hq₂).isUnit_of_dvd' hdvd (Int.natCast_dvd_natCast.mpr hpn)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (Int.ofNat_isUnit.mp hunit))
  have hord : orderOf ((a : ZMod p) ^ R) = F := orderOf_eq_of_pow_and_pow_div_prime hFpos hx hd
  have hx0 : (a : ZMod p) ^ R ≠ 0 := fun h ↦ by
    rw [h, zero_pow hFpos.ne'] at hx
    exact zero_ne_one hx
  have hdvd : F ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  exact ((Nat.modEq_iff_dvd' hp.one_le).mpr hdvd).symm

/-- **Corollary 4.1.4.**  If (4.2) and (4.3) hold and `F ≥ √n`, then `n` is prime. -/
theorem corollary_4_1_4 {n F a : ℕ} (hn : 1 < n) (hF : F ∣ n - 1) (hFn : n ≤ F * F)
    (h1 : a ^ (n - 1) ≡ 1 [MOD n])
    (hq : ∀ q : ℕ, q.Prime → q ∣ F → IsCoprime ((a : ℤ) ^ ((n - 1) / q) - 1) (n : ℤ)) :
    n.Prime := by
  by_contra hnp
  -- the least prime factor `p` of `n` has `p² ≤ n`, but `p ≡ 1 (mod F)` forces `p > F`
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hmod := theorem_4_1_3 hn hF h1 hq hp (Nat.minFac_dvd n)
  have hdvd : F ∣ n.minFac - 1 := (Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm
  have hle : F ≤ n.minFac - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have h2 := hp.two_le
  have : (F + 1) * (F + 1) ≤ n.minFac ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  nlinarith

/-- Check the Pocklington conditions (4.3) for a list `qs` of primes:
`a^(n-1) mod n = 1` and `gcd(a^((n-1)/q) - 1, n) = 1` for each `q` in the list. -/
counted_def pocklingtonCheck (n a : ℕ) (qs : List ℕ) : Bool :=
  powMod a (n - 1) n = 1 &&
    qs.all fun q ↦ Int.gcd ((powMod a ((n - 1) / q) n : ℤ) - 1) n = 1

/-- **A Pocklington certificate proves primality**: if `F ∣ n - 1` with `F ≥ √n`, the
list `qs` contains every prime factor of `F`, and `pocklingtonCheck n a qs` succeeds, then
`n` is prime.  Only the *partial* factorization `F` of `n - 1` is needed. -/
theorem prime_of_pocklingtonCheck {n F a : ℕ} (hn : 1 < n) (hF : F ∣ n - 1) (hFn : n ≤ F * F)
    {qs : List ℕ} (hqs : ∀ q : ℕ, q.Prime → q ∣ F → q ∈ qs)
    (h : pocklingtonCheck n a qs = true) : n.Prime := by
  simp only [pocklingtonCheck, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true,
    powMod_eq] at h
  refine corollary_4_1_4 hn hF hFn (a := a)
    (by rw [Nat.ModEq, h.1, Nat.mod_eq_of_lt hn]) fun q hq₁ hq₂ ↦ ?_
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr (h.2 q (hqs q hq₁ hq₂))
  -- `a^m - 1` and `(a^m mod n) - 1` differ by a multiple of `n`
  have hdm : ((a ^ ((n - 1) / q) % n : ℕ) : ℤ) + n * (a ^ ((n - 1) / q) / n : ℕ) =
      (a : ℤ) ^ ((n - 1) / q) := by exact_mod_cast Nat.mod_add_div (a ^ ((n - 1) / q)) n
  rw [← hdm, add_sub_right_comm]
  exact hcop.add_mul_left_left _

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Pepin test: bit operations -/

/-- **Bit complexity of the Pepin test, grammar-school arithmetic**: cubic in the bit
length of `F_k`. -/
theorem pepinCost_school_le {k : ℕ} (hk : 1 ≤ k) :
    costOf school (pepin k) ≤
      (4 * Nat.log 2 (2 ^ 2 ^ k + 1) + 1) * ((2 ^ 2 ^ k + 1).size + 1) ^ 2 := by
  cost_unfold pepin.counted
  have h4 : 2 ^ 2 ≤ 2 ^ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) (Nat.one_lt_two_pow (by omega))
  refine (powModCost_school_le (by omega) _).trans (Nat.mul_le_mul_right _ ?_)
  have := Nat.log_mono_right (b := 2) (Nat.div_le_self (2 ^ 2 ^ k + 1 - 1) 2)
  have := Nat.log_mono_right (b := 2) (Nat.sub_le (2 ^ 2 ^ k + 1) 1)
  omega

end RunningTime

end PrimeNumbers.Chapter4
