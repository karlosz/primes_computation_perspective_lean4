import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter3.Sieve

/-!
# §5.4 Pollard `p - 1` method

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.4.

* `pollardPMinusOne`        — Algorithm 5.4.1 (basic Pollard `p - 1` method).
* `pollardPMinusOne_dvd`    — the result divides `n`.
* `ladder_eq`               — after the power ladders, `c ≡ c₀^M (mod n)` with
                              `M = pm1Exponent B = ∏_{p ≤ B} p^(a_p)`, the least common
                              multiple `M(B)` of `1, …, B`.
* `dvd_pollardPMinusOne`    — **when the method works**: every prime `p ∣ n` with `p ∤ c₀`
                              and `p - 1 ∣ M(B)` divides the result.
* `sub_one_dvd_pm1Exponent` — `p - 1 ∣ M(B)` holds as soon as every prime power dividing
                              `p - 1` is at most `B` (`p - 1` is "`B`-powersmooth").

So if `n` has a prime factor `p` with `p - 1` `B`-powersmooth, the result is `≠ 1`.  As the
book explains, the result may still be `n` itself (e.g. `n = 2047`, `B = 12`).
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3

/-- **Algorithm 5.4.1, step 1 [Establish prime-power base]**: the primes `p ≤ B`, found
with the sieve of Eratosthenes of §3.2. -/
def primesUpTo (B : ℕ) : List ℕ := sievePrimes B

theorem mem_primesUpTo {B q : ℕ} : q ∈ primesUpTo B ↔ q.Prime ∧ q ≤ B := mem_sievePrimes

/-- The exponent `M(B) = ∏_{p ≤ B} p^(a_p)`, where `a_p = ⌊log_p B⌋` is the maximum integer
with `p^(a_p) ≤ B`.  This is `lcm(1, …, B)`. -/
def pm1Exponent (B : ℕ) : ℕ :=
  ((primesUpTo B).map fun p ↦ p ^ Nat.log p B).prod

/-- The inner loop of step 2: `for (1 ≤ j ≤ a) c = c^p mod n`. -/
def ladder (n p : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => c
  | j + 1 => ladder n p (powMod c p n) j

/-- **Algorithm 5.4.1, step 2 [Perform power ladders]**:
```
for (1 ≤ i ≤ m) { for (1 ≤ j ≤ aᵢ) c = c^(pᵢ) mod n; }
```
-/
def ladders (n B c : ℕ) : ℕ :=
  (primesUpTo B).foldl (fun c p ↦ ladder n p c (Nat.log p B)) c

/-- **Algorithm 5.4.1 (Basic Pollard `p - 1` method).**  Given a composite odd `n` and a
search bound `B`, attempts to find a nontrivial factor of `n`, starting from `c` (the
book takes `c = 2`).
```
3. [Test gcd]   g = gcd(c - 1, n);   return g;      // We hope for a success 1 < g < n.
```
-/
def pollardPMinusOne (n B : ℕ) (c : ℕ := 2) : ℕ :=
  euclid n ((ladders n B c + n - 1) % n)

theorem pollardPMinusOne_dvd (n B c : ℕ) : pollardPMinusOne n B c ∣ n := by
  rw [pollardPMinusOne, euclid_eq_gcd]
  exact Nat.gcd_dvd_left _ _

/-! ## What the ladders compute -/

theorem ladder_mod (n p c j : ℕ) : ladder n p c j % n = c ^ p ^ j % n := by
  induction j generalizing c with
  | zero => simp [ladder]
  | succ j ih => rw [ladder, ih, powMod_eq, ← Nat.pow_mod, ← pow_mul, ← pow_succ']

theorem foldl_ladder_mod (n B : ℕ) (L : List ℕ) (c : ℕ) :
    L.foldl (fun c p ↦ ladder n p c (Nat.log p B)) c % n =
      c ^ (L.map fun p ↦ p ^ Nat.log p B).prod % n := by
  induction L generalizing c with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, pow_mul, Nat.pow_mod, ladder_mod,
      ← Nat.pow_mod]

/-- After step 2, `c ≡ c₀^(M(B)) (mod n)`. -/
theorem ladder_eq (n B c : ℕ) : ladders n B c % n = c ^ pm1Exponent B % n :=
  foldl_ladder_mod n B _ c

/-! ## When the method works -/

/-- If every prime power dividing `m` is at most `B`, then `m ∣ M(B)`. -/
theorem dvd_pm1Exponent {m B : ℕ}
    (hsmooth : ∀ q e : ℕ, q.Prime → q ^ e ∣ m → q ^ e ≤ B) : m ∣ pm1Exponent B := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro q e hq hqe
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hle : q ^ e ≤ B := hsmooth q e hq hqe
  have hqB : q ≤ B := (Nat.le_self_pow he.ne' q).trans hle
  -- `q^e ∣ q^(a_q)`, one of the factors of `M(B)`
  refine (pow_dvd_pow q (Nat.le_log_of_pow_le hq.one_lt hle)).trans ?_
  exact List.dvd_prod (List.mem_map.mpr ⟨q, mem_primesUpTo.mpr ⟨hq, hqB⟩, rfl⟩)

/-- For a prime `p`, if `p - 1` is `B`-powersmooth then `p - 1 ∣ M(B)`. -/
theorem sub_one_dvd_pm1Exponent {p B : ℕ}
    (hsmooth : ∀ q e : ℕ, q.Prime → q ^ e ∣ p - 1 → q ^ e ≤ B) : p - 1 ∣ pm1Exponent B :=
  dvd_pm1Exponent hsmooth

/-- **Why Algorithm 5.4.1 works.**  If `p` is a prime factor of `n` not dividing the start
value `c`, and `p - 1 ∣ M(B)`, then `p` divides the result `gcd(c^(M(B)) - 1, n)`:
"if `p - 1 ∣ M`, then `c^M ≡ 1 (mod p)`". -/
theorem dvd_pollardPMinusOne {n p B c : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n)
    (hpc : ¬p ∣ c) (hM : p - 1 ∣ pm1Exponent B) : p ∣ pollardPMinusOne n B c := by
  have : Fact p.Prime := ⟨hp⟩
  -- Fermat: `c^M ≡ 1 (mod p)`
  have hc0 : (c : ZMod p) ≠ 0 := fun h ↦ hpc ((ZMod.natCast_eq_zero_iff c p).mp h)
  have hpow : (c : ZMod p) ^ pm1Exponent B = 1 := by
    obtain ⟨e, he⟩ := hM
    rw [he, pow_mul, ZMod.pow_card_sub_one_eq_one hc0, one_pow]
  -- so `p` divides `c' - 1`, where `c' ≡ c^M (mod n)` is the output of the ladders
  have hcast : ((ladders n B c : ℕ) : ZMod p) = 1 := by
    have h₁ : ((ladders n B c % n : ℕ) : ZMod p) = ((c ^ pm1Exponent B % n : ℕ) : ZMod p) := by
      rw [ladder_eq]
    have key : ∀ x : ℕ, ((x % n : ℕ) : ZMod p) = (x : ZMod p) := fun x ↦ by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hpn]
    rw [key, key, Nat.cast_pow, hpow] at h₁
    exact h₁
  have hdvd : p ∣ (ladders n B c + n - 1) % n := by
    rw [Nat.dvd_mod_iff hpn, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), Nat.cast_add,
      hcast, (ZMod.natCast_eq_zero_iff n p).mpr hpn]
    simp
  rw [pollardPMinusOne, euclid_eq_gcd]
  exact Nat.dvd_gcd hpn hdvd

/-- In particular the result is not `1` when `n` has such a prime factor. -/
theorem pollardPMinusOne_ne_one {n p B c : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n)
    (hpc : ¬p ∣ c) (hsmooth : ∀ q e : ℕ, q.Prime → q ^ e ∣ p - 1 → q ^ e ≤ B) :
    pollardPMinusOne n B c ≠ 1 := fun h ↦ by
  have := dvd_pollardPMinusOne hp hpn hn hpc (sub_one_dvd_pm1Exponent hsmooth)
  rw [h] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

end PrimeNumbers.Chapter5
