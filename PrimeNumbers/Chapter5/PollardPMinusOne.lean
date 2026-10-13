import PrimeNumbers.Chapter9.BitCost
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

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Bit operations -/

/-- The bit operations of `ladder n p c j`: `j` modular powers with exponent `p`. -/
def ladderCost (C : CostModel) (n p : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => powModCost C c p n + ladderCost C n p (powMod c p n) j

/-- The bit operations of the power ladders over a list of primes. -/
def laddersCost (C : CostModel) (n B : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: L, c =>
    ladderCost C n p c (Nat.log p B) + laddersCost C n B L (ladder n p c (Nat.log p B))

/-- The bit operations of `pollardPMinusOne n B c` (steps 2 and 3). -/
def pm1Cost (C : CostModel) (n B c : ℕ) : ℕ :=
  laddersCost C n B (primesUpTo B) c + euclidBitCost C n ((ladders n B c + n - 1) % n)

/-- The number of modular powers in step 2: `∑_{p ≤ B} a_p`. -/
def pm1Steps (B : ℕ) : ℕ := ((primesUpTo B).map fun p ↦ Nat.log p B).sum

/-- `pm1Steps B ≤ π(B) · log₂ B`. -/
theorem pm1Steps_le (B : ℕ) : pm1Steps B ≤ (primesUpTo B).length * Nat.log 2 B := by
  have := List.sum_le_length_nsmul ((primesUpTo B).map fun p ↦ Nat.log p B) (Nat.log 2 B)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact Nat.log_anti_left (by norm_num) (mem_primesUpTo.mp hp).1.two_le)
  simpa [pm1Steps] using this

theorem ladder_lt {n p c : ℕ} (hc : c < n) (j : ℕ) : ladder n p c j < n := by
  induction j generalizing c with
  | zero => exact hc
  | succ j ih => exact ih (powMod_lt _ _ (by omega))

section

variable (C : CostModel) {n B : ℕ}

/-- The cost of one modular power with exponent at most `B`. -/
def powBound (C : CostModel) (n B : ℕ) : ℕ :=
  C.divMod n.size n.size + Nat.log 2 B * (2 * C.mulMod n.size)

theorem ladderCost_le {p c : ℕ} (hp : p ≤ B) (hc : c < n) (j : ℕ) :
    ladderCost C n p c j ≤ j * powBound C n B := by
  induction j generalizing c with
  | zero => simp [ladderCost]
  | succ j ih =>
    have h₁ : powModCost C c p n ≤ powBound C n B :=
      (powModCost_le C hc p).trans (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.log_mono_right hp)) _)
    have ih := ih (c := powMod c p n) (powMod_lt _ _ (by omega))
    simp only [ladderCost, add_mul, one_mul]
    omega

theorem laddersCost_le (L : List ℕ) (hL : ∀ p ∈ L, p ≤ B) {c : ℕ} (hc : c < n) :
    laddersCost C n B L c ≤ (L.map fun p ↦ Nat.log p B).sum * powBound C n B := by
  induction L generalizing c with
  | nil => simp [laddersCost]
  | cons p L ih =>
    have h₁ := ladderCost_le C (hL p (by simp)) hc (Nat.log p B)
    have ih := ih (fun q hq ↦ hL q (by simp [hq])) (ladder_lt (p := p) hc (Nat.log p B))
    simp only [laddersCost, List.map_cons, List.sum_cons, add_mul]
    omega

/-- **Bit complexity of Pollard `p - 1`**, for any cost model: `pm1Steps B` modular powers
with exponents at most `B`, and one gcd with `n` (bounded by `G`). -/
theorem pm1Cost_le {G c : ℕ} (hG : ∀ d < n, euclidBitCost C n d ≤ G) (hc : c < n) :
    pm1Cost C n B c ≤ pm1Steps B * powBound C n B + G := by
  have h₁ := laddersCost_le C (primesUpTo B) (fun p hp ↦ (mem_primesUpTo.mp hp).2) hc
  have h₂ := hG _ (Nat.mod_lt (ladders n B c + n - 1) (by omega : 0 < n))
  simp only [pm1Cost, pm1Steps]
  omega

end

/-- **Bit complexity of Pollard `p - 1`, grammar-school arithmetic**: at most
`pm1Steps B · (4 log₂ B + 1)(k + 1)² + k(3k + 1)` bit operations. -/
theorem pm1Cost_school_le {n B c : ℕ} (hc : c < n) :
    pm1Cost school n B c ≤
      pm1Steps B * ((4 * Nat.log 2 B + 1) * (n.size + 1) ^ 2) + n.size * (3 * n.size + 1) := by
  refine (pm1Cost_le school (fun d hd ↦ euclidBitCost_school_le' hd le_rfl) hc).trans ?_
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
  rw [powBound, school_mulMod]
  have : school.divMod n.size n.size = n.size := by simp [school]
  rw [this]
  nlinarith [Nat.zero_le (Nat.log 2 B), Nat.zero_le n.size,
    Nat.zero_le (Nat.log 2 B * n.size)]

end RunningTime

end PrimeNumbers.Chapter5
