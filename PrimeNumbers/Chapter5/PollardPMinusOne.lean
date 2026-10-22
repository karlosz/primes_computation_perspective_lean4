import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter3.Sieve
import Mathlib.Data.Nat.Size
import Mathlib.FieldTheory.Finite.Basic

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
counted_def primesUpTo (B : ℕ) : List ℕ := sievePrimes B

theorem primesUpTo_cost (C : Chapter9.CostModel) (B : ℕ) :
    costOf C (primesUpTo B) = C.unit + costOf C (sievePrimes B) := by
  cost_unfold primesUpTo.counted

theorem mem_primesUpTo {B q : ℕ} : q ∈ primesUpTo B ↔ q.Prime ∧ q ≤ B := mem_sievePrimes

/-- The exponent `M(B) = ∏_{p ≤ B} p^(a_p)`, where `a_p = ⌊log_p B⌋` is the maximum integer
with `p^(a_p) ≤ B`.  This is `lcm(1, …, B)`. -/
counted_def pm1Exponent (B : ℕ) : ℕ :=
  ((primesUpTo B).map fun p ↦ p ^ Nat.log p B).prod

/-- The inner loop of step 2: `for (1 ≤ j ≤ a) c = c^p mod n`. -/
counted_def ladder (n p : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => c
  | j + 1 => ladder n p (powMod c p n) j

/-- **Algorithm 5.4.1, step 2 [Perform power ladders]**:
```
for (1 ≤ i ≤ m) { for (1 ≤ j ≤ aᵢ) c = c^(pᵢ) mod n; }
```
-/
counted_def ladders (n B c : ℕ) : ℕ :=
  (primesUpTo B).foldl (fun c p ↦ ladder n p c (Nat.log p B)) c

/-- **Algorithm 5.4.1 (Basic Pollard `p - 1` method).**  Given a composite odd `n` and a
search bound `B`, attempts to find a nontrivial factor of `n`, starting from `c` (the
book takes `c = 2`).
```
3. [Test gcd]   g = gcd(c - 1, n);   return g;      // We hope for a success 1 < g < n.
```
-/
counted_def pollardPMinusOne (n B : ℕ) (c : ℕ := 2) : ℕ :=
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

/-! ## The second stage

"After searching through the exponents `M(1), …, M(B)`, we next search through the
exponents `Q M(B)`, where `Q` runs over the primes in the interval `(B, B']`.  This then
has the chance of uncovering those primes `p ∣ n` with `p - 1 = Q u`, where `Q` is a prime
in `(B, B']` and `u ∣ M(B)`." -/

/-- Traverse the exponents `Q M(B)`: with `c₁ = c^(M(B)) mod n` and `h = c₁^(prevQ) mod n`,
pass to `c₁^Q` by multiplying with `c₁^(Q - prevQ)` ("the differences `Q_{i+1} - Q_i` are
all much smaller than the `Q_i`'s"), and accumulate `P = ∏ (c₁^Q - 1) mod n`. -/
counted_def stage2Loop (n c₁ : ℕ) : (prevQ h P : ℕ) → List ℕ → ℕ
  | _, _, P, [] => P
  | prevQ, h, P, Q :: Qs =>
    let h' := h * powMod c₁ (Q - prevQ) n % n
    stage2Loop n c₁ Q h' (P * (h' + n - 1) % n) Qs

/-- The primes `Q` with `B < Q ≤ B'`. -/
counted_def stage2Primes (B B' : ℕ) : List ℕ := (primesUpTo B').filter (B < ·)

/-- **The second stage of the Pollard `p - 1` method**: `gcd(∏_Q (c^(Q M(B)) - 1), n)` over
the primes `Q ∈ (B, B']`. -/
counted_def pollardStage2 (n B B' : ℕ) (c : ℕ := 2) : ℕ :=
  euclid n (stage2Loop n (ladders n B c % n) 0 (1 % n) (1 % n) (stage2Primes B B'))

theorem pollardStage2_dvd (n B B' c : ℕ) : pollardStage2 n B B' c ∣ n := by
  rw [pollardStage2, euclid_eq_gcd]
  exact Nat.gcd_dvd_left _ _

theorem mem_stage2Primes {B B' Q : ℕ} : Q ∈ stage2Primes B B' ↔ Q.Prime ∧ B < Q ∧ Q ≤ B' := by
  simp only [stage2Primes, List.mem_filter, mem_primesUpTo, decide_eq_true_iff]
  tauto

theorem stage2Primes_sorted (B B' : ℕ) : (stage2Primes B B').Pairwise (· ≤ ·) := by
  have h : (List.range (B' + 1)).Pairwise (· ≤ ·) := List.pairwise_le_range
  exact (h.filter _).filter _

/-- Loop invariant of the second stage: `h ≡ c₁^(prevQ)`, and once some factor
`c₁^Q - 1` is divisible by `p`, so is the accumulated product. -/
theorem dvd_stage2Loop {n p c₁ : ℕ} (hp : 1 < p) (hpn : p ∣ n) (hn : 0 < n) (prevQ h P : ℕ)
    (Qs : List ℕ) (hh : h % n = c₁ ^ prevQ % n) (hsorted : (prevQ :: Qs).Pairwise (· ≤ ·))
    (hw : p ∣ P ∨ ∃ Q ∈ Qs, c₁ ^ Q % p = 1) : p ∣ stage2Loop n c₁ prevQ h P Qs := by
  induction Qs generalizing prevQ h P with
  | nil =>
    rcases hw with hP | ⟨Q, hQ, -⟩
    · exact hP
    · simp at hQ
  | cons Q Qs ih =>
    rw [List.pairwise_cons] at hsorted
    have hle : prevQ ≤ Q := hsorted.1 Q (by simp)
    -- the new `h'` is `c₁^Q mod n`
    have hh' : h * powMod c₁ (Q - prevQ) n % n % n = c₁ ^ Q % n := by
      rw [Nat.mod_mod, Nat.mul_mod, hh, powMod_eq, Nat.mod_mod, ← Nat.mul_mod, ← pow_add,
        Nat.add_sub_cancel' hle]
    refine ih Q _ _ hh' hsorted.2 ?_
    rcases hw with hP | ⟨Q', hQ', hone⟩
    · exact Or.inl ((Nat.dvd_mod_iff hpn).mpr (Dvd.dvd.mul_right hP _))
    · rcases List.mem_cons.mp hQ' with rfl | htail
      · -- this factor `h' - 1` is divisible by `p`
        left
        rw [Nat.dvd_mod_iff hpn]
        refine Dvd.dvd.mul_left ?_ _
        have hmodp : h * powMod c₁ (Q' - prevQ) n % n % p = 1 := by
          have := congrArg (· % p) hh'
          simp only [Nat.mod_mod_of_dvd _ hpn, Nat.mod_mod] at this
          rw [Nat.mod_mod_of_dvd _ hpn, this, hone]
        set h' := h * powMod c₁ (Q' - prevQ) n % n with hh'def
        have h1 : 1 ≤ h' := by
          rcases Nat.eq_zero_or_pos h' with h0 | hpos
          · rw [h0, Nat.zero_mod] at hmodp; omega
          · exact hpos
        have hdvd : p ∣ h' - 1 :=
          (Nat.modEq_iff_dvd' h1).mp (by rw [Nat.ModEq, hmodp, Nat.mod_eq_of_lt hp])
        rw [show h' + n - 1 = h' - 1 + n by omega]
        exact Dvd.dvd.add hdvd hpn
      · exact Or.inr ⟨Q', htail, hone⟩

/-- **Why the second stage works.**  If `p` is a prime factor of `n` not dividing `c`, and
`p - 1 ∣ Q · M(B)` for some prime `Q ∈ (B, B']` — in particular if `p - 1 = Q u` with
`u ∣ M(B)` — then `p` divides the result of the second stage. -/
theorem dvd_pollardStage2 {n p B B' c Q : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n)
    (hpc : ¬p ∣ c) (hQ : Q.Prime) (hBQ : B < Q) (hQB : Q ≤ B')
    (hM : p - 1 ∣ Q * pm1Exponent B) : p ∣ pollardStage2 n B B' c := by
  have : Fact p.Prime := ⟨hp⟩
  have hc0 : (c : ZMod p) ≠ 0 := fun h ↦ hpc ((ZMod.natCast_eq_zero_iff c p).mp h)
  -- `c₁^Q ≡ c^(Q M) ≡ 1 (mod p)`
  have hone : (ladders n B c % n) ^ Q % p = 1 := by
    have hz : (((ladders n B c % n) ^ Q : ℕ) : ZMod p) = 1 := by
      have key : ((ladders n B c % n : ℕ) : ZMod p) = (c : ZMod p) ^ pm1Exponent B := by
        have h₂ : ∀ x : ℕ, ((x % n : ℕ) : ZMod p) = (x : ZMod p) := fun x ↦ by
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hpn]
        rw [ladder_eq, h₂, Nat.cast_pow]
      obtain ⟨e, he⟩ := hM
      rw [Nat.cast_pow, key, ← pow_mul, mul_comm, he, pow_mul,
        ZMod.pow_card_sub_one_eq_one hc0, one_pow]
    have := (ZMod.natCast_eq_natCast_iff' ((ladders n B c % n) ^ Q) 1 p).mp
      (by rw [hz, Nat.cast_one])
    rwa [Nat.mod_eq_of_lt hp.one_lt] at this
  rw [pollardStage2, euclid_eq_gcd]
  refine Nat.dvd_gcd hpn (dvd_stage2Loop hp.one_lt hpn hn 0 _ _ _ (by simp) ?_
    (Or.inr ⟨Q, mem_stage2Primes.mpr ⟨hQ, hBQ, hQB⟩, hone⟩))
  exact List.pairwise_cons.mpr ⟨fun _ _ ↦ Nat.zero_le _, stage2Primes_sorted B B'⟩

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Bit operations -/

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

@[val_le] theorem ladder_lt {n p c : ℕ} (hc : c < n) (j : ℕ) : ladder n p c j < n := by
  induction j generalizing c with
  | zero => exact hc
  | succ j ih => exact ih (powMod_lt _ _ (by omega))

@[val_le] theorem ladders_lt {n B c : ℕ} (hc : c < n) : ladders n B c < n := by
  rw [ladders]
  generalize primesUpTo B = L
  induction L generalizing c with
  | nil => exact hc
  | cons p L ih => exact ih (ladder_lt hc _)

section

variable (C : CostModel) {n B : ℕ}

/-- The cost of one modular power with exponent at most `B` (`powModCost_le`), and a step. -/
def powBound (C : CostModel) (n B : ℕ) : ℕ :=
  C.divMod n.size n.size + Nat.log 2 B * (2 * C.mulMod n.size) +
    (Nat.log 2 B + 2) * 6 * C.lin (B.size + 2)

theorem powMod_cost_le_powBound {c p : ℕ} (hp : p ≤ B) (hc : c < n) :
    costOf C (powMod c p n) + C.unit ≤ powBound C n B := by
  have h := powModCost_le C hc (k := B.size) p (Nat.size_le_size hp)
  have := Nat.log_mono_right (b := 2) hp
  have h₁ := Nat.mul_le_mul_right (2 * C.mulMod n.size) this
  have h₂ := Nat.mul_le_mul_right (6 * C.lin (B.size + 2)) (show Nat.log 2 p + 1 ≤ Nat.log 2 B + 1
    by omega)
  have h₃ := C.unit_le_lin (B.size + 2)
  unfold powBound
  nlinarith

@[cost_le] theorem ladderCost_le {p c : ℕ} (hp : p ≤ B) (hc : c < n) (j : ℕ) :
    costOf C (ladder n p c j) ≤ j * powBound C n B + C.unit := by
  induction j generalizing c with
  | zero => cost_unfold ladder.counted
  | succ j ih =>
    have h₁ := powMod_cost_le_powBound C hp hc
    have ih := ih (c := powMod c p n) (powMod_lt _ _ (by omega))
    cost_unfold ladder.counted
    rw [add_mul, one_mul]
    omega

/-- The cost of an exponent `a_p = ⌊log_p B⌋` (`ilog_cost_le`). -/
def logBound (C : CostModel) (B : ℕ) : ℕ :=
  (B.size + 2) * (C.mul B.size B.size + C.divBound B.size + 4 * C.lin (B.size + 1))

/-- **Bit complexity of step 2 of Pollard `p - 1`**, for any cost model: the sieve for the
primes `p ≤ B`; for each, the exponent `a_p = ⌊log_p B⌋` (`logBound`) and two steps; and
`pm1Steps B` modular powers with exponents at most `B`. -/
@[cost_le] theorem laddersCost_le {c : ℕ} (hc : c < n) :
    costOf C (ladders n B c) ≤ costOf C (primesUpTo B) +
      ((primesUpTo B).length * (logBound C B + 2 * C.unit) + pm1Steps B * powBound C n B) +
        2 * C.unit := by
  cost_unfold ladders.counted
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (CostM.foldl_cost_le C (· < n)
    (fun p ↦ logBound C B + Nat.log p B * powBound C n B + C.unit)
    (fun a p ha ↦ ladder_lt ha _) _ (fun a p ha hp ↦ ?_) hc) _) _) ?_
  · have hp' := mem_primesUpTo.mp hp
    have h₁ := ilog_cost_le C (n := B) hp'.1.two_le
    have h₂ := ladderCost_le C hp'.2 ha (Nat.log p B)
    unfold logBound
    cost_simp
    omega
  · have e : ((primesUpTo B).map fun p ↦ logBound C B + Nat.log p B * powBound C n B +
        C.unit).sum = (primesUpTo B).length * (logBound C B + C.unit) +
          pm1Steps B * powBound C n B := by
      simp [pm1Steps, List.sum_map_add, List.sum_map_mul_right]; ring
    rw [e]
    nlinarith

/-- **Bit complexity of Pollard `p - 1`**, for any cost model: step 2 (`laddersCost_le`), the
reduction of `c - 1` modulo `n` and one gcd with `n`. -/
@[cost_le] theorem pm1Cost_le {c : ℕ} (hc : c < n) :
    costOf C (pollardPMinusOne n B c) ≤ costOf C (primesUpTo B) +
      ((primesUpTo B).length * (logBound C B + 2 * C.unit) + pm1Steps B * powBound C n B) +
      C.divMod (n.size + 1) n.size + gcdCost C n.size + 5 * C.lin (n.size + 1) := by
  cost_unfold pollardPMinusOne.counted
  cost_bound

end

/-- **Bit complexity of Pollard `p - 1`, grammar-school arithmetic**: with `k` the bit length
of `n` and `K` that of `B`, the sieve (`sieve_cost_le`, `sievePrimes_cost_le`), for each
prime `p ≤ B` the exponent `a_p` (`logBound`, `O(K³)`), `pm1Steps B` modular powers of
at most `(4 log₂ B + 1)(k + 1)² + 6(log₂ B + 2)(K + 4)` bit operations each, and the gcd. -/
@[cost_le] theorem pm1Cost_school_le {n B c : ℕ} (hc : c < n) :
    costOf school (pollardPMinusOne n B c) ≤
      (3 * (B + 6 + costOf writeCount (sieveLoop B 2 (sieveInit B))) + 4 * (B + 2)) *
          (B.size + 4) + (2 * B + 1) * ((B + 2).size * (B + 2).size) + 1 +
      ((primesUpTo B).length * (logBound school B + 2) +
        pm1Steps B * ((4 * Nat.log 2 B + 1) * (n.size + 1) ^ 2 +
          6 * (Nat.log 2 B + 2) * (B.size + 4))) +
      n.size * (3 * n.size + 6) + 7 * n.size + 21 := by
  have h := pm1Cost_le school (B := B) hc
  have hg := gcdCost_school_le n.size
  have hs := sieve_cost_le school B
  have hs' := sievePrimes_cost_le school B
  have hp := primesUpTo_cost school B
  have hpow : powBound school n B ≤ (4 * Nat.log 2 B + 1) * (n.size + 1) ^ 2 +
      6 * (Nat.log 2 B + 2) * (B.size + 4) := by
    rw [powBound, school_mulMod, school_divMod_self, school_lin]
    nlinarith [Nat.zero_le (Nat.log 2 B), Nat.zero_le n.size,
      Nat.zero_le (Nat.log 2 B * n.size)]
  have hdiv : school.divMod (n.size + 1) n.size = 2 * n.size := by
    rw [school_divMod, show n.size + 1 - n.size + 1 = 2 by omega]
  rw [hdiv, school_lin, school_unit] at h
  rw [school_mul, school_lin] at hs
  rw [school_lin] at hs'
  rw [school_unit] at hp
  have := Nat.mul_le_mul_left (pm1Steps B) hpow
  linarith

/-! ### Second stage: bit operations -/

/-- **Bit complexity of the second stage**, for any cost model: per prime `Q ∈ (B, B']`
one modular power with exponent at most `B'` (in practice the small difference
`Q - prevQ`), two modular multiplications and four linear operations. -/
@[cost_le] theorem stage2Cost_le (C : CostModel) {n c₁ B' : ℕ} (hc : c₁ < n) (prevQ h P : ℕ)
    (Qs : List ℕ) (hh : h < n) (hP : P < n) (hprev : prevQ ≤ B') (hQs : ∀ Q ∈ Qs, Q ≤ B') :
    costOf C (stage2Loop n c₁ prevQ h P Qs) ≤
      Qs.length * (powBound C n B' + C.mulMod n.size +
        (C.mul n.size (n.size + 1) + C.divMod (2 * n.size + 1) n.size) +
        4 * C.lin (n.size + B'.size + 1)) + C.unit := by
  have hn : 0 < n := by omega
  induction Qs generalizing prevQ h P with
  | nil => cost_unfold stage2Loop.counted
  | cons Q Qs ih =>
    have hQ : Q ≤ B' := hQs Q (by simp)
    have h₁ := powMod_cost_le_powBound C (n := n) (B := B') (c := c₁) (p := Q - prevQ)
      (by omega) hc
    have hh' : h * powMod c₁ (Q - prevQ) n % n < n := Nat.mod_lt _ hn
    -- `h' + n - 1 < 2n` has at most `k + 1` bits
    have hsz' : (h * powMod c₁ (Q - prevQ) n % n + n).size ≤ n.size + 1 := by
      rw [Nat.size_le, pow_succ]
      have := Nat.lt_size_self n
      omega
    have ih := ih Q (h * powMod c₁ (Q - prevQ) n % n)
      (P * (h * powMod c₁ (Q - prevQ) n % n + n - 1) % n) hh' (Nat.mod_lt _ hn) hQ
      (fun Q' hQ' ↦ hQs Q' (by simp [hQ']))
    cost_unfold stage2Loop.counted
    cost_bound

/-- **Bit complexity of the second stage, grammar-school arithmetic**: at most
`(4 log₂ B' + 5)(k + 1)² + 6(log₂ B' + 2)(K' + 4) + 4(k + K' + 3)` bit operations per prime
`Q ∈ (B, B']`, `K'` the bit length of `B'`. -/
@[cost_le] theorem stage2Cost_school_le {n c₁ B' : ℕ} (hc : c₁ < n) (prevQ h P : ℕ) (Qs : List ℕ)
    (hh : h < n) (hP : P < n) (hprev : prevQ ≤ B') (hQs : ∀ Q ∈ Qs, Q ≤ B') :
    costOf school (stage2Loop n c₁ prevQ h P Qs) ≤
      Qs.length * ((4 * Nat.log 2 B' + 5) * (n.size + 1) ^ 2 +
        6 * (Nat.log 2 B' + 2) * (B'.size + 4) + 4 * (n.size + B'.size + 3)) + 1 := by
  refine (stage2Cost_le school hc prevQ h P Qs hh hP hprev hQs).trans
    (Nat.add_le_add (Nat.mul_le_mul_left _ ?_) le_rfl)
  have h₁ : school.divMod n.size n.size = n.size := by simp [school]
  have h₂ : school.divMod (2 * n.size + 1) n.size = (n.size + 2) * n.size := by
    change (2 * n.size + 1 - n.size + 1) * n.size = _
    rw [show 2 * n.size + 1 - n.size + 1 = n.size + 2 by omega]
  have h₃ : school.mul n.size (n.size + 1) = n.size * (n.size + 1) := rfl
  rw [powBound, school_mulMod, h₁, h₂, h₃, school_lin, school_lin]
  nlinarith [Nat.zero_le (Nat.log 2 B'), Nat.zero_le n.size,
    Nat.zero_le (Nat.log 2 B' * n.size)]

end RunningTime

end PrimeNumbers.Chapter5
