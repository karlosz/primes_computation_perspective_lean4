import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Assumed
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Data.Nat.Size
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting

/-!
# §3.2 Sieving: the sieve of Eratosthenes

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 3.2.1.

* `sieve N`        — the sieve of Eratosthenes on a Boolean array indexed `0 … N`: for each
                     `p` with `p² ≤ N` whose bit is still set, clear the bits of
                     `p², p² + p, p² + 2p, …`.  No division is performed.
* `sieve_spec`     — bit `i` of `sieve N` is set exactly when `i ≤ N` is prime.
* `sievePrimes N`  — the list of primes up to `N`; `mem_sievePrimes`.

This is the basic sieve described at the start of §3.2.1.  The book's Algorithm 3.2.1
(the same sieve run on odd numbers only, in blocks of `B`, over an interval `(L, R)`) and
Algorithm 3.2.2 (the "fancy" sieve with a wheel) are refinements of the memory layout of
this procedure and are not formalized.
-/

namespace PrimeNumbers.Chapter3

/-- Bit `i` of a Boolean array (`false` outside the array). -/
counted_def bit (bits : Array Bool) (i : ℕ) : Bool := bits.getD i false

theorem bit_eq_false_of_size_le {bits : Array Bool} {i : ℕ} (h : bits.size ≤ i) :
    bit bits i = false := by
  simp [bit, Array.getD, Nat.not_lt.mpr h]

theorem bit_setIfInBounds (bits : Array Bool) (j i : ℕ) (v : Bool) :
    bit (bits.setIfInBounds j v) i = if i = j ∧ j < bits.size then v else bit bits i := by
  simp only [bit, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hij : j = i
  · subst hij
    by_cases hj : j < bits.size <;> simp [hj]
  · have : ¬i = j := fun h ↦ hij h.symm
    simp [hij, this]

/-- Clear the bits `j, j + p, j + 2p, …`. -/
counted_def markMultiples (p : ℕ) (bits : Array Bool) (j : ℕ) : Array Bool :=
  if j < bits.size ∧ 0 < p then markMultiples p (bits.setIfInBounds j false) (j + p) else bits
termination_by bits.size - j
decreasing_by simp only [Array.size_setIfInBounds]; omega

theorem markMultiples_spec (p : ℕ) (bits : Array Bool) (j : ℕ) (hp : 0 < p) :
    (markMultiples p bits j).size = bits.size ∧
      ∀ i, bit (markMultiples p bits j) i = true ↔
        bit bits i = true ∧ ¬(j ≤ i ∧ p ∣ i - j) := by
  fun_induction markMultiples p bits j with
  | case1 bits j h ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    refine ⟨by rw [ih₁, Array.size_setIfInBounds], fun i ↦ ?_⟩
    rw [ih₂, bit_setIfInBounds]
    by_cases hij : i = j
    · subst hij; simp [h.1]
    · -- for `i ≠ j`: `i` is among `j + p, j + 2p, …` iff it is among `j, j + p, …`
      have key : (j + p ≤ i ∧ p ∣ i - (j + p)) ↔ (j ≤ i ∧ p ∣ i - j) := by
        constructor
        · rintro ⟨h₁, h₂⟩
          refine ⟨by omega, ?_⟩
          have : i - j = i - (j + p) + p := by omega
          rw [this]; exact Dvd.dvd.add h₂ dvd_rfl
        · rintro ⟨h₁, h₂⟩
          have hpos : 0 < i - j := by omega
          have hle := Nat.le_of_dvd hpos h₂
          refine ⟨by omega, ?_⟩
          have : i - (j + p) = i - j - p := by omega
          rw [this]; exact Nat.dvd_sub h₂ dvd_rfl
      simp [hij, key]
  | case2 bits j h =>
    refine ⟨rfl, fun i ↦ ⟨fun hi ↦ ⟨hi, fun hji ↦ ?_⟩, fun hi ↦ hi.1⟩⟩
    have : bits.size ≤ i := by
      by_contra hlt
      exact h ⟨by omega, hp⟩
    rw [bit_eq_false_of_size_le this] at hi
    exact absurd hi (by simp)

/-- The main loop of the sieve: for `p = 2, 3, …` while `p² ≤ N`, if `p` is still marked
prime, clear its multiples starting at `p²`. -/
counted_def sieveLoop (N p : ℕ) (bits : Array Bool) : Array Bool :=
  if p * p ≤ N ∧ 0 < p then
    sieveLoop N (p + 1) (if bit bits p then markMultiples p bits (p * p) else bits)
  else bits
termination_by N + 1 - p
decreasing_by
  have : p ≤ p * p := Nat.le_mul_self p
  omega

/-- The initial array: `N + 1` entries, all marked except `0` and `1`. -/
counted_def sieveInit (N : ℕ) : Array Bool :=
  ((Array.replicate (N + 1) true).setIfInBounds 0 false).setIfInBounds 1 false

/-- **The sieve of Eratosthenes**: a Boolean array of length `N + 1` whose `i`-th entry
tells whether `i` is prime. -/
counted_def sieve (N : ℕ) : Array Bool :=
  sieveLoop N 2 (sieveInit N)

/-- The primes up to `N`, read off the sieve. -/
counted_def sievePrimes (N : ℕ) : List ℕ :=
  let bits := sieve N        -- computed once
  (List.range (N + 1)).filter fun i ↦ bit bits i

/-- The state of the sieve when it is about to process `p`: bit `i` is set iff
`2 ≤ i ≤ N` and `i` has not been struck out by a prime `q < p` (that is, no prime `q < p`
has `q ∣ i` and `q² ≤ i`). -/
def SieveInv (N p : ℕ) (bits : Array Bool) : Prop :=
  ∀ i, bit bits i = true ↔
    2 ≤ i ∧ i ≤ N ∧ ¬∃ q : ℕ, q.Prime ∧ q < p ∧ q ∣ i ∧ q * q ≤ i

/-- A number `i ≥ 2` with no prime factor `q` satisfying `q² ≤ i` is prime. -/
theorem prime_of_forall_not {i : ℕ} (hi : 2 ≤ i)
    (h : ¬∃ q : ℕ, q.Prime ∧ q ∣ i ∧ q * q ≤ i) : i.Prime := by
  by_contra hnp
  refine h ⟨i.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd i, ?_⟩
  have := Nat.minFac_sq_le_self (by omega) hnp
  rwa [sq] at this

/-- When the sieve reaches `p`, the bit of `p` is set iff `p` is prime. -/
theorem SieveInv.bit_iff_prime {N p : ℕ} {bits : Array Bool} (hinv : SieveInv N p bits)
    (hp : 2 ≤ p) (hpN : p ≤ N) : bit bits p = true ↔ p.Prime := by
  rw [hinv p]
  constructor
  · rintro ⟨-, -, h⟩
    exact prime_of_forall_not hp fun ⟨q, hq, hqp, hqq⟩ ↦
      h ⟨q, hq, (by
        have := Nat.le_of_dvd (by omega) hqp
        rcases Nat.lt_or_ge q p with h | h
        · exact h
        · obtain rfl : q = p := by omega
          have : q * 2 ≤ q * q := Nat.mul_le_mul_left q hp
          omega), hqp, hqq⟩
  · intro hpp
    refine ⟨hp, hpN, fun ⟨q, hq, hqlt, hqp, _⟩ ↦ ?_⟩
    have := (Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp
    omega

/-- One pass of the main loop preserves the invariant. -/
theorem SieveInv.step {N p : ℕ} {bits : Array Bool} (hinv : SieveInv N p bits) (hp : 2 ≤ p)
    (hle : p * p ≤ N) :
    SieveInv N (p + 1) (if bit bits p then markMultiples p bits (p * p) else bits) := by
  have hpN : p ≤ N := (Nat.le_mul_self p).trans hle
  have hbit := hinv.bit_iff_prime hp hpN
  intro i
  -- extending "struck out by a prime `< p`" to "`< p + 1`"
  have hext : (∃ q : ℕ, q.Prime ∧ q < p + 1 ∧ q ∣ i ∧ q * q ≤ i) ↔
      (∃ q : ℕ, q.Prime ∧ q < p ∧ q ∣ i ∧ q * q ≤ i) ∨ (p.Prime ∧ p ∣ i ∧ p * p ≤ i) := by
    constructor
    · rintro ⟨q, hq, hlt, h₁, h₂⟩
      rcases Nat.lt_or_ge q p with h | h
      · exact Or.inl ⟨q, hq, h, h₁, h₂⟩
      · obtain rfl : q = p := by omega
        exact Or.inr ⟨hq, h₁, h₂⟩
    · rintro (⟨q, hq, hlt, h₁, h₂⟩ | ⟨hq, h₁, h₂⟩)
      · exact ⟨q, hq, by omega, h₁, h₂⟩
      · exact ⟨p, hq, by omega, h₁, h₂⟩
  rw [hext]
  split_ifs with hb
  · have hpp := hbit.mp hb
    rw [(markMultiples_spec p bits (p * p) (by omega)).2, hinv i]
    have hmul : (p * p ≤ i ∧ p ∣ i - p * p) ↔ (p.Prime ∧ p ∣ i ∧ p * p ≤ i) := by
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨hpp, ?_, h₁⟩
        have : i = i - p * p + p * p := by omega
        rw [this]; exact Dvd.dvd.add h₂ (Dvd.intro _ rfl)
      · rintro ⟨-, h₁, h₂⟩
        exact ⟨h₂, Nat.dvd_sub h₁ (Dvd.intro _ rfl)⟩
    rw [hmul, not_or]
    constructor
    · rintro ⟨⟨a, b, c⟩, d⟩; exact ⟨a, b, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨⟨a, b, c⟩, d⟩
  · have hnp : ¬p.Prime := fun h ↦ hb (hbit.mpr h)
    rw [hinv i, not_or]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, b, c, fun h ↦ hnp h.1⟩
    · rintro ⟨a, b, c, _⟩; exact ⟨a, b, c⟩

theorem sieveLoop_spec (N p : ℕ) (bits : Array Bool) (hp : 2 ≤ p) (hinv : SieveInv N p bits) :
    ∀ i, bit (sieveLoop N p bits) i = true ↔ i ≤ N ∧ i.Prime := by
  fun_induction sieveLoop N p bits with
  | case1 p bits hle ih => exact ih (by omega) (hinv.step hp hle.1)
  | case2 p bits hgt =>
    intro i
    rw [hinv i]
    have hlt : N < p * p := by
      by_contra h
      exact hgt ⟨by omega, by omega⟩
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      refine ⟨h₂, prime_of_forall_not h₁ fun ⟨q, hq, hqi, hqq⟩ ↦ h₃ ⟨q, hq, ?_, hqi, hqq⟩⟩
      by_contra hge
      have : p * p ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      omega
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₂.two_le, h₁, fun ⟨q, hq, _, hqi, hqq⟩ ↦ ?_⟩
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq h₂).mp hqi
      have : q * 2 ≤ q * q := Nat.mul_le_mul_left q hq.two_le
      have := hq.two_le
      omega

/-- The initial array (all of `2 … N` marked) satisfies the invariant for `p = 2`. -/
theorem sieveInv_init (N : ℕ) : SieveInv N 2 (sieveInit N) := by
  intro i
  unfold sieveInit
  rw [bit_setIfInBounds, bit_setIfInBounds]
  have hno : ¬∃ q : ℕ, q.Prime ∧ q < 2 ∧ q ∣ i ∧ q * q ≤ i := fun ⟨q, hq, h, _⟩ ↦ by
    have := hq.two_le
    omega
  have hrep : bit (Array.replicate (N + 1) true) i = true ↔ i ≤ N := by
    by_cases hi : i ≤ N
    · simp [bit, Array.getD, show i < N + 1 by omega, hi]
    · simp [bit_eq_false_of_size_le (bits := Array.replicate (N + 1) true) (i := i)
        (by simp; omega), hi]
  simp only [Array.size_setIfInBounds, Array.size_replicate]
  split_ifs with h₁ h₀
  · simp; omega
  · simp; omega
  · rw [hrep]
    constructor
    · intro hi; exact ⟨by omega, hi, hno⟩
    · rintro ⟨-, hi, -⟩; exact hi

/-- **Correctness of the sieve of Eratosthenes**: bit `i` of `sieve N` is set exactly when
`i ≤ N` is prime. -/
theorem sieve_spec (N i : ℕ) : bit (sieve N) i = true ↔ i ≤ N ∧ i.Prime :=
  sieveLoop_spec N 2 _ le_rfl (sieveInv_init N) i

/-- `sievePrimes N` is the list of the primes `≤ N`. -/
theorem mem_sievePrimes {N q : ℕ} : q ∈ sievePrimes N ↔ q.Prime ∧ q ≤ N := by
  simp only [sievePrimes, List.mem_filter, List.mem_range, sieve_spec]
  constructor
  · rintro ⟨-, h₁, h₂⟩; exact ⟨h₂, h₁⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨by omega, h₂, h₁⟩

/-! ## Running time

The sieve's work is counted in steps — calls, array reads and writes — by the counting
model `writeCount`: striking out the multiples of `p` takes about `3 N / p` steps.  In a
general cost model each step costs at most a linear operation on numbers of `size N + 2`
bits, and the products `p · p` are charged as multiplications. -/

open PrimeNumbers.Chapter9

@[cost_simps] theorem bit_cost (C : CostModel) (bits : Array Bool) (i : ℕ) :
    costOf C (bit bits i) = 2 * C.unit := by
  cost_unfold bit.counted

/-! ### Steps -/

theorem markSteps_done {p : ℕ} {bits : Array Bool} {j : ℕ} (h : ¬(j < bits.size ∧ 0 < p)) :
    costOf writeCount (markMultiples p bits j) = 2 := by
  cost_unfold markMultiples.counted

/-- Striking out `j, j + p, …` below `size`: three steps for each of the at most
`⌈(size - j)/p⌉` multiples, and two to stop. -/
theorem markSteps_mul_le {p : ℕ} (hp : 0 < p) (bits : Array Bool) (j : ℕ) :
    costOf writeCount (markMultiples p bits j) * p ≤ 3 * (bits.size - j) + 5 * p := by
  fun_induction markMultiples p bits j with
  | case1 bits j h ih =>
    have e : costOf writeCount (markMultiples p bits j) =
        3 + costOf writeCount (markMultiples p (bits.setIfInBounds j false) (j + p)) := by
      cost_unfold markMultiples.counted
    rw [e, add_mul]
    rw [Array.size_setIfInBounds] at ih
    by_cases hlt : j + p < bits.size
    · omega
    · rw [markSteps_done (by rw [Array.size_setIfInBounds]; omega)]
      omega
  | case2 bits j h => rw [markSteps_done h]; omega

/-- For `p² ≤ N`, the sieve strikes out the multiples of `p` in at most `3 N/p + 8` steps. -/
@[cost_le] theorem markSteps_sq_le {N p : ℕ} (hp : 0 < p) (hpN : p * p ≤ N) {bits : Array Bool}
    (hsize : bits.size = N + 1) : costOf writeCount (markMultiples p bits (p * p)) ≤
      3 * (N / p) + 8 := by
  have h₁ := markSteps_mul_le hp bits (p * p)
  rw [hsize] at h₁
  have h₂ : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h₃ := Nat.lt_mul_div_succ N hp
  have h₄ : 3 * (N + 1 - p * p) ≤ 3 * N := by omega
  by_contra hc
  have : (3 * (N / p) + 9) * p ≤ costOf writeCount (markMultiples p bits (p * p)) * p :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- The steps of the main loop: at most `3 ⌊N/p⌋ + 11` for each `p ≤ √N`, and one to stop. -/
@[cost_le] theorem sieveLoopSteps_le (N p : ℕ) (bits : Array Bool) (hsize : bits.size = N + 1) :
    costOf writeCount (sieveLoop N p bits) ≤
      3 * ∑ q ∈ Finset.Ico p (Nat.sqrt N + 1), N / q + 11 * (Nat.sqrt N + 1 - p) + 1 := by
  fun_induction sieveLoop N p bits with
  | case1 p bits hle ih =>
    have hps : p ≤ Nat.sqrt N := Nat.le_sqrt.mpr hle.1
    have hsize' : (if bit bits p = true then markMultiples p bits (p * p) else bits).size =
        N + 1 := by
      split_ifs
      · rw [(markMultiples_spec p bits (p * p) hle.2).1, hsize]
      · exact hsize
    have ih := ih hsize'
    have hmark : (if bit bits p = true then costOf writeCount (markMultiples p bits (p * p))
        else 0) ≤ 3 * (N / p) + 8 := by
      split_ifs
      · exact markSteps_sq_le hle.2 hle.1 hsize
      · exact Nat.zero_le _
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : p < Nat.sqrt N + 1)]
    cost_unfold sieveLoop.counted
    simp only [dite_eq_ite] at ih
    split_ifs at hmark ih ⊢ <;> omega
  | case2 p bits hgt =>
    cost_unfold sieveLoop.counted

/-- Only primes strike out: the main loop takes at most `3 ⌊N/p⌋ + 11` steps for each prime
`p ≤ √N`, and `11` for each other `p ≤ √N`. -/
@[cost_le] theorem sieveLoopSteps_le_primes (N p : ℕ) (bits : Array Bool) (hsize : bits.size = N + 1)
    (hp : 2 ≤ p) (hinv : SieveInv N p bits) :
    costOf writeCount (sieveLoop N p bits) ≤
      3 * (∑ q ∈ Finset.Ico p (Nat.sqrt N + 1), if q.Prime then N / q else 0) +
        11 * (Nat.sqrt N + 1 - p) + 1 := by
  fun_induction sieveLoop N p bits with
  | case1 p bits hle ih =>
    have hps : p ≤ Nat.sqrt N := Nat.le_sqrt.mpr hle.1
    have hpN : p ≤ N := (Nat.le_mul_self p).trans hle.1
    have hbit := hinv.bit_iff_prime hp hpN
    have hsize' : (if bit bits p = true then markMultiples p bits (p * p) else bits).size =
        N + 1 := by
      split_ifs
      · rw [(markMultiples_spec p bits (p * p) hle.2).1, hsize]
      · exact hsize
    have ih := ih hsize' (by omega) (hinv.step hp hle.1)
    have hmark : (if bit bits p = true then costOf writeCount (markMultiples p bits (p * p))
        else 0) ≤ 3 * (if p.Prime then N / p else 0) + 8 := by
      split_ifs with h₁ h₂ h₂
      · exact markSteps_sq_le hle.2 hle.1 hsize
      · exact absurd (hbit.mp h₁) h₂
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : p < Nat.sqrt N + 1)]
    cost_unfold sieveLoop.counted
    simp only [dite_eq_ite] at ih
    split_ifs at hmark ih ⊢ <;> omega
  | case2 p bits hgt =>
    cost_unfold sieveLoop.counted

/-! ### Bit operations -/

theorem size_le_of_le_two_mul_add_two {x N : ℕ} (h : x ≤ 2 * N + 2) : x.size ≤ N.size + 2 := by
  refine Nat.size_le.mpr ?_
  have := Nat.lt_size_self N
  rw [pow_add]; omega

/-- Each step of `markMultiples` is at most one linear operation on `(size N + 2)`-bit
numbers. -/
@[cost_le] theorem markMultiples_cost_le (C : CostModel) {N p : ℕ} (bits : Array Bool) (j : ℕ)
    (hs : bits.size ≤ N + 1) (hp : p ≤ N + 1) (hj : j ≤ 2 * N + 2) :
    costOf C (markMultiples p bits j) ≤
      costOf writeCount (markMultiples p bits j) * C.lin (N.size + 2) := by
  fun_induction markMultiples p bits j with
  | case1 bits j h ih =>
    have ih := ih (by rw [Array.size_setIfInBounds]; exact hs) (by omega)
    have h₁ := size_le_of_le_two_mul_add_two hj
    have h₂ := size_le_of_le_two_mul_add_two (show p ≤ 2 * N + 2 by omega)
    have e : costOf writeCount (markMultiples p bits j) =
        3 + costOf writeCount (markMultiples p (bits.setIfInBounds j false) (j + p)) := by
      cost_unfold markMultiples.counted
    rw [e]
    cost_unfold markMultiples.counted
    cost_bound
  | case2 bits j h =>
    have h₁ := size_le_of_le_two_mul_add_two hj
    rw [markSteps_done h]
    cost_unfold markMultiples.counted
    split_ifs <;> cost_bound

/-- The bit operations of the main loop: three linear operations per step, and the
products `p · p` (the test `p² ≤ N` and the start `p²` of the multiples), `p ≤ N + 2`. -/
@[cost_le] theorem sieveLoop_cost_le (C : CostModel) (N p : ℕ) (bits : Array Bool) (hp : p ≤ N + 2)
    (hsize : bits.size = N + 1) :
    costOf C (sieveLoop N p bits) ≤ 3 * costOf writeCount (sieveLoop N p bits) * C.lin (N.size + 2) +
      (2 * (N + 2 - p) + 1) * C.mul (N + 2).size (N + 2).size := by
  have hM : ∀ p ≤ N + 2, C.mul p.size p.size ≤ C.mul (N + 2).size (N + 2).size := fun p hp ↦
    C.mul_mono (Nat.size_le_size hp) (Nat.size_le_size hp)
  fun_induction sieveLoop N p bits with
  | case1 p bits h ih =>
    have hpp : p ≤ N := (Nat.le_mul_self p).trans h.1
    have hsize' : (if bit bits p = true then markMultiples p bits (p * p) else bits).size =
        N + 1 := by
      split_ifs
      · rw [(markMultiples_spec p bits (p * p) h.2).1, hsize]
      · exact hsize
    have ih := ih (by omega) hsize'
    have hmk := markMultiples_cost_le C (N := N) (p := p) bits (p * p) (by omega) (by omega)
      (by omega)
    have e : costOf writeCount (sieveLoop N p bits) = 3 +
        ((if bit bits p = true then costOf writeCount (markMultiples p bits (p * p)) else 0) +
          costOf writeCount (sieveLoop N (p + 1)
            (if bit bits p = true then markMultiples p bits (p * p) else bits))) := by
      cost_unfold sieveLoop.counted
    rw [e, show 2 * (N + 2 - p) + 1 = (2 * (N + 2 - (p + 1)) + 1) + 2 by omega]
    cost_unfold sieveLoop.counted
    simp only [dite_eq_ite] at ih
    split_ifs at ih ⊢ <;> cost_bound
  | case2 p bits h =>
    have e : costOf writeCount (sieveLoop N p bits) = 1 := by
      cost_unfold sieveLoop.counted
    rw [e]
    cost_unfold sieveLoop.counted
    split_ifs <;> cost_bound

/-- **Bit operations of the sieve**: filling the array, the steps of the main loop, and at
most `2N + 1` products `p · p` of numbers `≤ N + 2`. -/
@[cost_le] theorem sieve_cost_le (C : CostModel) (N : ℕ) :
    costOf C (sieve N) ≤ 3 * (N + 6 + costOf writeCount (sieveLoop N 2 (sieveInit N))) *
      C.lin (N.size + 2) + (2 * N + 1) * C.mul (N + 2).size (N + 2).size := by
  have h := sieveLoop_cost_le C N 2 (sieveInit N) (by omega) (by simp [sieveInit])
  rw [show 2 * (N + 2 - 2) + 1 = 2 * N + 1 by omega] at h
  cost_unfold sieve.counted
  cost_unfold sieveInit.counted
  cost_bound

/-- Reading off the primes: a pass over the array. -/
@[cost_le] theorem sievePrimes_cost_le (C : CostModel) (N : ℕ) :
    costOf C (sievePrimes N) ≤ costOf C (sieve N) + 4 * (N + 2) * C.lin (N.size + 2) := by
  cost_unfold sievePrimes.counted
  simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  cost_bound

/-! ### The number of steps -/

/-- **Running time of the sieve of Eratosthenes**: at most `3 ∑_{p=2}^{⌊√N⌋} ⌊N/p⌋ +
11 √N + 1` steps (one term for each `p`, whether prime or not; over primes only the sum is
`∼ N ln ln N`, which needs Mertens' theorem 1.4.2). -/
@[cost_le] theorem sieveSteps_le (N : ℕ) :
    costOf writeCount (sieveLoop N 2 (sieveInit N)) ≤
      3 * ∑ i ∈ Finset.range (Nat.sqrt N - 1), N / (i + 2) + 11 * Nat.sqrt N + 1 := by
  have := sieveLoopSteps_le N 2 (sieveInit N) (by simp [sieveInit])
  rw [Finset.sum_Ico_eq_sum_range, show Nat.sqrt N + 1 - 2 = Nat.sqrt N - 1 by omega] at this
  simp only [add_comm 2] at this
  rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h | h <;> omega

/-- **Running time of the sieve, closed form**: at most `3 N ln √N + 11 √N + 1` steps, by
comparing with the harmonic series. -/
theorem sieveSteps_le_log (N : ℕ) :
    (costOf writeCount (sieveLoop N 2 (sieveInit N)) : ℝ) ≤
      3 * N * Real.log (Nat.sqrt N) + 11 * Nat.sqrt N + 1 := by
  have h₀ := sieveSteps_le N
  rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h0 | hpos
  · simp [h0] at h₀ ⊢
    exact_mod_cast h₀
  have h₁ : (costOf writeCount (sieveLoop N 2 (sieveInit N)) : ℝ) ≤
      3 * ∑ i ∈ Finset.range (Nat.sqrt N - 1), (N : ℝ) / (i + 2) + 11 * Nat.sqrt N + 1 := by
    calc (costOf writeCount (sieveLoop N 2 (sieveInit N)) : ℝ)
        ≤ ((3 * ∑ i ∈ Finset.range (Nat.sqrt N - 1), N / (i + 2) + 11 * Nat.sqrt N + 1 : ℕ) :
          ℝ) := by
          exact_mod_cast h₀
      _ ≤ _ := by
          push_cast
          gcongr with i
          exact_mod_cast Nat.cast_div_le (α := ℝ)
  -- `∑_{i < S-1} 1/(i+2) = H_S - 1 ≤ ln S`
  have h₂ : (harmonic (Nat.sqrt N) : ℝ) =
      1 + ∑ i ∈ Finset.range (Nat.sqrt N - 1), (1 : ℝ) / (i + 2) := by
    obtain ⟨S, hS⟩ : ∃ S, Nat.sqrt N = S + 1 := ⟨Nat.sqrt N - 1, by omega⟩
    rw [hS, harmonic, Finset.sum_range_succ', Nat.add_sub_cancel]
    push_cast
    rw [add_comm]
    congr 1
    · norm_num
    · exact Finset.sum_congr rfl fun i _ ↦ by rw [one_div]; congr 1; ring
  have h₃ := harmonic_le_one_add_log (Nat.sqrt N)
  have h₄ : ∑ i ∈ Finset.range (Nat.sqrt N - 1), (N : ℝ) / (i + 2) =
      N * ∑ i ∈ Finset.range (Nat.sqrt N - 1), (1 : ℝ) / (i + 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h₄] at h₁
  have h₅ : (N : ℝ) * ∑ i ∈ Finset.range (Nat.sqrt N - 1), (1 : ℝ) / (i + 2) ≤
      N * Real.log (Nat.sqrt N) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
  linarith

/-- **Running time of the sieve of Eratosthenes, assuming Mertens' theorem 1.4.2**: the
sieve up to `N ≥ 4` takes at most `3 N (ln ln √N + c) + 11 √N` steps — the book's
`O(N ln ln N)`. -/
theorem sieveSteps_le_of_mertens {c : ℝ} (hM : Assumed.Mertens c) {N : ℕ} (hN : 4 ≤ N) :
    (costOf writeCount (sieveLoop N 2 (sieveInit N)) : ℝ) ≤
      3 * N * (Real.log (Real.log (Nat.sqrt N)) + c) + 11 * Nat.sqrt N := by
  have hS : 2 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have h₁ := sieveLoopSteps_le_primes N 2 _ (by simp [sieveInit]) le_rfl (sieveInv_init N)
  -- pass to a sum over the primes below `√N + 1`
  have h₂ : (∑ q ∈ Finset.Ico 2 (Nat.sqrt N + 1), if q.Prime then N / q else 0) ≤
      ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q := by
    rw [Nat.primesBelow, Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset (fun q hq ↦ by
      simp only [Finset.mem_Ico, Finset.mem_range] at hq ⊢; omega)
  have h₃ : (costOf writeCount (sieveLoop N 2 (sieveInit N)) : ℝ) ≤
      3 * ((∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q : ℕ) : ℝ) + 11 * Nat.sqrt N := by
    have : costOf writeCount (sieveLoop N 2 (sieveInit N)) ≤
        3 * ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q + 11 * Nat.sqrt N := by omega
    exact_mod_cast this
  have h₄ : ((∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q : ℕ) : ℝ) ≤
      N * (Real.log (Real.log (Nat.sqrt N)) + c) :=
    calc ((∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q : ℕ) : ℝ)
        ≤ ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), (N : ℝ) * (1 / (q : ℝ)) := by
          push_cast
          exact Finset.sum_le_sum fun q _ ↦ by
            rw [mul_one_div]; exact_mod_cast Nat.cast_div_le (α := ℝ)
      _ = N * ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), (1 / (q : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hM _ hS) (Nat.cast_nonneg N)
  linarith

end PrimeNumbers.Chapter3
