import Mathlib

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
def bit (bits : Array Bool) (i : ℕ) : Bool := bits.getD i false

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
def markMultiples (p : ℕ) (bits : Array Bool) (j : ℕ) : Array Bool :=
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
def sieveLoop (N p : ℕ) (bits : Array Bool) : Array Bool :=
  if p * p ≤ N ∧ 0 < p then
    sieveLoop N (p + 1) (if bit bits p then markMultiples p bits (p * p) else bits)
  else bits
termination_by N + 1 - p
decreasing_by
  have : p ≤ p * p := Nat.le_mul_self p
  omega

/-- **The sieve of Eratosthenes**: a Boolean array of length `N + 1` whose `i`-th entry
tells whether `i` is prime. -/
def sieve (N : ℕ) : Array Bool :=
  sieveLoop N 2 (((Array.replicate (N + 1) true).setIfInBounds 0 false).setIfInBounds 1 false)

/-- The primes up to `N`, read off the sieve. -/
def sievePrimes (N : ℕ) : List ℕ :=
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

theorem sieveLoop_spec (N p : ℕ) (bits : Array Bool) (hp : 2 ≤ p) (hinv : SieveInv N p bits) :
    ∀ i, bit (sieveLoop N p bits) i = true ↔ i ≤ N ∧ i.Prime := by
  fun_induction sieveLoop N p bits with
  | case1 p bits hle ih =>
    have hpN : p ≤ N := (Nat.le_mul_self p).trans hle.1
    refine ih (by omega) fun i ↦ ?_
    -- `p` is prime iff its bit is still set
    have hbit : bit bits p = true ↔ p.Prime := by
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

/-- **Correctness of the sieve of Eratosthenes**: bit `i` of `sieve N` is set exactly when
`i ≤ N` is prime. -/
theorem sieve_spec (N i : ℕ) : bit (sieve N) i = true ↔ i ≤ N ∧ i.Prime := by
  refine sieveLoop_spec N 2 _ le_rfl (fun i ↦ ?_) i
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

/-- `sievePrimes N` is the list of the primes `≤ N`. -/
theorem mem_sievePrimes {N q : ℕ} : q ∈ sievePrimes N ↔ q.Prime ∧ q ≤ N := by
  simp only [sievePrimes, List.mem_filter, List.mem_range, sieve_spec]
  constructor
  · rintro ⟨-, h₁, h₂⟩; exact ⟨h₂, h₁⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨by omega, h₂, h₁⟩

end PrimeNumbers.Chapter3
