import PrimeNumbers.Assumed

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
theorem sieveInv_init (N : ℕ) : SieveInv N 2
    (((Array.replicate (N + 1) true).setIfInBounds 0 false).setIfInBounds 1 false) := by
  intro i
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

The sieve performs no multiplications or divisions of big numbers: its work is the bit
writes that strike out multiples.  We count those. -/

/-- The number of bits written by `markMultiples p bits j`. -/
def markCost (p : ℕ) (bits : Array Bool) (j : ℕ) : ℕ :=
  if j < bits.size ∧ 0 < p then markCost p (bits.setIfInBounds j false) (j + p) + 1 else 0
termination_by bits.size - j
decreasing_by simp only [Array.size_setIfInBounds]; omega

/-- The number of bits written by `sieveLoop N p bits`. -/
def sieveCost (N p : ℕ) (bits : Array Bool) : ℕ :=
  if p * p ≤ N ∧ 0 < p then
    (if bit bits p then markCost p bits (p * p) else 0) +
      sieveCost N (p + 1) (if bit bits p then markMultiples p bits (p * p) else bits)
  else 0
termination_by N + 1 - p
decreasing_by
  have : p ≤ p * p := Nat.le_mul_self p
  omega

/-- Striking out `j, j + p, …` below `size` writes at most `⌈(size - j)/p⌉` bits. -/
theorem markCost_mul_le (p : ℕ) (bits : Array Bool) (j : ℕ) :
    markCost p bits j * p ≤ bits.size - j + (p - 1) := by
  fun_induction markCost p bits j with
  | case1 bits j h ih =>
    rw [Array.size_setIfInBounds] at ih
    rw [add_mul, one_mul]
    rcases Nat.lt_or_ge bits.size (j + p) with hlt | hge
    · -- the next index is already out of range: no further writes
      have h0 : markCost p (bits.setIfInBounds j false) (j + p) = 0 := by
        by_contra hne
        have := Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero hne)
        omega
      rw [h0]; omega
    · omega
  | case2 bits j h => omega

/-- For a prime `p`, the sieve writes at most `N / p` bits. -/
theorem markCost_sq_le {N p : ℕ} (hp : 0 < p) (hpN : p * p ≤ N) {bits : Array Bool}
    (hsize : bits.size = N + 1) : markCost p bits (p * p) ≤ N / p := by
  rw [Nat.le_div_iff_mul_le hp]
  have h₁ := markCost_mul_le p bits (p * p)
  rw [hsize] at h₁
  have h₂ : p ≤ p * p := Nat.le_mul_self p
  omega

theorem sieveCost_le (N p : ℕ) (bits : Array Bool) (hsize : bits.size = N + 1) :
    sieveCost N p bits ≤ ∑ i ∈ Finset.range (Nat.sqrt N + 1 - p), N / (p + i) := by
  fun_induction sieveCost N p bits with
  | case1 p bits hle ih =>
    have hps : p ≤ Nat.sqrt N := Nat.le_sqrt.mpr hle.1
    have hsize' : (if bit bits p = true then markMultiples p bits (p * p) else bits).size =
        N + 1 := by
      split_ifs
      · rw [(markMultiples_spec p bits (p * p) hle.2).1, hsize]
      · exact hsize
    have ih := ih hsize'
    have hmark : (if bit bits p = true then markCost p bits (p * p) else 0) ≤ N / p := by
      split_ifs
      · exact markCost_sq_le hle.2 hle.1 hsize
      · exact Nat.zero_le _
    rw [show Nat.sqrt N + 1 - p = (Nat.sqrt N + 1 - (p + 1)) + 1 by omega,
      Finset.sum_range_succ', add_zero]
    have hcongr : ∑ i ∈ Finset.range (Nat.sqrt N + 1 - (p + 1)), N / (p + (i + 1)) =
        ∑ i ∈ Finset.range (Nat.sqrt N + 1 - (p + 1)), N / (p + 1 + i) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [add_right_comm, add_assoc]
    rw [hcongr]
    simp only [dite_eq_ite] at ih
    omega
  | case2 p bits hgt => exact Nat.zero_le _

/-- The number of bit writes made by `sieve N` in its main loop. -/
def sieveWrites (N : ℕ) : ℕ :=
  sieveCost N 2 (((Array.replicate (N + 1) true).setIfInBounds 0 false).setIfInBounds 1 false)

/-- **Running time of the sieve of Eratosthenes**: at most `∑_{p=2}^{⌊√N⌋} ⌊N/p⌋` bit
writes (one term for each `p`, whether prime or not; the true count, over primes only, is
`∼ N ln ln N`, which needs Mertens' theorem 1.4.2). -/
theorem sieveWrites_le (N : ℕ) :
    sieveWrites N ≤ ∑ i ∈ Finset.range (Nat.sqrt N - 1), N / (i + 2) := by
  have := sieveCost_le N 2
    (((Array.replicate (N + 1) true).setIfInBounds 0 false).setIfInBounds 1 false) (by simp)
  rw [show Nat.sqrt N + 1 - 2 = Nat.sqrt N - 1 by omega] at this
  simpa [sieveWrites, add_comm] using this

/-- **Running time of the sieve, closed form**: at most `N ln √N = ½ N ln N` bit writes,
by comparing with the harmonic series. -/
theorem sieveWrites_le_log (N : ℕ) :
    (sieveWrites N : ℝ) ≤ N * Real.log (Nat.sqrt N) := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h0 | hpos
  · have := sieveWrites_le N
    simp [h0] at this
    simp [this, h0]
  have h₁ : (sieveWrites N : ℝ) ≤ ∑ i ∈ Finset.range (Nat.sqrt N - 1), (N : ℝ) / (i + 2) := by
    calc (sieveWrites N : ℝ)
        ≤ ((∑ i ∈ Finset.range (Nat.sqrt N - 1), N / (i + 2) : ℕ) : ℝ) := by
          exact_mod_cast sieveWrites_le N
      _ ≤ _ := by
          push_cast
          exact Finset.sum_le_sum fun i _ ↦ by exact_mod_cast Nat.cast_div_le (α := ℝ)
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
  refine h₁.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N))

/-! ### Counting only the primes: the `N ln ln N` bound -/

/-- Only primes strike out: the sieve writes at most `∑_{p ≤ √N, p prime} ⌊N/p⌋` bits. -/
theorem sieveCost_le_primes (N p : ℕ) (bits : Array Bool) (hsize : bits.size = N + 1)
    (hp : 2 ≤ p) (hinv : SieveInv N p bits) :
    sieveCost N p bits ≤
      ∑ q ∈ Finset.Ico p (Nat.sqrt N + 1), if q.Prime then N / q else 0 := by
  fun_induction sieveCost N p bits with
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
    have hmark : (if bit bits p = true then markCost p bits (p * p) else 0) ≤
        if p.Prime then N / p else 0 := by
      split_ifs with h₁ h₂ h₂
      · exact markCost_sq_le hle.2 hle.1 hsize
      · exact absurd (hbit.mp h₁) h₂
      · exact Nat.zero_le _
      · exact le_rfl
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : p < Nat.sqrt N + 1)]
    simp only [dite_eq_ite] at ih
    omega
  | case2 p bits hgt => exact Nat.zero_le _

/-- **Running time of the sieve of Eratosthenes, assuming Mertens' theorem 1.4.2**: the
sieve up to `N ≥ 4` makes at most `N (ln ln √N + c)` bit writes — the book's
`O(N ln ln N)`. -/
theorem sieveWrites_le_of_mertens {c : ℝ} (hM : Assumed.Mertens c) {N : ℕ} (hN : 4 ≤ N) :
    (sieveWrites N : ℝ) ≤ N * (Real.log (Real.log (Nat.sqrt N)) + c) := by
  have hS : 2 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have h₁ := sieveCost_le_primes N 2 _ (by simp) le_rfl (sieveInv_init N)
  -- pass to a sum over the primes below `√N + 1`
  have h₂ : (∑ q ∈ Finset.Ico 2 (Nat.sqrt N + 1), if q.Prime then N / q else 0) ≤
      ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q := by
    rw [Nat.primesBelow, Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset (fun q hq ↦ by
      simp only [Finset.mem_Ico, Finset.mem_range] at hq ⊢; omega)
  calc (sieveWrites N : ℝ)
      ≤ ((∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), N / q : ℕ) : ℝ) := by
        exact_mod_cast h₁.trans h₂
    _ ≤ ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), (N : ℝ) * (1 / (q : ℝ)) := by
        push_cast
        exact Finset.sum_le_sum fun q _ ↦ by
          rw [mul_one_div]; exact_mod_cast Nat.cast_div_le (α := ℝ)
    _ = N * ∑ q ∈ Nat.primesBelow (Nat.sqrt N + 1), (1 / (q : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM _ hS) (Nat.cast_nonneg N)

end PrimeNumbers.Chapter3
