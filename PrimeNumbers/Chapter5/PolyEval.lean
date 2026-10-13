import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter5.Lehman

/-!
# §5.5 Polynomial evaluation method (Pollard–Strassen)

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.5.

With `B = ⌈n^{1/4}⌉` and `f(x) = x (x - 1) ⋯ (x - B + 1)`, we have
`f(jB) = (jB)! / ((j - 1)B)!`, "so that the least `j` with `gcd(f(jB), n) > 1` isolates the
least prime factor of `n` in the interval `((j - 1)B, jB]`"; one then tries the members of
that interval as divisors.

* `pollardStrassen`     — the method, returning the least prime factor of `n`.
* `pollardStrassen_eq`  — for composite `n > 1` it returns `some (minFac n)`: this is a
                          *deterministic, rigorous* factoring algorithm, as the book says.

**What is not here yet (this file is a start on §5.5):** the values `f(jB) mod n` are
computed by multiplying out each block (`blockProd`), which costs `B` multiplications per
block and `B² ≈ √n` in total.  The point of the method is that Algorithm 9.6.7 (fast
polynomial multiplication and multipoint evaluation) produces all `f(jB) mod n` in
`O(n^{1/4} ln² n)` operations; that algorithm, and hence the running time
`O(n^{1/4 + ε})`, is not formalized.  The correctness theorem below does not depend on how
the `f(jB) mod n` are computed, only on their values.
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2

/-- `m (m - 1) ⋯ (m - i + 1) mod n`; for `m = jB`, `i = B` this is `f(jB) mod n`. -/
def blockProd (n m : ℕ) : ℕ → ℕ
  | 0 => 1 % n
  | i + 1 => blockProd n m i * (m - i) % n

/-- The least `j` (among `fuel` values from `j` on) with `gcd(f(jB), n) > 1`. -/
def findBlock (n B : ℕ) : (j fuel : ℕ) → Option ℕ
  | _, 0 => none
  | j, fuel + 1 =>
    if euclid n (blockProd n (j * B) B) ≠ 1 then some j else findBlock n B (j + 1) fuel

/-- **The Pollard–Strassen polynomial evaluation method** (§5.5): find the least `j` with
`gcd(f(jB), n) > 1`, then the first divisor of `n` in the interval `((j - 1)B, jB]`. -/
def pollardStrassen (n : ℕ) : Option ℕ :=
  let B := iroot 4 n + 1
  match findBlock n B 1 B with
  | none => none
  | some j => smallDivisor n (max 2 ((j - 1) * B + 1)) B

/-- A prime `r ∣ n` divides `f(m) mod n = m (m - 1) ⋯ (m - i + 1) mod n` iff it divides
one of the factors. -/
theorem prime_dvd_blockProd {n r : ℕ} (hr : r.Prime) (hrn : r ∣ n) (m i : ℕ) :
    r ∣ blockProd n m i ↔ ∃ e < i, r ∣ m - e := by
  induction i with
  | zero =>
    simp only [blockProd, Nat.dvd_mod_iff hrn, Nat.dvd_one, not_lt_zero, false_and,
      exists_false, iff_false]
    exact hr.one_lt.ne'
  | succ i ih =>
    rw [blockProd, Nat.dvd_mod_iff hrn, hr.dvd_mul, ih]
    constructor
    · rintro (⟨e, he, h⟩ | h)
      · exact ⟨e, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨e, he, h⟩
      rcases Nat.lt_or_ge e i with hlt | hge
      · exact Or.inl ⟨e, hlt, h⟩
      · obtain rfl : e = i := by omega
        exact Or.inr h

theorem findBlock_eq {n B j₀ : ℕ} (j fuel : ℕ) (hj : j ≤ j₀) (hfuel : j₀ < j + fuel)
    (hbefore : ∀ j', j ≤ j' → j' < j₀ → euclid n (blockProd n (j' * B) B) = 1)
    (hat : euclid n (blockProd n (j₀ * B) B) ≠ 1) : findBlock n B j fuel = some j₀ := by
  induction fuel generalizing j with
  | zero => omega
  | succ fuel ih =>
    rw [findBlock]
    split_ifs with h
    · rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · rfl
      · exact absurd (hbefore j le_rfl hlt) h
    · have hne : j ≠ j₀ := by rintro rfl; exact h hat
      exact ih (j + 1) (by omega) (by omega) fun j' h₁ h₂ ↦ hbefore j' (by omega) h₂

theorem smallDivisor_le {n d fuel m : ℕ} (hdm : d ≤ m) (hm : m < d + fuel) (hmn : m ∣ n) :
    ∃ r, smallDivisor n d fuel = some r ∧ r ≤ m := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    rw [smallDivisor]
    split_ifs with h
    · exact ⟨d, rfl, hdm⟩
    · have hne : d ≠ m := by rintro rfl; exact h (Nat.mod_eq_zero_of_dvd hmn)
      exact ih (by omega) (by omega)

/-- **Correctness of the polynomial evaluation method.**  For composite `n > 1`, the
method returns the least prime factor of `n`. -/
theorem pollardStrassen_eq {n : ℕ} (hn : 1 < n) (hnp : ¬n.Prime) :
    pollardStrassen n = some n.minFac := by
  have hB4 : n < (iroot 4 n + 1) ^ 4 := lt_iroot_succ_pow (by norm_num) n
  simp only [pollardStrassen]
  generalize iroot 4 n + 1 = B at hB4 ⊢
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with rfl | h
    · simp at hB4
    · exact h
  -- the least prime factor `p` satisfies `p ≤ B²`
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hpn := Nat.minFac_dvd n
  have hpsq := Nat.minFac_sq_le_self (by omega) hnp
  set p := n.minFac with hp_def
  have hpB : p ≤ B * B := by
    by_contra hgt
    have h₁ : (B * B) * (B * B) < p * p := Nat.mul_lt_mul'' (by omega) (by omega)
    have h₂ : B ^ 4 = (B * B) * (B * B) := by ring
    have h₃ : p ^ 2 = p * p := sq p
    omega
  -- `p` lies in the block `j₀ = ⌈p / B⌉`: `(j₀ - 1) B < p ≤ j₀ B`
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j, j * B < p ∧ p ≤ (j + 1) * B := by
    refine ⟨(p - 1) / B, ?_, ?_⟩
    · have := Nat.div_mul_le_self (p - 1) B
      have := hp.two_le
      omega
    · have := Nat.lt_div_mul_add (a := p - 1) hB
      rw [Nat.add_mul, one_mul]
      omega
  have hjB : j < B := by
    by_contra hge
    have : B * B ≤ j * B := Nat.mul_le_mul_right B (not_lt.mp hge)
    omega
  -- no earlier block has a common factor with `n`
  have hbefore : ∀ j', 1 ≤ j' → j' < j + 1 → euclid n (blockProd n (j' * B) B) = 1 := by
    intro j' h1 hlt
    by_contra hne
    rw [euclid_eq_gcd] at hne
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
    have hrn : r ∣ n := hrdvd.trans (Nat.gcd_dvd_left _ _)
    obtain ⟨e, he, hre⟩ := (prime_dvd_blockProd hr hrn _ _).mp
      (hrdvd.trans (Nat.gcd_dvd_right _ _))
    have h₁ : B ≤ j' * B := Nat.le_mul_of_pos_left B h1
    have h₂ : j' * B ≤ j * B := Nat.mul_le_mul_right B (by omega)
    have h₃ : r ≤ j' * B - e := Nat.le_of_dvd (by omega) hre
    have h₄ : p ≤ r := Nat.minFac_le_of_dvd hr.two_le hrn
    omega
  -- the block `j + 1` does
  have hat : euclid n (blockProd n ((j + 1) * B) B) ≠ 1 := by
    intro h1
    have hdvd : p ∣ blockProd n ((j + 1) * B) B :=
      (prime_dvd_blockProd hp hpn _ _).mpr ⟨(j + 1) * B - p, by
        rw [Nat.add_mul, one_mul]; omega, by
        rw [Nat.sub_sub_self hj₂]⟩
    have := Nat.dvd_gcd hpn hdvd
    rw [← euclid_eq_gcd, h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  rw [findBlock_eq 1 B (by omega) (by omega) hbefore hat]
  -- scanning the interval finds `p` first
  simp only [Nat.add_sub_cancel]
  obtain ⟨r, hr, hrp⟩ := smallDivisor_le (n := n) (d := max 2 (j * B + 1)) (fuel := B) (m := p)
    (max_le hp.two_le (by omega)) (by
      have : j * B + 1 ≤ max 2 (j * B + 1) := le_max_right _ _
      rw [Nat.add_mul, one_mul] at hj₂
      omega) hpn
  rw [hr]
  obtain ⟨h₁, -, h₃⟩ := smallDivisor_some hr
  have h2 : 2 ≤ r := (le_max_left _ _).trans h₁
  have : p ≤ r := Nat.minFac_le_of_dvd h2 h₃
  congr 1
  omega

end PrimeNumbers.Chapter5
