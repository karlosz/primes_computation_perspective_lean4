import PrimeNumbers.Chapter5.Fermat

/-!
# §5.1.2 Lehman method

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.1.2.

* `lehman`          — Algorithm 5.1.2 (Lehman method).
* `lehman_sound`    — for `n ≥ 512`, a returned `d` is a nontrivial divisor of `n`.  This is
                      the last paragraph of the book's proof of Theorem 5.1.3: the pair
                      found satisfies `a + b < n`, and `n ∣ (a + b)(a - b)`.
* `lehmanPasses_le` — the number of passes of the inner loop is at most
                      `∑_{k=1}^{⌊n^{1/3}⌋} (⌊n^{1/6}⌋ / (4⌊√k⌋) + 2)`, the sum the book
                      evaluates as `O(n^{1/3})`.

**Not proved:** the other half of Theorem 5.1.3, that the algorithm returning nothing
implies `n` is prime.  That argument rests on Dirichlet's approximation theorem applied
to `p/q` for `n = p q`; it is not formalized.  Soundness is proved for `n ≥ 512` rather
than the book's `n > 21`, to keep the inequality `a + b < n` in integer arithmetic.
-/

namespace PrimeNumbers.Chapter5

/-- Search upward for `⌊n^(1/e)⌋`: the largest `c` (within `fuel` steps) with `c^e ≤ n`. -/
def rootLoop (e n : ℕ) : (c fuel : ℕ) → ℕ
  | c, 0 => c
  | c, fuel + 1 => if (c + 1) ^ e ≤ n then rootLoop e n (c + 1) fuel else c

/-- `⌊n^(1/e)⌋`. -/
def iroot (e n : ℕ) : ℕ := rootLoop e n 0 n

theorem rootLoop_pow_le {e n c : ℕ} (hc : c ^ e ≤ n) (fuel : ℕ) :
    rootLoop e n c fuel ^ e ≤ n := by
  induction fuel generalizing c with
  | zero => exact hc
  | succ fuel ih =>
    rw [rootLoop]
    split_ifs with h
    · exact ih h
    · exact hc

theorem iroot_pow_le {e : ℕ} (he : e ≠ 0) (n : ℕ) : iroot e n ^ e ≤ n :=
  rootLoop_pow_le (by simp [he]) n

/-- **Algorithm 5.1.2, step 1 [Trial division]**: a divisor `d` of `n` with `2 ≤ d ≤ c`. -/
def smallDivisor (n : ℕ) : (d fuel : ℕ) → Option ℕ
  | _, 0 => none
  | d, fuel + 1 => if n % d = 0 then some d else smallDivisor n (d + 1) fuel

/-- The inner loop of Algorithm 5.1.2, for `a, a + 1, …` (`fuel` values):
```
if b = √(a² - 4kn) is an integer return gcd(a + b, n);
```
-/
def lehmanInner (n k a : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    let t := a * a - 4 * k * n
    let b := Nat.sqrt t
    if b * b = t then some (Nat.gcd (a + b) n) else lehmanInner n k (a + 1) fuel

/-- The outer loop of Algorithm 5.1.2, for `k, k + 1, …` (`fuel` values):
```
for (2√(kn) ≤ a ≤ 2√(kn) + n^(1/6)/(4√k)) { … }
```
-/
def lehmanOuter (n r6 : ℕ) : (k fuel : ℕ) → Option ℕ
  | _, 0 => none
  | k, fuel + 1 =>
    match lehmanInner n k (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2) with
    | some d => some d
    | none => lehmanOuter n r6 (k + 1) fuel

/-- **Algorithm 5.1.2 (Lehman method).**  Given an integer `n > 21`, either provides a
nontrivial factor of `n` or reports nothing (the book: "proves `n` prime").
```
1. Check whether n has a nontrivial divisor d ≤ n^(1/3), and if so, return d;
2. for (1 ≤ k ≤ n^(1/3)) { for (2√(kn) ≤ a ≤ 2√(kn) + n^(1/6)/(4√k)) { … } }
   return "n is prime";
```
-/
def lehman (n : ℕ) : Option ℕ :=
  let c := iroot 3 n
  match smallDivisor n 2 (c - 1) with
  | some d => some d
  | none => lehmanOuter n (iroot 6 n) 1 c

/-! ## Soundness -/

theorem smallDivisor_some {n d fuel r : ℕ} (h : smallDivisor n d fuel = some r) :
    d ≤ r ∧ r < d + fuel ∧ r ∣ n := by
  induction fuel generalizing d with
  | zero => simp [smallDivisor] at h
  | succ fuel ih =>
    rw [smallDivisor] at h
    split_ifs at h with hd
    · obtain rfl := Option.some.inj h
      exact ⟨le_rfl, by omega, Nat.dvd_of_mod_eq_zero hd⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih h
      exact ⟨by omega, by omega, h₃⟩

theorem lehmanInner_some {n k a fuel d : ℕ} (h : lehmanInner n k a fuel = some d) :
    ∃ a' b, a ≤ a' ∧ a' < a + fuel ∧ a' * a' - 4 * k * n = b * b ∧ d = Nat.gcd (a' + b) n := by
  induction fuel generalizing a with
  | zero => simp [lehmanInner] at h
  | succ fuel ih =>
    simp only [lehmanInner] at h
    split_ifs at h with hsq
    · exact ⟨a, _, le_rfl, by omega, hsq.symm, (Option.some.inj h).symm⟩
    · obtain ⟨a', b, h₁, h₂, h₃, h₄⟩ := ih h
      exact ⟨a', b, by omega, by omega, h₃, h₄⟩

theorem lehmanOuter_some {n r6 k fuel d : ℕ} (h : lehmanOuter n r6 k fuel = some d) :
    ∃ k', k ≤ k' ∧ k' < k + fuel ∧
      lehmanInner n k' (ceilSqrt (4 * k' * n)) (r6 / (4 * Nat.sqrt k') + 2) = some d := by
  induction fuel generalizing k with
  | zero => simp [lehmanOuter] at h
  | succ fuel ih =>
    rw [lehmanOuter] at h
    split at h
    · rename_i d' hd'
      obtain rfl := Option.some.inj h
      exact ⟨k, le_rfl, by omega, hd'⟩
    · obtain ⟨k', h₁, h₂, h₃⟩ := ih h
      exact ⟨k', by omega, by omega, h₃⟩

/-- **Soundness of Algorithm 5.1.2**: for `n ≥ 512`, a returned `d` is a nontrivial
divisor of `n`. -/
theorem lehman_sound {n d : ℕ} (hn : 512 ≤ n) (h : lehman n = some d) :
    d ∣ n ∧ 1 < d ∧ d < n := by
  have hc3 : iroot 3 n ^ 3 ≤ n := iroot_pow_le (by norm_num) n
  have hr6 : iroot 6 n ^ 6 ≤ n := iroot_pow_le (by norm_num) n
  simp only [lehman] at h
  generalize iroot 3 n = c at hc3 h
  generalize iroot 6 n = r6 at hr6 h
  -- `c³ ≤ n` forces `c < n`, and `r6⁶ ≤ n` forces `64 r6 ≤ n`
  have hcn : c < n := by
    by_contra hge
    have : n * 1 * 1 ≤ c * c * c := by
      have h1 : 1 ≤ c := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) h1
    have : c ^ 3 = c * c * c := by ring
    nlinarith
  have hr6n : 64 * r6 ≤ n := by
    rcases Nat.lt_or_ge r6 3 with hlt | hge
    · omega
    · have h5 : 3 ^ 5 ≤ r6 ^ 5 := Nat.pow_le_pow_left hge 5
      have : r6 ^ 6 = r6 * r6 ^ 5 := by ring
      nlinarith
  split at h
  · -- found by trial division
    rename_i d' hd'
    obtain rfl := Option.some.inj h
    obtain ⟨h₁, h₂, h₃⟩ := smallDivisor_some hd'
    exact ⟨h₃, by omega, by omega⟩
  · -- found in the main loop: `a² - 4kn = b²`
    obtain ⟨k, hk1, hkc, hinner⟩ := lehmanOuter_some h
    obtain ⟨a, b, ha₁, ha₂, hsq, rfl⟩ := lehmanInner_some hinner
    have hkn : 0 < 4 * k * n := by positivity
    have hna : 4 * k * n ≤ a * a :=
      (le_ceilSqrt_mul_self _).trans (Nat.mul_le_mul ha₁ ha₁)
    have haa : a * a = 4 * k * n + b * b := by omega
    have hba : b ≤ a := by
      by_contra hlt
      have : a * a < b * b := Nat.mul_lt_mul'' (by omega) (by omega)
      omega
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at hna; omega
      · exact h0
    -- `64 k ≤ n`, because `k ≤ c` and `c³ ≤ n`
    have hk64 : 64 * k ≤ n := by
      rcases Nat.lt_or_ge k 8 with hlt | hge
      · omega
      · have h₁ : k ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have h₂ : k ^ 3 = k * k * k := by ring
        nlinarith
    -- hence `⌈√(4kn)⌉ ≤ n/4 + 1`
    have ha₀ : ceilSqrt (4 * k * n) ≤ n / 4 + 1 := by
      refine ceilSqrt_le ?_
      have h4 : n < 4 * (n / 4 + 1) := by omega
      nlinarith
    -- so `a + b ≤ 2a < n`
    have hfuel : r6 / (4 * Nat.sqrt k) ≤ r6 := Nat.div_le_self _ _
    have hab : a + b < n := by omega
    have hdvd : Nat.gcd (a + b) n ∣ n := Nat.gcd_dvd_right _ _
    have hlt : Nat.gcd (a + b) n < n :=
      (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)).trans_lt hab
    refine ⟨hdvd, ?_, hlt⟩
    -- if `gcd(a + b, n) = 1` then `n ∣ a - b < n`, so `a = b` and `4kn = 0`
    by_contra hd1
    have hpos : 0 < Nat.gcd (a + b) n := Nat.gcd_pos_of_pos_right _ (by omega)
    have hcop : Nat.Coprime n (a + b) := by
      rw [Nat.coprime_comm]; exact (by omega : Nat.gcd (a + b) n = 1)
    have hfac : (a + b) * (a - b) = 4 * k * n := by
      rw [← Nat.mul_self_sub_mul_self_eq]; omega
    have hn_dvd : n ∣ (a + b) * (a - b) := ⟨4 * k, by rw [hfac]; ring⟩
    have := hcop.dvd_of_dvd_mul_left hn_dvd
    have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    rw [hzero, mul_zero] at hfac
    omega

/-! ## Running time -/

/-- The number of passes of the inner loop made by `lehmanInner`. -/
def lehmanInnerPasses (n k a : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
    if Nat.sqrt (a * a - 4 * k * n) * Nat.sqrt (a * a - 4 * k * n) = a * a - 4 * k * n then 1
    else lehmanInnerPasses n k (a + 1) fuel + 1

/-- The number of passes of the inner loop made by `lehmanOuter`. -/
def lehmanPasses (n r6 : ℕ) : (k fuel : ℕ) → ℕ
  | _, 0 => 0
  | k, fuel + 1 =>
    lehmanInnerPasses n k (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2) +
      match lehmanInner n k (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2) with
      | some _ => 0
      | none => lehmanPasses n r6 (k + 1) fuel

theorem lehmanInnerPasses_le (n k a fuel : ℕ) : lehmanInnerPasses n k a fuel ≤ fuel := by
  induction fuel generalizing a with
  | zero => simp [lehmanInnerPasses]
  | succ fuel ih =>
    rw [lehmanInnerPasses]
    split_ifs
    · omega
    · have := ih (a + 1); omega

/-- **Running time of Algorithm 5.1.2**: step [Loop] makes at most
`∑_{k} (⌊n^{1/6}⌋ / (4⌊√k⌋) + 2)` passes (over the `k` actually tried), each costing two
multiplications, one integer square root and (once) a gcd.  This is the sum the book bounds
by `O(n^{1/3})`; step [Trial division] adds at most `⌊n^{1/3}⌋` divisions. -/
theorem lehmanPasses_le (n r6 k fuel : ℕ) :
    lehmanPasses n r6 k fuel ≤
      ∑ i ∈ Finset.range fuel, (r6 / (4 * Nat.sqrt (k + i)) + 2) := by
  induction fuel generalizing k with
  | zero => simp [lehmanPasses]
  | succ fuel ih =>
    have h₁ := lehmanInnerPasses_le n k (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2)
    have h₂ := ih (k + 1)
    rw [Finset.sum_range_succ', add_zero]
    have hcongr : ∑ i ∈ Finset.range fuel, (r6 / (4 * Nat.sqrt (k + (i + 1))) + 2) =
        ∑ i ∈ Finset.range fuel, (r6 / (4 * Nat.sqrt (k + 1 + i)) + 2) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [add_right_comm, add_assoc]
    rw [hcongr, lehmanPasses]
    split <;> omega

end PrimeNumbers.Chapter5
