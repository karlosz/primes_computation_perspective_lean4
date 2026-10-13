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

/-! ## Completeness, reduced to the existence statement of Theorem 5.1.3 -/

/-- **The existence statement in the proof of Theorem 5.1.3**: some `k ≤ n^{1/3}` and some
`a` in the range scanned for that `k` have `a² - 4kn` a perfect square.

The book proves: if `n` is composite with no divisor in `[2, n^{1/3}]`, then `n = p q`
with primes `n^{1/3} < p ≤ q`, and by Dirichlet's approximation theorem there are `u, v`
with `k = u v ≤ n^{1/3}` and `|u q - v p| < n^{1/3}`; then `a = u q + v p` works.  That
derivation is **not formalized**; `LehmanWitness n` is what it produces. -/
def LehmanWitness (n : ℕ) : Prop :=
  ∃ k a b, 1 ≤ k ∧ k ≤ iroot 3 n ∧ ceilSqrt (4 * k * n) ≤ a ∧
    a < ceilSqrt (4 * k * n) + (iroot 6 n / (4 * Nat.sqrt k) + 2) ∧ a * a - 4 * k * n = b * b

theorem lehmanInner_isSome {n k a fuel : ℕ}
    (h : ∃ a' b, a ≤ a' ∧ a' < a + fuel ∧ a' * a' - 4 * k * n = b * b) :
    (lehmanInner n k a fuel).isSome := by
  induction fuel generalizing a with
  | zero => obtain ⟨a', b, h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    simp only [lehmanInner]
    split_ifs with hsq
    · rfl
    · obtain ⟨a', b, h₁, h₂, h₃⟩ := h
      have hne : a' ≠ a := by
        rintro rfl
        exact hsq (by rw [h₃, Nat.sqrt_eq])
      exact ih ⟨a', b, by omega, by omega, h₃⟩

theorem lehmanOuter_isSome {n r6 k fuel : ℕ}
    (h : ∃ k', k ≤ k' ∧ k' < k + fuel ∧
      (lehmanInner n k' (ceilSqrt (4 * k' * n)) (r6 / (4 * Nat.sqrt k') + 2)).isSome) :
    (lehmanOuter n r6 k fuel).isSome := by
  induction fuel generalizing k with
  | zero => obtain ⟨k', h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    rw [lehmanOuter]
    split
    · rfl
    · rename_i hnone
      obtain ⟨k', h₁, h₂, h₃⟩ := h
      have hne : k' ≠ k := by
        rintro rfl
        rw [hnone] at h₃
        exact absurd h₃ (by simp)
      exact ih ⟨k', by omega, by omega, h₃⟩

/-- If the existence statement holds, Algorithm 5.1.2 returns an answer. -/
theorem lehman_isSome_of_witness {n : ℕ} (h : LehmanWitness n) : (lehman n).isSome := by
  obtain ⟨k, a, b, hk1, hkc, ha₁, ha₂, hsq⟩ := h
  simp only [lehman]
  split
  · rfl
  · exact lehmanOuter_isSome ⟨k, hk1, by omega, lehmanInner_isSome ⟨a, b, ha₁, ha₂, hsq⟩⟩

theorem smallDivisor_none {n d fuel : ℕ} (h : smallDivisor n d fuel = none) :
    ∀ r, d ≤ r → r < d + fuel → ¬r ∣ n := by
  induction fuel generalizing d with
  | zero => intro r h₁ h₂; omega
  | succ fuel ih =>
    rw [smallDivisor] at h
    split_ifs at h with hd
    intro r h₁ h₂ hr
    rcases Nat.eq_or_lt_of_le h₁ with rfl | hlt
    · exact hd (Nat.mod_eq_zero_of_dvd hr)
    · exact ih h r (by omega) (by omega) hr

/-- **Completeness of Algorithm 5.1.2, modulo the existence statement.**  Suppose that for
composite `n` without a divisor in `[2, n^{1/3}]` the existence statement `LehmanWitness n`
holds (this is the part of the proof of Theorem 5.1.3 that is not formalized).  Then if
the algorithm returns nothing, `n` is prime. -/
theorem lehman_none_prime {n : ℕ}
    (hex : ¬n.Prime → (∀ d, 2 ≤ d → d ≤ iroot 3 n → ¬d ∣ n) → LehmanWitness n)
    (h : lehman n = none) : n.Prime := by
  by_contra hnp
  have hsmall : smallDivisor n 2 (iroot 3 n - 1) = none := by
    simp only [lehman] at h
    split at h
    · exact absurd h (by simp)
    · assumption
  have hwit := hex hnp fun d h₁ h₂ ↦ smallDivisor_none hsmall d h₁ (by omega)
  have := lehman_isSome_of_witness hwit
  rw [h] at this
  exact absurd this (by simp)

/-! ## Closed form of the running time -/

/-- `∑_{k=1}^{c} 1/√k ≤ 2√c`. -/
theorem sum_inv_sqrt_le (c : ℕ) :
    ∑ i ∈ Finset.range c, (1 / Real.sqrt ((i : ℝ) + 1)) ≤ 2 * Real.sqrt c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ]
    have ha : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
    have hb : (0 : ℝ) < Real.sqrt ((c : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((c : ℝ) + 1) ^ 2 = c + 1 := Real.sq_sqrt (by positivity)
    have hstep : 1 / Real.sqrt ((c : ℝ) + 1) ≤
        2 * Real.sqrt ((c : ℝ) + 1) - 2 * Real.sqrt c := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((c : ℝ) + 1) - Real.sqrt c)]
    push_cast
    linarith

/-- `⌊√k⌋ ≥ √k / 2` for `k ≥ 1`. -/
theorem sqrt_le_two_mul_natSqrt {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt k ≤ 2 * (Nat.sqrt k : ℝ) := by
  have h1 : 1 ≤ Nat.sqrt k := Nat.le_sqrt.mpr (by omega)
  have h2 : (k : ℝ) ≤ ((Nat.sqrt k : ℝ) + 1) ^ 2 := by
    have := (Nat.lt_succ_sqrt' k).le
    exact_mod_cast this
  have h3 : Real.sqrt k ≤ (Nat.sqrt k : ℝ) + 1 :=
    (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq (by positivity))
  have h4 : (1 : ℝ) ≤ Nat.sqrt k := by exact_mod_cast h1
  linarith

/-- **Closed form for the running time of Algorithm 5.1.2**: with `c = ⌊n^{1/3}⌋` and
`r6 = ⌊n^{1/6}⌋`, step [Loop] makes at most `r6 √c + 2c` passes.  Since `r6⁶ ≤ n` and
`c³ ≤ n` this is at most `n^{1/3} + 2 n^{1/3}`: the book's `O(n^{1/3})`. -/
theorem lehmanPasses_le_closed (n r6 c : ℕ) :
    (lehmanPasses n r6 1 c : ℝ) ≤ r6 * Real.sqrt c + 2 * c := by
  have h₁ : (lehmanPasses n r6 1 c : ℝ) ≤
      ((∑ i ∈ Finset.range c, (r6 / (4 * Nat.sqrt (1 + i)) + 2) : ℕ) : ℝ) := by
    exact_mod_cast lehmanPasses_le n r6 1 c
  have hterm : ∀ i ∈ Finset.range c,
      (((r6 / (4 * Nat.sqrt (1 + i)) + 2 : ℕ)) : ℝ) ≤
        (r6 : ℝ) / 2 * (1 / Real.sqrt ((i : ℝ) + 1)) + 2 := by
    intro i _
    have hs : 1 ≤ Nat.sqrt (1 + i) := Nat.le_sqrt.mpr (by omega)
    have hspos : (0 : ℝ) < Nat.sqrt (1 + i) := by exact_mod_cast hs
    have hrt : (0 : ℝ) < Real.sqrt ((i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h2 := sqrt_le_two_mul_natSqrt (k := 1 + i) (by omega)
    rw [show ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 by push_cast; ring] at h2
    have hdiv : ((r6 / (4 * Nat.sqrt (1 + i)) : ℕ) : ℝ) ≤ (r6 : ℝ) / (4 * Nat.sqrt (1 + i)) := by
      have := Nat.cast_div_le (α := ℝ) (m := r6) (n := 4 * Nat.sqrt (1 + i))
      simpa using this
    have hcmp : (r6 : ℝ) / (4 * Nat.sqrt (1 + i)) ≤
        (r6 : ℝ) / 2 * (1 / Real.sqrt ((i : ℝ) + 1)) := by
      rw [div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg r6) (by positivity) (by linarith)
    push_cast
    linarith
  have h₂ := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h₂
  have h₃ := sum_inv_sqrt_le c
  have hr : (0 : ℝ) ≤ (r6 : ℝ) / 2 := by positivity
  have h₄ := mul_le_mul_of_nonneg_left h₃ hr
  push_cast at h₁ h₂ ⊢
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h₂
  nlinarith

end PrimeNumbers.Chapter5
