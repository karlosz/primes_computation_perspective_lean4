import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.SquareRoot

/-!
# §3.4 Pseudoprimes and §3.5 Probable primes and witnesses

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Sections 3.4–3.5.

* `theorem_3_4_1`           — Fermat's little theorem `aⁿ ≡ a (mod n)`.
* `probablePrime`           — Algorithm 3.4.3 (probable prime test); `probablePrime_iff`,
                              `probablePrime_of_prime`.
* `theorem_3_4_4`           — infinitely many pseudoprimes to each base (Mathlib).
* `theorem_3_5_1`           — for an odd prime `n`, condition (3.4) holds.
* `strongProbablePrime`     — Algorithm 3.5.2 (strong probable prime test);
                              `strongProbablePrime_iff` says it decides (3.4), and
                              `strongProbablePrime_of_prime` that primes always pass.
* `millerRabin`             — the test with several bases; `not_prime_of_millerRabin`.

Not formalized: the counting results (Theorems 3.4.2, 3.4.7, 3.5.4 — "at least 3/4 of
the bases are witnesses" — and 3.5.10–3.5.12).
-/

namespace PrimeNumbers.Chapter3

open PrimeNumbers.Chapter2

/-! ## §3.4 Pseudoprimes -/

/-- **Theorem 3.4.1 (Fermat's little theorem).**  If `n` is prime, then for any integer
`a` we have `aⁿ ≡ a (mod n)`. -/
theorem theorem_3_4_1 {n : ℕ} (hn : n.Prime) (a : ℤ) : a ^ n ≡ a [ZMOD n] := by
  have : Fact n.Prime := ⟨hn⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  exact ZMod.pow_card _

/-- **Algorithm 3.4.3 (Probable prime test).**  Given `n > 3` and `2 ≤ a ≤ n - 2`,
returns `true` for "`n` is a probable prime base `a`" and `false` for "`n` is composite".
```
b = a^(n-1) mod n;                                // Use Algorithm 2.1.5.
if (b == 1) return "n is a probable prime base a";
return "n is composite";
```
-/
def probablePrime (n a : ℕ) : Bool :=
  powMod a (n - 1) n = 1

/-- Algorithm 3.4.3 decides the Fermat congruence (3.3), `a^(n-1) ≡ 1 (mod n)`. -/
theorem probablePrime_iff {n : ℕ} (hn : 1 < n) (a : ℕ) :
    probablePrime n a = true ↔ a ^ (n - 1) ≡ 1 [MOD n] := by
  rw [probablePrime, decide_eq_true_iff, powMod_eq, Nat.ModEq, Nat.mod_eq_of_lt hn]

/-- Algorithm 3.4.3 agrees with Mathlib's `Nat.ProbablePrime`. -/
theorem probablePrime_iff_probablePrime {n a : ℕ} (hn : 1 < n) (ha : 1 ≤ a) :
    probablePrime n a = true ↔ Nat.ProbablePrime n a := by
  rw [probablePrime_iff hn, Nat.probablePrime_iff_modEq n ha]

/-- A prime `n` passes Algorithm 3.4.3 for every base `a` not divisible by `n`: so the
answer "`n` is composite" is always correct. -/
theorem probablePrime_of_prime {n a : ℕ} (hn : n.Prime) (ha : ¬n ∣ a) :
    probablePrime n a = true :=
  (probablePrime_iff hn.one_lt a).mpr (fermat_little hn ha)

/-- **Theorem 3.4.4.**  For each integer `a ≥ 2` (indeed `a ≥ 1`) there are infinitely
many Fermat pseudoprimes base `a`. -/
theorem theorem_3_4_4 {a : ℕ} (ha : 1 ≤ a) : {n : ℕ | Nat.FermatPsp n a}.Infinite :=
  Nat.infinite_setOfPred_pseudoprimes ha

/-! ## §3.5 Probable primes and witnesses -/

/-- **Theorem 3.5.1.**  Suppose `n` is an odd prime and `n - 1 = 2^s t`.  If `a` is not
divisible by `n` then either `a^t ≡ 1 (mod n)` or `a^(2^i t) ≡ -1 (mod n)` for some
`0 ≤ i ≤ s - 1`.

As the book says, the proof uses only Fermat's little theorem and the fact that `±1` are
the only square roots of `1` modulo a prime. -/
theorem theorem_3_5_1 {n : ℕ} [Fact n.Prime] {s t : ℕ} (hst : n - 1 = 2 ^ s * t)
    {a : ZMod n} (ha : a ≠ 0) :
    a ^ t = 1 ∨ ∃ i < s, a ^ (2 ^ i * t) = -1 := by
  have key : ∀ k, a ^ (2 ^ k * t) = 1 → a ^ t = 1 ∨ ∃ i < k, a ^ (2 ^ i * t) = -1 := by
    intro k
    induction k with
    | zero => intro h; left; simpa using h
    | succ k ih =>
      intro h
      have hsq : (a ^ (2 ^ k * t)) ^ 2 = 1 := by rw [← pow_mul, ← h]; congr 1; ring
      rcases sq_eq_one_iff.mp hsq with h1 | hneg
      · rcases ih h1 with h | ⟨i, hi, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, h⟩
      · exact Or.inr ⟨k, by omega, hneg⟩
  exact key s (by rw [← hst, ZMod.pow_card_sub_one_eq_one ha])

/-- The loop of Algorithm 3.5.2 (`j` passes remaining):
```
b = b² mod n;
if (b == n - 1) return "n is a strong probable prime base a";
```
-/
def sprpLoop (n b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 =>
    let b' := b * b % n
    if b' = n - 1 then true else sprpLoop n b' j

/-- **Algorithm 3.5.2 (Strong probable prime test).**  Given an odd `n > 3`, written
`n = 1 + 2^s t` with `t` odd, and `1 < a < n - 1`, returns `true` for "`n` is a strong
probable prime base `a`" and `false` for "`n` is composite".
```
b = a^t mod n;                                    // Use Algorithm 2.1.5.
if (b == 1 or b == n - 1) return "n is a strong probable prime base a";
for (j ∈ [1, s - 1]) {
  b = b² mod n;
  if (b == n - 1) return "n is a strong probable prime base a";
}
return "n is composite";
```
-/
def strongProbablePrime (n a : ℕ) : Bool :=
  let st := oddPart (n - 1)
  let b := powMod a st.2 n
  if b = 1 ∨ b = n - 1 then true else sprpLoop n b (st.1 - 1)

/-- Several rounds of Algorithm 3.5.2 (the Miller–Rabin test, Algorithm 3.5.6 with the
"random" bases supplied by the caller). -/
def millerRabin (n : ℕ) (bases : List ℕ) : Bool :=
  bases.all (strongProbablePrime n)

/-- `b ≡ -1 (mod n)` for a reduced residue `b` means `b = n - 1`. -/
theorem natCast_eq_neg_one_iff {n b : ℕ} (hn : 0 < n) (hb : b < n) :
    (b : ZMod n) = -1 ↔ b = n - 1 := by
  have h1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hn]; simp
  rw [← h1, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]

/-- The loop of Algorithm 3.5.2 looks for `-1` among `b², b⁴, …, b^(2^j)`. -/
theorem sprpLoop_iff {n : ℕ} (hn : 0 < n) (b j : ℕ) :
    sprpLoop n b j = true ↔ ∃ i, 1 ≤ i ∧ i ≤ j ∧ (b : ZMod n) ^ 2 ^ i = -1 := by
  induction j generalizing b with
  | zero => simp only [sprpLoop, Bool.false_eq_true, false_iff]; rintro ⟨i, h₁, h₂, -⟩; omega
  | succ j ih =>
    have hcast : ((b * b % n : ℕ) : ZMod n) = (b : ZMod n) ^ 2 := by
      rw [ZMod.natCast_mod, Nat.cast_mul, sq]
    have hhit : b * b % n = n - 1 ↔ (b : ZMod n) ^ 2 ^ 1 = -1 := by
      rw [pow_one, ← hcast, natCast_eq_neg_one_iff hn (Nat.mod_lt _ hn)]
    simp only [sprpLoop]
    split_ifs with h
    · simp only [true_iff]
      exact ⟨1, le_rfl, by omega, hhit.mp h⟩
    · rw [ih, hcast]
      constructor
      · rintro ⟨i, h₁, h₂, h₃⟩
        exact ⟨i + 1, by omega, by omega, by rw [pow_succ', pow_mul]; exact h₃⟩
      · rintro ⟨i, h₁, h₂, h₃⟩
        obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact absurd (hhit.mpr h₃) h
        · exact ⟨i, hi, by omega, by rw [← pow_mul, ← pow_succ']; exact h₃⟩

/-- **Algorithm 3.5.2 decides condition (3.4).**  With `n - 1 = 2^s t`, the test returns
`true` exactly when `a^t ≡ 1` or `a^(2^i t) ≡ -1 (mod n)` for some `0 ≤ i ≤ s - 1`. -/
theorem strongProbablePrime_iff {n : ℕ} (hn : 2 < n) (hodd : n % 2 = 1) (a : ℕ) :
    strongProbablePrime n a = true ↔
      (a : ZMod n) ^ (oddPart (n - 1)).2 = 1 ∨
        ∃ i < (oddPart (n - 1)).1, (a : ZMod n) ^ (2 ^ i * (oddPart (n - 1)).2) = -1 := by
  have hn0 : 0 < n := by omega
  -- `n - 1 = 2^s t` with `s ≥ 1`, as `n` is odd
  obtain ⟨hst, ht⟩ := oddPart_spec (n := n - 1) (by omega)
  simp only [strongProbablePrime]
  generalize (oddPart (n - 1)).1 = s at hst ⊢
  generalize (oddPart (n - 1)).2 = t at hst ht ⊢
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp at hst; omega
    · exact hs
  have hb : powMod a t n < n := powMod_lt a t hn0
  have hcast : ((powMod a t n : ℕ) : ZMod n) = (a : ZMod n) ^ t := cast_powMod a t n
  have h1 : powMod a t n = 1 ↔ (a : ZMod n) ^ t = 1 := by
    constructor
    · intro h; rw [← hcast, h, Nat.cast_one]
    · intro h
      have h' : ((powMod a t n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
        rw [hcast, h, Nat.cast_one]
      rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (by omega : 1 < n)] at h'
  have hm1 : powMod a t n = n - 1 ↔ (a : ZMod n) ^ t = -1 := by
    rw [← hcast, natCast_eq_neg_one_iff hn0 hb]
  split_ifs with h
  · -- step 1 answered: `a^t = 1`, or `a^t = -1` which is the case `i = 0`
    simp only [true_iff]
    rcases h with h | h
    · exact Or.inl (h1.mp h)
    · exact Or.inr ⟨0, hs, by simpa using hm1.mp h⟩
  · -- step 2: the loop looks at `i = 1, …, s - 1`
    rw [sprpLoop_iff hn0, hcast]
    constructor
    · rintro ⟨i, h₁, h₂, h₃⟩
      exact Or.inr ⟨i, by omega, by rw [mul_comm, pow_mul]; exact h₃⟩
    · rintro (h' | ⟨i, hi, h'⟩)
      · exact absurd (Or.inl (h1.mpr h')) h
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact absurd (Or.inr (hm1.mpr (by simpa using h'))) h
        · exact ⟨i, hi0, by omega, by rw [← pow_mul, mul_comm]; exact h'⟩

/-- **Primes pass Algorithm 3.5.2** (Theorem 3.5.1): if `n` is an odd prime and `n ∤ a`
then `n` is a strong probable prime base `a`.  Equivalently, the answer "`n` is
composite" is always correct, and such an `a` is called a *witness* for `n`. -/
theorem strongProbablePrime_of_prime {n a : ℕ} (hn : n.Prime) (hn2 : n ≠ 2) (ha : ¬n ∣ a) :
    strongProbablePrime n a = true := by
  have : Fact n.Prime := ⟨hn⟩
  have hodd : n % 2 = 1 := hn.eq_two_or_odd.resolve_left hn2
  have h2 : 2 < n := by have := hn.two_le; omega
  rw [strongProbablePrime_iff h2 hodd]
  exact theorem_3_5_1 (oddPart_spec (n := n - 1) (by omega)).1
    (fun h ↦ ha ((ZMod.natCast_eq_zero_iff a n).mp h))

/-- If some base `a` not divisible by the odd number `n > 2` fails Algorithm 3.5.2, then
`n` is composite. -/
theorem not_prime_of_millerRabin {n : ℕ} (hn : 2 < n) {bases : List ℕ}
    (hbases : ∀ a ∈ bases, ¬n ∣ a) (h : millerRabin n bases = false) : ¬n.Prime := by
  intro hp
  rw [millerRabin, List.all_eq_false] at h
  obtain ⟨a, ha, hfail⟩ := h
  exact hfail (strongProbablePrime_of_prime hp (by omega) (hbases a ha))

/-- **Theorem 3.4.6 (Korselt criterion).**  An integer `n` is a Carmichael number if and
only if it is composite (`> 2`), squarefree, and `p - 1 ∣ n - 1` for each prime `p ∣ n`. -/
theorem theorem_3_4_6 {n : ℕ} :
    n.IsCarmichael ↔
      2 < n ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 :=
  Nat.isCarmichael_iff_korselt

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Bit operations -/

/-- The bit operations of `probablePrime n a` (Algorithm 3.4.3): one modular power. -/
def probablePrimeCost (C : CostModel) (n a : ℕ) : ℕ := powModCost C a (n - 1) n

/-- **Bit complexity of the Fermat test**: `O(ln³ n)` with grammar-school arithmetic. -/
theorem probablePrimeCost_school_le {n a : ℕ} (ha : a < n) :
    probablePrimeCost school n a ≤ (4 * Nat.log 2 n + 1) * (n.size + 1) ^ 2 := by
  refine (powModCost_school_le ha (n - 1)).trans (Nat.mul_le_mul_right _ ?_)
  have := Nat.log_mono_right (b := 2) (Nat.sub_le n 1)
  omega

/-- The bit operations of the loop of Algorithm 3.5.2, following `sprpLoop`. -/
def sprpLoopCost (C : CostModel) (n b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    let b' := b * b % n
    C.mul b.size b.size + C.divMod (b * b).size n.size +
      if b' = n - 1 then 0 else sprpLoopCost C n b' j

/-- The bit operations of `strongProbablePrime n a` (Algorithm 3.5.2). -/
def strongProbablePrimeCost (C : CostModel) (n a : ℕ) : ℕ :=
  let st := oddPart (n - 1)
  let b := powMod a st.2 n
  powModCost C a st.2 n + if b = 1 ∨ b = n - 1 then 0 else sprpLoopCost C n b (st.1 - 1)

theorem sprpLoopCost_le (C : CostModel) {n b : ℕ} (hb : b < n) (j : ℕ) :
    sprpLoopCost C n b j ≤ j * C.mulMod n.size := by
  induction j generalizing b with
  | zero => simp [sprpLoopCost]
  | succ j ih =>
    have hstep := mul_add_divMod_le C hb hb
    have ih := ih (b := b * b % n) (Nat.mod_lt _ (by omega))
    simp only [sprpLoopCost, add_mul, one_mul]
    split_ifs <;> omega

/-- **Bit complexity of the strong probable prime test**, for any cost model: with
`n - 1 = 2^s t`, the power `a^t` and the `s - 1` squarings together use at most
`2 log₂ n` modular multiplications. -/
theorem strongProbablePrimeCost_le (C : CostModel) {n a : ℕ} (hn : 1 < n) (ha : a < n) :
    strongProbablePrimeCost C n a ≤
      C.divMod n.size n.size + Nat.log 2 n * (2 * C.mulMod n.size) := by
  obtain ⟨hst, ht⟩ := oddPart_spec (n := n - 1) (by omega)
  simp only [strongProbablePrimeCost]
  generalize (oddPart (n - 1)).1 = s at hst ⊢
  generalize (oddPart (n - 1)).2 = t at hst ht ⊢
  have hpow := powModCost_le C ha t
  have hloop := sprpLoopCost_le C (b := powMod a t n) (powMod_lt _ _ (by omega)) (s - 1)
  -- `log₂ t + s ≤ log₂ n`, because `2^s t = n - 1`
  have hlog : Nat.log 2 t + s ≤ Nat.log 2 n := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have h₁ : 2 ^ Nat.log 2 t ≤ t := Nat.pow_log_le_self 2 (by omega)
    calc 2 ^ (Nat.log 2 t + s) = 2 ^ s * 2 ^ Nat.log 2 t := by rw [pow_add, mul_comm]
      _ ≤ 2 ^ s * t := Nat.mul_le_mul_left _ h₁
      _ ≤ n := by omega
  have hmul : Nat.log 2 t * (2 * C.mulMod n.size) + (s - 1) * C.mulMod n.size ≤
      Nat.log 2 n * (2 * C.mulMod n.size) := by
    have : 2 * Nat.log 2 t + (s - 1) ≤ 2 * Nat.log 2 n := by omega
    calc Nat.log 2 t * (2 * C.mulMod n.size) + (s - 1) * C.mulMod n.size
        = (2 * Nat.log 2 t + (s - 1)) * C.mulMod n.size := by ring
      _ ≤ 2 * Nat.log 2 n * C.mulMod n.size := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  split_ifs <;> omega

/-- **Bit complexity of the strong probable prime test, grammar-school arithmetic**:
at most `(4 log₂ n + 1)(k + 1)²` bit operations, i.e. `O(ln³ n)` per base. -/
theorem strongProbablePrimeCost_school_le {n a : ℕ} (hn : 1 < n) (ha : a < n) :
    strongProbablePrimeCost school n a ≤ (4 * Nat.log 2 n + 1) * (n.size + 1) ^ 2 := by
  refine (strongProbablePrimeCost_le school hn ha).trans ?_
  rw [school_mulMod]
  have : school.divMod n.size n.size = n.size := by simp [school]
  rw [this]
  nlinarith [Nat.zero_le (Nat.log 2 n), Nat.zero_le n.size,
    Nat.zero_le (Nat.log 2 n * n.size)]

end RunningTime

end PrimeNumbers.Chapter3
