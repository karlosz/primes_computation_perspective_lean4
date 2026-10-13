import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter3.TrialDivision
import PrimeNumbers.Chapter3.ProbablePrime
import PrimeNumbers.Chapter4.LucasLehmer
import PrimeNumbers.Chapter4.NMinusOne

/-!
# Bit complexity of the algorithms of Chapters 3 and 4

Using the cost model of `Chapter9/BitCost.lean`.  With `k` the bit length of `n`:

* `trialDivisionCost_school_le` — trial division (Algorithm 3.1.1) factors `n` in at most
  `(2 log₂ n + √n/2 + 1) · k (k + 1)` bit operations: `O(√n ln² n)`.
* `probablePrimeCost_school_le`, `strongProbablePrimeCost_school_le` — the Fermat test
  (Algorithm 3.4.3) and the strong probable prime test (Algorithm 3.5.2) take at most
  `(4 log₂ n + 1)(k + 1)²` bit operations: `O(ln³ n)`.
* `lucasLehmerCost_school_le` — the Lucas–Lehmer test (Algorithm 4.2.7) for `2^p - 1`
  takes at most `(p - 2)(2p² + p)` bit operations: `O(p³)`.

* `pepinCost_school_le` — the Pepin test (Theorem 4.1.2) for `F = F_k` takes at most
  `(4 log₂ F + 1)(size F + 1)²` bit operations.

* `tonelliMults_le` — Tonelli's algorithm 2.3.8 uses at most `6 log₂ t + 4s² + 1` modular
  multiplications, where `p - 1 = 2^s t`: the book's "`O(s² + ln t)` modular operations",
  hence `O(ln⁴ p)` bit operations in the worst case and `O(ln³ p)` when `s` is small.

Each is first stated for an arbitrary `CostModel`.
-/

namespace PrimeNumbers.Chapter9

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3 PrimeNumbers.Chapter4

/-! ## Trial division (Algorithm 3.1.1) -/

/-- The number of divisions made by the inner loop `divideOut d N F`: one divisibility
test per pass, and one more division `N / d` each time the test succeeds. -/
def divideOutOps (d N : ℕ) (F : List ℕ) : ℕ :=
  if 1 < d ∧ 0 < N ∧ d ∣ N then divideOutOps d (N / d) (d :: F) + 2 else 1
termination_by N
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The bit operations of `divideOut d N F`: each of its divisions, at operand size. -/
def divideOutCost (C : CostModel) (d N : ℕ) (F : List ℕ) : ℕ :=
  if 1 < d ∧ 0 < N ∧ d ∣ N then
    divideOutCost C d (N / d) (d :: F) + 2 * C.divMod N.size d.size
  else C.divMod N.size d.size
termination_by N
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The number of divisions made by the main loop `trialLoop d N F`. -/
def trialOps (d N : ℕ) (F : List ℕ) : ℕ :=
  if d * d ≤ N then
    let r := divideOut d N F
    trialOps (d + 2) r.1 r.2 + divideOutOps d N F
  else 0
termination_by N + 2 - d
decreasing_by
  have h₁ : d ≤ d * d := Nat.le_mul_self d
  have h₂ := divideOut_fst_le d N F
  omega

/-- The bit operations of `trialLoop d N F`.  (The test `d² ≤ N` multiplies two numbers of
at most half the length of `N`; it is dominated by the division in the same pass and is
not counted.) -/
def trialCost (C : CostModel) (d N : ℕ) (F : List ℕ) : ℕ :=
  if d * d ≤ N then
    let r := divideOut d N F
    trialCost C (d + 2) r.1 r.2 + divideOutCost C d N F
  else 0
termination_by N + 2 - d
decreasing_by
  have h₁ : d ≤ d * d := Nat.le_mul_self d
  have h₂ := divideOut_fst_le d N F
  omega

/-- The bit operations of `trialDivision n` (Algorithm 3.1.1). -/
def trialDivisionCost (C : CostModel) (n : ℕ) : ℕ :=
  let r := divideOut 2 n []
  divideOutCost C 2 n [] + trialCost C 3 r.1 r.2

/-- Each successful division at least halves `N`: so the divisions of one inner loop
number at most `2 (log₂ N - log₂ N') + 1`, where `N'` is the cofactor left. -/
theorem divideOutOps_add_le (d N : ℕ) (F : List ℕ) :
    divideOutOps d N F + 2 * Nat.log 2 (divideOut d N F).1 ≤ 2 * Nat.log 2 N + 1 := by
  fun_induction divideOutOps d N F with
  | case1 N F h ih =>
    have hdN : d ≤ N := Nat.le_of_dvd h.2.1 h.2.2
    have h₁ : Nat.log 2 (N / d) ≤ Nat.log 2 (N / 2) :=
      Nat.log_mono_right (Nat.div_le_div_left (by omega) (by norm_num))
    have h₂ : Nat.log 2 (N / 2) = Nat.log 2 N - 1 := Nat.log_div_base 2 N
    have h₃ : 0 < Nat.log 2 N := Nat.log_pos (by norm_num) (by omega)
    rw [divideOut]
    simp only [h, and_self, ↓reduceIte]
    omega
  | case2 N F h =>
    rw [divideOut]
    simp only [h, ↓reduceIte]
    omega

/-- All divisions of the main loop: at most `2 log₂ N` successful ones in total, plus one
failed test per pass. -/
theorem trialOps_le (d N : ℕ) (F : List ℕ) :
    trialOps d N F ≤ 2 * Nat.log 2 N + trialSteps d N F := by
  fun_induction trialOps d N F with
  | case1 d N F hle r ih =>
    have h := divideOutOps_add_le d N F
    have hs : trialSteps d N F = trialSteps (d + 2) r.1 r.2 + 1 := by
      rw [trialSteps]; simp [hle, r]
    simp only [r] at ih hs ⊢
    omega
  | case2 d N F hlt => omega

section Bound

variable (C : CostModel) {n B : ℕ}
  (hB : ∀ a b : ℕ, a ≤ n.size → b ≤ n.size → C.divMod a b ≤ B)
include hB

theorem divideOutCost_le {d N : ℕ} (hd : d ≤ n) (hN : N ≤ n) (F : List ℕ) :
    divideOutCost C d N F ≤ divideOutOps d N F * B := by
  have hdiv : ∀ N' ≤ n, C.divMod N'.size d.size ≤ B := fun N' hN' ↦
    hB _ _ (Nat.size_le_size hN') (Nat.size_le_size hd)
  fun_induction divideOutCost C d N F with
  | case1 N F h ih =>
    have ih := ih ((Nat.div_le_self _ _).trans hN)
    have := hdiv N hN
    rw [divideOutOps]
    simp only [h, and_self, ↓reduceIte, add_mul]
    omega
  | case2 N F h =>
    rw [divideOutOps]
    simpa [h] using hdiv N hN

theorem trialCost_le {d N : ℕ} (hN : N ≤ n) (F : List ℕ) :
    trialCost C d N F ≤ trialOps d N F * B := by
  fun_induction trialCost C d N F with
  | case1 d N F hle r ih =>
    have hdN : d ≤ N := (Nat.le_mul_self d).trans hle
    have ih := ih ((divideOut_fst_le d N F).trans hN)
    have := divideOutCost_le C hB (hdN.trans hN) hN F
    rw [trialOps]
    simp only [hle, ↓reduceIte, add_mul, r] at ih ⊢
    omega
  | case2 d N F hlt => simp

/-- **Bit complexity of trial division**, for any cost model: at most
`2 log₂ n + √n/2 + 1` divisions, each of numbers no longer than `n`. -/
theorem trialDivisionCost_le (hn : 2 ≤ n) :
    trialDivisionCost C n ≤ (2 * Nat.log 2 n + Nat.sqrt n / 2 + 1) * B := by
  have h₁ := divideOutCost_le C hB hn le_rfl []
  have h₂ := trialCost_le C hB (divideOut_fst_le 2 n []) (d := 3) (divideOut 2 n []).2
  have h₃ := divideOutOps_add_le 2 n []
  have h₄ := trialOps_le 3 (divideOut 2 n []).1 (divideOut 2 n []).2
  have h₅ := two_mul_trialSteps_le 3 (divideOut 2 n []).1 (divideOut 2 n []).2
  have h₆ : Nat.sqrt (divideOut 2 n []).1 ≤ Nat.sqrt n :=
    Nat.sqrt_le_sqrt (divideOut_fst_le 2 n [])
  have hops : divideOutOps 2 n [] + trialOps 3 (divideOut 2 n []).1 (divideOut 2 n []).2 ≤
      2 * Nat.log 2 n + Nat.sqrt n / 2 + 1 := by omega
  calc trialDivisionCost C n
      ≤ divideOutOps 2 n [] * B +
          trialOps 3 (divideOut 2 n []).1 (divideOut 2 n []).2 * B := by
        simp only [trialDivisionCost]; omega
    _ = (divideOutOps 2 n [] + trialOps 3 (divideOut 2 n []).1 (divideOut 2 n []).2) * B := by
        ring
    _ ≤ _ := Nat.mul_le_mul_right B hops

end Bound

/-- **Bit complexity of trial division, grammar-school arithmetic.**  Algorithm 3.1.1
factors a `k`-bit number `n` in at most `(2 log₂ n + √n/2 + 1) · k (k + 1)` bit
operations, i.e. `O(√n ln² n)`. -/
theorem trialDivisionCost_school_le {n : ℕ} (hn : 2 ≤ n) :
    trialDivisionCost school n ≤
      (2 * Nat.log 2 n + Nat.sqrt n / 2 + 1) * ((n.size + 1) * n.size) :=
  trialDivisionCost_le school (fun a b ha hb ↦ Nat.mul_le_mul (by omega) hb) hn

/-! ## Probable prime tests (Algorithms 3.4.3 and 3.5.2) -/

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

/-! ## Lucas–Lehmer (Algorithm 4.2.7) -/

/-- The bit operations of `lucasLehmerLoop M v k`: a squaring and a reduction per pass. -/
def lucasLehmerCost (C : CostModel) (M v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    C.mul v.size v.size + C.divMod (v * v + M - 2).size M.size +
      lucasLehmerCost C M ((v * v + M - 2) % M) k

theorem lucasLehmerCost_le (C : CostModel) {M v : ℕ} (hv : v < M) (k : ℕ) :
    lucasLehmerCost C M v k ≤ k * C.mulMod M.size := by
  induction k generalizing v with
  | zero => simp [lucasLehmerCost]
  | succ k ih =>
    have ih := ih (v := (v * v + M - 2) % M) (Nat.mod_lt _ (by omega))
    -- `v² + M - 2 < M²`, so it has at most `2 size M` bits
    have hlt : v * v + M - 2 < M * M := by
      obtain ⟨c, rfl⟩ : ∃ c, M = c + 1 := ⟨M - 1, by omega⟩
      have h₁ : v * v ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
      have h₂ : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
      omega
    have hsize : (v * v + M - 2).size ≤ 2 * M.size := by
      have := size_le_of_lt hlt
      have := size_mul_le M M
      omega
    have h₁ : C.mul v.size v.size ≤ C.mul M.size M.size :=
      C.mul_mono (size_le_of_lt hv) (size_le_of_lt hv)
    have h₂ := C.divMod_mono M.size hsize
    simp only [lucasLehmerCost, add_mul, one_mul, CostModel.mulMod] at ih ⊢
    omega

/-- **Bit complexity of the Lucas–Lehmer test, grammar-school arithmetic**: deciding the
primality of `2^p - 1` takes at most `(p - 2)(2p² + p)` bit operations, i.e. `O(p³)`. -/
theorem lucasLehmerCost_school_le {p : ℕ} (hp : 3 ≤ p) :
    lucasLehmerCost school (2 ^ p - 1) 4 (p - 2) ≤ (p - 2) * (2 * p ^ 2 + p) := by
  have h8 : 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  refine (lucasLehmerCost_le school (by omega) (p - 2)).trans (Nat.mul_le_mul_left _ ?_)
  have hsize : (2 ^ p - 1).size ≤ p := Nat.size_le.mpr (by omega)
  rw [school_mulMod]
  nlinarith [Nat.pow_le_pow_left hsize 2]

/-! ## Pepin test (Theorem 4.1.2) -/

/-- The bit operations of `pepin k`: one modular power modulo `F_k`. -/
def pepinCost (C : CostModel) (k : ℕ) : ℕ :=
  let F := 2 ^ 2 ^ k + 1
  powModCost C 3 ((F - 1) / 2) F

/-- **Bit complexity of the Pepin test, grammar-school arithmetic**: cubic in the bit
length of `F_k`. -/
theorem pepinCost_school_le {k : ℕ} (hk : 1 ≤ k) :
    pepinCost school k ≤
      (4 * Nat.log 2 (2 ^ 2 ^ k + 1) + 1) * ((2 ^ 2 ^ k + 1).size + 1) ^ 2 := by
  have h4 : 2 ^ 2 ≤ 2 ^ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) (Nat.one_lt_two_pow (by omega))
  refine (powModCost_school_le (by omega) _).trans (Nat.mul_le_mul_right _ ?_)
  have := Nat.log_mono_right (b := 2) (Nat.div_le_self (2 ^ 2 ^ k + 1 - 1) 2)
  have := Nat.log_mono_right (b := 2) (Nat.sub_le (2 ^ 2 ^ k + 1) 1)
  omega

/-! ## Tonelli (Algorithm 2.3.8) -/

/-- The modular multiplications made by `tonelliLoop A D s i m`: per pass, the power
`D^m`, one product, and the power `(A D^m)^(2^(s-1-i))`. -/
def tonelliLoopMults {p : ℕ} (A D : ZMod p) (s i m : ℕ) : ℕ :=
  if i < s then
    if power (A * power D m) (2 ^ (s - 1 - i)) = -1 then
      tonelliLoopMults A D s (i + 1) (m + 2 ^ i) + (powCost m + 1 + powCost (2 ^ (s - 1 - i)))
    else tonelliLoopMults A D s (i + 1) m + (powCost m + 1 + powCost (2 ^ (s - 1 - i)))
  else 0
termination_by s - i
decreasing_by all_goals omega

/-- The modular multiplications made by `tonelli a d`: the powers `a^t`, `d^t`, the loop,
and the final `a^((t+1)/2) · D^(m/2)`. -/
def tonelliMults {p : ℕ} (a d : ZMod p) : ℕ :=
  let st := oddPart (p - 1)
  let m := tonelliLoop (power a st.2) (power d st.2) st.1 1 0
  2 * powCost st.2 + tonelliLoopMults (power a st.2) (power d st.2) st.1 1 0 +
    (powCost ((st.2 + 1) / 2) + powCost (m / 2) + 1)

/-- In the Tonelli loop the exponent `m` stays below `2^i`, hence below `2^s`. -/
theorem tonelliLoop_lt {p : ℕ} (A D : ZMod p) (s i m : ℕ) (hm : m < 2 ^ i) (his : i ≤ s) :
    tonelliLoop A D s i m < 2 ^ s := by
  fun_induction tonelliLoop A D s i m with
  | case1 i m hlt hz ih => exact ih (by rw [pow_succ]; omega) (by omega)
  | case2 i m hlt hz ih => exact ih (by rw [pow_succ]; omega) (by omega)
  | case3 i m hlt => exact hm.trans_le (Nat.pow_le_pow_right (by norm_num) his)

theorem powCost_le_of_lt_two_pow {m i : ℕ} (hm : m < 2 ^ i) : powCost m ≤ 2 * i := by
  have h₁ := powCost_le m
  have h₂ : Nat.log 2 m ≤ Nat.log 2 (2 ^ i) := Nat.log_mono_right hm.le
  rw [Nat.log_pow (by norm_num)] at h₂
  omega

theorem tonelliLoopMults_le {p : ℕ} (A D : ZMod p) (s i m : ℕ) (hm : m < 2 ^ i)
    (his : i ≤ s) : tonelliLoopMults A D s i m ≤ (s - i) * (4 * s + 1) := by
  have hpass : ∀ i m : ℕ, i < s → m < 2 ^ i →
      powCost m + 1 + powCost (2 ^ (s - 1 - i)) ≤ 4 * s + 1 := by
    intro i m hi hm
    have h₁ := powCost_le_of_lt_two_pow hm
    have h₂ := powCost_le (2 ^ (s - 1 - i))
    rw [Nat.log_pow (by norm_num)] at h₂
    omega
  fun_induction tonelliLoopMults A D s i m with
  | case1 i m hlt hz ih =>
    have ih := ih (by rw [pow_succ]; omega) (by omega)
    have := hpass i m hlt hm
    rw [show s - i = s - (i + 1) + 1 by omega, add_mul, one_mul]
    omega
  | case2 i m hlt hz ih =>
    have ih := ih (by rw [pow_succ]; omega) (by omega)
    have := hpass i m hlt hm
    rw [show s - i = s - (i + 1) + 1 by omega, add_mul, one_mul]
    omega
  | case3 i m hlt => omega

/-- **Complexity of Tonelli's algorithm 2.3.8.**  With `p - 1 = 2^s t`, the algorithm makes
at most `6 log₂ t + 4s² + 1` multiplications modulo `p` — the book's
"`O(s² + ln t)` modular operations".  Each costs at most `C.mulMod (size p)` bit
operations (`mul_add_divMod_le`), so with grammar-school arithmetic the worst case
(`s` large) is `O(ln⁴ p)` and the typical case (`s` small) is `O(ln³ p)`. -/
theorem tonelliMults_le {p : ℕ} (a d : ZMod p) :
    tonelliMults a d ≤
      6 * Nat.log 2 (oddPart (p - 1)).2 + 4 * (oddPart (p - 1)).1 ^ 2 + 1 := by
  simp only [tonelliMults]
  generalize (oddPart (p - 1)).1 = s
  generalize (oddPart (p - 1)).2 = t
  generalize power a t = A
  generalize power d t = D
  have h₁ := powCost_le t
  have h₂ := powCost_le ((t + 1) / 2)
  have h₃ : Nat.log 2 ((t + 1) / 2) ≤ Nat.log 2 t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · exact Nat.log_mono_right (by omega)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- `s = 0`: the loop does not run and `m = 0`
    have h₄ : tonelliLoopMults A D 0 1 0 = 0 := by rw [tonelliLoopMults]; simp
    have h₅ : tonelliLoop A D 0 1 0 = 0 := by rw [tonelliLoop]; simp
    have h₆ : powCost (0 / 2) = 0 := by rw [powCost]; simp
    rw [h₄, h₅, h₆, show (0 : ℕ) ^ 2 = 0 by norm_num]
    omega
  · have h₄ := tonelliLoopMults_le A D s 1 0 (by norm_num) hs
    have h₅ : powCost (tonelliLoop A D s 1 0 / 2) ≤ 2 * s :=
      powCost_le_of_lt_two_pow ((Nat.div_le_self _ _).trans_lt
        (tonelliLoop_lt A D s 1 0 (by norm_num) hs))
    have h₆ : (s - 1) * (4 * s + 1) + 2 * s ≤ 4 * s ^ 2 := by
      obtain ⟨c, rfl⟩ : ∃ c, s = c + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    omega

end PrimeNumbers.Chapter9
