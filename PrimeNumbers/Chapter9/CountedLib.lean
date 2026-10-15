import PrimeNumbers.Chapter9.CountedDef

/-!
# Counted versions of library functions

Library functions that do big-number arithmetic are charged, when an algorithm written with
`counted_def` calls them, through a counted version.  Some are given in `Counted.lean` (list
combinators, `List.prod`, array writes); the ones here are written with `counted_def`
itself, mirroring the library's implementation, and proved equal to it.  Algorithm files
import this file (and through it `counted_def`).
-/

namespace PrimeNumbers.Chapter9

/-- `Nat.log.go`, Mathlib's implementation of `Nat.log` by repeated squaring of the base. -/
counted_def logGo (n : ℕ) : (b fuel : ℕ) → ℕ × ℕ
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then (n, 0)
    else
      match logGo n (b * b) fuel with
      | (q, e) => if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

theorem logGo_eq (n b fuel : ℕ) : logGo n b fuel = Nat.log.go n b fuel := by
  induction fuel generalizing b with
  | zero => rw [logGo, Nat.log.go]
  | succ fuel ih => rw [logGo, Nat.log.go, ih]

/-- `⌊log_b n⌋`, as Mathlib computes it. -/
counted_def ilog (b n : ℕ) : ℕ := if b ≤ 1 then 0 else (logGo n b n).2

theorem ilog_eq (b n : ℕ) : ilog b n = Nat.log b n := by
  rw [ilog, Nat.log, logGo_eq]

/-- A call of `Nat.log` in a `counted_def` is charged as Mathlib's implementation. -/
def _root_.Nat.log.counted {m : Type → Type} [Monad m] [NatArith m] (b n : ℕ) : m ℕ :=
  ilog.counted b n

/-- `Nat.clog.go`, Mathlib's implementation of `Nat.clog`. -/
counted_def clogGo (n : ℕ) : (b fuel : ℕ) → ℕ × ℕ
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n ≤ b then (b / n, 0)
    else
      match clogGo n (b * b) fuel with
      | (q, e) => if q < b then (q, 2 * e + 1) else (q / b, 2 * e)

theorem clogGo_eq (n b fuel : ℕ) : clogGo n b fuel = Nat.clog.go n b fuel := by
  induction fuel generalizing b with
  | zero => rw [clogGo, Nat.clog.go]
  | succ fuel ih => rw [clogGo, Nat.clog.go, ih]

/-- `⌈log_b n⌉`, as Mathlib computes it. -/
counted_def iclog (b n : ℕ) : ℕ := if 1 < b ∧ 1 < n then (clogGo n b n).2 + 1 else 0

theorem iclog_eq (b n : ℕ) : iclog b n = Nat.clog b n := by
  rw [iclog, Nat.clog, clogGo_eq]

/-- A call of `Nat.clog` in a `counted_def` is charged as Mathlib's implementation. -/
def _root_.Nat.clog.counted {m : Type → Type} [Monad m] [NatArith m] (b n : ℕ) : m ℕ :=
  iclog.counted b n

theorem logGo_fst_le (n b fuel : ℕ) : (logGo n b fuel).1 ≤ n := by
  induction fuel generalizing b with
  | zero => simp [logGo]
  | succ fuel ih =>
    rw [logGo]
    split_ifs
    · exact le_rfl
    · have := ih (b * b)
      rcases h : logGo n (b * b) fuel with ⟨q, e⟩
      rw [h] at this
      simp only
      split_ifs
      · exact this
      · exact (Nat.div_le_self _ _).trans this

/-- Each level of `logGo` squares the base once and divides once, by numbers `≤ n`; there
are at most `k` levels when `n < b^(2^k)`. -/
theorem logGo_cost_le (C : CostModel) {n : ℕ} (fuel : ℕ) :
    ∀ (b k : ℕ), 2 ≤ b → n < b ^ 2 ^ k →
      costOf C (logGo n b fuel) ≤ k * (C.mul n.size n.size + C.divBound n.size) := by
  induction fuel with
  | zero => intro b k _ _; cost_unfold logGo.counted
  | succ fuel ih =>
    intro b k hb hk
    by_cases hnb : n < b
    · cost_unfold logGo.counted
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hk; omega
        · omega⟩
      have ih := ih (b * b) k (by nlinarith)
        (by rw [← pow_two, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]; exact hk)
      have hq := logGo_fst_le n (b * b) fuel
      have hbn := Nat.size_le_size (not_lt.mp hnb)
      cost_unfold logGo.counted
      rcases h : logGo n (b * b) fuel with ⟨q, e⟩
      rw [h] at hq
      simp only at hq
      have hW₁ := C.mul_le_mul_bound hbn hbn
      have hW₂ := C.divMod_le_divBound (Nat.size_le_size hq) hbn
      simp only [cost_simps]
      split_ifs <;> nlinarith

/-- The charge for `Nat.log b n` (`b ≥ 2`): at most `size n` levels, each a squaring and a
division of numbers `≤ n`. -/
theorem ilog_cost_le (C : CostModel) {b n : ℕ} (hb : 2 ≤ b) :
    costOf C (Nat.log b n) ≤ n.size * (C.mul n.size n.size + C.divBound n.size) := by
  show CostM.cost C (ilog.counted b n) ≤ _
  cost_unfold ilog.counted
  refine logGo_cost_le C n b n.size hb ?_
  calc n < 2 ^ n.size := Nat.lt_size_self n
    _ ≤ b ^ n.size := Nat.pow_le_pow_left hb _
    _ ≤ b ^ 2 ^ n.size := Nat.pow_le_pow_right (by omega) (Nat.lt_two_pow_self).le

theorem clogGo_fst_lt {n : ℕ} (fuel : ℕ) :
    ∀ b, b < n * n → (clogGo n b fuel).1 < n * n := by
  induction fuel with
  | zero => intro b hb; simp only [clogGo]; exact (Nat.div_le_self _ _).trans_lt hb
  | succ fuel ih =>
    intro b hb
    rw [clogGo]
    split_ifs with hnb
    · exact (Nat.div_le_self _ _).trans_lt hb
    · have := ih (b * b) (Nat.mul_lt_mul'' (by omega) (by omega))
      rcases h : clogGo n (b * b) fuel with ⟨q, e⟩
      rw [h] at this
      simp only at this ⊢
      split_ifs
      · exact this
      · exact (Nat.div_le_self _ _).trans_lt this

/-- Each level of `clogGo` squares the base (below `n`) once and divides at most twice, by
numbers below `n²`; there are at most `k + 1` levels when `n ≤ b^(2^k)`. -/
theorem clogGo_cost_le (C : CostModel) {n : ℕ} (fuel : ℕ) :
    ∀ (b k : ℕ), 2 ≤ b → b < n * n → n ≤ b ^ 2 ^ k →
      costOf C (clogGo n b fuel) ≤
        (k + 1) * (C.mul (2 * n.size) (2 * n.size) + 2 * C.divBound (2 * n.size)) := by
  have hsq : ∀ x, x < n * n → x.size ≤ 2 * n.size := fun x hx ↦ by
    have := Nat.size_le_size hx.le; have := size_mul_le n n; omega
  have hn : n.size ≤ 2 * n.size := by omega
  induction fuel with
  | zero =>
    intro b k _ hb _
    have := C.divMod_le_divBound (hsq b hb) hn
    cost_unfold clogGo.counted
    nlinarith
  | succ fuel ih =>
    intro b k hb2 hb hk
    by_cases hnb : n ≤ b
    · have := C.divMod_le_divBound (hsq b hb) hn
      cost_unfold clogGo.counted
      nlinarith
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hk; omega
        · omega⟩
      have hbb : b * b < n * n := Nat.mul_lt_mul'' (by omega) (by omega)
      have ih := ih (b * b) k (by nlinarith) hbb
        (by rw [← pow_two, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]; exact hk)
      have hq := clogGo_fst_lt (n := n) fuel (b * b) hbb
      have hbs := hsq b (by nlinarith)
      have hm := C.mul_le_mul_bound hbs hbs
      cost_unfold clogGo.counted
      rcases h : clogGo n (b * b) fuel with ⟨q, e⟩
      rw [h] at hq
      simp only at hq
      have hd := C.divMod_le_divBound (hsq q hq) hbs
      simp only [cost_simps]
      split_ifs <;> nlinarith

/-- The charge for `Nat.clog 2 n`: at most `size n + 1` levels, each a squaring and at most
two divisions of numbers below `n²`. -/
theorem iclog_cost_le (C : CostModel) (n : ℕ) :
    costOf C (Nat.clog 2 n) ≤
      (n.size + 1) * (C.mul (2 * n.size) (2 * n.size) + 2 * C.divBound (2 * n.size)) := by
  show CostM.cost C (iclog.counted 2 n) ≤ _
  cost_unfold iclog.counted
  split_ifs with h
  · refine clogGo_cost_le C n 2 n.size le_rfl (by nlinarith) ?_
    calc n ≤ 2 ^ n.size := (Nat.lt_size_self n).le
      _ ≤ 2 ^ 2 ^ n.size := Nat.pow_le_pow_right (by omega) (Nat.lt_two_pow_self).le
  · exact Nat.zero_le _

end PrimeNumbers.Chapter9
