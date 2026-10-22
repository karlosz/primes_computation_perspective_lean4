import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter5.Lehman
import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter9.FastMultipointCost
import PrimeNumbers.Chapter9.NussModel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic

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
counted_def blockProd (n m : ℕ) : ℕ → ℕ
  | 0 => 1 % n
  | i + 1 => blockProd n m i * (m - i) % n

/-- The least `j` (among `fuel` values from `j` on) with `gcd(f(jB), n) > 1`. -/
counted_def findBlock (n B : ℕ) : (j fuel : ℕ) → Option ℕ
  | _, 0 => none
  | j, fuel + 1 =>
    if euclid n (blockProd n (j * B) B) ≠ 1 then some j else findBlock n B (j + 1) fuel

/-- **The Pollard–Strassen polynomial evaluation method** (§5.5): find the least `j` with
`gcd(f(jB), n) > 1`, then the first divisor of `n` in the interval `((j - 1)B, jB]`. -/
counted_def pollardStrassen (n : ℕ) : Option ℕ :=
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

/-! ## Running time (with block-by-block evaluation) -/

section RunningTime

open PrimeNumbers.Chapter9

@[val_le] theorem blockProd_lt {n : ℕ} (hn : 0 < n) (m i : ℕ) : blockProd n m i < n := by
  cases i <;> exact Nat.mod_lt _ hn

/-- One block costs at most `B` multiplications of an `n`-residue by a number `≤ M`, and
two linear operations per factor (and the initial reduction `1 mod n`). -/
@[cost_le] theorem blockProdCost_le (C : CostModel) {n M : ℕ} (hn : 0 < n) {m : ℕ} (hm : m ≤ M) (i : ℕ)
    (hi : i ≤ M) :
    costOf C (blockProd n m i) ≤
      i * (C.mul n.size M.size + C.divMod (n.size + M.size) n.size +
        2 * C.lin (n.size + M.size)) + C.divMod (1 : ℕ).size n.size + C.unit := by
  induction i with
  | zero => cost_unfold blockProd.counted
  | succ i ih =>
    cost_unfold blockProd.counted
    cost_bound

/-- **Bit complexity of the polynomial evaluation method with block-by-block evaluation**,
for any cost model: with `B = ⌊n^{1/4}⌋ + 1`, searching the blocks costs at most
`B · (B · (C.mul + C.divMod + 2L) + G + …)` — `B² ≈ √n` multiplications of an `n`-residue
by a number of at most `2 log₂ B` bits, and `B` gcds with `n`, besides the products `j B`,
the reductions `1 mod n` and the linear work `L` on numbers of `size n + size B²` bits.  The
final scan of one interval adds at most `B` divisions.  With Algorithm 9.6.7 in place of
`blockProd` the `B²` becomes `O(B ln² B)`: see `pollardStrassenFast`. -/
@[cost_le] theorem findBlockCost_le (C : CostModel) {n B : ℕ} (hn : 0 < n)
    (j fuel : ℕ) (hj : j + fuel ≤ B + 1) :
    costOf C (findBlock n B j fuel) ≤
      fuel * (B * (C.mul n.size (B * B).size + C.divMod (n.size + (B * B).size) n.size +
          2 * C.lin (n.size + (B * B).size)) +
        gcdCost C n.size + C.mul (B + 1).size B.size + C.divMod (1 : ℕ).size n.size +
        4 * C.lin (n.size + (B * B).size)) + C.unit := by
  have hBB : B ≤ B * B := Nat.le_mul_self B
  induction fuel generalizing j with
  | zero => cost_unfold findBlock.counted
  | succ fuel ih =>
    have h₁ := blockProdCost_le C hn (M := B * B) (m := j * B)
      (Nat.mul_le_mul_right B (by omega)) B hBB
    cost_unfold findBlock.counted
    rw [euclid_eq_gcd] at *
    split_ifs <;> cost_bound

end RunningTime

/-! ## The method with fast multipoint evaluation

Here `f(t) = t (t - 1) ⋯ (t - B + 1)` is formed once as a polynomial over `Z_n` and
evaluated at all the points `jB`, `j = 1, …, B`, by Algorithm 9.6.7 with fast
multiplication and fast remainder (`multipointEvalFast`), as the book describes. -/

section Fast

open PrimeNumbers.Chapter9

/-- The values `f(jB) mod n`, `j = 1, …, B`, by fast multipoint evaluation. -/
counted_def psValues (n B : ℕ) : List ℕ :=
  (multipointEvalFast n 4 (prodTree (mulMod n) ((List.range B).map ((↑) : ℕ → ZMod n)))
    ((List.range B).map fun j ↦ (((1 + j) * B : ℕ) : ZMod n))).map ZMod.val

/-- The first index (counting from `j`) whose value has a nontrivial gcd with `n`. -/
counted_def findFirst (n : ℕ) : ℕ → List ℕ → Option ℕ
  | _, [] => none
  | j, v :: vs => if euclid n v ≠ 1 then some j else findFirst n (j + 1) vs

/-- **The Pollard–Strassen method with fast polynomial evaluation.** -/
counted_def pollardStrassenFast (n : ℕ) : Option ℕ :=
  let B := iroot 4 n + 1
  match findFirst n 1 (psValues n B) with
  | none => none
  | some j => smallDivisor n (max 2 ((j - 1) * B + 1)) B

theorem findFirst_eq_findBlock (n B j fuel : ℕ) :
    findFirst n j ((List.range fuel).map fun i ↦ blockProd n ((j + i) * B) B) =
      findBlock n B j fuel := by
  induction fuel generalizing j with
  | zero => simp [findFirst, findBlock]
  | succ fuel ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, findFirst, findBlock, add_zero]
    have hl : (List.range fuel).map ((fun i ↦ blockProd n ((j + i) * B) B) ∘ Nat.succ) =
        (List.range fuel).map fun i ↦ blockProd n ((j + 1 + i) * B) B :=
      List.map_congr_left fun x _ ↦ by
        simp only [Function.comp_apply, Nat.succ_eq_add_one, show j + (x + 1) = j + 1 + x by ring]
    rw [hl, ih (j + 1)]

theorem cast_blockProd {n : ℕ} (m i : ℕ) :
    ((blockProd n m i : ℕ) : ZMod n) = ((List.range i).map fun e ↦ ((m - e : ℕ) : ZMod n)).prod := by
  induction i with
  | zero => simp [blockProd]
  | succ i ih => rw [blockProd, ZMod.natCast_mod, Nat.cast_mul, ih, List.range_succ]; simp

/-- Fast evaluation produces exactly the block products `f(jB) mod n`. -/
theorem psValues_eq {n : ℕ} (hn : 1 < n) (B : ℕ) :
    psValues n B = (List.range B).map fun i ↦ blockProd n ((1 + i) * B) B := by
  have : Fact (1 < n) := ⟨hn⟩
  have : NeZero n := ⟨by omega⟩
  rw [psValues, multipointEvalFast_eq, List.map_map, List.map_map]
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Function.comp_apply]
  rw [(prodTree_spec (mulCorrect_mulMod n) _).1, eval_prodLinear, List.map_map]
  have hcast : ((List.range B).map ((fun u ↦ (((1 + j) * B : ℕ) : ZMod n) - u) ∘
      ((↑) : ℕ → ZMod n))).prod = ((blockProd n ((1 + j) * B) B : ℕ) : ZMod n) := by
    rw [cast_blockProd]
    congr 1
    refine List.map_congr_left fun e he ↦ ?_
    have : e ≤ (1 + j) * B := by
      have := List.mem_range.mp he
      nlinarith
    simp [Nat.cast_sub this]
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (blockProd_lt (by omega) _ _)]

/-- **The fast method computes the same answer**, so `pollardStrassen_eq` applies: for
composite `n > 1` it returns the least prime factor. -/
theorem pollardStrassenFast_eq {n : ℕ} (hn : 1 < n) :
    pollardStrassenFast n = pollardStrassen n := by
  simp only [pollardStrassenFast, pollardStrassen, psValues_eq hn,
    findFirst_eq_findBlock n _ 1]

theorem pollardStrassenFast_eq_minFac {n : ℕ} (hn : 1 < n) (hnp : ¬n.Prime) :
    pollardStrassenFast n = some n.minFac := by
  rw [pollardStrassenFast_eq hn, pollardStrassen_eq hn hnp]

end Fast

/-! ## Running time of the fast method: the book's `O(n^{1/4})` -/

section RunningTimeFast

open PrimeNumbers.Chapter9

theorem findFirst_lt {n j : ℕ} {vs : List ℕ} {i : ℕ} (h : findFirst n j vs = some i) :
    i < j + vs.length := by
  induction vs generalizing j with
  | nil => simp [findFirst] at h
  | cons v vs ih =>
    rw [findFirst] at h
    split_ifs at h
    · cases h; simp
    · have := ih h; simp only [List.length_cons]; omega

/-- The gcd scan: one gcd with `n` per value, and three linear operations. -/
@[cost_le] theorem findFirst_cost_le (C : CostModel) {n K : ℕ} (hn : n.size ≤ K) (hn0 : 0 < n) (j : ℕ)
    (vs : List ℕ) (hv : ∀ v ∈ vs, v.size ≤ K) (hj : (j + vs.length).size ≤ K) :
    costOf C (findFirst n j vs) ≤ vs.length * (gcdCost C K + 3 * C.lin K) + C.unit := by
  induction vs generalizing j with
  | nil => cost_unfold findFirst.counted
  | cons v vs ih =>
    have ih := ih (j + 1) (fun w hw ↦ hv w (by simp [hw]))
      ((Nat.size_le_size (by simp; omega)).trans hj)
    have := gcd_cost_le C hn (hv v (by simp))
    cost_unfold findFirst.counted
    rw [euclid_eq_gcd] at *
    split_ifs <;> cost_bound

theorem psValues_length (n B : ℕ) : (psValues n B).length = B := by
  simp [psValues, multipointEvalFast, length_multipointEvalWith]

/-- The bound of `psValues_cost_le`: the product tree for `f`, the `B` points `jB`, and fast
multipoint evaluation (`multipointEvalFast_cost_le`), with the bookkeeping on numbers of
`K = size (B + 6)` bits. -/
def psValuesBound (C : CostModel) (n B : ℕ) : ℕ :=
  (Nat.clog 2 B + 1) * (polyMulBound C n B + 8 * B * C.lin (B + 4 + 2).size) +
    B * (40 * (C.unit + zcost C n)) +
    (Nat.clog 2 B + 1) * nodeBound C n 4 (B + 4 + 2).size B + 7 * C.lin (B + 4 + 2).size +
    B * (C.mul (B + 4 + 2).size (B + 4 + 2).size + C.divMod (B + 4 + 2).size n.size +
      C.divMod (2 * (B + 4 + 2).size) n.size + 6 * C.lin (2 * (B + 4 + 2).size)) +
    6 * C.lin (2 * (B + 4 + 2).size)

/-- **The values `f(jB) mod n` by fast polynomial arithmetic**: the product tree for
`f(t) = t (t - 1) ⋯ (t - B + 1)`, the `B` points `jB`, and fast multipoint evaluation. -/
@[cost_le] theorem psValues_cost_le (C : CostModel) (hC : C.SuperadditiveMul) {n : ℕ} [NeZero n]
    {B : ℕ} (hB : 1 ≤ B) : costOf C (psValues n B) ≤ psValuesBound C n B := by
  set K := (B + 4 + 2).size
  have h2K : 2 ≤ K := by
    have := Nat.size_le_size (show 2 ≤ B + 4 + 2 by omega); rwa [Nat.size_two] at this
  have hBK : B.size ≤ K := Nat.size_le_size (by omega)
  have h₁ := prodTree_cost_le C (mulF := mulMod n) _
    (fun a b ↦ polyMulBound_superadditive C n hC) (mulMod_charge_le C n)
    (show ArithCost.Bounded (ZMod n) C (zcost C n) from ArithCost.bounded_zmod C n) h2K
    ((List.range B).map ((↑) : ℕ → ZMod n)) (by simp; omega) (by simpa using hBK)
  have h₂ : (List.map (fun a => C.add 1 a.size + (C.mul (1 + a).size B.size +
      C.divMod ((1 + a) * B).size n.size)) (List.range B)).sum ≤
      B * (C.mul K K + C.divMod (2 * K) n.size + C.lin (2 * K)) := by
    simpa using sum_map_le_length_mul (List.range B) (fun a => C.add 1 a.size +
      (C.mul (1 + a).size B.size + C.divMod ((1 + a) * B).size n.size)) fun a ha ↦ by
      have ha := List.mem_range.1 ha
      have s₁ : (1 + a).size ≤ K := Nat.size_le_size (by omega)
      have s₂ : ((1 + a) * B).size ≤ 2 * K := (size_mul_le _ _).trans (by omega)
      have s₃ : a.size ≤ 2 * K := (Nat.size_le_size (show a ≤ B + 4 + 2 by omega)).trans (by omega)
      have := C.mul_mono s₁ hBK
      have := C.divMod_mono n.size s₂
      have : (Nat.size 1) ≤ 2 * K := by simp; omega
      cost_bound
  have h₃ : (List.map (fun a => C.divMod a.size n.size) (List.range B)).sum ≤
      B * C.divMod K n.size := by
    simpa using sum_map_le_length_mul (List.range B) _ fun a ha ↦
      C.divMod_mono n.size (Nat.size_le_size (show a ≤ B + 4 + 2 by simp at ha; omega))
  have h₄ := multipointEvalFast_cost_le C hC 4
    (prodTree (mulMod n) ((List.range B).map ((↑) : ℕ → ZMod n)))
    ((List.range B).map fun j ↦ (((1 + j) * B : ℕ) : ZMod n))
    (by simpa using length_prodTree_le (mulMod n) ((List.range B).map ((↑) : ℕ → ZMod n)))
  simp only [List.length_map, List.length_range] at h₁ h₄
  have hl : (multipointEvalFast n 4 (prodTree (mulMod n) (List.map Nat.cast (List.range B)))
      (List.map (fun j => ((((1 + j) * B : ℕ)) : ZMod n)) (List.range B))).length = B := by
    simp [multipointEvalFast, length_multipointEvalWith]
  unfold psValuesBound
  cost_unfold psValues.counted
  rw [hl, List.length_range]
  cost_bound

/-- **Running time of the Pollard–Strassen method with fast polynomial arithmetic (§5.5)**,
for any cost model with superadditive multiplication: with `B = ⌊n^{1/4}⌋ + 1` and `k` the
bit length of `n`, the cost is at most
* `B` fourth powers for computing `⌊n^{1/4}⌋`,
* the product tree for `f(t) = t (t - 1) ⋯ (t - B + 1)` and `B` small products for the points,
* fast multipoint evaluation of `f` at the `B` points `jB` (`multipointEvalFast_cost_le`),
* `B` gcds with `n`, and the final scan of one interval of length `B`.
With products of length-`m` polynomials costing `M(m (k + log m))` bit operations
(`polyMulBound`), this is `O(M(n^{1/4} log n) log² n)` — the book's `O(n^{1/4})` up to
logarithmic factors with a quasi-linear multiplication. -/
@[cost_le] theorem pollardStrassenFast_cost_le (C : CostModel) (hC : C.SuperadditiveMul) {n : ℕ}
    (hn : 1 < n) {B : ℕ} (hB : iroot 4 n + 1 = B) :
    costOf C (pollardStrassenFast n) ≤
      B * (3 * C.mul (n.size + 4) (n.size + 4)) + psValuesBound C n B +
        B * gcdCost C (n + B * B + B + 2).size + C.mul B.size B.size +
        B * C.divBound (n + B * B + B + 2).size + (9 * B + 12) * C.lin ((n + B * B + B + 2).size + 1) := by
  have : NeZero n := ⟨by omega⟩
  set W := (n + B * B + B + 2).size with hWdef
  have hW : ∀ x, x ≤ n + B * B + B + 2 → x.size ≤ W := fun x hx ↦ Nat.size_le_size hx
  have h₀ := iroot4_cost_le C n
  have hv : ∀ v ∈ psValues n B, v.size ≤ W := by
    intro v hv
    rw [psValues_eq hn] at hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    exact hW _ ((blockProd_lt (show 0 < n by omega) _ _).le.trans (by omega))
  have h₂ := findFirst_cost_le C (hW n (by omega)) (by omega) 1 (psValues n B) hv
    (hW _ (by rw [psValues_length]; omega))
  rw [psValues_length] at h₂
  rw [hB] at h₀
  have := hW (iroot 4 n) (by omega); have := hW B (by omega); have := hW (iroot 4 n + 1) (by omega)
  cost_unfold pollardStrassenFast.counted
  rw [hB]
  rcases hf : findFirst n 1 (psValues n B) with _ | j
  · simp only [cost_simps]
    cost_bound
  · have hj := findFirst_lt hf
    rw [psValues_length] at hj
    have hd := smallDivisor_cost_le C (n := n) (N := n + B * B + B + 2) (by omega) B
      (max 2 ((j - 1) * B + 1)) (by
        have : (j - 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
        omega)
    have := hW j (by omega); have := hW (j - 1) (by omega)
    have := hW ((j - 1) * B) (by have : (j - 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega); omega)
    have := hW ((j - 1) * B + 1) (by have : (j - 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega); omega)
    simp only [cost_simps]
    cost_bound

end RunningTimeFast

section QuasiLinear

open PrimeNumbers.Chapter9 PrimeNumbers.Chapter2

/-! ### With Nussbaumer multiplication: the closed form -/

@[simp] theorem nussModel_unit : nussModel.unit = 1 := rfl
@[simp] theorem nussModel_add (a b : ℕ) : nussModel.add a b = max a b + 1 := by
  simp [CostModel.add, nussModel]
@[simp] theorem nussModel_lin (k : ℕ) : nussModel.lin k = k + 2 := by
  simp only [CostModel.lin, nussModel_add, nussModel_unit, max_self]; omega
theorem nussModel_divMod (a b : ℕ) : nussModel.divMod a b = (a - b + 1) * b := rfl

theorem nussModel_superadditiveMul : nussModel.SuperadditiveMul := fun a b ↦ by
  simp only [nussModel_mul, max_self]
  have ha := Nat.size_le_size (Nat.le_add_right a b)
  have hb := Nat.size_le_size (Nat.le_add_left b a)
  cost_bound

/-- A gcd costs the same in every model with the same divisions and linear operations. -/
theorem euclid_cost_congr {C D : CostModel} (h : C.divMod = D.divMod) (hu : C.unit = D.unit)
    (ha : C.addRate = D.addRate) (x y : ℕ) : costOf C (euclid x y) = costOf D (euclid x y) := by
  fun_induction euclid x y with
  | case1 x y hy ih => cost_unfold_both euclid.counted; simp only [CostModel.add, h, hu, ha, ih]
  | case2 x y hy => cost_unfold_both euclid.counted; simp only [CostModel.add, hu, ha]

theorem gcdCost_nussModel (k : ℕ) : gcdCost nussModel k = gcdCost school k := by
  unfold gcdCost; congr 1; funext x y
  exact euclid_cost_congr (C := nussModel) (D := school) rfl rfl rfl x y

theorem nussModel_divBound_le (k : ℕ) : nussModel.divBound k ≤ (k + 1) * k :=
  school_divBound_le k

theorem size_mul_const_le {c S : ℕ} : (c * S).size ≤ c.size + S :=
  (size_mul_le c S).trans (by have := Chapter9.size_le_self S; omega)

/-- A product of small numbers (at most `10 S` bits). -/
theorem nussModel_mul_small {a S : ℕ} (hS : 8 ≤ S) (ha : a ≤ 10 * S) :
    nussModel.mul a a ≤ 2 ^ 29 * S ^ 5 := by
  simp only [nussModel_mul, max_self]
  have h₁ : a.size + 3 ≤ 3 * S := by
    have := (Nat.size_le_size ha).trans (size_mul_const_le (c := 10))
    rw [show Nat.size 10 = 4 by decide] at this; omega
  calc 360000 * a * (a.size + 3) ^ 4 ≤ 360000 * (10 * S) * (3 * S) ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) (Nat.pow_le_pow_left h₁ 4)
    _ ≤ 2 ^ 29 * S ^ 5 := by ring_nf; omega

/-- A product of large numbers (at most `20 S B` bits, with `B` of at most `S` bits). -/
theorem nussModel_mul_large {a S B : ℕ} (hS : 8 ≤ S) (hB : B.size ≤ S) (ha : a ≤ 20 * S * B) :
    nussModel.mul a a ≤ 2 ^ 31 * (B * S ^ 5) := by
  simp only [nussModel_mul, max_self]
  have h₁ : a.size + 3 ≤ 4 * S := by
    have := (Nat.size_le_size ha).trans (size_mul_le (20 * S) B)
    have := size_mul_const_le (c := 20) (S := S)
    rw [show Nat.size 20 = 5 by decide] at this; omega
  calc 360000 * a * (a.size + 3) ^ 4 ≤ 360000 * (20 * S * B) * (4 * S) ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) (Nat.pow_le_pow_left h₁ 4)
    _ ≤ 2 ^ 31 * (B * S ^ 5) := by ring_nf; omega

theorem pow_le_pow_five {S j : ℕ} (hS : 1 ≤ S) (hj : j ≤ 5) : S ^ j ≤ S ^ 5 :=
  Nat.pow_le_pow_right hS hj

theorem nussModel_mulMod_le {k S : ℕ} (hS : 8 ≤ S) (hk : k + 1 ≤ S) :
    nussModel.mulMod k ≤ 2 ^ 30 * S ^ 5 := by
  have h₁ := nussModel_mul_small (a := k) hS (by omega)
  have h₃ : (2 * k - k + 1) * k ≤ S ^ 5 := by
    calc (2 * k - k + 1) * k ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
      _ = S ^ 2 := by ring
      _ ≤ S ^ 5 := pow_le_pow_five (by omega) (by norm_num)
  simp only [CostModel.mulMod, nussModel_divMod]
  omega

theorem zcost_nussModel_le {n S : ℕ} (hS : 8 ≤ S) (hn : n.size + 1 ≤ S) :
    zcost nussModel n ≤ 2 ^ 31 * S ^ 5 := by
  have := nussModel_mulMod_le hS hn
  have : 2 * (n.size + 1) ≤ S ^ 5 := by
    have h₂ := pow_le_pow_five (S := S) (by omega) (show 2 ≤ 5 by norm_num)
    rw [sq] at h₂
    have : 2 * S ≤ S * S := Nat.mul_le_mul_right _ (by omega)
    omega
  unfold zcost; simp only [nussModel_add, max_self]; omega

theorem halvingBound_le_mul {c d N : ℕ} (hN : 1 ≤ N) :
    halvingBound c d N ≤ N * (c * Nat.clog 2 N + 2 * d) := by
  unfold halvingBound
  rw [show max N 1 = N by omega]
  have : d * (2 * N - 1) ≤ d * (2 * N) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

theorem polyMulBound_nussModel_le {n m B S : ℕ} (hS : n.size + 3 ≤ S) (h8 : 8 ≤ S)
    (hB : B.size ≤ n.size) (hm1 : 1 ≤ m) (hm : m ≤ 4 * B) :
    polyMulBound nussModel n m ≤ 2 ^ 36 * (B * S ^ 5) := by
  have hw : segWidth n m + 4 ≤ 5 * S := by
    have := (Nat.size_le_size hm).trans (size_mul_le 4 B)
    rw [show Nat.size 4 = 3 by decide] at this; unfold segWidth; omega
  unfold polyMulBound
  generalize segWidth n m = w at hw ⊢
  have hw' : w ≤ 5 * S := by omega
  have h₁ := nussModel_mul_large (a := w * m) (S := S) (B := B) h8 (by omega) (by
    calc w * m ≤ 5 * S * (4 * B) := Nat.mul_le_mul (by omega) hm
      _ = 20 * S * B := by ring)
  have h₂ := nussModel_mul_small (a := 2 * w) (S := S) h8 (by omega)
  have h₂' : nussModel.mul w.size (2 * w) ≤ 2 ^ 29 * S ^ 5 := by
    refine le_trans (nussModel.mul_mono ?_ le_rfl) h₂
    have := Chapter9.size_le_self w; omega
  have hcl : Nat.clog 2 (2 * m) ≤ S := by
    have : 2 * m ≤ 2 ^ (n.size + 3) := by
      have := Nat.lt_size_self B
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hB
      rw [pow_add]; omega
    have := Nat.clog_le_of_le_pow this; omega
  have hH := halvingBound_le_mul (c := 2 * nussModel.unit + 6 * nussModel.add (2 * w) (2 * w))
    (d := 4 * nussModel.unit + 4 * nussModel.add (2 * w) (2 * w) + nussModel.mul w.size (2 * w))
    (show 1 ≤ 2 * m by omega)
  simp only [nussModel_lin, nussModel_unit, nussModel_add, nussModel_divMod, max_self] at hH ⊢
  cost_bound

theorem clogBound_nussModel_le {z S : ℕ} (hS : 8 ≤ S) (hz : 2 * z + 1 ≤ 10 * S) :
    clogBound nussModel z ≤ 2 ^ 30 * S ^ 5 := by
  have h₁ := nussModel_mul_small (a := 2 * z) hS (by omega)
  have h₂ := nussModel_divBound_le (2 * z)
  have h₃ : (2 * z + 1) * (2 * z) ≤ 100 * S ^ 2 := by
    calc (2 * z + 1) * (2 * z) ≤ (10 * S) * (10 * S) := Nat.mul_le_mul (by omega) (by omega)
      _ = 100 * S ^ 2 := by ring
  have h₄ : S ^ 2 ≤ S ^ 5 := pow_le_pow_five (by omega) (by norm_num)
  have h₅ : S ≤ S ^ 5 := by simpa using pow_le_pow_five (S := S) (j := 1) (by omega) (by norm_num)
  unfold clogBound; simp only [nussModel_lin]
  omega

/-- **The Pollard–Strassen method with Nussbaumer multiplication** (Theorem 5.5.3): at most
`2^45 (⌊n^{1/4}⌋ + 1) (log₂ n + 8)⁷` bit operations, i.e. `O(n^{1/4} log⁷ n)`. -/
@[cost_le] theorem pollardStrassenFast_cost_nuss {n : ℕ} (hn : 1 < n) :
    costOf nussModel (pollardStrassenFast n) ≤ 2 ^ 45 * (iroot 4 n + 1) * (n.size + 8) ^ 7 := by
  have h := pollardStrassenFast_cost_le nussModel nussModel_superadditiveMul hn rfl
  set B := iroot 4 n + 1 with hBdef
  set s := n.size
  set S := s + 8 with hSdef
  have hs : 2 ≤ s := by
    have := Nat.lt_size.2 (show 2 ^ 1 ≤ n by omega); omega
  have hS1 : 1 ≤ S := by omega
  have hBn : B ≤ n := by
    have h4 := iroot_pow_le (by norm_num : (4 : ℕ) ≠ 0) n
    rcases Nat.lt_or_ge (iroot 4 n) 2 with h0 | h0
    · omega
    · have h3 := Nat.pow_le_pow_left h0 3
      have : iroot 4 n ^ 4 = iroot 4 n * iroot 4 n ^ 3 := by ring
      nlinarith
  have hB1 : 1 ≤ B := by omega
  have hBs : B.size ≤ s := Nat.size_le_size hBn
  have hclog : Nat.clog 2 B ≤ s :=
    (Nat.clog_le_of_le_pow (Nat.lt_size_self B).le).trans hBs
  have h8 : 8 ≤ S := by omega
  set K := (B + 4 + 2).size with hKdef
  have hKs : K ≤ s + 3 := by
    have := Nat.size_le_size (show B + 4 + 2 ≤ 4 * n by omega)
    have := size_mul_le 4 n; rw [show Nat.size 4 = 3 by decide] at this; omega
  have h4B : (4 * B).size + 4 ≤ S := by
    have := size_mul_le 4 B; rw [show Nat.size 4 = 3 by decide] at this; omega
  have h2B : (2 * B).size ≤ s + 2 := by
    have := size_mul_le 2 B; rw [show Nat.size 2 = 2 by decide] at this; omega
  -- the pieces, polynomials in `B` and `S`
  have hP1 := polyMulBound_nussModel_le (n := n) (m := B) (S := S) (by omega) h8 hBs hB1 (by omega)
  have hP4 := polyMulBound_nussModel_le (n := n) (m := 4 * B) (S := S) (by omega) h8 hBs
    (by omega) le_rfl
  have hz := zcost_nussModel_le (n := n) h8 (by omega)
  have hcb := clogBound_nussModel_le (z := (2 * B).size) h8 (by omega)
  have hW : (n + B * B + B + 2).size ≤ s + 4 := by
    have h4 := iroot_pow_le (by norm_num : (4 : ℕ) ≠ 0) n
    have : B * B ≤ 4 * n := by
      rcases Nat.eq_zero_or_pos (iroot 4 n) with h0 | h0
      · simp only [hBdef, h0]; omega
      · have : iroot 4 n * iroot 4 n ≤ iroot 4 n ^ 4 := by nlinarith [Nat.mul_le_mul h0 h0]
        nlinarith
    have := Nat.size_le_size (show n + B * B + B + 2 ≤ 8 * n by omega)
    have := size_mul_le 8 n; rw [show Nat.size 8 = 4 by decide] at this; omega
  have hm := nussModel_mul_small (a := 10 * S) h8 le_rfl
  have hg : gcdCost nussModel (n + B * B + B + 2).size ≤
      (n + B * B + B + 2).size * (3 * (n + B * B + B + 2).size + 6) + 6 := by
    rw [gcdCost_nussModel]; exact gcdCost_school_le _
  have hd := nussModel_divBound_le (n + B * B + B + 2).size
  unfold psValuesBound nodeBound nodeInner at h
  simp only [nussModel_lin, nussModel_unit, nussModel_divMod] at h
  generalize (n + B * B + B + 2).size = W at *
  clear_value B S
  cost_bound

end QuasiLinear

end PrimeNumbers.Chapter5
