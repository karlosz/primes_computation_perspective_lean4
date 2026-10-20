import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter9.IntSqrt
import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power

/-!
# §5.3 Baby-steps, giant-steps

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.3.

* `bsgs` — Algorithm 5.3.1 (baby-steps, giant-steps for discrete logarithms) in the group
  `Z_p^*`, with residues as naturals and the baby steps stored in a hash table, as the
  book's remark after the algorithm suggests ("it is not necessary to sort both lists").
* `bsgs_sound` — a returned `l` satisfies `g^l ≡ t (mod p)`.

* `bsgs_complete` — if `t ≡ g^l (mod p)` for some `l ≤ n` (as is the case when `t` is a
  power of `g` and `n` bounds the order of `g`), the algorithm returns an answer.
* `bsgsCost_le` — at most `2b + 2 log₂ b` modular multiplications, `b = ⌊√n⌋ + 1`.
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2

/-- Step 2, list `A`: insert `gⁱ ↦ i` for `count` consecutive `i`, where `cur = gⁱ mod p`. -/
counted_def babyTable (p g : ℕ) : (i cur count : ℕ) → Std.HashMap ℕ ℕ → Std.HashMap ℕ ℕ
  | _, _, 0, m => m
  | i, cur, count + 1, m => babyTable p g (i + 1) (cur * g % p) count (m.insert cur i)

/-- Step 2–3, list `B`: for `count` consecutive `j`, with `y = t hʲ mod p`, look `y` up
among the baby steps; a hit `y = gⁱ` gives `l = i + j b`. -/
counted_def giantLoop (p b h : ℕ) (m : Std.HashMap ℕ ℕ) : (j y count : ℕ) → Option ℕ
  | _, _, 0 => none
  | j, y, count + 1 =>
    match m[y]? with
    | some i => some (i + j * b)
    | none => giantLoop p b h m (j + 1) (y * h % p) count

/-- **Algorithm 5.3.1 (Baby-steps, giant-steps for discrete logarithms)** in `Z_p^*`.
Given a generator `g`, an upper bound `n` for its order, and `t`, returns `l` with
`g^l = t`.
```
b = ⌈√n⌉;   h = (g⁻¹)^b;
A = {gⁱ : i = 0, 1, …, b - 1};   B = {t hʲ : j = 0, 1, …, b - 1};
Find an intersection, say gⁱ = t hʲ;   return l = i + j b;
```
-/
counted_def bsgs (p g t n : ℕ) : Option ℕ :=
  let b := Nat.sqrt n + 1
  let h := powMod (modInv g p) b p
  let m := babyTable p g 0 (1 % p) b ∅
  giantLoop p b h m 0 (t % p) b

/-- Every entry `y ↦ k` of the baby-step table satisfies `g^k mod p = y`. -/
theorem babyTable_spec (p g : ℕ) (i cur count : ℕ) (m : Std.HashMap ℕ ℕ)
    (hcur : cur = g ^ i % p) (hm : ∀ y k, m[y]? = some k → g ^ k % p = y) :
    ∀ y k, (babyTable p g i cur count m)[y]? = some k → g ^ k % p = y := by
  induction count generalizing i cur m with
  | zero => simpa [babyTable] using hm
  | succ count ih =>
    refine ih (i + 1) _ _ ?_ ?_
    · rw [hcur, pow_succ, Nat.mod_mul_mod]
    · intro y k hk
      rw [Std.HashMap.getElem?_insert] at hk
      split_ifs at hk with heq
      · obtain rfl := Option.some.inj hk
        rw [← hcur]
        simpa using heq
      · exact hm y k hk

theorem giantLoop_spec {p b h : ℕ} {m : Std.HashMap ℕ ℕ} {j y count l : ℕ}
    (hl : giantLoop p b h m j y count = some l) :
    ∃ i j' y', l = i + j' * b ∧ m[y']? = some i ∧ ∃ c, j' = j + c ∧ y' % p = y * h ^ c % p := by
  induction count generalizing j y with
  | zero => simp [giantLoop] at hl
  | succ count ih =>
    simp only [giantLoop] at hl
    split at hl
    · rename_i i hi
      exact ⟨i, j, y, (Option.some.inj hl).symm, hi, 0, rfl, by simp⟩
    · obtain ⟨i, j', y', h₁, h₂, c, h₃, h₄⟩ := ih hl
      refine ⟨i, j', y', h₁, h₂, c + 1, by omega, ?_⟩
      rw [h₄, pow_succ', ← mul_assoc, Nat.mul_mod (y * h % p), Nat.mod_mod, ← Nat.mul_mod]

/-- **Soundness of Algorithm 5.3.1**: if `g` is invertible modulo `p` and the algorithm
returns `l`, then `g^l ≡ t (mod p)`. -/
theorem bsgs_sound {p g t n l : ℕ} (hg : Nat.Coprime g p) (h : bsgs p g t n = some l) :
    g ^ l ≡ t [MOD p] := by
  obtain ⟨i, j, y, rfl, hmem, c, rfl, hy⟩ := giantLoop_spec h
  have hi := babyTable_spec p g 0 (1 % p) (Nat.sqrt n + 1) ∅ (by simp)
    (fun y k hk ↦ by simp at hk) y i hmem
  -- in `ZMod p`: `g^i = t h^j` and `h g^b = 1`
  rw [zero_add, ← ZMod.natCast_eq_natCast_iff]
  have hinv : (g : ZMod p) * (modInv g p : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (mul_modInv_modEq hg)
    simpa using this
  have hy' : ((g ^ i : ℕ) : ZMod p) =
      (t : ZMod p) * ((powMod (modInv g p) (Nat.sqrt n + 1) p : ℕ) : ZMod p) ^ c := by
    have h₁ : ((g ^ i % p : ℕ) : ZMod p) = ((y % p : ℕ) : ZMod p) := by rw [hi, ZMod.natCast_mod]
    rw [hy, ZMod.natCast_mod, ZMod.natCast_mod] at h₁
    simpa using h₁
  rw [cast_powMod] at hy'
  push_cast at hy' ⊢
  rw [pow_add, hy', pow_mul', mul_assoc, ← mul_pow, ← mul_pow, mul_comm (modInv g p : ZMod p),
    hinv, one_pow, one_pow, mul_one]

/-! ## Completeness -/

/-- The baby-step table keeps what it had and contains every `g^(i+k) mod p`, `k < count`. -/
theorem babyTable_mem (p g : ℕ) (i cur count : ℕ) (m : Std.HashMap ℕ ℕ)
    (hcur : cur = g ^ i % p) :
    (∀ y : ℕ, (m[y]?).isSome → ((babyTable p g i cur count m)[y]?).isSome) ∧
      ∀ k < count, ((babyTable p g i cur count m)[g ^ (i + k) % p]?).isSome := by
  induction count generalizing i cur m with
  | zero => exact ⟨fun y h ↦ by simpa [babyTable] using h, fun k hk ↦ by omega⟩
  | succ count ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (i + 1) (cur * g % p) (m.insert cur i)
      (by rw [hcur, pow_succ, Nat.mod_mul_mod])
    have hins : ∀ y : ℕ, (m[y]?).isSome → ((m.insert cur i)[y]?).isSome := by
      intro y hy
      rw [Std.HashMap.getElem?_insert]
      split_ifs
      · rfl
      · exact hy
    refine ⟨fun y hy ↦ ih₁ y (hins y hy), fun k hk ↦ ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ih₁ _ ?_
      rw [add_zero, ← hcur, Std.HashMap.getElem?_insert]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have := ih₂ k (by omega)
      rwa [show i + 1 + k = i + (k + 1) by ring] at this

/-- The giant-step loop stops as soon as some `y hᶜ mod p` is in the table. -/
theorem giantLoop_isSome {p b h : ℕ} (m : Std.HashMap ℕ ℕ) (j y count : ℕ) (hy : y < p)
    (hex : ∃ c < count, (m[y * h ^ c % p]?).isSome) :
    (giantLoop p b h m j y count).isSome := by
  induction count generalizing j y with
  | zero => obtain ⟨c, hc, -⟩ := hex; omega
  | succ count ih =>
    simp only [giantLoop]
    split
    · rfl
    · rename_i hnone
      obtain ⟨c, hc, hmem⟩ := hex
      rcases Nat.eq_zero_or_pos c with rfl | hc0
      · rw [pow_zero, mul_one, Nat.mod_eq_of_lt hy, hnone] at hmem
        exact absurd hmem (by simp)
      · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        refine ih (j + 1) (y * h % p) (Nat.mod_lt _ (by omega)) ⟨c, by omega, ?_⟩
        rwa [Nat.mod_mul_mod, mul_assoc, ← pow_succ']

/-- **Completeness of Algorithm 5.3.1**: if `g` is invertible modulo `p` and
`t ≡ g^l (mod p)` for some `l ≤ n`, the algorithm returns an answer (which is then a
discrete logarithm of `t`, by `bsgs_sound`).  With `b = ⌊√n⌋ + 1` write `l = i + j b`,
`i, j < b`: then `t hʲ = gⁱ` is found among the baby steps at giant step `j`. -/
theorem bsgs_complete {p g t n l : ℕ} (hp : 0 < p) (hg : Nat.Coprime g p) (hl : l ≤ n)
    (ht : g ^ l ≡ t [MOD p]) : (bsgs p g t n).isSome := by
  simp only [bsgs]
  set b := Nat.sqrt n + 1 with hb
  have hlb : l < b * b := hl.trans_lt (Nat.lt_succ_sqrt n)
  have hj : l / b < b := (Nat.div_lt_iff_lt_mul (by omega)).mpr hlb
  have hi : l % b < b := Nat.mod_lt _ (by omega)
  have hmem := (babyTable_mem p g 0 (1 % p) b ∅ (by simp)).2 (l % b) hi
  rw [zero_add] at hmem
  refine giantLoop_isSome _ 0 (t % p) b (Nat.mod_lt _ hp) ⟨l / b, hj, ?_⟩
  -- `t h^j = g^i` in `ZMod p`, hence as reduced residues
  have hinv : (g : ZMod p) * (modInv g p : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (mul_modInv_modEq hg)
    simpa using this
  have hT : (t : ZMod p) = (g : ZMod p) ^ l := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
    simpa using this.symm
  have key : t % p * powMod (modInv g p) b p ^ (l / b) % p = g ^ (l % b) % p := by
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    have hlm : (g : ZMod p) ^ l = (g : ZMod p) ^ (l % b) * ((g : ZMod p) ^ b) ^ (l / b) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [ZMod.natCast_mod, cast_powMod, hT, hlm, mul_assoc, ← mul_pow, ← mul_pow, hinv, one_pow,
      one_pow, mul_one]
  rw [key]
  exact hmem

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-- The baby-step table records indices below `i + count`. -/
theorem babyTable_lt (p g : ℕ) (i cur count : ℕ) (m : Std.HashMap ℕ ℕ)
    (hm : ∀ (y k : ℕ), m[y]? = some k → k < i) :
    ∀ (y k : ℕ), (babyTable p g i cur count m)[y]? = some k → k < i + count := by
  induction count generalizing i cur m with
  | zero => simpa [babyTable] using hm
  | succ count ih =>
    intro y k hk
    have := ih (i + 1) (cur * g % p) (m.insert cur i) (fun (y k : ℕ) hk ↦ by
      rw [Std.HashMap.getElem?_insert] at hk
      split_ifs at hk
      · obtain rfl := Option.some.inj hk; omega
      · exact (hm y k hk).trans (by omega)) y k hk
    omega

/-- One modular multiplication per baby step, and the insertion and the index, on numbers
of at most `K` bits. -/
theorem babyCost_le (C : CostModel) {p g K : ℕ} (hg : g < p) (i : ℕ) {cur : ℕ} (hcur : cur < p)
    (count : ℕ) (m : Std.HashMap ℕ ℕ) (hp : p.size ≤ K) (hK : (i + count).size ≤ K) :
    costOf C (babyTable p g i cur count m) ≤
      count * (C.mulMod p.size + 3 * C.lin K) + C.unit := by
  induction count generalizing i cur m with
  | zero => cost_unfold babyTable.counted
  | succ count ih =>
    have := mul_add_divMod_le C hcur hg
    have ih := ih (i + 1) (cur := cur * g % p) (Nat.mod_lt _ (by omega)) (m.insert cur i)
      ((Nat.size_le_size (by omega)).trans hK)
    have := size_le_of_lt hcur
    have : (i + 1).size ≤ K := (Nat.size_le_size (by omega)).trans hK
    have : i.size ≤ K := (Nat.size_le_size (by omega)).trans hK
    have : 1 ≤ K := le_trans (Nat.size_pos.mpr (show 0 < p by omega)) hp
    cost_unfold babyTable.counted
    cost_bound

/-- One modular multiplication per giant step taken, a look-up and the index; on success
the product `j b` and a sum, on numbers of at most `K` bits (the table's indices are at
most `B`). -/
theorem giantCost_le (C : CostModel) {p b h B K : ℕ} (m : Std.HashMap ℕ ℕ) (hh : h < p)
    (hm : ∀ (y i : ℕ), m[y]? = some i → i ≤ B) (hp : p.size ≤ K) (hK : (B + b * b).size ≤ K)
    (j : ℕ) {y : ℕ} (hy : y < p) (count : ℕ) (hj : j + count ≤ b) :
    costOf C (giantLoop p b h m j y count) ≤
      count * (C.mulMod p.size + 3 * C.lin K) + C.mul b.size b.size + C.lin K + C.unit := by
  induction count generalizing j y with
  | zero => cost_unfold giantLoop.counted
  | succ count ih =>
    have := mul_add_divMod_le C hy hh
    have ih := ih (j + 1) (y := y * h % p) (Nat.mod_lt _ (by omega)) (by omega)
    have hjb : C.mul j.size b.size ≤ C.mul b.size b.size :=
      C.mul_mono (Nat.size_le_size (by omega)) le_rfl
    have := size_le_of_lt hy
    have hjK : (j + 1).size ≤ K := (Nat.size_le_size (show j + 1 ≤ B + b * b by
      have : b ≤ b * b := Nat.le_mul_self b; omega)).trans hK
    have hjK' : j.size ≤ K := (Nat.size_le_size (by omega)).trans hjK
    have : 1 ≤ K := le_trans (Nat.size_pos.mpr (show 0 < p by omega)) hp
    cost_unfold giantLoop.counted
    split
    · rename_i i hi
      have hiB := hm y i hi
      have : (j * b).size ≤ K := (Nat.size_le_size (show j * b ≤ B + b * b from
        (Nat.mul_le_mul_right b (by omega : j ≤ b)).trans (Nat.le_add_left _ _))).trans hK
      have : i.size ≤ K := (Nat.size_le_size (show i ≤ B + b * b by omega)).trans hK
      cost_simp
      cost_bound
    · cost_simp
      cost_bound

/-- The bit length of the numbers of `bsgs`: the residues, the indices up to `b²` and the
exponent `b`. -/
def bsgsWidth (p n : ℕ) : ℕ := p.size + 2 * (Nat.sqrt n + 1).size + 3

/-- **Bit complexity of baby-steps, giant-steps**, for any cost model: with
`b = ⌊√n⌋ + 1`, the square root, the modular inverse `g⁻¹ mod p`, at most
`2b + 2 log₂ b` modular multiplications (the book's "`O(√n)` group operations"), three
reductions modulo `p`, the product `j b`, and `O(b)` linear operations (the table's
insertions and look-ups, the indices). -/
theorem bsgsCost_le (C : CostModel) {p g t : ℕ} (hg : g < p) (ht : t < p) (n : ℕ) :
    costOf C (bsgs p g t n) ≤
      costOf C (Nat.sqrt n) + costOf C (modInv g p) + 3 * C.divMod p.size p.size +
        (2 * Nat.log 2 (Nat.sqrt n + 1) + 2 * (Nat.sqrt n + 1)) * C.mulMod p.size +
        C.mul (Nat.sqrt n + 1).size (Nat.sqrt n + 1).size +
        (6 * (Nat.sqrt n + 1) + 6 * Nat.log 2 (Nat.sqrt n + 1) + 12) * C.lin (bsgsWidth p n) := by
  have hp : 0 < p := by omega
  cost_unfold bsgs.counted
  set b := Nat.sqrt n + 1 with hb
  set K := bsgsWidth p n
  have hKb : ∀ x, x < 2 ^ (2 * b.size + 1) → x.size ≤ K := fun x hx ↦
    (Nat.size_le.mpr hx).trans (by simp only [K, bsgsWidth, ← hb]; omega)
  have hbb : b * b + b < 2 ^ (2 * b.size + 1) := by
    have := Nat.lt_size_self b
    have : b * b < 2 ^ b.size * 2 ^ b.size := Nat.mul_lt_mul'' this this
    rw [pow_succ, two_mul, pow_add]; nlinarith
  have hpK : p.size ≤ K := by simp only [K, bsgsWidth]; omega
  have hbK : b.size + 2 ≤ K := by simp only [K, bsgsWidth, ← hb]; omega
  have h₁ := powModCost_le C (modInv_lt g hp) (k := b.size) b le_rfl
  have h₂ := babyCost_le C hg 0 (Nat.mod_lt 1 hp) b ∅ hpK (hKb _ (by omega))
  have hlt := babyTable_lt p g 0 (1 % p) b ∅ (by simp)
  have h₃ := giantCost_le C (b := b) (B := b) (babyTable p g 0 (1 % p) b ∅)
    (powMod_lt (modInv g p) b hp) (fun y i hi ↦ by have := hlt y i hi; omega) hpK
    (hKb _ (by omega)) 0 (Nat.mod_lt t hp) b (by omega)
  have h₄ : C.divMod t.size p.size ≤ C.divMod p.size p.size :=
    C.divMod_mono _ (size_le_of_lt ht)
  have h₄' : C.divMod (1 : ℕ).size p.size ≤ C.divMod p.size p.size :=
    C.divMod_mono _ (Nat.size_le_size (by omega))
  have hl := C.lin_mono hbK
  have hnb : (Nat.sqrt n).size ≤ K := hKb _ (by omega)
  cost_bound

/-- **Bit complexity of baby-steps, giant-steps, grammar-school arithmetic**, with the
square root by Algorithm 9.2.11 and the inverse by Algorithm 2.1.4: with `k` the bit length
of `p`, `b = ⌊√n⌋ + 1` and `w = bsgsWidth p n`, at most
`schoolSqrt (size n) + 6(k + 1)(3k + 2) + 5k + 4 + (2 log₂ b + 2b)(2k² + k) + (size b)² +
(6b + 6 log₂ b + 12)(w + 2)` bit operations — `O(√n ln² p)`. -/
theorem bsgsCost_school_le {p g t : ℕ} (hg0 : 0 < g) (hg : g < p) (ht : t < p) (n : ℕ) :
    costOf school (bsgs p g t n) ≤
      schoolSqrt n.size + (6 * (p.size + 1) * (3 * p.size + 2) + 2 * p.size + 4) +
        3 * p.size +
        (2 * Nat.log 2 (Nat.sqrt n + 1) + 2 * (Nat.sqrt n + 1)) * (2 * p.size ^ 2 + p.size) +
        (Nat.sqrt n + 1).size * (Nat.sqrt n + 1).size +
        (6 * (Nat.sqrt n + 1) + 6 * Nat.log 2 (Nat.sqrt n + 1) + 12) * (bsgsWidth p n + 2) := by
  have h₁ := bsgsCost_le school hg ht n
  have h₂ := modInvCost_school_le hg0 (by omega : 0 < p) hg.le (le_refl p)
  have h₃ : school.divMod p.size p.size = p.size := by simp [school]
  have h₄ := sqrt_counted_cost_school_le n
  have h₅ : school.mul (Nat.sqrt n + 1).size (Nat.sqrt n + 1).size =
      (Nat.sqrt n + 1).size * (Nat.sqrt n + 1).size := rfl
  rw [school_mulMod, h₃, h₅, school_lin] at h₁
  omega

end RunningTime

end PrimeNumbers.Chapter5
