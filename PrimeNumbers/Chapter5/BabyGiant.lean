import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power

/-!
# §5.3 Baby-steps, giant-steps

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.3.

* `bsgs` — Algorithm 5.3.1 (baby-steps, giant-steps for discrete logarithms) in the group
  `Z_p^*`, with residues as naturals and the baby steps stored in a hash table, as the
  book's remark after the algorithm suggests ("it is not necessary to sort both lists").
* `bsgs_sound` — a returned `l` satisfies `g^l ≡ t (mod p)`.

Not yet proved: completeness (that an `l` is found whenever `t` is a power of `g` and `n`
bounds the order of `g`), and the `O(√n)` operation count.
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2

/-- Step 2, list `A`: insert `gⁱ ↦ i` for `count` consecutive `i`, where `cur = gⁱ mod p`. -/
def babyTable (p g : ℕ) : (i cur count : ℕ) → Std.HashMap ℕ ℕ → Std.HashMap ℕ ℕ
  | _, _, 0, m => m
  | i, cur, count + 1, m => babyTable p g (i + 1) (cur * g % p) count (m.insert cur i)

/-- Step 2–3, list `B`: for `count` consecutive `j`, with `y = t hʲ mod p`, look `y` up
among the baby steps; a hit `y = gⁱ` gives `l = i + j b`. -/
def giantLoop (p b h : ℕ) (m : Std.HashMap ℕ ℕ) : (j y count : ℕ) → Option ℕ
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
def bsgs (p g t n : ℕ) : Option ℕ :=
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

end PrimeNumbers.Chapter5
