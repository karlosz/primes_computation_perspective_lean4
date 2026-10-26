import PrimeNumbers.Chapter5.QuadForms
import PrimeNumbers.Chapter2.SqrtComposite
import PrimeNumbers.Chapter3.TrialDivision
import PrimeNumbers.Chapter9.IntSqrt

/-!
# Algorithm 5.6.3 (McKee test)

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.6.2.

With `d = n - x₀²` for `x₀ = ⌊√(n - ⌈n^{2/3}⌉)⌋`, the form `(1, 0, d)` of discriminant `-4d`
represents `n` at `(x₀, 1)`; McKee searches for a second representation `a n = w² + d v²`
with `1 ≤ a ≤ √(4d/3)` (writing `u = 2w`), among the `w` with `w² ≡ a n (mod d)` found
from the factorization of `d` (`rootsMod`, Exercise 2.36), and splits `n` by
`gcd(x₀ v - w, n)`.

* `mckee` — Algorithm 5.6.3, returning a factorization `(g, n/g)` or `none` ("n is prime").
* `mckee_sound` — a returned pair is a nontrivial factorization of `n` (no hypothesis on
  `n`: the test `w ≢ ±x₀ v (mod n)` and `n ∣ (x₀ v - w)(x₀ v + w)` make the gcd proper).
* `mckee_complete` — if `n` has no prime factor below `3n^{1/3}` and the test answers
  "prime", `n` is prime: a composite `n` is then `p q` (`eq_mul_of_large_factors`), a root
  `h ≡ x₀ (mod p)`, `h ≡ -x₀ (mod q)` of `-d` gives the form `(A, 2h, n)`, and its reduced
  form represents `n` at a pair the search reaches (`exists_rep_of_reduce`,
  `exists_witness`).
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3

/-! ### `⌈n^{2/3}⌉` by bisection -/

/-- Bisection for the least `t` with `n² ≤ t³`, between `lo` (`lo³ < n²`) and `hi`
(`n² ≤ hi³`). -/
counted_def ceilTwoThirdsLoop (n : ℕ) : (lo hi fuel : ℕ) → ℕ
  | _, hi, 0 => hi
  | lo, hi, fuel + 1 =>
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if n * n ≤ mid * mid * mid then ceilTwoThirdsLoop n lo mid fuel
      else ceilTwoThirdsLoop n mid hi fuel
    else hi

/-- `⌈n^{2/3}⌉`: the least `t` with `n² ≤ t³` (for `n ≥ 1`). -/
counted_def ceilTwoThirds (n : ℕ) : ℕ := ceilTwoThirdsLoop n 0 n (n.size + 1)

/-! ### The factorization of `d` as pairs `(p, e)` -/

/-- The list without repetitions (the last occurrence of each element kept). -/
counted_def dedupNat : List ℕ → List ℕ
  | [] => []
  | x :: xs => if xs.any fun y ↦ y = x then dedupNat xs else x :: dedupNat xs

/-- The distinct elements of a list of primes, each with its multiplicity. -/
counted_def factorPairs (L : List ℕ) : List (ℕ × ℕ) :=
  (dedupNat L).map fun p ↦ (p, (L.filter fun y ↦ y = p).length)

/-- A quadratic nonresidue modulo the odd prime `p` by Euler's criterion: the least `z ≥ 2`
with `z^{(p-1)/2} ≢ 1 (mod p)` — at most `√p + 1` (`exists_nonresidue_le_sqrt`). -/
counted_def eulerNonresidue (p : ℕ) : ℕ :=
  searchFrom (fun z ↦ powMod z (p / 2) p ≠ 1) p 2

/-- The factorization with a quadratic nonresidue for each prime (Tonelli's algorithm needs
one; it is found once per prime, not once per square root). -/
counted_def withNonresidues (fs : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  fs.map fun pe ↦ (pe.1, pe.2, eulerNonresidue pe.1)

/-! ### The search -/

/-- The candidates `w, w + d, w + 2d, …` (`fuel` of them) with `w² < a n`: the first with
`a n - w² = d v²` and `w ≢ ±x₀ v (mod n)`, giving the factor `gcd(x₀ v - w, n)`. -/
counted_def searchClass (n d a x₀ : ℕ) : (w fuel : ℕ) → Option ℕ
  | _, 0 => none
  | w, fuel + 1 =>
    if w * w < a * n then
      let r := a * n - w * w
      let v := Nat.sqrt (r / d)
      let c := (x₀ * v % n + n - w % n) % n          -- `x₀ v - w (mod n)`
      if r % d = 0 ∧ v * v = r / d ∧ c ≠ 0 ∧ (x₀ * v + w) % n ≠ 0 then some (Nat.gcd c n)
      else searchClass n d a x₀ (w + d) fuel
    else none

/-- The search over the residue classes `ws` of `w` modulo `d`. -/
counted_def searchRoots (n d a x₀ : ℕ) : List ℕ → Option ℕ
  | [] => none
  | w :: ws =>
    match searchClass n d a x₀ w (Nat.sqrt (a * n) / d + 1) with
    | some g => some g
    | none => searchRoots n d a x₀ ws

/-- The loop `for (1 ≤ a ≤ 2√(d/3))`: the classes of `w` with `w² ≡ a n (mod d)` from the
factorization `fs` of `d`. -/
counted_def searchA (n d x₀ : ℕ) (fs : List (ℕ × ℕ × ℕ)) : (a fuel : ℕ) → Option ℕ
  | _, 0 => none
  | a, fuel + 1 =>
    if 3 * (a * a) ≤ 4 * d then
      match searchRoots n d a x₀ (rootsMod (a * n % d) fs).2 with
      | some g => some g
      | none => searchA n d x₀ fs (a + 1) fuel
    else none

/-- **Algorithm 5.6.3 (McKee test).**  Given `n > 1` with no prime factor below `3n^{1/3}`,
the prime factorization `(p, n/p)` of a composite `n`, or `none`: `n` is prime.
```
1. if n = p² return p · p;                                  // Algorithm 9.2.11
2. d = n - ⌊√(n - ⌈n^{2/3}⌉)⌋²;
   if (gcd(n, d) > 1) return gcd(n, d) · (n / gcd(n, d));
   factor d by trial division;
3. for (1 ≤ a ≤ 2√(d/3))
     for each solution w of w² ≡ a n (mod d)                 // Exercise 2.36
       for the w' ≡ w (mod d), 0 ≤ w' < √(a n):
         if (a n - w'²)/d = v² and w' ≢ ±x₀ v (mod n), goto 4;
   return "n is prime";
4. g = gcd(x₀ v - w', n);  return g · (n/g);
```
(The book writes `u = 2w'`, with `u² ≡ 4an (mod 4d)` and `(4an - u²)/4d = v²`; the gcd
case returns only a proper divisor, which `gcd(n, d)` is unless `n ≤ 2`.) -/
counted_def mckee (n : ℕ) : Option (ℕ × ℕ) :=
  let s := Nat.sqrt n
  if s * s = n then some (s, s)                                          -- 1. [Square test]
  else
    let x₀ := Nat.sqrt (n - ceilTwoThirds n)                             -- 2. [Side factorization]
    let d := n - x₀ * x₀
    let g := Nat.gcd n d
    if 1 < g ∧ g < n then some (g, n / g)
    else
      let fs := withNonresidues (factorPairs (trialDivision d))
      match searchA n d x₀ fs 1 d with                                   -- 3. [Congruences]
      | some g => some (g, n / g)                                        -- 4. [gcd computation]
      | none => none

/-! ### Soundness -/

/-- **The test of step 3 gives a proper factor**: with `x₀² + d = n` and `w² + d v² = a n`,
`n ∣ (x₀ v - w)(x₀ v + w) = n v² - a n`; if `n` divides neither factor, the gcd of the
first with `n` is proper. -/
theorem gcd_check {n d a x₀ w v : ℕ} (hn : 0 < n) (hd : n = x₀ * x₀ + d)
    (hwv : w * w + d * (v * v) = a * n)
    (hc : (x₀ * v % n + n - w % n) % n ≠ 0) (hc' : (x₀ * v + w) % n ≠ 0) :
    1 < Nat.gcd ((x₀ * v % n + n - w % n) % n) n ∧
      Nat.gcd ((x₀ * v % n + n - w % n) % n) n < n := by
  set c := (x₀ * v % n + n - w % n) % n
  have hle : w % n ≤ x₀ * v % n + n := by have := Nat.mod_lt w hn; omega
  have hcz : (c : ZMod n) = x₀ * v - w := by
    simp only [c, ZMod.natCast_mod]
    push_cast [Nat.cast_sub hle, ZMod.natCast_mod, ZMod.natCast_self]; ring
  have hdvd : (n : ℤ) ∣ (c : ℤ) * ((x₀ * v + w : ℕ) : ℤ) := by
    have : ((c * (x₀ * v + w) : ℕ) : ZMod n) = 0 := by
      have h₁ : ((x₀ * x₀ + d : ℕ) : ZMod n) = 0 := by rw [← hd, ZMod.natCast_self]
      have h₂ : ((w * w + d * (v * v) : ℕ) : ZMod n) = ((a * n : ℕ) : ZMod n) := by rw [hwv]
      push_cast at h₁ h₂ ⊢
      rw [hcz, ZMod.natCast_self, mul_zero] at *
      linear_combination v * v * h₁ - h₂
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).1 this
  have := QF.one_lt_gcd_lt_of_dvd_mul (n := n) hdvd
    (fun h ↦ hc (Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast h) (Nat.mod_lt _ hn)))
    (fun h ↦ hc' (Nat.mod_eq_zero_of_dvd (by exact_mod_cast h)))
  simpa [Int.gcd_natCast_natCast] using this

/-- A factor found in a class is proper. -/
theorem searchClass_sound {n d a x₀ : ℕ} (hn : 0 < n) (hd : n = x₀ * x₀ + d) {w fuel g : ℕ}
    (h : searchClass n d a x₀ w fuel = some g) : 1 < g ∧ g < n ∧ g ∣ n := by
  induction fuel generalizing w with
  | zero => simp [searchClass] at h
  | succ fuel ih =>
    rw [searchClass] at h
    split_ifs at h with h₁
    · dsimp only at h
      split_ifs at h with h₂
      · obtain rfl := Option.some.inj h
        obtain ⟨hr, hv, hc, hc'⟩ := h₂
        have hwv : w * w + d * (Nat.sqrt ((a * n - w * w) / d) *
            Nat.sqrt ((a * n - w * w) / d)) = a * n := by
          rw [hv, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hr)]; omega
        exact ⟨(gcd_check hn hd hwv hc hc').1, (gcd_check hn hd hwv hc hc').2,
          Nat.gcd_dvd_right _ _⟩
      · exact ih h

theorem searchRoots_sound {n d a x₀ : ℕ} (hn : 0 < n) (hd : n = x₀ * x₀ + d) {ws : List ℕ}
    {g : ℕ} (h : searchRoots n d a x₀ ws = some g) : 1 < g ∧ g < n ∧ g ∣ n := by
  induction ws with
  | nil => simp [searchRoots] at h
  | cons w ws ih =>
    rw [searchRoots] at h
    split at h
    · next g' hg => obtain rfl := Option.some.inj h; exact searchClass_sound hn hd hg
    · exact ih h

theorem searchA_sound {n d x₀ : ℕ} (hn : 0 < n) (hd : n = x₀ * x₀ + d)
    {fs : List (ℕ × ℕ × ℕ)} {a fuel g : ℕ} (h : searchA n d x₀ fs a fuel = some g) :
    1 < g ∧ g < n ∧ g ∣ n := by
  induction fuel generalizing a with
  | zero => simp [searchA] at h
  | succ fuel ih =>
    rw [searchA] at h
    split_ifs at h
    · split at h
      · next g' hg => obtain rfl := Option.some.inj h; exact searchRoots_sound hn hd hg
      · exact ih h

theorem one_lt_div_of_proper {n g : ℕ} (h₁ : 1 < g) (h₂ : g < n) (hd : g ∣ n) : 1 < n / g := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left _ (by omega)]
  by_contra hc; push Not at hc; interval_cases k <;> omega

/-- **Soundness of Algorithm 5.6.3**: a returned pair is a factorization of `n` into
proper factors. -/
theorem mckee_sound {n p q : ℕ} (hn : 1 < n) (h : mckee n = some (p, q)) :
    p * q = n ∧ 1 < p ∧ 1 < q := by
  unfold mckee at h
  dsimp only at h
  split_ifs at h with h₁ h₂
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨h₁, ?_, ?_⟩ <;> by_contra hc <;> push Not at hc <;> interval_cases (Nat.sqrt n) <;>
      omega
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hg₁, hg₂⟩ := h₂
    have hdvd := Nat.gcd_dvd_left n (n - Nat.sqrt (n - ceilTwoThirds n) *
      Nat.sqrt (n - ceilTwoThirds n))
    exact ⟨Nat.mul_div_cancel' hdvd, hg₁, one_lt_div_of_proper hg₁ hg₂ hdvd⟩
  · have hd : n = Nat.sqrt (n - ceilTwoThirds n) * Nat.sqrt (n - ceilTwoThirds n) +
        (n - Nat.sqrt (n - ceilTwoThirds n) * Nat.sqrt (n - ceilTwoThirds n)) := by
      have := Nat.sqrt_le (n - ceilTwoThirds n); omega
    split at h
    · next g hg =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hg₁, hg₂, hdvd⟩ := searchA_sound (by omega) hd hg
      exact ⟨Nat.mul_div_cancel' hdvd, hg₁, one_lt_div_of_proper hg₁ hg₂ hdvd⟩
    · simp at h

/-! ### Completeness -/

theorem ceilTwoThirdsLoop_spec (n : ℕ) (fuel : ℕ) :
    ∀ {lo hi : ℕ}, lo < hi → lo * lo * lo < n * n → n * n ≤ hi * hi * hi → hi - lo ≤ 2 ^ fuel →
      n * n ≤ ceilTwoThirdsLoop n lo hi fuel * ceilTwoThirdsLoop n lo hi fuel *
        ceilTwoThirdsLoop n lo hi fuel ∧
      (ceilTwoThirdsLoop n lo hi fuel - 1) * (ceilTwoThirdsLoop n lo hi fuel - 1) *
        (ceilTwoThirdsLoop n lo hi fuel - 1) < n * n := by
  induction fuel with
  | zero =>
    intro lo hi hlt hlo hhi hw
    obtain rfl : hi = lo + 1 := by simp at hw; omega
    simp only [ceilTwoThirdsLoop, Nat.add_sub_cancel]; exact ⟨hhi, hlo⟩
  | succ fuel ih =>
    intro lo hi hlt hlo hhi hw
    rw [ceilTwoThirdsLoop]
    rw [pow_succ] at hw
    by_cases h₁ : lo + 1 < hi
    · simp only [h₁, ↓reduceIte]
      by_cases h₂ : n * n ≤ (lo + hi) / 2 * ((lo + hi) / 2) * ((lo + hi) / 2)
      · simp only [h₂, ↓reduceIte]; exact ih (by omega) hlo h₂ (by omega)
      · simp only [h₂, ↓reduceIte]; exact ih (by omega) (by omega) hhi (by omega)
    · obtain rfl : hi = lo + 1 := by omega
      simp only [h₁, ↓reduceIte, Nat.add_sub_cancel]; exact ⟨hhi, hlo⟩

/-- `ceilTwoThirds n` is `⌈n^{2/3}⌉`: the least `t` with `n² ≤ t³`. -/
theorem ceilTwoThirds_spec {n : ℕ} (hn : 1 ≤ n) :
    n * n ≤ ceilTwoThirds n * ceilTwoThirds n * ceilTwoThirds n ∧
      (ceilTwoThirds n - 1) * (ceilTwoThirds n - 1) * (ceilTwoThirds n - 1) < n * n := by
  unfold ceilTwoThirds
  refine ceilTwoThirdsLoop_spec n _ (by omega) (by simp; positivity)
    (by nlinarith) ?_
  have := Nat.lt_size_self n
  rw [pow_succ]; omega

theorem dedupNat_spec (L : List ℕ) : (dedupNat L).Nodup ∧ ∀ x, x ∈ dedupNat L ↔ x ∈ L := by
  induction L with
  | nil => simp [dedupNat]
  | cons x xs ih =>
    obtain ⟨h₁, h₂⟩ := ih
    rw [dedupNat]
    split_ifs with h
    · have hx : x ∈ xs := by simpa using h
      refine ⟨h₁, fun y ↦ ?_⟩
      rw [h₂]; simp only [List.mem_cons]; constructor
      · exact Or.inr
      · rintro (rfl | h); exacts [hx, h]
    · have hx : x ∉ xs := by simpa using h
      refine ⟨List.nodup_cons.2 ⟨by rwa [h₂], h₁⟩, fun y ↦ ?_⟩
      simp only [List.mem_cons, h₂]

/-- **The least quadratic nonresidue is at most `√p + 1`.**  If `n` is the least
nonresidue modulo the odd prime `p` and `m = ⌊p/n⌋ + 1`, then `0 < m n - p < n`, so
`m n ≡ m n - p` is a residue and `m` is a nonresidue: `m ≥ n`, so `n (n - 1) ≤ p`. -/
theorem exists_nonresidue_le_sqrt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∃ n, 2 ≤ n ∧ n ≤ Nat.sqrt p + 1 ∧ ¬IsSquare ((n : ℕ) : ZMod p) ∧
      ∀ k, 1 ≤ k → k < n → IsSquare ((k : ℕ) : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have hex : ∃ n, 1 ≤ n ∧ ¬IsSquare ((n : ℕ) : ZMod p) := by
    obtain ⟨z, hz⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [Ne, ZMod.ringChar_zmod_n]; exact hp)
    refine ⟨z.val, ?_, by rwa [ZMod.natCast_zmod_val]⟩
    rcases Nat.eq_zero_or_pos z.val with h | h
    · exfalso; apply hz; rw [ZMod.val_eq_zero] at h; rw [h]; exact ⟨0, by ring⟩
    · exact h
  classical
  let n := Nat.find hex
  have hn₁ : 1 ≤ n := (Nat.find_spec hex).1
  have hn₂ : ¬IsSquare ((n : ℕ) : ZMod p) := (Nat.find_spec hex).2
  have hmin : ∀ k, 1 ≤ k → k < n → IsSquare ((k : ℕ) : ZMod p) := fun k hk hkn ↦ by
    by_contra h; exact Nat.find_min hex hkn ⟨hk, h⟩
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    exact hn₂ (by rw [this]; exact ⟨1, by simp⟩)
  -- `n < p`: the residues `n mod p` repeat
  have hnp : n < p := by
    by_contra h; push Not at h
    have hm := hmin (n % p) ?_ (Nat.mod_lt _ hpp.pos |>.trans_le h)
    · exact hn₂ (by rwa [ZMod.natCast_mod] at hm)
    · rcases Nat.eq_zero_or_pos (n % p) with h0 | h0
      · exfalso; apply hn₂
        rw [(ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero h0)]; exact ⟨0, by ring⟩
      · exact h0
  refine ⟨n, hn2, ?_, hn₂, hmin⟩
  set m := p / n + 1 with hm_def
  have hmn : p < m * n := by
    show p < (p / n + 1) * n; rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hmp : m < p := by
    have : p / n ≤ p / 2 := Nat.div_le_div_left hn2 (by norm_num)
    have : p / 2 < p - 1 := by omega
    rw [hm_def]; omega
  have hmn' : m * n - p < n := by
    have := Nat.div_mul_le_self p n
    have : p / n * n ≠ p := fun h ↦ by
      have : n ∣ p := ⟨p / n, by rw [mul_comm]; exact h.symm⟩
      rcases (Nat.dvd_prime hpp).1 this with h1 | h1 <;> omega
    simp only [m, add_mul, one_mul]; omega
  -- `m n - p` is a residue, so `m n` is, so `m` is a nonresidue
  have hr := hmin (m * n - p) (by omega) hmn'
  have hcast : (((m * n - p : ℕ)) : ZMod p) = (m : ZMod p) * n := by
    rw [Nat.cast_sub hmn.le, ZMod.natCast_self, sub_zero, Nat.cast_mul]
  rw [hcast] at hr
  have hm : ¬IsSquare ((m : ℕ) : ZMod p) := by
    intro hm
    have hm0 : ((m : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
      have := Nat.le_of_dvd (by rw [hm_def]; exact Nat.succ_pos _) h; omega
    have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
    -- a residue times a nonresidue is a nonresidue
    have h1 := (legendreSym.eq_one_iff p (a := (m : ℤ)) (by exact_mod_cast hm0)).2 (by exact_mod_cast hm)
    have h2 := (legendreSym.eq_neg_one_iff p (a := (n : ℤ))).2 (by exact_mod_cast hn₂)
    have h3 := (legendreSym.eq_one_iff p (a := ((m : ℤ) * n)) (by exact_mod_cast mul_ne_zero hm0 hn0)).2
      (by exact_mod_cast hr)
    rw [legendreSym.mul, h1, h2] at h3; norm_num at h3
  have hmge : n ≤ m := by
    by_contra h; push Not at h
    exact hm (hmin m (by rw [hm_def]; exact Nat.succ_le_succ (Nat.zero_le _)) h)
  -- `n (n - 1) ≤ p`, so `n - 1 ≤ √p`
  have : (n - 1) * (n - 1) ≤ p := by
    have : (n - 1) * n ≤ p := by
      have := Nat.div_mul_le_self p n
      have : (n - 1) * n ≤ p / n * n := Nat.mul_le_mul_right n (by omega)
      omega
    exact (Nat.mul_le_mul_left (n - 1) (by omega : n - 1 ≤ n)).trans this
  have := Nat.le_sqrt.2 this; omega

/-- The search returns at most its first success. -/
theorem searchFrom_le_of {P : ℕ → Bool} {fuel d e : ℕ} (hde : d ≤ e) (he : e < d + fuel)
    (hP : P e) : searchFrom P fuel d ≤ e := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    rw [searchFrom]
    split_ifs with h
    · exact hde
    · exact ih (by rcases Nat.eq_or_lt_of_le hde with rfl | h' <;> [exact absurd hP h; omega])
        (by omega)

theorem le_searchFrom (P : ℕ → Bool) (fuel d : ℕ) : d ≤ searchFrom P fuel d := by
  induction fuel generalizing d with
  | zero => rw [searchFrom]
  | succ fuel ih => rw [searchFrom]; split_ifs <;> [exact le_rfl; exact (ih _).trans' (by omega)]

/-- Euler's criterion finds a nonresidue below `√p + 2`. -/
theorem eulerNonresidue_spec {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ¬IsSquare ((eulerNonresidue p : ℕ) : ZMod p) ∧ 2 ≤ eulerNonresidue p ∧
      eulerNonresidue p ≤ Nat.sqrt p + 1 := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  obtain ⟨n, hn2, hnp, hn, -⟩ := exists_nonresidue_le_sqrt hp
  have hnlt : n < p := by
    have : 2 * (p - 1) ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right (p - 1) (by omega)
    have := Nat.sqrt_lt'.2 (show p < (p - 1) ^ 2 by rw [sq]; omega); omega
  have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := fun h ↦ hn (by rw [h]; exact ⟨0, by ring⟩)
  -- the predicate: `z^{p/2} ≢ 1`
  have hPn : powMod n (p / 2) p ≠ 1 := by
    rw [powMod_eq]; intro h
    apply hn; rw [ZMod.euler_criterion p hn0]
    have := (ZMod.natCast_eq_natCast_iff' (n ^ (p / 2)) 1 p).2 (by
      rw [h, Nat.one_mod_eq_one.2 hpp.one_lt.ne'])
    push_cast at this; exact this
  have h₁ := searchFrom_le_of (P := fun z ↦ powMod z (p / 2) p ≠ 1) (fuel := p) hn2
    (by omega) (by simpa using hPn)
  have h₂ := le_searchFrom (fun z ↦ powMod z (p / 2) p ≠ 1) p 2
  have h₃ := searchFrom_spec (fun z ↦ powMod z (p / 2) p ≠ 1) p 2 ⟨n, hn2, by omega,
    by simpa using hPn⟩
  unfold eulerNonresidue
  set z := searchFrom (fun z ↦ powMod z (p / 2) p ≠ 1) p 2
  refine ⟨fun hz ↦ ?_, h₂, h₁.trans hnp⟩
  have hz0 : ((z : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  rw [ZMod.euler_criterion p hz0] at hz
  apply (by simpa using h₃ : powMod z (p / 2) p ≠ 1)
  rw [powMod_eq]
  have := (ZMod.natCast_eq_natCast_iff' (z ^ (p / 2)) 1 p).1 (by push_cast; exact hz)
  rw [this, Nat.one_mod_eq_one.2 hpp.one_lt.ne']

/-- The pairs of the factorization by trial division, with nonresidues, are a factorization
of `d`. -/
theorem factorPairs_spec {d : ℕ} (hd : 0 < d) :
    IsFactorization (withNonresidues (factorPairs (trialDivision d))) ∧
      factorProd (withNonresidues (factorPairs (trialDivision d))) = d := by
  set L := trialDivision d
  obtain ⟨hprod, hprime⟩ := trialDivision_spec hd
  obtain ⟨hnd, hmem⟩ := dedupNat_spec L
  have hcount : ∀ p, (L.filter fun y ↦ decide (y = p)).length = L.count p := fun p ↦ by
    rw [List.count_eq_length_filter]; congr 1
  refine ⟨⟨?_, fun pe hpe ↦ ?_⟩, ?_⟩
  · simpa [withNonresidues, factorPairs, List.map_map, Function.comp_def] using hnd
  · simp only [withNonresidues, factorPairs, List.map_map, List.mem_map,
      Function.comp_def] at hpe
    obtain ⟨p, hp, rfl⟩ := hpe
    have hpL := (hmem p).1 hp
    have hpp := hprime p hpL
    have := Fact.mk hpp
    refine ⟨hpp, ?_, fun h2 ↦ (eulerNonresidue_spec h2).1⟩
    simp only [hcount]; exact List.count_pos_iff.2 hpL
  · simp only [factorProd, withNonresidues, factorPairs, List.map_map, Function.comp_def,
      hcount]
    rw [← List.prod_toFinset _ hnd, ← hprod]
    have : (dedupNat L).toFinset = L.toFinset := by ext x; simp [hmem]
    rw [this, Finset.prod_list_count]

/-- A representation `a n = w² + d v²`, `v ≥ 1`, with `w ≢ ±x₀ v (mod n)`, is found by the
search of its class `w mod d`. -/
theorem searchClass_isSome {n d a x₀ w v : ℕ} (hd : 0 < d) (hv : 1 ≤ v)
    (hrep : a * n = w * w + d * (v * v)) (hc : (x₀ * v % n + n - w % n) % n ≠ 0)
    (hc' : (x₀ * v + w) % n ≠ 0) :
    ∀ {i fuel w₀ : ℕ}, i < fuel → w = w₀ + d * i → (searchClass n d a x₀ w₀ fuel).isSome := by
  intro i
  induction i with
  | zero =>
    intro fuel w₀ hi hw
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [mul_zero, add_zero] at hw; subst hw
    have hlt : w * w < a * n := by nlinarith
    have hr : a * n - w * w = d * (v * v) := by omega
    rw [searchClass]
    simp only [hlt, ↓reduceIte, hr, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hd,
      Nat.sqrt_eq, true_and]
    simp [hc, hc']
  | succ i ih =>
    intro fuel w₀ hi hw
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlt : w₀ * w₀ < a * n := by
      have : w₀ ≤ w := by rw [hw]; omega
      nlinarith [Nat.mul_le_mul this this]
    rw [searchClass]
    simp only [hlt, ↓reduceIte]
    split_ifs
    · simp
    · exact ih (by omega) (by rw [hw]; ring)

theorem searchRoots_isSome {n d a x₀ w : ℕ} {ws : List ℕ} (hw : w ∈ ws)
    (h : (searchClass n d a x₀ w (Nat.sqrt (a * n) / d + 1)).isSome) :
    (searchRoots n d a x₀ ws).isSome := by
  induction ws with
  | nil => simp at hw
  | cons w' ws ih =>
    rw [searchRoots]
    split
    · simp
    · next hnone =>
      rcases List.mem_cons.1 hw with rfl | hw
      · rw [hnone] at h; simp at h
      · exact ih hw

theorem searchA_isSome {n d x₀ : ℕ} {fs : List (ℕ × ℕ × ℕ)} {a₀ : ℕ} (h₀ : 3 * (a₀ * a₀) ≤ 4 * d)
    (h : (searchRoots n d a₀ x₀ (rootsMod (a₀ * n % d) fs).2).isSome) :
    ∀ {k a fuel : ℕ}, k < fuel → a₀ = a + k → (searchA n d x₀ fs a fuel).isSome := by
  intro k
  induction k with
  | zero =>
    intro a fuel hk ha
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [Nat.add_zero] at ha; subst ha
    rw [searchA]; simp only [h₀, ↓reduceIte]
    split
    · simp
    · next hn => rw [hn] at h; simp at h
  | succ k ih =>
    intro a fuel hk ha
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have : 3 * (a * a) ≤ 4 * d := le_trans (by nlinarith) h₀
    rw [searchA]; simp only [this, ↓reduceIte]
    split
    · simp
    · exact ih (by omega) (by omega)

/-- A composite `n` that is not a square, with every prime factor above `3 n^{1/3}`
(`27 n ≤ p³`), is a product of two distinct primes. -/
theorem eq_mul_of_large_factors {n : ℕ} (hn : 1 < n)
    (hsmall : ∀ p, p.Prime → p ∣ n → 27 * n ≤ p ^ 3) (hnp : ¬n.Prime)
    (hsq : ∀ s, s * s ≠ n) : ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q := by
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  obtain ⟨q, hq⟩ := hpn
  have hq1 : 1 < q := by
    rcases Nat.lt_or_ge 1 q with h | h
    · exact h
    · interval_cases q
      · omega
      · exact absurd (by rw [hq, mul_one]; exact hp) hnp
  have hqp : q.Prime := by
    by_contra hqc
    -- `q = r s` with prime factors `r ∣ q`, `t ∣ s`: then `(p r t)³ > n³`
    set r := q.minFac
    have hr : r.Prime := Nat.minFac_prime (by omega)
    obtain ⟨s, hs⟩ := Nat.minFac_dvd q
    have hs1 : 1 < s := by
      rcases Nat.lt_or_ge 1 s with h | h
      · exact h
      · interval_cases s
        · omega
        · exact absurd (by rw [hs, mul_one]; exact hr) hqc
    set t := s.minFac
    have ht : t.Prime := Nat.minFac_prime (by omega)
    obtain ⟨u, hu⟩ := Nat.minFac_dvd s
    have hn' : n = p * r * t * u := by rw [hq, hs, hu]; ring
    have h₁ := hsmall p hp ⟨q, hq⟩
    have h₂ := hsmall r hr ⟨p * s, by rw [hq, hs]; ring⟩
    have h₃ := hsmall t ht ⟨p * r * u, by rw [hn']; ring⟩
    have hu1 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · simp [h] at hn'; omega
      · exact h
    have hle : p * r * t ≤ n := by rw [hn']; exact Nat.le_mul_of_pos_right _ hu1
    have : (p * r * t) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hle 3
    have : (27 * n) * (27 * n) * (27 * n) ≤ (p * r * t) ^ 3 := by
      rw [mul_pow, mul_pow]; exact Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
    nlinarith
  refine ⟨p, q, hp, hqp, fun h ↦ hsq p (by rw [hq, h]), hq⟩

open QF in
/-- **The representation behind McKee's search.**  The form `(A, 2h, n)` of discriminant
`-4d` represents `n` at `(0, 1)`; its reduced form `(a, b, c)` represents `n` at
`(x, y) = (-β, α)`, which gives `W² + d V² = a n` with `W = a x + (b/2) y ≡ h V (mod n)`
(Exercise 5.18) and `3a² ≤ 4d` (Exercise 5.14). -/
theorem exists_rep_of_reduce {A h n d : ℤ} (hA : 0 < A) (hdisc : 4 * h ^ 2 - 4 * A * n = -4 * d)
    (hd : 0 < d) :
    ∃ a W V γ : ℤ, 0 < a ∧ 3 * a ^ 2 ≤ 4 * d ∧ W ^ 2 + d * V ^ 2 = a * n ∧ W = h * V + n * γ := by
  have hP : Pos (A, 2 * h, n) := ⟨by simp only [ofTriple, disc]; nlinarith, hA⟩
  have hred := reduce_reduced hP
  obtain ⟨α, β, γ, δ, hdet, hg⟩ := reduce_equiv A (2 * h) n
  set g := ofTriple (reduce A (2 * h) n)
  obtain ⟨g₀, g₁, g₂, g₃⟩ := hred.bounds
  have hgD : g.disc = -4 * d := by
    rw [(Equiv.disc_eq ⟨α, β, γ, δ, hdet, hg⟩), disc]; simp only; linarith
  have ha : g.a = A * α ^ 2 + 2 * h * α * γ + n * γ ^ 2 := by rw [hg]; simp [subst, eval]
  have hb : g.b = 2 * (A * α * β + h * (α * δ + β * γ) + n * γ * δ) := by
    rw [hg]; simp [subst]; ring
  set b₀ := A * α * β + h * (α * δ + β * γ) + n * γ * δ
  have hc : g.c = A * β ^ 2 + 2 * h * β * δ + n * δ ^ 2 := by rw [hg]; simp [subst, eval]
  refine ⟨g.a, -g.a * β + b₀ * α, α, γ, g₀, ?_, ?_, ?_⟩
  · simp only [disc] at hgD
    have : g.b ^ 2 ≤ g.a ^ 2 := sq_le_sq' (by linarith) g₂
    nlinarith
  · simp only [disc] at hgD
    rw [hb] at hgD
    have hn : n = g.a * β ^ 2 - 2 * b₀ * α * β + g.c * α ^ 2 := by
      rw [ha, hc]; linear_combination (-(n * (α * δ - β * γ + 1))) * hdet
    have h' : b₀ ^ 2 + d = g.a * g.c := by linarith
    rw [hn]; linear_combination α ^ 2 * h'
  · rw [ha]; linear_combination (h * α + n * γ) * hdet

/-- `v < p` when `d v² ≤ a n`, `3a² ≤ 4d`, `n² ≤ d³` and `27 n ≤ p³`: then
`27 v¹² ≤ 64 n⁴ < 27 p¹²`. -/
theorem lt_of_small {n d a v p : ℕ} (hn : 0 < n) (hd : 0 < d) (h₁ : d * (v * v) ≤ a * n)
    (h₂ : 3 * (a * a) ≤ 4 * d) (h₃ : n * n ≤ d * d * d) (hp : 27 * n ≤ p ^ 3) : v < p := by
  by_contra hc; push Not at hc
  set S := v * v
  -- `3 d S² ≤ 4 n²`
  have e₁ : 3 * d * (S * S) ≤ 4 * (n * n) := by
    have : 3 * (d * S) * (d * S) ≤ 3 * (a * n) * (a * n) := by
      have := Nat.mul_le_mul h₁ h₁; nlinarith
    have : d * (3 * d * (S * S)) ≤ d * (4 * (n * n)) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hd
  -- `27 S⁶ ≤ 64 n⁴`
  have e₂ : 27 * (S * S) ^ 3 ≤ 64 * (n * n) ^ 2 := by
    have h₄ := Nat.pow_le_pow_left e₁ 3
    have : (n * n) * (27 * (S * S) ^ 3) ≤ (n * n) * (64 * (n * n) ^ 2) := by
      calc (n * n) * (27 * (S * S) ^ 3) ≤ (d * d * d) * (27 * (S * S) ^ 3) :=
            Nat.mul_le_mul_right _ h₃
        _ = (3 * d * (S * S)) ^ 3 := by ring
        _ ≤ (4 * (n * n)) ^ 3 := h₄
        _ = (n * n) * (64 * (n * n) ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  -- `S ≥ p²`, so `S⁶ ≥ p¹² ≥ 27⁴ n⁴`
  have e₃ : p * p ≤ S := Nat.mul_le_mul hc hc
  have e₄ : (27 * n) ^ 4 ≤ (p * p) ^ 6 := by
    calc (27 * n) ^ 4 ≤ (p ^ 3) ^ 4 := Nat.pow_le_pow_left hp 4
      _ = (p * p) ^ 6 := by ring
  have e₅ : (p * p) ^ 6 ≤ (S * S) ^ 3 := by
    calc (p * p) ^ 6 = ((p * p) * (p * p)) ^ 3 := by ring
      _ ≤ (S * S) ^ 3 := Nat.pow_le_pow_left (Nat.mul_le_mul e₃ e₃) 3
  have : 27 * (27 * n) ^ 4 ≤ 64 * (n * n) ^ 2 := by linarith
  have : (n * n) ^ 2 * 64 < (n * n) ^ 2 * (27 * 27 ^ 4) := by
    have : 0 < (n * n) ^ 2 := by positivity
    omega
  nlinarith

/-- `n ∤ x₀ (±V) ∓ W` when `W ≡ h V (mod n)`, `V` is coprime to `n` and `n ∤ x₀ ± h`. -/
theorem not_dvd_of_signs {n : ℤ} {x₀ h V W : ℤ} (hW : n ∣ W - h * V) (hV : IsCoprime V n)
    (hx : ¬n ∣ x₀ - h) (hx' : ¬n ∣ x₀ + h) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : ¬n ∣ x₀ * (s * V) - t * W := by
  intro hd
  have : n ∣ V * (s * x₀ - t * h) := by
    have := dvd_sub hd (dvd_mul_of_dvd_right hW (-t))
    convert this using 1; ring
  have h₂ := hV.symm.dvd_of_dvd_mul_left this
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact hx (by simpa using h₂)
  · exact hx' (by simpa using h₂)
  · exact hx' (by have := dvd_neg.2 h₂; convert this using 1; ring)
  · exact hx (by have := dvd_neg.2 h₂; convert this using 1; ring)

/-- **A second representation exists** (the heart of McKee's argument): for `n = p q`,
`p ≠ q` primes above `3 n^{1/3}`, `n = x₀² + d` with `gcd(x₀, n) = 1` and `n² ≤ d³`, there
are `a ≤ 2√(d/3)` and `a n = w² + d v²` with `v ≥ 1` and `w ≢ ±x₀ v (mod n)`. -/
theorem exists_witness {n d x₀ p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hn : n = p * q) (hp27 : 27 * n ≤ p ^ 3) (hq27 : 27 * n ≤ q ^ 3) (hd : n = x₀ * x₀ + d)
    (hd0 : 0 < d) (hd3 : n * n ≤ d * d * d) (hcop : Nat.Coprime x₀ n) :
    ∃ a w v, 1 ≤ a ∧ 3 * (a * a) ≤ 4 * d ∧ a * n = w * w + d * (v * v) ∧ 1 ≤ v ∧
      (x₀ * v % n + n - w % n) % n ≠ 0 ∧ (x₀ * v + w) % n ≠ 0 := by
  have hn0 : 0 < n := by rw [hn]; exact Nat.mul_pos hp.pos hq.pos
  have hp2 : p ≠ 2 := by rintro rfl; have := hp27; rw [hn] at this; nlinarith [hq.two_le]
  have hq2 : q ≠ 2 := by rintro rfl; have := hq27; rw [hn] at this; nlinarith [hp.two_le]
  have hpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  -- `h ≡ x₀ (mod p)`, `h ≡ -x₀ (mod q)`
  set k : ℕ := (Nat.chineseRemainder hpq x₀ (q - x₀ % q)).1
  obtain ⟨hk₁, hk₂⟩ := (Nat.chineseRemainder hpq x₀ (q - x₀ % q)).2
  have hxq : x₀ % q < q := Nat.mod_lt _ hq.pos
  have hkp : (k : ZMod p) = x₀ := (ZMod.natCast_eq_natCast_iff _ _ _).2 hk₁
  have hkq : (k : ZMod q) = -x₀ := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hk₂, Nat.cast_sub hxq.le, ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  -- `n ∣ k² + d`
  have hdvd : n ∣ k * k + d := by
    rw [hn]
    refine hpq.mul_dvd_of_dvd_of_dvd ((ZMod.natCast_eq_zero_iff _ _).1 ?_)
      ((ZMod.natCast_eq_zero_iff _ _).1 ?_)
    · have : ((n : ℕ) : ZMod p) = 0 := by rw [hn, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      rw [hd] at this; push_cast at this ⊢; rw [hkp]; exact this
    · have : ((n : ℕ) : ZMod q) = 0 := by rw [hn, Nat.cast_mul, ZMod.natCast_self, mul_zero]
      rw [hd] at this; push_cast at this ⊢; rw [hkq]; linear_combination this
  obtain ⟨A, hA⟩ := hdvd
  have hA0 : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · rw [h0] at hA; omega
    · exact h0
  obtain ⟨a, W, V, γ, ha, h3a, hrep, hWV⟩ := exists_rep_of_reduce (A := (A : ℤ)) (h := (k : ℤ))
    (n := (n : ℤ)) (d := (d : ℤ)) (by exact_mod_cast hA0)
    (by have : ((k * k + d : ℕ) : ℤ) = n * A := by rw [hA]; push_cast; ring
        push_cast at this; linear_combination 4 * this) (by exact_mod_cast hd0)
  have hdn : d ≤ n := by omega
  -- `V ≠ 0`: else `W = n γ` and `a = n γ² ≥ n`, against `3a² ≤ 4d ≤ 4n`
  have hV0 : V ≠ 0 := by
    rintro rfl
    simp only [mul_zero, add_zero, zero_pow two_ne_zero] at hrep hWV
    rw [hWV] at hrep
    have hγ : γ ≠ 0 := by
      rintro rfl; simp at hrep
      rcases hrep with h | h
      · linarith
      · exact absurd h (by exact_mod_cast hn0.ne')
    have : (n : ℤ) * γ ^ 2 = a := by
      have h' : (n : ℤ) * (n * γ ^ 2) = n * a := by linear_combination hrep
      exact mul_left_cancel₀ (by exact_mod_cast hn0.ne') h'
    have : (n : ℤ) ≤ a := by rw [← this]; nlinarith [sq_pos_of_ne_zero hγ]
    have : (n : ℤ) * n ≤ a * a := by nlinarith
    have h4 : (3 : ℤ) * (n * n) ≤ 4 * n := by nlinarith [show (d : ℤ) ≤ n by exact_mod_cast hdn]
    have : (2 : ℤ) ≤ n := by exact_mod_cast (show 2 ≤ n by rw [hn]; nlinarith [hp.two_le,
      hq.two_le])
    nlinarith
  set v := V.natAbs
  set w := W.natAbs
  have hv1 : 1 ≤ v := Int.natAbs_pos.2 hV0
  have hrep' : a.toNat * n = w * w + d * (v * v) := by
    have ew : ((w * w : ℕ) : ℤ) = W ^ 2 := by
      push_cast; rw [Int.natCast_natAbs, abs_mul_abs_self, sq]
    have ev : ((v * v : ℕ) : ℤ) = V ^ 2 := by
      push_cast; rw [Int.natCast_natAbs, abs_mul_abs_self, sq]
    have : ((a.toNat * n : ℕ) : ℤ) = ((w * w + d * (v * v) : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_mul d, ew, ev, Nat.cast_mul, Int.toNat_of_nonneg ha.le]
      linear_combination -hrep
    exact_mod_cast this
  have h3 : 3 * (a.toNat * a.toNat) ≤ 4 * d := by
    have : ((3 * (a.toNat * a.toNat) : ℕ) : ℤ) ≤ ((4 * d : ℕ) : ℤ) := by
      push_cast [Int.toNat_of_nonneg ha.le]; linarith
    exact_mod_cast this
  have hle : d * (v * v) ≤ a.toNat * n := by omega
  have hvp := lt_of_small hn0 hd0 hle h3 hd3 hp27
  have hvq := lt_of_small hn0 hd0 hle h3 hd3 hq27
  have hcopv : Nat.Coprime v n := by
    rw [hn]
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦
        absurd (Nat.le_of_dvd (by omega) h) (by omega))
    · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h ↦
        absurd (Nat.le_of_dvd (by omega) h) (by omega))
  have hVc : IsCoprime V (n : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using hcopv
  -- `n ∤ x₀ ∓ k`, by `p` and `q`
  have hx : ¬(n : ℤ) ∣ x₀ - k := fun h ↦ by
    have hqd : (q : ℤ) ∣ x₀ - k := (Int.natCast_dvd_natCast.2 ⟨p, by rw [hn]; ring⟩).trans h
    have : ((2 * x₀ : ℕ) : ZMod q) = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hqd
      push_cast at this ⊢; rw [hkq] at this; linear_combination this
    rcases (Nat.Prime.dvd_mul hq).1 ((ZMod.natCast_eq_zero_iff _ _).1 this) with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact absurd (Nat.dvd_gcd h (show q ∣ n from ⟨p, by rw [hn]; ring⟩))
        (by rw [hcop]; exact hq.not_dvd_one)
  have hx' : ¬(n : ℤ) ∣ x₀ + k := fun h ↦ by
    have hpd : (p : ℤ) ∣ x₀ + k := (Int.natCast_dvd_natCast.2 ⟨q, hn⟩).trans h
    have : ((2 * x₀ : ℕ) : ZMod p) = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpd
      push_cast at this ⊢; rw [hkp] at this; linear_combination this
    rcases (Nat.Prime.dvd_mul hp).1 ((ZMod.natCast_eq_zero_iff _ _).1 this) with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact absurd (Nat.dvd_gcd h (show p ∣ n from ⟨q, hn⟩))
        (by rw [hcop]; exact hp.not_dvd_one)
  have hW : (n : ℤ) ∣ W - k * V := ⟨γ, by rw [hWV]; ring⟩
  -- the signs of `v = |V|`, `w = |W|`
  obtain ⟨s, hs, hvs⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (v : ℤ) = s * V := by
    rcases Int.natAbs_eq V with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_mul]; exact h.symm⟩
    · exact ⟨-1, Or.inr rfl, by linear_combination h⟩
  obtain ⟨t, ht, hwt⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ (w : ℤ) = t * W := by
    rcases Int.natAbs_eq W with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_mul]; exact h.symm⟩
    · exact ⟨-1, Or.inr rfl, by linear_combination h⟩
  refine ⟨a.toNat, w, v, by omega, h3, hrep', hv1, fun hc ↦ ?_, fun hc ↦ ?_⟩
  · -- `x₀ v - w ≡ 0 (mod n)`
    apply not_dvd_of_signs hW hVc hx hx' hs ht
    have hle' : w % n ≤ x₀ * v % n + n := by have := Nat.mod_lt w hn0; omega
    have : ((((x₀ * v % n + n - w % n) % n : ℕ)) : ZMod n) = x₀ * v - w := by
      simp only [ZMod.natCast_mod]
      push_cast [Nat.cast_sub hle', ZMod.natCast_mod, ZMod.natCast_self]; ring
    rw [hc, Nat.cast_zero] at this
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((x₀ : ℤ) * v - w) n).1 (by
      push_cast; rw [← this])
    rwa [hvs, hwt] at this
  · have := not_dvd_of_signs hW hVc hx hx' hs (t := -t) (by rcases ht with rfl | rfl <;> simp)
    apply this
    have := Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hc)
    push_cast at this; rw [hvs, hwt] at this
    convert this using 1; ring

/-- **Completeness of Algorithm 5.6.3**: for `n > 1` with no prime factor below `3n^{1/3}`,
if the test answers "n is prime" (`none`), `n` is prime. -/
theorem mckee_complete {n : ℕ} (hn : 1 < n)
    (hsmall : ∀ p, p.Prime → p ∣ n → 27 * n ≤ p ^ 3) (h : mckee n = none) : n.Prime := by
  by_contra hnp
  unfold mckee at h
  dsimp only at h
  split_ifs at h with h₁ h₂
  have hsq : ∀ s, s * s ≠ n := fun s hs ↦ h₁ (by rw [← hs, Nat.sqrt_eq])
  obtain ⟨p, q, hp, hq, hne, hpq⟩ := eq_mul_of_large_factors hn hsmall hnp hsq
  have hp27 := hsmall p hp ⟨q, hpq⟩
  have hq27 := hsmall q hq ⟨p, by rw [hpq]; ring⟩
  have hn6 : 6 ≤ n := by
    have hpn : p ≤ n := Nat.le_of_dvd (by omega) ⟨q, hpq⟩
    have : 27 * n ≤ n ^ 3 := hp27.trans (Nat.pow_le_pow_left hpn 3)
    by_contra hc; push Not at hc
    interval_cases n <;> norm_num at this
  -- `t = ⌈n^{2/3}⌉ < n`, `x₀ ≥ 1`, `t ≤ d < n`
  obtain ⟨ht₁, ht₂⟩ := ceilTwoThirds_spec (n := n) (by omega)
  set t := ceilTwoThirds n
  have htn : t < n := by
    by_contra hc; push Not at hc
    have : (n - 1) * (n - 1) * (n - 1) ≤ (t - 1) * (t - 1) * (t - 1) := by
      have := Nat.sub_le_sub_right hc 1; exact Nat.mul_le_mul (Nat.mul_le_mul this this) this
    have : n * n ≤ (n - 1) * (n - 1) * (n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [show m + 6 - 1 = m + 5 by omega]; nlinarith
    omega
  set x₀ := Nat.sqrt (n - t)
  have hx₀ : x₀ * x₀ ≤ n - t := Nat.sqrt_le _
  have hx₁ : 1 ≤ x₀ := Nat.le_sqrt.2 (by omega)
  set d := n - x₀ * x₀
  have hd : n = x₀ * x₀ + d := by omega
  have hdt : t ≤ d := by omega
  have hxx : 1 ≤ x₀ * x₀ := Nat.mul_le_mul hx₁ hx₁
  have ht1 : 1 ≤ t := by nlinarith
  have hd0 : 0 < d := by omega
  have hd3 : n * n ≤ d * d * d := ht₁.trans (Nat.mul_le_mul (Nat.mul_le_mul hdt hdt) hdt)
  -- `gcd(n, d) = 1`
  have hg : Nat.gcd n d = 1 := by
    have hpos : 0 < Nat.gcd n d := Nat.gcd_pos_of_pos_left _ (by omega)
    have : Nat.gcd n d ≤ d := Nat.le_of_dvd hd0 (Nat.gcd_dvd_right _ _)
    by_contra hc; exact h₂ ⟨by omega, by omega⟩
  have hcop : Nat.Coprime x₀ n := by
    rw [Nat.Coprime, ← Nat.dvd_one, ← hg]
    refine Nat.dvd_gcd (Nat.gcd_dvd_right _ _) ?_
    have h₁ : Nat.gcd x₀ n ∣ n := Nat.gcd_dvd_right _ _
    have h₂ : Nat.gcd x₀ n ∣ x₀ * x₀ := dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
    exact Nat.dvd_sub h₁ h₂
  obtain ⟨a, w, v, ha, h3a, hrep, hv, hc, hc'⟩ :=
    exists_witness hp hq hne hpq hp27 hq27 hd hd0 hd3 hcop
  -- the search finds it
  obtain ⟨hfs, hfd⟩ := factorPairs_spec hd0
  obtain ⟨-, hroots⟩ := rootsMod_spec (a * n % d) hfs
  rw [hfd] at hroots
  have hwd : w % d ∈
      (rootsMod (a * n % d) (withNonresidues (factorPairs (trialDivision d)))).2 := by
    refine (hroots _).2 ⟨Nat.mod_lt _ hd0, ?_⟩
    rw [Nat.mod_mod, ← Nat.mul_mod, hrep, Nat.add_mul_mod_self_left]
  have hcls := searchClass_isSome (n := n) (d := d) (a := a) (x₀ := x₀) hd0 hv hrep hc hc'
    (i := w / d) (fuel := Nat.sqrt (a * n) / d + 1) (w₀ := w % d)
    (by have : w ≤ Nat.sqrt (a * n) := Nat.le_sqrt.2 (by omega)
        have := Nat.div_le_div_right (c := d) this; omega)
    (Nat.mod_add_div w d).symm
  have hroot := searchRoots_isSome hwd hcls
  have had : a ≤ d := by
    by_contra hc; push Not at hc
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · nlinarith
    · nlinarith
  have hA := searchA_isSome (fs := withNonresidues (factorPairs (trialDivision d))) h3a hroot
    (k := a - 1) (a := 1) (fuel := d) (by omega) (by omega)
  split at h
  · simp at h
  · next hn' => rw [hn'] at hA; simp at hA
