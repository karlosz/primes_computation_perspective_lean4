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
counted_def searchA (n d x₀ : ℕ) (fs : List (ℕ × ℕ)) : (a fuel : ℕ) → Option ℕ
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
      match searchA n d x₀ (factorPairs (trialDivision d)) 1 d with      -- 3. [Congruences]
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
    {fs : List (ℕ × ℕ)} {a fuel g : ℕ} (h : searchA n d x₀ fs a fuel = some g) :
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
