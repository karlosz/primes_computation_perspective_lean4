import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter2.Poly

/-!
# §9.5.8 Nussbaumer convolution (Algorithm 9.5.25) and quasi-linear multiplication

The product in `S_m = ℤ[x]/(x^m + 1)` (`m = 2^k`) — the *negacyclic convolution* of two
length-`m` coefficient lists — is computed by Nussbaumer's method: with `m = m₁ r`,
`r ≤ m₁`, an element of `S_m` is a polynomial of degree `< r` in `t` over `S_{m₁}`, where
`t^r = x`.  The product of two such polynomials (degree `< 2r - 1`) is a cyclic convolution
of length `L = 2r` over `S_{m₁}`, computed by a fast Fourier transform whose root of unity
`ω = x^{m₁/r}` is a power of `x`: multiplying by it is a signed rotation, so the transforms
use only additions, and the `L` pointwise products are recursive products in `S_{m₁}`.  The
inverse transform gives `L` times the result, divided out exactly.

Over `ℤ` this gives a multiplication of `N`-bit integers in `O(N log³ N)` bit operations:
the quasi-linear multiplication needed for the `n^{1/4}` bound of §5.5.  Its running time is
in `NussbaumerCost.lean`, and the cost model it realizes, `nussModel`, in `NussModel.lean`.
-/

namespace PrimeNumbers.Chapter9

open PrimeNumbers.Chapter2

/-! ## Arithmetic in `S_m = ℤ[x]/(x^m + 1)` -/

/-- Addition in `S_m`, coefficientwise. -/
counted_def vadd (u v : List ℤ) : List ℤ := List.zipWith (· + ·) u v

/-- Subtraction in `S_m`, coefficientwise. -/
counted_def vsub (u v : List ℤ) : List ℤ := List.zipWith (· - ·) u v

/-- Multiplication by `x^j` in `S_m` (`j < m`): a rotation, the coefficients wrapping around
with a change of sign (`x^m = -1`). -/
counted_def rotLow (m j : ℕ) (u : List ℤ) : List ℤ :=
  (u.drop (m - j)).map Neg.neg ++ u.take (m - j)

/-- Multiplication by `x^j` in `S_m` for `j < 2m` (`x^m = -1`). -/
counted_def rot (m j : ℕ) (u : List ℤ) : List ℤ :=
  if j < m then rotLow m j u else (rotLow m (j - m) u).map Neg.neg

/-- The entries at even positions. -/
counted_def evens {α : Type} : List α → List α
  | a :: _ :: l => a :: evens l
  | [a] => [a]
  | [] => []

/-- The entries at odd positions. -/
counted_def odds {α : Type} : List α → List α
  | _ :: b :: l => b :: odds l
  | _ => []

theorem length_evens {α : Type} : ∀ l : List α, (evens l).length = (l.length + 1) / 2
  | a :: b :: l => by simp only [evens, List.length_cons, length_evens l]; omega
  | [a] => by simp [evens]
  | [] => by simp [evens]

theorem length_odds {α : Type} : ∀ l : List α, (odds l).length = l.length / 2
  | a :: b :: l => by simp only [odds, List.length_cons, length_odds l]; omega
  | [a] => by simp [odds]
  | [] => by simp [odds]

/-- The twiddled odd half: `x^{e i mod 2m} · o_i`. -/
counted_def twiddle (m e : ℕ) : (i : ℕ) → List (List ℤ) → List (List ℤ)
  | _, [] => []
  | i, o :: os => rot m (e * i % (2 * m)) o :: twiddle m e (i + 1) os

/-- **The fast Fourier transform over `S_m`** with root `ω = x^e` (radix 2): for `v` of length
`L = 2^l`, the list `(∑_j ω^{ij} v_j)_{i < L}`. -/
counted_def fft (m e : ℕ) (vs : List (List ℤ)) : List (List ℤ) :=
  if vs.length ≤ 1 then vs
  else
    let E := fft m (2 * e) (evens vs)
    let T := twiddle m e 0 (fft m (2 * e) (odds vs))
    List.zipWith vadd E T ++ List.zipWith vsub E T
termination_by vs.length
decreasing_by
  · rw [length_evens]; omega
  · rw [length_odds]; omega

/-- Block `j` of `a`: the coefficients `a_{j + r l}`, `l < m₁` — the coefficient of `t^j` when
`a ∈ S_m` is written over `S_{m₁}` with `t^r = x`. -/
counted_def block (r m₁ j : ℕ) (a : List ℤ) : List ℤ :=
  (List.range m₁).map fun l ↦ a.getD (j + r * l) 0

/-- The `r` blocks of `a`, through an array, in linear time (`blocks_eq`). -/
counted_def blocks (r m₁ : ℕ) (a : List ℤ) : List (List ℤ) :=
  let arr := a.toArray
  (List.range r).map fun j ↦ (List.range m₁).map fun l ↦ arr.getD (j + r * l) 0

/-- The inverse of `block`: the coefficient `j + r l` is entry `l` of block `j` (through
arrays, in linear time; `unblock_eq`). -/
counted_def unblock (r m : ℕ) (D : List (List ℤ)) : List ℤ :=
  let arr := (D.map List.toArray).toArray
  (List.range m).map fun i ↦ (arr.getD (i % r) #[]).getD (i / r) 0

theorem blocks_eq (r m₁ : ℕ) (a : List ℤ) :
    blocks r m₁ a = (List.range r).map fun j ↦ block r m₁ j a := by
  simp [blocks, block, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem unblock_eq (r m : ℕ) (D : List (List ℤ)) :
    unblock r m D = (List.range m).map fun i ↦ (D.getD (i % r) []).getD (i / r) 0 := by
  simp only [unblock, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  refine List.map_congr_left fun i _ ↦ ?_
  cases h : D[i % r]? <;> simp [h]

/-- The negacyclic product in `S_m` by the schoolbook method: coefficient `s` is
`∑_{i+j=s} a_i b_j - ∑_{i+j=s+m} a_i b_j`. -/
counted_def ncTerm (m s : ℕ) (b : List ℤ) : (i : ℕ) → List ℤ → ℤ
  | _, [] => 0
  | i, ai :: as =>
    (if i ≤ s then ai * b.getD (s - i) 0 else -(ai * b.getD (m + s - i) 0)) +
      ncTerm m s b (i + 1) as

counted_def ncSchool (m : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range m).map fun s ↦ ncTerm m s b 0 a

/-- **Algorithm 9.5.25 (Nussbaumer convolution)**: the product of `a, b ∈ S_{2^k}`. -/
counted_def nussbaumer (k : ℕ) (a b : List ℤ) : List ℤ :=
  if k ≤ 2 then ncSchool (2 ^ k) a b
  else
    let k₁ := (k + 1) / 2              -- m₁ = 2^k₁
    let k₂ := k / 2                    -- r = 2^k₂ ≤ m₁
    let e := 2 ^ (k₁ - k₂)             -- ω = x^e, of order L = 2r in S_{m₁}
    let zero := List.replicate (2 ^ k₁) (0 : ℤ)
    let A := blocks (2 ^ k₂) (2 ^ k₁) a ++ List.replicate (2 ^ k₂) zero
    let B := blocks (2 ^ k₂) (2 ^ k₁) b ++ List.replicate (2 ^ k₂) zero
    let P := List.zipWith (nussbaumer k₁) (fft (2 ^ k₁) e A) (fft (2 ^ k₁) e B)
    let C := (fft (2 ^ k₁) (2 * 2 ^ k₁ - e) P).map fun v ↦ v.map (· / 2 ^ (k₂ + 1))
    let D := (List.range (2 ^ k₂)).map fun j ↦
      vadd (C.getD j zero) (rot (2 ^ k₁) 1 (C.getD (j + 2 ^ k₂) zero))
    unblock (2 ^ k₂) (2 ^ k) D
termination_by k
decreasing_by omega

/-! ## Correctness

Lists of length `m` represent elements of `S m = ℤ[x]/(x^m + 1)` (`AdjoinRoot`), uniquely. -/

open Polynomial PrimeNumbers.Chapter2.Poly

/-- The ring `ℤ[x]/(x^m + 1)`. -/
abbrev S (m : ℕ) := AdjoinRoot (X ^ m + 1 : ℤ[X])

/-- The element of `S m` represented by a coefficient list. -/
noncomputable def ev (m : ℕ) (v : List ℤ) : S m := AdjoinRoot.mk _ (toPolynomial v)

theorem root_pow_m (m : ℕ) : AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ m = -1 := by
  have h : AdjoinRoot.mk (X ^ m + 1 : ℤ[X]) (X ^ m + 1) = 0 := AdjoinRoot.mk_self
  rw [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem root_pow_two_m (m : ℕ) : AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ (2 * m) = 1 := by
  rw [mul_comm, pow_mul, root_pow_m]; norm_num

theorem root_pow_mod (m n : ℕ) :
    AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ (n % (2 * m)) = AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n (2 * m), pow_add, pow_mul, root_pow_two_m, one_pow, mul_one]

theorem toPolynomial_zipWith_add : ∀ u v : List ℤ, u.length = v.length →
    toPolynomial (List.zipWith (· + ·) u v) = toPolynomial u + toPolynomial v
  | [], [], _ => by simp
  | a :: u, b :: v, h => by
    simp only [List.zipWith_cons_cons, toPolynomial_cons,
      toPolynomial_zipWith_add u v (by simpa using h), C_add]; ring

theorem toPolynomial_zipWith_sub : ∀ u v : List ℤ, u.length = v.length →
    toPolynomial (List.zipWith (· - ·) u v) = toPolynomial u - toPolynomial v
  | [], [], _ => by simp
  | a :: u, b :: v, h => by
    simp only [List.zipWith_cons_cons, toPolynomial_cons,
      toPolynomial_zipWith_sub u v (by simpa using h), C_sub]; ring

theorem ev_vadd {m : ℕ} {u v : List ℤ} (h : u.length = v.length) :
    ev m (vadd u v) = ev m u + ev m v := by
  rw [ev, vadd, toPolynomial_zipWith_add u v h, map_add]; rfl

theorem ev_vsub {m : ℕ} {u v : List ℤ} (h : u.length = v.length) :
    ev m (vsub u v) = ev m u - ev m v := by
  rw [ev, vsub, toPolynomial_zipWith_sub u v h, map_sub]; rfl

theorem length_vadd {u v : List ℤ} (h : u.length = v.length) : (vadd u v).length = u.length := by
  simp [vadd, h]

theorem length_vsub {u v : List ℤ} (h : u.length = v.length) : (vsub u v).length = u.length := by
  simp [vsub, h]

theorem toPolynomial_map_neg (u : List ℤ) : toPolynomial (u.map Neg.neg) = -toPolynomial u := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih]; ring

theorem length_rotLow {m j : ℕ} {u : List ℤ} (hu : u.length = m) (hj : j ≤ m) :
    (rotLow m j u).length = m := by
  simp [rotLow, hu]

theorem ev_rotLow {m j : ℕ} {u : List ℤ} (hu : u.length = m) (hj : j ≤ m) :
    ev m (rotLow m j u) = AdjoinRoot.root _ ^ j * ev m u := by
  have hsplit := congrArg toPolynomial (List.take_append_drop (m - j) u)
  rw [toPolynomial_append, List.length_take, min_eq_left (by omega)] at hsplit
  simp only [ev, rotLow, toPolynomial_append, toPolynomial_map_neg, List.length_map,
    List.length_drop, hu, show m - (m - j) = j by omega]
  conv_rhs => rw [← hsplit]
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_mk]
  refine ⟨-toPolynomial (u.drop (m - j)), ?_⟩
  have hm : (X : ℤ[X]) ^ m = X ^ (m - j) * X ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [hm]
  ring

theorem length_rot {m j : ℕ} {u : List ℤ} (hu : u.length = m) (hj : j < 2 * m) :
    (rot m j u).length = m := by
  unfold rot; split_ifs
  · exact length_rotLow hu (by omega)
  · rw [List.length_map]; exact length_rotLow hu (by omega)

theorem ev_rot {m j : ℕ} {u : List ℤ} (hu : u.length = m) (hj : j < 2 * m) :
    ev m (rot m j u) = AdjoinRoot.root _ ^ j * ev m u := by
  unfold rot; split_ifs with h
  · exact ev_rotLow hu (by omega)
  · have := ev_rotLow (m := m) (j := j - m) hu (by omega)
    rw [ev, toPolynomial_map_neg, map_neg, ← ev, this,
      show AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ j =
        AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ m * AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ (j - m) by
        rw [← pow_add]; congr 1; omega, root_pow_m]
    ring

/-! ### The discrete Fourier transform -/

section DFT

variable {R : Type} [CommRing R]

/-- Entry `i` of the discrete Fourier transform of `v` with root `ω`: `∑_j ω^{ij} v_j`. -/
def dftAt (ω : R) (v : List R) (i : ℕ) : R :=
  ∑ j ∈ Finset.range v.length, ω ^ (i * j) * v.getD j 0

theorem getD_evens {α : Type} (d : α) : ∀ (v : List α) (t : ℕ), (evens v).getD t d = v.getD (2 * t) d
  | a :: b :: l, 0 => by simp [evens]
  | a :: b :: l, t + 1 => by
    simp only [evens, List.getD_cons_succ, getD_evens d l t]
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring]; simp
  | [a], 0 => by simp [evens]
  | [a], t + 1 => by simp [evens]
  | [], t => by simp [evens]

theorem getD_odds {α : Type} (d : α) : ∀ (v : List α) (t : ℕ), (odds v).getD t d = v.getD (2 * t + 1) d
  | a :: b :: l, 0 => by simp [odds]
  | a :: b :: l, t + 1 => by
    simp only [odds, List.getD_cons_succ, getD_odds d l t]
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring]; simp
  | [a], t => by simp [odds]
  | [], t => by simp [odds]

theorem evens_map {α β : Type} (f : α → β) : ∀ v : List α, evens (v.map f) = (evens v).map f
  | a :: b :: l => by simp [evens, evens_map f l]
  | [a] => by simp [evens]
  | [] => by simp [evens]

theorem odds_map {α β : Type} (f : α → β) : ∀ v : List α, odds (v.map f) = (odds v).map f
  | a :: b :: l => by simp [odds, odds_map f l]
  | [a] => by simp [odds]
  | [] => by simp [odds]

theorem sum_range_two_mul (f : ℕ → R) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), f j = ∑ t ∈ Finset.range n, f (2 * t) + ∑ t ∈ Finset.range n, f (2 * t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- **Cooley–Tukey**: a transform of length `2n` is two transforms of length `n` with root
`ω²`, of the even and the odd entries. -/
theorem dftAt_split (ω : R) {v : List R} {n : ℕ} (hv : v.length = 2 * n) (i : ℕ) :
    dftAt ω v i = dftAt (ω ^ 2) (evens v) i + ω ^ i * dftAt (ω ^ 2) (odds v) i := by
  simp only [dftAt, length_evens, length_odds, hv, show (2 * n + 1) / 2 = n by omega,
    show 2 * n / 2 = n by omega, getD_evens, getD_odds, Finset.mul_sum]
  rw [sum_range_two_mul]
  congr 1
  · refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← pow_mul]; ring_nf
  · refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← pow_mul, ← mul_assoc, ← pow_add]; ring_nf

/-- A transform with `ω^n = 1` is periodic with period `n`. -/
theorem dftAt_add_period {ω : R} {n : ℕ} (h : ω ^ n = 1) (v : List R) (i : ℕ) :
    dftAt ω v (i + n) = dftAt ω v i := by
  simp only [dftAt]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show (i + n) * j = i * j + n * j by ring, pow_add, pow_mul ω n j, h, one_pow, mul_one]

theorem geom_sum_two_pow (z : R) : ∀ l : ℕ,
    ∑ i ∈ Finset.range (2 ^ l), z ^ i = ∏ b ∈ Finset.range l, (1 + z ^ 2 ^ b)
  | 0 => by simp
  | l + 1 => by
    rw [Finset.prod_range_succ, ← geom_sum_two_pow z l, pow_succ, mul_two, Finset.sum_range_add]
    simp_rw [pow_add]
    rw [← Finset.mul_sum]; ring

/-- **Orthogonality**: if `ω^{2^{l-1}} = -1`, then `∑_{i < 2^l} ω^{is}` is `2^l` when `2^l ∣ s`
and `0` otherwise. -/
theorem sum_pow_mul_eq {ω : R} {l : ℕ} (hl : 1 ≤ l) (hω : ω ^ 2 ^ (l - 1) = -1) (s : ℕ) :
    ∑ i ∈ Finset.range (2 ^ l), ω ^ (i * s) = if 2 ^ l ∣ s then (2 ^ l : R) else 0 := by
  have hL : ω ^ 2 ^ l = 1 := by
    rw [show 2 ^ l = 2 ^ (l - 1) * 2 by rw [← pow_succ]; congr 1; omega, pow_mul, hω]; norm_num
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    simp [show ∀ i, i * (2 ^ l * c) = 2 ^ l * (i * c) from fun i ↦ by ring, pow_mul, hL]
  · have hs : s ≠ 0 := by rintro rfl; exact h (dvd_zero _)
    obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs
    have ha : a < l := by
      by_contra ha; exact h (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega)) _)
    simp_rw [mul_comm _ (2 ^ a * u), pow_mul]
    rw [geom_sum_two_pow]
    refine Finset.prod_eq_zero (i := l - 1 - a) (by simp; omega) ?_
    rw [← pow_mul, ← pow_mul, show 2 ^ a * (u * 2 ^ (l - 1 - a)) = 2 ^ (l - 1) * u by
      rw [mul_comm u, ← mul_assoc, ← pow_add, show a + (l - 1 - a) = l - 1 by omega],
      pow_mul, hω, hu.neg_one_pow]; ring

/-- **The convolution theorem**: transforming, multiplying pointwise and transforming back with
`ω⁻¹ = ω^{2^l - 1}` gives `2^l` times the acyclic convolution, for inputs supported below `r`
with `2r ≤ 2^l`. -/
theorem conv_spec {ω : R} {l : ℕ} (hl : 1 ≤ l) (hω : ω ^ 2 ^ (l - 1) = -1) {r : ℕ}
    (hr : 2 * r ≤ 2 ^ l) (a b : ℕ → R) (ha : ∀ j, r ≤ j → a j = 0) (hb : ∀ j, r ≤ j → b j = 0)
    {t : ℕ} (ht : t < 2 ^ l) :
    ∑ i ∈ Finset.range (2 ^ l), (ω ^ (2 ^ l - 1)) ^ (t * i) *
      ((∑ j ∈ Finset.range (2 ^ l), ω ^ (i * j) * a j) *
        ∑ k ∈ Finset.range (2 ^ l), ω ^ (i * k) * b k) =
    2 ^ l * ∑ j ∈ Finset.range (2 ^ l), ∑ k ∈ Finset.range (2 ^ l),
      if j + k = t then a j * b k else 0 := by
  have key : ∀ j k, (∑ i ∈ Finset.range (2 ^ l), ω ^ (i * (j + k + t * (2 ^ l - 1)))) * (a j * b k) =
      2 ^ l * if j + k = t then a j * b k else 0 := by
    intro j k
    rw [sum_pow_mul_eq hl hω]
    by_cases hj : r ≤ j
    · simp [ha j hj]
    by_cases hk : r ≤ k
    · simp [hb k hk]
    obtain ⟨L, hL⟩ : ∃ L, 2 ^ l = L + 1 := ⟨2 ^ l - 1, by have := Nat.one_le_two_pow (n := l); omega⟩
    rw [hL] at hr ht ⊢
    rw [Nat.add_sub_cancel]
    by_cases hjk : j + k = t
    · rw [if_pos ⟨t, by rw [← hjk]; ring⟩, if_pos hjk]
    · rw [if_neg, if_neg hjk, zero_mul, mul_zero]
      rintro ⟨c, hc⟩
      have e1 : j + k + t * (L + 1) = t + (L + 1) * c := by rw [← hc]; ring
      have := congrArg (· % (L + 1)) e1
      simp only [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_left] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact hjk this
  calc _ = ∑ j ∈ Finset.range (2 ^ l), ∑ k ∈ Finset.range (2 ^ l),
        (∑ i ∈ Finset.range (2 ^ l), ω ^ (i * (j + k + t * (2 ^ l - 1)))) * (a j * b k) := by
        simp_rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ ↦ ?_
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← pow_mul]; ring
    _ = _ := by simp_rw [key, Finset.mul_sum]

theorem sum_range_of_vanish {M : Type} [AddCommMonoid M] {f : ℕ → M} {n N : ℕ} (h : n ≤ N)
    (hf : ∀ j, n ≤ j → f j = 0) : ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range n, f j :=
  (Finset.sum_subset (Finset.range_subset_range.2 h) fun j _ hj ↦ hf j (by simpa using hj)).symm

/-- **Folding** the acyclic convolution of `2r` terms, evaluated at `x` with `y ↦ x^r`, into `r`
terms. -/
theorem fold_conv {R' : Type} [CommRing R'] (ψ : R →+* R') (x : R') (y : R) (r : ℕ)
    (hy : ψ y = x ^ r) (a b : ℕ → R) (ha : ∀ j, r ≤ j → a j = 0) (hb : ∀ j, r ≤ j → b j = 0) :
    let c := fun t ↦ ∑ j ∈ Finset.range (2 * r), ∑ k ∈ Finset.range (2 * r),
      if j + k = t then a j * b k else 0
    (∑ j ∈ Finset.range r, x ^ j * ψ (a j)) * (∑ k ∈ Finset.range r, x ^ k * ψ (b k)) =
      ∑ j ∈ Finset.range r, x ^ j * ψ (c j + y * c (j + r)) := by
  intro c
  have hc : ∀ t, c t = ∑ j ∈ Finset.range r, ∑ k ∈ Finset.range r,
      if j + k = t then a j * b k else 0 := by
    intro t
    simp only [c]
    rw [sum_range_of_vanish (n := r) (by omega) fun j hj ↦ by simp [ha j hj]]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact sum_range_of_vanish (n := r) (by omega) fun k hk ↦ by simp [hb k hk]
  calc _ = ∑ j ∈ Finset.range r, ∑ k ∈ Finset.range r, x ^ (j + k) * ψ (a j * b k) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        rw [map_mul, pow_add]; ring
    _ = ∑ j ∈ Finset.range r, ∑ k ∈ Finset.range r, ∑ t ∈ Finset.range (2 * r),
        x ^ t * ψ (if j + k = t then a j * b k else 0) := by
        refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun k hk ↦ ?_
        simp only [Finset.mem_range] at hj hk
        rw [Finset.sum_eq_single (j + k) (fun t _ ht ↦ by rw [if_neg (Ne.symm ht)]; simp)
          (fun h ↦ by simp at h; omega), if_pos rfl]
    _ = ∑ t ∈ Finset.range (2 * r), x ^ t * ψ (c t) := by
        simp_rw [hc, map_sum, Finset.mul_sum]
        symm; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
    _ = _ := by
        rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_add, map_mul, hy, add_comm r j, pow_add]; ring

end DFT

/-! ### The fast Fourier transform over `S m` -/

theorem getD_zipWith {α β γ : Type} (f : α → β → γ) (l : List α) (l' : List β) (dα : α)
    (dβ : β) (dγ : γ) {i : ℕ} (hi : i < l.length) (hi' : i < l'.length) :
    (List.zipWith f l l').getD i dγ = f (l.getD i dα) (l'.getD i dβ) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']

theorem length_twiddle (m e : ℕ) : ∀ (i : ℕ) (os : List (List ℤ)),
    (twiddle m e i os).length = os.length
  | _, [] => rfl
  | i, o :: os => by simp [twiddle, length_twiddle m e (i + 1) os]

theorem getD_twiddle (m e : ℕ) : ∀ (i : ℕ) (os : List (List ℤ)) (t : ℕ), t < os.length →
    (twiddle m e i os).getD t [] = rot m (e * (i + t) % (2 * m)) (os.getD t [])
  | _, [], t, h => by simp at h
  | i, o :: os, 0, _ => by simp [twiddle]
  | i, o :: os, t + 1, h => by
    simp only [twiddle, List.getD_cons_succ]
    rw [getD_twiddle m e (i + 1) os t (by simpa using h), show i + 1 + t = i + (t + 1) by ring]

@[simp] theorem ev_nil (m : ℕ) : ev m [] = 0 := by simp [ev]

theorem getD_mem' {α : Type} {l : List α} {i : ℕ} (h : i < l.length) (d : α) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem getD_map_ev (m : ℕ) (vs : List (List ℤ)) (j : ℕ) :
    (vs.map (ev m)).getD j 0 = ev m (vs.getD j []) := by
  rw [← ev_nil m, List.getD_map]

/-- **The fast Fourier transform over `S m`** computes the discrete Fourier transform with
root `ω = x^e`, for `2^l` inputs, provided `ω^{2^{l-1}} = -1`. -/
theorem fft_spec {m : ℕ} (hm : 0 < m) : ∀ (l e : ℕ) (vs : List (List ℤ)), vs.length = 2 ^ l →
    (∀ v ∈ vs, v.length = m) →
    (1 ≤ l → (AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ e) ^ 2 ^ (l - 1) = -1) →
    (fft m e vs).length = 2 ^ l ∧ (∀ v ∈ fft m e vs, v.length = m) ∧
      ∀ i < 2 ^ l, ev m ((fft m e vs).getD i []) =
        dftAt (AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ e) (vs.map (ev m)) i := by
  intro l
  induction l with
  | zero =>
    intro e vs hlen hvs he
    obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
      match vs, hlen with
      | [v], _ => exact ⟨v, rfl⟩
    rw [fft, if_pos (by simp)]
    refine ⟨by simp, hvs, fun i hi ↦ ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    simp [dftAt]
  | succ l ih =>
    intro e vs hlen hvs he
    rw [fft, if_neg (by rw [hlen]; have := Nat.one_lt_two_pow (n := l + 1) (by omega); omega)]
    set ω := AdjoinRoot.root (X ^ m + 1 : ℤ[X])
    have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by ring
    have hev : (evens vs).length = 2 ^ l := by rw [length_evens, hlen, h2l]; omega
    have hod : (odds vs).length = 2 ^ l := by rw [length_odds, hlen, h2l]; omega
    have hhalf : (AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ e) ^ 2 ^ l = -1 := he (by omega)
    have he' : 1 ≤ l → (AdjoinRoot.root (X ^ m + 1 : ℤ[X]) ^ (2 * e)) ^ 2 ^ (l - 1) = -1 := by
      intro hl
      rw [← hhalf, ← pow_mul, ← pow_mul]
      congr 1
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; ring
    have hvE : ∀ v ∈ evens vs, v.length = m := fun v hv ↦ hvs v (by
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv
      rw [← List.getD_eq_getElem _ [] ht, getD_evens]
      exact getD_mem' (by rw [hlen, h2l]; rw [hev] at ht; omega) [])
    have hvO : ∀ v ∈ odds vs, v.length = m := fun v hv ↦ hvs v (by
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv
      rw [← List.getD_eq_getElem _ [] ht, getD_odds]
      exact getD_mem' (by rw [hlen, h2l]; rw [hod] at ht; omega) [])
    obtain ⟨lE, vE, sE⟩ := ih (2 * e) (evens vs) hev hvE he'
    obtain ⟨lO, vO, sO⟩ := ih (2 * e) (odds vs) hod hvO he'
    set E := fft m (2 * e) (evens vs)
    set O := fft m (2 * e) (odds vs)
    set T := twiddle m e 0 O
    have lT : T.length = 2 ^ l := by rw [length_twiddle, lO]
    have hgE : ∀ i < 2 ^ l, (E.getD i []).length = m := fun i hi ↦
      vE _ (getD_mem' (l := E) (by omega) [])
    have hgO : ∀ i < 2 ^ l, (O.getD i []).length = m := fun i hi ↦
      vO _ (getD_mem' (l := O) (by omega) [])
    have hrot : ∀ i < 2 ^ l, e * i % (2 * m) < 2 * m := fun i _ ↦ Nat.mod_lt _ (by omega)
    have hgT : ∀ i < 2 ^ l, T.getD i [] = rot m (e * i % (2 * m)) (O.getD i []) := by
      intro i hi; rw [getD_twiddle m e 0 O i (by omega), zero_add]
    have hlT : ∀ i < 2 ^ l, (T.getD i []).length = m := fun i hi ↦ by
      rw [hgT i hi]; exact length_rot (hgO i hi) (hrot i hi)
    have hω2 : ω ^ (2 * e) = (ω ^ e) ^ 2 := by rw [← pow_mul, mul_comm]
    -- the butterflies
    have hsplit := fun i ↦ dftAt_split (ω ^ e) (v := vs.map (ev m)) (n := 2 ^ l)
      (by rw [List.length_map, hlen, h2l]) i
    have hper : ((ω ^ e) ^ 2) ^ 2 ^ l = 1 := by rw [← pow_mul, mul_comm, pow_mul, hhalf]; norm_num
    refine ⟨?_, ?_, ?_⟩
    · simp [lE, lT]; omega
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
        simp only [List.length_zipWith, lE, lT, min_self] at hi
        rw [List.getElem_zipWith, ← List.getD_eq_getElem _ [] (by omega),
          ← List.getD_eq_getElem _ [] (by omega)]
        rw [length_vadd (by rw [hgE i hi, hlT i hi])]; exact hgE i hi
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
        simp only [List.length_zipWith, lE, lT, min_self] at hi
        rw [List.getElem_zipWith, ← List.getD_eq_getElem _ [] (by omega),
          ← List.getD_eq_getElem _ [] (by omega)]
        rw [length_vsub (by rw [hgE i hi, hlT i hi])]; exact hgE i hi
    · intro i hi
      have hev' : (evens vs).map (ev m) = evens (vs.map (ev m)) := (evens_map _ _).symm
      have hod' : (odds vs).map (ev m) = odds (vs.map (ev m)) := (odds_map _ _).symm
      rcases Nat.lt_or_ge i (2 ^ l) with hi' | hi'
      · rw [List.getD_append _ _ _ _ (by simp [lE, lT]; omega),
          getD_zipWith _ _ _ [] [] [] (by omega) (by omega),
          ev_vadd (by rw [hgE i hi', hlT i hi']), sE i hi', hgT i hi', ev_rot (hgO i hi')
          (hrot i hi'), root_pow_mod m (e * i), sO i hi', hsplit i, hω2, hev', hod', pow_mul]
      · obtain ⟨i', rfl⟩ : ∃ i', i = 2 ^ l + i' := ⟨i - 2 ^ l, by omega⟩
        have hi'' : i' < 2 ^ l := by omega
        rw [List.getD_append_right _ _ _ _ (by simp [lE, lT]),
          show 2 ^ l + i' - (List.zipWith vadd E T).length = i' by simp [lE, lT],
          getD_zipWith _ _ _ [] [] [] (by omega) (by omega),
          ev_vsub (by rw [hgE i' hi'', hlT i' hi'']), sE i' hi'', hgT i' hi'', ev_rot (hgO i' hi'')
          (hrot i' hi''), root_pow_mod m (e * i'), sO i' hi'', Nat.add_comm (2 ^ l) i', hsplit, hω2, hev', hod',
          dftAt_add_period hper, dftAt_add_period hper, pow_add, hhalf, pow_mul]
        ring

/-! ### Representatives, exact division and blocks -/

theorem ev_cons (m : ℕ) (c : ℤ) (v : List ℤ) :
    ev m (c :: v) = (c : S m) + AdjoinRoot.root _ * ev m v := by
  simp [ev]

theorem ev_eq_sum (m : ℕ) : ∀ v : List ℤ,
    ev m v = ∑ i ∈ Finset.range v.length, (v.getD i 0 : S m) * AdjoinRoot.root _ ^ i
  | [] => by simp
  | c :: v => by
    rw [ev_cons, ev_eq_sum m v, List.length_cons, Finset.sum_range_succ', Finset.mul_sum, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    congr 1; exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem ev_map_mul (m : ℕ) (c : ℤ) (u : List ℤ) : ev m (u.map (c * ·)) = c * ev m u := by
  induction u with
  | nil => simp
  | cons a u ih => simp only [List.map_cons, ev_cons, ih]; push_cast; ring

theorem ev_replicate_zero (m n : ℕ) : ev m (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, ev_cons, ih]; simp

theorem toPolynomial_inj {u v : List ℤ} (h : u.length = v.length)
    (he : toPolynomial u = toPolynomial v) : u = v :=
  List.ext_getElem h fun i h1 h2 ↦ by
    have := congrArg (Polynomial.coeff · i) he
    simp only [coeff_toPolynomial] at this
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem degree_X_pow_add_one {m : ℕ} (hm : 0 < m) : (X ^ m + 1 : ℤ[X]).degree = m := by
  simpa using degree_X_pow_add_C hm (1 : ℤ)

/-- Lists of length `m` represent elements of `S m` uniquely. -/
theorem ev_inj {m : ℕ} (hm : 0 < m) {u v : List ℤ} (hu : u.length = m) (hv : v.length = m)
    (h : ev m u = ev m v) : u = v := by
  refine toPolynomial_inj (hu.trans hv.symm) (sub_eq_zero.1 ?_)
  refine Polynomial.eq_zero_of_dvd_of_degree_lt (AdjoinRoot.mk_eq_mk.1 h) ?_
  rw [degree_X_pow_add_one hm]
  refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
  · simpa [hu] using degree_toPolynomial_lt u
  · simpa [hv] using degree_toPolynomial_lt v

/-- Every element of `S m` is represented by a list of length `m`. -/
theorem ev_surj {m : ℕ} (hm : 0 < m) (z : S m) : ∃ q : List ℤ, q.length = m ∧ ev m q = z := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have hmon : (X ^ m + 1 : ℤ[X]).Monic := by simpa using monic_X_pow_add_C (1 : ℤ) hm.ne'
  refine ⟨(List.range m).map (p %ₘ (X ^ m + 1)).coeff, by simp, ?_⟩
  have hp' : toPolynomial ((List.range m).map (p %ₘ (X ^ m + 1)).coeff) = p %ₘ (X ^ m + 1) := by
    ext i; rw [coeff_toPolynomial]
    by_cases hi : i < m
    · simp [List.getD_eq_getElem?_getD, hi]
    · rw [List.getD_eq_default _ _ (by simpa using hi), Polynomial.coeff_eq_zero_of_degree_lt]
      refine lt_of_lt_of_le (degree_modByMonic_lt _ hmon) ?_
      rw [degree_X_pow_add_one hm]; exact_mod_cast not_lt.1 hi
  rw [ev, hp', AdjoinRoot.mk_eq_mk]
  exact ⟨-(p /ₘ (X ^ m + 1)), by linear_combination modByMonic_add_div p (X ^ m + 1)⟩

/-- **Exact division**: if `w` represents `L z`, dividing its entries by `L` represents `z`. -/
theorem ev_map_ediv {m : ℕ} (hm : 0 < m) {w : List ℤ} (hw : w.length = m) {L : ℤ} (hL : L ≠ 0)
    {z : S m} (h : ev m w = L * z) : (w.map (· / L)).length = m ∧ ev m (w.map (· / L)) = z := by
  obtain ⟨q, hq, rfl⟩ := ev_surj hm z
  obtain rfl : w = q.map (L * ·) := ev_inj hm hw (by simp [hq]) (by rw [h, ev_map_mul])
  refine ⟨by simp [hq], ?_⟩
  rw [List.map_map]; congr 1; conv_rhs => rw [← List.map_id q]
  exact List.map_congr_left fun x _ ↦ by simp [Int.mul_ediv_cancel_left _ hL]

/-- The ring map `S m₁ → S m`, `x ↦ x^r`, for `r m₁ = m`. -/
noncomputable def psi {m₁ r m : ℕ} (h : r * m₁ = m) : S m₁ →+* S m :=
  AdjoinRoot.lift (algebraMap ℤ (S m)) (AdjoinRoot.root _ ^ r) (by
    simp [eval₂_add, eval₂_X_pow, ← pow_mul, h, root_pow_m])

theorem psi_root {m₁ r m : ℕ} (h : r * m₁ = m) :
    psi h (AdjoinRoot.root _) = AdjoinRoot.root _ ^ r := AdjoinRoot.lift_root _

theorem psi_ev {m₁ r m : ℕ} (h : r * m₁ = m) (w : List ℤ) :
    psi h (ev m₁ w) = ∑ l ∈ Finset.range w.length, (w.getD l 0 : S m) * AdjoinRoot.root _ ^ (r * l) := by
  rw [ev_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [map_mul, map_intCast, map_pow, psi_root, ← pow_mul]

theorem sum_range_mul' {M : Type} [AddCommMonoid M] (f : ℕ → M) (r : ℕ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (r * n), f i = ∑ j ∈ Finset.range r, ∑ l ∈ Finset.range n, f (j + r * l)
  | 0 => by simp
  | n + 1 => by
    rw [mul_add_one, Finset.sum_range_add, sum_range_mul' f r n, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.sum_range_succ, add_comm j]

theorem length_block (r m₁ j : ℕ) (a : List ℤ) : (block r m₁ j a).length = m₁ := by simp [block]

theorem getD_block {r m₁ j l : ℕ} (a : List ℤ) (hl : l < m₁) :
    (block r m₁ j a).getD l 0 = a.getD (j + r * l) 0 := by
  simp [block, List.getD_eq_getElem?_getD, hl]

/-- **Blocks**: `a(x) = ∑_{j<r} x^j A_j(x^r)`, with `A_j` the coefficients `a_{j + rl}`. -/
theorem ev_block {m₁ r m : ℕ} (h : r * m₁ = m) {a : List ℤ} (ha : a.length = m) :
    ev m a = ∑ j ∈ Finset.range r, AdjoinRoot.root _ ^ j * psi h (ev m₁ (block r m₁ j a)) := by
  subst h
  rw [ev_eq_sum, ha, sum_range_mul']
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [psi_ev, Finset.mul_sum, length_block]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [getD_block a (Finset.mem_range.1 hl), pow_add]; ring

theorem block_unblock {m₁ r m : ℕ} (h : r * m₁ = m) {D : List (List ℤ)} {j : ℕ} (hj : j < r)
    (hD : (D.getD j []).length = m₁) : block r m₁ j (unblock r m D) = D.getD j [] := by
  rw [unblock_eq]
  refine List.ext_getElem (by rw [length_block, hD]) fun l h1 h2 ↦ ?_
  have hl : l < m₁ := by simpa [block] using h1
  have hlt : j + r * l < m := by subst h; nlinarith
  simp only [block, unblock, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hj, zero_add, List.getD_eq_getElem _ _ (by rw [hD]; exact hl)]

theorem ev_unblock {m₁ r m : ℕ} (h : r * m₁ = m) {D : List (List ℤ)}
    (hD : ∀ j < r, (D.getD j []).length = m₁) :
    ev m (unblock r m D) = ∑ j ∈ Finset.range r, AdjoinRoot.root _ ^ j * psi h (ev m₁ (D.getD j [])) := by
  rw [ev_block h (by simp [unblock_eq])]
  exact Finset.sum_congr rfl fun j hj ↦ by
    rw [block_unblock h (Finset.mem_range.1 hj) (hD j (Finset.mem_range.1 hj))]

/-! ### The schoolbook negacyclic product -/

theorem ncTerm_eq (m s : ℕ) (b : List ℤ) : ∀ (i : ℕ) (as : List ℤ),
    ncTerm m s b i as = ∑ t ∈ Finset.range as.length,
      if i + t ≤ s then as.getD t 0 * b.getD (s - (i + t)) 0
      else -(as.getD t 0 * b.getD (m + s - (i + t)) 0)
  | _, [] => by simp [ncTerm]
  | i, a :: as => by
    rw [ncTerm, ncTerm_eq m s b (i + 1) as, List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun t _ ↦ by rw [show i + 1 + t = i + (t + 1) by ring]

theorem length_ncSchool (m : ℕ) (a b : List ℤ) : (ncSchool m a b).length = m := by
  simp [ncSchool]

theorem sum_range_add_comm' {M : Type} [AddCommMonoid M] (f : ℕ → M) (t n : ℕ) :
    ∑ i ∈ Finset.range (t + n), f i = ∑ i ∈ Finset.range n, f i + ∑ i ∈ Finset.range t, f (n + i) := by
  rw [add_comm t n, Finset.sum_range_add]

/-- Multiplying by `x^t` is a negacyclic shift of the coefficients. -/
theorem root_pow_mul_ev {m t : ℕ} (ht : t < m) {b : List ℤ} (hb : b.length = m) :
    AdjoinRoot.root _ ^ t * ev m b = ∑ s ∈ Finset.range m, AdjoinRoot.root _ ^ s *
      (if t ≤ s then (b.getD (s - t) 0 : S m) else -(b.getD (m + s - t) 0 : S m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = t + n := ⟨m - t, by omega⟩
  rw [ev_eq_sum, hb]
  conv_lhs => rw [sum_range_add_comm', mul_add, Finset.mul_sum, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_range_add]
  refine (add_comm _ _).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Finset.mem_range] at hs
    rw [if_neg (by omega), show t + n + s - t = n + s by omega]
    have : AdjoinRoot.root (X ^ (t + n) + 1 : ℤ[X]) ^ t *
        AdjoinRoot.root (X ^ (t + n) + 1 : ℤ[X]) ^ n = -1 := by rw [← pow_add, root_pow_m]
    linear_combination (↑(b.getD (n + s) 0) * AdjoinRoot.root _ ^ s) * this
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [if_pos (by omega), show t + s - t = s by omega, pow_add (AdjoinRoot.root _) t s]; ring

/-- **The schoolbook negacyclic product** is the product in `S m`. -/
theorem ev_ncSchool {m : ℕ} {a b : List ℤ} (ha : a.length = m) (hb : b.length = m) :
    ev m (ncSchool m a b) = ev m a * ev m b := by
  rw [ev_eq_sum, length_ncSchool, ev_eq_sum m a, ha, Finset.sum_mul]
  have hc : ∀ s ∈ Finset.range m, ((ncSchool m a b).getD s 0 : S m) * AdjoinRoot.root _ ^ s =
      ∑ t ∈ Finset.range m, (a.getD t 0 : S m) * (AdjoinRoot.root _ ^ s *
        (if t ≤ s then (b.getD (s - t) 0 : S m) else -(b.getD (m + s - t) 0 : S m))) := by
    intro s hs
    rw [ncSchool, List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map,
      List.getElem_range, ncTerm_eq, ha, Int.cast_sum, Finset.sum_mul]
    simp only [zero_add]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hc, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [mul_assoc, root_pow_mul_ev (Finset.mem_range.1 ht) hb, Finset.mul_sum]

/-! ### Correctness of Nussbaumer's algorithm -/

theorem getD_map_of_lt {α β : Type} (f : α → β) {l : List α} {i : ℕ} (h : i < l.length) (d : β)
    (d' : α) : (l.map f).getD i d = f (l.getD i d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

/-- The blocks of `a`, padded with `r` zero blocks. -/
theorem padded_spec (r m₁ : ℕ) (a : List ℤ) :
    let A := (List.range r).map (fun j ↦ block r m₁ j a) ++ List.replicate r (List.replicate m₁ 0)
    A.length = 2 * r ∧ (∀ v ∈ A, v.length = m₁) ∧
      ∀ j, (A.map (ev m₁)).getD j 0 = if j < r then ev m₁ (block r m₁ j a) else 0 := by
  intro A
  refine ⟨by simp [A]; ring, fun v hv ↦ ?_, fun j ↦ ?_⟩
  · simp only [A, List.mem_append, List.mem_map, List.mem_replicate] at hv
    rcases hv with ⟨j, _, rfl⟩ | ⟨_, rfl⟩
    · exact length_block _ _ _ _
    · simp
  · rw [getD_map_ev]
    split_ifs with hj
    · rw [List.getD_append _ _ _ _ (by simpa using hj)]
      simp [List.getD_eq_getElem?_getD, hj]
    · by_cases hj2 : j < 2 * r
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate, ev_replicate_zero]
      · rw [List.getD_eq_default _ _ (by simp [A]; omega), ev_nil]

/-- **Nussbaumer's algorithm** computes the product in `S (2^k) = ℤ[x]/(x^{2^k} + 1)`. -/
theorem nussbaumer_spec (k : ℕ) : ∀ a b : List ℤ, a.length = 2 ^ k → b.length = 2 ^ k →
    (nussbaumer k a b).length = 2 ^ k ∧
      ev (2 ^ k) (nussbaumer k a b) = ev (2 ^ k) a * ev (2 ^ k) b := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a b ha hb
  by_cases hk : k ≤ 2
  · rw [nussbaumer, if_pos hk]; exact ⟨length_ncSchool _ _ _, ev_ncSchool ha hb⟩
  rw [nussbaumer, if_neg hk]
  dsimp only
  rw [blocks_eq, blocks_eq]
  generalize hk₁ : (k + 1) / 2 = k₁
  generalize hk₂ : k / 2 = k₂
  have hle : k₂ ≤ k₁ := by omega
  have hk1lt : k₁ < k := by omega
  have hrm : 2 ^ k₂ * 2 ^ k₁ = 2 ^ k := by rw [← pow_add]; congr 1; omega
  generalize he : 2 ^ (k₁ - k₂) = e
  have her : e * 2 ^ k₂ = 2 ^ k₁ := by rw [← he, ← pow_add, Nat.sub_add_cancel hle]
  set m₁ := 2 ^ k₁ with hm₁
  set r := 2 ^ k₂ with hr
  have hm₁pos : 0 < m₁ := by positivity
  have hL : 2 ^ (k₂ + 1) = 2 * r := by rw [pow_succ]; ring
  have heL : e * 2 ^ (k₂ + 1) = 2 * m₁ := by rw [hL, ← her]; ring
  set ω := AdjoinRoot.root (X ^ m₁ + 1 : ℤ[X])
  have hω : (ω ^ e) ^ 2 ^ (k₂ + 1 - 1) = -1 := by
    rw [Nat.add_sub_cancel, ← pow_mul, her, root_pow_m]
  have hω' : ω ^ (2 * m₁ - e) = (ω ^ e) ^ (2 ^ (k₂ + 1) - 1) := by
    rw [← pow_mul, Nat.mul_sub_one, heL]
  have hodd : Odd (2 ^ (k₂ + 1) - 1) :=
    ⟨2 ^ k₂ - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := k₂); omega⟩
  have hω'2 : (ω ^ (2 * m₁ - e)) ^ 2 ^ (k₂ + 1 - 1) = -1 := by
    rw [hω', ← pow_mul, mul_comm, pow_mul, hω, hodd.neg_one_pow]
  obtain ⟨hAl, hAv, hAg⟩ := padded_spec r m₁ a
  obtain ⟨hBl, hBv, hBg⟩ := padded_spec r m₁ b
  generalize (List.range r).map (fun j ↦ block r m₁ j a) ++
    List.replicate r (List.replicate m₁ 0) = A at hAl hAv hAg ⊢
  generalize (List.range r).map (fun j ↦ block r m₁ j b) ++
    List.replicate r (List.replicate m₁ 0) = B at hBl hBv hBg ⊢
  rw [← hL] at hAl hBl
  obtain ⟨hFAl, hFAv, hFAg⟩ := fft_spec hm₁pos (k₂ + 1) e A hAl hAv fun _ ↦ hω
  obtain ⟨hFBl, hFBv, hFBg⟩ := fft_spec hm₁pos (k₂ + 1) e B hBl hBv fun _ ↦ hω
  generalize fft m₁ e A = FA at hFAl hFAv hFAg ⊢
  generalize fft m₁ e B = FB at hFBl hFBv hFBg ⊢
  -- the pointwise products, by recursion
  have hPl : (List.zipWith (nussbaumer k₁) FA FB).length = 2 ^ (k₂ + 1) := by simp [hFAl, hFBl]
  have hPg : ∀ i < 2 ^ (k₂ + 1), ((List.zipWith (nussbaumer k₁) FA FB).getD i []).length = m₁ ∧
      ev m₁ ((List.zipWith (nussbaumer k₁) FA FB).getD i []) =
        dftAt (ω ^ e) (A.map (ev m₁)) i * dftAt (ω ^ e) (B.map (ev m₁)) i := by
    intro i hi
    rw [getD_zipWith _ _ _ [] [] [] (by omega) (by omega), ← hFAg i hi, ← hFBg i hi]
    exact ih k₁ hk1lt _ _ (hFAv _ (getD_mem' (by omega) _)) (hFBv _ (getD_mem' (by omega) _))
  have hPv : ∀ v ∈ List.zipWith (nussbaumer k₁) FA FB, v.length = m₁ := fun v hv ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rw [← List.getD_eq_getElem _ [] hi]; exact (hPg i (by omega)).1
  generalize List.zipWith (nussbaumer k₁) FA FB = P at hPl hPg hPv ⊢
  -- the inverse transform: `2r` times the acyclic convolution
  obtain ⟨hCl, hCv, hCg⟩ := fft_spec hm₁pos (k₂ + 1) (2 * m₁ - e) P hPl hPv fun _ ↦ hω'2
  generalize fft m₁ (2 * m₁ - e) P = Cf at hCl hCv hCg ⊢
  set a' := fun j ↦ (A.map (ev m₁)).getD j 0
  set b' := fun j ↦ (B.map (ev m₁)).getD j 0
  have ha' : ∀ j, r ≤ j → a' j = 0 := fun j hj ↦ by simp only [a', hAg, if_neg (by omega : ¬j < r)]
  have hb' : ∀ j, r ≤ j → b' j = 0 := fun j hj ↦ by simp only [b', hBg, if_neg (by omega : ¬j < r)]
  set c := fun t ↦ ∑ j ∈ Finset.range (2 * r), ∑ k ∈ Finset.range (2 * r),
    if j + k = t then a' j * b' k else 0
  have hC : ∀ t < 2 * r, ev m₁ (Cf.getD t []) = ((2 ^ (k₂ + 1) : ℤ) : S m₁) * c t := by
    intro t ht
    rw [hCg t (by omega), dftAt, List.length_map, hPl]
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [getD_map_ev, (hPg i (Finset.mem_range.1 hi)).2, dftAt, dftAt, List.length_map,
        List.length_map, hAl, hBl]]
    rw [hω']
    have := conv_spec (by omega) hω (by omega) a' b' ha' hb' (t := t) (by omega)
    rw [hL] at this ⊢
    push_cast
    exact this
  -- exact division by `2r`
  have hCd : ∀ t < 2 * r,
      ((Cf.map fun v ↦ v.map (· / 2 ^ (k₂ + 1))).getD t (List.replicate m₁ 0)).length = m₁ ∧
      ev m₁ ((Cf.map fun v ↦ v.map (· / 2 ^ (k₂ + 1))).getD t (List.replicate m₁ 0)) = c t := by
    intro t ht
    rw [getD_map_of_lt _ (by omega) _ []]
    exact ev_map_ediv hm₁pos (hCv _ (getD_mem' (by omega) _)) (by positivity) (hC t ht)
  generalize Cf.map (fun v ↦ v.map (· / 2 ^ (k₂ + 1))) = C at hCd ⊢
  -- folding and unblocking
  have hD : ∀ j < r, ((List.range r).map fun j ↦
        vadd (C.getD j (List.replicate m₁ 0)) (rot m₁ 1 (C.getD (j + r) (List.replicate m₁ 0)))).getD j [] =
      vadd (C.getD j (List.replicate m₁ 0)) (rot m₁ 1 (C.getD (j + r) (List.replicate m₁ 0))) := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, hj]
  have hlen1 : 1 < 2 * m₁ := by omega
  refine ⟨by simp [unblock_eq], ?_⟩
  rw [ev_unblock hrm fun j hj ↦ by
    rw [hD j hj, length_vadd (by rw [(hCd j (by omega)).1, length_rot (hCd _ (by omega)).1 hlen1])]
    exact (hCd j (by omega)).1]
  rw [ev_block hrm ha, ev_block hrm hb]
  have hblk : ∀ (a' : ℕ → S m₁) (a : List ℤ),
      (∀ j, a' j = if j < r then ev m₁ (block r m₁ j a) else 0) →
      ∑ j ∈ Finset.range r, AdjoinRoot.root _ ^ j * psi hrm (ev m₁ (block r m₁ j a)) =
        ∑ j ∈ Finset.range r, AdjoinRoot.root _ ^ j * psi hrm (a' j) := fun a' a h ↦
    Finset.sum_congr rfl fun j hj ↦ by rw [h j, if_pos (Finset.mem_range.1 hj)]
  rw [hblk a' a hAg, hblk b' b hBg, fold_conv (psi hrm) _ ω r (psi_root hrm) a' b' ha' hb']
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [hD j hj, ev_vadd (by rw [(hCd j (by omega)).1, length_rot (hCd _ (by omega)).1 hlen1]),
    ev_rot (hCd _ (by omega)).1 hlen1, (hCd j (by omega)).2, (hCd _ (by omega)).2, pow_one]

/-! ## Integer multiplication -/

/-- The low `m` binary digits of `x`, least significant first. -/
counted_def bitsOf : ℕ → ℕ → List ℤ
  | 0, _ => []
  | m + 1, x => ((x % 2 : ℕ) : ℤ) :: bitsOf m (x / 2)

/-- The number with the given binary digits (each `0` or `1`), least significant first:
writing them down is not arithmetic. -/
counted_def ofBits (l : List ℤ) : ℤ := l.foldr (fun d acc ↦ d + 2 * acc) 0

/-- The low `2^k` binary digits of `x`, by halving: `O(N log N)` word operations, against
`O(N²)` for `bitsOf`, which halves the whole number `2^k` times (`bitsOfPow2_eq`). -/
counted_def bitsOfPow2 : ℕ → ℕ → List ℤ
  | 0, x => [((x % 2 : ℕ) : ℤ)]
  | k + 1, x => bitsOfPow2 k (x % 2 ^ 2 ^ k) ++ bitsOfPow2 k (x >>> 2 ^ k)

/-- The number with the given binary digits, by halving and shifts (`ofBitsNat_eq`). -/
counted_def ofBitsNat (l : List ℤ) : ℕ :=
  if l.length ≤ 1 then (l.headD 0).toNat
  else (ofBitsNat (l.drop (l.length / 2)) <<< (l.length / 2)) + ofBitsNat (l.take (l.length / 2))
termination_by l.length
decreasing_by all_goals simp only [List.length_drop, List.length_take]; omega

/-- **Carry propagation**: the binary digits of `c + ∑ dᵢ 2^i`, and the final carry. -/
counted_def carry (c : ℤ) : List ℤ → List ℤ × ℤ
  | [] => ([], c)
  | d :: ds =>
    let s := c + d
    let r := carry (s / 2) ds
    (s % 2 :: r.1, r.2)

/-- The transform length `2^k` for multiplying `x` by `y`: at least twice their bit length,
so that the negacyclic product does not wrap around. -/
counted_def mulLog (x y : ℕ) : ℕ := (2 * max x.size y.size).size

/-- **Multiplication by Nussbaumer's convolution**: the binary digits of `x` and `y` as
coefficients, their product in `ℤ[x]/(x^{2^k} + 1)`, and carry propagation. -/
counted_def nussMul (x y : ℕ) : ℕ :=
  if x = 0 ∨ y = 0 then 0
  else
    let k := mulLog x y
    let r := carry 0 (nussbaumer k (bitsOfPow2 k x) (bitsOfPow2 k y))
    ((ofBitsNat r.1 : ℤ) + r.2 * 2 ^ (2 ^ k)).toNat

theorem length_bitsOf : ∀ m x, (bitsOf m x).length = m
  | 0, _ => rfl
  | m + 1, x => by simp [bitsOf, length_bitsOf m]

theorem eval_bitsOf : ∀ m x, (toPolynomial (bitsOf m x)).eval 2 = ((x % 2 ^ m : ℕ) : ℤ)
  | 0, x => by simp [bitsOf]
  | m + 1, x => by
    simp only [bitsOf, toPolynomial_cons, eval_add, eval_C, eval_mul, eval_X, eval_bitsOf m]
    rw [pow_succ', Nat.mod_mul]; push_cast; ring

theorem bitsOf_add : ∀ N j x, bitsOf (N + j) x = bitsOf N x ++ bitsOf j (x / 2 ^ N)
  | 0, j, x => by simp [bitsOf]
  | N + 1, j, x => by
    rw [show N + 1 + j = N + j + 1 by ring, bitsOf, bitsOf, bitsOf_add N j (x / 2),
      Nat.div_div_eq_div_mul, ← pow_succ']; rfl

theorem bitsOf_zero : ∀ j, bitsOf j 0 = List.replicate j 0
  | 0 => rfl
  | j + 1 => by simp [bitsOf, bitsOf_zero j, List.replicate_succ]

theorem bitsOf_mod : ∀ m x, bitsOf m (x % 2 ^ m) = bitsOf m x
  | 0, _ => rfl
  | m + 1, x => by
    rw [bitsOf, bitsOf, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), pow_succ',
      Nat.mod_mul_right_div_self, bitsOf_mod m (x / 2)]

theorem bitsOfPow2_eq : ∀ k x, bitsOfPow2 k x = bitsOf (2 ^ k) x
  | 0, x => rfl
  | k + 1, x => by
    rw [bitsOfPow2, bitsOfPow2_eq k, bitsOfPow2_eq k, bitsOf_mod, pow_succ, mul_two, bitsOf_add,
      Nat.shiftRight_eq_div_pow]

theorem degree_bitsOf_lt {m x N : ℕ} (hN : N ≤ m) (hx : x < 2 ^ N) :
    (toPolynomial (bitsOf m x)).degree < N := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [bitsOf_add, Nat.div_eq_of_lt hx, bitsOf_zero, toPolynomial_append,
    toPolynomial_replicate_zero, mul_zero, add_zero]
  simpa [length_bitsOf] using degree_toPolynomial_lt (bitsOf N x)

theorem degree_mul_lt_of {p q : ℤ[X]} {N m : ℕ} (hp : p.degree < N) (hq : q.degree < N)
    (h : 2 * N ≤ m) : (p * q).degree < m := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  have h₁ := (natDegree_lt_iff_degree_lt hp0).2 hp
  have h₂ := (natDegree_lt_iff_degree_lt hq0).2 hq
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast natDegree_mul_le.trans_lt (by omega))

/-- Polynomials of degree below `m` that agree in `S m` are equal. -/
theorem eq_of_mk_eq {m : ℕ} (hm : 0 < m) {p q : ℤ[X]} (hp : p.degree < m) (hq : q.degree < m)
    (h : AdjoinRoot.mk (X ^ m + 1 : ℤ[X]) p = AdjoinRoot.mk _ q) : p = q := by
  refine sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_degree_lt (AdjoinRoot.mk_eq_mk.1 h) ?_)
  rw [degree_X_pow_add_one hm]
  exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hp hq)

theorem ofBits_eq : ∀ l : List ℤ, ofBits l = (toPolynomial l).eval 2
  | [] => by simp [ofBits]
  | d :: l => by simp [ofBits, ← ofBits_eq l]

theorem ofBits_append (l l' : List ℤ) : ofBits (l ++ l') = ofBits l + 2 ^ l.length * ofBits l' := by
  rw [ofBits_eq, ofBits_eq, ofBits_eq, toPolynomial_append]; simp

theorem ofBitsNat_eq (l : List ℤ) (h : ∀ d ∈ l, 0 ≤ d ∧ d ≤ 1) : (ofBitsNat l : ℤ) = ofBits l := by
  induction l using WellFounded.induction (r := InvImage (· < ·) List.length)
    (InvImage.wf _ Nat.lt_wfRel.wf) with
  | h l ih =>
    rw [ofBitsNat]
    split_ifs with hl
    · match l, hl with
      | [], _ => rfl
      | [d], _ =>
        have := h d (by simp)
        simp only [List.headD_cons, ofBits, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
        omega
    · have h₁ := ih (l.drop (l.length / 2)) (by simp only [InvImage, List.length_drop]; omega)
        fun d hd ↦ h d (List.mem_of_mem_drop hd)
      have h₂ := ih (l.take (l.length / 2)) (by simp only [InvImage, List.length_take]; omega)
        fun d hd ↦ h d (List.mem_of_mem_take hd)
      conv_rhs => rw [← List.take_append_drop (l.length / 2) l]
      rw [ofBits_append, List.length_take, min_eq_left (by omega), Nat.shiftLeft_eq]
      push_cast; rw [h₁, h₂]; ring

theorem carry_digits : ∀ (c : ℤ) (ds : List ℤ), ∀ d ∈ (carry c ds).1, 0 ≤ d ∧ d ≤ 1
  | _, [] => by simp [carry]
  | c, d :: ds => fun x hx ↦ by
    simp only [carry, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact carry_digits _ ds x hx

theorem carry_spec : ∀ (c : ℤ) (ds : List ℤ),
    ofBits (carry c ds).1 + (carry c ds).2 * 2 ^ ds.length = c + (toPolynomial ds).eval 2
  | c, [] => by simp [carry, ofBits]
  | c, d :: ds => by
    have := carry_spec ((c + d) / 2) ds
    rw [ofBits_eq] at this ⊢
    simp only [carry, toPolynomial_cons, eval_add, eval_C, eval_mul, eval_X, List.length_cons]
    linear_combination 2 * this + Int.emod_add_mul_ediv (c + d) 2

/-- **Nussbaumer multiplication is multiplication.** -/
theorem nussMul_eq (x y : ℕ) : nussMul x y = x * y := by
  by_cases h0 : x = 0 ∨ y = 0
  · rw [nussMul, if_pos h0]; rcases h0 with rfl | rfl <;> simp
  have hm : 2 * max x.size y.size < 2 ^ mulLog x y := Nat.lt_size_self _
  have hx : x < 2 ^ max x.size y.size :=
    (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right two_pos (le_max_left _ _))
  have hy : y < 2 ^ max x.size y.size :=
    (Nat.lt_size_self y).trans_le (Nat.pow_le_pow_right two_pos (le_max_right _ _))
  have hN : max x.size y.size ≤ 2 ^ mulLog x y := by omega
  obtain ⟨hlen, hev⟩ := nussbaumer_spec (mulLog x y) (bitsOf (2 ^ mulLog x y) x)
    (bitsOf (2 ^ mulLog x y) y) (length_bitsOf _ _) (length_bitsOf _ _)
  have hc : toPolynomial (nussbaumer (mulLog x y) (bitsOf (2 ^ mulLog x y) x)
      (bitsOf (2 ^ mulLog x y) y)) =
      toPolynomial (bitsOf (2 ^ mulLog x y) x) * toPolynomial (bitsOf (2 ^ mulLog x y) y) := by
    refine eq_of_mk_eq (Nat.two_pow_pos _) ?_ ?_ (by rw [map_mul]; exact hev)
    · have := degree_toPolynomial_lt (nussbaumer (mulLog x y) (bitsOf (2 ^ mulLog x y) x)
        (bitsOf (2 ^ mulLog x y) y))
      rw [hlen] at this; exact_mod_cast this
    · exact degree_mul_lt_of (degree_bitsOf_lt hN hx) (degree_bitsOf_lt hN hy) hm.le
  have hxm : x < 2 ^ 2 ^ mulLog x y := hx.trans_le (Nat.pow_le_pow_right two_pos hN)
  have hym : y < 2 ^ 2 ^ mulLog x y := hy.trans_le (Nat.pow_le_pow_right two_pos hN)
  have := carry_spec 0 (nussbaumer (mulLog x y) (bitsOf (2 ^ mulLog x y) x)
    (bitsOf (2 ^ mulLog x y) y))
  rw [hc, eval_mul, eval_bitsOf, eval_bitsOf, Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hym,
    hlen, zero_add] at this
  simp only [nussMul, if_neg h0, bitsOfPow2_eq, ofBitsNat_eq _ (carry_digits _ _), this]
  exact Int.toNat_natCast _

end PrimeNumbers.Chapter9
