import PrimeNumbers.Chapter9.CountedDef
import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter2.Euclid

/-!
# §5.2.1 Pollard rho method for factoring

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.2.1.

* `pollardRho` — Algorithm 5.2.1, with the "random" seeds `a`, `s` supplied by the caller
  and a bound `fuel` on the number of passes of [Factor search].
* `pollardRho_sound` — whatever it returns is a nontrivial factor of `n`.
* `pollardRhoLoop_isSome` — the rigorous half of the analysis: if `p > 1` divides `n`,
  then within `p` passes the search stops with a gcd `g ≠ 1` (Floyd cycle-finding,
  `exists_iterate_eq_iterate_two_mul`).

**Not proved, because it is not a theorem:** that the search stops after `O(√p)` passes.
This is the heuristic assumption that `x ↦ x² + a mod p` behaves like a random function;
the book is explicit that the method "is heuristic".  Likewise nothing excludes the
[Bad seed] outcome `g = n`, in which case `pollardRho` returns `none` and one retries
with other seeds.
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2

/-- The iteration function of Algorithm 5.2.1: `F(x) = (x² + a) mod n`. -/
counted_def rhoF (n a x : ℕ) : ℕ := (x * x + a) % n

/-- `|u - v|` on naturals. -/
@[cost_free] def absDiff (u v : ℕ) : ℕ := if v ≤ u then u - v else v - u

/-- **Algorithm 5.2.1, step 2 [Factor search]**, at most `fuel` passes:
```
U = F(U);
V = F(V);
V = F(V);                            // F(V) intentionally invoked twice.
g = gcd(U - V, n);
if (g == 1) goto [Factor search];
```
Returns the first `g ≠ 1`, or `none` if the fuel runs out. -/
counted_def pollardRhoLoop (n a : ℕ) (U V : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    let U' := rhoF n a U
    let V' := rhoF n a (rhoF n a V)
    let g := euclid n (absDiff U' V')
    if g = 1 then pollardRhoLoop n a U' V' fuel else some g

/-- **Algorithm 5.2.1 (Pollard rho factorization method).**  Given a composite `n`,
attempts to find a nontrivial factor of `n`, from seeds `a ∈ [1, n - 3]` and
`s ∈ [0, n - 1]`.  Returns `none` on a [Bad seed] (`g = n`) or if `fuel` passes of
[Factor search] were not enough. -/
counted_def pollardRho (n a s fuel : ℕ) : Option ℕ :=
  match pollardRhoLoop n a s s fuel with
  | some g => if g = n then none else some g     -- 3. [Bad seed] / 4. [Success]
  | none => none

/-! ## Soundness -/

theorem pollardRhoLoop_spec {n a U V fuel g : ℕ} (h : pollardRhoLoop n a U V fuel = some g) :
    g ∣ n ∧ g ≠ 1 := by
  induction fuel generalizing U V with
  | zero => simp [pollardRhoLoop] at h
  | succ fuel ih =>
    simp only [pollardRhoLoop] at h
    split_ifs at h with h1
    · exact ih h
    · obtain rfl := Option.some.inj h
      exact ⟨by rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left _ _, h1⟩

/-- **Soundness of Algorithm 5.2.1**: any `g` returned is a nontrivial factor of `n`. -/
theorem pollardRho_sound {n a s fuel g : ℕ} (hn : 0 < n) (h : pollardRho n a s fuel = some g) :
    g ∣ n ∧ 1 < g ∧ g < n := by
  unfold pollardRho at h
  split at h
  · rename_i g' hloop
    split_ifs at h with hgn
    obtain rfl := Option.some.inj h
    obtain ⟨hdvd, h1⟩ := pollardRhoLoop_spec hloop
    have hpos : 0 < g' := Nat.pos_of_dvd_of_pos hdvd hn
    have hle : g' ≤ n := Nat.le_of_dvd hn hdvd
    exact ⟨hdvd, by omega, by omega⟩
  · simp at h

/-! ## Why the search stops: Floyd cycle-finding -/

/-- **Floyd cycle-finding.**  If the sequence `x, f(x), f(f(x)), …` repeats, say
`f⁽ʲ⁾(x) = f⁽ᵏ⁾(x)` with `j < k`, then `f⁽ⁱ⁾(x) = f⁽²ⁱ⁾(x)` for some `1 ≤ i ≤ k`.

Proof as in the book: with `l = k - j` the sequence has period `l` from index `j` on, and
one takes for `i` the first multiple of `l` exceeding `j`. -/
theorem floyd {α : Type*} (f : α → α) {x : α} {j k : ℕ} (hjk : j < k)
    (heq : f^[j] x = f^[k] x) : ∃ i, 1 ≤ i ∧ i ≤ k ∧ f^[i] x = f^[2 * i] x := by
  obtain ⟨l, rfl⟩ : ∃ l, k = j + l := ⟨k - j, by omega⟩
  have hl : 0 < l := by omega
  have hper : ∀ c m, j ≤ m → f^[m + c * l] x = f^[m] x := by
    intro c
    induction c with
    | zero => simp
    | succ c ih =>
      intro m hm
      obtain ⟨d, rfl⟩ : ∃ d, m = d + j := ⟨m - j, by omega⟩
      rw [show d + j + (c + 1) * l = d + c * l + (j + l) by ring, Function.iterate_add_apply,
        ← heq, ← Function.iterate_add_apply, ← ih (d + j) (by omega)]
      congr 1
      ring
  refine ⟨l * (j / l + 1), Nat.mul_pos hl (Nat.succ_pos _), ?_, ?_⟩
  · have : l * (j / l) ≤ j := Nat.mul_div_le j l
    rw [mul_add, mul_one]
    omega
  · have hji : j ≤ l * (j / l + 1) := (Nat.lt_mul_div_succ j hl).le
    rw [show 2 * (l * (j / l + 1)) = l * (j / l + 1) + (j / l + 1) * l by ring]
    exact (hper _ _ hji).symm

/-- By the pigeonhole principle a map into `{0, …, p - 1}` repeats within `p` steps, so
Floyd's method finds `1 ≤ i ≤ p` with `f⁽ⁱ⁾(x) = f⁽²ⁱ⁾(x)`. -/
theorem exists_iterate_eq_iterate_two_mul {p : ℕ} (f : ℕ → ℕ) (hf : ∀ x, f x < p) {x : ℕ}
    (hx : x < p) : ∃ i, 1 ≤ i ∧ i ≤ p ∧ f^[i] x = f^[2 * i] x := by
  have hlt : ∀ i, f^[i] x < p := fun i ↦ by
    cases i with
    | zero => simpa using hx
    | succ i => rw [Function.iterate_succ_apply']; exact hf _
  obtain ⟨j, k, hjk, heq⟩ : ∃ j k : Fin (p + 1), j ≠ k ∧ f^[j] x = f^[k] x := by
    obtain ⟨j, k, hjk, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (p + 1) ↦ (⟨f^[i] x, hlt i⟩ : Fin p)) (by simp)
    exact ⟨j, k, hjk, congrArg Fin.val h⟩
  wlog hlt' : (j : ℕ) < k generalizing j k
  · exact this k j hjk.symm heq.symm (by
      have : (j : ℕ) ≠ k := fun h ↦ hjk (Fin.ext h)
      omega)
  obtain ⟨i, h₁, h₂, h₃⟩ := floyd f hlt' heq
  exact ⟨i, h₁, by omega, h₃⟩

/-- Modulo a divisor `p` of `n`, the iteration `F` is the iteration `f(x) = x² + a mod p`
("Clearly, `f(x) = F(x) mod p`"). -/
theorem iterate_rhoF_mod {n p : ℕ} (hpn : p ∣ n) (a s i : ℕ) :
    (rhoF n a)^[i] s % p = (rhoF p a)^[i] (s % p) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    congr 1
    simp only [rhoF, Nat.mod_mod_of_dvd _ hpn]
    rw [Nat.add_mod, Nat.mul_mod]
    exact (Nat.add_mod _ _ _).symm

/-- If two numbers agree modulo `p > 1` and `p ∣ n`, then `gcd(n, |u - v|) ≠ 1`. -/
theorem euclid_absDiff_ne_one {n p u v : ℕ} (hp : 1 < p) (hpn : p ∣ n) (h : u % p = v % p) :
    euclid n (absDiff u v) ≠ 1 := by
  have hdvd : p ∣ absDiff u v := by
    unfold absDiff
    split_ifs with hle
    · exact (Nat.modEq_iff_dvd' hle).mp h.symm
    · exact (Nat.modEq_iff_dvd' (by omega)).mp h
  intro h1
  have := Nat.dvd_gcd hpn hdvd
  rw [← euclid_eq_gcd, h1] at this
  exact absurd (Nat.dvd_one.mp this) (by omega)

/-- The loop tracks `U = F⁽ⁱ⁾(s)` and `V = F⁽²ⁱ⁾(s)`; if some pass `i ≤ fuel` has
`gcd(n, |F⁽ⁱ⁾(U) - F⁽²ⁱ⁾(V)|) ≠ 1` the loop returns. -/
theorem pollardRhoLoop_isSome_of {n a : ℕ} (U V fuel : ℕ)
    (h : ∃ i, 1 ≤ i ∧ i ≤ fuel ∧
      euclid n (absDiff ((rhoF n a)^[i] U) ((rhoF n a)^[2 * i] V)) ≠ 1) :
    (pollardRhoLoop n a U V fuel).isSome := by
  induction fuel generalizing U V with
  | zero => obtain ⟨i, h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    simp only [pollardRhoLoop]
    split_ifs with hg
    · obtain ⟨i, h₁, h₂, h₃⟩ := h
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact absurd hg h₃
      · refine ih _ _ ⟨i, hi, by omega, ?_⟩
        rwa [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, Function.iterate_succ_apply,
          Function.iterate_succ_apply, Function.iterate_succ_apply] at h₃
    · rfl

/-- **The factor search of Algorithm 5.2.1 succeeds within `p` passes**, for any divisor
`p > 1` of `n` (in particular the least prime factor): the loop then returns some
`g ≠ 1` dividing `n`.  The heuristic claim, not proved, is that `O(√p)` passes suffice. -/
theorem pollardRhoLoop_isSome {n p : ℕ} (hp : 1 < p) (hpn : p ∣ n) (a s : ℕ) {fuel : ℕ}
    (hfuel : p ≤ fuel) : (pollardRhoLoop n a s s fuel).isSome := by
  obtain ⟨i, h₁, h₂, h₃⟩ := exists_iterate_eq_iterate_two_mul (rhoF p a)
    (fun x ↦ Nat.mod_lt _ (by omega)) (Nat.mod_lt s (by omega : 0 < p))
  refine pollardRhoLoop_isSome_of s s fuel ⟨i, h₁, by omega, ?_⟩
  exact euclid_absDiff_ne_one hp hpn (by rw [iterate_rhoF_mod hpn, iterate_rhoF_mod hpn, h₃])

/-! ## The heuristic, as an explicit hypothesis -/

/-- **The hypothesis behind the `O(√p)` running time.**  `RhoCollision p a s T` says that
the sequence `s, f(s), f(f(s)), …` for `f(x) = x² + a mod p` repeats within `T` steps
(its "tail plus cycle" has length at most `T`).

For a *random* map on `p` points the expected length is `√(πp/2)`; the heuristic
assumption of the Pollard rho method is that `f` behaves this way, i.e. that
`RhoCollision p a s T` holds with `T` of order `√p` for most seeds.  This is not known to
be true, and is not proved here: it is the hypothesis of the next theorem. -/
def RhoCollision (p a s T : ℕ) : Prop :=
  ∃ j k, j < k ∧ k ≤ T ∧ (rhoF p a)^[j] (s % p) = (rhoF p a)^[k] (s % p)

/-- Unconditionally, the sequence repeats within `p` steps. -/
theorem rhoCollision_self {p : ℕ} (hp : 0 < p) (a s : ℕ) : RhoCollision p a s p := by
  have hlt : ∀ i, (rhoF p a)^[i] (s % p) < p := fun i ↦ by
    cases i with
    | zero => exact Nat.mod_lt _ hp
    | succ i => rw [Function.iterate_succ_apply']; exact Nat.mod_lt _ hp
  obtain ⟨j, k, hjk, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (p + 1) ↦ (⟨(rhoF p a)^[i] (s % p), hlt i⟩ : Fin p)) (by simp)
  have h' := congrArg Fin.val h
  have hne : (j : ℕ) ≠ k := fun h ↦ hjk (Fin.ext h)
  rcases Nat.lt_or_ge j k with hlt' | hge
  · exact ⟨j, k, hlt', by omega, h'⟩
  · exact ⟨k, j, by omega, by omega, h'.symm⟩

/-- **Pollard rho, conditionally on the heuristic.**  If `p > 1` divides `n` and the
sequence modulo `p` repeats within `T` steps, then [Factor search] stops within `T`
passes with a gcd `g ≠ 1`.  Under the random-map heuristic `T = O(√p)`. -/
theorem pollardRhoLoop_isSome_of_collision {n p a s T : ℕ} (hp : 1 < p) (hpn : p ∣ n)
    (hcol : RhoCollision p a s T) {fuel : ℕ} (hfuel : T ≤ fuel) :
    (pollardRhoLoop n a s s fuel).isSome := by
  obtain ⟨j, k, hjk, hkT, heq⟩ := hcol
  obtain ⟨i, h₁, h₂, h₃⟩ := floyd (rhoF p a) hjk heq
  refine pollardRhoLoop_isSome_of s s fuel ⟨i, h₁, by omega, ?_⟩
  exact euclid_absDiff_ne_one hp hpn (by rw [iterate_rhoF_mod hpn, iterate_rhoF_mod hpn, h₃])

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Bit operations -/

/-- One evaluation of `F` on a residue costs at most one modular multiplication. -/
theorem rhoFCost_le (C : CostModel) {n a x : ℕ} (ha : a < n) (hx : x < n) :
    costOf C (rhoF n a x) ≤ C.mulMod n.size := by
  have hlt : x * x + a < n * n := by
    obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
    have h₁ : x * x ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
    have h₂ : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
    omega
  have hsize : (x * x + a).size ≤ 2 * n.size := by
    have := size_le_of_lt hlt
    have := size_mul_le n n
    omega
  cost_unfold rhoF.counted
  exact Nat.add_le_add (C.mul_mono (size_le_of_lt hx) (size_le_of_lt hx))
    (C.divMod_mono _ hsize)

theorem absDiff_lt {n u v : ℕ} (hu : u < n) (hv : v < n) : absDiff u v < n := by
  unfold absDiff ; split_ifs <;> omega

/-- **Bit complexity of Pollard rho**, for any cost model: each pass costs at most three
modular multiplications and one gcd with `n` (bounded by `G`). -/
theorem pollardRhoCost_le (C : CostModel) {n a G : ℕ} (ha : a < n)
    (hG : ∀ d < n, costOf C (euclid n d) ≤ G) {U V : ℕ} (hU : U < n) (hV : V < n) (fuel : ℕ) :
    costOf C (pollardRhoLoop n a U V fuel) ≤ fuel * (3 * C.mulMod n.size + G) := by
  have hn : 0 < n := by omega
  induction fuel generalizing U V with
  | zero => cost_unfold pollardRhoLoop.counted
  | succ fuel ih =>
    have hF : ∀ x, rhoF n a x < n := fun x ↦ Nat.mod_lt _ hn
    have h₁ := rhoFCost_le C ha hU
    have h₂ := rhoFCost_le C ha hV
    have h₃ := rhoFCost_le C ha (hF V)
    have h₄ := hG _ (absDiff_lt (hF U) (hF (rhoF n a V)))
    have ih := ih (hF U) (hF (rhoF n a V))
    cost_unfold pollardRhoLoop.counted
    simp only [add_mul, one_mul]
    split_ifs <;> omega

/-- **Bit complexity of Pollard rho, grammar-school arithmetic**: at most `9k² + 4k` bit
operations per pass of [Factor search]. -/
theorem pollardRhoCost_school_le {n a U V : ℕ} (ha : a < n) (hU : U < n) (hV : V < n)
    (fuel : ℕ) :
    costOf school (pollardRhoLoop n a U V fuel) ≤ fuel * (9 * n.size ^ 2 + 4 * n.size) := by
  refine (pollardRhoCost_le school ha
    (fun d hd ↦ euclidBitCost_school_le' hd le_rfl) hU hV fuel).trans (le_of_eq ?_)
  rw [school_mulMod]
  ring

end RunningTime

/-! ## The variant with accumulated gcd's

"With the cost of one extra modular multiplication, one may put off the gcd calculation so
that it is performed only rarely.  Namely, the numbers `U - V` may be accumulated
(multiplied all together) modulo `n` for `k` iterations, and then the gcd of this modular
product is taken with `n`." -/

/-- `count` passes of [Factor search] without the gcd, accumulating
`Q = Q · |U - V| mod n`.  Returns `(U, V, Q)`. -/
counted_def rhoBatch (n a : ℕ) : (U V Q count : ℕ) → ℕ × ℕ × ℕ
  | U, V, Q, 0 => (U, V, Q)
  | U, V, Q, count + 1 =>
    let U' := rhoF n a U
    let V' := rhoF n a (rhoF n a V)
    rhoBatch n a U' V' (Q * absDiff U' V' % n) count

/-- [Factor search] with one gcd per batch of `k` passes; at most `fuel` batches. -/
counted_def pollardRhoAccLoop (n a k : ℕ) (U V : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    let r := rhoBatch n a U V 1 k
    let g := euclid n r.2.2
    if g = 1 then pollardRhoAccLoop n a k r.1 r.2.1 fuel else some g

/-- **Pollard rho with accumulated gcd's.**  Returns `none` if a batch ends with `g = n`
(then one should redo that batch with a gcd at every pass, i.e. call `pollardRho`). -/
counted_def pollardRhoAcc (n a s k fuel : ℕ) : Option ℕ :=
  match pollardRhoAccLoop n a k s s fuel with
  | some g => if g = n then none else some g
  | none => none

theorem pollardRhoAccLoop_spec {n a k U V fuel g : ℕ}
    (h : pollardRhoAccLoop n a k U V fuel = some g) : g ∣ n ∧ g ≠ 1 := by
  induction fuel generalizing U V with
  | zero => simp [pollardRhoAccLoop] at h
  | succ fuel ih =>
    simp only [pollardRhoAccLoop] at h
    split_ifs at h with h1
    · exact ih h
    · obtain rfl := Option.some.inj h
      exact ⟨by rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left _ _, h1⟩

/-- **Soundness of the accumulated variant**: any `g` returned is a nontrivial factor. -/
theorem pollardRhoAcc_sound {n a s k fuel g : ℕ} (hn : 0 < n)
    (h : pollardRhoAcc n a s k fuel = some g) : g ∣ n ∧ 1 < g ∧ g < n := by
  unfold pollardRhoAcc at h
  split at h
  · rename_i g' hloop
    split_ifs at h with hgn
    obtain rfl := Option.some.inj h
    obtain ⟨hdvd, h1⟩ := pollardRhoAccLoop_spec hloop
    have hpos : 0 < g' := Nat.pos_of_dvd_of_pos hdvd hn
    have hle : g' ≤ n := Nat.le_of_dvd hn hdvd
    exact ⟨hdvd, by omega, by omega⟩
  · simp at h

section RunningTimeAcc

open PrimeNumbers.Chapter9

/-- **Cost of a batch**: "one generic loop consists of 3 modular squarings and one modular
multiplication" — at most `4 · C.mulMod k` bit operations per pass, and the gcd is paid
only once per batch. -/
theorem rhoBatchCost_le (C : CostModel) {n a : ℕ} (ha : a < n) {U V Q : ℕ} (hU : U < n)
    (hV : V < n) (hQ : Q < n) (count : ℕ) :
    costOf C (rhoBatch n a U V Q count) ≤ count * (4 * C.mulMod n.size) := by
  have hn : 0 < n := by omega
  induction count generalizing U V Q with
  | zero => cost_unfold rhoBatch.counted
  | succ count ih =>
    have hF : ∀ x, rhoF n a x < n := fun x ↦ Nat.mod_lt _ hn
    have h₁ := rhoFCost_le C ha hU
    have h₂ := rhoFCost_le C ha hV
    have h₃ := rhoFCost_le C ha (hF V)
    have h₄ := mul_add_divMod_le C hQ (absDiff_lt (hF U) (hF (rhoF n a V)))
    have ih := ih (hF U) (hF (rhoF n a V))
      (Q := Q * absDiff (rhoF n a U) (rhoF n a (rhoF n a V)) % n) (Nat.mod_lt _ hn)
    cost_unfold rhoBatch.counted
    simp only [add_mul, one_mul]
    omega

end RunningTimeAcc

/-! ## Brent's variant

Instead of Floyd's `F⁽ⁱ⁾(s)` versus `F⁽²ⁱ⁾(s)`, Brent compares each new iterate with the
iterate saved at the last power of two: `x_j` against `x_{2^m}` for `2^m < j ≤ 2^{m+1}`.
This needs one evaluation of `F` per step instead of three. -/

/-- Brent's cycle search.  `saved = x_{2^m}`, `cur = x_j`, `i = j - 2^m`, `limit = 2^m`. -/
counted_def pollardBrentLoop (n a : ℕ) : (saved cur i limit fuel : ℕ) → Option ℕ
  | _, _, _, _, 0 => none
  | saved, cur, i, limit, fuel + 1 =>
    let cur' := rhoF n a cur
    let g := euclid n (absDiff cur' saved)
    if g = 1 then
      if i + 1 = limit then pollardBrentLoop n a cur' cur' 0 (2 * limit) fuel
      else pollardBrentLoop n a saved cur' (i + 1) limit fuel
    else some g

/-- **Pollard rho with Brent's cycle-finding.** -/
counted_def pollardBrent (n a s fuel : ℕ) : Option ℕ :=
  match pollardBrentLoop n a s s 0 1 fuel with
  | some g => if g = n then none else some g
  | none => none

theorem pollardBrentLoop_spec {n a saved cur i limit fuel g : ℕ}
    (h : pollardBrentLoop n a saved cur i limit fuel = some g) : g ∣ n ∧ g ≠ 1 := by
  induction fuel generalizing saved cur i limit with
  | zero => simp [pollardBrentLoop] at h
  | succ fuel ih =>
    simp only [pollardBrentLoop] at h
    split_ifs at h with h1 h2
    · exact ih h
    · exact ih h
    · obtain rfl := Option.some.inj h
      exact ⟨by rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left _ _, h1⟩

/-- **Soundness of Brent's variant**: any `g` returned is a nontrivial factor of `n`. -/
theorem pollardBrent_sound {n a s fuel g : ℕ} (hn : 0 < n)
    (h : pollardBrent n a s fuel = some g) : g ∣ n ∧ 1 < g ∧ g < n := by
  unfold pollardBrent at h
  split at h
  · rename_i g' hloop
    split_ifs at h with hgn
    obtain rfl := Option.some.inj h
    obtain ⟨hdvd, h1⟩ := pollardBrentLoop_spec hloop
    have hpos : 0 < g' := Nat.pos_of_dvd_of_pos hdvd hn
    have hle : g' ≤ n := Nat.le_of_dvd hn hdvd
    exact ⟨hdvd, by omega, by omega⟩
  · simp at h

/-! ### Brent's variant terminates

Notation: `x_i = F⁽ⁱ⁾(s)`.  In the phase with `limit = L` the loop holds `saved = x_m` and
compares it with `x_{m+1}, …, x_{m+L}`; then it saves `x_{m+L}` and doubles `L`.  Starting
from `m = 0`, `L = 1`, the saved index is always `m = L - 1`. -/

/-- Within a phase: if one of the comparisons `x_{m+d}` vs `x_m`, `i < d ≤ L`, has a
nontrivial gcd, the loop returns. -/
theorem pollardBrentLoop_isSome_phase {n a s m L : ℕ} (f : ℕ) (r i : ℕ) (hr : L - i = r)
    (h : ∃ d, i < d ∧ d ≤ L ∧
      euclid n (absDiff ((rhoF n a)^[m + d] s) ((rhoF n a)^[m] s)) ≠ 1) :
    (pollardBrentLoop n a ((rhoF n a)^[m] s) ((rhoF n a)^[m + i] s) i L (r + f)).isSome := by
  induction r generalizing i with
  | zero => obtain ⟨d, h₁, h₂, -⟩ := h; omega
  | succ r ih =>
    rw [Nat.add_right_comm]
    simp only [pollardBrentLoop, ← Function.iterate_succ_apply' (rhoF n a)]
    split_ifs with hg hlim
    · -- the comparison at `d = i + 1` failed, so the witness has `d > i + 1 = L`: impossible
      obtain ⟨d, h₁, h₂, h₃⟩ := h
      have : d ≠ i + 1 := by rintro rfl; exact h₃ hg
      omega
    · obtain ⟨d, h₁, h₂, h₃⟩ := h
      have : d ≠ i + 1 := by rintro rfl; exact h₃ hg
      exact ih (i + 1) (by omega) ⟨d, by omega, h₂, h₃⟩
    · rfl

/-- A whole phase: from `(saved, cur, i) = (x_m, x_{m+i}, i)` the loop either returns or
arrives, `L - i` steps later, at the start of the next phase `(x_{m+L}, x_{m+L}, 0)` with
limit `2L`. -/
theorem pollardBrentLoop_phase {n a s m L : ℕ} (f : ℕ) (r i : ℕ) (hr : L - i = r + 1) :
    (pollardBrentLoop n a ((rhoF n a)^[m] s) ((rhoF n a)^[m + i] s) i L (r + 1 + f)).isSome ∨
      pollardBrentLoop n a ((rhoF n a)^[m] s) ((rhoF n a)^[m + i] s) i L (r + 1 + f) =
        pollardBrentLoop n a ((rhoF n a)^[m + L] s) ((rhoF n a)^[m + L] s) 0 (2 * L) f := by
  induction r generalizing i with
  | zero =>
    have hiL : i + 1 = L := by omega
    rw [Nat.add_right_comm]
    simp only [pollardBrentLoop, ← Function.iterate_succ_apply' (rhoF n a), zero_add]
    split_ifs with hg
    · right; rw [show (m + i).succ = m + L by omega]
    · left; rfl
  | succ r ih =>
    rw [Nat.add_right_comm]
    simp only [pollardBrentLoop, ← Function.iterate_succ_apply' (rhoF n a)]
    split_ifs with hg hlim
    · omega
    · exact ih (i + 1) (by omega)
    · left; rfl

/-- **Brent's variant, conditionally on the heuristic.**  If `p > 1` divides `n` and the
sequence modulo `p` repeats within `T` steps (`RhoCollision p a s T`), Brent's search
stops within `4T` steps with a gcd `g ≠ 1`.  (Unconditionally `T = p` works, by
`rhoCollision_self`.)

Proof: let `x_j ≡ x_k (mod p)` with `j < k ≤ T`.  Once the phase length `L` is at least
`k`, the saved index `L - 1 ≥ j` lies on the cycle and the period `k - j ≤ L` is among the
distances tested; the phases before that take fewer than `L` steps in total, and
`L < 2k`. -/
theorem pollardBrentLoop_isSome_of_collision {n p a s T : ℕ} (hp : 1 < p) (hpn : p ∣ n)
    (hcol : RhoCollision p a s T) {fuel : ℕ} (hfuel : 4 * T ≤ fuel) :
    (pollardBrentLoop n a s s 0 1 fuel).isSome := by
  obtain ⟨j, k, hjk, hkT, heq⟩ := hcol
  -- periodicity modulo `p` from index `j` on
  have hper : ∀ m, j ≤ m →
      (rhoF p a)^[m + (k - j)] (s % p) = (rhoF p a)^[m] (s % p) := by
    intro m hm
    obtain ⟨d, rfl⟩ : ∃ d, m = d + j := ⟨m - j, by omega⟩
    rw [show d + j + (k - j) = d + k by omega, Function.iterate_add_apply, ← heq,
      ← Function.iterate_add_apply]
  -- a phase with `L ≥ k` succeeds; earlier phases lead to it
  have key : ∀ e L f : ℕ, 1 ≤ L → k ≤ L * 2 ^ e →
      (pollardBrentLoop n a ((rhoF n a)^[L - 1] s) ((rhoF n a)^[L - 1] s) 0 L
        (L * (2 ^ (e + 1) - 1) + f)).isSome := by
    intro e
    induction e with
    | zero =>
      intro L f hL hk
      have h := pollardBrentLoop_isSome_phase (n := n) (a := a) (s := s) (m := L - 1) (L := L)
        f L 0 (by omega) ⟨k - j, by omega, by omega,
          euclid_absDiff_ne_one hp hpn (by
            rw [iterate_rhoF_mod hpn, iterate_rhoF_mod hpn, hper _ (by omega)])⟩
      simpa using h
    | succ e ih =>
      intro L f hL hk
      obtain ⟨r, hr⟩ : ∃ r, L = r + 1 := ⟨L - 1, by omega⟩
      have hfuel' : L * (2 ^ (e + 1 + 1) - 1) + f =
          r + 1 + (2 * L * (2 ^ (e + 1) - 1) + f) := by
        have h2 : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
        have : 2 ^ (e + 1 + 1) - 1 = 2 * (2 ^ (e + 1) - 1) + 1 := by
          rw [pow_succ]; omega
        rw [this, hr]; ring
      rw [hfuel']
      have hphase := pollardBrentLoop_phase (n := n) (a := a) (s := s) (m := L - 1) (L := L)
        (2 * L * (2 ^ (e + 1) - 1) + f) r 0 (by omega)
      rcases hphase with hsome | hnext
      · simpa using hsome
      · rw [add_zero] at hnext
        rw [hnext]
        have := ih (2 * L) f (by omega) (by rw [pow_succ] at hk; nlinarith)
        rwa [show 2 * L - 1 = L - 1 + L by omega] at this
  -- start: `L = 1`, with `2^e ≥ k` for `e = ⌊log₂ k⌋ + 1`, and `2^(e+1) - 1 ≤ 4k`
  have hk0 : k ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hk0
  have hbound : 1 * (2 ^ (Nat.log 2 k + 1 + 1) - 1) ≤ fuel := by
    have : 2 ^ (Nat.log 2 k + 1 + 1) = 4 * 2 ^ Nat.log 2 k := by ring
    omega
  obtain ⟨f, hf⟩ : ∃ f, fuel = 1 * (2 ^ (Nat.log 2 k + 1 + 1) - 1) + f :=
    ⟨fuel - 1 * (2 ^ (Nat.log 2 k + 1 + 1) - 1), by omega⟩
  have := key (Nat.log 2 k + 1) 1 f le_rfl
    (by rw [one_mul]; exact (Nat.lt_pow_succ_log_self (by norm_num) k).le)
  rw [hf]
  simpa using this

section RunningTimeBrent

open PrimeNumbers.Chapter9

/-- **Bit complexity of Brent's variant**: each step costs one modular multiplication and
one gcd — against three and one for Algorithm 5.2.1. -/
theorem pollardBrentCost_le (C : CostModel) {n a G : ℕ} (ha : a < n)
    (hG : ∀ d < n, costOf C (euclid n d) ≤ G) {saved cur : ℕ} (hs : saved < n) (hc : cur < n)
    (i limit fuel : ℕ) :
    costOf C (pollardBrentLoop n a saved cur i limit fuel) ≤ fuel * (C.mulMod n.size + G) := by
  have hn : 0 < n := by omega
  induction fuel generalizing saved cur i limit with
  | zero => cost_unfold pollardBrentLoop.counted
  | succ fuel ih =>
    have hF : rhoF n a cur < n := Nat.mod_lt _ hn
    have h₁ := rhoFCost_le C ha hc
    have h₂ := hG _ (absDiff_lt hF hs)
    have ih₁ := ih hF hF 0 (2 * limit)
    have ih₂ := ih hs hF (i + 1) limit
    cost_unfold pollardBrentLoop.counted
    simp only [add_mul, one_mul]
    split_ifs <;> omega

end RunningTimeBrent

end PrimeNumbers.Chapter5
