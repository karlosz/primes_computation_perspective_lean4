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
def rhoF (n a x : ℕ) : ℕ := (x * x + a) % n

/-- `|u - v|` on naturals. -/
def absDiff (u v : ℕ) : ℕ := if v ≤ u then u - v else v - u

/-- **Algorithm 5.2.1, step 2 [Factor search]**, at most `fuel` passes:
```
U = F(U);
V = F(V);
V = F(V);                            // F(V) intentionally invoked twice.
g = gcd(U - V, n);
if (g == 1) goto [Factor search];
```
Returns the first `g ≠ 1`, or `none` if the fuel runs out. -/
def pollardRhoLoop (n a : ℕ) (U V : ℕ) : ℕ → Option ℕ
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
def pollardRho (n a s fuel : ℕ) : Option ℕ :=
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

/-- **Floyd cycle-finding.**  If `f` maps into `{0, …, p - 1}`, then for any start
`x < p` there is `1 ≤ i ≤ p` with `f⁽ⁱ⁾(x) = f⁽²ⁱ⁾(x)`.

Proof as in the book: by the pigeonhole principle `f⁽ʲ⁾(x) = f⁽ᵏ⁾(x)` for some
`0 ≤ j < k ≤ p`; with `l = k - j` the sequence has period `l` from index `j` on, and one
takes for `i` the first multiple of `l` exceeding `j`. -/
theorem exists_iterate_eq_iterate_two_mul {p : ℕ} (f : ℕ → ℕ) (hf : ∀ x, f x < p) {x : ℕ}
    (hx : x < p) : ∃ i, 1 ≤ i ∧ i ≤ p ∧ f^[i] x = f^[2 * i] x := by
  have hlt : ∀ i, f^[i] x < p := fun i ↦ by
    cases i with
    | zero => simpa using hx
    | succ i => rw [Function.iterate_succ_apply']; exact hf _
  -- pigeonhole among `f⁽⁰⁾(x), …, f⁽ᵖ⁾(x)`
  obtain ⟨j, k, hjk, heq⟩ : ∃ j k : Fin (p + 1), j ≠ k ∧ f^[j] x = f^[k] x := by
    obtain ⟨j, k, hjk, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (p + 1) ↦ (⟨f^[i] x, hlt i⟩ : Fin p)) (by simp)
    exact ⟨j, k, hjk, congrArg Fin.val h⟩
  wlog hlt' : (j : ℕ) < k generalizing j k
  · exact this k j hjk.symm heq.symm (by
      have : (j : ℕ) ≠ k := fun h ↦ hjk (Fin.ext h)
      omega)
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  simp only at heq hlt'
  -- the sequence has period `l = k - j` from index `j` on
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
  -- `i` = the first multiple of `l` exceeding `j`
  refine ⟨l * (j / l + 1), Nat.mul_pos hl (Nat.succ_pos _), ?_, ?_⟩
  · have : l * (j / l) ≤ j := Nat.mul_div_le j l
    rw [mul_add, mul_one]
    omega
  · have hji : j ≤ l * (j / l + 1) := (Nat.lt_mul_div_succ j hl).le
    rw [show 2 * (l * (j / l + 1)) = l * (j / l + 1) + (j / l + 1) * l by ring]
    exact (hper _ _ hji).symm

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

end PrimeNumbers.Chapter5
