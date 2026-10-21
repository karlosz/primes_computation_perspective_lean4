import PrimeNumbers.Chapter9.Nussbaumer
import PrimeNumbers.Chapter9.NussModel

/-!
# Running time of Nussbaumer convolution and multiplication (Algorithm 9.5.25)

The derived costs of `fft`, `nussbaumer` and `nussMul` in the grammar-school model, and the
proof that `nussMul` realizes the quasi-linear model `nussModel` (`nussMul_cost_le`).
-/

namespace PrimeNumbers.Chapter9

open PrimeNumbers.Chapter2

/-! ## Running time

In the grammar-school model: an addition costs the bit length plus one, the products of the
base case are schoolbook, and every step (a list cell visited, a call) costs one.  The index
arithmetic (twiddle exponents, block positions) is charged too; it costs `O(log² m)` per
vector or per entry, a lower-order term. -/

/-- All entries of `v` are below `2^β` in absolute value. -/
def Bdd (β : ℕ) (v : List ℤ) : Prop := ∀ x ∈ v, x.natAbs < 2 ^ β

theorem Bdd.mono {β β' : ℕ} {v : List ℤ} (h : Bdd β v) (hβ : β ≤ β') : Bdd β' v :=
  fun x hx ↦ (h x hx).trans_le (Nat.pow_le_pow_right two_pos hβ)

theorem Bdd.getD {β : ℕ} {v : List ℤ} (h : Bdd β v) (i : ℕ) : (v.getD i 0).natAbs < 2 ^ β := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : v[i]? with
  | none => simp
  | some x => simpa using h x (List.mem_of_getElem? hv)

theorem bdd_replicate_zero (β n : ℕ) : Bdd β (List.replicate n 0) := fun x hx ↦ by
  rw [List.eq_of_mem_replicate hx]; simp

theorem natAbs_add_lt {x y : ℤ} {β : ℕ} (hx : x.natAbs < 2 ^ β) (hy : y.natAbs < 2 ^ β) :
    (x + y).natAbs < 2 ^ (β + 1) := by
  have := Int.natAbs_add_le x y; rw [pow_succ]; omega

theorem natAbs_sub_lt {x y : ℤ} {β : ℕ} (hx : x.natAbs < 2 ^ β) (hy : y.natAbs < 2 ^ β) :
    (x - y).natAbs < 2 ^ (β + 1) := by
  have := Int.natAbs_sub_le x y; rw [pow_succ]; omega

theorem mem_zipWith' {α β γ : Type} {f : α → β → γ} {l : List α} {l' : List β} {x : γ}
    (h : x ∈ List.zipWith f l l') : ∃ a ∈ l, ∃ b ∈ l', x = f a b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_zipWith, lt_min_iff] at hi
  exact ⟨_, List.getElem_mem hi.1, _, List.getElem_mem hi.2, List.getElem_zipWith ..⟩

theorem bdd_vadd {β : ℕ} {u v : List ℤ} (hu : Bdd β u) (hv : Bdd β v) : Bdd (β + 1) (vadd u v) :=
  fun x hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hx
    exact natAbs_add_lt (hu a ha) (hv b hb)

theorem bdd_vsub {β : ℕ} {u v : List ℤ} (hu : Bdd β u) (hv : Bdd β v) : Bdd (β + 1) (vsub u v) :=
  fun x hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hx
    exact natAbs_sub_lt (hu a ha) (hv b hb)

theorem bdd_rotLow {β m j : ℕ} {u : List ℤ} (hu : Bdd β u) : Bdd β (rotLow m j u) := fun x hx ↦ by
  simp only [rotLow, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩ | hx
  · simpa using hu y (List.mem_of_mem_drop hy)
  · exact hu x (List.mem_of_mem_take hx)

theorem bdd_rot {β m j : ℕ} {u : List ℤ} (hu : Bdd β u) : Bdd β (rot m j u) := by
  unfold rot; split_ifs
  · exact bdd_rotLow hu
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simpa using bdd_rotLow hu y hy

theorem mem_twiddle {m e : ℕ} (hm : 0 < m) : ∀ {i : ℕ} {os : List (List ℤ)} {v : List ℤ},
    v ∈ twiddle m e i os → ∃ o ∈ os, ∃ j, j < 2 * m ∧ v = rot m j o
  | _, [], _, h => by simp [twiddle] at h
  | i, o :: os, v, h => by
    simp only [twiddle, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨o, by simp, _, Nat.mod_lt _ (by omega), rfl⟩
    · obtain ⟨o', ho', j, hj, rfl⟩ := mem_twiddle hm h
      exact ⟨o', by simp [ho'], j, hj, rfl⟩

theorem mem_of_mem_evens {α : Type} : ∀ {l : List α} {x : α}, x ∈ evens l → x ∈ l
  | a :: b :: l, x, h => by
    simp only [evens, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (mem_of_mem_evens h))
  | [a], x, h => by simpa [evens] using h
  | [], x, h => by simp [evens] at h

theorem mem_of_mem_odds {α : Type} : ∀ {l : List α} {x : α}, x ∈ odds l → x ∈ l
  | a :: b :: l, x, h => by
    simp only [odds, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (mem_of_mem_odds h))
  | [a], x, h => by simp [odds] at h
  | [], x, h => by simp [odds] at h

theorem sum_zipWith_le {α β : Type} (f : α → β → ℕ) {s : ℕ} :
    ∀ (l : List α) (l' : List β), (∀ a ∈ l, ∀ b ∈ l', f a b ≤ s) →
      (List.zipWith f l l').sum ≤ l.length * s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: l', h => by
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    have := sum_zipWith_le f l l' fun a ha b hb ↦ h a (by simp [ha]) b (by simp [hb])
    have := h a (by simp) b (by simp)
    rw [add_mul, one_mul]; omega

@[cost_le] theorem vadd_cost_le {β : ℕ} {u v : List ℤ} (hu : Bdd β u) (hv : Bdd β v)
    (hl : u.length = v.length) : costOf school (vadd u v) ≤ u.length * (β + 2) + 2 := by
  cost_unfold vadd.counted
  have := sum_zipWith_le (fun a b : ℤ ↦ max a.natAbs.size b.natAbs.size + 1) (s := β + 1) u v
    fun a ha b hb ↦ by
      have := Nat.size_le.2 (hu a ha); have := Nat.size_le.2 (hv b hb); omega
  rw [hl, min_self] at *
  cost_bound

@[cost_le] theorem vsub_cost_le {β : ℕ} {u v : List ℤ} (hu : Bdd β u) (hv : Bdd β v)
    (hl : u.length = v.length) : costOf school (vsub u v) ≤ u.length * (β + 2) + 2 := by
  cost_unfold vsub.counted
  have := sum_zipWith_le (fun a b : ℤ ↦ max a.natAbs.size b.natAbs.size + 1) (s := β + 1) u v
    fun a ha b hb ↦ by
      have := Nat.size_le.2 (hu a ha); have := Nat.size_le.2 (hv b hb); omega
  rw [hl, min_self] at *
  cost_bound

theorem size_two_mul {m : ℕ} (hm : 1 ≤ m) : (2 * m).size = m.size + 1 := by
  rw [show 2 * m = m <<< 1 by rw [Nat.shiftLeft_eq]; ring, Nat.size_shiftLeft (by omega)]

@[cost_le] theorem rotLow_cost_le {m j : ℕ} {u : List ℤ} (hu : u.length = m) (hj : j ≤ m) :
    costOf school (rotLow m j u) ≤ 4 * m + 7 := by
  cost_unfold rotLow.counted
  simp only [List.length_drop, List.length_map, hu]
  cost_bound

@[cost_le] theorem rot_cost_le {m j : ℕ} {u : List ℤ} (hu : u.length = m) (hj : j < 2 * m) :
    costOf school (rot m j u) ≤ 7 * m + 12 := by
  have := size_le_self m
  have hjs : j.size ≤ m.size + 1 := by
    have := Nat.size_le_size (show j ≤ 2 * m by omega); rwa [size_two_mul (by omega)] at this
  cost_unfold rot.counted
  split_ifs with h
  · have := rotLow_cost_le hu h.le; omega
  · have := rotLow_cost_le hu (show j - m ≤ m by omega)
    rw [length_rotLow hu (by omega)]
    cost_bound

@[cost_le] theorem evens_cost_le {α : Type} : ∀ l : List α, costOf school (evens l) ≤ l.length + 1
  | a :: b :: l => by
    have := evens_cost_le l
    cost_unfold evens.counted
  | [a] => by cost_unfold evens.counted <;> simp
  | [] => by cost_unfold evens.counted <;> simp

@[cost_le] theorem odds_cost_le {α : Type} : ∀ l : List α, costOf school (odds l) ≤ l.length + 1
  | a :: b :: l => by
    have := odds_cost_le l
    cost_unfold odds.counted
  | [a] => by cost_unfold odds.counted <;> simp
  | [] => by cost_unfold odds.counted <;> simp

/-- `(size m + 2)² ≤ 16 m`: the index arithmetic of a vector is linear in its length. -/
theorem size_add_two_sq_le {m : ℕ} (hm : 1 ≤ m) : (m.size + 2) ^ 2 ≤ 16 * m := by
  have h := Nat.lt_size.mp (show m.size - 1 < m.size by have := Nat.size_pos.mpr hm; omega)
  have key : ∀ s, (s + 3) ^ 2 ≤ 16 * 2 ^ s := by
    intro s
    induction s with
    | zero => norm_num
    | succ s ih =>
      have : (s + 1 + 3) ^ 2 ≤ 2 * (s + 3) ^ 2 := by ring_nf; nlinarith [Nat.zero_le (s * s)]
      rw [pow_succ 2 s]; linarith
  have := key (m.size - 1)
  rw [show m.size - 1 + 3 = m.size + 2 by have := Nat.size_pos.mpr hm; omega] at this
  omega

/-- The twiddles: a rotation and the exponent `e i mod 2m` per vector. -/
@[cost_le] theorem twiddle_cost_le {m e : ℕ} (hm : 1 ≤ m) (he : e ≤ 4 * m * m) :
    ∀ (i : ℕ) (os : List (List ℤ)), (∀ o ∈ os, o.length = m) → i + os.length ≤ 2 * m →
      costOf school (twiddle m e i os) ≤ os.length * (99 * m) + 1
  | _, [], _, _ => by cost_unfold twiddle.counted
  | i, o :: os, ho, hi => by
    have ih := twiddle_cost_le hm he (i + 1) os (fun o' h' ↦ ho o' (by simp [h'])) (by
      simp at hi; omega)
    have hr := rot_cost_le (ho o (by simp)) (Nat.mod_lt (e * i) (show 0 < 2 * m by omega))
    have hsq := size_add_two_sq_le hm
    have hm2 := Nat.lt_size_self m
    have hes : e.size ≤ 2 * m.size + 2 := Nat.size_le.mpr (by
      calc e < 2 ^ m.size * 2 ^ m.size * 4 := by nlinarith
        _ = 2 ^ (2 * m.size + 2) := by ring)
    have his : i.size ≤ m.size + 1 := Nat.size_le.mpr (by
      simp at hi; rw [pow_succ]; omega)
    have h2m := size_two_mul hm
    have heis : (e * i).size ≤ 3 * m.size + 3 := (size_mul_le e i).trans (by omega)
    cost_unfold twiddle.counted
    rw [h2m, show Nat.size 2 = 2 by decide, school_mul, school_divMod]
    have m₁ : max 2 m.size ≤ m.size + 2 := by omega
    have m₂ : max i.size 1 ≤ m.size + 1 := by omega
    have t₁ : e.size * i.size ≤ (2 * m.size + 2) * (m.size + 1) := Nat.mul_le_mul hes his
    have t₂ : ((e * i).size - (m.size + 1) + 1) * (m.size + 1) ≤
        (2 * m.size + 3) * (m.size + 1) := Nat.mul_le_mul_right _ (by omega)
    cost_bound

/-- **Running time of the FFT**: `2^l (l m (β + l + 70) + 5)` bit operations for `2^l`
vectors of length `m` with entries below `2^β` (`2^l ≤ 2m`, the root `x^e` with
`e 2^l ≤ 4m²`); the entries grow by one bit per level. -/
theorem fft_cost {m : ℕ} (hm : 1 ≤ m) : ∀ (l e β : ℕ) (vs : List (List ℤ)), vs.length = 2 ^ l →
    (∀ v ∈ vs, v.length = m ∧ Bdd β v) → 2 ^ l ≤ 2 * m → e * 2 ^ l ≤ 4 * m * m →
    (fft m e vs).length = 2 ^ l ∧ (∀ v ∈ fft m e vs, v.length = m ∧ Bdd (β + l) v) ∧
      costOf school (fft m e vs) ≤ 2 ^ l * (l * m * (β + l + 70) + 5) := by
  have hm0 : 0 < m := by omega
  intro l
  induction l with
  | zero =>
    intro e β vs hlen hvs _ _
    obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
      match vs, hlen with
      | [v], _ => exact ⟨v, rfl⟩
    have h1 : [v].length ≤ 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [fft, if_pos h1]; rfl
    · rw [fft, if_pos h1]; simpa using hvs
    · cost_unfold fft.counted
  | succ l ih =>
    intro e β vs hlen hvs hL he
    have hnot : ¬ vs.length ≤ 1 := by
      rw [hlen]; have := Nat.one_lt_two_pow (n := l + 1) (by omega); omega
    have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by ring
    have hev : (evens vs).length = 2 ^ l := by rw [length_evens, hlen, h2l]; omega
    have hod : (odds vs).length = 2 ^ l := by rw [length_odds, hlen, h2l]; omega
    have hL' : 2 ^ l ≤ 2 * m := by omega
    have he' : 2 * e * 2 ^ l ≤ 4 * m * m := by rw [h2l] at he; linarith
    obtain ⟨lE, vE, cE⟩ := ih (2 * e) β (evens vs) hev (fun v hv ↦ hvs v (mem_of_mem_evens hv))
      hL' he'
    obtain ⟨lO, vO, cO⟩ := ih (2 * e) β (odds vs) hod (fun v hv ↦ hvs v (mem_of_mem_odds hv))
      hL' he'
    have vT : ∀ t ∈ twiddle m e 0 (fft m (2 * e) (odds vs)), t.length = m ∧ Bdd (β + l) t := by
      intro t ht
      obtain ⟨o, ho, j, hj, rfl⟩ := mem_twiddle hm0 ht
      exact ⟨length_rot (vO o ho).1 hj, bdd_rot (vO o ho).2⟩
    have lT : (twiddle m e 0 (fft m (2 * e) (odds vs))).length = 2 ^ l := by rw [length_twiddle, lO]
    refine ⟨?_, ?_, ?_⟩
    · rw [fft, if_neg hnot]; simp [lE, lT]; omega
    · rw [fft, if_neg hnot]
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hv
        exact ⟨by rw [length_vadd (by rw [(vE a ha).1, (vT b hb).1])]; exact (vE a ha).1,
          bdd_vadd (vE a ha).2 (vT b hb).2⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hv
        exact ⟨by rw [length_vsub (by rw [(vE a ha).1, (vT b hb).1])]; exact (vE a ha).1,
          bdd_vsub (vE a ha).2 (vT b hb).2⟩
    · have he₁ : e ≤ 4 * m * m := le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) he
      have cT := twiddle_cost_le hm he₁ 0 (fft m (2 * e) (odds vs)) (fun o ho ↦ (vO o ho).1)
        (by rw [lO]; omega)
      have hA := sum_zipWith_le (fun a b ↦ costOf school (vadd a b)) (s := m * (β + l + 2) + 2)
        (fft m (2 * e) (evens vs)) (twiddle m e 0 (fft m (2 * e) (odds vs))) fun a ha b hb ↦ by
          have := vadd_cost_le (vE a ha).2 (vT b hb).2 (by rw [(vE a ha).1, (vT b hb).1])
          rwa [(vE a ha).1] at this
      have hS := sum_zipWith_le (fun a b ↦ costOf school (vsub a b)) (s := m * (β + l + 2) + 2)
        (fft m (2 * e) (evens vs)) (twiddle m e 0 (fft m (2 * e) (odds vs))) fun a ha b hb ↦ by
          have := vsub_cost_le (vE a ha).2 (vT b hb).2 (by rw [(vE a ha).1, (vT b hb).1])
          rwa [(vE a ha).1] at this
      have hEv := evens_cost_le vs
      have hOd := odds_cost_le vs
      rw [lE] at hA hS
      rw [lO] at cT
      have hes : e.size ≤ 4 * m := by
        have := Nat.size_le.mpr (show e < 2 ^ (2 * m.size + 2) by
          have := Nat.lt_size_self m
          calc e < 2 ^ m.size * 2 ^ m.size * 4 := by nlinarith
            _ = 2 ^ (2 * m.size + 2) := by ring)
        have := size_le_self m; omega
      have hH : 1 ≤ 2 ^ l := Nat.one_le_two_pow
      have hHm : 1 ≤ 2 ^ l * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
      cost_unfold fft.counted
      rw [List.length_zipWith, lE, lT, min_self, hlen, show Nat.size 2 = 2 by decide]
      have m₁ : min (2 ^ (l + 1)).size 1 ≤ 1 := min_le_right _ _
      have m₂ : max 2 e.size ≤ 4 * m + 2 := by omega
      rw [hlen] at hEv hOd
      have key : 2 ^ (l + 1) * ((l + 1) * m * (β + (l + 1) + 70) + 5) =
          2 * (2 ^ l * (l * m * (β + l + 70) + 5)) + 2 * (2 ^ l * m) * (β + 2 * l + 71) := by
        rw [h2l]; ring
      rw [key]
      have t₁ : 2 ^ l * (m * (β + l + 2) + 2) = 2 ^ l * m * (β + l + 2) + 2 * 2 ^ l := by ring
      have t₂ : 2 ^ l * (99 * m) = 99 * (2 ^ l * m) := by ring
      have t₃ : 2 * (2 ^ l * m) * (β + 2 * l + 71) = 2 * (2 ^ l * m) * (β + l + 2) +
          2 * (2 ^ l * m) * (l + 69) := by ring
      have t₄ : 2 * (2 ^ l * m) * 69 ≤ 2 * (2 ^ l * m) * (l + 69) := Nat.mul_le_mul_left _ (by omega)
      have t₅ : m ≤ 2 ^ l * m := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      have t₆ : 2 ^ l ≤ 2 ^ l * m := Nat.le_mul_of_pos_right _ hm0
      rw [h2l] at hEv hOd
      linarith

theorem natAbs_term_add_one_le {β : ℕ} {x y : ℤ} (hx : x.natAbs < 2 ^ β) (hy : y.natAbs < 2 ^ β) :
    (x * y).natAbs + 1 ≤ 2 ^ (2 * β) := by
  rw [Int.natAbs_mul, two_mul, pow_add]
  exact Nat.mul_lt_mul'' hx hy

/-- The partial sums of the schoolbook product: `|ncTerm| + n ≤ n 2^{2β}` for `n` terms. -/
theorem ncTerm_bound {β m s : ℕ} {b : List ℤ} (hb : Bdd β b) : ∀ (i : ℕ) (as : List ℤ), Bdd β as →
    (ncTerm m s b i as).natAbs + as.length ≤ as.length * 2 ^ (2 * β)
  | _, [], _ => by simp [ncTerm]
  | i, a :: as, ha => by
    have ih := ncTerm_bound (m := m) (s := s) hb (i + 1) as fun x hx ↦ ha x (by simp [hx])
    have hterm : (if i ≤ s then a * b.getD (s - i) 0 else -(a * b.getD (m + s - i) 0)).natAbs + 1 ≤
        2 ^ (2 * β) := by
      split_ifs
      · exact natAbs_term_add_one_le (ha a (by simp)) (hb.getD _)
      · rw [Int.natAbs_neg]; exact natAbs_term_add_one_le (ha a (by simp)) (hb.getD _)
    have := Int.natAbs_add_le (if i ≤ s then a * b.getD (s - i) 0 else -(a * b.getD (m + s - i) 0))
      (ncTerm m s b (i + 1) as)
    rw [ncTerm, List.length_cons, add_mul, one_mul]
    omega

@[cost_le] theorem ncTerm_cost_le {β m s K : ℕ} {b : List ℤ} (hb : Bdd β b) (hm : m ≤ 2 ^ K) (hs : s < m) :
    ∀ (i : ℕ) (as : List ℤ), Bdd β as → i + as.length ≤ m →
    costOf school (ncTerm m s b i as) ≤
      as.length * (β * β + 4 * β + 5 * K + b.length + 13) + 1
  | _, [], _, _ => by cost_unfold ncTerm.counted
  | i, a :: as, ha, hlen => by
    have has : Bdd β as := fun x hx ↦ ha x (by simp [hx])
    simp only [List.length_cons] at hlen
    have ih := ncTerm_cost_le (K := K) hb hm hs (i + 1) as has (by omega)
    have hrest := ncTerm_bound (m := m) (s := s) hb (i + 1) as has
    have hsr : (ncTerm m s b (i + 1) as).natAbs.size ≤ 2 * β + K := by
      refine Nat.size_le.2 ?_
      rw [Nat.pow_add, mul_comm]
      have : as.length * 2 ^ (2 * β) ≤ 2 ^ K * 2 ^ (2 * β) :=
        Nat.mul_le_mul_right _ (by omega)
      have := Nat.one_le_two_pow (n := 2 * β)
      by_cases h0 : as.length = 0
      · rw [h0] at hrest; nlinarith [Nat.one_le_two_pow (n := K)]
      · omega
    have ha' := Nat.size_le.2 (ha a (by simp))
    have hgs := fun j ↦ Nat.size_le.2 (hb.getD (i := j))
    have hts : ∀ j, (a * b.getD j 0).natAbs.size ≤ 2 * β := fun j ↦ Nat.size_le.2 (by
      have := natAbs_term_add_one_le (ha a (by simp)) (hb.getD j); omega)
    have hmul : ∀ j, a.natAbs.size * (b.getD j 0).natAbs.size ≤ β * β := fun j ↦
      Nat.mul_le_mul ha' (hgs j)
    have hK : ∀ x, x < 2 * m → x.size ≤ K + 1 := fun x hx ↦ Nat.size_le.2 (by rw [pow_succ]; omega)
    have := hK i (by omega); have := hK s (by omega); have := hK (m + s) (by omega)
    have := hK m (by omega)
    have x₁ : min i.size s.size ≤ K + 1 := by omega
    have x₂ : max s.size i.size ≤ K + 1 := by omega
    have x₃ : max i.size 1 ≤ K + 1 := by omega
    have x₄ : max m.size s.size ≤ K + 1 := by omega
    have x₅ : max (m + s).size i.size ≤ K + 1 := by omega
    cost_unfold ncTerm.counted
    simp only [school_mul, List.length_cons]
    split_ifs
    · have := hmul (s - i); have := hts (s - i)
      have : (a * b.getD (s - i) 0).natAbs.size ≤ 2 * β + K := by omega
      have : min (s - i) b.length ≤ b.length := min_le_right _ _
      have hmx : max (a * b.getD (s - i) 0).natAbs.size (ncTerm m s b (i + 1) as).natAbs.size ≤
        2 * β + K := by omega
      nlinarith
    · have := hmul (m + s - i); have := hts (m + s - i)
      have : min (m + s - i) b.length ≤ b.length := min_le_right _ _
      have hmx : max (-(a * b.getD (m + s - i) 0)).natAbs.size
        (ncTerm m s b (i + 1) as).natAbs.size ≤ 2 * β + K := by rw [Int.natAbs_neg]; omega
      nlinarith

/-- The schoolbook negacyclic product of vectors of length `2^k` with entries below `2^β`
(the base case of Nussbaumer's recursion). -/
@[cost_le] theorem ncSchool_cost_le {β k : ℕ} {a b : List ℤ} (ha : a.length = 2 ^ k) (hb : b.length = 2 ^ k)
    (hab : Bdd β a) (hbb : Bdd β b) : costOf school (ncSchool (2 ^ k) a b) ≤
      2 ^ k * (2 ^ k * (β * β + 4 * β + 5 * k + 2 ^ k + 13) + 3) + 3 := by
  cost_unfold ncSchool.counted
  have := sum_map_le_length_mul (List.range (2 ^ k)) (fun s ↦ costOf school (ncTerm (2 ^ k) s b 0 a))
    (s := 2 ^ k * (β * β + 4 * β + 5 * k + 2 ^ k + 13) + 1) fun s hs ↦ by
      have := ncTerm_cost_le (m := 2 ^ k) (s := s) (K := k) hbb le_rfl (List.mem_range.1 hs) 0 a
        hab (by omega)
      rwa [ha, hb] at this
  simp only [List.length_range] at *
  nlinarith

theorem bdd_ncSchool {β k : ℕ} {a b : List ℤ} (ha : a.length = 2 ^ k) (hab : Bdd β a)
    (hbb : Bdd β b) : Bdd (2 * β + k) (ncSchool (2 ^ k) a b) := fun x hx ↦ by
  simp only [ncSchool, List.mem_map, List.mem_range] at hx
  obtain ⟨s, _, rfl⟩ := hx
  have := ncTerm_bound (m := 2 ^ k) (s := s) hbb 0 a hab
  rw [ha] at this
  rw [pow_add, mul_comm]
  have := Nat.one_le_two_pow (n := k)
  nlinarith

/-- Nussbaumer's algorithm and the schoolbook method give the same coefficients. -/
theorem nussbaumer_eq_ncSchool {k : ℕ} {a b : List ℤ} (ha : a.length = 2 ^ k)
    (hb : b.length = 2 ^ k) : nussbaumer k a b = ncSchool (2 ^ k) a b := by
  obtain ⟨hl, he⟩ := nussbaumer_spec k a b ha hb
  exact ev_inj (Nat.two_pow_pos k) hl (length_ncSchool _ _ _) (by rw [he, ev_ncSchool ha hb])

theorem bdd_padded {β : ℕ} (r m₁ : ℕ) {a : List ℤ} (ha : Bdd β a) :
    ∀ v ∈ (List.range r).map (fun j ↦ block r m₁ j a) ++ List.replicate r (List.replicate m₁ 0),
      Bdd β v := by
  intro v hv
  simp only [List.mem_append, List.mem_map, List.mem_replicate] at hv
  rcases hv with ⟨j, _, rfl⟩ | ⟨_, rfl⟩
  · intro x hx
    simp only [block, List.mem_map, List.mem_range] at hx
    obtain ⟨l, _, rfl⟩ := hx
    exact ha.getD _
  · exact bdd_replicate_zero _ _

/-- Splitting into `r` blocks of length `m₁` (`r m₁ = 2^K`): a product and a sum of indices
per entry. -/
@[cost_le] theorem blocks_cost_le {r m₁ K : ℕ} {a : List ℤ} (hr : r * m₁ = 2 ^ K) (ha : a.length = 2 ^ K) :
    costOf school (blocks r m₁ a) ≤ 2 ^ K * ((K + 1) ^ 2 + K + 9) + 4 := by
  have hsz : ∀ x, x < 2 ^ K → x.size ≤ K := fun x hx ↦ Nat.size_le.2 hx
  have hrK : r.size ≤ K + 1 := Nat.size_le.2 (by
    have : r ≤ 2 ^ K := by
      rcases Nat.eq_zero_or_pos m₁ with h | h
      · rw [h, mul_zero] at hr; exact absurd hr.symm (by positivity)
      · rw [← hr]; exact Nat.le_mul_of_pos_right _ h
    have := Nat.two_pow_pos K
    rw [pow_succ]; omega)
  have hrN : r ≤ 2 ^ K := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, mul_zero] at hr; exact absurd hr.symm (by positivity)
    · rw [← hr]; exact Nat.le_mul_of_pos_right _ h
  cost_unfold blocks.counted
  simp only [school_mul, List.length_range, ha]
  have inner : ∀ j ∈ List.range r, m₁ + 1 + (m₁ + 1 +
      (List.map (fun l ↦ r.size * l.size + (max j.size (r * l).size + 1 + 1)) (List.range m₁)).sum) ≤
        m₁ * ((K + 1) ^ 2 + K + 2) + 2 * m₁ + 2 := by
    intro j hj
    have hj := List.mem_range.1 hj
    have := sum_map_le_length_mul (List.range m₁)
      (fun l ↦ r.size * l.size + (max j.size (r * l).size + 1 + 1)) (s := (K + 1) ^ 2 + K + 2)
      fun l hl ↦ by
        have hl := List.mem_range.1 hl
        have hrl : r * l < 2 ^ K := by rw [← hr]; exact Nat.mul_lt_mul_of_pos_left hl (by omega)
        have h₁ := hsz (r * l) hrl
        have h₂ := hsz j (by omega)
        have h₃ := hsz l (by
          have : m₁ ≤ 2 ^ K := by rw [← hr]; exact Nat.le_mul_of_pos_left _ (by omega)
          omega)
        have := Nat.mul_le_mul hrK h₃
        have : max j.size (r * l).size ≤ K := by omega
        cost_bound
    simp only [List.length_range] at this
    cost_bound
  have outer := sum_map_le_length_mul (List.range r) _ inner
  simp only [List.length_range] at outer
  have : r * (m₁ * ((K + 1) ^ 2 + K + 2) + 2 * m₁ + 2) =
      2 ^ K * ((K + 1) ^ 2 + K + 2) + 2 * 2 ^ K + 2 * r := by rw [← hr]; ring
  rw [this] at outer
  cost_bound

/-- Reassembling `r` blocks of length `m₁` into `2^K = r m₁` coefficients: a division and a
remainder of indices per entry. -/
@[cost_le] theorem unblock_cost_le {r m₁ K : ℕ} {D : List (List ℤ)} (hr : r * m₁ = 2 ^ K)
    (hD : D.length = r) (hDl : ∀ v ∈ D, v.length = m₁) :
    costOf school (unblock r (2 ^ K) D) ≤ 2 ^ K * (2 * (K + 1) ^ 2 + 8) + 5 := by
  have hrN : r ≤ 2 ^ K := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, mul_zero] at hr; exact absurd hr.symm (by positivity)
    · rw [← hr]; exact Nat.le_mul_of_pos_right _ h
  have hrK : r.size ≤ K + 1 := Nat.size_le.2 (by have := Nat.two_pow_pos K; rw [pow_succ]; omega)
  cost_unfold unblock.counted
  simp only [school_divMod, List.length_range, List.length_map, hD]
  have hsum₁ : (List.map (fun a ↦ a.length + 1) D).sum = r * (m₁ + 1) := by
    rw [List.map_congr_left (fun a ha ↦ by rw [hDl a ha]), List.map_const', List.sum_replicate, hD]
    rfl
  have hsum₂ := sum_map_le_length_mul (List.range (2 ^ K))
    (fun a ↦ (a.size - r.size + 1) * r.size + (1 + ((a.size - r.size + 1) * r.size + 1)))
    (s := 2 * (K + 1) ^ 2 + 2) fun i hi ↦ by
      have hi := Nat.size_le.2 (List.mem_range.1 hi)
      have : (i.size - r.size + 1) * r.size ≤ (K + 1) * (K + 1) := Nat.mul_le_mul (by omega) hrK
      cost_bound
  simp only [List.length_range] at hsum₂
  cost_bound

/-- The arithmetic of the recursion: what one level costs, beyond its `2r` half-size
products, fits in the slack of `2k² + 1` over `2 (2k₁² + 1)`. -/
theorem nussbaumer_cost_step {k₁ k₂ N G : ℕ} (h : k₁ = k₂ ∨ k₁ = k₂ + 1) (hk₂ : 1 ≤ k₂)
    (hG : 72 ≤ G) :
    2 * (N * (2 * k₁ ^ 2 + 1) * (8 * G ^ 2)) + 64 * (N * G * (k₂ + 1)) ≤
      N * (2 * (k₁ + k₂) ^ 2 + 1) * (8 * G ^ 2) := by
  have key : 64 * (k₂ + 1) ≤ 8 * G * (2 * (k₁ + k₂) ^ 2 - 4 * k₁ ^ 2 - 1) := by
    have h1 : 4 * k₂ ^ 2 - 3 ≤ 2 * (k₁ + k₂) ^ 2 - 4 * k₁ ^ 2 - 1 := by
      rcases h with rfl | rfl
      · have : 2 * (k₁ + k₁) ^ 2 = 8 * k₁ ^ 2 := by ring
        omega
      · have : 2 * (k₂ + 1 + k₂) ^ 2 = 8 * k₂ ^ 2 + 8 * k₂ + 2 := by ring
        have : 4 * (k₂ + 1) ^ 2 = 4 * k₂ ^ 2 + 8 * k₂ + 4 := by ring
        omega
    have h2 : 1 ≤ k₂ ^ 2 := Nat.one_le_pow _ _ hk₂
    have h3 : 64 * (k₂ + 1) ≤ 576 * (4 * k₂ ^ 2 - 3) := by
      have : k₂ ≤ k₂ ^ 2 := by nlinarith
      omega
    calc 64 * (k₂ + 1) ≤ 576 * (4 * k₂ ^ 2 - 3) := h3
      _ ≤ 8 * G * (4 * k₂ ^ 2 - 3) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := Nat.mul_le_mul_left _ h1
  have h4 : 2 * (2 * k₁ ^ 2 + 1) + (2 * (k₁ + k₂) ^ 2 - 4 * k₁ ^ 2 - 1) = 2 * (k₁ + k₂) ^ 2 + 1 := by
    have : 4 * k₁ ^ 2 + 1 ≤ 2 * (k₁ + k₂) ^ 2 := by rcases h with rfl | rfl <;> nlinarith
    omega
  set D := 2 * (k₁ + k₂) ^ 2 - 4 * k₁ ^ 2 - 1
  have h5 : N * G * (64 * (k₂ + 1)) ≤ N * G * (8 * G * D) := Nat.mul_le_mul_left _ key
  rw [← h4]
  nlinarith

set_option maxHeartbeats 4000000 in
-- the unfolded cost of one level of the recursion is a long sum of charges
/-- **Running time of Nussbaumer's algorithm**: for vectors of length `2^k` with entries below
`2^β`, and any `γ ≥ β + 2k`, at most `2^k (2k² + 1) · 8 (γ + 72)²` bit operations. -/
@[cost_le] theorem nussbaumer_cost (k : ℕ) : ∀ (β γ : ℕ) (a b : List ℤ), a.length = 2 ^ k →
    b.length = 2 ^ k → Bdd β a → Bdd β b → β + 2 * k ≤ γ →
    costOf school (nussbaumer k a b) ≤ 2 ^ k * (2 * k ^ 2 + 1) * (8 * (γ + 72) ^ 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro β γ a b ha hb hab hbb hγ
  by_cases hk : k ≤ 2
  · have h := ncSchool_cost_le ha hb hab hbb
    have hks : k.size ≤ 2 := Nat.size_le.2 (by omega)
    cost_unfold nussbaumer.counted
    simp only [hk, ↓reduceIte, Nat.size_pow, show Nat.size 2 = 2 by decide]
    interval_cases k <;> simp only [show Nat.size 2 = 2 by decide, show Nat.size 1 = 1 by decide,
      Nat.size_zero] at * <;> simp at h ⊢ <;> nlinarith
  have hks : k.size ≤ k := size_le_self k
  cost_unfold nussbaumer.counted
  simp only [hk, ↓reduceIte, Nat.size_pow, show Nat.size 2 = 2 by decide]
  cost_simp
  generalize hk₁ : (k + 1) / 2 = k₁
  generalize hk₂ : k / 2 = k₂
  have hle : k₂ ≤ k₁ := by omega
  have hk1lt : k₁ < k := by omega
  have hkk : k = k₁ + k₂ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have hk1s : (k + 1).size ≤ k + 1 := size_le_self _
  have hk₁s : k₁.size ≤ k := (size_le_self _).trans (by omega)
  have hk₂s : k₂.size ≤ k := (size_le_self _).trans (by omega)
  have hrm : 2 ^ k₂ * 2 ^ k₁ = 2 ^ k := by rw [← pow_add]; congr 1; omega
  have hLm : 2 ^ (k₂ + 1) * 2 ^ k₁ = 2 * 2 ^ k := by rw [pow_succ, ← hrm]; ring
  have he : 2 ^ (k₁ - k₂) * 2 ^ (k₂ + 1) = 2 * 2 ^ k₁ := by
    rw [← pow_add, show k₁ - k₂ + (k₂ + 1) = k₁ + 1 by omega, pow_succ]; ring
  have hes : 2 ^ (k₁ - k₂) ≤ 2 * 2 ^ k₁ := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k₁ - k₂ ≤ k₁ by omega); omega
  have h2s : (2 * 2 ^ k₁).size = k₁ + 2 := by
    rw [show 2 * 2 ^ k₁ = 2 ^ (k₁ + 1) by ring, Nat.size_pow]
  generalize 2 ^ (k₁ - k₂) = e at he hes ⊢
  set m₁ := 2 ^ k₁ with hm₁
  set r := 2 ^ k₂ with hr
  set N := 2 ^ k with hN
  have hm₁pos : 1 ≤ m₁ := Nat.one_le_two_pow
  have hr1 : 1 ≤ r := Nat.one_le_two_pow
  have hrm₁ : r ≤ m₁ := Nat.pow_le_pow_right (by norm_num) hle
  have hL : 2 ^ (k₂ + 1) = r + r := by rw [pow_succ]; ring
  have hβ₁ : β + k₂ + 1 + 2 * k₁ ≤ γ := by omega
  -- the blocks
  have cBa := blocks_cost_le (K := k) (a := a) hrm ha
  have cBb := blocks_cost_le (K := k) (a := b) hrm hb
  have lBa : (blocks r m₁ a).length = r := by simp [blocks_eq]
  have lBb : (blocks r m₁ b).length = r := by simp [blocks_eq]
  rw [lBa, lBb]
  have hAv := fun v hv ↦ And.intro ((padded_spec r m₁ a).2.1 v hv) (bdd_padded r m₁ hab v hv)
  have hBv := fun v hv ↦ And.intro ((padded_spec r m₁ b).2.1 v hv) (bdd_padded r m₁ hbb v hv)
  have hAl := (padded_spec r m₁ a).1
  have hBl := (padded_spec r m₁ b).1
  simp only [← blocks_eq] at hAv hBv hAl hBl
  generalize blocks r m₁ a ++ List.replicate r (List.replicate m₁ 0) = A at hAv hAl ⊢
  generalize blocks r m₁ b ++ List.replicate r (List.replicate m₁ 0) = B at hBv hBl ⊢
  rw [two_mul, ← hL] at hAl hBl
  -- the transforms
  have hem : e * 2 ^ (k₂ + 1) ≤ 4 * m₁ * m₁ := by
    rw [he]; have := Nat.mul_le_mul_left (4 * m₁) hm₁pos; omega
  obtain ⟨lFA, vFA, cFA⟩ := fft_cost hm₁pos (k₂ + 1) e β A hAl hAv (by rw [hL]; omega) hem
  obtain ⟨lFB, vFB, cFB⟩ := fft_cost hm₁pos (k₂ + 1) e β B hBl hBv (by rw [hL]; omega) hem
  generalize fft m₁ e A = FA at lFA vFA cFA ⊢
  generalize fft m₁ e B = FB at lFB vFB cFB ⊢
  rw [lFA, lFB, min_self]
  -- the `2r` products of half size
  have cP := sum_zipWith_le (fun a b ↦ costOf school (nussbaumer k₁ a b))
    (s := m₁ * (2 * k₁ ^ 2 + 1) * (8 * (γ + 72) ^ 2)) FA FB fun u hu v hv ↦
      ih k₁ hk1lt (β + (k₂ + 1)) γ u v (vFA u hu).1 (vFB v hv).1 (vFA u hu).2 (vFB v hv).2
        (by omega)
  have vP : ∀ v ∈ List.zipWith (nussbaumer k₁) FA FB,
      v.length = m₁ ∧ Bdd (2 * (β + k₂ + 1) + k₁) v := by
    intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_zipWith' hv
    rw [nussbaumer_eq_ncSchool (vFA u hu).1 (vFB w hw).1]
    exact ⟨length_ncSchool _ _ _, by
      simpa [add_assoc] using bdd_ncSchool (vFA u hu).1 (vFA u hu).2 (vFB w hw).2⟩
  have lP : (List.zipWith (nussbaumer k₁) FA FB).length = 2 ^ (k₂ + 1) := by simp [lFA, lFB]
  generalize List.zipWith (nussbaumer k₁) FA FB = P at vP lP ⊢
  -- the inverse transform
  obtain ⟨lC, vC, cC⟩ := fft_cost hm₁pos (k₂ + 1) (2 * m₁ - e) _ P lP vP (by rw [hL]; omega)
    (by have h₁ := Nat.mul_le_mul_right (2 ^ (k₂ + 1)) (show 2 * m₁ - e ≤ 2 * m₁ by omega)
        have := Nat.mul_le_mul_left m₁ hrm₁
        rw [hL] at h₁ ⊢; linarith)
  generalize fft m₁ (2 * m₁ - e) P = Cf at lC vC cC ⊢
  rw [lC]
  have lCd : (Cf.map fun v ↦ v.map (· / 2 ^ (k₂ + 1))).length = 2 ^ (k₂ + 1) := by simp [lC]
  have vCd : ∀ j, ((Cf.map fun v ↦ v.map (· / 2 ^ (k₂ + 1))).getD j (List.replicate m₁ 0)).length
      = m₁ ∧ Bdd (2 * (β + k₂ + 1) + k₁ + (k₂ + 1))
        ((Cf.map fun v ↦ v.map (· / 2 ^ (k₂ + 1))).getD j (List.replicate m₁ 0)) := by
    intro j
    rw [List.getD_eq_getElem?_getD]
    cases hj : (Cf.map fun v ↦ v.map (· / 2 ^ (k₂ + 1)))[j]? with
    | none => exact ⟨by simp, bdd_replicate_zero _ _⟩
    | some w =>
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hj)
      refine ⟨by simp [(vC v hv).1], fun x hx ↦ ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt ((vC v hv).2 y hy)
  -- the exact division, before `C` is generalized
  set G := γ + 72 with hG
  set β₂ := 2 * (β + k₂ + 1) + k₁
  have hβ₂ : β₂ + (k₂ + 1) + 70 ≤ 2 * G := by omega
  have hz : ((2 : ℤ) ^ (k₂ + 1)).natAbs.size = k₂ + 2 := by
    rw [Int.natAbs_pow]; simp [Nat.size_pow]
  have cMap : (List.map (fun a => a.length + 1 + (List.map (fun a => max k₂.size 1 + 1 +
      ((2 ^ (k₂ + 1)).size + 1 + (max a.natAbs.size ((2 : ℤ) ^ (k₂ + 1)).natAbs.size + 1))) a).sum)
      Cf).sum ≤ 2 ^ (k₂ + 1) * (m₁ * (3 * G) + 1) := by
    have := sum_map_le_length_mul Cf (fun a => a.length + 1 + (List.map (fun a => max k₂.size 1 + 1 +
      ((2 ^ (k₂ + 1)).size + 1 + (max a.natAbs.size ((2 : ℤ) ^ (k₂ + 1)).natAbs.size + 1))) a).sum)
      (s := m₁ * (3 * G) + 1) fun v hv ↦ by
        have hin := sum_map_le_length_mul v (fun a : ℤ => max k₂.size 1 + 1 +
          ((2 ^ (k₂ + 1)).size + 1 + (max a.natAbs.size ((2 : ℤ) ^ (k₂ + 1)).natAbs.size + 1)))
          (s := 3 * G - 1) fun x hx ↦ by
            have := Nat.size_le.2 ((vC v hv).2 x hx)
            rw [hz, Nat.size_pow]; omega
        rw [(vC v hv).1] at hin ⊢
        have : m₁ * (3 * G - 1) + m₁ + 1 = m₁ * (3 * G) + 1 := by
          rw [Nat.mul_sub, mul_one]; have : m₁ ≤ m₁ * (3 * G) := Nat.le_mul_of_pos_right _ (by omega)
          omega
        omega
    rwa [lC] at this
  generalize Cf.map (fun v ↦ v.map (· / 2 ^ (k₂ + 1))) = C at vCd lCd ⊢
  rw [lCd]
  -- the folding
  have hk₂r : (k₂ + 1) ≤ G := by omega
  have cD : (List.map (fun a => min a (2 ^ (k₂ + 1)) + 1 + (m₁.size + 1 + (r.size + 1 +
      (max a.size r.size + 1 + (min (a + r) (2 ^ (k₂ + 1)) + 1 +
        (costOf school (rot m₁ 1 (C.getD (a + r) (List.replicate m₁ 0))) +
          costOf school (vadd (C.getD a (List.replicate m₁ 0))
            (rot m₁ 1 (C.getD (a + r) (List.replicate m₁ 0)))))))))) (List.range r)).sum ≤
      r * (m₁ * (5 * G)) := by
    have := sum_map_le_length_mul (List.range r) (fun a => min a (2 ^ (k₂ + 1)) + 1 + (m₁.size + 1 +
      (r.size + 1 + (max a.size r.size + 1 + (min (a + r) (2 ^ (k₂ + 1)) + 1 +
        (costOf school (rot m₁ 1 (C.getD (a + r) (List.replicate m₁ 0))) +
          costOf school (vadd (C.getD a (List.replicate m₁ 0))
            (rot m₁ 1 (C.getD (a + r) (List.replicate m₁ 0)))))))))) (s := m₁ * (5 * G))
      fun j hj ↦ by
        have hj := List.mem_range.1 hj
        have h₁ := rot_cost_le (vCd (j + r)).1 (show 1 < 2 * m₁ by omega)
        have h₂ := vadd_cost_le (vCd j).2 (bdd_rot (m := m₁) (j := 1) (vCd (j + r)).2)
          (by rw [(vCd j).1, length_rot (vCd (j + r)).1 (by omega)])
        rw [(vCd j).1] at h₂
        have hjs : j.size ≤ k₂ := Nat.size_le.2 hj
        have hm₁s : m₁.size = k₁ + 1 := by rw [hm₁, Nat.size_pow]
        have hrs : r.size = k₂ + 1 := by rw [hr, Nat.size_pow]
        rw [hm₁s, hrs]
        have u₁ : max j.size (k₂ + 1) ≤ k₂ + 1 := by omega
        have u₂ : min j (2 ^ (k₂ + 1)) ≤ r := by omega
        have u₃ : min (j + r) (2 ^ (k₂ + 1)) ≤ 2 * r := by omega
        have t₁ : m₁ * (β₂ + (k₂ + 1) + 2) ≤ m₁ * (2 * G) :=
          Nat.mul_le_mul_left _ (by omega)
        have a₁ : k₁ + 2 * k₂ + 22 ≤ G := by omega
        have a₂ : G ≤ G * m₁ := Nat.le_mul_of_pos_right _ (by omega)
        have a₃ : 10 * m₁ ≤ 2 * G * m₁ := Nat.mul_le_mul_right _ (by omega)
        have a₄ : r ≤ m₁ := hrm₁
        clear * - h₁ h₂ t₁ u₁ u₂ u₃ a₁ a₂ a₃ a₄
        linarith
    simpa using this
  have lD : (List.map (fun j ↦ vadd (C.getD j (List.replicate m₁ 0))
      (rot m₁ 1 (C.getD (j + r) (List.replicate m₁ 0)))) (List.range r)).length = r := by simp
  have vD : ∀ v ∈ List.map (fun j ↦ vadd (C.getD j (List.replicate m₁ 0))
      (rot m₁ 1 (C.getD (j + r) (List.replicate m₁ 0)))) (List.range r), v.length = m₁ := by
    intro v hv
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv
    rw [length_vadd (by rw [(vCd j).1, length_rot (vCd (j + r)).1 (by omega)]), (vCd j).1]
  have cU := unblock_cost_le (K := k) hrm lD vD
  -- adding up, in terms of `Y = N G (k₂ + 1)` and the products' `X`
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hG72 : 72 ≤ G := by omega
  have hkG : k + 3 ≤ G := by omega
  set Y := N * G * (k₂ + 1) with hY
  have hNG : N * G ≤ Y := Nat.le_mul_of_pos_right _ (by omega)
  have hN72 : 72 * N ≤ N * G := by have := Nat.mul_le_mul_left N hG72; omega
  have hGN : G ≤ N * G := Nat.le_mul_of_pos_left _ (by omega)
  have hrN : r ≤ N := by rw [← hrm]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hm₁N : m₁ ≤ N := by rw [← hrm]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hH : 2 ^ (k₂ + 1) ≤ 2 * N := by rw [hL]; omega
  have fA : costOf school (fft m₁ e A) ≤ 2 * Y + 10 * N := by
    have e₁ : 2 ^ (k₂ + 1) * ((k₂ + 1) * m₁ * (β + (k₂ + 1) + 70) + 5) =
        2 * N * (k₂ + 1) * (β + (k₂ + 1) + 70) + 5 * 2 ^ (k₂ + 1) := by
      rw [show 2 ^ (k₂ + 1) * ((k₂ + 1) * m₁ * (β + (k₂ + 1) + 70) + 5) =
        2 ^ (k₂ + 1) * m₁ * (k₂ + 1) * (β + (k₂ + 1) + 70) + 5 * 2 ^ (k₂ + 1) by ring, hLm]
    have e₂ : 2 * N * (k₂ + 1) * (β + (k₂ + 1) + 70) ≤ 2 * N * (k₂ + 1) * G :=
      Nat.mul_le_mul_left _ (by omega)
    have e₃ : 2 * N * (k₂ + 1) * G = 2 * Y := by rw [hY]; ring
    linarith
  have fB : costOf school (fft m₁ e B) ≤ 2 * Y + 10 * N := by
    have e₁ : 2 ^ (k₂ + 1) * ((k₂ + 1) * m₁ * (β + (k₂ + 1) + 70) + 5) =
        2 * N * (k₂ + 1) * (β + (k₂ + 1) + 70) + 5 * 2 ^ (k₂ + 1) := by
      rw [show 2 ^ (k₂ + 1) * ((k₂ + 1) * m₁ * (β + (k₂ + 1) + 70) + 5) =
        2 ^ (k₂ + 1) * m₁ * (k₂ + 1) * (β + (k₂ + 1) + 70) + 5 * 2 ^ (k₂ + 1) by ring, hLm]
    have e₂ : 2 * N * (k₂ + 1) * (β + (k₂ + 1) + 70) ≤ 2 * N * (k₂ + 1) * G :=
      Nat.mul_le_mul_left _ (by omega)
    have e₃ : 2 * N * (k₂ + 1) * G = 2 * Y := by rw [hY]; ring
    linarith
  have fC : costOf school (fft m₁ (2 * m₁ - e) P) ≤ 4 * Y + 10 * N := by
    have e₁ : 2 ^ (k₂ + 1) * ((k₂ + 1) * m₁ * (β₂ + (k₂ + 1) + 70) + 5) =
        2 * N * (k₂ + 1) * (β₂ + (k₂ + 1) + 70) + 5 * 2 ^ (k₂ + 1) := by
      rw [show 2 ^ (k₂ + 1) * ((k₂ + 1) * m₁ * (β₂ + (k₂ + 1) + 70) + 5) =
        2 ^ (k₂ + 1) * m₁ * (k₂ + 1) * (β₂ + (k₂ + 1) + 70) + 5 * 2 ^ (k₂ + 1) by ring, hLm]
    have e₂ : 2 * N * (k₂ + 1) * (β₂ + (k₂ + 1) + 70) ≤ 2 * N * (k₂ + 1) * (2 * G) :=
      Nat.mul_le_mul_left _ hβ₂
    have e₃ : 2 * N * (k₂ + 1) * (2 * G) = 4 * Y := by rw [hY]; ring
    linarith
  have fP : (List.zipWith (fun a b => costOf school (nussbaumer k₁ a b)) FA FB).sum ≤
      2 * (N * (2 * k₁ ^ 2 + 1) * (8 * G ^ 2)) := by
    rw [lFA] at cP
    refine cP.trans (le_of_eq ?_)
    rw [show 2 ^ (k₂ + 1) * (m₁ * (2 * k₁ ^ 2 + 1) * (8 * G ^ 2)) =
      2 ^ (k₂ + 1) * m₁ * ((2 * k₁ ^ 2 + 1) * (8 * G ^ 2)) by ring, hLm]; ring
  have fM : (List.map (fun a => a.length + 1 + (List.map (fun a => max k₂.size 1 + 1 +
      ((2 ^ (k₂ + 1)).size + 1 + (max a.natAbs.size ((2 : ℤ) ^ (k₂ + 1)).natAbs.size + 1))) a).sum)
      Cf).sum ≤ 6 * (N * G) + 2 * N := by
    have : 2 ^ (k₂ + 1) * (m₁ * (3 * G) + 1) = 3 * G * (2 ^ (k₂ + 1) * m₁) + 2 ^ (k₂ + 1) := by
      ring
    rw [this, hLm] at cMap; linarith
  have fD := cD
  rw [show r * (m₁ * (5 * G)) = r * m₁ * (5 * G) by ring, hrm] at fD
  rw [← hN] at cBa cBb cU
  have fBa : costOf school (blocks r m₁ a) ≤ 2 * Y + N * G + 4 := by
    have : N * ((k + 1) ^ 2 + k + 9) ≤ N * ((k + 1) * G) + N * G := by
      have : (k + 1) ^ 2 ≤ (k + 1) * G := by rw [sq]; exact Nat.mul_le_mul_left _ (by omega)
      have : N * (k + 1) ^ 2 ≤ N * ((k + 1) * G) := Nat.mul_le_mul_left _ this
      have : N * (k + 9) ≤ N * G := Nat.mul_le_mul_left _ (by omega)
      rw [show N * ((k + 1) ^ 2 + k + 9) = N * (k + 1) ^ 2 + N * (k + 9) by ring]
      omega
    have : N * ((k + 1) * G) ≤ 2 * Y := by
      rw [hY, show N * ((k + 1) * G) = N * G * (k + 1) by ring]
      have := Nat.mul_le_mul_left (N * G) (show k + 1 ≤ 2 * (k₂ + 1) by omega)
      rw [show N * G * (2 * (k₂ + 1)) = 2 * (N * G * (k₂ + 1)) by ring] at this; omega
    omega
  have fBb : costOf school (blocks r m₁ b) ≤ 2 * Y + N * G + 4 := by
    have : N * ((k + 1) ^ 2 + k + 9) ≤ N * ((k + 1) * G) + N * G := by
      have : (k + 1) ^ 2 ≤ (k + 1) * G := by rw [sq]; exact Nat.mul_le_mul_left _ (by omega)
      have : N * (k + 1) ^ 2 ≤ N * ((k + 1) * G) := Nat.mul_le_mul_left _ this
      have : N * (k + 9) ≤ N * G := Nat.mul_le_mul_left _ (by omega)
      rw [show N * ((k + 1) ^ 2 + k + 9) = N * (k + 1) ^ 2 + N * (k + 9) by ring]
      omega
    have : N * ((k + 1) * G) ≤ 2 * Y := by
      rw [hY, show N * ((k + 1) * G) = N * G * (k + 1) by ring]
      have := Nat.mul_le_mul_left (N * G) (show k + 1 ≤ 2 * (k₂ + 1) by omega)
      rw [show N * G * (2 * (k₂ + 1)) = 2 * (N * G * (k₂ + 1)) by ring] at this; omega
    omega
  have fU : costOf school (unblock r N (List.map (fun j ↦ vadd (C.getD j (List.replicate m₁ 0))
      (rot m₁ 1 (C.getD (j + r) (List.replicate m₁ 0)))) (List.range r))) ≤ 4 * Y + N * G + 5 := by
    have : N * (2 * (k + 1) ^ 2 + 8) ≤ 2 * (N * ((k + 1) * G)) + N * G := by
      have : (k + 1) ^ 2 ≤ (k + 1) * G := by rw [sq]; exact Nat.mul_le_mul_left _ (by omega)
      have : N * (k + 1) ^ 2 ≤ N * ((k + 1) * G) := Nat.mul_le_mul_left _ this
      have : N * 8 ≤ N * G := Nat.mul_le_mul_left _ (by omega)
      rw [show N * (2 * (k + 1) ^ 2 + 8) = 2 * (N * (k + 1) ^ 2) + N * 8 by ring]
      omega
    have : N * ((k + 1) * G) ≤ 2 * Y := by
      rw [hY, show N * ((k + 1) * G) = N * G * (k + 1) by ring]
      have := Nat.mul_le_mul_left (N * G) (show k + 1 ≤ 2 * (k₂ + 1) by omega)
      rw [show N * G * (2 * (k₂ + 1)) = 2 * (N * G * (k₂ + 1)) by ring] at this; omega
    omega
  have step := nussbaumer_cost_step (N := N) (G := G)
    (or_iff_not_imp_left.2 fun h ↦ by omega : k₁ = k₂ ∨ k₁ = k₂ + 1) hk₂1 hG72
  rw [← hkk] at step
  -- the small charges
  have hm₁s : m₁.size = k₁ + 1 := by rw [hm₁, Nat.size_pow]
  have hrs : r.size = k₂ + 1 := by rw [hr, Nat.size_pow]
  have hNs : N.size = k + 1 := by rw [hN, Nat.size_pow]
  have hes' : e.size ≤ k₁ + 2 := by
    have := Nat.size_le_size hes; rwa [h2s] at this
  rw [hm₁s, hrs, hNs, h2s, show Nat.size 2 = 2 by decide, List.length_range]
  rw [hm₁s, hrs] at fD
  have v₁ : min k.size 2 ≤ 2 := min_le_right _ _
  have v₂ : max k.size 1 ≤ k := by omega
  have v₃ : max (k + 1).size 2 ≤ k + 1 := by omega
  have v₄ : max k.size 2 ≤ k := by omega
  have v₅ : max k₁.size k₂.size ≤ k := by omega
  have v₆ : max 2 (k₁ + 1) ≤ k + 1 := by omega
  have v₇ : max (k₁ + 2) e.size ≤ k + 1 := by omega
  clear_value Y G β₂ m₁ r N
  linarith only [fA, fB, fC, fP, fM, fD, fBa, fBb, fU, step, v₁, v₂, v₃, v₄, v₅, v₆, v₇, hes',
    hrN, hm₁N, hN1, hNG, hN72, hGN, hH, hkG, hk₁s, hk₂s, hks, hk1s, hrm₁, hr1, hm₁pos, hY, hG72, hkk, hle, hk₂1]

theorem ofBits_bound : ∀ l : List ℤ, (∀ d ∈ l, 0 ≤ d ∧ d ≤ 1) →
    0 ≤ ofBits l ∧ ofBits l < 2 ^ l.length
  | [], _ => by simp [ofBits]
  | d :: l, h => by
    obtain ⟨h1, h2⟩ := ofBits_bound l fun x hx ↦ h x (by simp [hx])
    have := h d (by simp)
    change 0 ≤ d + 2 * ofBits l ∧ d + 2 * ofBits l < 2 ^ (l.length + 1)
    rw [pow_succ]; omega

theorem bdd_bitsOf : ∀ m x, Bdd 1 (bitsOf m x)
  | 0, _ => by simp [Bdd, bitsOf]
  | m + 1, x => fun d hd ↦ by
    simp only [bitsOf, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact bdd_bitsOf m (x / 2) d hd

theorem length_carry : ∀ (c : ℤ) (ds : List ℤ), (carry c ds).1.length = ds.length
  | _, [] => rfl
  | c, d :: ds => by simp [carry, length_carry _ ds]

/-- Carry propagation over digits below `2^D` keeps the carry at most `2^D`, produces binary
digits, and costs `3D + 10` bit operations per digit. -/
theorem carry_cost {D : ℕ} : ∀ (c : ℤ) (ds : List ℤ), c.natAbs ≤ 2 ^ D → Bdd D ds →
    (∀ d ∈ (carry c ds).1, 0 ≤ d ∧ d ≤ 1) ∧ (carry c ds).2.natAbs ≤ 2 ^ D ∧
      costOf school (carry c ds) ≤ ds.length * (3 * D + 10) + 1
  | c, [], hc, _ => by
    refine ⟨by simp [carry], by simpa [carry] using hc, ?_⟩
    cost_unfold carry.counted
  | c, d :: ds, hc, hds => by
    have hd := hds d (by simp)
    have hc' : ((c + d) / 2).natAbs ≤ 2 ^ D := by
      have := Int.natAbs_add_le c d
      have : ((c + d) / 2).natAbs ≤ ((c + d).natAbs + 1) / 2 := by omega
      cost_bound
    obtain ⟨h1, h2, h3⟩ := carry_cost ((c + d) / 2) ds hc' fun x hx ↦ hds x (by simp [hx])
    refine ⟨fun x hx ↦ ?_, by simpa [carry] using h2, ?_⟩
    · simp only [carry, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact h1 x hx
    · cost_unfold carry.counted
      have := Nat.size_le.2 hd
      have : c.natAbs.size ≤ D + 1 := Nat.size_le.2 (by rw [pow_succ]; omega)
      have : (c + d).natAbs.size ≤ D + 2 := Nat.size_le.2 (by
        have := Int.natAbs_add_le c d; rw [pow_succ, pow_succ]; omega)
      have : (Int.natAbs 2).size = 2 := by decide
      rw [add_mul, one_mul]
      omega

/-- The digits of `x < 2^{2^k}` by halving: `2^k (18k + 8)` bit operations. -/
theorem bitsOfPow2_cost_le : ∀ (k x : ℕ), x < 2 ^ 2 ^ k →
    costOf school (bitsOfPow2 k x) ≤ 2 ^ k * (18 * k + 8)
  | 0, x, hx => by
    cost_unfold bitsOfPow2.counted
    rw [show Nat.size 2 = 2 by decide]
    cost_bound
  | k + 1, x, hx => by
    have h₁ := bitsOfPow2_cost_le k (x % 2 ^ 2 ^ k) (Nat.mod_lt x (Nat.two_pow_pos (2 ^ k)))
    have h₂ := bitsOfPow2_cost_le k (x >>> 2 ^ k) (by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact hx.trans_le (Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ]; omega)))
    have hxs : x.size ≤ 2 ^ (k + 1) := Nat.size_le.2 hx
    have hlen : (bitsOfPow2 k (x % 2 ^ 2 ^ k)).length = 2 ^ k := by
      rw [bitsOfPow2_eq, length_bitsOf]
    have hk2 : k + 2 ≤ 2 ^ (k + 1) := by
      have := Nat.lt_two_pow_self (n := k + 1); omega
    cost_unfold bitsOfPow2.counted
    rw [Nat.size_pow, Nat.size_pow, hlen]
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have : max x.size (2 ^ k + 1) ≤ 2 * 2 ^ k + 1 := by omega
    have : max x.size (k + 1) ≤ 2 * 2 ^ k + 1 := by omega
    nlinarith

/-- Reading off `2^k` binary digits by halving: `2^k (20k + 16)` bit operations. -/
@[cost_le] theorem ofBitsNat_cost_le : ∀ (k : ℕ) (l : List ℤ), l.length = 2 ^ k → (∀ d ∈ l, 0 ≤ d ∧ d ≤ 1) →
    costOf school (ofBitsNat l) ≤ 2 ^ k * (20 * k + 16)
  | 0, l, hl, hd => by
    obtain ⟨d, rfl⟩ : ∃ d, l = [d] := by
      match l, hl with
      | [d], _ => exact ⟨d, rfl⟩
    have := hd d (by simp)
    have : d.natAbs.size ≤ 1 := Nat.size_le.2 (by omega)
    cost_unfold ofBitsNat.counted
    simp
    cost_bound
  | k + 1, l, hl, hd => by
    have hh : l.length / 2 = 2 ^ k := by rw [hl, pow_succ]; omega
    have hdrop : (l.drop (2 ^ k)).length = 2 ^ k := by
      rw [List.length_drop, hl, pow_succ]; omega
    have htake : (l.take (2 ^ k)).length = 2 ^ k := by
      rw [List.length_take, hl]; simp [pow_succ]
    have hd₁ : ∀ d ∈ l.drop (2 ^ k), 0 ≤ d ∧ d ≤ 1 := fun d h ↦ hd d (List.mem_of_mem_drop h)
    have hd₂ : ∀ d ∈ l.take (2 ^ k), 0 ≤ d ∧ d ≤ 1 := fun d h ↦ hd d (List.mem_of_mem_take h)
    have h₁ := ofBitsNat_cost_le k _ hdrop hd₁
    have h₂ := ofBitsNat_cost_le k _ htake hd₂
    have hb : ∀ l' : List ℤ, (∀ d ∈ l', 0 ≤ d ∧ d ≤ 1) → ofBitsNat l' < 2 ^ l'.length :=
      fun l' h' ↦ by
        have := ofBits_bound l' h'; rw [← ofBitsNat_eq l' h'] at this; exact_mod_cast this.2
    have b₁ := hb _ hd₁
    have b₂ := hb _ hd₂
    rw [hdrop] at b₁; rw [htake] at b₂
    have hsh : (ofBitsNat (l.drop (2 ^ k)) <<< 2 ^ k).size ≤ 2 ^ (k + 1) := by
      rw [Nat.shiftLeft_eq]
      refine Nat.size_le.2 ?_
      calc ofBitsNat (l.drop (2 ^ k)) * 2 ^ 2 ^ k < 2 ^ 2 ^ k * 2 ^ 2 ^ k :=
            Nat.mul_lt_mul_of_pos_right b₁ (by positivity)
        _ = 2 ^ 2 ^ (k + 1) := by rw [← pow_add]; congr 1; rw [pow_succ]; ring
    have hs₁ : (ofBitsNat (l.drop (2 ^ k))).size ≤ 2 ^ k := Nat.size_le.2 b₁
    have hs₂ : (ofBitsNat (l.take (2 ^ k))).size ≤ 2 ^ k := Nat.size_le.2 b₂
    have hls : l.length.size ≤ k + 2 := by rw [hl, Nat.size_pow]
    have hk : k + 2 ≤ 2 ^ (k + 1) := by have := Nat.lt_two_pow_self (n := k + 1); omega
    cost_unfold ofBitsNat.counted
    simp only [show Nat.size 2 = 2 by decide]
    rw [hh, Nat.size_pow]
    rw [hl] at hls ⊢
    have e₁ : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have w₁ : min (2 ^ (k + 1)).size 1 ≤ 1 := min_le_right _ _
    have w₂ : max (2 ^ (k + 1)).size 2 ≤ k + 2 := by omega
    have w₃ : min (2 ^ k) (2 ^ (k + 1)) ≤ 2 ^ k := min_le_left _ _
    have w₄ : max (ofBitsNat (l.drop (2 ^ k))).size (k + 1) ≤ 2 * 2 ^ k := by omega
    have w₅ : max (ofBitsNat (l.drop (2 ^ k)) <<< 2 ^ k).size (ofBitsNat (l.take (2 ^ k))).size ≤
        2 * 2 ^ k := by omega
    nlinarith

@[cost_le] theorem mulLog_cost_le (x y : ℕ) : costOf school (mulLog x y) ≤ 6 * max x.size y.size + 9 := by
  have := (size_le_self (2 * max x.size y.size))
  cost_unfold mulLog.counted
  rw [show Nat.size 2 = 2 by decide]
  cost_bound

set_option maxHeartbeats 1000000 in
-- the unfolded cost of `nussMul` is a long sum of charges
/-- **Running time of Nussbaumer multiplication**, in terms of the transform exponent
`k = mulLog x y`. -/
@[cost_le] theorem nussMul_cost_le_mulLog (x y : ℕ) :
    costOf school (nussMul x y) ≤ 2 ^ mulLog x y * (90000 * (mulLog x y + 1) ^ 4) := by
  by_cases h0 : x = 0 ∨ y = 0
  · cost_unfold nussMul.counted
    have := Nat.one_le_two_pow (n := mulLog x y)
    have := Nat.one_le_pow 4 (mulLog x y + 1) (by omega)
    split_ifs <;> nlinarith
  have hM := Nat.lt_size_self (2 * max x.size y.size)
  have hx : x < 2 ^ max x.size y.size :=
    (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right two_pos (le_max_left _ _))
  have hy : y < 2 ^ max x.size y.size :=
    (Nat.lt_size_self y).trans_le (Nat.pow_le_pow_right two_pos (le_max_right _ _))
  have hml : mulLog x y = (2 * max x.size y.size).size := rfl
  have hN1 : 1 ≤ max x.size y.size := by
    simp only [not_or] at h0
    have := Nat.size_pos.2 (Nat.pos_of_ne_zero h0.1); omega
  have hMK : 2 * max x.size y.size < 2 ^ mulLog x y := by rw [hml]; exact hM
  have hK2 : 2 ≤ mulLog x y := by
    have := Nat.size_le_size (show 2 ≤ 2 * max x.size y.size by omega)
    rw [show Nat.size 2 = 2 by decide, ← hml] at this; exact this
  have hxK : x < 2 ^ 2 ^ mulLog x y := hx.trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have hyK : y < 2 ^ 2 ^ mulLog x y := hy.trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have cL := mulLog_cost_le x y
  have cX := bitsOfPow2_cost_le _ x hxK
  have cY := bitsOfPow2_cost_le _ y hyK
  cost_unfold nussMul.counted
  simp only [bitsOfPow2_eq] at cX cY ⊢
  generalize mulLog x y = k at *
  have hA := length_bitsOf (2 ^ k) x
  have hB := length_bitsOf (2 ^ k) y
  have cN := nussbaumer_cost k 1 (1 + 2 * k) _ _ hA hB (bdd_bitsOf _ _) (bdd_bitsOf _ _) le_rfl
  have vN : Bdd (k + 2) (nussbaumer k (bitsOf (2 ^ k) x) (bitsOf (2 ^ k) y)) := by
    rw [nussbaumer_eq_ncSchool hA hB]
    simpa [add_comm] using bdd_ncSchool hA (bdd_bitsOf _ _) (bdd_bitsOf _ _)
  have lN := (nussbaumer_spec k _ _ hA hB).1
  obtain ⟨d1, d2, cC⟩ := carry_cost (D := k + 2) 0 _ (by simp) vN
  have lr := length_carry 0 (nussbaumer k (bitsOf (2 ^ k) x) (bitsOf (2 ^ k) y))
  rw [lN] at cC lr
  have cO := ofBitsNat_cost_le k _ lr d1
  have hO := ofBits_bound _ d1
  generalize carry 0 (nussbaumer k (bitsOf (2 ^ k) x) (bitsOf (2 ^ k) y)) = r at d1 d2 hO lr cC cO ⊢
  rw [lr] at hO
  have s1 : (ofBitsNat r.1).size ≤ 2 ^ k := Nat.size_le.2 (by
    have := ofBitsNat_eq r.1 d1; have : (ofBitsNat r.1 : ℤ) < 2 ^ 2 ^ k := by rw [this]; exact hO.2
    exact_mod_cast this)
  have s1' : ((ofBitsNat r.1 : ℕ) : ℤ).natAbs.size ≤ 2 ^ k := by simpa using s1
  have s2 : (r.2 * 2 ^ 2 ^ k).natAbs.size ≤ k + 3 + 2 ^ k := Nat.size_le.2 (by
    have e : (r.2 * 2 ^ 2 ^ k).natAbs = r.2.natAbs * 2 ^ 2 ^ k := by
      rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
    rw [e, pow_add]
    refine (Nat.mul_le_mul_right _ d2).trans_lt (Nat.mul_lt_mul_of_pos_right ?_ (Nat.two_pow_pos _))
    exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have s3 : r.2.natAbs.size ≤ k + 3 := Nat.size_le.2 (d2.trans_lt (Nat.pow_lt_pow_right
    (by norm_num) (by omega)))
  have s4 : ((2 : ℤ) ^ 2 ^ k).natAbs.size = 2 ^ k + 1 := by
    rw [Int.natAbs_pow]; simp [Nat.size_pow]
  have hk : k + 2 ≤ 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k - 1)
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have s5 : ((ofBitsNat r.1 : ℕ) + r.2 * 2 ^ 2 ^ k).natAbs.size ≤ 2 ^ k + k + 4 := by
    refine Nat.size_le.2 ?_
    have h₁ := Int.natAbs_add_le ((ofBitsNat r.1 : ℕ) : ℤ) (r.2 * 2 ^ 2 ^ k)
    have h₂ : ((ofBitsNat r.1 : ℕ) : ℤ).natAbs < 2 ^ 2 ^ k := Nat.size_le.1 s1'
    have h₃ : (r.2 * 2 ^ 2 ^ k).natAbs < 2 ^ (k + 3 + 2 ^ k) := Nat.size_le.1 s2
    have : 2 ^ 2 ^ k ≤ 2 ^ (k + 3 + 2 ^ k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show 2 ^ k + k + 4 = (k + 3 + 2 ^ k) + 1 by ring, pow_succ]
    omega
  rw [Nat.size_pow, Nat.size_pow]
  have m₁ : max r.2.natAbs.size ((2 : ℤ) ^ 2 ^ k).natAbs.size ≤ 2 ^ k + 1 := by omega
  have m₂ : max ((ofBitsNat r.1 : ℕ) : ℤ).natAbs.size (r.2 * 2 ^ 2 ^ k).natAbs.size ≤
      2 ^ k + k + 3 := by omega
  have hpoly : (2 * k ^ 2 + 1) * (8 * (1 + 2 * k + 72) ^ 2) ≤ 85264 * (k + 1) ^ 4 := by
    have p₁ : 2 * k ^ 2 + 1 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    have p₂ : (1 + 2 * k + 72) ^ 2 ≤ (73 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    calc (2 * k ^ 2 + 1) * (8 * (1 + 2 * k + 72) ^ 2)
        ≤ (2 * (k + 1) ^ 2) * (8 * (73 * (k + 1)) ^ 2) := Nat.mul_le_mul p₁ (by omega)
      _ = 85264 * (k + 1) ^ 4 := by ring
  have cN' : costOf school (nussbaumer k (bitsOf (2 ^ k) x) (bitsOf (2 ^ k) y)) ≤
      2 ^ k * (85264 * (k + 1) ^ 4) := by
    refine cN.trans ?_
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ hpoly
  have q : 2 ^ k * (59 * k + 90) ≤ 2 ^ k * (4736 * (k + 1) ^ 4) := by
    refine Nat.mul_le_mul_left _ ?_
    have : k + 1 ≤ (k + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
    omega
  have hM2 : 6 * max x.size y.size + 9 ≤ 3 * 2 ^ k + 9 := by omega
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  nlinarith

/-- **Nussbaumer multiplication realizes `nussModel`**: multiplying an `a`-bit by a `b`-bit
number takes at most `nussModel.mul a b` bit operations (for `a` or `b` positive: a product
of two zero-bit numbers still takes the few steps of the call). -/
@[cost_le] theorem nussMul_cost_le {x y a b : ℕ} (hx : x.size ≤ a) (hy : y.size ≤ b) (hab : 1 ≤ max a b) :
    costOf school (nussMul x y) ≤ nussModel.mul a b := by
  by_cases h0 : x = 0 ∨ y = 0
  · cost_unfold nussMul.counted
    split_ifs
    all_goals
      simp only [nussModel_mul]
      have := Nat.one_le_pow 4 ((max a b).size + 3) (by omega)
      have : 360000 * 1 ≤ 360000 * max a b := by omega
      cost_bound
  refine (nussMul_cost_le_mulLog x y).trans ?_
  set N := max x.size y.size
  have hN : 1 ≤ N := by
    simp only [not_or] at h0
    have := Nat.size_pos.2 (Nat.pos_of_ne_zero h0.1); omega
  have hml : mulLog x y = (2 * N).size := rfl
  have hk : mulLog x y ≤ N.size + 2 := by
    have := size_mul_le 2 N
    rw [hml]; rw [show Nat.size 2 = 2 by decide] at this; omega
  have h2k : 2 ^ mulLog x y ≤ 4 * N := by
    have hpos : 0 < mulLog x y := Nat.size_pos.2 (by omega)
    have := Nat.lt_size.1 (show mulLog x y - 1 < (2 * N).size by rw [← hml]; omega)
    calc 2 ^ mulLog x y = 2 * 2 ^ (mulLog x y - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 4 * N := by omega
  have hNM : N ≤ max a b := max_le_max hx hy
  calc 2 ^ mulLog x y * (90000 * (mulLog x y + 1) ^ 4)
      ≤ 4 * N * (90000 * (N.size + 3) ^ 4) :=
        Nat.mul_le_mul h2k (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = 360000 * N * (N.size + 3) ^ 4 := by ring
    _ ≤ nussModel.mul a b := Nat.mul_le_mul (Nat.mul_le_mul_left _ hNM)
        (Nat.pow_le_pow_left (by have := Nat.size_le_size hNM; omega) _)

end PrimeNumbers.Chapter9
