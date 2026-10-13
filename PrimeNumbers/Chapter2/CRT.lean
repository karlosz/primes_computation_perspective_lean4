import PrimeNumbers.Chapter2.Euclid

/-!
# §2.1.3 Chinese remainder theorem

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.1.3.

* `theorem_2_1_6`  — Theorem 2.1.6 (CRT): existence, uniqueness and the explicit formula
                     `n = (∑ nᵢ vᵢ Mᵢ) mod M`.
* `Garner.precompute`, `Garner.reconstruct`, `garner`
                   — Algorithm 2.1.7 (Garner), split into its [Precomputation] step and
                     its [Reentry point]; correctness is `garner_spec`.
-/

namespace PrimeNumbers.Chapter2

open Finset

/-! ## Theorem 2.1.6 (Chinese remainder theorem) -/

section Theorem

variable {r : ℕ} (m n : Fin r → ℕ)

/-- The explicit CRT solution of Theorem 2.1.6: the least nonnegative residue modulo
`M = ∏ mᵢ` of `∑ nᵢ vᵢ Mᵢ`, where `Mᵢ = M / mᵢ` and `vᵢ = Mᵢ⁻¹ mod mᵢ`. -/
def crt : ℕ :=
  let M := ∏ i, m i
  (∑ i, n i * modInv (M / m i) (m i) * (M / m i)) % M

variable {m}

/-- Congruent modulo pairwise coprime moduli implies congruent modulo their product. -/
theorem modEq_prod_of_forall_modEq (hcop : Pairwise fun i j ↦ (m i).Coprime (m j)) {a b : ℕ}
    (h : ∀ i, a ≡ b [MOD m i]) : a ≡ b [MOD ∏ i, m i] := by
  rw [Nat.modEq_iff_dvd]
  push_cast
  refine Fintype.prod_dvd_of_coprime (fun i j hij ↦ ?_) fun i ↦ (Nat.modEq_iff_dvd.mp (h i))
  exact Nat.isCoprime_iff_coprime.mpr (hcop hij)

/-- **Theorem 2.1.6 (Chinese remainder theorem).**  Let `m₀, …, m_{r-1}` be positive,
pairwise coprime moduli with product `M`, and let residues `nᵢ` be given.  Then the system
`n ≡ nᵢ (mod mᵢ)`, `0 ≤ n < M` has a unique solution, and this solution is given
explicitly by `crt m n = (∑ nᵢ vᵢ Mᵢ) mod M`. -/
theorem theorem_2_1_6 (hpos : ∀ i, 0 < m i) (hcop : Pairwise fun i j ↦ (m i).Coprime (m j)) :
    (crt m n < ∏ i, m i ∧ ∀ i, crt m n ≡ n i [MOD m i]) ∧
      ∀ x, x < ∏ i, m i → (∀ i, x ≡ n i [MOD m i]) → x = crt m n := by
  have hM : 0 < ∏ i, m i := prod_pos fun i _ ↦ hpos i
  -- existence: the explicit formula works
  have hsol : ∀ j, crt m n ≡ n j [MOD m j] := by
    intro j
    -- `Mⱼ = M / mⱼ` is the product of the other moduli
    have hMj : ∀ i, (∏ k, m k) / m i = ∏ k ∈ univ.erase i, m k := fun i ↦ by
      rw [← mul_prod_erase univ m (mem_univ i), Nat.mul_div_cancel_left _ (hpos i)]
    have hdvd : m j ∣ ∏ i, m i := dvd_prod_of_mem m (mem_univ j)
    refine ((Nat.mod_modEq _ _).of_dvd hdvd).trans ?_
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [sum_eq_single j]
    · -- the `j`-th term is `nⱼ vⱼ Mⱼ ≡ nⱼ`
      have hcopj : ((∏ k, m k) / m j).Coprime (m j) := by
        rw [hMj]
        exact Nat.Coprime.prod_left fun i hi ↦ hcop (ne_of_mem_erase hi)
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (mul_modInv_modEq hcopj)
      push_cast at this
      rw [mul_assoc, mul_comm (modInv _ _ : ZMod (m j)), this, mul_one]
    · -- every other term is divisible by `mⱼ`
      intro i _ hij
      have : (((∏ k, m k) / m i : ℕ) : ZMod (m j)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, hMj]
        exact dvd_prod_of_mem m (mem_erase.mpr ⟨hij.symm, mem_univ j⟩)
      rw [this, mul_zero]
    · simp
  refine ⟨⟨Nat.mod_lt _ hM, hsol⟩, fun x hx hxsol ↦ ?_⟩
  -- uniqueness
  exact (modEq_prod_of_forall_modEq hcop fun i ↦ (hxsol i).trans (hsol i).symm).eq_of_lt_of_lt hx
    (Nat.mod_lt _ hM)

end Theorem

/-! ## Algorithm 2.1.7 (CRT reconstruction with preconditioning (Garner)) -/

/-- The table built by the [Precomputation] step of Algorithm 2.1.7: for each `i ≥ 1`
the triple `(mᵢ, μᵢ, cᵢ)` with `μᵢ = ∏_{j<i} mⱼ` and `cᵢ = μᵢ⁻¹ mod mᵢ`.
The argument `μ` is the product of the moduli already processed. -/
def garnerTable (μ : ℕ) : List ℕ → List (ℕ × ℕ × ℕ)
  | [] => []
  | m :: ms => (m, μ, modInv μ m) :: garnerTable (μ * m) ms

/-- The data stored after the [Precomputation] step of Algorithm 2.1.7. -/
structure Garner where
  /-- the product `M` of all moduli -/
  M : ℕ
  /-- the triples `(mᵢ, μᵢ, cᵢ)` for `1 ≤ i < r` -/
  table : List (ℕ × ℕ × ℕ)

/-- **Algorithm 2.1.7, step 1 [Precomputation].**
```
for (1 ≤ i < r) { μᵢ = ∏_{j<i} mⱼ;  cᵢ = μᵢ⁻¹ mod mᵢ; }
M = μ_{r-1} m_{r-1};
```
-/
def Garner.precompute : List ℕ → Garner
  | [] => ⟨1, []⟩
  | m₀ :: ms => ⟨(m₀ :: ms).prod, garnerTable m₀ ms⟩

/-- The loop of the [Reentry point] of Algorithm 2.1.7:
```
for (1 ≤ i < r) { u = ((nᵢ - n) cᵢ) mod mᵢ;  n = n + u μᵢ; }
```
-/
def garnerLoop (n : ℕ) : List (ℕ × ℕ × ℕ) → List ℕ → ℕ
  | (m, μ, c) :: table, nᵢ :: ns =>
    let u := (((nᵢ : ℤ) - n) * c % m).toNat
    garnerLoop (n + u * μ) table ns
  | _, _ => n

/-- **Algorithm 2.1.7, step 2 [Reentry point for given input residues `{nᵢ}`].** -/
def Garner.reconstruct (G : Garner) : List ℕ → ℕ
  | [] => 0
  | n₀ :: ns => garnerLoop n₀ G.table ns % G.M

/-- **Algorithm 2.1.7 (Garner)**, both steps: for moduli `ms` and residues `ns` return
the `n ∈ [0, M-1]` with `n ≡ nᵢ (mod mᵢ)`. -/
def garner (ms ns : List ℕ) : ℕ :=
  (Garner.precompute ms).reconstruct ns

/-- One pass through the Garner loop makes `n` correct modulo the new modulus `m` … -/
theorem garner_step_modEq_new {μ m : ℕ} (hm : 0 < m) (hcop : μ.Coprime m) (n nᵢ : ℕ) :
    n + (((nᵢ : ℤ) - n) * modInv μ m % m).toNat * μ ≡ nᵢ [MOD m] := by
  have hc : (modInv μ m : ℤ) * μ ≡ 1 [ZMOD m] := by
    have := Int.natCast_modEq_iff.mpr (mul_modInv_modEq hcop)
    push_cast at this
    rwa [mul_comm] at this
  rw [← Int.natCast_modEq_iff]
  push_cast
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  calc (n : ℤ) + ((nᵢ : ℤ) - n) * modInv μ m % m * μ
      ≡ n + ((nᵢ : ℤ) - n) * modInv μ m * μ [ZMOD m] :=
        ((Int.mod_modEq _ _).mul_right _).add_left _
    _ = n + ((nᵢ : ℤ) - n) * (modInv μ m * μ) := by ring
    _ ≡ n + ((nᵢ : ℤ) - n) * 1 [ZMOD m] := (hc.mul_left _).add_left _
    _ = nᵢ := by ring

/-- … and does not change `n` modulo the product `μ` of the earlier moduli. -/
theorem garner_step_modEq_old (μ n u : ℕ) : n + u * μ ≡ n [MOD μ] := by
  simp [Nat.ModEq]

/-- Loop invariant of Algorithm 2.1.7 ("Now `n ≡ nⱼ (mod mⱼ)` for `0 ≤ j ≤ i`"). -/
theorem garnerLoop_spec (μ n : ℕ) (ms ns : List ℕ) (hlen : ms.length = ns.length)
    (hpos : ∀ m ∈ ms, 0 < m) (hμ : ∀ m ∈ ms, μ.Coprime m) (hcop : ms.Pairwise Nat.Coprime) :
    garnerLoop n (garnerTable μ ms) ns ≡ n [MOD μ] ∧
      ∀ i (h : i < ms.length),
        garnerLoop n (garnerTable μ ms) ns ≡ ns[i]'(hlen ▸ h) [MOD ms[i]] := by
  induction ms generalizing μ n ns with
  | nil => simp [garnerTable, garnerLoop, Nat.ModEq.refl]
  | cons m ms ih =>
    obtain _ | ⟨nᵢ, ns⟩ := ns
    · simp at hlen
    have hm : 0 < m := hpos m (by simp)
    have hμm : μ.Coprime m := hμ m (by simp)
    rw [List.pairwise_cons] at hcop
    -- apply the induction hypothesis to the rest of the loop
    obtain ⟨ih₁, ih₂⟩ := ih (μ * m) (n + (((nᵢ : ℤ) - n) * modInv μ m % m).toNat * μ) ns
      (by simpa using hlen) (fun m' hm' ↦ hpos m' (by simp [hm']))
      (fun m' hm' ↦ (hμ m' (by simp [hm'])).mul_left (hcop.1 m' hm')) hcop.2
    simp only [garnerTable, garnerLoop]
    refine ⟨(ih₁.of_mul_right m).trans (garner_step_modEq_old ..), fun i hi ↦ ?_⟩
    obtain _ | i := i
    · exact (ih₁.of_mul_left μ).trans (garner_step_modEq_new hm hμm n nᵢ)
    · exact ih₂ i (by simpa using hi)

/-- **Correctness of Algorithm 2.1.7 (Garner).**  For positive, pairwise coprime moduli
`ms` and residues `ns`, `garner ms ns` is the unique `n ∈ [0, M-1]` with
`n ≡ nᵢ (mod mᵢ)` for all `i`. -/
theorem garner_spec (ms ns : List ℕ) (hlen : ms.length = ns.length) (hpos : ∀ m ∈ ms, 0 < m)
    (hcop : ms.Pairwise Nat.Coprime) :
    garner ms ns < ms.prod ∧
      ∀ i (h : i < ms.length), garner ms ns ≡ ns[i]'(hlen ▸ h) [MOD ms[i]] := by
  obtain _ | ⟨m₀, ms⟩ := ms
  · obtain rfl : ns = [] := by simpa using hlen.symm
    simp [garner, Garner.reconstruct]
  obtain _ | ⟨n₀, ns⟩ := ns
  · simp at hlen
  have hM : 0 < (m₀ :: ms).prod := List.prod_pos (by simpa using hpos)
  rw [List.pairwise_cons] at hcop
  obtain ⟨h₁, h₂⟩ := garnerLoop_spec m₀ n₀ ms ns (by simpa using hlen)
    (fun m hm ↦ hpos m (by simp [hm])) hcop.1 hcop.2
  refine ⟨Nat.mod_lt _ hM, fun i hi ↦ ?_⟩
  -- the final reduction `n mod M` does not change `n` modulo any `mᵢ`
  have hdvd : (m₀ :: ms)[i] ∣ (m₀ :: ms).prod := List.dvd_prod (List.getElem_mem hi)
  refine ((Nat.mod_modEq _ _).of_dvd hdvd).trans ?_
  obtain _ | i := i
  · exact h₁
  · exact h₂ i (by simpa using hi)

end PrimeNumbers.Chapter2
