import HubRemoval.Giant
open HubRemoval Finset Filter Topology
open scoped symmDiff

/-! ### Eq. (3) and Corollary 1.5: axioms -/

#print axioms rate_cases
#print axioms gap_le_of_good
#print axioms mem_sccOf
#print axioms sccOf_conn
#print axioms card_sccOf_le
#print axioms exists_largest_scc
#print axioms exists_star
#print axioms secondSCC_le_PhiK
#print axioms sccOf_subset_or_card_le
#print axioms sigmaSet_mutual
#print axioms sigmaSet_closed
#print axioms sigmaSet_subset
#print axioms card_sigmaSet_le
#print axioms sccOf_eq_or_disjoint
#print axioms card_sccOf_le_of_ne
#print axioms giant_pointwise
#print axioms eq_4_2_core
#print axioms eq_4_2
#print axioms prob_ge_le
#print axioms expect_abs_eq_gap
#print axioms cor_structure
#print axioms cor_structure_prob
#print axioms cor_structure_whp

/-! ### Eq. (3) at the parameters of `Checks/CoreParamsCheck.lean`

`N = 2¹⁶`, `K = 10`, `s₀ = 1`, `η = 1/2`, `δ = 1/16`, `ρ = 1/2`. -/

theorem N_rpow (a : ℝ) : (65536 : ℝ) ^ a = (2 : ℝ) ^ (16 * a) := by
  rw [Real.rpow_mul (by norm_num), show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

theorem two_rpow_nat (n : ℕ) : (2 : ℝ) ^ (n : ℝ) = 2 ^ n := Real.rpow_natCast 2 n

theorem hyp : CoreHyp 65536 10 1 (1 / 2) (1 / 16) where
  η_pos := by norm_num
  η_lt_one := by norm_num
  s₀_pos := le_rfl
  δ_pos := by norm_num
  δ_le := by norm_num
  H1 := by
    push_cast
    rw [N_rpow, show 16 * (1 - 1 / 2 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  H2 := by
    push_cast
    rw [N_rpow, show 16 * (1 / 2 / 4 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  H3 := by
    push_cast
    rw [N_rpow, show 16 * (1 / 16 / 1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num

/-- `E[|F₁ \ Σ| · 1_𝓡] ≤ Err` in `𝒟_{1/2}(2¹⁶, 10)`, with `M = N^{1−2δ} = 2¹⁴`. -/
example := eq_4_2 hyp (ρ := 1 / 2) (by norm_num) (by norm_num)

/-- The same with `|F₁ \ 𝒰|` in place of its bound from Lemma 4.5(d). -/
example := eq_4_2_core hyp (ρ := 1 / 2) (by norm_num) (by norm_num)

/-! ### SCCs -/

/-- A largest SCC exists, so rules choosing one exist (here in `𝒟(10, 3)`). -/
example : ∃ star : (Edge 10 3 → Bool) → Finset ℕ,
    ∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK 10 3 ω :=
  exists_star (by norm_num)

/-! ### Corollary 1.5, applied (`ρ = 1/2`) -/

/-- (a)–(c) for every rule. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K < N, ∀ star : (Edge N K → Bool) → Finset ℕ,
    (∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK N K ω) →
    expectP (1 / 2) (fun ω : Edge N K → Bool => |(PhiK N K ω : ℝ) - psi N (N / (K + 1))|) ≤
        30 * N / Real.log (Real.log N) ∧
    expectP (1 / 2) (fun ω : Edge N K → Bool => ((smoothFibre N K ∆ star ω).card : ℝ)) ≤
        2 * K + 30 * N / Real.log (Real.log N) ∧
    expectP (1 / 2) (fun ω : Edge N K → Bool => (secondSCC ω (star ω) : ℝ)) ≤
        K + 30 * N / Real.log (Real.log N) :=
  cor_structure (by norm_num) (by norm_num)

/-- With a concrete rule from `exists_star`: the hypotheses of (b), (c) can be met. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K < N, ∃ star : (Edge N K → Bool) → Finset ℕ,
    (∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK N K ω) ∧
    expectP (1 / 2) (fun ω : Edge N K → Bool => (secondSCC ω (star ω) : ℝ)) ≤
      K + 30 * N / Real.log (Real.log N) := by
  obtain ⟨N₀, h⟩ := cor_structure (ρ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨N₀, fun N hN K hK => ?_⟩
  obtain ⟨star, hstar⟩ := exists_star hK
  exact ⟨star, hstar, (h N hN K hK star hstar).2.2⟩

/-- (a) in probability: `max_K P(|Φ_K/N − Ψ/N| ≥ 1/100) → 0`. -/
example : Tendsto (fun N : ℕ => ⨆ K : Fin N, prob (1 / 2) (fun ω : Edge N K → Bool =>
    (1 / 100 : ℝ) ≤ |(PhiK N K ω : ℝ) / N - (psi N (N / (K + 1)) : ℝ) / N|)) atTop (𝓝 0) :=
  cor_structure_prob (by norm_num) (by norm_num) (by norm_num)

/-- `K = o(N)`, here `K = 0`, with a concrete rule: w.h.p. the giant is `F₁` up to `N/100`
vertices, and every other SCC has fewer than `N/100` vertices. -/
example : ∃ star : ∀ N, (Edge N 0 → Bool) → Finset ℕ,
    Tendsto (fun N : ℕ => prob (1 / 2) (fun ω : Edge N 0 → Bool =>
      (1 / 100 : ℝ) * N ≤ ((smoothFibre N 0 ∆ star N ω).card : ℝ))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => prob (1 / 2) (fun ω : Edge N 0 → Bool =>
      (1 / 100 : ℝ) * N ≤ (secondSCC ω (star N ω) : ℝ))) atTop (𝓝 0) := by
  classical
  refine ⟨fun N => if h : 0 < N then (exists_star h).choose else fun _ => ∅, ?_⟩
  exact cor_structure_whp (K := fun _ => 0) (by norm_num) (by norm_num)
    (by simp) _
    (fun N hN ω => by simp only [hN, ↓reduceDIte]; exact (exists_star hN).choose_spec ω)
    (by norm_num)

/-- Markov's inequality on two fair coins: `P(both heads) ≤ E[#heads]/2`. -/
example : prob (1 / 2) (fun ω : Fin 2 → Bool =>
      (2 : ℝ) ≤ (if ω 0 then 1 else 0) + (if ω 1 then 1 else 0)) ≤
    expectP (1 / 2) (fun ω : Fin 2 → Bool => (if ω 0 then (1 : ℝ) else 0) + (if ω 1 then 1 else 0))
      / 2 :=
  prob_ge_le (by norm_num) (by norm_num) (fun ω => by positivity) (by norm_num)
