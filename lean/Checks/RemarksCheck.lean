import HubRemoval.RemarkEdges
import HubRemoval.RemarkForms
import HubRemoval.RemarkSmallK
import HubRemoval.RemarkRho
import HubRemoval.RemarkSecond
open HubRemoval Finset Filter Topology

/-! ### Remarks 7.1 and 7.3: axioms -/

#print axioms mem_hubEdges_iff
#print axioms card_hubEdges
#print axioms card_edges_zero
#print axioms sum_div_sub_one_bounds
#print axioms abs_card_hubEdges_sub_le
#print axioms abs_card_edges_sub_le
#print axioms abs_card_hubEdges_div_sub_le
#print axioms hub_edge_share
#print axioms kp_corollary_2

/-! ### Remark 3.4: axioms -/

#print axioms card_smoothFibre_bounds
#print axioms abs_card_sub_PhiK_le
#print axioms expect_psi_sub_add
#print axioms formI_to_formII
#print axioms formII_to_formIII
#print axioms formIII_to_formI
#print axioms remark_3_4
#print axioms remark_3_4_holds

/-! ### Remark 5.1: axioms -/

#print axioms sq_gt_of_gt_B
#print axioms N_sub_psi_eq
#print axioms smallK_psi
#print axioms remark_5_1

/-! ### Remark 5.2: axioms -/

#print axioms mul_mem_edges
#print axioms edgeMul_injective
#print axioms arc_edgeMul
#print axioms reach_edgeMul
#print axioms secondSCC_ge
#print axioms expect_secondSCC_ge
#print axioms sqrt_le_B
#print axioms prob_PhiK_le_K
#print axioms second_ge_fixed
#print axioms remark_5_2

/-! ### Remark 5.3: axioms -/

#print axioms lam_le_of_mem
#print axioms s0f_mono
#print axioms GoodT.mono
#print axioms remark_5_3_uniform
#print axioms remark_5_3_uniform_main
#print axioms lam_pow_le_exp
#print axioms q_ge_half_min
#print axioms slow_lam_term
#print axioms slow_q
#print axioms slow_exp_term
#print axioms slow_turan_term
#print axioms slow_small_case
#print axioms slow_large_case
#print axioms slow_rho_bound
#print axioms remark_5_3_slow

/-! ### Remark 7.1 on concrete instances -/

-- In `G_12` the hubs `{1, 2, 3}` meet `11 + 5 + 3 = 19` of the `∑_{d ≤ 12} (⌊12/d⌋ − 1) = 23`
-- edges.
example : (hubEdges 12 3).card = 19 := by
  rw [card_hubEdges (by norm_num)]; decide
example : (edges 12 0).card = 23 := by
  rw [card_edges_zero]; decide

/-- The count formula on a concrete case, with `K = N`. -/
example : (hubEdges 30 30).card = (edges 30 0).card := by
  rw [card_hubEdges (le_refl 30), card_edges_zero]

/-- With a bounded number of hubs (`K = 5`, so `θ = 0`), the hubs carry a vanishing share of the
edges. -/
example : Tendsto (fun N : ℕ => ((hubEdges N 5).card : ℝ) / (edges N 0).card) atTop (𝓝 0) := by
  refine hub_edge_share (K := fun _ => 5) (eventually_ge_atTop 5) ?_
  exact (tendsto_const_nhds (x := Real.log (((5 : ℕ) : ℝ) + 1))).div_atTop tendsto_log_nat

/-! ### Remark 7.3 at `ρ = 1/2` -/

example : Tendsto (fun N : ℕ => expectP (1 / 2) (fun ω : Edge N 0 → Bool => (PhiK N 0 ω : ℝ)) / N)
    atTop (𝓝 1) :=
  kp_corollary_2 (by norm_num) (by norm_num)

/-! ### Remark 3.4 at `ρ = 1/2`, `K ≡ 7`: all three forms hold -/

theorem forms_seven :
    FormI (1 / 2) (fun _ => 7) ∧ FormII (1 / 2) (fun _ => 7) ∧ FormIII (1 / 2) (fun _ => 7) := by
  have hI : FormI (1 / 2) (fun _ => 7) :=
    remark_3_4_holds (by norm_num) (by norm_num) (eventually_gt_atTop 7)
  have hK : Tendsto (fun N : ℕ => ((7 : ℕ) : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨h1, h2⟩ := remark_3_4 (ρ := 1 / 2) (K := fun _ => 7) (by norm_num) (by norm_num)
    (eventually_ge_atTop 7) hK
  exact ⟨hI, h1.mp hI, h2.mp (h1.mp hI)⟩

/-- Form (iii) spelled out: w.h.p. the largest SCC of `𝒟_{1/2}(N, 7)` has at least
`|F₁| − N/100` vertices. -/
example : Tendsto (fun N : ℕ => prob (1 / 2) (fun ω : Edge N 7 → Bool =>
    (PhiK N 7 ω : ℝ) < (smoothFibre N 7).card - 1 / 100 * N)) atTop (𝓝 0) :=
  forms_seven.2.2 (1 / 100) (by norm_num)

/-! ### Remark 5.1 at `ρ = 1/2` -/

example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K : ℕ, (K + 1) ^ 2 ≤ N →
    |1 - expectP (1 / 2) (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) / N -
        Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ))| ≤
      31 / Real.log (Real.log N) :=
  remark_5_1 (by norm_num) (by norm_num)

/-- The deterministic identity `N − Ψ(N, B) = ∑_{B<p≤N} ⌊N/p⌋` at `N = 100`, `K = 9`
(`B = 10`): the primes in `(10, 100]` contribute `100 − Ψ(100, 10) = 100 − 58 = 42`. -/
example : (100 : ℝ) - psi 100 (100 / (9 + 1)) =
    ∑ p ∈ (primesUpTo 100).filter (fun p => 100 / (9 + 1) < p), ((100 / p : ℕ) : ℝ) :=
  N_sub_psi_eq (by norm_num)

/-! ### Remark 5.3 -/

/-- (a) with `ρ₀ = 1/4`: one `N₀` serves every `ρ ∈ [1/4, 3/4]`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ : ℝ, 1 / 4 ≤ ρ → ρ ≤ 1 - 1 / 4 → ∀ K < N,
    0 ≤ gap ρ N K ∧ gap ρ N K ≤ 30 * N / Real.log (Real.log N) :=
  remark_5_3_uniform (by norm_num) (by norm_num)

/-- (b), quantitative, with `ε = 1/2`. -/
example : ∃ A : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    A ≤ min ρ (1 - ρ) * Real.log (Real.log N) → ∀ K < N, gap ρ N K ≤ 1 / 2 * N :=
  slow_rho_bound (by norm_num) (by norm_num)

/-- A slowly vanishing density: `ρ_N = 1/(2 + √(log log N))` for `N ≥ 16` (and `1/2` before). Then
`min(ρ_N, 1 − ρ_N) log log N ≥ ½ √(log log N) → ∞`, so Theorem 1.2 holds along `ρ_N`. -/
noncomputable def rhoSlow (N : ℕ) : ℝ := 1 / (2 + Real.sqrt (max 0 (Real.log (Real.log N))))

theorem rhoSlow_mem (N : ℕ) : 0 < rhoSlow N ∧ rhoSlow N < 1 := by
  unfold rhoSlow
  have h := Real.sqrt_nonneg (max 0 (Real.log (Real.log N)))
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

theorem rhoSlow_tendsto_zero : Tendsto rhoSlow atTop (𝓝 0) := by
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_nat
  have h1 : Tendsto (fun N : ℕ => max 0 (Real.log (Real.log N))) atTop atTop :=
    tendsto_atTop_mono (fun N => le_max_right _ _) hll
  have h2 : Tendsto (fun N : ℕ => 2 + Real.sqrt (max 0 (Real.log (Real.log N)))) atTop atTop :=
    tendsto_atTop_add_const_left _ 2 (Real.tendsto_sqrt_atTop.comp h1)
  exact Tendsto.congr (fun N => by simp [rhoSlow]) h2.inv_tendsto_atTop

theorem rhoSlow_min_mul (N : ℕ) (hN : 0 ≤ Real.log (Real.log N)) :
    Real.sqrt (Real.log (Real.log N)) / 3 ≤
      min (rhoSlow N) (1 - rhoSlow N) * Real.log (Real.log N) ∨
    Real.log (Real.log N) ≤ 1 := by
  rcases le_or_gt (Real.log (Real.log N)) 1 with h | h
  · exact Or.inr h
  left
  set L := Real.log (Real.log N) with hL
  set r := Real.sqrt L with hr
  have hmax : max 0 L = L := max_eq_right hN
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr h.le
  have hrr : r * r = L := Real.mul_self_sqrt hN
  have hρ : rhoSlow N = 1 / (2 + r) := by rw [rhoSlow, ← hL, hmax]
  have hmin : min (rhoSlow N) (1 - rhoSlow N) = 1 / (2 + r) := by
    rw [hρ]
    apply min_eq_left
    rw [le_sub_iff_add_le, ← add_div, div_le_one (by linarith)]
    linarith
  rw [hmin, ← hrr, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- (b) along `ρ_N = 1/(2 + √(log log N)) → 0`. -/
example : Tendsto (fun N : ℕ => ⨆ K : Fin N, gap (rhoSlow N) N K / N) atTop (𝓝 0) := by
  refine remark_5_3_slow rhoSlow_mem ?_
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_nat
  have hs : Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log N)) / 3) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hll).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hs
  filter_upwards [hll.eventually_gt_atTop 1] with N hN
  rcases rhoSlow_min_mul N (by linarith) with h | h
  · exact h
  · linarith

/-! ### Remark 5.2 at `ρ = 1/2`, `K = ⌊⌊√N⌋/2⌋` -/

/-- A rule choosing a largest SCC whenever `k < N`. -/
noncomputable def starSel (N k : ℕ) : (Edge N k → Bool) → Finset ℕ :=
  if h : k < N then Classical.choose (exists_star h) else fun _ => ∅

theorem starSel_spec {N k : ℕ} (h : k < N) (ω : Edge N k → Bool) :
    IsSCC ω (starSel N k ω) ∧ (starSel N k ω).card = PhiK N k ω := by
  unfold starSel
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (exists_star h) ω

theorem sqrt_half_tendsto : Tendsto (fun N : ℕ => Nat.sqrt N / 2) atTop atTop := by
  refine tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨(2 * b) * (2 * b), fun N hN => ?_⟩
  have := Nat.le_sqrt.mpr hN
  omega

theorem sqrt_half_le (N : ℕ) : ((Nat.sqrt N / 2 : ℕ) : ℝ) ≤ Real.sqrt N / 2 := by
  have h1 : ((Nat.sqrt N / 2 : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := Nat.sqrt N) (n := 2)
    simpa using this
  have h2 : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  linarith

/-- With `K = ⌊⌊√N⌋/2⌋`, the second largest SCC has mean at least `(1/2 − ε)K` for large `N`. -/
example {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, (1 / 2 - ε) * ((Nat.sqrt N / 2 : ℕ) : ℝ) ≤
    expectP (1 / 2) (fun ω : Edge N (Nat.sqrt N / 2) → Bool =>
      (secondSCC ω (starSel N (Nat.sqrt N / 2) ω) : ℝ)) :=
  remark_5_2 (K := fun N => Nat.sqrt N / 2) (by norm_num) (by norm_num) sqrt_half_tendsto
    (Eventually.of_forall sqrt_half_le) (fun N => starSel N (Nat.sqrt N / 2))
    (fun _ h ω => starSel_spec h ω) hε
