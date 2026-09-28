import HubRemoval.DickmanThm

/-!
# The limit of the smooth count (paper, Lemma 2.7)

**Lemma 2.7.** Let `K = K(N) ∈ [0, N)` satisfy `log(K + 1)/log N → θ`. Then
`Ψ(N, N/(K + 1))/N → ρ(1/(1 − θ))`, with `ρ(∞) = 0` (`psi_limit`).

The hypothesis `θ ∈ [0, 1]` of the paper is not needed: it follows from `0 ≤ K < N`.

*Proof.* Put `r_N = log(K + 1)/log N` and `y = N/(K + 1)`.
* If `θ < 1`, put `u_N = 1/(1 − r_N)`. Then `y = N^{1/u_N}`, `u_N → u = 1/(1 − θ)`, and
  eventually `u_N ∈ [1, u + 1]`. By Lemma 2.2 with `U = u + 1`,
  `Ψ(N, y)/N = ρ(u_N) + o(1) → ρ(u)`.
* If `θ = 1`, Lemma 2.3 gives
  `Ψ(N, y)/N ≤ N^{−1/2} + 2(1 − r_N) + 2c₀/log N → 0`.
-/

namespace HubRemoval

open Finset Filter Topology

/-- `ρ(1/(1 − θ))` for `θ < 1`, and `ρ(∞) = 0` for `θ ≥ 1`. -/
noncomputable def dickLim (θ : ℝ) : ℝ := if θ < 1 then dickman (1 / (1 - θ)) else 0

/-- `Ψ(N, N/(K + 1)) = Ψ(N, N^{1 − r})` with `r = log(K + 1)/log N`. -/
theorem psi_eq_PsiR_rpow {N K : ℕ} (hN : 2 ≤ N) :
    (psi N (N / (K + 1)) : ℝ) =
      PsiR (N : ℝ) ((N : ℝ) ^ (1 - Real.log ((K : ℝ) + 1) / Real.log N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hK0 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hy : (N : ℝ) ^ (1 - Real.log ((K : ℝ) + 1) / Real.log N) = (N : ℝ) / ((K : ℝ) + 1) := by
    rw [Real.rpow_def_of_pos hN0]
    have : Real.log N * (1 - Real.log ((K : ℝ) + 1) / Real.log N) =
        Real.log ((N : ℝ) / ((K : ℝ) + 1)) := by
      rw [Real.log_div hN0.ne' hK0.ne']
      field_simp
    rw [this, Real.exp_log (div_pos hN0 hK0)]
  rw [hy]
  unfold PsiR
  rw [Nat.floor_natCast, show (K : ℝ) + 1 = ((K + 1 : ℕ) : ℝ) by push_cast; ring,
    Nat.floor_div_eq_div]

/-- The upper bound for `θ = 1`: for `2 ≤ N` and `K < N`,
`Ψ(N, N/(K + 1))/N ≤ N^{−1/2} + 2(1 − r_N) + 2c₀/log N`. -/
theorem psi_div_le {N K : ℕ} (hN : 2 ≤ N) (hK : K < N) :
    (psi N (N / (K + 1)) : ℝ) / N ≤ (Real.sqrt N)⁻¹ +
      2 * (1 - Real.log ((K : ℝ) + 1) / Real.log N) + 2 * (Real.log 4 + 2) / Real.log N := by
  set c₀ := Real.log 4 + 2 with hc₀
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hK0 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hB1 : 1 ≤ N / (K + 1) := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hB0 : (0 : ℝ) < (N / (K + 1) : ℕ) := by exact_mod_cast hB1
  have hlogB : Real.log ((N / (K + 1) : ℕ) : ℝ) ≤ Real.log N - Real.log ((K : ℝ) + 1) := by
    rw [← Real.log_div hN0.ne' hK0.ne']
    refine Real.log_le_log hB0 ?_
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := K + 1)
    push_cast at this
    exact this
  have hpsi := psi_upper' hN hB1
  rw [div_le_iff₀ hN0]
  have e1 : ((Real.sqrt N)⁻¹ + 2 * (1 - Real.log ((K : ℝ) + 1) / Real.log N) +
      2 * c₀ / Real.log N) * N =
      Real.sqrt N + 2 * N * (Real.log N - Real.log ((K : ℝ) + 1) + c₀) / Real.log N := by
    have : (Real.sqrt N)⁻¹ * N = Real.sqrt N := by rw [inv_mul_eq_div, Real.div_sqrt]
    rw [add_assoc, add_mul, this]
    congr 1
    field_simp
  have e2 : 2 * N * (Real.log ((N / (K + 1) : ℕ) : ℝ) + c₀) / Real.log N ≤
      2 * N * (Real.log N - Real.log ((K : ℝ) + 1) + c₀) / Real.log N :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hL.le
  rw [e1]
  linarith

/-- **Lemma 2.7.** If `K(N) < N` eventually and `log(K + 1)/log N → θ`, then
`Ψ(N, N/(K + 1))/N → ρ(1/(1 − θ))`, with `ρ(∞) = 0` when `θ = 1`. -/
theorem psi_limit {K : ℕ → ℕ} (hK : ∀ᶠ N in atTop, K N < N) {θ : ℝ}
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => (psi N (N / (K N + 1)) : ℝ) / N) atTop (𝓝 (dickLim θ)) := by
  set r : ℕ → ℝ := fun N => Real.log ((K N : ℝ) + 1) / Real.log N with hrdef
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `0 ≤ r_N ≤ 1` eventually.
  have hr : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ K N < N ∧ 0 ≤ r N ∧ r N ≤ 1 := by
    filter_upwards [hK, eventually_ge_atTop 2] with N hKN hN2
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hK1 : (1 : ℝ) ≤ (K N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (K N)]
    have hKN' : (K N : ℝ) + 1 ≤ N := by exact_mod_cast hKN
    refine ⟨hN2, hKN, div_nonneg (Real.log_nonneg hK1) hL.le, ?_⟩
    rw [div_le_one hL]
    exact Real.log_le_log (by linarith) hKN'
  by_cases hθ1 : θ < 1
  · -- `θ < 1`: Dickman's theorem at `u_N = 1/(1 − r_N) → u`.
    rw [dickLim, ite_eq_left hθ1]
    set u := 1 / (1 - θ) with hudef
    have hθ1' : 1 - θ ≠ 0 := by linarith
    have hu : Tendsto (fun N => 1 / (1 - r N)) atTop (𝓝 u) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub hθ) hθ1'
    have hr1 : ∀ᶠ N in atTop, r N < 1 := hθ.eventually_lt_const hθ1
    have hu1 : ∀ᶠ N in atTop, 1 / (1 - r N) < u + 1 := hu.eventually_lt_const (lt_add_one u)
    have hmain : Tendsto (fun N : ℕ => (psi N (N / (K N + 1)) : ℝ) / N - dickman (1 / (1 - r N)))
        atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hr, hr1, hu1, hN.eventually (dickman_asymptotic (u + 1) (half_pos hε))]
        with N hrN' hrN huN hD
      obtain ⟨hN2, -, hr0, -⟩ := hrN'
      have hr' : 0 < 1 - r N := by linarith
      have h1 : 1 ≤ 1 / (1 - r N) := by
        rw [le_div_iff₀ hr']
        linarith
      have h := hD (1 / (1 - r N)) ⟨h1, huN.le⟩
      rw [one_div_one_div] at h
      rw [psi_eq_PsiR_rpow hN2, Real.dist_eq, sub_zero]
      exact h.trans_lt (half_lt_self hε)
    have := hmain.add ((dickman_continuous.tendsto u).comp hu)
    rw [zero_add] at this
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    ring
  · -- `θ = 1`: Lemma 2.3.
    rw [dickLim, ite_eq_right hθ1]
    have hθeq : θ = 1 := le_antisymm
      (le_of_tendsto hθ (hr.mono fun N h => h.2.2.2)) (not_lt.mp hθ1)
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
    have hup : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹ + 2 * (1 - r N) +
        2 * (Real.log 4 + 2) / Real.log N) atTop (𝓝 (0 + 2 * (1 - θ) + 0)) :=
      ((tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)).add
        ((tendsto_const_nhds.sub hθ).const_mul 2)).add (tendsto_const_nhds.div_atTop hlog)
    rw [hθeq, sub_self, mul_zero, zero_add, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun N => by positivity) ?_
    filter_upwards [hr] with N hrN
    exact psi_div_le hrN.1 hrN.2.1

end HubRemoval
