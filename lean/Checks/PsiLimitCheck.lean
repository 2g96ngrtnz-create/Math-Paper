import HubRemoval.PsiLimit
open HubRemoval Filter Topology

/-! ### Lemma 2.7: axioms -/

#print axioms psi_eq_PsiR_rpow
#print axioms psi_div_le
#print axioms psi_limit

/-! ### The lemma, applied -/

/-- `θ = 0` (`K = 0`): `Ψ(N, N)/N → ρ(1) = 1`. -/
example : Tendsto (fun N : ℕ => (psi N (N / (0 + 1)) : ℝ) / N) atTop (𝓝 1) := by
  have h := psi_limit (K := fun _ => 0) (θ := 0) (eventually_gt_atTop 0) (by simp)
  rwa [dickLim, ite_eq_left (by norm_num), sub_zero, div_one, dickman_eq_one le_rfl] at h

/-- `θ = 1` (`K = N − 1`): `Ψ(N, 1)/N → 0`. -/
example : Tendsto (fun N : ℕ => (psi N (N / (N - 1 + 1)) : ℝ) / N) atTop (𝓝 0) := by
  have hθ : Tendsto (fun N : ℕ => Real.log (((N - 1 : ℕ) : ℝ) + 1) / Real.log N) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hL : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel, div_self hL]
  have h := psi_limit (K := fun N => N - 1) (θ := 1)
    (by filter_upwards [eventually_gt_atTop 0] with N hN; omega) hθ
  rwa [dickLim, ite_eq_right (lt_irrefl 1)] at h

/-- `θ = 1/2` (`K = ⌊√N⌋`): `Ψ(N, N/(⌊√N⌋ + 1))/N → ρ(2) = 1 − log 2`. -/
example : Tendsto (fun N : ℕ => (psi N (N / (Nat.sqrt N + 1)) : ℝ) / N) atTop
    (𝓝 (1 - Real.log 2)) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hθ : Tendsto (fun N : ℕ => Real.log ((Nat.sqrt N : ℝ) + 1) / Real.log N) atTop
      (𝓝 (1 / 2)) := by
    have hup : Tendsto (fun N : ℕ => 1 / 2 + Real.log 2 / Real.log N) atTop (𝓝 (1 / 2)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hN))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with N hN2
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      rw [le_div_iff₀ hL]
      have h1 : Real.log (Real.sqrt N) ≤ Real.log ((Nat.sqrt N : ℝ) + 1) :=
        Real.log_le_log (Real.sqrt_pos.mpr hN0) Real.real_sqrt_lt_nat_sqrt_succ.le
      rw [Real.log_sqrt hN0.le] at h1
      linarith
    · filter_upwards [eventually_ge_atTop 2] with N hN2
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N by omega))
      have h1 : Real.log ((Nat.sqrt N : ℝ) + 1) ≤ Real.log (2 * Real.sqrt N) :=
        Real.log_le_log (by positivity) (by linarith [Real.nat_sqrt_le_real_sqrt (a := N)])
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hN0.le] at h1
      rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']
      linarith
  have h := psi_limit (K := Nat.sqrt) (θ := 1 / 2)
    (by filter_upwards [eventually_gt_atTop 1] with N hN; exact Nat.sqrt_lt_self hN) hθ
  rw [dickLim, ite_eq_left (by norm_num), show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num,
    dickman_eq_one_sub_log (by norm_num) (by norm_num)] at h
  exact h
