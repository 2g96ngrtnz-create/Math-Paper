import HubRemoval.Profile
open HubRemoval Filter Topology

/-! ### Corollaries 1.3 and 3.3: axioms -/

#print axioms dickLim_of_lt
#print axioms dickLim_of_ge
#print axioms dickLim_zero
#print axioms dickLim_one
#print axioms dickLim_nonneg
#print axioms dickLim_le
#print axioms dickLim_continuous
#print axioms dickLim_strictAntiOn
#print axioms dickLim_of_le_half
#print axioms cor_profile
#print axioms cor_upper_profile_eventually
#print axioms cor_upper_profile
#print axioms tendsto_log_sqrt_succ

/-! ### The profile -/

/-- Continuous and strictly decreasing on `[0, 1]`, from `1` down to `0`. -/
example : ContinuousOn dickLim (Set.Icc 0 1) ∧ StrictAntiOn dickLim (Set.Icc 0 1) ∧
    dickLim 0 = 1 ∧ dickLim 1 = 0 :=
  ⟨dickLim_continuous.continuousOn, dickLim_strictAntiOn, dickLim_zero, dickLim_one⟩

/-- At `θ = 1/2` the profile is `1 − log 2`; at `θ = 1/3` it is `1 − log(3/2)`. -/
example : dickLim (1 / 2) = 1 - Real.log 2 ∧ dickLim (1 / 3) = 1 - Real.log (3 / 2) := by
  refine ⟨?_, ?_⟩
  · rw [dickLim_of_le_half (by norm_num) (by norm_num)]
    norm_num
  · rw [dickLim_of_le_half (by norm_num) (by norm_num)]
    norm_num

/-! ### Corollary 1.3, applied (`ρ = 1/2`) -/

/-- `K = 0`, `θ = 0`: `E[Φ_0]/N → 1`. This is Kim–Phillips' Corollary 2. -/
example : Tendsto (fun N : ℕ => expectP (1 / 2)
    (fun ω : Edge N 0 → Bool => (PhiK N 0 ω : ℝ)) / N) atTop (𝓝 1) := by
  have h := cor_profile (ρ := 1 / 2) (K := fun _ => 0) (θ := 0) (by norm_num) (by norm_num)
    (eventually_gt_atTop 0) (by simp)
  rwa [dickLim_zero] at h

/-- `K = ⌊√N⌋`, `θ = 1/2`: `E[Φ_K]/N → 1 − log 2 ≈ 0.307`. -/
example : Tendsto (fun N : ℕ => expectP (1 / 2)
    (fun ω : Edge N (Nat.sqrt N) → Bool => (PhiK N (Nat.sqrt N) ω : ℝ)) / N) atTop
    (𝓝 (1 - Real.log 2)) := by
  have h := cor_profile (ρ := 1 / 2) (K := Nat.sqrt) (θ := 1 / 2) (by norm_num) (by norm_num)
    (by filter_upwards [eventually_gt_atTop 1] with N hN; exact Nat.sqrt_lt_self hN)
    tendsto_log_sqrt_succ
  rwa [dickLim_of_le_half (by norm_num) (by norm_num),
    show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num] at h

/-- `K = N − 1`, `θ = 1`: `E[Φ_K]/N → 0`. -/
example : Tendsto (fun N : ℕ => expectP (1 / 2)
    (fun ω : Edge N (N - 1) → Bool => (PhiK N (N - 1) ω : ℝ)) / N) atTop (𝓝 0) := by
  have hθ : Tendsto (fun N : ℕ => Real.log (((N - 1 : ℕ) : ℝ) + 1) / Real.log N) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hL : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel, div_self hL]
  have h := cor_profile (ρ := 1 / 2) (K := fun N => N - 1) (θ := 1) (by norm_num) (by norm_num)
    (by filter_upwards [eventually_gt_atTop 0] with N hN; omega) hθ
  rwa [dickLim_one] at h

/-- Corollary 3.3 holds for every `ρ ∈ [0, 1]`, including the degenerate `ρ = 0`. -/
example : limsup (fun N : ℕ => expectP 0
    (fun ω : Edge N (Nat.sqrt N) → Bool => (PhiK N (Nat.sqrt N) ω : ℝ)) / N) atTop ≤
    1 - Real.log 2 := by
  have h := cor_upper_profile (ρ := 0) (K := Nat.sqrt) (θ := 1 / 2) le_rfl zero_le_one
    (by filter_upwards [eventually_gt_atTop 1] with N hN; exact Nat.sqrt_lt_self hN)
    tendsto_log_sqrt_succ
  rwa [dickLim_of_le_half (by norm_num) (by norm_num),
    show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num] at h

/-! ### The profile, numerically (not a proof)

`ρ(1/(1 − θ))` at `θ = 0, 1/3, 1/2, 3/5, 2/3, 3/4, 4/5`, i.e. `u = 1, 1.5, 2, 2.5, 3, 4, 5`,
from the trapezoid rule for `u ρ'(u) = −ρ(u − 1)` with step `1/1000`:
`1, 0.5945, 0.3069, 0.1303, 0.0486, 0.0049, 0.0004`. -/

def rhoGrid (n : ℕ) : Array Float := Id.run do
  let h : Float := 1 / 1000
  let mut a : Array Float := Array.replicate 1001 1
  for i in [1000:n] do
    let t0 := i.toFloat * h
    let v := a[i]! - h / 2 * (a[i - 1000]! / t0 + a[i + 1 - 1000]! / (t0 + h))
    a := a.push v
  return a

#eval let a := rhoGrid 5000; [1000, 1500, 2000, 2500, 3000, 4000, 5000].map (a[·]!)
