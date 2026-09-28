import HubRemoval.Rate
open HubRemoval Filter Topology

/-! ### Theorems 1.1 and 1.2: axioms -/

#print axioms half_le_lam
#print axioms s0f_le
#print axioms lam_pow_s0f_le
#print axioms eventually_mul_log_pow_le
#print axioms eventually_goodT
#print axioms eventually_goodN
#print axioms expect_PhiK_nonneg
#print axioms gap_nonneg
#print axioms gap_le_of_good
#print axioms thm_rate
#print axioms thm_main

/-! ### The theorems, applied -/

/-- Theorem 1.2 for `ρ = 1/2`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K < N,
    0 ≤ gap (1 / 2) N K ∧ gap (1 / 2) N K ≤ 30 * N / Real.log (Real.log N) :=
  thm_rate (by norm_num) (by norm_num)

/-- Theorem 1.1 for `ρ = 1/3`. -/
example : Tendsto (fun N : ℕ => ⨆ K : Fin N, gap (1 / 3) N K / N) atTop (𝓝 0) :=
  (thm_main (by norm_num) (by norm_num)).2

/-- The uniform form of Theorem 1.1: for every `ε > 0`, eventually `gap/N ≤ ε` for all `K < N`. -/
example {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ K < N, gap ρ N K ≤ ε * N := by
  have hlim : Tendsto (fun N : ℕ => 30 / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_log_nat)
  filter_upwards [eventually_goodN hρ0 hρ1, (hlim.eventually (gt_mem_nhds hε))]
    with N hG hsmall K hK
  have h := gap_le_of_good hρ0 hρ1 hK hG
  calc gap ρ N K ≤ 30 * N / Real.log (Real.log N) := h
    _ = 30 / Real.log (Real.log N) * N := by ring
    _ ≤ ε * N := mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg N)

/-! ### How large is `N₀`? (numerics, not a proof)

The binding condition is (R2), `log(8ℓ²s₀) + 13 + 2s₀ ≤ ℓ/2` with `ℓ = log log N`. For `ρ = 1/2`
it first holds at `ℓ = 80`, so `N₀ ≥ exp(exp 80)`. As the paper says, the bound `30N/log log N`
is non-trivial only when `log log N > 30`, and its content is the uniformity in `K` and the rate. -/

#eval
  let lamInv : Float := 2   -- 1/λ for ρ = 1/2
  let ok (ℓ : Float) : Bool :=
    let s0 := max 1 (Float.ceil (Float.log ℓ / Float.log lamInv))
    Float.log (8 * ℓ * ℓ * s0) + 13 + 2 * s0 ≤ ℓ / 2
  ((List.range 200).map (fun i => (i + 2).toFloat)).find? ok   -- some 80
