import HubRemoval.Unconditional

/-!
# The growth conditions (R1)–(R6) in the proof of Theorem 1.3

The proof of Theorem 1.3 uses the parameters
`ℓ = log log N`, `η = 1/ℓ`, `δ = 1/(8ℓ²)`, `s₀ = max(1, ⌈log ℓ / log(1/λ)⌉)`, `z = N^{δ/s₀}`,
where `λ = max(ρ, 1 − ρ)`, and six growth conditions (R1)–(R6) that hold "for `N ≥ N₀(ρ)`".

Here `t = log N`, so `ℓ = log t`. `GoodT ρ t` collects the inequalities in `t` that the proof
needs, and `eventually_goodT` proves that they hold for all large `t`. All of them come from one
fact: `A (log t)^k ≤ t` eventually, because powers of `log t` are `o(t)`
(`eventually_mul_log_pow_le`, from Mathlib's `Real.isLittleO_pow_log_id_atTop`).
`eventually_goodN` transfers this to `N → ∞`.
-/

namespace HubRemoval

open Filter Topology

/-- `λ = max(ρ, 1 − ρ)`. -/
noncomputable def lam (ρ : ℝ) : ℝ := max ρ (1 - ρ)

/-- `s₀ = max(1, ⌈log ℓ / log(1/λ)⌉)`, as a function of `ℓ`. -/
noncomputable def s0f (ρ ℓ : ℝ) : ℕ := max 1 ⌈Real.log ℓ / Real.log (1 / lam ρ)⌉₊

theorem half_le_lam (ρ : ℝ) : 1 / 2 ≤ lam ρ := by
  unfold lam
  rcases le_total ρ (1 - ρ) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem lam_lt_one {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : lam ρ < 1 := max_lt hρ1 (by linarith)

theorem log_inv_lam_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < Real.log (1 / lam ρ) := by
  have h1 := half_le_lam ρ
  have h2 := lam_lt_one hρ0 hρ1
  exact Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)

theorem one_le_s0f (ρ ℓ : ℝ) : 1 ≤ s0f ρ ℓ := le_max_left _ _

/-- `s₀ ≤ 2 + log ℓ / log(1/λ)` for `ℓ ≥ 1`. -/
theorem s0f_le {ρ ℓ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hℓ : 1 ≤ ℓ) :
    (s0f ρ ℓ : ℝ) ≤ 2 + Real.log ℓ / Real.log (1 / lam ρ) := by
  have hx : 0 ≤ Real.log ℓ / Real.log (1 / lam ρ) :=
    div_nonneg (Real.log_nonneg hℓ) (log_inv_lam_pos hρ0 hρ1).le
  have hc := Nat.ceil_lt_add_one hx
  unfold s0f
  rcases le_total 1 ⌈Real.log ℓ / Real.log (1 / lam ρ)⌉₊ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; push_cast; linarith

/-- `λ^{s₀} ≤ 1/ℓ`, because `s₀ ≥ log ℓ / log(1/λ)`. -/
theorem lam_pow_s0f_le {ρ ℓ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hℓ : 0 < ℓ) :
    lam ρ ^ s0f ρ ℓ ≤ 1 / ℓ := by
  have hlam0 : 0 < lam ρ := by linarith [half_le_lam ρ]
  have hc := log_inv_lam_pos hρ0 hρ1
  have hs : Real.log ℓ / Real.log (1 / lam ρ) ≤ s0f ρ ℓ :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hloglam : Real.log (lam ρ) = -Real.log (1 / lam ρ) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hkey : (s0f ρ ℓ : ℝ) * Real.log (lam ρ) ≤ -Real.log ℓ := by
    rw [hloglam]
    have := (div_le_iff₀ hc).mp hs
    linarith
  calc lam ρ ^ s0f ρ ℓ = Real.exp ((s0f ρ ℓ : ℝ) * Real.log (lam ρ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlam0, mul_comm]
    _ ≤ Real.exp (-Real.log ℓ) := Real.exp_le_exp.mpr hkey
    _ = 1 / ℓ := by rw [Real.exp_neg, Real.exp_log hℓ, one_div]

/-- **The master fact.** For all `A` and `k`, `A (log t)^k ≤ t` for all large `t`. -/
theorem eventually_mul_log_pow_le (A : ℝ) (k : ℕ) :
    ∀ᶠ t : ℝ in atTop, A * Real.log t ^ k ≤ t := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := k)).bound
    (show (0 : ℝ) < 1 / (|A| + 1) by positivity)
  filter_upwards [h, eventually_ge_atTop 0] with t ht ht0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg ht0] at ht
  have hA : |A| * (1 / (|A| + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  calc A * Real.log t ^ k ≤ |A| * |Real.log t ^ k| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |A| * (1 / (|A| + 1) * t) := mul_le_mul_of_nonneg_left ht (abs_nonneg A)
    _ = (|A| * (1 / (|A| + 1))) * t := by ring
    _ ≤ 1 * t := mul_le_mul_of_nonneg_right hA ht0
    _ = t := one_mul t

/-- The inequalities in `t = log N` used in the proof of Theorem 1.3 (`ℓ = log t`). -/
structure GoodT (ρ t : ℝ) : Prop where
  /-- `ℓ > 1`. -/
  p0 : 1 < Real.log t
  /-- (R1), first part: `N^{η/4} ≥ 4`. -/
  p1 : 4 * Real.log 4 * Real.log t ≤ t
  /-- (R1), second part: `z ≥ 2`. -/
  p2 : 8 * Real.log 2 * Real.log t ^ 2 * s0f ρ (Real.log t) ≤ t
  /-- (R2): `L ≥ max(2 s₀, ℓ/2)`. -/
  p3 : Real.log (8 * Real.log t ^ 2 * s0f ρ (Real.log t)) + 13 + 2 * s0f ρ (Real.log t) ≤
    Real.log t / 2
  /-- (R3), first part: `N^{1−η} ≤ N/ℓ`. -/
  p4 : Real.log t * Real.log (Real.log t) ≤ t
  /-- (R3), second part: `N^{1−δ} ≤ N/ℓ`. -/
  p5 : 8 * Real.log t ^ 2 * Real.log (Real.log t) ≤ t
  /-- (R4): `2(1 + C₁)/(η log N) ≤ 1/(2ℓ)` with `C₁ = 18`. -/
  p6 : 76 * Real.log t ^ 2 ≤ t
  /-- (R5): `N³ exp(−q (N^{2δ} − 2)) ≤ 1`. -/
  p7 : 3 * t ≤ ρ * (1 - ρ) * (Real.exp (t / (4 * Real.log t ^ 2)) - 2)
  /-- (R6), first part: `√N ≤ N/(2ℓ)`. -/
  p8 : 2 * Real.log t ≤ Real.exp (t / 2)
  /-- (R6), second part: `2 c₀ N/log N ≤ N/(2ℓ)` with `c₀ = log 4 + 2`. -/
  p9 : 4 * (Real.log 4 + 2) * Real.log t ≤ t

/-- `log log t ≤ log t` when `log t > 0`. -/
theorem loglog_le_log {t : ℝ} (h : 0 < Real.log t) : Real.log (Real.log t) ≤ Real.log t := by
  have := Real.log_le_sub_one_of_pos h
  linarith

/-- **(R1)–(R6) hold for all large `t`.** -/
theorem eventually_goodT {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ t : ℝ in atTop, GoodT ρ t := by
  set c := 1 / Real.log (1 / lam ρ) with hcdef
  have hc : 0 < c := one_div_pos.mpr (log_inv_lam_pos hρ0 hρ1)
  have hq0 : 0 < ρ * (1 - ρ) := mul_pos hρ0 (by linarith)
  have hq1 : ρ * (1 - ρ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
  have hs0 : ∀ ℓ : ℝ, 1 ≤ ℓ → (s0f ρ ℓ : ℝ) ≤ 2 + c * Real.log ℓ := fun ℓ hℓ => by
    have := s0f_le hρ0 hρ1 hℓ
    rw [hcdef]
    linarith [show Real.log ℓ / Real.log (1 / lam ρ) = 1 / Real.log (1 / lam ρ) * Real.log ℓ by
      ring]
  -- `log t → ∞`, so conditions in `ℓ = log t` transfer to `t`.
  have hlog := Real.tendsto_log_atTop
  -- (R2), in the variable `ℓ`.
  have hR2 : ∀ᶠ ℓ : ℝ in atTop, Real.log (8 * ℓ ^ 2 * s0f ρ ℓ) + 13 + 2 * s0f ρ ℓ ≤ ℓ / 2 := by
    filter_upwards [eventually_mul_log_pow_le (4 * (3 + 2 * c)) 1, eventually_ge_atTop 1,
      eventually_ge_atTop (4 * (Real.log (8 * (2 + c)) + 17))] with ℓ h1 hℓ1 hℓ2
    rw [pow_one] at h1
    have hs := hs0 ℓ hℓ1
    have hs1 : (1 : ℝ) ≤ s0f ρ ℓ := by exact_mod_cast one_le_s0f ρ ℓ
    have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
    have hlogℓ' : Real.log ℓ ≤ ℓ := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < ℓ)]
    -- `8ℓ² s₀ ≤ 8(2 + c) ℓ³`.
    have hbound : 8 * ℓ ^ 2 * (s0f ρ ℓ : ℝ) ≤ 8 * (2 + c) * ℓ ^ 3 := by
      have : (s0f ρ ℓ : ℝ) ≤ (2 + c) * ℓ := by nlinarith
      nlinarith [sq_nonneg ℓ]
    have hlog8 : Real.log (8 * ℓ ^ 2 * s0f ρ ℓ) ≤ Real.log (8 * (2 + c)) + 3 * Real.log ℓ := by
      calc Real.log (8 * ℓ ^ 2 * s0f ρ ℓ) ≤ Real.log (8 * (2 + c) * ℓ ^ 3) :=
            Real.log_le_log (by positivity) hbound
        _ = Real.log (8 * (2 + c)) + 3 * Real.log ℓ := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
            push_cast
            ring
    nlinarith
  filter_upwards [hlog.eventually (eventually_gt_atTop 1), hlog.eventually hR2,
    eventually_mul_log_pow_le (4 * Real.log 4) 1,
    eventually_mul_log_pow_le (8 * Real.log 2 * (2 + c)) 3,
    eventually_mul_log_pow_le 1 2, eventually_mul_log_pow_le 8 3, eventually_mul_log_pow_le 76 2,
    eventually_mul_log_pow_le (128 / (ρ * (1 - ρ))) 4, eventually_mul_log_pow_le 4 1,
    eventually_mul_log_pow_le (4 * (Real.log 4 + 2)) 1, eventually_ge_atTop 1]
    with t h0 h3 h1 h2 h4 h5 h6 h7 h8 h9 ht1
  have hl1 : 1 ≤ Real.log t := h0.le
  have hl0 : 0 < Real.log t := by linarith
  have hll := loglog_le_log hl0
  have hll0 : 0 ≤ Real.log (Real.log t) := Real.log_nonneg hl1
  rw [pow_one] at h1 h8 h9
  refine ⟨h0, h1, ?_, h3, ?_, ?_, h6, ?_, ?_, h9⟩
  · -- (R1b)
    have hs := hs0 (Real.log t) hl1
    have hs' : (s0f ρ (Real.log t) : ℝ) ≤ (2 + c) * Real.log t := by nlinarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc 8 * Real.log 2 * Real.log t ^ 2 * s0f ρ (Real.log t)
        ≤ 8 * Real.log 2 * Real.log t ^ 2 * ((2 + c) * Real.log t) :=
          mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = 8 * Real.log 2 * (2 + c) * Real.log t ^ 3 := by ring
      _ ≤ t := h2
  · -- (R3a)
    calc Real.log t * Real.log (Real.log t) ≤ Real.log t * Real.log t :=
          mul_le_mul_of_nonneg_left hll hl0.le
      _ = 1 * Real.log t ^ 2 := by ring
      _ ≤ t := h4
  · -- (R3b)
    calc 8 * Real.log t ^ 2 * Real.log (Real.log t) ≤ 8 * Real.log t ^ 2 * Real.log t :=
          mul_le_mul_of_nonneg_left hll (by positivity)
      _ = 8 * Real.log t ^ 3 := by ring
      _ ≤ t := h5
  · -- (R5): `exp u ≥ u²/2` with `u = t/(4 log² t)`.
    set u := t / (4 * Real.log t ^ 2) with hu
    have hu0 : 0 ≤ u := by positivity
    have hexp := Real.quadratic_le_exp_of_nonneg hu0
    have hu2 : u ^ 2 = t ^ 2 / (16 * Real.log t ^ 4) := by rw [hu]; field_simp; ring
    -- `q t ≥ 128 log⁴ t`.
    have h7' : 128 * Real.log t ^ 4 ≤ ρ * (1 - ρ) * t := by
      have := mul_le_mul_of_nonneg_left h7 hq0.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hq0.ne'] at this
    have hL4 : 0 < Real.log t ^ 4 := by positivity
    -- `q u²/2 ≥ 4t ≥ 3t + 2q`.
    have hkey : 4 * t ≤ ρ * (1 - ρ) * (u ^ 2 / 2) := by
      rw [hu2]
      rw [show ρ * (1 - ρ) * (t ^ 2 / (16 * Real.log t ^ 4) / 2) =
        (ρ * (1 - ρ) * t) * t / (32 * Real.log t ^ 4) by ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  · -- (R6a): `exp(t/2) ≥ 1 + t/2 ≥ 2 log t`.
    have := Real.add_one_le_exp (t / 2)
    linarith

/-- `log N → ∞` along the natural numbers. -/
theorem tendsto_log_nat : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **(R1)–(R6) hold for all large `N`**, with `t = log N`. -/
theorem eventually_goodN {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ N : ℕ in atTop, GoodT ρ (Real.log N) :=
  tendsto_log_nat.eventually (eventually_goodT hρ0 hρ1)

end HubRemoval
