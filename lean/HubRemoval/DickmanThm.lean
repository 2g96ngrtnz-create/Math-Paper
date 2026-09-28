import HubRemoval.Dickman
import HubRemoval.PrimeSum

/-!
# Dickman's theorem (paper, Lemma 2.2, second part)

**Lemma 2.2 (second part).** For every fixed `U ≥ 1`,
`sup_{1 ≤ u ≤ U} |Ψ(x, x^{1/u})/x − ρ(u)| → 0` as `x → ∞` (`dickman_asymptotic`,
`dickman_tendstoUniformlyOn`).

The paper cites this (Dickman; de Bruijn; Hildebrand). Here it is proved from Lemma 2.1(b)
and (d), Buchstab's identity and the integral equation, by induction on `n` with
`u ∈ [1, n]`.

* **Base, `u ∈ [1, 2]`** (`psi_dickman_base`). Buchstab with `z = x` gives
  `Ψ(x, x^{1/u}) = ⌊x⌋ − ∑_{x^{1/u} < p ≤ x} Ψ(x/p, p)`. For `p > x^{1/u} ≥ √x` we have
  `x/p < p`, so `Ψ(x/p, p) = ⌊x/p⌋ = x/p + O(1)`. Lemma 2.1(b) gives `∑ 1/p = log u + O(1/log x)`,
  and Lemma 2.1(d) bounds the number of `O(1)` errors by `π(x) ≤ 5x/log x`. So
  `Ψ(x, x^{1/u})/x = 1 − log u + o(1) = ρ(u) + o(1)`.
* **Step, `u ∈ [n, n + 1]`, `n ≥ 2`** (`psi_dickman_step`). Buchstab with `z = x^{1/n}` gives
  `Ψ(x, x^{1/u}) = Ψ(x, x^{1/n}) − ∑_{x^{1/u} < p ≤ x^{1/n}} Ψ(x/p, p)`. For such `p`, put
  `w_p = log x/log p ∈ [n, u)`. Then `(x/p)^{1/(w_p − 1)} = p`, `w_p − 1 ∈ [1, n]`, and
  `x/p ≥ √x`. So the induction hypothesis gives `Ψ(x/p, p) = (x/p)(ρ(w_p − 1) + o(1))`. The prime
  sum `∑ ρ(w_p − 1)/p` tends to `∫_n^u ρ(w − 1)/w dw` (`primeSum_integral`), and
  `ρ(u) = ρ(n) − ∫_n^u ρ(w − 1)/w dw`.

**Consequence (end of Lemma 2.3).** `ρ(u) ≤ 2/u` for `u ≥ 1`, and `ρ(u) → 0`
(`dickman_le_two_div`, `dickman_tendsto_zero`). This follows by letting `x → ∞` in Lemma 2.3.
-/

namespace HubRemoval

open Finset Filter Topology intervalIntegral

/-- `Ψ(X, y)` is non-decreasing in `y`. -/
theorem psi_mono_right (X : ℕ) {Y Z : ℕ} (h : Y ≤ Z) : psi X Y ≤ psi X Z := by
  rw [buchstab X h]
  exact Nat.le_add_right _ _

/-- With `v = log x/log p − 1 ≠ 0`, `(x/p)^{1/v} = p`. -/
theorem div_rpow_log_div {x p : ℝ} (hx : 0 < x) (hp : 1 < p)
    (hv : Real.log x / Real.log p - 1 ≠ 0) :
    (x / p) ^ (1 / (Real.log x / Real.log p - 1)) = p := by
  have hp0 : 0 < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos hp
  have hv' : Real.log x - Real.log p = (Real.log x / Real.log p - 1) * Real.log p := by
    rw [sub_mul, div_mul_cancel₀ _ hlp.ne', one_mul]
  rw [Real.rpow_def_of_pos (div_pos hx hp0), Real.log_div hx.ne' hp0.ne', hv',
    mul_comm (Real.log x / Real.log p - 1), mul_assoc, mul_one_div_cancel hv, mul_one,
    Real.exp_log hp0]

/-- The arithmetic of the base case. -/
theorem base_arith {x L ℓ u ε F P S A c : ℝ} (hx0 : 0 < x) (hL : 0 < L) (hε : 0 < ε)
    (hxε : 2 / ε ≤ x) (hLx : 82 / ε ≤ L) (hu2 : u ≤ 2) (hF1 : x - 1 < F) (hF2 : F ≤ x)
    (hB : F = P + S) (hlow : x * A - c ≤ S) (hup : S ≤ x * A) (hc : c ≤ 5 * x / L)
    (hA : |A - ℓ| ≤ 18 * u / L) :
    |P / x - (1 - ℓ)| ≤ ε := by
  have e : P / x - (1 - ℓ) = (P - x * (1 - ℓ)) / x := by field_simp
  rw [e, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  set q := 1 / L with hqdef
  have e1 : 18 * u / L = 18 * u * q := by rw [hqdef]; ring
  have e2 : 5 * x / L = 5 * x * q := by rw [hqdef]; ring
  rw [e1] at hA
  rw [e2] at hc
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ ε / 82 := by
    rw [hqdef, div_le_div_iff₀ hL (by norm_num)]
    have := (div_le_iff₀ hε).mp hLx
    linarith
  have h2 : 2 ≤ x * ε := by
    have := (div_le_iff₀ hε).mp hxε
    linarith
  have p1 : x * (A - ℓ) ≤ x * (18 * u * q) := mul_le_mul_of_nonneg_left hA2 hx0.le
  have p2 : x * (-(18 * u * q)) ≤ x * (A - ℓ) := mul_le_mul_of_nonneg_left hA1 hx0.le
  have p3 : x * q * u ≤ x * q * 2 := mul_le_mul_of_nonneg_left hu2 (by positivity)
  have p4 : x * q ≤ x * (ε / 82) := mul_le_mul_of_nonneg_left hq hx0.le
  have hu0 : 0 ≤ x * q * u := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- **Base case: `u ∈ [1, 2]`.** -/
theorem psi_dickman_base {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (1 : ℝ) 2,
      |(PsiR x (x ^ (1 / u)) : ℝ) / x - dickman u| ≤ ε := by
  filter_upwards [eventually_ge_atTop 4, eventually_ge_atTop (2 / ε),
    Real.tendsto_log_atTop.eventually_ge_atTop (82 / ε)] with x hx4 hxε hLx u hu
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hu0 : 0 < u := by linarith [hu.1]
  have hsq : Real.sqrt x ≤ x ^ (1 / u) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1.le (one_div_le_one_div_of_le hu0 hu.2)
  have hsq2 : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
  have h2 : 2 ≤ x ^ (1 / u) := hsq2.trans hsq
  -- Buchstab with `z = x`.
  have hB := buchstab_real (x := x) (y := x ^ (1 / u)) (z := x ^ (1 / (1 : ℝ)))
    (Real.rpow_nonneg hx0.le _)
    (Real.rpow_le_rpow_of_exponent_le hx1.le (one_div_le_one_div_of_le one_pos hu.1))
  change (PsiR x (x ^ (1 / (1 : ℝ))) : ℝ) = PsiR x (x ^ (1 / u)) +
    ∑ p ∈ primesBetween x 1 u, (PsiR (x / p) p : ℝ) at hB
  have hPx : (PsiR x (x ^ (1 / (1 : ℝ))) : ℝ) = ⌊x⌋₊ := by
    unfold PsiR
    rw [div_one, Real.rpow_one, psi_eq_self_of_le le_rfl]
  -- For `p > √x`, `Ψ(x/p, p) = ⌊x/p⌋`.
  have hterm : ∀ p ∈ primesBetween x 1 u, (PsiR (x / p) p : ℝ) = ⌊x / p⌋₊ := fun p hp => by
    obtain ⟨hpp, -, hpu⟩ := (mem_primesBetween hx0.le).mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hxp : x < (p : ℝ) ^ 2 := (Real.sqrt_lt' hp0).mp (hsq.trans_lt hpu)
    have hle : x / p ≤ p := by
      rw [div_le_iff₀ hp0]
      rw [pow_two] at hxp
      linarith
    unfold PsiR
    rw [Nat.floor_natCast, psi_eq_self_of_le (Nat.floor_le_of_le hle)]
  rw [hPx, sum_congr rfl hterm] at hB
  have hA := sum_primesBetween_inv hx1 one_pos hu.1 h2
  rw [div_one] at hA
  have hlow : x * ∑ p ∈ primesBetween x 1 u, (1 : ℝ) / p - (primesBetween x 1 u).card ≤
      ∑ p ∈ primesBetween x 1 u, (⌊x / p⌋₊ : ℝ) := by
    have : x * ∑ p ∈ primesBetween x 1 u, (1 : ℝ) / p - (primesBetween x 1 u).card =
        ∑ p ∈ primesBetween x 1 u, (x / p - 1) := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, mul_sum]
      simp only [mul_one_div]
    rw [this]
    exact sum_le_sum fun p _ => (Nat.sub_one_lt_floor _).le
  have hup : ∑ p ∈ primesBetween x 1 u, (⌊x / p⌋₊ : ℝ) ≤
      x * ∑ p ∈ primesBetween x 1 u, (1 : ℝ) / p := by
    rw [mul_sum]
    exact sum_le_sum fun p _ => by rw [mul_one_div]; exact Nat.floor_le (by positivity)
  have hc : ((primesBetween x 1 u).card : ℝ) ≤ 5 * x / Real.log x := by
    have h1 : (primesBetween x 1 u).card ≤ (primesUpTo ⌊x⌋₊).card := by
      unfold primesBetween
      rw [div_one, Real.rpow_one]
      exact card_filter_le _ _
    exact (Nat.cast_le.mpr h1).trans (mertens_d (by linarith))
  rw [dickman_eq_one_sub_log hu.1 hu.2]
  exact base_arith hx0 hL hε hxε hLx hu.2 (Nat.sub_one_lt_floor x) (Nat.floor_le hx0.le) hB
    hlow hup hc hA

/-- The arithmetic of the induction step. -/
theorem step_arith {Pu Pn S₁ S₂ J ρu ρn A ε : ℝ} (hε : 0 < ε) (hB : Pu = Pn - S₁)
    (hρ : ρu = ρn - J) (hn : |Pn - ρn| ≤ ε / 4) (hs : |S₁ - S₂| ≤ ε / 4 * A)
    (hA : A ≤ 2) (hR : |S₂ - J| ≤ ε / 4) : |Pu - ρu| ≤ ε := by
  have h1 : ε / 4 * A ≤ ε / 4 * 2 := mul_le_mul_of_nonneg_left hA (by positivity)
  rw [abs_le] at hn hs hR ⊢
  constructor <;> linarith

/-- **Induction step: `u ∈ [n, n + 1]`, from `[1, n]`, for `n ≥ 2`.** -/
theorem psi_dickman_step {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ ε > 0, ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (1 : ℝ) n,
      |(PsiR x (x ^ (1 / u)) : ℝ) / x - dickman u| ≤ ε) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (n : ℝ) (n + 1),
      |(PsiR x (x ^ (1 / u)) : ℝ) / x - dickman u| ≤ ε := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ih (ε / 4) hε4)
  have hR := primeSum_integral (a := n) (b := n + 1) (G := 1) (g := fun w => dickman (w - 1))
    hn0 (by linarith) (fun v _ w _ hvw => dickman_antitone (sub_le_sub_right hvw 1))
    (fun w _ => (dickman_pos _).le) (fun w _ => dickman_le_one _)
    (dickman_continuous.comp (continuous_sub_right 1)).continuousOn hε4
  filter_upwards [eventually_gt_atTop 1, hR,
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (n + 1))).eventually_ge_atTop 2,
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (max T 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (18 * (n + 1))] with x hx1 hRx hx2 hsqT hLx u hu
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hu0 : 0 < u := by linarith [hu.1]
  have hsq1 : 1 ≤ Real.sqrt x := (le_max_right _ _).trans hsqT
  have hsqx : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left hx0.le]
    nlinarith
  have hxT : T ≤ x := ((le_max_left _ _).trans hsqT).trans hsqx
  -- Buchstab with `z = x^{1/n}`.
  have hB := buchstab_real (x := x) (y := x ^ (1 / u)) (z := x ^ (1 / (n : ℝ)))
    (Real.rpow_nonneg hx0.le _)
    (Real.rpow_le_rpow_of_exponent_le hx1.le (one_div_le_one_div_of_le hn0 hu.1))
  change (PsiR x (x ^ (1 / (n : ℝ))) : ℝ) = PsiR x (x ^ (1 / u)) +
    ∑ p ∈ primesBetween x n u, (PsiR (x / p) p : ℝ) at hB
  -- The induction hypothesis at `u = n`.
  have hIn := hT x hxT n ⟨by linarith, le_rfl⟩
  -- The induction hypothesis at `x/p`, for each prime in the range.
  have hper : ∀ p ∈ primesBetween x n u,
      |(PsiR (x / p) p : ℝ) / x - dickman (Real.log x / Real.log p - 1) / p| ≤
        ε / 4 * (1 / p) := fun p hp => by
    obtain ⟨hw1, hw2⟩ := log_div_log_mem hx1 hn0 hu.1 hp
    obtain ⟨hpp, hpx, -⟩ := (mem_primesBetween hx0.le).mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hv0 : Real.log x / Real.log p - 1 ≠ 0 := by linarith
    have hpsq : (p : ℝ) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      exact hpx.trans (Real.rpow_le_rpow_of_exponent_le hx1.le
        (one_div_le_one_div_of_le (by norm_num) hn2))
    have hxp : T ≤ x / p := by
      have : x / Real.sqrt x ≤ x / p := div_le_div_of_nonneg_left hx0.le hp0 hpsq
      rw [Real.div_sqrt] at this
      exact ((le_max_left _ _).trans hsqT).trans this
    have h := hT (x / p) hxp (Real.log x / Real.log p - 1)
      ⟨by linarith, by linarith [hu.2]⟩
    rw [div_rpow_log_div hx0 hp1 hv0] at h
    have e : (PsiR (x / p) p : ℝ) / x - dickman (Real.log x / Real.log p - 1) / p =
        ((PsiR (x / p) p : ℝ) / (x / p) - dickman (Real.log x / Real.log p - 1)) / p := by
      field_simp
    rw [e, abs_div, abs_of_pos hp0, div_eq_mul_one_div _ (p : ℝ)]
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hsum : |∑ p ∈ primesBetween x n u, (PsiR (x / p) p : ℝ) / x -
      ∑ p ∈ primesBetween x n u, dickman (Real.log x / Real.log p - 1) / p| ≤
      ε / 4 * ∑ p ∈ primesBetween x n u, (1 : ℝ) / p := by
    rw [← sum_sub_distrib, mul_sum]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper)
  -- `∑ 1/p ≤ 2` over the range.
  have hA : ∑ p ∈ primesBetween x n u, (1 : ℝ) / p ≤ 2 := by
    have hu2 : 2 ≤ x ^ (1 / u) :=
      hx2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (one_div_le_one_div_of_le hu0 hu.2))
    have h := (abs_le.mp (sum_primesBetween_inv hx1 hn0 hu.1 hu2)).2
    have hl : Real.log (u / n) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (div_pos hu0 hn0)
      have h' : u / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith [hu.2]
      linarith
    have hq : 18 * u / Real.log x ≤ 1 := by
      rw [div_le_iff₀ hL]
      linarith [hu.2]
    linarith
  have hR' : |∑ p ∈ primesBetween x n u, dickman (Real.log x / Real.log p - 1) / p -
      ∫ w in (n : ℝ)..u, dickman (w - 1) / w| ≤ ε / 4 := hRx u hu
  have hB' : (PsiR x (x ^ (1 / u)) : ℝ) / x = (PsiR x (x ^ (1 / (n : ℝ))) : ℝ) / x -
      ∑ p ∈ primesBetween x n u, (PsiR (x / p) p : ℝ) / x := by
    rw [← sum_div, hB]
    ring
  exact step_arith hε hB' (dickman_sub (by linarith) hu.1) hIn hsum hA hR'

/-- Dickman's theorem on `[1, n]`, for `n ≥ 2`. -/
theorem psi_dickman_nat (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε > 0, ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (1 : ℝ) n,
      |(PsiR x (x ^ (1 / u)) : ℝ) / x - dickman u| ≤ ε := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro ε hε
    simpa only [Nat.cast_ofNat] using psi_dickman_base hε
  | succ n hn ih =>
    intro ε hε
    filter_upwards [ih ε hε, psi_dickman_step hn ih hε] with x h1 h2 u hu
    rcases le_or_gt u n with h | h
    · exact h1 u ⟨hu.1, h⟩
    · exact h2 u ⟨h.le, by exact_mod_cast hu.2⟩

/-- **Lemma 2.2 (Dickman's theorem).** For every `U`, uniformly in `u ∈ [1, U]`,
`Ψ(x, x^{1/u})/x → ρ(u)` as `x → ∞`. -/
theorem dickman_asymptotic (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (1 : ℝ) U,
      |(PsiR x (x ^ (1 / u)) : ℝ) / x - dickman u| ≤ ε := by
  filter_upwards [psi_dickman_nat (⌈U⌉₊ + 2) (by omega) ε hε] with x hx u hu
  exact hx u ⟨hu.1, by push_cast; linarith [Nat.le_ceil U, hu.2]⟩

/-- **Lemma 2.2**, as uniform convergence on `[1, U]`. -/
theorem dickman_tendstoUniformlyOn (U : ℝ) :
    TendstoUniformlyOn (fun x u => (PsiR x (x ^ (1 / u)) : ℝ) / x) dickman atTop
      (Set.Icc 1 U) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [dickman_asymptotic U (half_pos hε)] with x hx u hu
  rw [dist_comm, Real.dist_eq]
  exact (hx u hu).trans_lt (half_lt_self hε)

/-- Pointwise: `Ψ(x, x^{1/u})/x → ρ(u)` for `u ≥ 1`. -/
theorem tendsto_psi_dickman {u : ℝ} (hu : 1 ≤ u) :
    Tendsto (fun x : ℝ => (PsiR x (x ^ (1 / u)) : ℝ) / x) atTop (𝓝 (dickman u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [dickman_asymptotic u (half_pos hε)] with x hx
  rw [Real.dist_eq]
  exact (hx u ⟨hu, le_rfl⟩).trans_lt (half_lt_self hε)

/-- **Lemma 2.3, consequence.** `ρ(u) ≤ 2/u` for `u ≥ 1`. -/
theorem dickman_le_two_div {u : ℝ} (hu : 1 ≤ u) : dickman u ≤ 2 / u := by
  have hu0 : 0 < u := by linarith
  set c₀ := Real.log 4 + 2 with hc₀
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim := (tendsto_psi_dickman hu).comp hN
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hup : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹ + 2 / u + 2 * c₀ / Real.log N) atTop
      (𝓝 (0 + 2 / u + 0)) :=
    ((tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)).add
      tendsto_const_nhds).add (tendsto_const_nhds.div_atTop hlog)
  rw [zero_add, add_zero] at hup
  refine le_of_tendsto_of_tendsto hlim hup ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set Y := ⌊(N : ℝ) ^ (1 / u)⌋₊ with hY
  have hY1 : 1 ≤ Y := Nat.le_floor (by
    push_cast
    exact Real.one_le_rpow (by linarith) (by positivity))
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hlogY : Real.log Y ≤ 1 / u * Real.log N := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log hY0 (Nat.floor_le (by positivity))
  have hpsi := psi_upper' hN2 hY1
  have hPsi : (PsiR (N : ℝ) ((N : ℝ) ^ (1 / u)) : ℝ) = psi N Y := by
    unfold PsiR
    rw [Nat.floor_natCast]
  show (PsiR (N : ℝ) ((N : ℝ) ^ (1 / u)) : ℝ) / N ≤
    (Real.sqrt N)⁻¹ + 2 / u + 2 * c₀ / Real.log N
  rw [hPsi, div_le_iff₀ hN0]
  have e1 : ((Real.sqrt N)⁻¹ + 2 / u + 2 * c₀ / Real.log N) * N =
      Real.sqrt N + 2 * N * (1 / u * Real.log N + c₀) / Real.log N := by
    have : (Real.sqrt N)⁻¹ * N = Real.sqrt N := by rw [inv_mul_eq_div, Real.div_sqrt]
    rw [add_assoc, add_mul, this]
    congr 1
    field_simp
  have e2 : 2 * N * (Real.log Y + c₀) / Real.log N ≤
      2 * N * (1 / u * Real.log N + c₀) / Real.log N :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hL.le
  rw [e1]
  linarith

/-- `ρ(u) → 0` as `u → ∞`. -/
theorem dickman_tendsto_zero : Tendsto dickman atTop (𝓝 0) := by
  have h2 : Tendsto (fun u : ℝ => 2 / u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun u => (dickman_pos u).le) ?_
  filter_upwards [eventually_ge_atTop 1] with u hu
  exact dickman_le_two_div hu

end HubRemoval
