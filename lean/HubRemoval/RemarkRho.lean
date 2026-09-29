import HubRemoval.Rate

/-!
# Remark 5.3 (Uniformity in `ρ`; slowly vanishing `ρ`)

**(a) Uniformity.** Let `0 < ρ₀ ≤ 1/2`. Theorems 1.2 and 1.3 hold uniformly for
`ρ ∈ [ρ₀, 1 − ρ₀]`, with `N₀ = N₀(ρ₀)` (`remark_5_3_uniform`, `remark_5_3_uniform_main`). The proof
depends on `ρ` only through `s₀` (via `λ = max(ρ, 1 − ρ) ≤ 1 − ρ₀`) and `q = ρ(1 − ρ) ≥ ρ₀(1 − ρ₀)`.
The growth conditions (R1)–(R6) at `ρ₀` imply those at `ρ` (`GoodT.mono`), since the ones that
involve `ρ` are monotone in `s₀` and in `q`.

**(b) Slowly vanishing `ρ`.** Theorem 1.2 remains true for `ρ = ρ_N` with
`min(ρ_N, 1 − ρ_N) log log N → ∞` (`remark_5_3_slow`). Proposition 4.6 is applied with fixed `η`,
`δ ≤ η/8` and `s₀ = ⌊¼ log log N⌋`. Then `λ^{s₀} ≤ exp(−min(ρ, 1−ρ) s₀) → 0`, the `ω_z` term is
`≤ 12N/L = o(N)`, and `N P(𝓡ᶜ) ≤ N³ exp(−q(N^{2δ} − 2)) → 0` because `q ≥ 1/(2 log log N)`. Letting
`η, δ → 0` gives the claim (`slow_rho_bound`: for each `ε > 0` there is `A` such that eventually
`gap ≤ εN` whenever `min(ρ, 1 − ρ) log log N ≥ A`).
-/

namespace HubRemoval

open Finset Filter Topology

/-! ### (a) Uniformity -/

theorem lam_le_of_mem {ρ₀ ρ : ℝ} (hρ₀h : ρ₀ ≤ 1 / 2) (hρ : ρ₀ ≤ ρ) (hρ' : ρ ≤ 1 - ρ₀) :
    lam ρ ≤ lam ρ₀ := by
  have : lam ρ₀ = 1 - ρ₀ := by unfold lam; exact max_eq_right (by linarith)
  rw [this]
  exact max_le hρ' (by linarith)

/-- `s₀` is monotone in `λ`. -/
theorem s0f_mono {ρ₀ ρ ℓ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀h : ρ₀ ≤ 1 / 2) (hρ : ρ₀ ≤ ρ)
    (hρ' : ρ ≤ 1 - ρ₀) (hℓ : 1 ≤ ℓ) : s0f ρ ℓ ≤ s0f ρ₀ ℓ := by
  unfold s0f
  refine max_le_max le_rfl (Nat.ceil_mono ?_)
  have hlam := lam_le_of_mem hρ₀h hρ hρ'
  have hlam0 : 0 < lam ρ := by linarith [half_le_lam ρ]
  have h1 : 0 < Real.log (1 / lam ρ₀) := log_inv_lam_pos hρ₀ (by linarith)
  have h2 : Real.log (1 / lam ρ₀) ≤ Real.log (1 / lam ρ) :=
    Real.log_le_log (by have := half_le_lam ρ₀; positivity) (one_div_le_one_div_of_le hlam0 hlam)
  exact div_le_div_of_nonneg_left (Real.log_nonneg hℓ) h1 h2

/-- **(R1)–(R6) at `ρ₀` imply (R1)–(R6) at every `ρ ∈ [ρ₀, 1 − ρ₀]`.** -/
theorem GoodT.mono {ρ₀ ρ t : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀h : ρ₀ ≤ 1 / 2) (hρ : ρ₀ ≤ ρ)
    (hρ' : ρ ≤ 1 - ρ₀) (h : GoodT ρ₀ t) : GoodT ρ t := by
  have hℓ : 1 < Real.log t := h.p0
  have hs := s0f_mono hρ₀ hρ₀h hρ hρ' hℓ.le (ℓ := Real.log t)
  have hsR : (s0f ρ (Real.log t) : ℝ) ≤ s0f ρ₀ (Real.log t) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s0f ρ (Real.log t) := by exact_mod_cast one_le_s0f ρ _
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have ht0 : 0 < t := by nlinarith [h.p1]
  have hq : ρ₀ * (1 - ρ₀) ≤ ρ * (1 - ρ) := by nlinarith
  have hq0 : 0 < ρ₀ * (1 - ρ₀) := by nlinarith
  have hE : 0 < Real.exp (t / (4 * Real.log t ^ 2)) - 2 := by
    by_contra hc
    push Not at hc
    have := h.p7
    nlinarith
  refine ⟨h.p0, h.p1, ?_, ?_, h.p4, h.p5, h.p6, ?_, h.p8, h.p9⟩
  · have := h.p2
    have hc : 0 ≤ 8 * Real.log 2 * Real.log t ^ 2 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hsR hc]
  · have := h.p3
    have hl : Real.log (8 * Real.log t ^ 2 * s0f ρ (Real.log t)) ≤
        Real.log (8 * Real.log t ^ 2 * s0f ρ₀ (Real.log t)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hsR (by positivity))
    linarith
  · have := h.p7
    nlinarith [mul_le_mul_of_nonneg_right hq hE.le]

/-- **Remark 5.3(a), Theorem 1.3 uniformly in `ρ`.** For `0 < ρ₀ ≤ 1/2` there is `N₀` such that
for all `N ≥ N₀`, all `ρ ∈ [ρ₀, 1 − ρ₀]` and all `K < N`,
`0 ≤ Ψ(N, N/(K+1)) − E[Φ_K] ≤ 30N/log log N`. -/
theorem remark_5_3_uniform {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀h : ρ₀ ≤ 1 / 2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ : ℝ, ρ₀ ≤ ρ → ρ ≤ 1 - ρ₀ → ∀ K < N,
      0 ≤ gap ρ N K ∧ gap ρ N K ≤ 30 * N / Real.log (Real.log N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_goodN hρ₀ (show ρ₀ < 1 by linarith))
  refine ⟨N₀, fun N hN ρ hρ hρ' K hK => ?_⟩
  have h0 : 0 < ρ := by linarith
  have h1 : ρ < 1 := by linarith
  exact ⟨gap_nonneg h0.le h1.le N K,
    gap_le_of_good h0 h1 hK ((hN₀ N hN).mono hρ₀ hρ₀h hρ hρ')⟩

/-- **Remark 5.3(a), Theorem 1.2 uniformly in `ρ`.** For every `ε > 0` there is `N₀` such that
`Ψ(N, N/(K+1)) − E[Φ_K] ≤ εN` for all `N ≥ N₀`, `ρ ∈ [ρ₀, 1 − ρ₀]` and `K < N`. -/
theorem remark_5_3_uniform_main {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀h : ρ₀ ≤ 1 / 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ : ℝ, ρ₀ ≤ ρ → ρ ≤ 1 - ρ₀ → ∀ K < N, gap ρ N K ≤ ε * N := by
  obtain ⟨N₁, hN₁⟩ := remark_5_3_uniform hρ₀ hρ₀h
  have hlim : Tendsto (fun N : ℕ => 30 / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_log_nat)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (ge_mem_nhds hε))
  refine ⟨max N₁ N₂, fun N hN ρ hρ hρ' K hK => ?_⟩
  have h := (hN₁ N (le_of_max_le_left hN) ρ hρ hρ' K hK).2
  have h2 := hN₂ N (le_of_max_le_right hN)
  calc gap ρ N K ≤ 30 * N / Real.log (Real.log N) := h
    _ = 30 / Real.log (Real.log N) * N := by ring
    _ ≤ ε * N := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg N)

/-! ### (b) Slowly vanishing `ρ` -/

/-- `max(ρ, 1 − ρ) = 1 − min(ρ, 1 − ρ)`. -/
theorem max_eq_one_sub_min (ρ : ℝ) : max ρ (1 - ρ) = 1 - min ρ (1 - ρ) := by
  rcases le_total ρ (1 - ρ) with h | h
  · rw [max_eq_right h, min_eq_left h]
  · rw [max_eq_left h, min_eq_right h]; ring

/-- `λ^s ≤ exp(−min(ρ, 1 − ρ) s)`. -/
theorem lam_pow_le_exp {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (s : ℕ) :
    (max ρ (1 - ρ)) ^ s ≤ Real.exp (-(min ρ (1 - ρ) * s)) := by
  rw [max_eq_one_sub_min]
  have hm0 : 0 ≤ min ρ (1 - ρ) := le_min hρ0 (by linarith)
  have hm1 : min ρ (1 - ρ) ≤ 1 := (min_le_left _ _).trans hρ1
  calc (1 - min ρ (1 - ρ)) ^ s ≤ (Real.exp (-min ρ (1 - ρ))) ^ s :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-min ρ (1 - ρ))]) s
    _ = Real.exp (-(min ρ (1 - ρ) * s)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- `q = ρ(1 − ρ) ≥ min(ρ, 1 − ρ)/2`. -/
theorem q_ge_half_min {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    min ρ (1 - ρ) / 2 ≤ ρ * (1 - ρ) := by
  rcases le_total ρ (1 - ρ) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- `N^{1−a} ≤ (ε/8) N` once `N^a ≥ 8/ε`. -/
theorem rpow_one_sub_le {N a ε : ℝ} (hN0 : 0 < N) (hε : 0 < ε) (h : 8 / ε ≤ N ^ a) :
    N ^ (1 - a) ≤ ε / 8 * N := by
  have hNa : 0 < N ^ a := Real.rpow_pos_of_pos hN0 a
  have h1 : 8 ≤ N ^ a * ε := (div_le_iff₀ hε).mp h
  have h2 := mul_le_mul_of_nonneg_left h1 hN0.le
  rw [Real.rpow_sub hN0, Real.rpow_one, div_le_iff₀ hNa]
  linarith

/-- The `λ^{s₀+1}` term: `2λ^{s₀+1} ≤ ε/8` once `min(ρ, 1 − ρ) ℓ ≥ 8 log(16/ε) + 8` and
`s₀ ≥ ℓ/8`. -/
theorem slow_lam_term {ε ρ ℓ : ℝ} {s₀ : ℕ} (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hmℓ : 8 * Real.log (16 / ε) + 8 ≤ min ρ (1 - ρ) * ℓ) (hs₀ : ℓ / 8 ≤ (s₀ : ℝ)) :
    2 * (max ρ (1 - ρ)) ^ (s₀ + 1) ≤ ε / 8 := by
  have hm0 : 0 < min ρ (1 - ρ) := lt_min hρ0 (by linarith)
  have h1 := lam_pow_le_exp hρ0.le hρ1.le (s₀ + 1)
  have h4 := mul_le_mul_of_nonneg_left hs₀ hm0.le
  have h3 : Real.log (16 / ε) ≤ min ρ (1 - ρ) * ((s₀ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h2 : Real.exp (-(min ρ (1 - ρ) * ((s₀ + 1 : ℕ) : ℝ))) ≤ ε / 16 :=
    calc Real.exp (-(min ρ (1 - ρ) * ((s₀ + 1 : ℕ) : ℝ))) ≤ Real.exp (-Real.log (16 / ε)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ε / 16 := by rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hε), inv_div]
  linarith

/-- `q = ρ(1 − ρ) ≥ 1/(2ℓ)` once `min(ρ, 1 − ρ) ℓ ≥ 1`. -/
theorem slow_q {ρ ℓ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hℓ : 0 < ℓ)
    (hmℓ : 1 ≤ min ρ (1 - ρ) * ℓ) : 1 / (2 * ℓ) ≤ ρ * (1 - ρ) := by
  have h1 := q_ge_half_min hρ0.le hρ1.le
  have h2 : 1 / ℓ ≤ min ρ (1 - ρ) := by rw [div_le_iff₀ hℓ]; exact hmℓ
  calc 1 / (2 * ℓ) = 1 / ℓ / 2 := by rw [div_div, mul_comm]
    _ ≤ min ρ (1 - ρ) / 2 := by linarith
    _ ≤ ρ * (1 - ρ) := h1

/-- The exponential term: `N³ exp(−q(N^{2δ} − 2)) ≤ εN/8` once `q ≥ 1/(2ℓ)` and
`N^{2δ} ≥ ((6 + 2c)/(4δ²)) (log N^{2δ})²` with `c = log(8/ε)`. -/
theorem slow_exp_term {ε ρ δ ℓ : ℝ} {N : ℕ} (hε : 0 < ε) (hε8 : ε ≤ 8) (hN0 : (0 : ℝ) < N)
    (hδ0 : 0 < δ) (hℓ0 : 0 < ℓ) (hℓt : ℓ ≤ Real.log N) (ht1 : 1 ≤ Real.log N)
    (hq : 1 / (2 * ℓ) ≤ ρ * (1 - ρ))
    (e9 : (6 + 2 * Real.log (8 / ε)) / (4 * δ ^ 2) * Real.log ((N : ℝ) ^ (2 * δ)) ^ 2 ≤
      (N : ℝ) ^ (2 * δ)) :
    (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2)) ≤ ε / 8 * N := by
  obtain ⟨t, ht⟩ : ∃ t, Real.log N = t := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, Real.log (8 / ε) = c := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, (N : ℝ) ^ (2 * δ) = X := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  rw [ht] at hℓt ht1
  rw [Real.log_rpow hN0, ht, hc, hX] at e9
  rw [hX]
  have h4 : (6 + 2 * c) / (4 * δ ^ 2) * (2 * δ * t) ^ 2 = (6 + 2 * c) * t ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_iff (mul_pos (by norm_num) (pow_pos hδ0 2)).ne']
    ring
  rw [h4] at e9
  have h1 : 2 * ℓ * (2 * t + c) ≤ 2 * t * (2 * t + c) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : 1 ≤ t ^ 2 := by nlinarith
  have h3 : c * t ≤ c * t ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc0
  have hbig : 2 * ℓ * (2 * t + c) ≤ X - 2 := by linarith
  have hX0 : 0 ≤ X - 2 := le_trans (mul_nonneg (by linarith) (by linarith)) hbig
  have hexp : 2 * t + c ≤ ρ * (1 - ρ) * (X - 2) :=
    calc 2 * t + c = 1 / (2 * ℓ) * (2 * ℓ * (2 * t + c)) := by
          rw [one_div, ← mul_assoc, inv_mul_cancel₀ (by linarith : (0 : ℝ) < 2 * ℓ).ne',
            one_mul]
      _ ≤ 1 / (2 * ℓ) * (X - 2) :=
          mul_le_mul_of_nonneg_left hbig (div_nonneg zero_le_one (by linarith))
      _ ≤ ρ * (1 - ρ) * (X - 2) := mul_le_mul_of_nonneg_right hq hX0
  have hNe : Real.exp t = N := by rw [← ht]; exact Real.exp_log hN0
  have hN3 : (N : ℝ) ^ 3 = Real.exp (3 * t) := by
    rw [← hNe, ← Real.exp_nat_mul]; norm_num
  have hce : Real.exp (-c) = ε / 8 := by
    rw [Real.exp_neg, ← hc, Real.exp_log (div_pos (by norm_num) hε), inv_div]
  calc (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * (X - 2))
      = Real.exp (3 * t + -(ρ * (1 - ρ)) * (X - 2)) := by rw [hN3, Real.exp_add]
    _ ≤ Real.exp (-c + t) := Real.exp_le_exp.mpr (by linarith)
    _ = ε / 8 * N := by rw [Real.exp_add, hce, hNe]

/-- The `ω_z` term: `#{m ≤ N : ω_z(m) < s₀} ≤ εN/8`, via Lemmas 2.4 and 2.1(c). -/
theorem slow_turan_term {ε δ t ℓ : ℝ} {N s₀ : ℕ} (hε : 0 < ε) (hN1 : (1 : ℝ) ≤ N)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : Real.log N = t) (hℓ : Real.log t = ℓ) (ht0 : 0 < t)
    (hs₀1 : 1 ≤ s₀) (hs₀le : (s₀ : ℝ) ≤ ℓ / 4) (hℓε : 192 / ε ≤ ℓ)
    (hH3 : 2 ≤ (N : ℝ) ^ (δ / s₀))
    (e4 : 4 * Real.log ℓ ≤ ℓ) (e4' : 4 * (13 - Real.log δ) ≤ ℓ) :
    (((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card : ℝ) ≤
      ε / 8 * N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hs₀R : (1 : ℝ) ≤ s₀ := by exact_mod_cast hs₀1
  have h192 : 0 < 192 / ε := div_pos (by norm_num) hε
  obtain ⟨zR, hzR⟩ : ∃ zR, (N : ℝ) ^ (δ / s₀) = zR := ⟨_, rfl⟩
  rw [hzR] at hH3 ⊢
  have hz2 : 2 ≤ ⌊zR⌋₊ := Nat.le_floor (by exact_mod_cast hH3)
  have hzle : ⌊zR⌋₊ ≤ N := by
    have h1 : zR ≤ N := by
      rw [← hzR]
      have := Real.rpow_le_rpow_of_exponent_le hN1
        (show δ / s₀ ≤ 1 by rw [div_le_one (by linarith)]; linarith)
      rwa [Real.rpow_one] at this
    have := Nat.floor_le_floor h1
    rwa [Nat.floor_natCast] at this
  have hL : Real.log (Real.log zR) - 13 ≤ (Lz ⌊zR⌋₊ : ℝ) := mertens_c hH3
  have hloglogz : Real.log (Real.log zR) = Real.log δ + ℓ - Real.log s₀ := by
    rw [← hzR, Real.log_rpow hN0, ht, show δ / s₀ * t = δ * t / s₀ by ring,
      Real.log_div (mul_pos hδ0 ht0).ne' (show (0 : ℝ) < s₀ by linarith).ne',
      Real.log_mul hδ0.ne' ht0.ne', hℓ]
  have hlogs : Real.log s₀ ≤ Real.log ℓ := Real.log_le_log (by linarith) (by linarith)
  have hLbig : ℓ / 2 ≤ (Lz ⌊zR⌋₊ : ℝ) := by linarith
  have hLpos : 0 < (Lz ⌊zR⌋₊ : ℝ) := by linarith
  have hturan := turan_count hz2 hzle (s := (s₀ : ℝ)) (by linarith)
  have hfilt : (Ioc 0 N).filter (fun m => omegaZ ⌊zR⌋₊ m < s₀) =
      (Ioc 0 N).filter (fun m => (omegaZ ⌊zR⌋₊ m : ℝ) < s₀) :=
    filter_congr fun m _ => by exact_mod_cast Iff.rfl
  rw [hfilt]
  refine hturan.trans ?_
  rw [div_le_iff₀ hLpos]
  have h1 : 192 ≤ ε * ℓ := by rw [div_le_iff₀ hε] at hℓε; linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hN0.le
  have h3 := mul_le_mul_of_nonneg_left hLbig (mul_nonneg (by linarith : (0 : ℝ) ≤ ε / 8) hN0.le)
  linarith

/-- Remark 5.3(b), the case `K ≤ N^{1−η}`: Proposition 4.6 with `η = ε/4`, `δ = εη/32` and
`s₀ ≈ ℓ/4`; each of the seven error terms is `≤ εN/8`. -/
theorem slow_small_case {ε η δ ρ t ℓ : ℝ} {N K s₀ : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : η = ε / 4) (hδ : δ = ε * η / 32) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hN1 : (1 : ℝ) ≤ N) (ht : Real.log N = t) (hℓ : Real.log t = ℓ) (ht1 : 1 ≤ t)
    (hℓt : ℓ ≤ t) (hs₀1 : 1 ≤ s₀) (hs₀le : (s₀ : ℝ) ≤ ℓ / 4) (hℓε : 192 / ε ≤ ℓ)
    (hq : 1 / (2 * ℓ) ≤ ρ * (1 - ρ)) (hlam : 2 * (max ρ (1 - ρ)) ^ (s₀ + 1) ≤ ε / 8)
    (hKs : (K : ℝ) ≤ (N : ℝ) ^ (1 - η)) (e2 : 4 ≤ (N : ℝ) ^ (η / 4))
    (e3 : Real.log 2 / δ * ℓ ≤ t) (e4 : 4 * Real.log ℓ ≤ ℓ) (e4' : 4 * (13 - Real.log δ) ≤ ℓ)
    (e6 : 8 / ε ≤ (N : ℝ) ^ η) (e7 : 8 / ε ≤ (N : ℝ) ^ δ) (e8 : 304 / (η * ε) ≤ t)
    (e9 : (6 + 2 * Real.log (8 / ε)) / (4 * δ ^ 2) * Real.log ((N : ℝ) ^ (2 * δ)) ^ 2 ≤
      (N : ℝ) ^ (2 * δ)) :
    gap ρ N K ≤ ε * N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδη : δ ≤ η / 8 := by rw [hδ]; nlinarith
  have hη1 : η < 1 := by rw [hη]; linarith
  have hδ1 : δ ≤ 1 := by linarith
  have ht0 : 0 < t := by linarith
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (div_pos (by norm_num) hε) hℓε
  have hs₀R : (1 : ℝ) ≤ s₀ := by exact_mod_cast hs₀1
  have hH3 : 2 ≤ (N : ℝ) ^ (δ / s₀) := by
    rw [Real.rpow_def_of_pos hN0, ht]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (t * (δ / s₀)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [mul_div_assoc', le_div_iff₀ (by linarith)]
        rw [div_mul_eq_mul_div, div_le_iff₀ hδ0] at e3
        have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have := mul_le_mul_of_nonneg_left (show (s₀ : ℝ) ≤ ℓ by linarith) hl2
        linarith
  have h : CoreHyp N K s₀ η δ := ⟨hη0, hη1, hs₀1, hδ0, hδη, hKs, e2, hH3⟩
  obtain ⟨hlow, -⟩ := fixedN_sandwich' h hρ0.le hρ1.le
  have t1 : (K : ℝ) ≤ ε / 8 * N := hKs.trans (rpow_one_sub_le hN0 hε e6)
  have t2 : (N : ℝ) ^ (1 - δ) ≤ ε / 8 * N := rpow_one_sub_le hN0 hε e7
  have t3 : (N : ℝ) * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) ≤ 2 * (ε / 8) * N := by
    have h1 : 4 * δ / η = ε / 8 := by rw [hδ, div_eq_iff hη0.ne']; ring
    have h2 : 2 * (1 + 18) / (η * Real.log N) ≤ ε / 8 := by
      rw [ht, div_le_iff₀ (mul_pos hη0 ht0)]
      rw [div_le_iff₀ (mul_pos hη0 hε)] at e8
      linarith
    calc (N : ℝ) * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) ≤ N * (2 * (ε / 8)) :=
          mul_le_mul_of_nonneg_left (by linarith) hN0.le
      _ = 2 * (ε / 8) * N := by ring
  have t4 := slow_turan_term hε hN1 hδ0 hδ1 ht hℓ ht0 hs₀1 hs₀le hℓε hH3 e4 e4'
  have t5 := slow_exp_term hε (by linarith) hN0 hδ0 hℓ0 (by rw [ht]; exact hℓt)
    (by rw [ht]; exact ht1) hq e9
  have t6 : 2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N ≤ ε / 8 * N :=
    mul_le_mul_of_nonneg_right hlam hN0.le
  unfold gap
  linarith

/-- Remark 5.3(b), the case `K > N^{1−η}`: then `Ψ(N, N/(K+1)) ≤ εN` by Lemma 2.3. -/
theorem slow_large_case {ε η ρ t : ℝ} {N K : ℕ} (hε : 0 < ε) (hη : η = ε / 4) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hN3 : 3 ≤ N) (hKN : K < N) (ht : Real.log N = t) (ht0 : 0 < t)
    (hKs : (N : ℝ) ^ (1 - η) < K) (e10 : 4 / ε ≤ (N : ℝ) ^ (1 / 2 : ℝ))
    (e11 : 8 * (Real.log 4 + 2) / ε ≤ t) :
    gap ρ N K ≤ ε * N := by
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hB1 : 1 ≤ N / (K + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hpsi := psi_upper' (x := N) (y := N / (K + 1)) (by omega) hB1
  have hBR : (0 : ℝ) < ((N / (K + 1) : ℕ) : ℝ) := by exact_mod_cast hB1
  have hlogB : Real.log ((N / (K + 1) : ℕ) : ℝ) < η * t := by
    have h1 : ((N / (K + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((K : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := K + 1)
      push_cast at this
      exact this
    have hpos : 0 < (N : ℝ) ^ (1 - η) := Real.rpow_pos_of_pos hN0 _
    have h2 : (N : ℝ) / ((K : ℝ) + 1) < N / (N : ℝ) ^ (1 - η) :=
      div_lt_div_of_pos_left hN0 hpos (by linarith)
    have h3 : (N : ℝ) / (N : ℝ) ^ (1 - η) = (N : ℝ) ^ η := by
      rw [div_eq_iff hpos.ne', ← Real.rpow_add hN0, show η + (1 - η) = (1 : ℝ) by ring,
        Real.rpow_one]
    have := Real.log_lt_log hBR (h1.trans_lt (h2.trans_eq h3))
    rwa [Real.log_rpow hN0, ht] at this
  have hsq : Real.sqrt N ≤ ε / 4 * N := by
    have h2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have h3 : 4 / ε ≤ Real.sqrt N := by rw [Real.sqrt_eq_rpow]; exact e10
    rw [div_le_iff₀ hε] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg (N : ℝ))
    have h5 : Real.sqrt N * (Real.sqrt N * ε) = N * ε := by rw [← mul_assoc, h2]
    linarith
  have hc0t : 2 * (Real.log 4 + 2) / t ≤ ε / 4 := by
    rw [div_le_iff₀ ht0]
    rw [div_le_iff₀ hε] at e11
    linarith
  have hE := expect_PhiK_nonneg hρ0.le hρ1.le N K
  have hΨ : (psi N (N / (K + 1)) : ℝ) ≤ ε * N := by
    rw [ht] at hpsi
    have e : 2 * N * (Real.log ((N / (K + 1) : ℕ) : ℝ) + (Real.log 4 + 2)) / t =
        2 * N * Real.log ((N / (K + 1) : ℕ) : ℝ) / t + 2 * (Real.log 4 + 2) / t * N := by ring
    have h1 : 2 * N * Real.log ((N / (K + 1) : ℕ) : ℝ) / t ≤ ε / 2 * N := by
      rw [div_le_iff₀ ht0]
      have := mul_le_mul_of_nonneg_left hlogB.le (by positivity : (0 : ℝ) ≤ 2 * N)
      rw [hη] at this
      linarith
    have h2 : 2 * (Real.log 4 + 2) / t * N ≤ ε / 4 * N := mul_le_mul_of_nonneg_right hc0t hN0.le
    linarith
  unfold gap
  linarith

/-- **The quantitative form of Remark 5.3(b).** For every `ε ∈ (0, 1]` there are `A` and `N₀` such
that for all `N ≥ N₀`, all `ρ ∈ (0, 1)` with `min(ρ, 1 − ρ) log log N ≥ A`, and all `K < N`,
`Ψ(N, N/(K+1)) − E[Φ_K] ≤ εN`. Here `A = 8 log(16/ε) + 8`. -/
theorem slow_rho_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      A ≤ min ρ (1 - ρ) * Real.log (Real.log N) → ∀ K < N, gap ρ N K ≤ ε * N := by
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε * η / 32 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hlog16 : 0 ≤ Real.log (16 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := tendsto_log_nat
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  -- The eventual conditions on `N`.
  have E1 := hll.eventually_ge_atTop (max 8 (192 / ε))
  have E2 := hN.eventually
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < η / 4)).eventually_ge_atTop 4)
  have E3 := hlog.eventually (eventually_mul_log_pow_le (Real.log 2 / δ) 1)
  have E4 := hll.eventually (eventually_mul_log_pow_le 4 1)
  have E4' := hll.eventually_ge_atTop (4 * (13 - Real.log δ))
  have E6 := hN.eventually ((tendsto_rpow_atTop hη0).eventually_ge_atTop (8 / ε))
  have E7 := hN.eventually ((tendsto_rpow_atTop hδ0).eventually_ge_atTop (8 / ε))
  have E8 := hlog.eventually_ge_atTop (max 1 (304 / (η * ε)))
  have E9 := hN.eventually ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 * δ)).eventually
    (eventually_mul_log_pow_le ((6 + 2 * Real.log (8 / ε)) / (4 * δ ^ 2)) 2))
  have E10 := hN.eventually
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (4 / ε))
  have E11 := hlog.eventually_ge_atTop (8 * (Real.log 4 + 2) / ε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((((E1.and E2).and (E3.and E4)).and
    ((E4'.and E6).and (E7.and E8))).and (((E9.and E10).and E11).and (eventually_ge_atTop 3)))
  refine ⟨8 * Real.log (16 / ε) + 8, N₀, fun N hN ρ hρ0 hρ1 hAm K hK => ?_⟩
  obtain ⟨⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩, ⟨⟨e4', e6⟩, ⟨e7, e8⟩⟩⟩ := (hN₀ N hN).1
  obtain ⟨⟨⟨e9, e10⟩, e11⟩, hN3⟩ := (hN₀ N hN).2
  simp only [pow_one] at e3 e4
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hℓ8 : 8 ≤ Real.log (Real.log N) := le_trans (le_max_left _ _) e1
  have hℓε : 192 / ε ≤ Real.log (Real.log N) := le_trans (le_max_right _ _) e1
  have ht1 : 1 ≤ Real.log N := le_trans (le_max_left _ _) e8
  have hℓt : Real.log (Real.log N) ≤ Real.log N := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < Real.log (N : ℝ) by linarith)]
  -- `s₀ = ⌊ℓ/4⌋`, with `ℓ/8 ≤ s₀ ≤ ℓ/4`.
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℕ, s = ⌊Real.log (Real.log N) / 4⌋₊ := ⟨_, rfl⟩
  have hs₀le : (s₀ : ℝ) ≤ Real.log (Real.log N) / 4 := by
    rw [hs₀]; exact Nat.floor_le (by linarith)
  have hs₀ge : Real.log (Real.log N) / 8 ≤ (s₀ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log (Real.log N) / 4)
    rw [← hs₀] at this
    linarith
  have hs₀1 : 1 ≤ s₀ := by
    have : (1 : ℝ) ≤ s₀ := by linarith
    exact_mod_cast this
  have hq := slow_q hρ0 hρ1 (by linarith)
    (by linarith : 1 ≤ min ρ (1 - ρ) * Real.log (Real.log N))
  have hlam := slow_lam_term hε hρ0 hρ1 hAm hs₀ge
  rcases le_or_gt (K : ℝ) ((N : ℝ) ^ (1 - η)) with hKs | hKs
  · exact slow_small_case hε hε1 hη hδ hρ0 hρ1 (by linarith) rfl rfl ht1 hℓt hs₀1 hs₀le hℓε hq
      hlam hKs e2 e3 e4 e4' e6 e7 (le_trans (le_max_right _ _) e8) e9
  · exact slow_large_case hε hη hρ0 hρ1 hN3 hK rfl (by linarith) hKs e10 e11

/-- **Remark 5.3(b).** Theorem 1.2 remains true for `ρ = ρ_N ∈ (0, 1)` with
`min(ρ_N, 1 − ρ_N) log log N → ∞`: `max_{K<N} (Ψ(N, N/(K+1)) − E[Φ_K])/N → 0`. -/
theorem remark_5_3_slow {ρ : ℕ → ℝ} (hρ : ∀ N, 0 < ρ N ∧ ρ N < 1)
    (hm : Tendsto (fun N : ℕ => min (ρ N) (1 - ρ N) * Real.log (Real.log N)) atTop atTop) :
    Tendsto (fun N : ℕ => ⨆ K : Fin N, gap (ρ N) N K / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := min (ε / 2) 1 with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) one_pos
  obtain ⟨A, N₀, hN₀⟩ := slow_rho_bound hε'0 (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hm.eventually_ge_atTop A)
  refine ⟨max (max N₀ N₁) 1, fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN1 : N₁ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hN1' : 1 ≤ N := le_of_max_le_right hN
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1'
  have hbound : ∀ K : Fin N, gap (ρ N) N K / N ≤ ε' := fun K => by
    rw [div_le_iff₀ hNpos]
    exact hN₀ N hN0 (ρ N) (hρ N).1 (hρ N).2 (hN₁ N hN1) K K.2
  have hsup : ⨆ K : Fin N, gap (ρ N) N K / N ≤ ε' := ciSup_le hbound
  have hnn : 0 ≤ ⨆ K : Fin N, gap (ρ N) N K / N :=
    Real.iSup_nonneg fun K => div_nonneg (gap_nonneg (hρ N).1.le (hρ N).2.le N K) hNpos.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have : ε' ≤ ε / 2 := min_le_left _ _
  linarith

end HubRemoval
