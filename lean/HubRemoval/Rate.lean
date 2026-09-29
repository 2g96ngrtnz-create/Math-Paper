import HubRemoval.Asymptotics

/-!
# Theorems 1.2 and 1.3

`gap ρ N K = Ψ(N, N/(K+1)) − E[Φ_K]` in `𝒟_ρ(N, K)`. (As the paper notes,
`Ψ(N, N/(K+1)) = Ψ(N, B)` with `B = ⌊N/(K+1)⌋`, which is what `psi N (N / (K + 1))` counts.)

**Theorem 1.3 (Rate).** For every `ρ ∈ (0,1)` there is `N₀(ρ)` such that for all `N ≥ N₀(ρ)`
and all `0 ≤ K < N`, `0 ≤ Ψ(N, N/(K+1)) − E[Φ_K] ≤ 30N/log log N` (`thm_rate`).

**Theorem 1.2 (Main theorem).** `Φ_K ≤ Ψ(N, N/(K+1))` for every orientation, and
`max_{0 ≤ K < N} (Ψ(N, N/(K+1)) − E[Φ_K])/N → 0` (`thm_main`).

The proof of Theorem 1.3 is the paper's, with `ℓ = log log N`, `η = 1/ℓ`, `δ = 1/(8ℓ²)`,
`s₀ = max(1, ⌈log ℓ / log(1/λ)⌉)` and `z = N^{δ/s₀}`. `GoodT ρ (log N)` (conditions (R1)–(R6))
holds for all large `N` (`eventually_goodN`). Under it (`gap_le_of_good`):
* **if `K ≤ N^{1−η}`**, the hypotheses of Lemma 4.5 hold. Proposition 4.6 with Lemma 4.1
  (`fixedN_sandwich'`) bounds the gap by `K + Err + N³e^{−q(N^{2δ}−2)}`, and each term is at most a
  multiple of `N/ℓ`: `K ≤ N/ℓ`, `N^{1−δ} ≤ N/ℓ`, `N(4δ/η + 38/(η log N)) ≤ N/ℓ`,
  `#{ω_z < s₀} ≤ 12N/L ≤ 24N/ℓ` (Lemmas 2.4 and 2.1(c)), `2λ^{s₀+1}N ≤ 2N/ℓ`, and the last term
  is `≤ 1`. The total is `29N/ℓ + 1 ≤ 30N/ℓ`;
* **if `K > N^{1−η}`**, then `B < N^η`, and Lemma 2.3 gives `Ψ(N, B) ≤ √N + 2N/ℓ + 2c₀N/log N
  ≤ 3N/ℓ`.
-/

namespace HubRemoval

open Finset Filter Topology

/-- The gap `Ψ(N, N/(K+1)) − E[Φ_K]`. -/
noncomputable def gap (ρ : ℝ) (N K : ℕ) : ℝ :=
  (psi N (N / (K + 1)) : ℝ) - expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ))

theorem expect_PhiK_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (N K : ℕ) :
    0 ≤ expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) :=
  calc (0 : ℝ) = expectP ρ (fun _ : Edge N K → Bool => (0 : ℝ)) := (expectP_const ρ 0).symm
    _ ≤ _ := expectP_mono hρ0 hρ1 fun _ => Nat.cast_nonneg _

/-- `0 ≤ gap`, from Proposition 3.2. -/
theorem gap_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (N K : ℕ) : 0 ≤ gap ρ N K :=
  sub_nonneg.mpr (expect_PhiK_le_psi hρ0 hρ1)

/-- `ℓ = log log N`. -/
noncomputable def ellN (N : ℕ) : ℝ := Real.log (Real.log N)

/-- The paper's parameters in the proof of Theorem 1.3: `η = 1/ℓ`, `δ = 1/(8ℓ²)`,
`s₀ = max(1, ⌈log ℓ/log(1/λ)⌉)`. -/
noncomputable def etaN (N : ℕ) : ℝ := 1 / ellN N
noncomputable def deltaN (N : ℕ) : ℝ := 1 / (8 * ellN N ^ 2)
noncomputable def s0N (ρ : ℝ) (N : ℕ) : ℕ := s0f ρ (ellN N)

/-- `Err` of Proposition 4.6, with `C₁ = 18`. -/
noncomputable def errT (ρ : ℝ) (N s₀ : ℕ) (η δ : ℝ) : ℝ :=
  (N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) +
    ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card +
    2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N

/-- **The two cases of the proof of Theorem 1.3.** Under (R1)–(R6) at `t = log N`, and for
`K < N`: `N/ℓ ≥ 1`, and
* if `K ≤ N^{1−η}`, the hypotheses of Lemma 4.5 hold, `K ≤ N/ℓ`, `Err ≤ 28N/ℓ` and
  `N³ exp(−q(N^{2δ} − 2)) ≤ 1`;
* if `K > N^{1−η}`, then `Ψ(N, B) ≤ 3N/ℓ`. -/
theorem rate_cases {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {N K : ℕ} (hK : K < N)
    (hG : GoodT ρ (Real.log N)) :
    1 ≤ (N : ℝ) / ellN N ∧
    ((K : ℝ) ≤ (N : ℝ) ^ (1 - etaN N) →
      CoreHyp N K (s0N ρ N) (etaN N) (deltaN N) ∧ (K : ℝ) ≤ N / ellN N ∧
      errT ρ N (s0N ρ N) (etaN N) (deltaN N) ≤ 28 * N / ellN N ∧
      (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * deltaN N) - 2)) ≤ 1) ∧
    (¬ (K : ℝ) ≤ (N : ℝ) ^ (1 - etaN N) →
      (psi N (N / (K + 1)) : ℝ) ≤ 3 * (N / ellN N)) := by
  unfold etaN deltaN s0N ellN
  set t := Real.log (N : ℝ) with htdef
  set ℓ := Real.log t with hℓdef
  have hℓ1 : 1 < ℓ := hG.p0
  have hℓ0 : 0 < ℓ := by linarith
  -- `t > 1`, so `N ≥ 3`.
  have ht1 : 1 < t := by
    by_contra h
    push Not at h
    have h0 : 0 ≤ t := Real.log_natCast_nonneg N
    have : ℓ ≤ 0 := Real.log_nonpos h0 h
    linarith
  have hNpos : (0 : ℝ) < N := by
    by_contra h
    push Not at h
    have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    rw [htdef, this, Real.log_zero] at ht1
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by exact_mod_cast hNpos)
  have hN2 : 2 ≤ N := by
    have h : Real.exp 1 < N := by
      rw [← Real.exp_log hNpos]
      exact Real.exp_lt_exp.mpr ht1
    have := Real.exp_one_gt_d9
    have : (2 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hℓt : ℓ < t := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < t)]
  have htN : t < N := by linarith [Real.log_le_sub_one_of_pos hNpos]
  have hNℓ : 1 ≤ (N : ℝ) / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
  have hrpow : ∀ a : ℝ, (N : ℝ) ^ a = Real.exp (t * a) := fun a => Real.rpow_def_of_pos hNpos a
  have hle_rpow : ∀ c a : ℝ, 0 < c → Real.log c ≤ t * a → c ≤ (N : ℝ) ^ a := fun c a hc h => by
    rw [hrpow]
    calc c = Real.exp (Real.log c) := (Real.exp_log hc).symm
      _ ≤ Real.exp (t * a) := Real.exp_le_exp.mpr h
  -- The paper's parameters.
  set η := 1 / ℓ with hη
  set δ := 1 / (8 * ℓ ^ 2) with hδ
  set s₀ := s0f ρ ℓ with hs₀
  have hs₀1 : (1 : ℝ) ≤ s₀ := by exact_mod_cast one_le_s0f ρ ℓ
  -- `N^η ≥ ℓ` and `N^δ ≥ ℓ` (R3).
  have hNη : ℓ ≤ (N : ℝ) ^ η := hle_rpow ℓ η hℓ0 (by
    rw [hη, mul_one_div, le_div_iff₀ hℓ0]
    linarith [hG.p4])
  have hNδ : ℓ ≤ (N : ℝ) ^ δ := hle_rpow ℓ δ hℓ0 (by
    rw [hδ, mul_one_div, le_div_iff₀ (by positivity)]
    linarith [hG.p5])
  -- `N^{1−a} = N / N^a`.
  have hsub : ∀ a : ℝ, (N : ℝ) ^ (1 - a) = N / (N : ℝ) ^ a := fun a => by
    rw [Real.rpow_sub hNpos, Real.rpow_one]
  refine ⟨hNℓ, fun hKs => ?_, fun hKs => ?_⟩
  · ---------------- Case `K ≤ N^{1−η}`: Proposition 4.6.
    have hH2 : 4 ≤ (N : ℝ) ^ (η / 4) := hle_rpow 4 (η / 4) (by norm_num) (by
      rw [hη, show t * (1 / ℓ / 4) = t / (4 * ℓ) by ring, le_div_iff₀ (by positivity)]
      linarith [hG.p1])
    have hH3 : 2 ≤ (N : ℝ) ^ (δ / s₀) := hle_rpow 2 (δ / s₀) (by norm_num) (by
      rw [hδ, show t * (1 / (8 * ℓ ^ 2) / (s₀ : ℝ)) = t / (8 * ℓ ^ 2 * (s₀ : ℝ)) by ring,
        le_div_iff₀ (by positivity)]
      linarith [hG.p2])
    have h : CoreHyp N K s₀ η δ :=
      { η_pos := by rw [hη]; positivity
        η_lt_one := by rw [hη, div_lt_one hℓ0]; exact hℓ1
        s₀_pos := one_le_s0f ρ ℓ
        δ_pos := by rw [hδ]; positivity
        δ_le := by
          rw [hδ, hη, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        H1 := hKs
        H2 := hH2
        H3 := hH3 }
    -- `K ≤ N/ℓ`.
    have e1 : (K : ℝ) ≤ N / ℓ := by
      refine hKs.trans ?_
      rw [hsub]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hℓ0 hNη
    -- `N^{1−δ} ≤ N/ℓ`.
    have e2 : (N : ℝ) ^ (1 - δ) ≤ N / ℓ := by
      rw [hsub]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hℓ0 hNδ
    -- `N(4δ/η + 38/(η log N)) ≤ N/ℓ`.
    have e3 : (N : ℝ) * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) ≤ N / ℓ := by
      have h1 : 4 * δ / η = 1 / (2 * ℓ) := by rw [hδ, hη]; field_simp; ring
      have h2 : 2 * (1 + 18) / (η * Real.log N) ≤ 1 / (2 * ℓ) := by
        rw [← htdef, hη, show 2 * (1 + 18) / (1 / ℓ * t) = 38 * ℓ / t by field_simp; ring,
          div_le_div_iff₀ (by linarith) (by positivity)]
        nlinarith [hG.p6]
      rw [h1]
      calc (N : ℝ) * (1 / (2 * ℓ) + 2 * (1 + 18) / (η * Real.log N))
          ≤ N * (1 / (2 * ℓ) + 1 / (2 * ℓ)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N); linarith
        _ = N / ℓ := by field_simp; ring
    -- `#{m ≤ N : ω_z(m) < s₀} ≤ 24N/ℓ`, by Lemmas 2.4 and 2.1(c).
    set zR := (N : ℝ) ^ (δ / s₀) with hzR
    set zN := ⌊zR⌋₊ with hzN
    have hz2 : 2 ≤ zN := Nat.le_floor (by exact_mod_cast hH3)
    have hzle : zN ≤ N := by
      have h1 : zR ≤ N := by
        have := Real.rpow_le_rpow_of_exponent_le hN1
          (show δ / s₀ ≤ 1 by
            rw [div_le_one (by linarith)]
            rw [hδ, div_le_iff₀ (by positivity)]
            nlinarith)
        rwa [Real.rpow_one] at this
      have := Nat.floor_le_floor h1
      rwa [Nat.floor_natCast] at this
    have hL : Real.log (Real.log zR) - 13 ≤ (Lz zN : ℝ) := mertens_c hH3
    have hloglogz : Real.log (Real.log zR) = ℓ - Real.log (8 * ℓ ^ 2 * s₀) := by
      rw [hzR, Real.log_rpow hNpos, ← htdef,
        show δ / s₀ * t = t / (8 * ℓ ^ 2 * s₀) by rw [hδ]; field_simp,
        Real.log_div (by linarith) (by positivity)]
    have hp3 := hG.p3
    rw [← hℓdef] at hp3
    have hLbig : ℓ / 2 + 2 * s₀ ≤ (Lz zN : ℝ) := by linarith
    have hLpos : 0 < (Lz zN : ℝ) := by linarith
    have hturan := turan_count (z := zN) (N := N) hz2 hzle (s := (s₀ : ℝ)) (by linarith)
    have hfilt : (Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀) =
        (Ioc 0 N).filter (fun m => (omegaZ zN m : ℝ) < s₀) :=
      filter_congr fun m _ => by rw [hzN, hzR]; exact_mod_cast Iff.rfl
    have e4 : (((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card : ℝ) ≤
        24 * N / ℓ := by
      rw [hfilt]
      refine hturan.trans ?_
      rw [div_le_div_iff₀ hLpos hℓ0]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    -- `2λ^{s₀+1} N ≤ 2N/ℓ`.
    have e5 : 2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N ≤ 2 * N / ℓ := by
      have hlam := lam_pow_s0f_le hρ0 hρ1 hℓ0
      have hl0 : 0 ≤ lam ρ := by linarith [half_le_lam ρ]
      have hl1 : lam ρ ≤ 1 := (lam_lt_one hρ0 hρ1).le
      have : (max ρ (1 - ρ)) ^ (s₀ + 1) ≤ 1 / ℓ := by
        rw [pow_succ]
        calc (max ρ (1 - ρ)) ^ s₀ * max ρ (1 - ρ) ≤ (max ρ (1 - ρ)) ^ s₀ * 1 :=
              mul_le_mul_of_nonneg_left hl1 (pow_nonneg hl0 _)
          _ ≤ 1 / ℓ := by rw [mul_one]; exact hlam
      calc 2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N ≤ 2 * (1 / ℓ) * N := by
            apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N); linarith
        _ = 2 * N / ℓ := by ring
    -- `N³ exp(−q(N^{2δ} − 2)) ≤ 1` (R5).
    have e6 : (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2)) ≤ 1 := by
      have hN3 : (N : ℝ) ^ 3 = Real.exp (3 * t) := by
        rw [show (3 : ℝ) * t = Real.log ((N : ℝ) ^ 3) by rw [Real.log_pow, htdef]; norm_num,
          Real.exp_log (by positivity)]
      rw [hN3, hrpow, show t * (2 * δ) = t / (4 * ℓ ^ 2) by rw [hδ]; field_simp; ring,
        ← Real.exp_add]
      rw [Real.exp_le_one_iff]
      have := hG.p7
      rw [← hℓdef] at this
      linarith
    refine ⟨h, e1, ?_, e6⟩
    have e28 : (N : ℝ) / ℓ + N / ℓ + 24 * N / ℓ + 2 * N / ℓ = 28 * N / ℓ := by ring
    unfold errT
    linarith
  · ---------------- Case `K > N^{1−η}`: Lemma 2.3.
    push Not at hKs
    have hB1 : 1 ≤ N / (K + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hpsi := psi_upper' (x := N) (y := N / (K + 1)) hN2 hB1
    -- `B < N^η`, so `log B < t/ℓ`.
    have hBR : (0 : ℝ) < ((N / (K + 1) : ℕ) : ℝ) := by exact_mod_cast hB1
    have hBlt : ((N / (K + 1) : ℕ) : ℝ) < (N : ℝ) ^ η := by
      have h1 : ((N / (K + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((K : ℝ) + 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := K + 1)
        push_cast at this
        exact this
      have hpos : 0 < (N : ℝ) ^ (1 - η) := Real.rpow_pos_of_pos hNpos _
      have h2 : (N : ℝ) / ((K : ℝ) + 1) < N / (N : ℝ) ^ (1 - η) :=
        div_lt_div_of_pos_left hNpos hpos (by linarith)
      have h3 : (N : ℝ) / (N : ℝ) ^ (1 - η) = (N : ℝ) ^ η := by
        rw [div_eq_iff hpos.ne', ← Real.rpow_add hNpos, show η + (1 - η) = (1 : ℝ) by ring,
          Real.rpow_one]
      linarith
    have hlogB : Real.log ((N / (K + 1) : ℕ) : ℝ) < t / ℓ := by
      have := Real.log_lt_log hBR hBlt
      rwa [Real.log_rpow hNpos, ← htdef, hη, one_div_mul_eq_div] at this
    -- `√N ≤ N/(2ℓ)`.
    have hsqrt : Real.sqrt N = Real.exp (t / 2) := by
      rw [Real.sqrt_eq_rpow, hrpow]
      ring_nf
    have hs1 : Real.sqrt N ≤ N / (2 * ℓ) := by
      have hp8 := hG.p8
      rw [← hsqrt, ← hℓdef] at hp8
      have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
      rw [le_div_iff₀ (by positivity)]
      calc Real.sqrt N * (2 * ℓ) ≤ Real.sqrt N * Real.sqrt N :=
            mul_le_mul_of_nonneg_left hp8 (Real.sqrt_nonneg _)
        _ = N := hsq
    -- `2N(log B + c₀)/log N ≤ 2N/ℓ + N/(2ℓ)`.
    have hs2 : 2 * N * (Real.log ((N / (K + 1) : ℕ) : ℝ) + (Real.log 4 + 2)) / Real.log N ≤
        2 * N / ℓ + N / (2 * ℓ) := by
      rw [← htdef]
      have h9 := hG.p9
      rw [← hℓdef] at h9
      have hlB : Real.log ((N / (K + 1) : ℕ) : ℝ) * ℓ < t := by
        rwa [lt_div_iff₀ hℓ0] at hlogB
      have htpos : 0 < t := by linarith
      have hNt : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have ha : 2 * N * Real.log ((N / (K + 1) : ℕ) : ℝ) / t ≤ 2 * N / ℓ := by
        rw [div_le_div_iff₀ htpos hℓ0]
        have := mul_le_mul_of_nonneg_left hlB.le (show (0 : ℝ) ≤ 2 * N by positivity)
        linarith
      have hb : 2 * N * (Real.log 4 + 2) / t ≤ N / (2 * ℓ) := by
        rw [div_le_div_iff₀ htpos (by positivity)]
        have := mul_le_mul_of_nonneg_left h9 hNt
        linarith
      have e : 2 * N * (Real.log ((N / (K + 1) : ℕ) : ℝ) + (Real.log 4 + 2)) / t =
          2 * N * Real.log ((N / (K + 1) : ℕ) : ℝ) / t + 2 * N * (Real.log 4 + 2) / t := by
        ring
      linarith
    have hid : (N : ℝ) / (2 * ℓ) + (2 * N / ℓ + N / (2 * ℓ)) = 3 * (N / ℓ) := by
      field_simp; ring
    linarith

/-- **The core of Theorem 1.3.** Under (R1)–(R6) at `t = log N`, every `K < N` has
`gap ≤ 30N/log log N`. -/
theorem gap_le_of_good {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {N K : ℕ} (hK : K < N)
    (hG : GoodT ρ (Real.log N)) : gap ρ N K ≤ 30 * N / Real.log (Real.log N) := by
  obtain ⟨hNℓ, hsmall, hlarge⟩ := rate_cases hρ0 hρ1 hK hG
  have e30 : 30 * (N : ℝ) / ellN N = 30 * (N / ellN N) := by ring
  change gap ρ N K ≤ 30 * N / ellN N
  by_cases hKs : (K : ℝ) ≤ (N : ℝ) ^ (1 - etaN N)
  · obtain ⟨h, e1, e28, e6⟩ := hsmall hKs
    obtain ⟨hlow, -⟩ := fixedN_sandwich' h hρ0.le hρ1.le
    have e28' : 28 * (N : ℝ) / ellN N = 28 * (N / ellN N) := by ring
    unfold errT at e28
    unfold gap
    linarith
  · have hΨ := hlarge hKs
    have hEnn := expect_PhiK_nonneg hρ0.le hρ1.le N K
    unfold gap
    linarith

/-- **Theorem 1.3 (Rate).** For every `ρ ∈ (0,1)` there is `N₀` such that for all `N ≥ N₀` and all
`K < N`, `0 ≤ Ψ(N, N/(K+1)) − E[Φ_K] ≤ 30N/log log N`. -/
theorem thm_rate {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K < N,
      0 ≤ gap ρ N K ∧ gap ρ N K ≤ 30 * N / Real.log (Real.log N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_goodN hρ0 hρ1)
  exact ⟨N₀, fun N hN K hK =>
    ⟨gap_nonneg hρ0.le hρ1.le N K, gap_le_of_good hρ0 hρ1 hK (hN₀ N hN)⟩⟩

/-- **Theorem 1.2 (Main theorem).** For every orientation, `Φ_K ≤ Ψ(N, N/(K+1))`; and
`max_{0 ≤ K < N} (Ψ(N, N/(K+1)) − E[Φ_K])/N → 0` as `N → ∞`. -/
theorem thm_main {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∀ (N K : ℕ) (ω : Edge N K → Bool), PhiK N K ω ≤ psi N (N / (K + 1))) ∧
    Tendsto (fun N : ℕ => ⨆ K : Fin N, gap ρ N K / N) atTop (𝓝 0) := by
  refine ⟨fun N K ω => PhiK_le_psi ω, ?_⟩
  have hlim : Tendsto (fun N : ℕ => 30 / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_log_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun N =>
      Real.iSup_nonneg fun K => div_nonneg (gap_nonneg hρ0.le hρ1.le N K) (Nat.cast_nonneg N)
  · filter_upwards [eventually_goodN hρ0 hρ1, eventually_ge_atTop 1] with N hG hN1
    have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    refine ciSup_le fun K => ?_
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h := gap_le_of_good hρ0 hρ1 K.2 hG
    rw [div_le_iff₀ hNpos]
    calc gap ρ N K ≤ 30 * N / Real.log (Real.log N) := h
      _ = 30 / Real.log (Real.log N) * N := by ring

end HubRemoval
