import HubRemoval.Giant
import HubRemoval.Attack
import HubRemoval.RemarkEdges
import HubRemoval.RemarkSmallK

/-!
# Remark 5.2 (The term `K` in Corollary 1.5(c) is needed)

**Remark 5.2.** Fix `ρ ∈ (0, 1)` and let `K = K(N) → ∞` with `K ≤ √N/2`. Then for any rule `Φ*`
choosing a largest SCC, `liminf E[Φ^{(2)}_K]/K ≥ 1/2` (`remark_5_2`, stated as: for every `ε > 0`,
eventually `E[Φ^{(2)}_K] ≥ (1/2 − ε)K`).

*Proof.* For `N ≥ 16`, `B = ⌊N/(K+1)⌋ ≥ √N` and `(K + 1)² ≤ N` (`sqrt_le_B`). Take a prime
`p ∈ (B, 2B]` (Bertrand) and put `N' = ⌊N/p⌋`; then `K/2 ≤ N' ≤ K`. The map `s ↦ ps` sends the
edges of `G_{N'}` injectively to edges of `G_{N,K}` (`edgeMul`), and arcs to arcs
(`arc_edgeMul`). So `ω ↦ ω ∘ edgeMul` pushes `𝒟_ρ(N, K)` to `𝒟_ρ(N')` (`expectP_comp_injective`),
and the image of a largest strongly connected set of the copy lies in one SCC of `𝒟_ρ(N, K)`,
through the vertex `ps₀ ∉ F₁`. If `Φ_K > K`, the chosen largest SCC lies in `F₁`
(Proposition 3.2, Lemma 3.1(c)), so this other SCC counts for `Φ^{(2)}`. Hence
`Φ^{(2)} ≥ Φ_{N'}(ω ∘ edgeMul) − N'·1[Φ_K ≤ K]` (`secondSCC_ge`), and
`E[Φ^{(2)}] ≥ E[Φ_{N'}] − N'·P(Φ_K ≤ K)` (`expect_secondSCC_ge`).
By Remark 5.1's estimate, `Ψ(N, B) ≥ N/4` for large `N`, so Markov's inequality and Theorem 1.3
give `P(Φ_K ≤ K) ≤ 240/log log N` (`prob_PhiK_le_K`). Kim–Phillips' Corollary 2
(`kp_corollary_2`) gives `E[Φ_{N'}] ≥ (1 − ε/2)N'` once `N'` is large.
-/

namespace HubRemoval

open Finset Filter Topology

variable {N K p N' : ℕ}

/-! ### The copy of `G_{N'}` on `V_p` -/

/-- For `K < p` and `pN' ≤ N`, `s ↦ ps` maps vertices of `G_{N'}` to vertices of `G_{N,K}`. -/
theorem mul_mem_Ioc (hpK : K < p) (hpN : p * N' ≤ N) {s : ℕ} (hs : s ∈ Ioc 0 N') :
    p * s ∈ Ioc K N := by
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hs
  refine mem_Ioc.mpr ⟨?_, (Nat.mul_le_mul_left p h2).trans hpN⟩
  nlinarith

/-- For `K < p` and `pN' ≤ N`, `s ↦ ps` maps edges of `G_{N'}` to edges of `G_{N,K}`. -/
theorem mul_mem_edges (hpK : K < p) (hpN : p * N' ≤ N) {a b : ℕ} (h : (a, b) ∈ edges N' 0) :
    (p * a, p * b) ∈ edges N K := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_edges.mp h
  refine mem_edges.mpr ⟨?_, ?_, (Nat.mul_le_mul_left p h3).trans hpN, mul_dvd_mul_left p h4⟩
  · nlinarith
  · nlinarith

/-- The edge map `(a, b) ↦ (pa, pb)` from `G_{N'}` to `G_{N,K}`. -/
def edgeMul (hpK : K < p) (hpN : p * N' ≤ N) (e : Edge N' 0) : Edge N K :=
  ⟨(p * e.1.1, p * e.1.2), mul_mem_edges hpK hpN e.2⟩

theorem edgeMul_injective (hpK : K < p) (hpN : p * N' ≤ N) :
    Function.Injective (edgeMul hpK hpN) := by
  rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨a', b'⟩, hb⟩ h
  have h1 := congrArg Subtype.val h
  simp only [edgeMul, Prod.mk.injEq] at h1
  have hp : 0 < p := by omega
  exact Subtype.ext (Prod.ext (Nat.eq_of_mul_eq_mul_left hp h1.1)
    (Nat.eq_of_mul_eq_mul_left hp h1.2))

theorem bit_edgeMul (hpK : K < p) (hpN : p * N' ≤ N) (ω : Edge N K → Bool) {a b : ℕ}
    (h : (a, b) ∈ edges N' 0) : bit (ω ∘ edgeMul hpK hpN) a b = bit ω (p * a) (p * b) := by
  unfold bit
  simp only [h, mul_mem_edges hpK hpN h, ↓reduceDIte]
  rfl

/-- An arc of the copy is the image of an arc of `𝒟_ρ(N, K)`. -/
theorem arc_edgeMul (hpK : K < p) (hpN : p * N' ≤ N) {ω : Edge N K → Bool} {a b : ℕ}
    (h : arc (ω ∘ edgeMul hpK hpN) a b) : arc ω (p * a) (p * b) := by
  rcases h with ⟨he, hbit⟩ | ⟨he, hbit⟩
  · rw [bit_edgeMul hpK hpN ω he] at hbit
    exact Or.inl ⟨mul_mem_edges hpK hpN he, hbit⟩
  · rw [bit_edgeMul hpK hpN ω he] at hbit
    exact Or.inr ⟨mul_mem_edges hpK hpN he, hbit⟩

/-- Paths of the copy map to paths of `𝒟_ρ(N, K)`. -/
theorem reach_edgeMul (hpK : K < p) (hpN : p * N' ≤ N) {ω : Edge N K → Bool} {V : Finset ℕ}
    {a b : ℕ} (h : Relation.ReflTransGen (inducedArc (arc (ω ∘ edgeMul hpK hpN)) V) a b) :
    Relation.ReflTransGen (arc ω) (p * a) (p * b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih => exact ih.tail (arc_edgeMul hpK hpN hxy.2.2)

/-! ### The pointwise bound -/

/-- **The pointwise bound.** Let `p` be a prime with `B < p`, `K < p` and `pN' ≤ N`. For an SCC
`S` of size `Φ_K`, `Φ^{(2)} = secondSCC ω S ≥ Φ_{N'}(ω ∘ edgeMul) − N'·1[Φ_K ≤ K]`. -/
theorem secondSCC_ge (hpK : K < p) (hpN : p * N' ≤ N) (hp : p.Prime) (hpB : N / (K + 1) < p)
    {S : Finset ℕ} (ω : Edge N K → Bool) (hS : IsSCC ω S) (hcard : S.card = PhiK N K ω) :
    (PhiK N' 0 (ω ∘ edgeMul hpK hpN) : ℝ) - N' * (if PhiK N K ω ≤ K then 1 else 0) ≤
      secondSCC ω S := by
  have hle : (PhiK N' 0 (ω ∘ edgeMul hpK hpN) : ℝ) ≤ N' := by
    exact_mod_cast PhiK_le_N (ω ∘ edgeMul hpK hpN)
  split_ifs with hΦ
  · have h0 : (0 : ℝ) ≤ secondSCC ω S := Nat.cast_nonneg _
    linarith
  · push Not at hΦ
    rw [mul_zero, sub_zero]
    obtain ⟨v', hv', rfl⟩ := hS
    -- The chosen SCC lies in `F₁`.
    have hSF : sccOf ω v' ⊆ smoothFibre N K := by
      rcases sccOf_subset_or_card_le hv' with h | h
      · exact h
      · omega
    -- A largest strongly connected set `S'` of the copy.
    obtain ⟨S', hS', hS'card⟩ := exists_card_eq_maxSCC (arc (ω ∘ edgeMul hpK hpN)) (Ioc 0 N')
    rcases S'.eq_empty_or_nonempty with hE | ⟨s₀, hs₀⟩
    · have : PhiK N' 0 (ω ∘ edgeMul hpK hpN) = 0 := by
        unfold PhiK
        rw [← hS'card, hE, card_empty]
      rw [this, Nat.cast_zero]
      exact Nat.cast_nonneg _
    · have hv := mul_mem_Ioc hpK hpN (hS'.1 hs₀)
      -- The image of `S'` lies in the SCC of `p s₀`.
      have himg : S'.image (p * ·) ⊆ sccOf ω (p * s₀) := by
        intro w hw
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hw
        exact mem_sccOf.mpr ⟨mul_mem_Ioc hpK hpN (hS'.1 hs),
          reach_edgeMul hpK hpN (hS'.2 s₀ hs₀ s hs), reach_edgeMul hpK hpN (hS'.2 s hs s₀ hs₀)⟩
      have hcardimg : (S'.image (p * ·)).card = S'.card :=
        card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)
      -- `p s₀ ∉ F₁`, so the SCC of `p s₀` is not the chosen one.
      have hvF : p * s₀ ∉ smoothFibre N K := fun h => by
        have h2 := (mem_filter.mp h).2
        have := Nat.mem_smoothNumbers'.mp h2 p hp (dvd_mul_right p s₀)
        omega
      have hne : sccOf ω (p * s₀) ≠ sccOf ω v' := fun h =>
        hvF (hSF (h ▸ mem_sccOf_self hv))
      have hsec : (sccOf ω (p * s₀)).card ≤ secondSCC ω (sccOf ω v') := by
        unfold secondSCC
        exact Finset.le_sup (f := fun v => (sccOf ω v).card) (mem_filter.mpr ⟨hv, hne⟩)
      have : PhiK N' 0 (ω ∘ edgeMul hpK hpN) ≤ secondSCC ω (sccOf ω v') :=
        calc PhiK N' 0 (ω ∘ edgeMul hpK hpN) = S'.card := hS'card.symm
          _ = (S'.image (p * ·)).card := hcardimg.symm
          _ ≤ (sccOf ω (p * s₀)).card := card_le_card himg
          _ ≤ _ := hsec
      exact_mod_cast this

/-- **In expectation:** `E[Φ^{(2)}] ≥ E[Φ_{N'}] − N'·P(Φ_K ≤ K)`, where `E[Φ_{N'}]` is taken in
`𝒟_ρ(N')`. -/
theorem expect_secondSCC_ge {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hpK : K < p) (hpN : p * N' ≤ N)
    (hp : p.Prime) (hpB : N / (K + 1) < p) (star : (Edge N K → Bool) → Finset ℕ)
    (hstar : ∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK N K ω) :
    expectP ρ (fun ω : Edge N' 0 → Bool => (PhiK N' 0 ω : ℝ)) -
        N' * prob ρ (fun ω : Edge N K → Bool => PhiK N K ω ≤ K) ≤
      expectP ρ (fun ω : Edge N K → Bool => (secondSCC ω (star ω) : ℝ)) := by
  have hprob : prob ρ (fun ω : Edge N K → Bool => PhiK N K ω ≤ K) =
      expectP ρ (fun ω : Edge N K → Bool => if PhiK N K ω ≤ K then (1 : ℝ) else 0) := by
    rw [prob_eq]; rfl
  have h := expectP_mono hρ0 hρ1
    (fun ω => secondSCC_ge hpK hpN hp hpB ω (hstar ω).1 (hstar ω).2)
  rw [expectP_sub, expectP_const_mul,
    expectP_comp_injective ρ (edgeMul_injective hpK hpN) (fun ω' => (PhiK N' 0 ω' : ℝ))] at h
  rw [hprob]
  exact h

/-! ### The estimates for fixed `N` -/

/-- For `N ≥ 16` and `K ≤ √N/2`: `B = ⌊N/(K+1)⌋ ≥ √N` and `(K + 1)² ≤ N`. -/
theorem sqrt_le_B (hN16 : 16 ≤ N) (hKN : (K : ℝ) ≤ Real.sqrt N / 2) :
    Real.sqrt N ≤ ((N / (K + 1) : ℕ) : ℝ) ∧ (K + 1) ^ 2 ≤ N := by
  have hN : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hs4 : 4 ≤ Real.sqrt N := by nlinarith
  have hsq : (K + 1) ^ 2 ≤ N := by
    have : ((K : ℝ) + 1) ^ 2 ≤ N := by nlinarith
    exact_mod_cast this
  refine ⟨?_, hsq⟩
  have hlt : N < (K + 1) * (N / (K + 1) + 1) := Nat.lt_mul_div_succ N (by omega)
  have hltR : (N : ℝ) < ((K : ℝ) + 1) * (((N / (K + 1) : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
  by_contra hc
  push Not at hc
  have hB0 : (0 : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((K : ℝ) + 1) * (((N / (K + 1) : ℕ) : ℝ) + 1) ≤
      (Real.sqrt N / 2 + 1) * (((N / (K + 1) : ℕ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (Real.sqrt N / 2 + 1) * (((N / (K + 1) : ℕ) : ℝ) + 1) ≤
      (Real.sqrt N / 2 + 1) * (Real.sqrt N + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/-- **`P(Φ_K ≤ K) → 0`.** For `N ≥ 16` with `log N ≥ 1540`, `K ≤ √N/2` and (R1)–(R6) at `N`:
`Ψ(N, B) ≥ N/4`, and Markov's inequality with Theorem 1.3 gives `P(Φ_K ≤ K) ≤ 240/log log N`. -/
theorem prob_PhiK_le_K {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hN16 : 16 ≤ N)
    (hlogN : 1540 ≤ Real.log N) (hKN : (K : ℝ) ≤ Real.sqrt N / 2) (hG : GoodT ρ (Real.log N)) :
    prob ρ (fun ω : Edge N K → Bool => PhiK N K ω ≤ K) ≤ 240 / Real.log (Real.log N) := by
  obtain ⟨hB, hsq⟩ := sqrt_le_B hN16 hKN
  have hKlt : K < N := by nlinarith
  have hN : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0 : (0 : ℝ) < N := by linarith
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hs4 : 4 ≤ Real.sqrt N := by nlinarith
  -- `Ψ(N, B) ≥ N/4`, from Remark 5.1's estimate and `log(log N/log B) ≤ log 2`.
  have hpsi := smallK_psi hN16 hsq
  have hlogN0 : 0 < Real.log (N : ℝ) := by linarith
  have hlogB : 0 < Real.log ((N / (K + 1) : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hNB : (N : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ) ^ 2 := by nlinarith
  have h2 : Real.log N ≤ 2 * Real.log ((N / (K + 1) : ℕ) : ℝ) :=
    calc Real.log N ≤ Real.log (((N / (K + 1) : ℕ) : ℝ) ^ 2) := Real.log_le_log hN0 hNB
      _ = 2 * Real.log ((N / (K + 1) : ℕ) : ℝ) := by rw [Real.log_pow]; norm_num
  have h3 : Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ)) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hlogN0 hlogB) (by rw [div_le_iff₀ hlogB]; linarith)
  have h4 := Real.log_two_lt_d9
  have h5 : 77 / Real.log N ≤ 1 / 20 := by
    rw [div_le_iff₀ hlogN0]; linarith
  have hΨN : 1 / 4 ≤ (psi N (N / (K + 1)) : ℝ) / N := by
    have := (abs_le.mp hpsi).2
    linarith
  have hΨ : (N : ℝ) / 4 ≤ psi N (N / (K + 1)) := by
    rw [le_div_iff₀ hN0] at hΨN; linarith
  have hK8 : (K : ℝ) ≤ N / 8 := by nlinarith
  have hc : 0 < (psi N (N / (K + 1)) : ℝ) - K := by linarith
  -- Markov.
  have hmarkov := prob_ge_le hρ0.le hρ1.le
    (f := fun ω : Edge N K → Bool => (psi N (N / (K + 1)) : ℝ) - PhiK N K ω)
    (fun ω => sub_nonneg.mpr (by exact_mod_cast PhiK_le_psi ω)) hc
  have hmono : prob ρ (fun ω : Edge N K → Bool => PhiK N K ω ≤ K) ≤
      prob ρ (fun ω : Edge N K → Bool =>
        (psi N (N / (K + 1)) : ℝ) - K ≤ (psi N (N / (K + 1)) : ℝ) - PhiK N K ω) :=
    prob_mono hρ0.le hρ1.le fun ω h => by
      have : (PhiK N K ω : ℝ) ≤ K := by exact_mod_cast h
      linarith
  have hE : expectP ρ (fun ω : Edge N K → Bool => (psi N (N / (K + 1)) : ℝ) - PhiK N K ω) =
      gap ρ N K := by
    rw [expectP_sub, expectP_const]; rfl
  rw [hE] at hmarkov
  have hgap := gap_le_of_good hρ0 hρ1 hKlt hG
  have hℓ : 0 < Real.log (Real.log N) := by linarith [hG.p0]
  calc prob ρ (fun ω : Edge N K → Bool => PhiK N K ω ≤ K)
      ≤ gap ρ N K / ((psi N (N / (K + 1)) : ℝ) - K) := hmono.trans hmarkov
    _ ≤ (30 * N / Real.log (Real.log N)) / (N / 8) :=
        div_le_div₀ (div_nonneg (by positivity) hℓ.le) hgap (by positivity) (by linarith)
    _ = 240 / Real.log (Real.log N) := by field_simp; ring

/-- **The fixed-`N` bound.** For `N ≥ 16` and `K ≤ √N/2` there is `N'` with `K/2 ≤ N' ≤ K` and
`E[Φ^{(2)}] ≥ E[Φ_{N'}] − N'·P(Φ_K ≤ K)`. -/
theorem second_ge_fixed {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hN16 : 16 ≤ N)
    (hKN : (K : ℝ) ≤ Real.sqrt N / 2) (star : (Edge N K → Bool) → Finset ℕ)
    (hstar : ∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK N K ω) :
    ∃ N' : ℕ, K ≤ 2 * N' ∧ N' ≤ K ∧
      expectP ρ (fun ω : Edge N' 0 → Bool => (PhiK N' 0 ω : ℝ)) -
          N' * prob ρ (fun ω : Edge N K → Bool => PhiK N K ω ≤ K) ≤
        expectP ρ (fun ω : Edge N K → Bool => (secondSCC ω (star ω) : ℝ)) := by
  obtain ⟨hB, hsq⟩ := sqrt_le_B hN16 hKN
  have hN : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hs4 : 4 ≤ Real.sqrt N := by nlinarith
  have hB1 : 1 ≤ N / (K + 1) := by
    have : (1 : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨p, hp, hBp, hp2B⟩ := Nat.exists_prime_lt_and_le_two_mul (N / (K + 1)) (by omega)
  have hKB : K + 1 ≤ N / (K + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [← pow_two]; exact hsq)
  have hpK : K < p := by omega
  have hpN : p * (N / p) ≤ N := Nat.mul_div_le N p
  refine ⟨N / p, ?_, ?_, expect_secondSCC_ge hρ0 hρ1 hpK hpN hp hBp star hstar⟩
  · -- `K ≤ 2N'`: otherwise `N < p(N' + 1) ≤ 2B(N' + 1) ≤ B(K + 1) ≤ N`.
    have h1 : N < p * (N / p + 1) := Nat.lt_mul_div_succ N hp.pos
    have h2 : N / (K + 1) * (K + 1) ≤ N := Nat.div_mul_le_self N (K + 1)
    by_contra hc
    push Not at hc
    have h3 : p * (N / p + 1) ≤ 2 * (N / (K + 1)) * (N / p + 1) := Nat.mul_le_mul_right _ hp2B
    have h4 : 2 * (N / (K + 1)) * (N / p + 1) ≤ N / (K + 1) * (K + 1) := by
      have : 2 * (N / p + 1) ≤ K + 1 := by omega
      calc 2 * (N / (K + 1)) * (N / p + 1) = N / (K + 1) * (2 * (N / p + 1)) := by ring
        _ ≤ N / (K + 1) * (K + 1) := Nat.mul_le_mul_left _ this
    exact lt_irrefl N (h1.trans_le (h3.trans (h4.trans h2)))
  · -- `N' ≤ K`: otherwise `N < (B + 1)(K + 1) ≤ pN' ≤ N`.
    have h1 : N < (K + 1) * (N / (K + 1) + 1) := Nat.lt_mul_div_succ N (by omega)
    by_contra hc
    push Not at hc
    have h3 : (N / (K + 1) + 1) * (K + 1) ≤ p * (N / p) :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hBp) (Nat.succ_le_of_lt hc)
    exact lt_irrefl N (h1.trans_le (by rw [Nat.mul_comm]; exact h3.trans hpN))

/-! ### Remark 5.2 -/

/-- **Remark 5.2.** Fix `ρ ∈ (0, 1)` and let `K = K(N) → ∞` with `K ≤ √N/2` for large `N`. For
any rules `Φ*` choosing a largest SCC (whenever `K < N`, so that one exists),
`liminf E[Φ^{(2)}_K]/K ≥ 1/2`: for every `ε > 0`, eventually `E[Φ^{(2)}_K] ≥ (1/2 − ε)K`. -/
theorem remark_5_2 {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ}
    (hK : Tendsto K atTop atTop) (hKN : ∀ᶠ N in atTop, (K N : ℝ) ≤ Real.sqrt N / 2)
    (star : ∀ N, (Edge N (K N) → Bool) → Finset ℕ)
    (hstar : ∀ N, K N < N → ∀ ω, IsSCC ω (star N ω) ∧ (star N ω).card = PhiK N (K N) ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, (1 / 2 - ε) * K N ≤
      expectP ρ (fun ω : Edge N (K N) → Bool => (secondSCC ω (star N ω) : ℝ)) := by
  -- `E[Φ_{n,0}] > (1 − ε/2) n` for `n ≥ n₀` (Kim–Phillips' Corollary 2).
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((kp_corollary_2 hρ0 hρ1).eventually (lt_mem_nhds (show 1 - ε / 2 < 1 by linarith)))
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_nat
  filter_upwards [hKN, hK.eventually_ge_atTop (2 * n₀ + 2), eventually_goodN hρ0 hρ1,
    eventually_ge_atTop 16, tendsto_log_nat.eventually_ge_atTop 1540,
    hll.eventually_ge_atTop (960 / ε)] with N hkN hk0 hG hN16 hlogN hllN
  have hsec0 : 0 ≤ expectP ρ (fun ω : Edge N (K N) → Bool => (secondSCC ω (star N ω) : ℝ)) :=
    (expectP_const (ι := Edge N (K N)) ρ (0 : ℝ)).symm.le.trans
      (expectP_mono hρ0.le hρ1.le fun ω => Nat.cast_nonneg _)
  have hKlt : K N < N := by nlinarith [(sqrt_le_B hN16 hkN).2]
  obtain ⟨N', hN'1, hN'2, hmain⟩ :=
    second_ge_fixed hρ0.le hρ1.le hN16 hkN (star N) (hstar N hKlt)
  have hP := prob_PhiK_le_K hρ0 hρ1 hN16 hlogN hkN hG
  have hℓ : 0 < Real.log (Real.log N) := by linarith [hG.p0]
  have hP' : prob ρ (fun ω : Edge N (K N) → Bool => PhiK N (K N) ω ≤ K N) ≤ ε / 4 := by
    refine hP.trans ?_
    rw [div_le_iff₀ hℓ]
    rw [div_le_iff₀ hε] at hllN
    linarith
  have hN'n₀ : n₀ ≤ N' := by omega
  have hN'pos : (0 : ℝ) < N' := by exact_mod_cast (show 0 < N' by omega)
  have hE := hn₀ N' hN'n₀
  rw [lt_div_iff₀ hN'pos] at hE
  have hk2 : (K N : ℝ) ≤ 2 * N' := by exact_mod_cast hN'1
  have hPn := mul_le_mul_of_nonneg_left hP' hN'pos.le
  rcases le_or_gt (1 / 2 - ε) 0 with hε2 | hε2
  · nlinarith [Nat.cast_nonneg (α := ℝ) (K N)]
  · have h1 := mul_le_mul_of_nonneg_left hk2 hε2.le
    have h2 := mul_pos hε hN'pos
    linarith

end HubRemoval
