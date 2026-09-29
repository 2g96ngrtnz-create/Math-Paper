import HubRemoval.Attack
open HubRemoval Finset Filter Topology

/-! ### Corollary 1.6: axioms -/

#print axioms expectP_comp_injective
#print axioms arc_restrict
#print axioms maxSCC_restrict
#print axioms expect_maxSCC_Ioc
#print axioms tendsto_ratio_of_close
#print axioms abs_log_Kminus
#print axioms abs_log_Kplus
#print axioms eventually_lt_of_ratio
#print axioms eventually_sandwich_hyp
#print axioms expect_attack_sandwich
#print axioms attack_limit
#print axioms cor_degree_static
#print axioms cor_degree_adaptive
#print axioms static_eq_Icc
#print axioms exists_static
#print axioms isAdaptive_adaptSeq

/-! ### Marginals -/

/-- `ω ↦ (ω 2)` pushes the product measure on `Bool³` to the one on `Bool¹`. -/
example (g : (Fin 1 → Bool) → ℝ) :
    expectP (1 / 3) (fun ω : Fin 3 → Bool => g (ω ∘ fun _ : Fin 1 => (2 : Fin 3))) =
      expectP (1 / 3) g :=
  expectP_comp_injective _ (fun a b _ => Subsingleton.elim a b) g

/-- Removing the hubs `1, …, K` from `𝒟_ρ(N)` has the law of `𝒟_ρ(N, K)`. -/
example : expectP (1 / 2) (fun ω : Edge 12 0 → Bool => (maxSCC (arc ω) (Ioc 3 12) : ℝ)) =
    expectP (1 / 2) (fun ω : Edge 12 3 → Bool => (PhiK 12 3 ω : ℝ)) :=
  expect_maxSCC_Ioc _

/-! ### Attack sets exist -/

example : ∃ T ⊆ Icc 1 100, T.card = 3 ∧
    ∀ t ∈ T, ∀ v ∈ Icc 1 100, v ∉ T → deg 100 v ≤ deg 100 t :=
  exists_static 100 3 (by norm_num)

example : IsAdaptive 100 3 (adaptSeq 100) := isAdaptive_adaptSeq (by norm_num)

-- In `G_100`, the degrees of `1, …, 6` are `99, 50, 33, 26, 20, 18`, and every `v ≥ 4` has
-- degree `< 33`. So the only static top-3 set is `{1, 2, 3}`.
#guard (List.range 6).map (fun v => deg 100 (v + 1)) = [99, 50, 33, 26, 20, 18]
#guard (List.range 97).all (fun i => deg 100 (i + 4) < 33)

/-- The last claim, with `κ = 1/4`: for large `N` and `1 ≤ K ≤ N^{1/4}`, a static set is
`{1, …, K}`. -/
example : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (1 / 2 - 1 / 4 : ℝ) →
    ∀ T : Finset ℕ, T ⊆ Icc 1 N → T.card = K →
      (∀ t ∈ T, ∀ v ∈ Icc 1 N, v ∉ T → deg N v ≤ deg N t) → T = Icc 1 K :=
  static_eq_Icc (by norm_num) (by norm_num)

/-! ### Corollary 1.6, applied (`ρ = 1/2`, `K = ⌊√N⌋`, `θ = 1/2`) -/

/-- A static top-`⌊√N⌋` set of `G_N`. -/
noncomputable def staticSqrt (N : ℕ) : Finset ℕ :=
  Classical.choose (exists_static N (Nat.sqrt N) (Nat.sqrt_le_self N))

/-- Static attack on `⌊√N⌋` vertices: the giant tends to `1 − log 2 ≈ 30.7%`. -/
example : Tendsto (fun N : ℕ => expectP (1 / 2) (fun ω : Edge N 0 → Bool =>
    (maxSCC (arc ω) (Icc 1 N \ staticSqrt N) : ℝ)) / N) atTop (𝓝 (1 - Real.log 2)) := by
  have h := cor_degree_static (ρ := 1 / 2) (K := Nat.sqrt) (θ := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) tendsto_log_sqrt_succ (T := staticSqrt)
    (Eventually.of_forall fun N =>
      Classical.choose_spec (exists_static N (Nat.sqrt N) (Nat.sqrt_le_self N)))
  rwa [dickLim_of_le_half (by norm_num) (by norm_num),
    show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num] at h

/-- Adaptive attack on `⌊√N⌋` vertices: the same limit. -/
example : Tendsto (fun N : ℕ => expectP (1 / 2) (fun ω : Edge N 0 → Bool =>
    (maxSCC (arc ω) (Icc 1 N \ removedSet (adaptSeq N) (Nat.sqrt N)) : ℝ)) / N) atTop
    (𝓝 (1 - Real.log 2)) := by
  have h := cor_degree_adaptive (ρ := 1 / 2) (K := Nat.sqrt) (θ := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) tendsto_log_sqrt_succ (u := adaptSeq)
    (Eventually.of_forall fun N => isAdaptive_adaptSeq (Nat.sqrt_le_self N))
  rwa [dickLim_of_le_half (by norm_num) (by norm_num),
    show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num] at h
