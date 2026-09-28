import HubRemoval.Profile
import HubRemoval.Sandwich
import HubRemoval.Divisor

/-!
# Removing the vertices of highest degree (paper, Corollary 1.5)

`𝒟_ρ(N)` is the random orientation of `G_N`, with outcomes `ω : Edge N 0 → Bool` (`G_{N,0} = G_N`).
For `T ⊆ [N]`, `#Φ(𝒟_ρ(N) − T)` is `maxSCC (arc ω) ([N] \ T)`.

**Corollary 1.5.** Fix `ρ ∈ (0, 1)`, and let `log(K + 1)/log N → θ ∈ [0, 1)`. Let `T = T(N)`
with `|T| = K` be chosen from `G_N` alone, by a static attack (`cor_degree_static`) or an
adaptive attack (`cor_degree_adaptive`). Then `E[#Φ(𝒟_ρ(N) − T)]/N → ρ(1/(1 − θ))`.
Moreover, for fixed `κ ∈ (0, 1/2)` and large `N`, if `1 ≤ K ≤ N^{1/2−κ}`, then a static set is
exactly `{1, …, K}` (`static_eq_Icc`).

*Proof.* Put `ε = 1/4` and `K_± = ⌊(1 ± ε)K⌋`. The divisor bound (Lemma 2.5, exponent
`(1 − θ)/2`) makes the hypothesis of Lemma 6.2 hold for large `N`
(`eventually_sandwich_hyp`). So `V_{N,K₊} ⊆ [N] \ T ⊆ V_{N,K₋}`. Lemma 6.1 gives
`Φ_{K₊} ≤ #Φ(𝒟_ρ(N) − T) ≤ Φ_{K₋}` pointwise, where `Φ_{K'}` is the largest SCC of `𝒟_ρ(N)`
restricted to `(K', N]`. That restriction has the law of `𝒟_ρ(N, K')`
(`expect_maxSCC_Ioc`, from `expectP_comp_injective`), so its mean is `E[Φ_{K'}]`. Finally
`log(K_± + 1)/log N → θ`, and Corollary 1.3 applies to `K_±`.

As `T` is a fixed function of `N`, it does not depend on the orientation.
-/

namespace HubRemoval

open Finset Filter Topology

/-! ### Marginals of the product measure -/

section Marginal

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **Marginals.** For an injection `j : ι' → ι`, `ω ↦ ω ∘ j` pushes the product measure on
`Bool^ι` to the product measure on `Bool^ι'`: `E[g(ω ∘ j)] = E[g]`. -/
theorem expectP_comp_injective (ρ : ℝ) {j : ι' → ι} (hj : Function.Injective j)
    (g : (ι' → Bool) → ℝ) :
    expectP ρ (fun ω : ι → Bool => g (ω ∘ j)) = expectP ρ g := by
  classical
  -- An extension of `σ : ι' → Bool` to `ι`.
  set ext : (ι' → Bool) → ι → Bool :=
    fun σ i => if h : ∃ i', j i' = i then σ h.choose else false with hextdef
  have hext : ∀ σ i', ext σ (j i') = σ i' := by
    intro σ i'
    have h : ∃ i'', j i'' = j i' := ⟨i', rfl⟩
    simp only [hextdef, h, ↓reduceDIte]
    exact congrArg σ (hj h.choose_spec)
  -- `P(ω ∘ j = σ) = wt σ`, a cylinder probability.
  have hcyl : ∀ σ : ι' → Bool, prob ρ (fun ω : ι → Bool => ω ∘ j = σ) = wt ρ σ := by
    intro σ
    have hiff : ∀ ω : ι → Bool, ω ∘ j = σ ↔ ∀ i ∈ univ.image j, ω i = ext σ i := by
      intro ω
      constructor
      · rintro rfl i hi
        obtain ⟨i', -, rfl⟩ := mem_image.mp hi
        rw [hext]
        rfl
      · intro h
        funext i'
        rw [Function.comp_apply, h (j i') (mem_image_of_mem j (mem_univ i')), hext]
    rw [prob_congr hiff, prob_cylinder, prod_image (fun a _ b _ hab => hj hab)]
    unfold wt
    exact Fintype.prod_congr _ _ fun i' => by rw [hext]
  have hsplit : ∀ ω : ι → Bool,
      g (ω ∘ j) = ∑ σ : ι' → Bool, g σ * (if ω ∘ j = σ then 1 else 0) := by
    intro ω
    rw [sum_eq_single (ω ∘ j)]
    · simp
    · intro σ _ hσ
      simp [Ne.symm hσ]
    · intro h
      exact absurd (mem_univ _) h
  calc expectP ρ (fun ω : ι → Bool => g (ω ∘ j))
      = expectP ρ (fun ω : ι → Bool => ∑ σ : ι' → Bool, g σ * (if ω ∘ j = σ then 1 else 0)) := by
        congr 1
        funext ω
        exact hsplit ω
    _ = ∑ σ : ι' → Bool, g σ * prob ρ (fun ω : ι → Bool => ω ∘ j = σ) := by
        rw [expectP_sum]
        refine sum_congr rfl fun σ _ => ?_
        rw [expectP_const_mul, prob_eq]
        rfl
    _ = expectP ρ g := by
        unfold expectP
        refine sum_congr rfl fun σ _ => ?_
        rw [hcyl]
        ring

end Marginal

/-! ### `𝒟_ρ(N)` restricted to `(K, N]` is `𝒟_ρ(N, K)` -/

variable {N K : ℕ}

theorem edges_subset_zero : edges N K ⊆ edges N 0 := fun e he => by
  obtain ⟨a, b⟩ := e
  obtain ⟨h1, h2, h3, h4⟩ := mem_edges.mp he
  exact mem_edges.mpr ⟨by omega, h2, h3, h4⟩

/-- The inclusion of the edges of `G_{N,K}` into those of `G_N`. -/
def edgeIncl (N K : ℕ) (e : Edge N K) : Edge N 0 := ⟨e.1, edges_subset_zero e.2⟩

theorem edgeIncl_injective : Function.Injective (edgeIncl N K) := fun _ _ h => by
  have := congrArg Subtype.val h
  exact Subtype.ext this

theorem mem_edges_iff_zero {a b : ℕ} (ha : K < a) : (a, b) ∈ edges N K ↔ (a, b) ∈ edges N 0 := by
  rw [mem_edges, mem_edges]
  constructor
  · rintro ⟨-, h2, h3, h4⟩
    exact ⟨by omega, h2, h3, h4⟩
  · rintro ⟨-, h2, h3, h4⟩
    exact ⟨ha, h2, h3, h4⟩

theorem bit_restrict {ω : Edge N 0 → Bool} {a b : ℕ} (h : (a, b) ∈ edges N K) :
    bit (ω ∘ edgeIncl N K) a b = bit ω a b := by
  unfold bit
  simp only [h, edges_subset_zero h, ↓reduceDIte]
  rfl

/-- Between vertices of `(K, N]`, the arcs of `𝒟_ρ(N)` and of its restriction agree. -/
theorem arc_restrict {ω : Edge N 0 → Bool} {a b : ℕ} (ha : a ∈ Ioc K N) (hb : b ∈ Ioc K N) :
    arc (ω ∘ edgeIncl N K) a b ↔ arc ω a b := by
  have haK := (mem_Ioc.mp ha).1
  have hbK := (mem_Ioc.mp hb).1
  unfold arc
  constructor
  · rintro (⟨h, hbit⟩ | ⟨h, hbit⟩)
    · rw [bit_restrict h] at hbit
      exact Or.inl ⟨edges_subset_zero h, hbit⟩
    · rw [bit_restrict h] at hbit
      exact Or.inr ⟨edges_subset_zero h, hbit⟩
  · rintro (⟨h, hbit⟩ | ⟨h, hbit⟩)
    · have h' := (mem_edges_iff_zero (N := N) (b := b) haK).mpr h
      rw [← bit_restrict h'] at hbit
      exact Or.inl ⟨h', hbit⟩
    · have h' := (mem_edges_iff_zero (N := N) (b := a) hbK).mpr h
      rw [← bit_restrict h'] at hbit
      exact Or.inr ⟨h', hbit⟩

/-- `#Φ` only sees the arcs inside `V`. -/
theorem maxSCC_le_of_imp {α : Type*} {D D' : α → α → Prop} {V : Finset α}
    (h : ∀ a ∈ V, ∀ b ∈ V, D a b → D' a b) : maxSCC D V ≤ maxSCC D' V := by
  obtain ⟨S, hS, hcard⟩ := exists_card_eq_maxSCC D V
  rw [← hcard]
  exact card_le_maxSCC ⟨hS.1, fun a ha b hb => Relation.ReflTransGen.mono
    (fun x y hxy => ⟨hxy.1, hxy.2.1, h x hxy.1 y hxy.2.1 hxy.2.2⟩) _ _ (hS.2 a ha b hb)⟩

/-- The largest SCC of `𝒟_ρ(N)` restricted to `(K, N]` is `Φ_K` of the restricted outcome. -/
theorem maxSCC_restrict (ω : Edge N 0 → Bool) :
    maxSCC (arc ω) (Ioc K N) = PhiK N K (ω ∘ edgeIncl N K) :=
  le_antisymm (maxSCC_le_of_imp fun _ ha _ hb h => (arc_restrict ha hb).mpr h)
    (maxSCC_le_of_imp fun _ ha _ hb h => (arc_restrict ha hb).mp h)

/-- **The restriction of `𝒟_ρ(N)` to `(K, N]` has the law of `𝒟_ρ(N, K)`**:
its largest SCC has mean `E[Φ_K]`. -/
theorem expect_maxSCC_Ioc (ρ : ℝ) :
    expectP ρ (fun ω : Edge N 0 → Bool => (maxSCC (arc ω) (Ioc K N) : ℝ)) =
      expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) := by
  have e : (fun ω : Edge N 0 → Bool => (maxSCC (arc ω) (Ioc K N) : ℝ)) =
      fun ω => (PhiK N K (ω ∘ edgeIncl N K) : ℝ) := funext fun ω => by rw [maxSCC_restrict]
  rw [e]
  exact expectP_comp_injective ρ edgeIncl_injective (fun ω' => (PhiK N K ω' : ℝ))

/-! ### The asymptotics of `K_±` -/

/-- If `log(K' + 1)` and `log(K + 1)` differ by a bounded amount, the ratios `log(· + 1)/log N`
have the same limit. -/
theorem tendsto_ratio_of_close {K K' : ℕ → ℕ} {θ c : ℝ}
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ))
    (hc : ∀ N, |Real.log ((K' N : ℝ) + 1) - Real.log ((K N : ℝ) + 1)| ≤ c) :
    Tendsto (fun N : ℕ => Real.log ((K' N : ℝ) + 1) / Real.log N) atTop (𝓝 θ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := tendsto_log_nat
  have h1 : Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have h2 : Tendsto (fun N : ℕ => -(c / Real.log N)) atTop (𝓝 0) := by simpa using h1.neg
  have hd : Tendsto (fun N : ℕ => (Real.log ((K' N : ℝ) + 1) - Real.log ((K N : ℝ) + 1)) /
      Real.log N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 ?_ ?_
    · filter_upwards [hlog.eventually_gt_atTop 0] with N hN
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (abs_le.mp (hc N)).1 hN.le
    · filter_upwards [hlog.eventually_gt_atTop 0] with N hN
      exact div_le_div_of_nonneg_right (abs_le.mp (hc N)).2 hN.le
  have := hθ.add hd
  rw [add_zero] at this
  refine this.congr fun N => ?_
  ring

/-- `K₋ = ⌊(1 − 1/4)K⌋`. -/
noncomputable def Kminus (k : ℕ) : ℕ := ⌊(1 - 1 / 4 : ℝ) * k⌋₊

/-- `K₊ = ⌊(1 + 1/4)K⌋`. -/
noncomputable def Kplus (k : ℕ) : ℕ := ⌊(1 + 1 / 4 : ℝ) * k⌋₊

theorem Kminus_le (k : ℕ) : Kminus k ≤ k := by
  have h : ((Kminus k : ℕ) : ℝ) ≤ (1 - 1 / 4 : ℝ) * k := Nat.floor_le (by positivity)
  have : ((Kminus k : ℕ) : ℝ) ≤ k := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact_mod_cast this

theorem le_Kplus (k : ℕ) : k ≤ Kplus k :=
  Nat.le_floor (by nlinarith [Nat.cast_nonneg (α := ℝ) k])

theorem abs_log_Kminus (k : ℕ) :
    |Real.log ((Kminus k : ℝ) + 1) - Real.log ((k : ℝ) + 1)| ≤ Real.log 4 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hup : (Kminus k : ℝ) + 1 ≤ k + 1 := by exact_mod_cast Nat.add_le_add_right (Kminus_le k) 1
  have hlow : ((k : ℝ) + 1) / 4 ≤ (Kminus k : ℝ) + 1 := by
    have h1 := Nat.sub_one_lt_floor ((1 - 1 / 4 : ℝ) * k)
    have h2 : (0 : ℝ) ≤ Kminus k := Nat.cast_nonneg _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      norm_num
      linarith
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      unfold Kminus
      linarith
  have hpos : (0 : ℝ) < ((k : ℝ) + 1) / 4 := by positivity
  have l1 := Real.log_le_log (by positivity) hup
  have l2 := Real.log_le_log hpos hlow
  rw [Real.log_div (by positivity) (by norm_num)] at l2
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]

theorem abs_log_Kplus (k : ℕ) :
    |Real.log ((Kplus k : ℝ) + 1) - Real.log ((k : ℝ) + 1)| ≤ Real.log 2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlow : (k : ℝ) + 1 ≤ (Kplus k : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (le_Kplus k) 1
  have hup : (Kplus k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by
    have : (Kplus k : ℝ) ≤ (1 + 1 / 4 : ℝ) * k := Nat.floor_le (by positivity)
    linarith
  have l1 := Real.log_le_log (by positivity) hlow
  have l2 := Real.log_le_log (by positivity) hup
  rw [Real.log_mul (by norm_num) (by positivity)] at l2
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

/-- If `log(K + 1)/log N → θ < 1`, then eventually `K < N`. -/
theorem eventually_lt_of_ratio {K : ℕ → ℕ} {θ : ℝ} (hθ1 : θ < 1)
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    ∀ᶠ N in atTop, K N < N := by
  filter_upwards [hθ.eventually_lt_const hθ1, eventually_ge_atTop 2] with N hN hN2
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [div_lt_one hL, Real.log_lt_log_iff (by positivity) (by positivity)] at hN
  have : ((K N + 1 : ℕ) : ℝ) < N := by push_cast; exact hN
  have := Nat.cast_lt.mp this
  omega

/-! ### The attacks -/

/-- **The hypothesis of Lemma 6.2 holds for large `N`**, with `ε = 1/4` and `τ = C N^α`,
`α = (1 − θ)/2` (Lemma 2.5). -/
theorem eventually_sandwich_hyp {K : ℕ → ℕ} {θ : ℝ} (hθ1 : θ < 1)
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    ∃ τ : ℕ → ℝ, ∀ᶠ N : ℕ in atTop, K N < N ∧
      (∀ n, 1 ≤ n → n ≤ N → (n.divisors.card : ℝ) ≤ τ N) ∧
      (1 ≤ K N → τ N + 5 ≤ (N : ℝ) / K N * ((1 / 4 : ℝ) / 2)) := by
  set α := (1 - θ) / 2 with hα
  set β := (1 + 3 * θ) / 4 with hβ
  set γ := (1 - θ) / 4 with hγ
  have hα0 : 0 < α := by rw [hα]; linarith
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hθβ : θ < β := by rw [hβ]; linarith
  have hsum : 1 - β = α + γ := by rw [hα, hβ, hγ]; ring
  obtain ⟨C, hC0, hC⟩ := divisor_bound hα0
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨fun N => C * (N : ℝ) ^ α, ?_⟩
  filter_upwards [eventually_lt_of_ratio hθ1 hθ, hθ.eventually_lt_const hθβ,
    eventually_ge_atTop 2, hN.eventually ((tendsto_rpow_atTop hγ0).eventually_ge_atTop (16 * C)),
    hN.eventually ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - β)).eventually_ge_atTop 80)]
    with N hKN hrat hN2 hNγ hNβ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  refine ⟨hKN, fun n hn hnN => ?_, fun hK1 => ?_⟩
  · -- `τ(n) ≤ C n^α ≤ C N^α`.
    have h1 := hC n (by omega)
    have h2 : (n : ℝ) ^ α ≤ (N : ℝ) ^ α :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnN) hα0.le
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0.le)
  · -- `K + 1 < N^β`, so `N/K ≥ N^{1−β} = N^α N^γ`.
    have hK0 : (0 : ℝ) < K N := by exact_mod_cast hK1
    have hKβ : (K N : ℝ) + 1 < (N : ℝ) ^ β := by
      rw [div_lt_iff₀ hL] at hrat
      rw [Real.lt_rpow_iff_log_lt (by positivity) hN0]
      linarith
    have hNK : (N : ℝ) ^ (1 - β) ≤ N / K N := by
      have e : (N : ℝ) ^ (1 - β) = N / (N : ℝ) ^ β := by
        rw [Real.rpow_sub hN0, Real.rpow_one]
      rw [e]
      exact div_le_div_of_nonneg_left hN0.le hK0 (by linarith)
    have hsplit : (N : ℝ) ^ (1 - β) = (N : ℝ) ^ α * (N : ℝ) ^ γ := by
      rw [hsum, Real.rpow_add hN0]
    have hα' : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN0 α
    have h1 : C * (N : ℝ) ^ α ≤ (N : ℝ) ^ (1 - β) / 16 := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hNγ hα'.le
      nlinarith
    show C * (N : ℝ) ^ α + 5 ≤ (N : ℝ) / K N * ((1 / 4 : ℝ) / 2)
    nlinarith

/-- **The coupling.** If `{v ≥ 1 : v ≤ (1 − ε)K} ⊆ T ⊆ {t ≤ (1 + ε)K}` (`ε = 1/4`), then
`E[Φ_{K₊}] ≤ E[#Φ(𝒟_ρ(N) − T)] ≤ E[Φ_{K₋}]`. -/
theorem expect_attack_sandwich {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {T : Finset ℕ}
    (hlow : ∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ (1 - 1 / 4) * K → v ∈ T)
    (hup : ∀ t ∈ T, (t : ℝ) ≤ (1 + 1 / 4) * K) :
    expectP ρ (fun ω : Edge N (Kplus K) → Bool => (PhiK N (Kplus K) ω : ℝ)) ≤
        expectP ρ (fun ω : Edge N 0 → Bool => (maxSCC (arc ω) (Icc 1 N \ T) : ℝ)) ∧
      expectP ρ (fun ω : Edge N 0 → Bool => (maxSCC (arc ω) (Icc 1 N \ T) : ℝ)) ≤
        expectP ρ (fun ω : Edge N (Kminus K) → Bool => (PhiK N (Kminus K) ω : ℝ)) := by
  have hsub1 : Ioc (Kplus K) N ⊆ Icc 1 N \ T := by
    intro v hv
    obtain ⟨hv1, hvN⟩ := mem_Ioc.mp hv
    refine mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, hvN⟩, fun hvT => ?_⟩
    have h := hup v hvT
    have : v ≤ Kplus K := Nat.le_floor h
    omega
  have hsub2 : Icc 1 N \ T ⊆ Ioc (Kminus K) N := by
    intro v hv
    obtain ⟨hvI, hvT⟩ := mem_sdiff.mp hv
    obtain ⟨hv1, hvN⟩ := mem_Icc.mp hvI
    refine mem_Ioc.mpr ⟨?_, hvN⟩
    by_contra hc
    push Not at hc
    have : (v : ℝ) ≤ (1 - 1 / 4) * K :=
      (Nat.cast_le.mpr hc).trans (Nat.floor_le (by positivity))
    exact hvT (hlow v hv1 this)
  rw [← expect_maxSCC_Ioc, ← expect_maxSCC_Ioc]
  exact ⟨expectP_mono hρ0 hρ1 fun ω => by exact_mod_cast maxSCC_mono (arc ω) hsub1,
    expectP_mono hρ0 hρ1 fun ω => by exact_mod_cast maxSCC_mono (arc ω) hsub2⟩

/-- **The limit for any attack set squeezed as in Lemma 6.2.** -/
theorem attack_limit {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ} {θ : ℝ} (hθ1 : θ < 1)
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ))
    {T : ℕ → Finset ℕ}
    (hT : ∀ᶠ N in atTop, (∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ (1 - 1 / 4) * K N → v ∈ T N) ∧
      (∀ t ∈ T N, (t : ℝ) ≤ (1 + 1 / 4) * K N)) :
    Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N 0 → Bool =>
      (maxSCC (arc ω) (Icc 1 N \ T N) : ℝ)) / N) atTop (𝓝 (dickLim θ)) := by
  have hθm := tendsto_ratio_of_close (K' := fun N => Kminus (K N)) hθ fun N => abs_log_Kminus _
  have hθp := tendsto_ratio_of_close (K' := fun N => Kplus (K N)) hθ fun N => abs_log_Kplus _
  have hKp := eventually_lt_of_ratio hθ1 hθp
  have hKm : ∀ᶠ N in atTop, Kminus (K N) < N := by
    filter_upwards [hKp] with N hN
    exact lt_of_le_of_lt ((Kminus_le _).trans (le_Kplus _)) hN
  have hlimm := cor_profile hρ0 hρ1 hKm hθm
  have hlimp := cor_profile hρ0 hρ1 hKp hθp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimp hlimm ?_ ?_
  · filter_upwards [hT] with N hTN
    exact div_le_div_of_nonneg_right (expect_attack_sandwich hρ0.le hρ1.le hTN.1 hTN.2).1
      (Nat.cast_nonneg N)
  · filter_upwards [hT] with N hTN
    exact div_le_div_of_nonneg_right (expect_attack_sandwich hρ0.le hρ1.le hTN.1 hTN.2).2
      (Nat.cast_nonneg N)

/-- **Corollary 1.5, static attack.** If `|T| = K`, `T ⊆ [N]`, and every `t ∈ T` has degree in
`G_N` at least that of every `v ∉ T`, then `E[#Φ(𝒟_ρ(N) − T)]/N → ρ(1/(1 − θ))`. -/
theorem cor_degree_static {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ} {θ : ℝ} (hθ1 : θ < 1)
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ))
    {T : ℕ → Finset ℕ}
    (hT : ∀ᶠ N in atTop, T N ⊆ Icc 1 N ∧ (T N).card = K N ∧
      ∀ t ∈ T N, ∀ v ∈ Icc 1 N, v ∉ T N → deg N v ≤ deg N t) :
    Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N 0 → Bool =>
      (maxSCC (arc ω) (Icc 1 N \ T N) : ℝ)) / N) atTop (𝓝 (dickLim θ)) := by
  obtain ⟨τ, hτ⟩ := eventually_sandwich_hyp hθ1 hθ
  refine attack_limit hρ0 hρ1 hθ1 hθ ?_
  filter_upwards [hT, hτ] with N ⟨hTN, hTK, hst⟩ ⟨hKN, hτN, hgap⟩
  rcases Nat.eq_zero_or_pos (K N) with hK0 | hK1
  · have hT0 : T N = ∅ := card_eq_zero.mp (hTK.trans hK0)
    refine ⟨fun v hv hvK => ?_, fun t ht => by simp [hT0] at ht⟩
    rw [hK0, Nat.cast_zero, mul_zero] at hvK
    have : (1 : ℝ) ≤ v := by exact_mod_cast hv
    linarith
  · exact sandwich_static (by norm_num) (by norm_num) hK1 hKN hτN (hgap hK1) hTN hTK hst

/-- **Corollary 1.5, adaptive attack.** If `T = {u₀, …, u_{K−1}}` where each `u_j` has maximal
degree in `G_N − {u₀, …, u_{j−1}}`, then `E[#Φ(𝒟_ρ(N) − T)]/N → ρ(1/(1 − θ))`. -/
theorem cor_degree_adaptive {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ} {θ : ℝ}
    (hθ1 : θ < 1)
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ))
    {u : ℕ → ℕ → ℕ} (hu : ∀ᶠ N in atTop, IsAdaptive N (K N) (u N)) :
    Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N 0 → Bool =>
      (maxSCC (arc ω) (Icc 1 N \ removedSet (u N) (K N)) : ℝ)) / N) atTop
      (𝓝 (dickLim θ)) := by
  obtain ⟨τ, hτ⟩ := eventually_sandwich_hyp hθ1 hθ
  refine attack_limit hρ0 hρ1 hθ1 hθ ?_
  filter_upwards [hu, hτ] with N huN ⟨hKN, hτN, hgap⟩
  rcases Nat.eq_zero_or_pos (K N) with hK0 | hK1
  · have hT0 : removedSet (u N) (K N) = ∅ := by simp [removedSet, hK0]
    refine ⟨fun v hv hvK => ?_, fun t ht => by simp [hT0] at ht⟩
    rw [hK0, Nat.cast_zero, mul_zero] at hvK
    have : (1 : ℝ) ≤ v := by exact_mod_cast hv
    linarith
  · exact sandwich_adaptive (by norm_num) (by norm_num) hK1 hKN hτN (hgap hK1) huN

/-- **Corollary 1.5, last claim.** For fixed `κ ∈ (0, 1/2)` and large `N`, if
`1 ≤ K ≤ N^{1/2−κ}`, then a static set `T` is exactly `{1, …, K}`. -/
theorem static_eq_Icc {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 2) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (1 / 2 - κ) →
      ∀ T : Finset ℕ, T ⊆ Icc 1 N → T.card = K →
        (∀ t ∈ T, ∀ v ∈ Icc 1 N, v ∉ T → deg N v ≤ deg N t) → T = Icc 1 K := by
  obtain ⟨C, hC0, hC⟩ := divisor_bound hκ0
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((eventually_ge_atTop 1).and
    (hN.eventually ((tendsto_rpow_atTop hκ0).eventually_ge_atTop (2 * C + 4))))
  refine ⟨N₁, fun N hN1 K hK1 hKN T hTN hTK hst => ?_⟩
  obtain ⟨hN1', hx⟩ := hN₁ N hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set x := (N : ℝ) ^ κ with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 κ
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  -- `K² ≤ N^{1−2κ}`, so `2N ≥ x² K(K+1)`.
  have hK2 : (K : ℝ) ^ 2 * x ^ 2 ≤ N := by
    have h1 : (K : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 2 - κ)) ^ 2 := pow_le_pow_left₀ (by positivity) hKN 2
    have h2 : ((N : ℝ) ^ (1 / 2 - κ)) ^ 2 * x ^ 2 = N := by
      rw [hxdef, ← mul_pow, ← Real.rpow_add hN0, show 1 / 2 - κ + κ = (1 / 2 : ℝ) by ring,
        ← Real.sqrt_eq_rpow, Real.sq_sqrt hN0.le]
    calc (K : ℝ) ^ 2 * x ^ 2 ≤ ((N : ℝ) ^ (1 / 2 - κ)) ^ 2 * x ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = N := h2
  have hKN' : K < N := by
    have hx4 : 4 ≤ x := by linarith
    have h16 : 16 ≤ x ^ 2 := by nlinarith
    have h1 : (K : ℝ) ^ 2 * 16 ≤ (K : ℝ) ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left h16 (by positivity)
    have h2 : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have : (K : ℝ) < N := by nlinarith
    exact_mod_cast this
  -- Every `t ∈ T` is `≤ K`.
  have hTK' : ∀ t ∈ T, t ≤ K := by
    intro t ht
    by_contra htK
    push Not at htK
    -- Some `v ≤ K` is not in `T`.
    have hlt : (T.erase t).card < (Icc 1 K).card := by
      rw [card_erase_of_mem ht, hTK, Nat.card_Icc]
      omega
    obtain ⟨v, hvI, hvT⟩ := exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨hv1, hvK⟩ := mem_Icc.mp hvI
    have hvT' : v ∉ T := fun h => hvT (mem_erase.mpr ⟨by omega, h⟩)
    have hdeg := hst t ht v (mem_Icc.mpr ⟨hv1, by omega⟩) hvT'
    -- `deg v ≥ N/v − 2 ≥ N/K − 2`.
    have hv := degT_ge (N := N) (A := v) (T := ∅) hv1 le_rfl (by omega) (by simp)
    have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv1
    have hvKR : (v : ℝ) ≤ K := by exact_mod_cast hvK
    have hNv : (N : ℝ) / K ≤ N / v := div_le_div_of_nonneg_left hN0.le (by linarith) hvKR
    have hvv : (v : ℝ) / v = 1 := div_self (by linarith)
    -- `deg t ≤ τ(t) + N/t ≤ C x + N/(K+1)`.
    obtain ⟨ht1, htN⟩ := mem_Icc.mp (hTN ht)
    have hdt := deg_le N ht1
    have htau : ((t.divisors.card : ℕ) : ℝ) ≤ C * x := by
      have := hC t (by omega)
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
      exact Real.rpow_le_rpow (Nat.cast_nonneg t) (by exact_mod_cast htN) hκ0.le
    have htR : (K : ℝ) + 1 ≤ t := by exact_mod_cast htK
    have hNt : (N : ℝ) / t ≤ N / ((K : ℝ) + 1) :=
      div_le_div_of_nonneg_left hN0.le (by positivity) htR
    have hdegR : (deg N v : ℝ) ≤ deg N t := by exact_mod_cast hdeg
    -- So `N/(K(K+1)) ≤ C x + 2`, but `N/(K(K+1)) ≥ x²/2 > C x + 2`.
    have key : (N : ℝ) / K - N / ((K : ℝ) + 1) ≤ C * x + 2 := by linarith
    have e : (N : ℝ) / K - N / ((K : ℝ) + 1) = N / (K * ((K : ℝ) + 1)) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)] at key
    have hKK : (K : ℝ) * ((K : ℝ) + 1) ≤ 2 * (K : ℝ) ^ 2 := by nlinarith
    have hxC : 2 * C + 4 ≤ x := hx
    have h3 : (N : ℝ) ≤ (C * x + 2) * (2 * (K : ℝ) ^ 2) :=
      key.trans (mul_le_mul_of_nonneg_left hKK (by positivity))
    have h4 : (K : ℝ) ^ 2 * x ^ 2 ≤ (C * x + 2) * (2 * (K : ℝ) ^ 2) := hK2.trans h3
    have hK2pos : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
    have h5 : x ^ 2 ≤ 2 * (C * x + 2) := by nlinarith
    nlinarith
  exact eq_of_subset_of_card_le (fun t ht => mem_Icc.mpr ⟨(mem_Icc.mp (hTN ht)).1, hTK' t ht⟩)
    (by rw [hTK, Nat.card_Icc]; omega)

/-! ### Attack sets exist -/

/-- **Static attack sets exist**: for `K ≤ N`, some `K`-subset of `[N]` has every degree at
least every degree outside it. Take a `K`-subset maximising the total degree. -/
theorem exists_static (N K : ℕ) (hKN : K ≤ N) :
    ∃ T ⊆ Icc 1 N, T.card = K ∧ ∀ t ∈ T, ∀ v ∈ Icc 1 N, v ∉ T → deg N v ≤ deg N t := by
  have hne : ((Icc 1 N).powersetCard K).Nonempty :=
    powersetCard_nonempty.mpr (by rw [Nat.card_Icc]; omega)
  obtain ⟨T, hT, hmax⟩ := exists_max_image _ (fun T => ∑ t ∈ T, deg N t) hne
  obtain ⟨hTN, hTK⟩ := mem_powersetCard.mp hT
  refine ⟨T, hTN, hTK, fun t ht v hv hvT => ?_⟩
  by_contra hlt
  push Not at hlt
  -- Swapping `t` for `v` would increase the total degree.
  have hvT' : v ∉ T.erase t := fun h => hvT (mem_of_mem_erase h)
  have hmem : insert v (T.erase t) ∈ (Icc 1 N).powersetCard K := by
    refine mem_powersetCard.mpr ⟨insert_subset hv ((erase_subset t T).trans hTN), ?_⟩
    rw [card_insert_of_notMem hvT', card_erase_of_mem ht, hTK]
    have : 1 ≤ K := hTK ▸ card_pos.mpr ⟨t, ht⟩
    omega
  have h1 := hmax _ hmem
  rw [sum_insert hvT'] at h1
  have h2 := add_sum_erase T (fun x => deg N x) ht
  omega

/-- One adaptive step: a vertex of maximal degree in `G_N − R` (or `0` if none is left). -/
noncomputable def adaptStep (N : ℕ) (R : Finset ℕ) : ℕ :=
  if h : (Icc 1 N \ R).Nonempty then
    Classical.choose ((Icc 1 N \ R).exists_max_image (degT N R) h)
  else 0

/-- The first `j` vertices removed by the adaptive attack. -/
noncomputable def adaptSet (N : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => insert (adaptStep N (adaptSet N j)) (adaptSet N j)

/-- The adaptive sequence `u_j`. -/
noncomputable def adaptSeq (N : ℕ) (j : ℕ) : ℕ := adaptStep N (adaptSet N j)

theorem removedSet_adaptSeq (N : ℕ) : ∀ j, removedSet (adaptSeq N) j = adaptSet N j
  | 0 => by simp [removedSet, adaptSet]
  | j + 1 => by rw [removedSet_succ, removedSet_adaptSeq N j, adaptSet, adaptSeq]

theorem card_adaptSet_le (N : ℕ) : ∀ j, (adaptSet N j).card ≤ j
  | 0 => by simp [adaptSet]
  | j + 1 => (card_insert_le _ _).trans (Nat.succ_le_succ (card_adaptSet_le N j))

/-- **Adaptive attack sequences exist**: for `K ≤ N`, `adaptSeq N` is one. -/
theorem isAdaptive_adaptSeq {N K : ℕ} (hKN : K ≤ N) : IsAdaptive N K (adaptSeq N) := by
  intro j hj
  rw [removedSet_adaptSeq]
  have hne : (Icc 1 N \ adaptSet N j).Nonempty := by
    have h1 := card_adaptSet_le N j
    have h2 : (adaptSet N j).card < (Icc 1 N).card := by rw [Nat.card_Icc]; omega
    obtain ⟨v, hv, hvR⟩ := exists_mem_notMem_of_card_lt_card h2
    exact ⟨v, mem_sdiff.mpr ⟨hv, hvR⟩⟩
  have hspec := Classical.choose_spec ((Icc 1 N \ adaptSet N j).exists_max_image
    (degT N (adaptSet N j)) hne)
  have hu : adaptSeq N j = Classical.choose ((Icc 1 N \ adaptSet N j).exists_max_image
      (degT N (adaptSet N j)) hne) := by
    unfold adaptSeq adaptStep
    simp only [hne, ↓reduceDIte]
  rw [hu]
  obtain ⟨hmem, hmax⟩ := hspec
  obtain ⟨hI, hR⟩ := mem_sdiff.mp hmem
  exact ⟨hI, hR, fun v hv hvR => hmax v (mem_sdiff.mpr ⟨hv, hvR⟩)⟩

end HubRemoval
