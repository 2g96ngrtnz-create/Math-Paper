import HubRemoval.RobustProb
import HubRemoval.Asymptotics

/-!
# Remark 7.2, first aside: the hub set is strongly connected w.h.p.

The remark considers the hub set `H = (K, N^{1/2−δ}]` and says: *"It is strongly connected w.h.p.,
because any two hubs have at least `N^{2δ}` common multiples."* Both parts are proved here, for
every fixed `ρ ∈ (0, 1)` and `δ > 0`, uniformly in `K`.

* `card_common_multiples_ge`: if `ab ≤ N^{1−2δ}`, then `a` and `b` have at least `⌊N^{2δ}⌋`
  common multiples in `[1, N]`.
* `hub_mutual`: on the event `𝓗`, all hubs lie in one SCC. The event `𝓗` asks, for every pair of
  hubs `a < b`, for a common multiple `y ∈ (b, N]` with `a → y → b`, and one with `b → y' → a`.
* `prob_not_hub`: `P(𝓗ᶜ) ≤ 2 N^{1−2δ} (1 − q)^{N^{2δ} − 2}` with `q = ρ(1 − ρ)`. As in Lemma 4.1,
  the witnesses at distinct `y` use disjoint pairs of edges, and a union bound over the pairs
  finishes.
* `remark_7_2_hubs`: `P(all hubs are pairwise mutually reachable) → 1`.
-/

namespace HubRemoval

open Finset Filter Topology

variable {N K : ℕ}

/-- **Any two hubs have many common multiples.** If `0 < a, b` and `ab ≤ N^{1−2δ}` with `N ≥ 1`,
then `a` and `b` have at least `⌊N^{2δ}⌋` common multiples in `[1, N]`. -/
theorem card_common_multiples_ge (hN : 1 ≤ N) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {δ : ℝ}
    (hab : ((a * b : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 - 2 * δ)) :
    ⌊(N : ℝ) ^ (2 * δ)⌋₊ ≤ ((Ioc 0 N).filter (fun y => a ∣ y ∧ b ∣ y)).card := by
  have hset : (Ioc 0 N).filter (fun y => a ∣ y ∧ b ∣ y) = (Ioc 0 N).filter (Nat.lcm a b ∣ ·) :=
    filter_congr fun y _ => Nat.lcm_dvd_iff.symm
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  have hL0 : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have hLab : Nat.lcm a b ≤ a * b := by
    have h := Nat.gcd_mul_lcm a b
    have hg : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    nlinarith
  rw [Nat.le_div_iff_mul_le hL0]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfl : (⌊(N : ℝ) ^ (2 * δ)⌋₊ : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Nat.floor_le (by positivity)
  have hLab' : (Nat.lcm a b : ℝ) ≤ ((a * b : ℕ) : ℝ) := by exact_mod_cast hLab
  have hLR : (Nat.lcm a b : ℝ) ≤ (N : ℝ) ^ (1 - 2 * δ) := hLab'.trans hab
  have hprod : (N : ℝ) ^ (2 * δ) * (N : ℝ) ^ (1 - 2 * δ) = N := by
    rw [← Real.rpow_add hN0, show 2 * δ + (1 - 2 * δ) = (1 : ℝ) by ring, Real.rpow_one]
  have : ((⌊(N : ℝ) ^ (2 * δ)⌋₊ * Nat.lcm a b : ℕ) : ℝ) ≤ N := by
    push_cast
    calc (⌊(N : ℝ) ^ (2 * δ)⌋₊ : ℝ) * (Nat.lcm a b : ℝ)
        ≤ (N : ℝ) ^ (2 * δ) * (N : ℝ) ^ (1 - 2 * δ) :=
          mul_le_mul hfl hLR (Nat.cast_nonneg _) (by positivity)
      _ = N := hprod
  exact_mod_cast this

/-- The witnesses for hubs `a < b`: the common multiples `y ∈ (b, N]`. -/
def hubW (N a b : ℕ) : Finset ℕ := (Ioc b N).filter (Nat.lcm a b ∣ ·)

/-- The hub event `𝓗(H)`: every two hubs `K < a < b ≤ H` are joined by 2-paths `a → y → b` and
`b → y' → a` through common multiples `y, y' ∈ (b, N]`. -/
def HubEvent (ω : Edge N K → Bool) (H : ℕ) : Prop :=
  ∀ a b, K < a → a < b → b ≤ H →
    (∃ y ∈ hubW N a b, pat a b y ω) ∧ (∃ y ∈ hubW N a b, pat b a y ω)

theorem hubW_edges {a b y : ℕ} (hKa : K < a) (hab : a < b) (hy : y ∈ hubW N a b) :
    (a, y) ∈ edges N K ∧ (b, y) ∈ edges N K := by
  obtain ⟨hyI, hdvd⟩ := mem_filter.mp hy
  obtain ⟨hby, hyN⟩ := mem_Ioc.mp hyI
  exact ⟨mem_edges.mpr ⟨hKa, by omega, hyN, (Nat.dvd_lcm_left a b).trans hdvd⟩,
    mem_edges.mpr ⟨by omega, hby, hyN, (Nat.dvd_lcm_right a b).trans hdvd⟩⟩

/-- A witness `pat a b y` gives the 2-path `a → y → b`. -/
theorem path_of_pat {ω : Edge N K → Bool} {a b y : ℕ} (ha : (a, y) ∈ edges N K)
    (hb : (b, y) ∈ edges N K) (h : pat a b y ω) : Relation.ReflTransGen (arc ω) a b :=
  (Relation.ReflTransGen.single ((arc_of_edge ha).1.mpr h.1)).tail ((arc_of_edge hb).2.mpr h.2)

/-- **On `𝓗(H)`, the hubs `(K, H]` lie in one SCC.** -/
theorem hub_mutual {ω : Edge N K → Bool} {H : ℕ} (hH : HubEvent ω H) {a b : ℕ}
    (ha : a ∈ Ioc K H) (hb : b ∈ Ioc K H) : MutuallyReachable (arc ω) a b := by
  obtain ⟨hKa, haH⟩ := mem_Ioc.mp ha
  obtain ⟨hKb, hbH⟩ := mem_Ioc.mp hb
  have key : ∀ a b, K < a → a < b → b ≤ H → MutuallyReachable (arc ω) a b :=
    fun a b hKa hab hbH => by
      obtain ⟨⟨y, hy, hp⟩, ⟨y', hy', hp'⟩⟩ := hH a b hKa hab hbH
      obtain ⟨e1, e2⟩ := hubW_edges hKa hab hy
      obtain ⟨e3, e4⟩ := hubW_edges hKa hab hy'
      exact ⟨path_of_pat e1 e2 hp, path_of_pat e4 e3 hp'⟩
  rcases lt_trichotomy a b with h | rfl | h
  · exact key a b hKa h hbH
  · exact MutuallyReachable.refl _ _
  · exact (key b a hKb h haH).symm

/-- **The probability bound.** For `N ≥ 1` and `H = ⌊N^{1/2−δ}⌋`,
`P(𝓗(H)ᶜ) ≤ 2 N^{1−2δ} (1 − q)^{N^{2δ} − 2}` with `q = ρ(1 − ρ)`. -/
theorem prob_not_hub {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {δ : ℝ} (hN : 1 ≤ N) :
    prob ρ (fun ω : Edge N K → Bool => ¬ HubEvent ω ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊) ≤
      2 * (N : ℝ) ^ (1 - 2 * δ) * (1 - ρ * (1 - ρ)) ^ ((N : ℝ) ^ (2 * δ) - 2) := by
  classical
  set H := ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ with hH
  set M := (N : ℝ) ^ (1 - 2 * δ) with hM
  set b := 1 - ρ * (1 - ρ) with hb
  set t := (N : ℝ) ^ (2 * δ) - 2 with ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 < M := by positivity
  have hq : ρ * (1 - ρ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
  have hb0 : 0 < b := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  have hbt : 0 ≤ b ^ t := Real.rpow_nonneg hb0.le t
  have hHR : (H : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := Nat.floor_le (by positivity)
  have hHH : (H : ℝ) * H ≤ M := by
    have h := mul_le_mul hHR hHR (Nat.cast_nonneg _) (by positivity)
    rwa [← Real.rpow_add hN0, show 1 / 2 - δ + (1 / 2 - δ) = 1 - 2 * δ by ring] at h
  have hNM : (N : ℝ) / M = (N : ℝ) ^ (2 * δ) := by
    rw [div_eq_iff hM0.ne', hM, ← Real.rpow_add hN0,
      show 2 * δ + (1 - 2 * δ) = (1 : ℝ) by ring, Real.rpow_one]
  set P := ((Ioc K H) ×ˢ (Ioc K H)).filter (fun p : ℕ × ℕ => p.1 < p.2) with hP
  -- If `𝓗` fails, some pair has no witness in one direction.
  have hbad : ∀ ω : Edge N K → Bool, ¬ HubEvent ω H → ∃ p ∈ P,
      (∀ y ∈ hubW N p.1 p.2, ¬ pat p.1 p.2 y ω) ∨ (∀ y ∈ hubW N p.1 p.2, ¬ pat p.2 p.1 y ω) := by
    intro ω h
    unfold HubEvent at h
    push Not at h
    obtain ⟨a, c, hKa, hac, hcH, hfail⟩ := h
    refine ⟨(a, c), mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨hKa, by omega⟩,
      mem_Ioc.mpr ⟨by omega, hcH⟩⟩, hac⟩, ?_⟩
    by_cases h1 : ∃ y ∈ hubW N a c, pat a c y ω
    · exact Or.inr (hfail h1)
    · push Not at h1
      exact Or.inl h1
  -- One pair, one direction.
  have hone : ∀ p ∈ P, ∀ u v : ℕ, (u = p.1 ∧ v = p.2 ∨ u = p.2 ∧ v = p.1) →
      prob ρ (fun ω : Edge N K → Bool => ∀ y ∈ hubW N p.1 p.2, ¬ pat u v y ω) ≤ b ^ t := by
    intro p hp u v huv
    obtain ⟨hpI, hlt⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_product.mp hpI
    obtain ⟨hK1, h1H⟩ := mem_Ioc.mp h1
    obtain ⟨hK2, h2H⟩ := mem_Ioc.mp h2
    have hW : ∀ y ∈ hubW N p.1 p.2, (u, y) ∈ edges N K ∧ (v, y) ∈ edges N K := by
      intro y hy
      obtain ⟨e1, e2⟩ := hubW_edges hK1 hlt hy
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e1, e2⟩
      · exact ⟨e2, e1⟩
    have huv' : u ≠ v := by rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    rw [prob_no_pat ρ huv' _ hW, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hb0 hb1
    -- `|W| ≥ N/L − 2 ≥ N^{2δ} − 2`, with `L = lcm(p₁, p₂) ≤ p₁p₂ ≤ H² ≤ N^{1−2δ}`.
    have hL0 : 0 < Nat.lcm p.1 p.2 := Nat.lcm_pos (by omega) (by omega)
    have hLab : Nat.lcm p.1 p.2 ≤ p.1 * p.2 := by
      have h := Nat.gcd_mul_lcm p.1 p.2
      have hg : 1 ≤ Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ (by omega)
      nlinarith
    have hLM : (Nat.lcm p.1 p.2 : ℝ) ≤ M := by
      have h1R : (p.1 : ℝ) ≤ H := by exact_mod_cast h1H
      have h2R : (p.2 : ℝ) ≤ H := by exact_mod_cast h2H
      have : ((p.1 * p.2 : ℕ) : ℝ) ≤ (H : ℝ) * H := by
        push_cast
        exact mul_le_mul h1R h2R (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact ((by exact_mod_cast hLab : (Nat.lcm p.1 p.2 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ)).trans
        this).trans hHH
    have hcount := card_multiples_Ioc_ge N hL0 hLM
    have hsub : (Ioc (Nat.lcm p.1 p.2) N).filter (Nat.lcm p.1 p.2 ∣ ·) ⊆ hubW N p.1 p.2 := by
      intro y hy
      obtain ⟨hyI, hdvd⟩ := mem_filter.mp hy
      obtain ⟨hLy, hyN⟩ := mem_Ioc.mp hyI
      have h2L : p.2 ≤ Nat.lcm p.1 p.2 := Nat.le_of_dvd hL0 (Nat.dvd_lcm_right _ _)
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hyN⟩, hdvd⟩
    have hcard : (((Ioc (Nat.lcm p.1 p.2) N).filter (Nat.lcm p.1 p.2 ∣ ·)).card : ℝ) ≤
        (hubW N p.1 p.2).card := by exact_mod_cast card_le_card hsub
    rw [hNM] at hcount
    linarith
  -- `|P| ≤ H² ≤ N^{1−2δ}`.
  have hPcard : (P.card : ℝ) ≤ M := by
    have h1 : P.card ≤ H * H := by
      refine (card_le_card (filter_subset _ _)).trans ?_
      rw [card_product, Nat.card_Ioc]
      exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    exact (by exact_mod_cast h1 : (P.card : ℝ) ≤ ((H * H : ℕ) : ℝ)).trans (by push_cast; exact hHH)
  calc prob ρ (fun ω : Edge N K → Bool => ¬ HubEvent ω H)
      ≤ prob ρ (fun ω : Edge N K → Bool => ∃ p ∈ P,
          (fun p ω => (∀ y ∈ hubW N p.1 p.2, ¬ pat p.1 p.2 y ω) ∨
            (∀ y ∈ hubW N p.1 p.2, ¬ pat p.2 p.1 y ω)) p ω) :=
        prob_mono hρ0 hρ1 fun ω h => hbad ω h
    _ ≤ ∑ p ∈ P, prob ρ (fun ω : Edge N K → Bool =>
          (∀ y ∈ hubW N p.1 p.2, ¬ pat p.1 p.2 y ω) ∨
            (∀ y ∈ hubW N p.1 p.2, ¬ pat p.2 p.1 y ω)) :=
        prob_exists_le hρ0 hρ1 _ _
    _ ≤ ∑ _p ∈ P, 2 * b ^ t := by
        refine sum_le_sum fun p hp => (prob_or_le hρ0 hρ1 _ _).trans ?_
        have h1 := hone p hp p.1 p.2 (Or.inl ⟨rfl, rfl⟩)
        have h2 := hone p hp p.2 p.1 (Or.inr ⟨rfl, rfl⟩)
        linarith
    _ = 2 * P.card * b ^ t := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * M * b ^ t := by
        have := mul_le_mul_of_nonneg_right hPcard hbt
        linarith

/-- `N exp(−q(N^{2δ} − 2)) → 0` for `q, δ > 0`. -/
theorem tendsto_mul_exp_neg {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-q * ((N : ℝ) ^ (2 * δ) - 2))) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- Eventually `2 log N ≤ q N^{2δ}`.
  have hev := hN.eventually ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 * δ)).eventually
    (eventually_mul_log_pow_le (1 / (q * δ)) 1))
  have hlim : Tendsto (fun N : ℕ => Real.exp (2 * q) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [hev, eventually_ge_atTop 1] with N hN' hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [pow_one, Real.log_rpow hN0] at hN'
  have h2 : 2 * Real.log N ≤ q * (N : ℝ) ^ (2 * δ) := by
    have e : 1 / (q * δ) * (2 * δ * Real.log N) = 2 * Real.log N / q := by
      field_simp
    rw [e, div_le_iff₀ hq] at hN'
    linarith
  have hexp : Real.exp (-q * ((N : ℝ) ^ (2 * δ) - 2)) ≤ Real.exp (2 * q) / (N : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity), ← Real.exp_log hN0, ← Real.exp_nat_mul, ← Real.exp_add,
      Real.exp_log hN0]
    exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
  calc (N : ℝ) * Real.exp (-q * ((N : ℝ) ^ (2 * δ) - 2))
      ≤ (N : ℝ) * (Real.exp (2 * q) / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hexp hN0.le
    _ = Real.exp (2 * q) / (N : ℝ) := by field_simp

/-- **Remark 7.2, first aside.** For `ρ ∈ (0, 1)`, `δ > 0` and any `K = K(N)`, with probability
tending to `1` the hubs in `(K, N^{1/2−δ}]` are pairwise mutually reachable in `𝒟_ρ(N, K)`. -/
theorem remark_7_2_hubs {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {δ : ℝ} (hδ : 0 < δ)
    (K : ℕ → ℕ) :
    Tendsto (fun N : ℕ => prob ρ (fun ω : Edge N (K N) → Bool =>
      ∀ a ∈ Ioc (K N) ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊, ∀ b ∈ Ioc (K N) ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊,
        MutuallyReachable (arc ω) a b)) atTop (𝓝 1) := by
  set q := ρ * (1 - ρ) with hqdef
  have hq : 0 < q := mul_pos hρ0 (by linarith)
  have hq1 : q ≤ 1 / 4 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim := (tendsto_mul_exp_neg hq hδ).const_mul 2
  rw [mul_zero] at hlim
  have hlow : Tendsto (fun N : ℕ => 1 - 2 * ((N : ℝ) * Real.exp (-q * ((N : ℝ) ^ (2 * δ) - 2))))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun N => prob_le_one hρ0.le hρ1.le _)
  filter_upwards [eventually_ge_atTop 1,
    hN.eventually ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 * δ)).eventually_ge_atTop 2)]
    with N hN1 hN2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- `P(good) ≥ P(𝓗) = 1 − P(𝓗ᶜ)`.
  have hmono := prob_mono hρ0.le hρ1.le (A := fun ω : Edge N (K N) → Bool =>
    HubEvent ω ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊) (B := fun ω : Edge N (K N) → Bool =>
      ∀ a ∈ Ioc (K N) ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊, ∀ b ∈ Ioc (K N) ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊,
        MutuallyReachable (arc ω) a b) fun ω hH a ha b hb => hub_mutual hH ha hb
  have hnot := prob_not ρ (fun ω : Edge N (K N) → Bool => HubEvent ω ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊)
  have hbound := prob_not_hub (K := K N) hρ0.le hρ1.le (δ := δ) hN1
  -- `2 N^{1−2δ} (1 − q)^{N^{2δ} − 2} ≤ 2 N exp(−q(N^{2δ} − 2))`.
  have ht : 0 ≤ (N : ℝ) ^ (2 * δ) - 2 := by linarith
  have hbase : (1 - q) ^ ((N : ℝ) ^ (2 * δ) - 2) ≤ Real.exp (-q * ((N : ℝ) ^ (2 * δ) - 2)) := by
    have := Real.rpow_le_rpow (by linarith) (Real.one_sub_le_exp_neg q) ht
    rwa [← Real.exp_mul] at this
  have hMN : (N : ℝ) ^ (1 - 2 * δ) ≤ N := by
    calc (N : ℝ) ^ (1 - 2 * δ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      _ = N := Real.rpow_one _
  have h1 : 0 ≤ (1 - q) ^ ((N : ℝ) ^ (2 * δ) - 2) := Real.rpow_nonneg (by linarith) _
  have h2 := mul_le_mul hMN hbase h1 hN0.le
  linarith

end HubRemoval
