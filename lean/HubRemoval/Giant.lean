import HubRemoval.Rate

/-!
# The structure of the giant (paper, eq. (3) and Corollary 1.5)

**SCCs.** `sccOf ω v` is the SCC of `v` in the digraph of `ω`: the vertices of `G_{N,K}`
mutually reachable with `v`. `IsSCC ω C` says that `C` is one of these. A largest SCC exists
(`exists_largest_scc`), so there is a rule choosing one for every outcome (`exists_star`).
`secondSCC ω S` is the largest size of an SCC other than `S`, or `0` if there is none.

**The giant's seed `Σ`.** `sigmaSet M ω` is the set of vertices mutually reachable with some
element of `S_M`. On `𝓡` (with `M ≥ 4(K+1)`) it is strongly connected (Corollary 4.3), closed
under mutual reachability, and contained in `F₁` when `M ≤ N`. So it is the SCC containing `S_M`
whenever `S_M ≠ ∅`.

**Proposition 4.6, eq. (3).** `E[|F₁ \ Σ| · 1_𝓡] ≤ Err` (`eq_4_2`). On `𝓡`,
`F₁ \ Σ ⊆ (F₁ \ 𝒰) ∪ {m ∈ 𝒰 : A_mᶜ}`, and `P(A_mᶜ) ≤ 2λ^{s₀+1}` (Lemmas 4.4, 4.5(c)).

**Corollary 1.5 (Structure of the giant).** Fix `ρ ∈ (0, 1)`. There is `N₀` such that for
`N ≥ N₀`, all `K < N` and every rule `Φ*_K` choosing a largest SCC (`cor_structure`):
* (a) `E|Φ_K − Ψ(N, N/(K+1))| ≤ 30N/log log N`. Also `Φ_K/N − Ψ/N → 0` in probability,
  uniformly in `K` (`cor_structure_prob`);
* (b) `E|F₁ ∆ Φ*_K| ≤ 2K + 30N/log log N`;
* (c) `E[Φ_K^{(2)}] ≤ K + 30N/log log N`.

*Proof of (b), (c).* If `K ≤ N^{1−η}`, then on `𝓡` every SCC other than `Σ` is disjoint from
`Σ` and lies in one fibre. So it lies in `F₁ \ Σ`, or has at most `K` elements
(Proposition 3.2 and Lemma 3.1(c)). A case analysis gives `|F₁ ∆ Φ*| ≤ W + 2K` and
`Φ^{(2)} ≤ W + K`, where `W = |F₁ \ Σ|` (`giant_pointwise`). Off `𝓡` both are at most `N`.
Then eq. (3), `Err ≤ 28N/ℓ` and `N·P(𝓡ᶜ) ≤ 1` finish the bound. If `K > N^{1−η}`, then
`Ψ(N, B) ≤ 3N/ℓ` bounds everything.
-/

namespace HubRemoval

open Finset Filter Topology
open scoped symmDiff

variable {N K : ℕ}

/-! ### SCCs of `𝒟_ρ(N, K)` -/

open Classical in
/-- The SCC of `v`: the vertices of `G_{N,K}` mutually reachable with `v`. -/
noncomputable def sccOf (ω : Edge N K → Bool) (v : ℕ) : Finset ℕ :=
  (Ioc K N).filter fun w => MutuallyReachable (arc ω) v w

/-- `C` is an SCC of the digraph of `ω`. -/
def IsSCC (ω : Edge N K → Bool) (C : Finset ℕ) : Prop := ∃ v ∈ Ioc K N, C = sccOf ω v

open Classical in
theorem mem_sccOf {ω : Edge N K → Bool} {v w : ℕ} :
    w ∈ sccOf ω v ↔ w ∈ Ioc K N ∧ MutuallyReachable (arc ω) v w := by
  unfold sccOf
  exact mem_filter

open Classical in
theorem sccOf_subset (ω : Edge N K → Bool) (v : ℕ) : sccOf ω v ⊆ Ioc K N := filter_subset _ _

theorem mem_sccOf_self {ω : Edge N K → Bool} {v : ℕ} (hv : v ∈ Ioc K N) : v ∈ sccOf ω v :=
  mem_sccOf.mpr ⟨hv, MutuallyReachable.refl _ _⟩

/-- An SCC is strongly connected. -/
theorem sccOf_conn {ω : Edge N K → Bool} {v : ℕ} :
    ∀ a ∈ sccOf ω v, ∀ b ∈ sccOf ω v, Relation.ReflTransGen (arc ω) a b := fun _ ha _ hb =>
  ((mem_sccOf.mp ha).2.symm.trans (mem_sccOf.mp hb).2).1

theorem card_sccOf_le (ω : Edge N K → Bool) (v : ℕ) : (sccOf ω v).card ≤ PhiK N K ω :=
  card_le_PhiK (sccOf_subset ω v) sccOf_conn

/-- **A largest SCC exists**: for `K < N`, some SCC has `Φ_K` elements. -/
theorem exists_largest_scc (hKN : K < N) (ω : Edge N K → Bool) :
    ∃ v ∈ Ioc K N, (sccOf ω v).card = PhiK N K ω := by
  obtain ⟨S, hS, hcard⟩ := exists_card_eq_maxSCC (arc ω) (Ioc K N)
  have hcard' : S.card = PhiK N K ω := hcard
  have hN : N ∈ Ioc K N := mem_Ioc.mpr ⟨hKN, le_rfl⟩
  have hpos : 0 < S.card := by
    rw [hcard']
    exact lt_of_lt_of_le (card_pos.mpr ⟨N, mem_sccOf_self hN⟩) (card_sccOf_le ω N)
  obtain ⟨v, hv⟩ := card_pos.mp hpos
  refine ⟨v, hS.1 hv, le_antisymm (card_sccOf_le ω v) ?_⟩
  rw [← hcard']
  refine card_le_card fun w hw => mem_sccOf.mpr ⟨hS.1 hw, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _ (hS.2 v hv w hw)
  · exact Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _ (hS.2 w hw v hv)

/-- **A rule choosing a largest SCC exists.** -/
theorem exists_star (hKN : K < N) :
    ∃ star : (Edge N K → Bool) → Finset ℕ,
      ∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK N K ω := by
  choose v hv hcard using exists_largest_scc hKN
  exact ⟨fun ω => sccOf ω (v ω), fun ω => ⟨⟨v ω, hv ω, rfl⟩, hcard ω⟩⟩

open Classical in
/-- `Φ^{(2)}`: the largest size of an SCC other than `S` (`0` if there is none). -/
noncomputable def secondSCC (ω : Edge N K → Bool) (S : Finset ℕ) : ℕ :=
  ((Ioc K N).filter fun v => sccOf ω v ≠ S).sup fun v => (sccOf ω v).card

theorem secondSCC_le_PhiK (ω : Edge N K → Bool) (S : Finset ℕ) : secondSCC ω S ≤ PhiK N K ω :=
  Finset.sup_le fun v _ => card_sccOf_le ω v

/-- An SCC lies in `F₁` or has at most `K` elements (Proposition 3.2, Lemma 3.1(c)). -/
theorem sccOf_subset_or_card_le {ω : Edge N K → Bool} {v : ℕ} (hv : v ∈ Ioc K N) :
    sccOf ω v ⊆ smoothFibre N K ∨ (sccOf ω v).card ≤ K := by
  have hsub := stronglyConnected_subset_fibre (D := arc ω) (fun a b h => arc_adj h)
    (sccOf_subset ω v) sccOf_conn (mem_sccOf_self hv)
  rcases Nat.lt_or_ge 1 (roughPart (N / (K + 1)) v) with h1 | h1
  · exact Or.inr ((card_le_card hsub).trans (card_fibre_le_K h1))
  · have hone : roughPart (N / (K + 1)) v = 1 := le_antisymm h1 (roughPart_pos _ _)
    rw [hone, fibre_one] at hsub
    exact Or.inl hsub

/-! ### The seed `Σ` -/

open Classical in
/-- `Σ`: the vertices mutually reachable with some element of `S_M`. -/
noncomputable def sigmaSet (M : ℝ) (ω : Edge N K → Bool) : Finset ℕ :=
  (Ioc K N).filter fun v => ∃ d, goodSet M K d ∧ MutuallyReachable (arc ω) v d

open Classical in
theorem mem_sigmaSet {M : ℝ} {ω : Edge N K → Bool} {v : ℕ} :
    v ∈ sigmaSet M ω ↔ v ∈ Ioc K N ∧ ∃ d, goodSet M K d ∧ MutuallyReachable (arc ω) v d := by
  unfold sigmaSet
  exact mem_filter

section Sigma

variable {M : ℝ} {ω : Edge N K → Bool}

/-- On `𝓡`, `Σ` is strongly connected. -/
theorem sigmaSet_mutual (hM : 4 * ((K : ℝ) + 1) ≤ M) (hR : RobustEvent (arc ω) N K M)
    {a b : ℕ} (ha : a ∈ sigmaSet M ω) (hb : b ∈ sigmaSet M ω) :
    MutuallyReachable (arc ω) a b := by
  obtain ⟨-, d, hd, had⟩ := mem_sigmaSet.mp ha
  obtain ⟨-, d', hd', hbd'⟩ := mem_sigmaSet.mp hb
  exact (had.trans (sigma_mutual hM hR hd hd')).trans hbd'.symm

/-- `Σ` is closed under mutual reachability. -/
theorem sigmaSet_closed {v w : ℕ} (hv : v ∈ sigmaSet M ω) (hw : w ∈ Ioc K N)
    (hvw : MutuallyReachable (arc ω) v w) : w ∈ sigmaSet M ω := by
  obtain ⟨-, d, hd, hvd⟩ := mem_sigmaSet.mp hv
  exact mem_sigmaSet.mpr ⟨hw, d, hd, hvw.symm.trans hvd⟩

/-- **`Σ ⊆ F₁`** when `M ≤ N` (Corollary 4.3). -/
theorem sigmaSet_subset (hMN : M ≤ N) : sigmaSet M ω ⊆ smoothFibre N K := by
  intro v hv
  obtain ⟨hvI, d, hd, hvd⟩ := mem_sigmaSet.mp hv
  have hdI : d ∈ Ioc K N := mem_Ioc.mpr ⟨hd.1, by exact_mod_cast hd.2.1.trans hMN⟩
  have hS : ({v, d} : Finset ℕ) ⊆ vertices N K := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with hx | hx <;> rw [hx]
    · exact hvI
    · exact hdI
  have hconn : ∀ a ∈ ({v, d} : Finset ℕ), ∀ b ∈ ({v, d} : Finset ℕ),
      Relation.ReflTransGen (arc ω) a b := by
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;>
      first | exact hvd.1 | exact hvd.2
  exact sigma_subset_smoothFibre hMN (fun a b h => arc_adj h) hS hconn
    (mem_insert_of_mem (mem_singleton_self d)) hd (mem_insert_self v {d})

open Classical in
theorem card_sigmaSet_le (hM : 4 * ((K : ℝ) + 1) ≤ M) (hR : RobustEvent (arc ω) N K M) :
    (sigmaSet M ω).card ≤ PhiK N K ω :=
  card_le_PhiK (filter_subset _ _) fun _ ha _ hb => (sigmaSet_mutual hM hR ha hb).1

/-- On `𝓡`, an SCC is `Σ` or is disjoint from `Σ`. -/
theorem sccOf_eq_or_disjoint (hM : 4 * ((K : ℝ) + 1) ≤ M) (hR : RobustEvent (arc ω) N K M)
    (v : ℕ) : sccOf ω v = sigmaSet M ω ∨ Disjoint (sccOf ω v) (sigmaSet M ω) := by
  by_cases h : ∃ x ∈ sccOf ω v, x ∈ sigmaSet M ω
  · left
    obtain ⟨x, hx, hxSg⟩ := h
    have hvx := (mem_sccOf.mp hx).2
    ext w
    constructor
    · intro hw
      obtain ⟨hwI, hvw⟩ := mem_sccOf.mp hw
      exact sigmaSet_closed hxSg hwI (hvx.symm.trans hvw)
    · intro hw
      exact mem_sccOf.mpr ⟨(mem_sigmaSet.mp hw).1,
        hvx.trans (sigmaSet_mutual hM hR hw hxSg).symm⟩
  · right
    exact disjoint_left.mpr fun x hx hxSg => h ⟨x, hx, hxSg⟩

/-- On `𝓡`, an SCC other than `Σ` has at most `|F₁ \ Σ| + K` elements. -/
theorem card_sccOf_le_of_ne (hM : 4 * ((K : ℝ) + 1) ≤ M) (hR : RobustEvent (arc ω) N K M)
    {v : ℕ} (hv : v ∈ Ioc K N) (hne : sccOf ω v ≠ sigmaSet M ω) :
    (sccOf ω v).card ≤ (smoothFibre N K \ sigmaSet M ω).card + K := by
  have hdisj := (sccOf_eq_or_disjoint hM hR v).resolve_left hne
  rcases sccOf_subset_or_card_le (ω := ω) hv with hF | hK
  · have : sccOf ω v ⊆ smoothFibre N K \ sigmaSet M ω := subset_sdiff.mpr ⟨hF, hdisj⟩
    exact (card_le_card this).trans (Nat.le_add_right _ _)
  · omega

/-- **The pointwise bounds on `𝓡`.** With `W = |F₁ \ Σ|`, a largest SCC `S` satisfies
`|F₁ ∆ S| ≤ W + 2K`, and every other SCC has at most `W + K` elements. -/
theorem giant_pointwise (hM : 4 * ((K : ℝ) + 1) ≤ M) (hMN : M ≤ N)
    (hR : RobustEvent (arc ω) N K M) {S : Finset ℕ} (hS : IsSCC ω S)
    (hSc : S.card = PhiK N K ω) :
    (smoothFibre N K ∆ S).card ≤ (smoothFibre N K \ sigmaSet M ω).card + 2 * K ∧
      secondSCC ω S ≤ (smoothFibre N K \ sigmaSet M ω).card + K := by
  have hSgF : sigmaSet M ω ⊆ smoothFibre N K := sigmaSet_subset hMN
  have hSgS : (sigmaSet M ω).card ≤ S.card := hSc ▸ card_sigmaSet_le hM hR
  have hFW : (smoothFibre N K).card =
      (smoothFibre N K \ sigmaSet M ω).card + (sigmaSet M ω).card := by
    rw [card_sdiff_of_subset hSgF]
    have := card_le_card hSgF
    omega
  have hsymm : ∀ T : Finset ℕ, (smoothFibre N K ∆ T).card ≤
      (smoothFibre N K \ T).card + (T \ smoothFibre N K).card := fun T => by
    rw [symmDiff_def, sup_eq_union]
    exact card_union_le _ _
  obtain ⟨v, hv, rfl⟩ := hS
  refine ⟨?_, ?_⟩
  · have h0 := hsymm (sccOf ω v)
    rcases sccOf_eq_or_disjoint hM hR v with heq | -
    · have h1 : (sigmaSet M ω \ smoothFibre N K).card = 0 := by
        rw [card_eq_zero, sdiff_eq_empty_iff_subset]
        exact hSgF
      rw [heq] at h0 ⊢
      omega
    · rcases sccOf_subset_or_card_le (ω := ω) hv with hF | hK
      · have h1 : (sccOf ω v \ smoothFibre N K).card = 0 := by
          rw [card_eq_zero, sdiff_eq_empty_iff_subset]
          exact hF
        have h2 : (smoothFibre N K \ sccOf ω v).card =
            (smoothFibre N K).card - (sccOf ω v).card := card_sdiff_of_subset hF
        have h3 := card_le_card hF
        omega
      · have h1 : (smoothFibre N K \ sccOf ω v).card ≤ (smoothFibre N K).card :=
          card_le_card sdiff_subset
        have h2 : (sccOf ω v \ smoothFibre N K).card ≤ (sccOf ω v).card :=
          card_le_card sdiff_subset
        omega
  · refine Finset.sup_le fun u hu => ?_
    obtain ⟨huI, hne⟩ := mem_filter.mp hu
    by_cases hSg : sccOf ω u = sigmaSet M ω
    · -- `S ≠ Σ`, so `|S| ≤ W + K`, and `|Σ| ≤ |S|`.
      have hSne : sccOf ω v ≠ sigmaSet M ω := fun h => hne (hSg.trans h.symm)
      have := card_sccOf_le_of_ne hM hR hv hSne
      rw [hSg]
      omega
    · exact card_sccOf_le_of_ne hM hR huI hSg

end Sigma

/-- Trivial bounds, for every outcome: `|F₁ ∆ S| ≤ |F₁| + |S|`, and both are at most `N`. -/
theorem card_symmDiff_le {S : Finset ℕ} :
    (smoothFibre N K ∆ S).card ≤ (smoothFibre N K).card + S.card := by
  rw [symmDiff_def, sup_eq_union]
  exact (card_union_le _ _).trans (add_le_add (card_le_card sdiff_subset)
    (card_le_card sdiff_subset))

theorem card_symmDiff_le_N {S : Finset ℕ} (hS : S ⊆ Ioc K N) :
    (smoothFibre N K ∆ S).card ≤ N := by
  have hsub : smoothFibre N K ∆ S ⊆ Ioc K N := by
    rw [symmDiff_def, sup_eq_union]
    exact union_subset (sdiff_subset.trans (filter_subset _ _)) (sdiff_subset.trans hS)
  have := card_le_card hsub
  rw [Nat.card_Ioc] at this
  omega

theorem PhiK_le_N (ω : Edge N K → Bool) : PhiK N K ω ≤ N := by
  have h1 := PhiK_le_psi ω
  have h2 := psi_le_self N (N / (K + 1))
  omega

/-! ### Proposition 4.6, eq. (3) -/

variable {s₀ : ℕ} {η δ : ℝ}

open Classical in
/-- **Eq. (3), with `|F₁ \ 𝒰|`.** `E[|F₁ \ Σ| · 1_𝓡] ≤ |F₁ \ 𝒰| + 2λ^{s₀+1} N`. -/
theorem eq_4_2_core (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    expectP ρ (fun ω : Edge N K → Bool =>
      if RobustEvent (arc ω) N K ((N : ℝ) ^ (1 - 2 * δ)) then
        ((smoothFibre N K \ sigmaSet ((N : ℝ) ^ (1 - 2 * δ)) ω).card : ℝ) else 0) ≤
      ((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card +
        2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N := by
  set M := (N : ℝ) ^ (1 - 2 * δ) with hMdef
  set U := coreU N K s₀ δ with hUdef
  set lam := max ρ (1 - ρ) with hlam
  set c : ℝ := (((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card : ℝ) with hc
  have hlam0 : 0 ≤ lam := le_trans hρ0 (le_max_left _ _)
  have hlam1 : lam ≤ 1 := max_le hρ1 (by linarith)
  have hM := core_a h
  -- Pointwise: on `𝓡`, `F₁ \ Σ ⊆ (F₁ \ 𝒰) ∪ {m ∈ 𝒰 : A_mᶜ}`.
  have hpt : ∀ ω : Edge N K → Bool,
      (if RobustEvent (arc ω) N K M then ((smoothFibre N K \ sigmaSet M ω).card : ℝ) else 0) ≤
        c + ∑ m ∈ U, (if ¬ attachEv M m ω then (1 : ℝ) else 0) := by
    intro ω
    have hnn : (0 : ℝ) ≤ c + ∑ m ∈ U, (if ¬ attachEv M m ω then (1 : ℝ) else 0) := by
      have : (0 : ℝ) ≤ ∑ m ∈ U, (if ¬ attachEv M m ω then (1 : ℝ) else 0) :=
        sum_nonneg fun m _ => by split_ifs <;> norm_num
      positivity
    split_ifs with hR
    · have hsub : smoothFibre N K \ sigmaSet M ω ⊆
          (smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m) ∪
            U.filter (fun m => ¬ attachEv M m ω) := by
        intro m hm
        obtain ⟨hmF, hmSg⟩ := mem_sdiff.mp hm
        by_cases hU : InU N K s₀ δ m
        · refine mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hmF, hU⟩, fun hA => hmSg ?_⟩)
          obtain ⟨⟨d, hd, hmd⟩, ⟨d', hd', hd'm⟩⟩ := hA
          have hgd := (mem_lowerDivisors.mp hd).2
          have hgd' := (mem_lowerDivisors.mp hd').2
          exact mem_sigmaSet.mpr ⟨(mem_filter.mp hmF).1, d, hgd,
            attach_mutual hM hR hgd hgd' hmd hd'm⟩
        · exact mem_union_left _ (mem_filter.mpr ⟨hmF, hU⟩)
      have h1 := (card_le_card hsub).trans (card_union_le _ _)
      have h2 : ((U.filter (fun m => ¬ attachEv M m ω)).card : ℝ) =
          ∑ m ∈ U, (if ¬ attachEv M m ω then (1 : ℝ) else 0) := natCast_card_filter _ _
      have h3 : ((smoothFibre N K \ sigmaSet M ω).card : ℝ) ≤
          c + ((U.filter (fun m => ¬ attachEv M m ω)).card : ℝ) := by
        rw [hc]
        exact_mod_cast h1
      linarith
    · exact hnn
  -- Each `P(A_mᶜ) ≤ 2λ^{s₀+1}`.
  have hterm : ∀ m ∈ U, expectP ρ (fun ω : Edge N K → Bool =>
      if ¬ attachEv M m ω then (1 : ℝ) else 0) ≤ 2 * lam ^ (s₀ + 1) := by
    intro m hm
    have he : expectP ρ (fun ω : Edge N K → Bool => if ¬ attachEv M m ω then (1 : ℝ) else 0) =
        prob ρ (fun ω : Edge N K → Bool => ¬ attachEv M m ω) := by
      rw [prob_eq]
      rfl
    have hmU : InU N K s₀ δ m := (mem_filter.mp hm).2
    obtain ⟨hmF, hMm⟩ := core_b h hmU
    have hmN : m ≤ N := by
      have := (mem_filter.mp hmF).1
      simp only [vertices, mem_Ioc] at this
      exact this.2
    have hs := core_c h hmU
    have hA := prob_attachEv_ge (N := N) (K := K) hρ0 hρ1 hmN hMm
    have hpow : lam ^ (lowerDivisors M K m).card ≤ lam ^ (s₀ + 1) :=
      pow_le_pow_of_le_one hlam0 hlam1 hs
    have hnot := prob_not ρ (attachEv (N := N) (K := K) M m)
    rw [he]
    linarith
  have hUN : (U.card : ℝ) ≤ N := by exact_mod_cast card_coreU_le
  have ha : 0 ≤ 2 * lam ^ (s₀ + 1) := by positivity
  calc expectP ρ (fun ω : Edge N K → Bool =>
        if RobustEvent (arc ω) N K M then ((smoothFibre N K \ sigmaSet M ω).card : ℝ) else 0)
      ≤ expectP ρ (fun ω : Edge N K → Bool =>
          c + ∑ m ∈ U, (if ¬ attachEv M m ω then (1 : ℝ) else 0)) := expectP_mono hρ0 hρ1 hpt
    _ = c + ∑ m ∈ U, expectP ρ (fun ω : Edge N K → Bool =>
          if ¬ attachEv M m ω then (1 : ℝ) else 0) := by
        rw [expectP_add, expectP_const, expectP_sum]
    _ ≤ c + ∑ _m ∈ U, 2 * lam ^ (s₀ + 1) := by
        have := sum_le_sum hterm
        linarith
    _ = c + U.card * (2 * lam ^ (s₀ + 1)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ c + 2 * lam ^ (s₀ + 1) * N := by nlinarith

open Classical in
/-- **Proposition 4.6, eq. (3).** Under the hypotheses of Lemma 4.5, in `𝒟_ρ(N, K)`,
`E[|F₁ \ Σ| · 1_𝓡] ≤ Err`, with `C₁ = 18` in `Err`. -/
theorem eq_4_2 (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    expectP ρ (fun ω : Edge N K → Bool =>
      if RobustEvent (arc ω) N K ((N : ℝ) ^ (1 - 2 * δ)) then
        ((smoothFibre N K \ sigmaSet ((N : ℝ) ^ (1 - 2 * δ)) ω).card : ℝ) else 0) ≤
      errT ρ N s₀ η δ := by
  have h1 := eq_4_2_core h hρ0 hρ1
  have h2 := core_d' h
  unfold errT
  linarith

/-! ### Markov's inequality -/

section Markov

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Markov's inequality.** For `f ≥ 0` and `c > 0`, `P(f ≥ c) ≤ E[f]/c`. -/
theorem prob_ge_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {f : (ι → Bool) → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) {c : ℝ} (hc : 0 < c) :
    prob ρ (fun ω => c ≤ f ω) ≤ expectP ρ f / c := by
  rw [le_div_iff₀ hc, prob_eq]
  have h : expectP ρ (fun ω => c * (if c ≤ f ω then (1 : ℝ) else 0)) ≤ expectP ρ f :=
    expectP_mono h0 h1 fun ω => by
      split_ifs with hω
      · linarith
      · linarith [hf ω]
  rw [expectP_const_mul] at h
  unfold expectP at h ⊢
  beta_reduce at h
  linarith

end Markov

/-! ### Corollary 1.5 -/

/-- `E|Φ_K − Ψ(N, B)| = Ψ(N, B) − E[Φ_K]`, since `Φ_K ≤ Ψ(N, B)` pointwise. -/
theorem expect_abs_eq_gap {ρ : ℝ} (N K : ℕ) :
    expectP ρ (fun ω : Edge N K → Bool => |(PhiK N K ω : ℝ) - psi N (N / (K + 1))|) =
      gap ρ N K := by
  have e : (fun ω : Edge N K → Bool => |(PhiK N K ω : ℝ) - psi N (N / (K + 1))|) =
      fun ω => (psi N (N / (K + 1)) : ℝ) - PhiK N K ω := funext fun ω => by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast PhiK_le_psi ω))]
  rw [e, expectP_sub, expectP_const]
  rfl

/-- **Corollary 1.5 (Structure of the giant).** Fix `ρ ∈ (0, 1)`. For `N ≥ N₀(ρ)`, all
`K < N` and any rule `Φ*_K` choosing a largest SCC:
(a) `E|Φ_K − Ψ(N, N/(K+1))| ≤ 30N/log log N`;
(b) `E|F₁ ∆ Φ*_K| ≤ 2K + 30N/log log N`;
(c) `E[Φ_K^{(2)}] ≤ K + 30N/log log N`. -/
theorem cor_structure {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K < N, ∀ star : (Edge N K → Bool) → Finset ℕ,
      (∀ ω, IsSCC ω (star ω) ∧ (star ω).card = PhiK N K ω) →
      expectP ρ (fun ω : Edge N K → Bool => |(PhiK N K ω : ℝ) - psi N (N / (K + 1))|) ≤
          30 * N / Real.log (Real.log N) ∧
      expectP ρ (fun ω : Edge N K → Bool => ((smoothFibre N K ∆ star ω).card : ℝ)) ≤
          2 * K + 30 * N / Real.log (Real.log N) ∧
      expectP ρ (fun ω : Edge N K → Bool => (secondSCC ω (star ω) : ℝ)) ≤
          K + 30 * N / Real.log (Real.log N) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_goodN hρ0 hρ1)
  refine ⟨N₀, fun N hN K hK star hstar => ?_⟩
  have hG := hN₀ N hN
  have hρ0' := hρ0.le
  have hρ1' := hρ1.le
  refine ⟨by rw [expect_abs_eq_gap]; exact gap_le_of_good hρ0 hρ1 hK hG, ?_⟩
  obtain ⟨hNℓ, hsmall, hlarge⟩ := rate_cases hρ0 hρ1 hK hG
  change _ ≤ 2 * K + 30 * N / ellN N ∧ _ ≤ K + 30 * N / ellN N
  have e30 : 30 * (N : ℝ) / ellN N = 30 * (N / ellN N) := by ring
  have hNℓ0 : (0 : ℝ) ≤ N / ellN N := by linarith
  rw [e30]
  by_cases hKs : (K : ℝ) ≤ (N : ℝ) ^ (1 - etaN N)
  · ---------- `K ≤ N^{1−η}`: eq. (3).
    obtain ⟨h, -, eErr, e6⟩ := hsmall hKs
    set δ := deltaN N with hδ
    set M := (N : ℝ) ^ (1 - 2 * δ) with hMdef
    have hM := core_a h
    have hM0 : 0 < M := Real.rpow_pos_of_pos h.N_pos _
    have hMN : M ≤ N := (h.rpow_le (by linarith [h.δ_pos])).trans (Real.rpow_one (N : ℝ)).le
    set fW : (Edge N K → Bool) → ℝ := fun ω =>
      if RobustEvent (arc ω) N K M then ((smoothFibre N K \ sigmaSet M ω).card : ℝ) else 0
      with hfW
    set fR : (Edge N K → Bool) → ℝ := fun ω =>
      if ¬ RobustEvent (arc ω) N K M then (1 : ℝ) else 0 with hfR
    have hEW : expectP ρ fW ≤ 28 * N / ellN N := (eq_4_2 h hρ0' hρ1').trans eErr
    have hER : (N : ℝ) * expectP ρ fR ≤ 1 := by
      have hp := prob_not_robust_exp (N := N) (K := K) hρ0' hρ1' hM0 hMN
      rw [h.N_div_M] at hp
      have he : expectP ρ fR = prob ρ (fun ω : Edge N K → Bool => ¬ RobustEvent (arc ω) N K M) := by
        rw [prob_eq]
        rfl
      rw [he]
      have := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)
      have e : (N : ℝ) * ((N : ℝ) ^ 2 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2))) =
          (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2)) := by ring
      linarith
    have e28 : 28 * (N : ℝ) / ellN N = 28 * (N / ellN N) := by ring
    have hlin : ∀ c : ℝ, expectP ρ (fun ω => fW ω + c + N * fR ω) =
        expectP ρ fW + c + N * expectP ρ fR := fun c => by
      rw [expectP_add, expectP_add, expectP_const, expectP_const_mul]
    -- Pointwise bounds: `W + 2K` (resp. `W + K`) on `𝓡`, and `N` off `𝓡`.
    have hptb : ∀ ω, ((smoothFibre N K ∆ star ω).card : ℝ) ≤ fW ω + 2 * K + N * fR ω := by
      intro ω
      by_cases hR : RobustEvent (arc ω) N K M
      · have := (giant_pointwise hM hMN hR (hstar ω).1 (hstar ω).2).1
        simp only [hfW, hfR, hR, ↓reduceIte, not_true_eq_false, mul_zero, add_zero]
        exact_mod_cast this
      · obtain ⟨v, -, hv⟩ := (hstar ω).1
        have := card_symmDiff_le_N (N := N) (K := K) (hv ▸ sccOf_subset ω v)
        simp only [hfW, hfR, hR, ↓reduceIte, not_false_eq_true, mul_one, zero_add]
        have : ((smoothFibre N K ∆ star ω).card : ℝ) ≤ N := by exact_mod_cast this
        linarith [Nat.cast_nonneg (α := ℝ) K]
    have hptc : ∀ ω, (secondSCC ω (star ω) : ℝ) ≤ fW ω + K + N * fR ω := by
      intro ω
      by_cases hR : RobustEvent (arc ω) N K M
      · have := (giant_pointwise hM hMN hR (hstar ω).1 (hstar ω).2).2
        simp only [hfW, hfR, hR, ↓reduceIte, not_true_eq_false, mul_zero, add_zero]
        exact_mod_cast this
      · have := (secondSCC_le_PhiK ω (star ω)).trans (PhiK_le_N ω)
        simp only [hfW, hfR, hR, ↓reduceIte, not_false_eq_true, mul_one, zero_add]
        have : (secondSCC ω (star ω) : ℝ) ≤ N := by exact_mod_cast this
        linarith [Nat.cast_nonneg (α := ℝ) K]
    have hb := (expectP_mono hρ0' hρ1' hptb).trans_eq (hlin _)
    have hc := (expectP_mono hρ0' hρ1' hptc).trans_eq (hlin _)
    constructor <;> linarith
  · ---------- `K > N^{1−η}`: everything is at most `Ψ(N, B) ≤ 3N/ℓ`.
    have hΨ := hlarge hKs
    have hF : ((smoothFibre N K).card : ℝ) ≤ psi N (N / (K + 1)) := by
      have := card_smoothFibre (N := N) (K := K) hK.le
      exact_mod_cast (show (smoothFibre N K).card ≤ psi N (N / (K + 1)) by omega)
    have hptb : ∀ ω, ((smoothFibre N K ∆ star ω).card : ℝ) ≤
        (fun _ : Edge N K → Bool => 2 * (psi N (N / (K + 1)) : ℝ)) ω := by
      intro ω
      have h1 := card_symmDiff_le (N := N) (K := K) (S := star ω)
      have h2 : ((star ω).card : ℝ) ≤ psi N (N / (K + 1)) := by
        rw [(hstar ω).2]
        exact_mod_cast PhiK_le_psi ω
      have h3 : ((smoothFibre N K ∆ star ω).card : ℝ) ≤
          (smoothFibre N K).card + (star ω).card := by exact_mod_cast h1
      dsimp only
      linarith
    have hptc : ∀ ω, (secondSCC ω (star ω) : ℝ) ≤
        (fun _ : Edge N K → Bool => (psi N (N / (K + 1)) : ℝ)) ω := fun ω => by
      dsimp only
      exact_mod_cast (secondSCC_le_PhiK ω (star ω)).trans (PhiK_le_psi ω)
    have hb := (expectP_mono hρ0' hρ1' hptb).trans_eq (expectP_const _ _)
    have hc := (expectP_mono hρ0' hρ1' hptc).trans_eq (expectP_const _ _)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    constructor <;> linarith

/-- **Corollary 1.5(a), in probability.** For every `ε > 0`,
`max_{K < N} P(|Φ_K/N − Ψ(N, N/(K+1))/N| ≥ ε) → 0`. -/
theorem cor_structure_prob {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => ⨆ K : Fin N, prob ρ (fun ω : Edge N K → Bool =>
      ε ≤ |(PhiK N K ω : ℝ) / N - (psi N (N / (K + 1)) : ℝ) / N|)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 30 / ε / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_log_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun N => Real.iSup_nonneg fun K => prob_nonneg hρ0.le hρ1.le _
  · filter_upwards [eventually_goodN hρ0 hρ1, eventually_ge_atTop 1] with N hG hN1
    have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    refine ciSup_le fun K => ?_
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hεN : 0 < ε * N := mul_pos hε hNpos
    have hmono : prob ρ (fun ω : Edge N K → Bool =>
          ε ≤ |(PhiK N K ω : ℝ) / N - (psi N (N / (K + 1)) : ℝ) / N|) ≤
        prob ρ (fun ω : Edge N K → Bool =>
          ε * N ≤ |(PhiK N K ω : ℝ) - psi N (N / (K + 1))|) := by
      refine prob_mono hρ0.le hρ1.le fun ω hω => ?_
      rw [← sub_div, abs_div, abs_of_pos hNpos, le_div_iff₀ hNpos] at hω
      exact hω
    have hmarkov := prob_ge_le hρ0.le hρ1.le (f := fun ω : Edge N K → Bool =>
      |(PhiK N K ω : ℝ) - psi N (N / (K + 1))|) (fun ω => abs_nonneg _) hεN
    rw [expect_abs_eq_gap] at hmarkov
    have hgap := gap_le_of_good hρ0 hρ1 K.2 hG
    have hℓ : 0 < Real.log (Real.log N) := by linarith [hG.p0]
    have e : gap ρ N K / (ε * N) ≤ 30 / ε / Real.log (Real.log N) := by
      rw [div_le_div_iff₀ hεN hℓ]
      have := mul_le_mul_of_nonneg_left hgap hℓ.le
      rw [mul_div_cancel₀ _ hℓ.ne'] at this
      have e2 : 30 / ε * (ε * N) = 30 * N := by field_simp
      nlinarith
    exact hmono.trans (hmarkov.trans e)

/-- **After Corollary 1.5: the case `K = o(N)`.** If `K(N)/N → 0`, then for every `ε > 0` and any
rule choosing a largest SCC, `P(|F₁ △ Φ*_K| ≥ εN) → 0` and `P(Φ^{(2)}_K ≥ εN) → 0`. This is
Markov's inequality applied to (b) and (c). -/
theorem cor_structure_whp {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ}
    (hK : Tendsto (fun N : ℕ => (K N : ℝ) / N) atTop (𝓝 0))
    (star : ∀ N, (Edge N (K N) → Bool) → Finset ℕ)
    (hstar : ∀ N, K N < N → ∀ ω, IsSCC ω (star N ω) ∧ (star N ω).card = PhiK N (K N) ω)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => prob ρ (fun ω : Edge N (K N) → Bool =>
      ε * N ≤ ((smoothFibre N (K N) ∆ star N ω).card : ℝ))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => prob ρ (fun ω : Edge N (K N) → Bool =>
      ε * N ≤ (secondSCC ω (star N ω) : ℝ))) atTop (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := cor_structure hρ0 hρ1
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_nat
  have hlim : ∀ c : ℝ, Tendsto (fun N : ℕ =>
      (c * ((K N : ℝ) / N) + 30 / Real.log (Real.log N)) / ε) atTop (𝓝 0) := fun c => by
    have := ((hK.const_mul c).add
      ((tendsto_const_nhds (x := (30 : ℝ))).div_atTop hll)).div_const ε
    simpa using this
  have hKN : ∀ᶠ N : ℕ in atTop, K N < N := by
    filter_upwards [hK.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_ge_atTop 1] with N h hN1
    have hN : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [div_lt_one hN] at h
    exact_mod_cast h
  have key : ∀ (c : ℝ) (g : ∀ N, (Edge N (K N) → Bool) → ℝ), (∀ N ω, 0 ≤ g N ω) →
      (∀ N ≥ N₀, K N < N → expectP ρ (g N) ≤ c * K N + 30 * N / Real.log (Real.log N)) →
      Tendsto (fun N : ℕ => prob ρ (fun ω : Edge N (K N) → Bool => ε * N ≤ g N ω)) atTop
        (𝓝 0) := by
    intro c g hg hE
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlim c) ?_ ?_
    · exact Eventually.of_forall fun N => prob_nonneg hρ0.le hρ1.le _
    · filter_upwards [hKN, eventually_ge_atTop N₀, eventually_ge_atTop 1,
        hll.eventually_gt_atTop 0] with N hKN hN hN1 hℓ
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have hεN : 0 < ε * N := mul_pos hε hNpos
      calc prob ρ (fun ω : Edge N (K N) → Bool => ε * N ≤ g N ω)
          ≤ expectP ρ (g N) / (ε * N) := prob_ge_le hρ0.le hρ1.le (hg N) hεN
        _ ≤ (c * K N + 30 * N / Real.log (Real.log N)) / (ε * N) :=
            div_le_div_of_nonneg_right (hE N hN hKN) hεN.le
        _ = (c * ((K N : ℝ) / N) + 30 / Real.log (Real.log N)) / ε := by
            field_simp
  refine ⟨key 2 (fun N ω => ((smoothFibre N (K N) ∆ star N ω).card : ℝ))
      (fun _ _ => Nat.cast_nonneg _) fun N hN hKN => ?_,
    key 1 (fun N ω => (secondSCC ω (star N ω) : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      fun N hN hKN => ?_⟩
  · exact (hN₀ N hN (K N) hKN (star N) (hstar N hKN)).2.1
  · simpa using (hN₀ N hN (K N) hKN (star N) (hstar N hKN)).2.2

end HubRemoval
