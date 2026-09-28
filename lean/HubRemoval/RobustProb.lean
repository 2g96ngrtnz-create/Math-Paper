import HubRemoval.Orientation
import HubRemoval.Robust

/-!
# Robust edges: the probability bound (paper, Lemma 4.1)

In the random orientation `𝒟_ρ(N, K)`, put `q = ρ(1 − ρ)`.

**Lemma 4.1.** For real `M > 0`, `P(𝓡ᶜ) ≤ M² (1 − q)^{N/M − 2}`. If also `M ≤ N`, then
`P(𝓡ᶜ) ≤ N² exp(−q (N/M − 2))`. (In the paper `M = N^{1−2δ}`, so `N/M = N^{2δ}`.)

The proof is the paper's.
* Fix a pair `K < x < x' ≤ M` with `x ∣ x'`. For each multiple `y` of `x'` in `(x', N]`, the event
  `E_y = {x → y → x'}` says that the edge `(x, y)` is reversed and `(x', y)` is not. It is a
  cylinder on two edges, so `P(E_y) = q` (`prob_pat`).
* Distinct `y` use disjoint pairs of edges, so the events `E_yᶜ` are independent, and
  `P(no E_y occurs) = (1 − q)^{|𝒴|} ≤ (1 − q)^{N/M − 2}` (`prob_no_pat`).
* The same holds for `E'_y = {x' → y → x}`. If neither family fails for any pair, then `𝓡`
  holds. There are at most `⌊M⌋²/2` pairs (`two_mul_card_edges_le`), and the union bound finishes
  the proof.
-/

namespace HubRemoval

open Finset

variable {N K : ℕ}

theorem prob_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {A B : (ι → Bool) → Prop}
    (h : ∀ ω, A ω ↔ B ω) : prob ρ A = prob ρ B := by
  have : A = B := funext fun ω => propext (h ω)
  rw [this]

/-- The witness pattern at `y`: the edge `(a, y)` is reversed and `(b, y)` is not. For
`(a, b) = (x, x')` this is `x → y → x'`; for `(a, b) = (x', x)` it is `x' → y → x`. -/
def pat (a b y : ℕ) (ω : Edge N K → Bool) : Prop := bit ω a y = true ∧ bit ω b y = false

instance {a b y : ℕ} : DecidablePred (pat (N := N) (K := K) a b y) := fun ω => by
  unfold pat
  infer_instance

/-- The coordinates that `pat a b y` reads. -/
def patBlock (N K a b y : ℕ) : Finset (Edge N K) :=
  univ.filter fun e => e.val = (a, y) ∨ e.val = (b, y)

/-- **A two-edge cylinder.** `P(pat a b y) = ρ(1 − ρ)`. -/
theorem prob_pat (ρ : ℝ) {a b y : ℕ} (hab : a ≠ b) (ha : (a, y) ∈ edges N K)
    (hb : (b, y) ∈ edges N K) : prob ρ (pat (N := N) (K := K) a b y) = ρ * (1 - ρ) := by
  set e₁ : Edge N K := ⟨(a, y), ha⟩
  set e₂ : Edge N K := ⟨(b, y), hb⟩
  have hne : e₁ ≠ e₂ := fun h => hab (congrArg (fun e : Edge N K => e.val.1) h)
  have hiff : ∀ ω : Edge N K → Bool, pat a b y ω ↔
      ∀ e ∈ ({e₁, e₂} : Finset (Edge N K)), ω e = decide (e = e₁) := by
    intro ω
    have h1 : bit ω a y = ω e₁ := dite_eq_left ha
    have h2 : bit ω b y = ω e₂ := dite_eq_left hb
    simp only [pat, h1, h2, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      decide_true, hne.symm, decide_false]
  rw [prob_congr hiff, prob_cylinder, prod_pair hne]
  simp [pb, hne.symm]

theorem pat_dependsOn {a b y : ℕ} :
    DependsOnCoords (fun ω : Edge N K → Bool => if pat a b y ω then (0 : ℝ) else 1)
      (patBlock N K a b y) := by
  intro ω ω' h
  have h1 : bit ω a y = bit ω' a y :=
    bit_congr fun e he => h e (mem_filter.mpr ⟨mem_univ e, Or.inl he⟩)
  have h2 : bit ω b y = bit ω' b y :=
    bit_congr fun e he => h e (mem_filter.mpr ⟨mem_univ e, Or.inr he⟩)
  simp only [pat, h1, h2]

/-- **Independence over witnesses.** If `(a, y)` and `(b, y)` are edges for every `y ∈ W`, then
`P(pat a b y fails for every y ∈ W) = (1 − ρ(1 − ρ))^{|W|}`. -/
theorem prob_no_pat (ρ : ℝ) {a b : ℕ} (hab : a ≠ b) (W : Finset ℕ)
    (hW : ∀ y ∈ W, (a, y) ∈ edges N K ∧ (b, y) ∈ edges N K) :
    prob ρ (fun ω : Edge N K → Bool => ∀ y ∈ W, ¬ pat a b y ω) = (1 - ρ * (1 - ρ)) ^ W.card := by
  classical
  have hind : prob ρ (fun ω : Edge N K → Bool => ∀ y ∈ W, ¬ pat a b y ω) =
      expectP ρ (fun ω : Edge N K → Bool => ∏ y ∈ W, (if pat a b y ω then (0 : ℝ) else 1)) := by
    rw [prob_eq]
    unfold expectP
    refine sum_congr rfl fun ω _ => ?_
    congr 1
    by_cases hall : ∀ y ∈ W, ¬ pat a b y ω
    · rw [ite_eq_left hall]
      exact (prod_eq_one fun y hy => by simp [hall y hy]).symm
    · rw [ite_eq_right hall]
      push Not at hall
      obtain ⟨y, hy, hp⟩ := hall
      exact (prod_eq_zero hy (by simp [hp])).symm
  have hdisj : (W : Set ℕ).PairwiseDisjoint (patBlock N K a b) := by
    intro y _ y' _ hyy'
    refine disjoint_left.mpr fun e he he' => hyy' ?_
    simp only [patBlock, mem_filter, mem_univ, true_and] at he he'
    rcases he with h | h <;> rcases he' with h' | h' <;>
      exact congrArg Prod.snd (h.symm.trans h')
  rw [hind, expectP_prod_of_pairwiseDisjoint ρ W (patBlock N K a b)
    (fun y (ω : Edge N K → Bool) => if pat a b y ω then (0 : ℝ) else 1) hdisj
    (fun y _ => pat_dependsOn)]
  rw [← prod_const]
  refine prod_congr rfl fun y hy => ?_
  have hnot := prob_not ρ (pat (N := N) (K := K) a b y)
  rw [prob_pat ρ hab (hW y hy).1 (hW y hy).2] at hnot
  rw [← hnot, prob_eq]
  unfold expectP
  refine sum_congr rfl fun ω _ => ?_
  by_cases hp : pat a b y ω <;> simp [hp]

/-- `2 · |edges(L, K)| ≤ L²`: an edge `(a, b)` has `a < b`, and its mirror image has `a > b`. -/
theorem two_mul_card_edges_le (L K : ℕ) : 2 * (edges L K).card ≤ L ^ 2 := by
  set E := edges L K
  have hswap : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) := Prod.swap_injective
  have hdisj : Disjoint E (E.image Prod.swap) := by
    refine disjoint_left.mpr fun p hp hp' => ?_
    obtain ⟨⟨u, v⟩, hq, rfl⟩ := mem_image.mp hp'
    have h1 := (mem_edges.mp hq).2.1
    have h2 := (mem_edges.mp (show (v, u) ∈ edges L K from hp)).2.1
    omega
  have hsub : E ∪ E.image Prod.swap ⊆ Icc 1 L ×ˢ Icc 1 L := by
    rintro ⟨u, v⟩ hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨h1, h2, h3, -⟩ := mem_edges.mp hp
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Icc.mpr ⟨by omega, h3⟩⟩
    · obtain ⟨⟨u', v'⟩, hq, he⟩ := mem_image.mp hp
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, h2, h3, -⟩ := mem_edges.mp hq
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, h3⟩, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have h := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ hswap, card_product,
    Nat.card_Icc, Nat.add_sub_cancel] at h
  nlinarith

/-- If the robust event fails, some pair `(x, x')` has no witness in one direction. -/
theorem exists_bad_pair {ω : Edge N K → Bool} {M : ℝ} (h : ¬ RobustEvent (arc ω) N K M) :
    ∃ p ∈ edges ⌊M⌋₊ K,
      (∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat p.1 p.2 y ω) ∨
      (∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat p.2 p.1 y ω) := by
  by_contra hall
  push Not at hall
  apply h
  intro x x' hKx hxx' hx'M hdvd
  have hM0 : 0 ≤ M := le_trans (Nat.cast_nonneg x') hx'M
  have hp : (x, x') ∈ edges ⌊M⌋₊ K := mem_edges.mpr ⟨hKx, hxx', Nat.le_floor hx'M, hdvd⟩
  obtain ⟨⟨y, hy, hfwd⟩, ⟨y', hy', hbwd⟩⟩ := hall (x, x') hp
  obtain ⟨hyI, hy'dvd⟩ := mem_filter.mp hy
  obtain ⟨hxy, hyN⟩ := mem_Ioc.mp hyI
  obtain ⟨hy'I, hy''dvd⟩ := mem_filter.mp hy'
  obtain ⟨hxy', hy'N⟩ := mem_Ioc.mp hy'I
  have e1 : (x, y) ∈ edges N K := mem_edges.mpr ⟨hKx, by omega, hyN, hdvd.trans hy'dvd⟩
  have e2 : (x', y) ∈ edges N K := mem_edges.mpr ⟨by omega, hxy, hyN, hy'dvd⟩
  have e3 : (x, y') ∈ edges N K := mem_edges.mpr ⟨hKx, by omega, hy'N, hdvd.trans hy''dvd⟩
  have e4 : (x', y') ∈ edges N K := mem_edges.mpr ⟨by omega, hxy', hy'N, hy''dvd⟩
  refine ⟨⟨y, by omega, hyN, hy'dvd, (arc_of_edge e1).1.mpr hfwd.1,
    (arc_of_edge e2).2.mpr hfwd.2⟩, ⟨y', by omega, hy'N, hy''dvd,
    (arc_of_edge e4).1.mpr hbwd.1, (arc_of_edge e3).2.mpr hbwd.2⟩⟩

/-- **Lemma 4.1, the probability bound.** For `0 ≤ ρ ≤ 1` and real `M > 0`,
`P(𝓡ᶜ) ≤ M² (1 − q)^{N/M − 2}` with `q = ρ(1 − ρ)`. -/
theorem prob_not_robust {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {M : ℝ} (hM : 0 < M) :
    prob ρ (fun ω : Edge N K → Bool => ¬ RobustEvent (arc ω) N K M) ≤
      M ^ 2 * (1 - ρ * (1 - ρ)) ^ ((N : ℝ) / M - 2) := by
  set b := 1 - ρ * (1 - ρ) with hb
  set t := (N : ℝ) / M - 2 with ht
  set L := ⌊M⌋₊
  have hq : ρ * (1 - ρ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
  have hb0 : 0 < b := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  have hbt : 0 ≤ b ^ t := Real.rpow_nonneg hb0.le t
  -- The bound for one pair and one direction.
  have hone : ∀ p ∈ edges L K, ∀ a c : ℕ, (a = p.1 ∧ c = p.2 ∨ a = p.2 ∧ c = p.1) →
      prob ρ (fun ω : Edge N K → Bool => ∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat a c y ω) ≤
        b ^ t := by
    intro p hp a c hac
    obtain ⟨h1, h2, h3, h4⟩ := mem_edges.mp (show (p.1, p.2) ∈ edges L K from hp)
    have hW : ∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), (a, y) ∈ edges N K ∧ (c, y) ∈ edges N K := by
      intro y hy
      obtain ⟨hyI, hdy⟩ := mem_filter.mp hy
      obtain ⟨hpy, hyN⟩ := mem_Ioc.mp hyI
      have ep1 : (p.1, y) ∈ edges N K := mem_edges.mpr ⟨h1, by omega, hyN, h4.trans hdy⟩
      have ep2 : (p.2, y) ∈ edges N K := mem_edges.mpr ⟨by omega, hpy, hyN, hdy⟩
      rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ep1, ep2⟩
      · exact ⟨ep2, ep1⟩
    have hac' : a ≠ c := by rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    rw [prob_no_pat ρ hac' _ hW, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hb0 hb1
    have hp2M : (p.2 : ℝ) ≤ M := by
      have : (p.2 : ℝ) ≤ L := by exact_mod_cast h3
      exact this.trans (Nat.floor_le hM.le)
    exact card_multiples_Ioc_ge N (by omega) hp2M
  calc prob ρ (fun ω : Edge N K → Bool => ¬ RobustEvent (arc ω) N K M)
      ≤ prob ρ (fun ω : Edge N K → Bool => ∃ p ∈ edges L K,
          (fun p ω => (∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat p.1 p.2 y ω) ∨
            (∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat p.2 p.1 y ω)) p ω) :=
        prob_mono hρ0 hρ1 fun ω h => exists_bad_pair h
    _ ≤ ∑ p ∈ edges L K, prob ρ (fun ω : Edge N K → Bool =>
          (∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat p.1 p.2 y ω) ∨
            (∀ y ∈ (Ioc p.2 N).filter (p.2 ∣ ·), ¬ pat p.2 p.1 y ω)) :=
        prob_exists_le hρ0 hρ1 _ _
    _ ≤ ∑ _p ∈ edges L K, 2 * b ^ t := by
        refine sum_le_sum fun p hp => (prob_or_le hρ0 hρ1 _ _).trans ?_
        have h1 := hone p hp p.1 p.2 (Or.inl ⟨rfl, rfl⟩)
        have h2 := hone p hp p.2 p.1 (Or.inr ⟨rfl, rfl⟩)
        linarith
    _ = (2 * (edges L K).card : ℕ) * b ^ t := by rw [sum_const, nsmul_eq_mul]; push_cast; ring
    _ ≤ (L ^ 2 : ℕ) * b ^ t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast two_mul_card_edges_le L K) hbt
    _ ≤ M ^ 2 * b ^ t := by
        refine mul_le_mul_of_nonneg_right ?_ hbt
        push_cast
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hM.le) 2

/-- **Lemma 4.1, the paper's second form.** If `0 < M ≤ N`, then
`P(𝓡ᶜ) ≤ N² exp(−q (N/M − 2))`. -/
theorem prob_not_robust_exp {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {M : ℝ} (hM : 0 < M)
    (hMN : M ≤ N) :
    prob ρ (fun ω : Edge N K → Bool => ¬ RobustEvent (arc ω) N K M) ≤
      (N : ℝ) ^ 2 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) / M - 2)) := by
  set q := ρ * (1 - ρ)
  set t := (N : ℝ) / M - 2
  have hq0 : 0 ≤ q := mul_nonneg hρ0 (by linarith)
  have hq : q ≤ 1 / 4 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
  have hN1 : (1 : ℝ) ≤ N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le hM hMN
    have hN : 0 < N := by exact_mod_cast this
    exact_mod_cast hN
  rcases le_or_gt 0 t with ht | ht
  · refine (prob_not_robust hρ0 hρ1 hM).trans ?_
    have hbase : (1 - q) ^ t ≤ Real.exp (-q) ^ t :=
      Real.rpow_le_rpow (by linarith) (Real.one_sub_le_exp_neg q) ht
    rw [← Real.exp_mul] at hbase
    have hM2 : M ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hM.le hMN 2
    have h1 : 0 ≤ (1 - q) ^ t := Real.rpow_nonneg (by linarith) t
    calc M ^ 2 * (1 - q) ^ t ≤ (N : ℝ) ^ 2 * (1 - q) ^ t := mul_le_mul_of_nonneg_right hM2 h1
      _ ≤ (N : ℝ) ^ 2 * Real.exp (-q * t) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
  · refine (prob_le_one hρ0 hρ1 _).trans ?_
    have h1 : 1 ≤ Real.exp (-q * t) := Real.one_le_exp (by nlinarith)
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith

end HubRemoval
