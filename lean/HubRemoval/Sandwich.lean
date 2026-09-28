import Mathlib

/-!
# The sandwich lemma (paper, Lemma 6.2)

`G_N` is the divisor graph on `[N] = {1, …, N}`. For `T ⊆ [N]`, `deg_T(v)` is the degree of `v` in
`G_N − T`, that is, the number of `w ∈ [N] \ T` with `w ≠ v` and `w ∣ v` or `v ∣ w`. We write
`deg = deg_∅`, and `τ̂` for any bound on `τ(n)` over `n ≤ N` (the paper takes `τ̂ = τ_N`).

**Lemma 6.2.** Let `0 < ε ≤ 1/2` and `1 ≤ K < N` with `(N/K)(ε/2) ≥ τ̂ + 5`. If `T` is a static
or an adaptive top-`K` set, then `{v ≥ 1 : v ≤ (1−ε)K} ⊆ T ⊆ {t : t ≤ (1+ε)K}`.

* **Static:** `|T| = K`, and `deg(t) ≥ deg(v)` for all `t ∈ T` and `v ∈ [N] \ T`.
* **Adaptive:** `T = {u₀, …, u_{K−1}}`, where `u_j` has maximal degree in `G_N − {u₀, …, u_{j−1}}`.

The paper states the conclusion with floors, `{1, …, ⌊(1−ε)K⌋} ⊆ T ⊆ {1, …, ⌊(1+ε)K⌋}`. For
natural numbers `v ≤ (1±ε)K` is the same as `v ≤ ⌊(1±ε)K⌋`.

The two degree estimates used are:
* `deg(v) ≤ τ(v) + N/v` (`deg_le`), which gives the paper's `deg_T(m) ≤ deg(m) ≤ τ_N + N/m`;
* if `T ⊆ [1, A]` and `v ≤ A ≤ N`, then `deg_T(v) ≥ N/v − A/v − 1` (`degT_ge`), by counting the
  multiples of `v` in `(A, N]`.
-/

namespace HubRemoval

open Finset

/-- The neighbours of `v` in `G_N − T`. -/
def nbrs (N : ℕ) (T : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (Icc 1 N \ T).filter fun w => w ≠ v ∧ (w ∣ v ∨ v ∣ w)

/-- `deg_T(v)`: the degree of `v` in `G_N − T`. -/
def degT (N : ℕ) (T : Finset ℕ) (v : ℕ) : ℕ := (nbrs N T v).card

/-- `deg(v)`: the degree of `v` in `G_N`. -/
abbrev deg (N v : ℕ) : ℕ := degT N ∅ v

/-- Removing vertices cannot increase a degree. -/
theorem degT_le_deg (N : ℕ) (T : Finset ℕ) (v : ℕ) : degT N T v ≤ deg N v :=
  card_le_card (filter_subset_filter _ (sdiff_subset_sdiff subset_rfl (empty_subset T)))

/-- `deg(v) ≤ τ(v) + N/v`: a neighbour is a divisor of `v` or a multiple of `v` in `[N]`. -/
theorem deg_le (N : ℕ) {v : ℕ} (hv : 1 ≤ v) :
    (deg N v : ℝ) ≤ v.divisors.card + (N : ℝ) / v := by
  have hsub : nbrs N ∅ v ⊆ v.divisors ∪ (Ioc 0 N).filter (v ∣ ·) := by
    intro w hw
    simp only [nbrs, sdiff_empty, mem_filter, mem_Icc] at hw
    obtain ⟨⟨hw1, hwN⟩, -, hd⟩ := hw
    rcases hd with hd | hd
    · exact mem_union_left _ (Nat.mem_divisors.mpr ⟨hd, by omega⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hwN⟩, hd⟩)
  have h1 : deg N v ≤ v.divisors.card + N / v := by
    have := (card_le_card hsub).trans (card_union_le _ _)
    rwa [Nat.Ioc_filter_dvd_card_eq_div] at this
  have h2 : (deg N v : ℝ) ≤ v.divisors.card + ((N / v : ℕ) : ℝ) := by exact_mod_cast h1
  linarith [Nat.cast_div_le (α := ℝ) (m := N) (n := v)]

/-- The multiples of `v` in `(A, N]` number `⌊N/v⌋ − ⌊A/v⌋`. -/
theorem card_Ioc_filter_dvd {A N : ℕ} (hAN : A ≤ N) (v : ℕ) :
    ((Ioc A N).filter (v ∣ ·)).card = N / v - A / v := by
  have hsplit : (Ioc 0 N).filter (v ∣ ·) =
      (Ioc 0 A).filter (v ∣ ·) ∪ (Ioc A N).filter (v ∣ ·) := by
    rw [← filter_union, Ioc_union_Ioc_eq_Ioc (Nat.zero_le A) hAN]
  have hdisj : Disjoint ((Ioc 0 A).filter (v ∣ ·)) ((Ioc A N).filter (v ∣ ·)) :=
    disjoint_filter_filter (Ioc_disjoint_Ioc_of_le le_rfl)
  have h := congrArg card hsplit
  rw [card_union_of_disjoint hdisj, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at h
  omega

/-- If every removed vertex is `≤ A` and `1 ≤ v ≤ A ≤ N`, the multiples of `v` in `(A, N]` are
all neighbours of `v` in `G_N − T`. So `deg_T(v) ≥ N/v − A/v − 1`. -/
theorem degT_ge {N A v : ℕ} {T : Finset ℕ} (hv : 1 ≤ v) (hvA : v ≤ A) (hAN : A ≤ N)
    (hT : ∀ t ∈ T, t ≤ A) : (N : ℝ) / v - A / v - 1 ≤ degT N T v := by
  have hsub : (Ioc A N).filter (v ∣ ·) ⊆ nbrs N T v := by
    intro w hw
    obtain ⟨hwI, hd⟩ := mem_filter.mp hw
    obtain ⟨hAw, hwN⟩ := mem_Ioc.mp hwI
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, hwN⟩, fun hwT => ?_⟩,
      by omega, Or.inr hd⟩
    have := hT w hwT
    omega
  have h1 := card_le_card hsub
  rw [card_Ioc_filter_dvd hAN] at h1
  have hdiv : A / v ≤ N / v := Nat.div_le_div_right hAN
  have h2 : ((N / v : ℕ) : ℝ) - ((A / v : ℕ) : ℝ) ≤ degT N T v := by
    rw [← Nat.cast_sub hdiv]
    exact_mod_cast h1
  have h3 : (N : ℝ) / v - 1 ≤ ((N / v : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((N : ℝ) / v)
    rw [Nat.floor_div_eq_div] at h
    linarith
  have h4 := Nat.cast_div_le (α := ℝ) (m := A) (n := v)
  linarith

/-- `1/(1+ε) ≤ 1 − ε/2` for `0 ≤ ε ≤ 1`. -/
theorem inv_one_add_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : 1 / (1 + ε) ≤ 1 - ε / 2 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `1/(1−ε) − 1/(1−ε/2) ≥ ε/2` for `0 < ε ≤ 1/2`. -/
theorem inv_gap {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    ε / 2 ≤ 1 / (1 - ε) - 1 / (1 - ε / 2) := by
  have ha : 0 < 1 - ε := by linarith
  have hb : 0 < 1 - ε / 2 := by linarith
  rw [div_sub_div _ _ ha.ne' hb.ne', le_div_iff₀ (mul_pos ha hb)]
  have hprod : (1 - ε) * (1 - ε / 2) ≤ 1 := by nlinarith
  have := mul_le_of_le_one_right (by linarith : (0 : ℝ) ≤ ε / 2) hprod
  linarith

/-- `N/w < (N/K) · (1/c)` when `w > cK > 0`. -/
theorem div_lt_of_gt {N K : ℕ} {c w : ℝ} (hN : 0 < N) (hK : 0 < K) (hc : 0 < c)
    (hw : c * K < w) : (N : ℝ) / w < (N : ℝ) / K * (1 / c) := by
  have hcK : 0 < c * (K : ℝ) := mul_pos hc (by exact_mod_cast hK)
  calc (N : ℝ) / w < (N : ℝ) / (c * K) := div_lt_div_of_pos_left (by exact_mod_cast hN) hcK hw
    _ = (N : ℝ) / K * (1 / c) := by field_simp

/-- `N/v ≥ (N/K) · (1/c)` when `0 < v ≤ cK`. -/
theorem div_ge_of_le {N K : ℕ} {c v : ℝ} (hK : 0 < K) (hc : 0 < c) (hv : 0 < v)
    (hvK : v ≤ c * K) : (N : ℝ) / K * (1 / c) ≤ (N : ℝ) / v := by
  have hcK : 0 < c * (K : ℝ) := mul_pos hc (by exact_mod_cast hK)
  calc (N : ℝ) / K * (1 / c) = (N : ℝ) / (c * K) := by field_simp
    _ ≤ (N : ℝ) / v := div_le_div_of_nonneg_left (Nat.cast_nonneg N) hv hvK

/-- A finite set of positive integers all `≤ x`, with `x < K`, has fewer than `K` elements. -/
theorem card_lt_of_le {S : Finset ℕ} {x : ℝ} {K : ℕ} (hx : 0 ≤ x) (hxK : x < K)
    (hS : ∀ s ∈ S, 1 ≤ s ∧ (s : ℝ) ≤ x) : S.card < K := by
  have hsub : S ⊆ Icc 1 ⌊x⌋₊ := fun s hs =>
    mem_Icc.mpr ⟨(hS s hs).1, Nat.le_floor (hS s hs).2⟩
  have h1 := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  exact lt_of_le_of_lt h1 ((Nat.floor_lt hx).mpr hxK)

/-! ### The static attack -/

/-- **Lemma 6.2, static attack.** -/
theorem sandwich_static {N K : ℕ} {ε τ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hK : 1 ≤ K)
    (hKN : K < N) (hτ : ∀ n, 1 ≤ n → n ≤ N → (n.divisors.card : ℝ) ≤ τ)
    (hgap : τ + 5 ≤ (N : ℝ) / K * (ε / 2))
    {T : Finset ℕ} (hTN : T ⊆ Icc 1 N) (hTK : T.card = K)
    (hstatic : ∀ t ∈ T, ∀ v ∈ Icc 1 N, v ∉ T → deg N v ≤ deg N t) :
    (∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ (1 - ε) * K → v ∈ T) ∧
      (∀ t ∈ T, (t : ℝ) ≤ (1 + ε) * K) := by
  have hN0 : 0 < N := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hXpos : 0 < (N : ℝ) / K := div_pos (by exact_mod_cast hN0) hKR
  set X := (N : ℝ) / K with hXdef
  -- `deg(v) ≥ N/v − 2`, from `degT_ge` with `A = v` and `T = ∅`.
  have hdeg_ge : ∀ v, 1 ≤ v → v ≤ N → (N : ℝ) / v - 2 ≤ deg N v := by
    intro v hv hvN
    have := degT_ge (T := ∅) hv le_rfl hvN (by simp)
    have hvv : (v : ℝ) / v = 1 := div_self (by positivity)
    linarith
  -- `deg(w) ≤ τ̂ + N/w`.
  have hdeg_le : ∀ w, 1 ≤ w → w ≤ N → (deg N w : ℝ) ≤ τ + (N : ℝ) / w := fun w hw hwN =>
    (deg_le N hw).trans (by linarith [hτ w hw hwN])
  have hT1 : ∀ t ∈ T, 1 ≤ t ∧ t ≤ N := fun t ht => mem_Icc.mp (hTN ht)
  constructor
  · -- Lower inclusion.
    intro v hv hvK
    by_contra hvT
    have hvKn : v ≤ K := by
      have : (v : ℝ) ≤ K := hvK.trans (by nlinarith)
      exact_mod_cast this
    have hvN : v ∈ Icc 1 N := mem_Icc.mpr ⟨hv, by omega⟩
    -- Every `t ∈ T` is `≤ (1 − ε/2)K`.
    have hsmall : ∀ t ∈ T, 1 ≤ t ∧ (t : ℝ) ≤ (1 - ε / 2) * K := by
      intro t ht
      refine ⟨(hT1 t ht).1, ?_⟩
      by_contra htbig
      push Not at htbig
      have h1 := hstatic t ht v hvN hvT
      have h2 := hdeg_ge v hv (by omega)
      have h3 := hdeg_le t (hT1 t ht).1 (hT1 t ht).2
      have h4 : X * (1 / (1 - ε)) ≤ (N : ℝ) / v :=
        div_ge_of_le hK (by linarith) (by exact_mod_cast hv) hvK
      have h5 : (N : ℝ) / t < X * (1 / (1 - ε / 2)) :=
        div_lt_of_gt hN0 hK (by linarith) htbig
      have h6 := inv_gap hε0 hε
      have h1' : (deg N v : ℝ) ≤ deg N t := by exact_mod_cast h1
      nlinarith
    have := card_lt_of_le (x := (1 - ε / 2) * K) (K := K) (by nlinarith) (by nlinarith) hsmall
    omega
  · -- Upper inclusion.
    intro w hw
    by_contra hwbig
    push Not at hwbig
    have hwK : K < w := by
      have : (K : ℝ) < w := lt_of_le_of_lt (by nlinarith) hwbig
      exact_mod_cast this
    -- Some `v ≤ K` is not in `T`.
    obtain ⟨v, hvI, hvT⟩ : ∃ v ∈ Icc 1 K, v ∉ T := by
      by_contra hall
      push Not at hall
      have hsub : insert w (Icc 1 K) ⊆ T := insert_subset hw hall
      have := card_le_card hsub
      rw [card_insert_of_notMem (by simp; omega), Nat.card_Icc] at this
      omega
    obtain ⟨hv1, hvK⟩ := mem_Icc.mp hvI
    have h1 := hstatic w hw v (mem_Icc.mpr ⟨hv1, by omega⟩) hvT
    have h2 := hdeg_ge v hv1 (by omega)
    have h3 := hdeg_le w (hT1 w hw).1 (hT1 w hw).2
    have h4 : X * (1 / 1) ≤ (N : ℝ) / v :=
      div_ge_of_le hK one_pos (by exact_mod_cast hv1) (by simpa using (show (v : ℝ) ≤ K by
        exact_mod_cast hvK))
    have h5 : (N : ℝ) / w < X * (1 / (1 + ε)) := div_lt_of_gt hN0 hK (by linarith) hwbig
    have h6 := inv_one_add_le hε0.le (by linarith)
    have h1' : (deg N v : ℝ) ≤ deg N w := by exact_mod_cast h1
    nlinarith

/-! ### The adaptive attack -/

/-- `T_j = {u₀, …, u_{j−1}}`. -/
def removedSet (u : ℕ → ℕ) (j : ℕ) : Finset ℕ := (range j).image u

/-- `u₀, …, u_{K−1}` is an adaptive top-`K` sequence of `G_N`: each `u_j` is a vertex of
`G_N − T_j` of maximal degree there. -/
def IsAdaptive (N K : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ j < K, u j ∈ Icc 1 N ∧ u j ∉ removedSet u j ∧
    ∀ v ∈ Icc 1 N, v ∉ removedSet u j →
      degT N (removedSet u j) v ≤ degT N (removedSet u j) (u j)

theorem removedSet_succ (u : ℕ → ℕ) (j : ℕ) :
    removedSet u (j + 1) = insert (u j) (removedSet u j) := by
  simp [removedSet, range_add_one, image_insert]

theorem removedSet_mono (u : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    removedSet u i ⊆ removedSet u j :=
  image_subset_image (range_mono hij)

theorem card_removedSet {N K : ℕ} {u : ℕ → ℕ} (hu : IsAdaptive N K u) :
    ∀ j ≤ K, (removedSet u j).card = j
  | 0, _ => by simp [removedSet]
  | j + 1, hj => by
    rw [removedSet_succ, card_insert_of_notMem (hu j (by omega)).2.1,
      card_removedSet hu j (by omega)]

/-- **Lemma 6.2, adaptive attack.** -/
theorem sandwich_adaptive {N K : ℕ} {ε τ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hK : 1 ≤ K)
    (hKN : K < N) (hτ : ∀ n, 1 ≤ n → n ≤ N → (n.divisors.card : ℝ) ≤ τ)
    (hgap : τ + 5 ≤ (N : ℝ) / K * (ε / 2)) {u : ℕ → ℕ} (hu : IsAdaptive N K u) :
    (∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ (1 - ε) * K → v ∈ removedSet u K) ∧
      (∀ t ∈ removedSet u K, (t : ℝ) ≤ (1 + ε) * K) := by
  have hN0 : 0 < N := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hXpos : 0 < (N : ℝ) / K := div_pos (by exact_mod_cast hN0) hKR
  have hτ1 : 1 ≤ τ := by simpa using hτ 1 le_rfl (by omega)
  set X := (N : ℝ) / K with hXdef
  have hX24 : 24 ≤ X := by nlinarith
  have hNK : (N : ℝ) = X * K := by rw [hXdef]; field_simp
  have hdeg_le : ∀ w, 1 ≤ w → w ≤ N → (deg N w : ℝ) ≤ τ + (N : ℝ) / w := fun w hw hwN =>
    (deg_le N hw).trans (by linarith [hτ w hw hwN])
  -- `A = ⌊(1+ε)K⌋`: the removed vertices will all be `≤ A`.
  set A := ⌊(1 + ε) * K⌋₊ with hAdef
  have hAle : (A : ℝ) ≤ (1 + ε) * K := Nat.floor_le (by positivity)
  have hA_N : A ≤ N := by
    have : (A : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hKA : K ≤ A := Nat.le_floor (by nlinarith)
  have hNA : (0 : ℝ) ≤ (N : ℝ) - A := by
    have : (A : ℝ) ≤ N := by exact_mod_cast hA_N
    linarith
  -- For `1 ≤ v ≤ K` with `T_j ⊆ [1, A]`: `deg_{T_j}(v) ≥ (N − A)/v − 1`.
  have hlow : ∀ j v, 1 ≤ v → v ≤ K → (∀ t ∈ removedSet u j, t ≤ A) →
      ((N : ℝ) - A) / v - 1 ≤ degT N (removedSet u j) v := by
    intro j v hv hvK hT
    have h := degT_ge (T := removedSet u j) hv (hvK.trans hKA) hA_N hT
    rw [sub_div]
    linarith
  -- Upper inclusion, by induction on `j`: `T_j ⊆ [1, (1+ε)K]`.
  have hup : ∀ j ≤ K, ∀ t ∈ removedSet u j, (t : ℝ) ≤ (1 + ε) * K := by
    intro j
    induction j with
    | zero => intro _ t ht; simp [removedSet] at ht
    | succ j ih =>
      intro hj t ht
      rw [removedSet_succ, mem_insert] at ht
      rcases ht with rfl | ht
      · by_contra hbig
        push Not at hbig
        obtain ⟨huN, -, humax⟩ := hu j (by omega)
        obtain ⟨v, hvI, hvT⟩ : ∃ v ∈ Icc 1 K, v ∉ removedSet u j := by
          by_contra hall
          push Not at hall
          have := card_le_card (show Icc 1 K ⊆ removedSet u j from hall)
          rw [Nat.card_Icc, card_removedSet hu j (by omega)] at this
          omega
        obtain ⟨hv1, hvK⟩ := mem_Icc.mp hvI
        have hTj : ∀ t ∈ removedSet u j, t ≤ A := fun t ht => Nat.le_floor (ih (by omega) t ht)
        have h1 : (degT N (removedSet u j) v : ℝ) ≤ degT N (removedSet u j) (u j) := by
          exact_mod_cast humax v (mem_Icc.mpr ⟨hv1, by omega⟩) hvT
        have h2 := hlow j v hv1 hvK hTj
        -- `(N − A)/v ≥ (N − A)/K ≥ X − (1+ε)`.
        have h3 : ((N : ℝ) - A) / K ≤ ((N : ℝ) - A) / v :=
          div_le_div_of_nonneg_left hNA (by exact_mod_cast hv1) (by exact_mod_cast hvK)
        have h4 : X - (1 + ε) ≤ ((N : ℝ) - A) / K := by
          rw [le_div_iff₀ hKR, hNK]
          nlinarith
        have h5 : (degT N (removedSet u j) (u j) : ℝ) ≤ deg N (u j) := by
          exact_mod_cast degT_le_deg N (removedSet u j) (u j)
        have h6 := hdeg_le (u j) (mem_Icc.mp huN).1 (mem_Icc.mp huN).2
        have h7 : (N : ℝ) / (u j) < X * (1 / (1 + ε)) := div_lt_of_gt hN0 hK (by linarith) hbig
        have h8 : X * (1 / (1 + ε)) ≤ X * (1 - ε / 2) :=
          mul_le_mul_of_nonneg_left (inv_one_add_le hε0.le (by linarith)) hXpos.le
        nlinarith
      · exact ih (by omega) t ht
  refine ⟨?_, hup K le_rfl⟩
  -- Lower inclusion.
  intro v hv hvK
  by_contra hvT
  have hvKn : v ≤ K := by
    have : (v : ℝ) ≤ K := hvK.trans (by nlinarith)
    exact_mod_cast this
  have hsmall : ∀ t ∈ removedSet u K, 1 ≤ t ∧ (t : ℝ) ≤ (1 - ε / 2) * K := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
    have hjK := mem_range.mp hj
    obtain ⟨huN, -, humax⟩ := hu j hjK
    refine ⟨(mem_Icc.mp huN).1, ?_⟩
    by_contra hbig
    push Not at hbig
    have hvTj : v ∉ removedSet u j := fun h => hvT (removedSet_mono u hjK.le h)
    have hTj : ∀ t ∈ removedSet u j, t ≤ A := fun t ht => Nat.le_floor (hup j hjK.le t ht)
    have h1 : (degT N (removedSet u j) v : ℝ) ≤ degT N (removedSet u j) (u j) := by
      exact_mod_cast humax v (mem_Icc.mpr ⟨hv, by omega⟩) hvTj
    have h2 := hlow j v hv hvKn hTj
    -- `(N − A)/v ≥ (N − 2K)/v ≥ (X − 2)/(1 − ε)`.
    have hN2K : (0 : ℝ) ≤ (N : ℝ) - 2 * K := by nlinarith
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have h3 : ((N : ℝ) - 2 * K) / v ≤ ((N : ℝ) - A) / v :=
      div_le_div_of_nonneg_right (by nlinarith) hvR.le
    have h4 : ((N : ℝ) - 2 * K) / ((1 - ε) * K) ≤ ((N : ℝ) - 2 * K) / v :=
      div_le_div_of_nonneg_left hN2K hvR hvK
    have h5 : ((N : ℝ) - 2 * K) / ((1 - ε) * K) = (X - 2) * (1 / (1 - ε)) := by
      rw [hNK]
      field_simp
    have h6 : (degT N (removedSet u j) (u j) : ℝ) ≤ deg N (u j) := by
      exact_mod_cast degT_le_deg N (removedSet u j) (u j)
    have h7 := hdeg_le (u j) (mem_Icc.mp huN).1 (mem_Icc.mp huN).2
    have h8 : (N : ℝ) / (u j) < X * (1 / (1 - ε / 2)) := div_lt_of_gt hN0 hK (by linarith) hbig
    have h9 := mul_le_mul_of_nonneg_left (inv_gap hε0 hε) hXpos.le
    have h10 : 1 / (1 - ε) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  have := card_lt_of_le (x := (1 - ε / 2) * K) (K := K) (by nlinarith) (by nlinarith) hsmall
  rw [card_removedSet hu K le_rfl] at this
  omega

end HubRemoval
