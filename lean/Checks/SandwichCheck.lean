import HubRemoval.Sandwich
open HubRemoval Finset

/-! ### Lemma 6.2: axioms -/

#print axioms deg_le
#print axioms card_Ioc_filter_dvd
#print axioms degT_ge
#print axioms inv_one_add_le
#print axioms inv_gap
#print axioms sandwich_static
#print axioms card_removedSet
#print axioms sandwich_adaptive

/-! ### The degree formula `deg(m) = (τ(m) − 1) + (⌊N/m⌋ − 1)`, checked for every `m ≤ 100` -/

#guard deg 100 1 = 99
#guard deg 100 12 = 12      -- 5 proper divisors, 7 proper multiples
#guard (List.range 100).all fun i =>
  deg 100 (i + 1) = ((i + 1).divisors.card - 1) + (100 / (i + 1) - 1)

/-! Removing `T = {1, 2}` from `G_100` lowers `deg(12)` by 2. -/
#guard degT 100 {1, 2} 12 = 10

/-! ### Non-vacuity: `N = 80`, `K = 1`, `ε = 1/2`, `τ̂ = 12`

`τ(n) ≤ 12` for `n ≤ 80` (the maximum, 12, is attained at 60 and 72), and
`(N/K)(ε/2) = 20 ≥ 12 + 5`. The vertex `1` is adjacent to every other vertex, so it has the
maximum degree `N − 1`. Hence `T = {1}` is a static top-1 set, and `u₀ = 1` is an adaptive
top-1 sequence. -/

theorem tau_le_12 : ∀ n, 1 ≤ n → n ≤ 80 → (n.divisors.card : ℝ) ≤ 12 := by
  have key : ∀ n < 81, n.divisors.card ≤ 12 := by decide
  intro n _ hn
  exact_mod_cast key n (by omega)

/-- Every vertex of `G_N` has degree at most `N − 1`. (For `v = 0`, which is not a vertex, this
fails: every `w` divides `0`.) -/
theorem deg_le_pred {N v : ℕ} (hv : v ∈ Icc 1 N) : deg N v ≤ N - 1 := by
  have hsub : nbrs N ∅ v ⊆ (Icc 1 N).erase v := fun w hw => by
    simp only [nbrs, sdiff_empty, mem_filter] at hw
    exact mem_erase.mpr ⟨hw.2.1, hw.1⟩
  have := card_le_card hsub
  simp only [deg, degT]
  rw [card_erase_of_mem hv, Nat.card_Icc] at this
  omega

/-- The vertex `1` has degree `N − 1`. -/
theorem deg_one (N : ℕ) : deg N 1 = N - 1 := by
  have hset : nbrs N ∅ 1 = (Icc 1 N).erase 1 := by
    ext w
    simp only [nbrs, sdiff_empty, mem_filter, mem_erase, one_dvd, or_true, and_true]
    exact and_comm
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rfl
  · simp only [deg, degT]
    rw [hset, card_erase_of_mem (mem_Icc.mpr ⟨le_rfl, hN⟩), Nat.card_Icc]
    omega

example : (∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ (1 - 1 / 2) * (1 : ℕ) → v ∈ ({1} : Finset ℕ)) ∧
    (∀ t ∈ ({1} : Finset ℕ), (t : ℝ) ≤ (1 + 1 / 2) * (1 : ℕ)) :=
  sandwich_static (N := 80) (K := 1) (ε := 1 / 2) (τ := 12) (by norm_num) le_rfl le_rfl
    (by norm_num) tau_le_12 (by norm_num) (by decide) rfl
    fun t ht v hv _ => by
      rw [mem_singleton.mp ht, deg_one]
      exact deg_le_pred hv

/-- The adaptive sequence `u₀ = 1`. -/
theorem adaptive_one : IsAdaptive 80 1 (fun _ => 1) := by
  intro j hj
  obtain rfl : j = 0 := by omega
  refine ⟨by decide, by simp [removedSet], fun v hv _ => ?_⟩
  simp only [removedSet, range_zero, image_empty]
  rw [show degT 80 ∅ 1 = deg 80 1 from rfl, deg_one]
  exact deg_le_pred hv

example : (∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ (1 - 1 / 2) * (1 : ℕ) → v ∈ removedSet (fun _ => 1) 1) ∧
    (∀ t ∈ removedSet (fun _ => 1) 1, (t : ℝ) ≤ (1 + 1 / 2) * (1 : ℕ)) :=
  sandwich_adaptive (N := 80) (K := 1) (ε := 1 / 2) (τ := 12) (by norm_num) le_rfl le_rfl
    (by norm_num) tau_le_12 (by norm_num) adaptive_one
