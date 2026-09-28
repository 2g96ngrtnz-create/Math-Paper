import HubRemoval.AttachProb
open HubRemoval Finset

/-! ### Lemma 4.4 in the model: axioms -/

#print axioms edge_of_lowerDivisor
#print axioms card_starEdges
#print axioms prob_all_bit
#print axioms prob_attachEv
#print axioms prob_attachEv_ge

/-! ### Applied: `m = 30` in `𝒟_{1/2}(48, 1)` with `M = 24`

`2` and `3` lie in `D(30)`: they divide `30`, lie in `(1, 24]`, and their prime factors `p` satisfy
`2 · 2 · p ≤ 24`. So `s ≥ 2`, and `P(A₃₀) ≥ 1 − 2 (1/2)^s ≥ 1/2`. (In fact
`D(30) = {2, 3, 5, 6, 10, 15}`, so `s = 6` and `P(A₃₀) = 31/32`.) -/

theorem two_mem : 2 ∈ lowerDivisors 24 1 30 := by
  refine mem_lowerDivisors.mpr ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num,
    fun p hp hpd => ?_⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd]
  norm_num

theorem three_mem : 3 ∈ lowerDivisors 24 1 30 := by
  refine mem_lowerDivisors.mpr ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num,
    fun p hp hpd => ?_⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd]
  norm_num

example : (1 / 2 : ℝ) ≤ prob (1 / 2) (attachEv (N := 48) (K := 1) 24 30) := by
  have hs : 2 ≤ (lowerDivisors 24 1 30).card := by
    have := card_le_card (show ({2, 3} : Finset ℕ) ⊆ lowerDivisors 24 1 30 by
      intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact two_mem
      · exact three_mem)
    simpa using this
  have h := prob_attachEv_ge (N := 48) (K := 1) (ρ := 1 / 2) (by norm_num) (by norm_num)
    (M := 24) (m := 30) (by norm_num) (by norm_num)
  rw [show max (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 by norm_num] at h
  have hpow : (1 / 2 : ℝ) ^ (lowerDivisors 24 1 30).card ≤ (1 / 2) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  linarith

/-! The edge `(2, 30)` of `G_{48,1}` is one of the `s` edges. -/

example : (2, 30) ∈ edges 48 1 := edge_of_lowerDivisor (by norm_num) (by norm_num) two_mem
