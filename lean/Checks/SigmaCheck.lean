import HubRemoval.Sigma
open HubRemoval

/-! ### Corollary 4.3: axioms -/

#print axioms sigma_mutual
#print axioms goodSet_mem_smoothFibre
#print axioms sigma_subset_smoothFibre

/-! ### The hypotheses can hold together (non-vacuity)

Corollary 4.3 is stated for any relation `D`. Here `D` is the symmetric relation `Adj` of
`G_{N,K}`, which contains both directions of each edge; it is **not** an orientation. It satisfies
`𝓡` whenever `2M ≤ N`, with the witness `y = y' = 2x'`. (`Checks/RobustCheck.lean` has a genuine
orientation on which `𝓡` holds.) -/

theorem robust_adj_of_two_mul {N K : ℕ} {M : ℝ} (hMN : 2 * M ≤ N) :
    RobustEvent (divGraph N K).Adj N K M := by
  intro x x' hKx hxx' hx'M hdvd
  have h2 : 2 * x' ≤ N := by exact_mod_cast (show (2 * x' : ℝ) ≤ N by linarith)
  have hy : x' ∣ 2 * x' := Dvd.intro_left 2 rfl
  have e1 : (divGraph N K).Adj x (2 * x') :=
    ⟨by omega, hKx, by omega, by omega, h2, Or.inl (hdvd.trans hy)⟩
  have e2 : (divGraph N K).Adj (2 * x') x' :=
    ⟨by omega, by omega, h2, by omega, by omega, Or.inr hy⟩
  exact ⟨⟨2 * x', by omega, h2, hy, e1, e2⟩, ⟨2 * x', by omega, h2, hy, e2.symm, e1.symm⟩⟩

/-! `N = 48`, `K = 1`, `M = 24`, so `4(K+1) = 8 ≤ M`, `2M ≤ N` and `Y = 24/4 = 6`. The primes
`3` and `5` are `≤ Y`, so both lie in `S_M`. -/

theorem goodSet_3 : goodSet 24 1 3 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd]
  norm_num

theorem goodSet_5 : goodSet 24 1 5 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpd]
  norm_num

/-- `7` is not in `S_M`, because `2 · 2 · 7 = 28 > 24`. -/
example : ¬ goodSet 24 1 7 := fun h => by
  have := h.2.2 7 (by norm_num) dvd_rfl
  norm_num at this

example : MutuallyReachable (divGraph 48 1).Adj 3 5 :=
  sigma_mutual (by norm_num) (robust_adj_of_two_mul (by norm_num)) goodSet_3 goodSet_5

example : (5 : ℕ) ∈ smoothFibre 48 1 := goodSet_mem_smoothFibre (by norm_num) goodSet_5

/-- The strongly connected set `{3, 6}` (`3 ∣ 6`) meets `S_M` at `3`, so it lies in `F₁`. -/
example : ({3, 6} : Finset ℕ) ⊆ smoothFibre 48 1 := by
  have hadj : (divGraph 48 1).Adj 3 6 := by unfold divGraph; decide
  refine sigma_subset_smoothFibre (M := 24) (by norm_num) (fun _ _ h => h) ?_ ?_
    (by simp) goodSet_3
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [vertices, Finset.mem_Ioc]
    omega
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single hadj
    · exact Relation.ReflTransGen.single hadj.symm
    · exact Relation.ReflTransGen.refl
