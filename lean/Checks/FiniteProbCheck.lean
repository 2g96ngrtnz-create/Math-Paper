import HubRemoval.FiniteProb
open HubRemoval Finset

/-! ### Finite product probability: axioms -/

#print axioms sum_wt
#print axioms expectP_const
#print axioms expectP_sum
#print axioms expectP_mono
#print axioms prob_eq
#print axioms prob_not
#print axioms prob_and_ge
#print axioms prob_or_le
#print axioms prob_exists_le
#print axioms prob_cylinder
#print axioms wt_split
#print axioms expectP_mul_of_disjoint
#print axioms expectP_prod_of_pairwiseDisjoint

/-! ### Concrete checks on `Fin 3 → Bool` -/

/-- One weight, by hand: `wt ρ (true, false, true) = ρ(1−ρ)ρ`. -/
example (ρ : ℝ) : wt ρ ![true, false, true] = ρ * (1 - ρ) * ρ := by
  simp [wt, pb, Fin.prod_univ_three]

/-- A cylinder: `P(ω₀ = true, ω₁ = false) = ρ(1 − ρ)`. -/
example (ρ : ℝ) :
    prob ρ (fun ω : Fin 3 → Bool => ∀ i ∈ ({0, 1} : Finset (Fin 3)), ω i = ![true, false, true] i) =
      ρ * (1 - ρ) := by
  rw [prob_cylinder]
  simp [pb]

/-- The indicator of `ω i = true`. -/
noncomputable def ind (i : Fin 3) : (Fin 3 → Bool) → ℝ := fun ω => if ω i = true then 1 else 0

theorem ind_dependsOn (i : Fin 3) : DependsOnCoords (ind i) {i} := fun ω ω' h => by
  simp [ind, h i (mem_singleton_self i)]

theorem expectP_ind (ρ : ℝ) (i : Fin 3) : expectP ρ (ind i) = ρ := by
  have h := prob_cylinder ρ {i} (fun _ => true)
  rw [prob_eq] at h
  simp only [mem_singleton, forall_eq, prod_singleton, pb, ite_true] at h
  unfold expectP ind
  convert h using 2

/-- Independence of disjoint coordinates: `E[1{ω₀} · 1{ω₁}] = ρ²`. -/
example (ρ : ℝ) : expectP ρ (fun ω => ind 0 ω * ind 1 ω) = ρ ^ 2 := by
  rw [expectP_mul_of_disjoint ρ (by decide) (ind_dependsOn 0) (ind_dependsOn 1), expectP_ind,
    expectP_ind]
  ring

/-- **Disjointness is needed.** With the same coordinate twice, `E[f · f] = ρ`, which is not
`E[f]² = ρ²` for `ρ = 1/2`. -/
example : expectP (1 / 2) (fun ω => ind 0 ω * ind 0 ω) ≠
    expectP (1 / 2) (ind 0) * expectP (1 / 2) (ind 0) := by
  have hsq : (fun ω => ind 0 ω * ind 0 ω) = ind 0 := by
    funext ω
    unfold ind
    split_ifs <;> norm_num
  rw [hsq, expectP_ind]
  norm_num

/-- Three disjoint blocks: `E[∏ᵢ 1{ωᵢ}] = ρ³`. -/
example (ρ : ℝ) : expectP ρ (fun ω => ∏ i ∈ (univ : Finset (Fin 3)), ind i ω) = ρ ^ 3 := by
  rw [expectP_prod_of_pairwiseDisjoint ρ univ (fun i => {i}) ind
    (fun a _ b _ hab => by simpa using hab) (fun i _ => ind_dependsOn i)]
  simp [expectP_ind]
