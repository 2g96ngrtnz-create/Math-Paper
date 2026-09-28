import HubRemoval.SubSum
open HubRemoval

/-! ### Lemma A.1: axioms -/

#print axioms subsum_of_mem_Icc
#print axioms subsum
#print axioms subsum_sharp

/-! ### Concrete applications (non-vacuity)

Five equal parts `1/5` with `θ = 3/10`: every part is `< 7/10`, so some sub-sum lies in
`[3/10, 1/2]`, for example `1/5 + 1/5 = 2/5`. -/

example : ∃ I : Finset (Fin 5), (3 / 10 : ℝ) ≤ ∑ i ∈ I, (fun _ => (1 / 5 : ℝ)) i ∧
    ∑ i ∈ I, (fun _ => (1 / 5 : ℝ)) i ≤ 1 / 2 :=
  subsum _ (by simp) (by norm_num) (by norm_num) (fun _ => by norm_num)

/-- The parts `(1/2, 1/2, −1/5, 1/5)` sum to `1` and are all `< 7/10`, but one is negative.
The lemma still applies, because nonnegativity is not a hypothesis. -/
example : ∃ I : Finset (Fin 4), (3 / 10 : ℝ) ≤ ∑ i ∈ I, ![1 / 2, 1 / 2, -1 / 5, 1 / 5] i ∧
    ∑ i ∈ I, ![(1 / 2 : ℝ), 1 / 2, -1 / 5, 1 / 5] i ≤ 1 / 2 :=
  subsum _ (by simp [Fin.sum_univ_succ]; norm_num) (by norm_num) (by norm_num)
    (fun i => by fin_cases i <;> simp <;> norm_num)

/-! ### Sharpness at `1/3`

With `θ = 17/50 > 1/3` and parts `(1/3, 1/3, 1/3)`, every part is `1/3 < 1 − θ = 33/50`, yet no
sub-sum lies in `[17/50, 1/2]`. So the hypothesis `θ ≤ 1/3` cannot be dropped. -/

example (I : Finset (Fin 3)) :
    ¬ ((17 / 50 : ℝ) ≤ ∑ _i ∈ I, (1 / 3 : ℝ) ∧ ∑ _i ∈ I, (1 / 3 : ℝ) ≤ 1 / 2) :=
  subsum_sharp (by norm_num) I
