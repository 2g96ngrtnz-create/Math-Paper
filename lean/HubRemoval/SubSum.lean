import Mathlib

/-!
# The sub-sum lemma (paper, Lemma A.1)

**Lemma A.1 (finite form).** Let `x₁, …, xₙ ≥ 0` with `∑ xᵢ = 1`, let `0 < θ ≤ 1/3`, and suppose
every `xᵢ < 1 − θ`. Then some sub-sum lies in `[θ, 1/2]`.

The paper states this for a non-increasing sequence with `x₁ < 1 − θ`, which says exactly that
every term is `< 1 − θ`. Monotonicity is not needed here, and neither is `xᵢ ≥ 0`: if every term
is `< θ`, the first partial sum that reaches `θ` is `< 2θ ≤ 1 − θ`, whatever the signs. The
theorem below is therefore stated without the nonnegativity hypothesis, which makes it stronger.

The bound `1/3` is sharp. For `1/3 < θ`, the parts `(1/3, 1/3, 1/3)` have no sub-sum in
`[θ, 1/2]`.
-/

namespace HubRemoval

open Finset

/-- A sub-sum in `[θ, 1 − θ]` yields a sub-sum in `[θ, 1/2]`: take it or its complement. -/
theorem subsum_of_mem_Icc {n : ℕ} (x : Fin n → ℝ) (hsum : ∑ i, x i = 1) {θ : ℝ}
    (I : Finset (Fin n)) (h1 : θ ≤ ∑ i ∈ I, x i) (h2 : ∑ i ∈ I, x i ≤ 1 - θ) :
    ∃ J : Finset (Fin n), θ ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 1 / 2 := by
  have hc := Finset.sum_add_sum_compl I x
  rw [hsum] at hc
  by_cases h : ∑ i ∈ I, x i ≤ 1 / 2
  · exact ⟨I, h1, h⟩
  · push Not at h
    exact ⟨Iᶜ, by linarith, by linarith⟩

/-- **Lemma A.1 (finite form).** No nonnegativity hypothesis is needed. -/
theorem subsum {n : ℕ} (x : Fin n → ℝ) (hsum : ∑ i, x i = 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 3) (hmax : ∀ i, x i < 1 - θ) :
    ∃ I : Finset (Fin n), θ ≤ ∑ i ∈ I, x i ∧ ∑ i ∈ I, x i ≤ 1 / 2 := by
  classical
  by_cases hbig : ∃ i, θ ≤ x i
  · obtain ⟨i, hi⟩ := hbig
    exact subsum_of_mem_Icc x hsum {i} (by simpa using hi) (by simpa using (hmax i).le)
  push Not at hbig
  -- Partial sums `f k = x₀ + ⋯ + x_{k-1}`.
  let f : ℕ → ℝ := fun k => ∑ i ∈ univ.filter (fun i : Fin n => i.val < k), x i
  have hf_all : ∀ k, n ≤ k → f k = 1 := by
    intro k hk
    simp only [f]
    rw [Finset.filter_true_of_mem (fun i _ => lt_of_lt_of_le i.isLt hk)]
    exact hsum
  have hf0 : f 0 = 0 := by simp [f]
  have hex : ∃ k, θ ≤ f k := ⟨n, by rw [hf_all n le_rfl]; linarith⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, θ ≤ f k ∧ ∀ m < k, f m < θ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      have := Nat.find_min hex hm
      push Not at this
      exact this⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hf0] at hk
    linarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hprev : f j < θ := hmin j (Nat.lt_succ_self j)
  have hjn : j < n := by
    by_contra hjn
    push Not at hjn
    have := hf_all j hjn
    linarith
  have hstep : f (j + 1) = f j + x ⟨j, hjn⟩ := by
    simp only [f]
    have hset : (univ.filter fun i : Fin n => i.val < j + 1) =
        insert ⟨j, hjn⟩ (univ.filter fun i : Fin n => i.val < j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_insert (by simp), add_comm]
  have hup : f (j + 1) ≤ 1 - θ := by
    rw [hstep]
    have := hbig ⟨j, hjn⟩
    linarith
  exact subsum_of_mem_Icc x hsum _ hk hup

/-- **Lemma A.1 is sharp.** For `θ > 1/3`, the parts `(1/3, 1/3, 1/3)` have no sub-sum in
`[θ, 1/2]`. -/
theorem subsum_sharp {θ : ℝ} (hθ : 1 / 3 < θ) (I : Finset (Fin 3)) :
    ¬ (θ ≤ ∑ _i ∈ I, (1 / 3 : ℝ) ∧ ∑ _i ∈ I, (1 / 3 : ℝ) ≤ 1 / 2) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : I.card ≤ 3 := by simpa using Finset.card_le_univ I
  rintro ⟨h1, h2⟩
  interval_cases hI : I.card <;> norm_num at h1 h2 <;> linarith

end HubRemoval
