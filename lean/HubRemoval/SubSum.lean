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

**Lemma A.1 (infinite form).** Let `x₀, x₁, …` be real with `∑ xᵢ = 1` absolutely convergent, let
`0 < θ ≤ 1/3`, and suppose every `xᵢ < 1 − θ`. Then `∑_{i ∈ S} xᵢ ∈ [θ, 1/2]` for some `S ⊆ ℕ`
(`subsum_infinite`).
Choose `n` with `x₀ + ⋯ + x_{n−1} > θ`; then the tail `r = ∑_{i ≥ n} xᵢ` is `< 1 − θ`. The finite
form applied to `(x₀, …, x_{n−1}, r)` gives a set `I`, and `S` is `I` with `r` replaced by all
indices `≥ n`.
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

/-- **Lemma A.1 (infinite form).** For real `xᵢ` with `∑ xᵢ = 1` (unconditionally, which for real
series means absolutely), `0 < θ ≤ 1/3` and every `xᵢ < 1 − θ`, some sub-sum `∑_{i ∈ S} xᵢ`
(`S ⊆ ℕ`, possibly infinite) lies in `[θ, 1/2]`. No sign condition is needed. -/
theorem subsum_infinite {x : ℕ → ℝ} (hsum : HasSum x 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 3) (hmax : ∀ i, x i < 1 - θ) :
    ∃ S : Set ℕ, θ ≤ ∑' i, S.indicator x i ∧ ∑' i, S.indicator x i ≤ 1 / 2 := by
  classical
  have hs := hsum.summable
  -- A prefix with sum `> θ`.
  obtain ⟨n, hn⟩ : ∃ n, θ < ∑ i ∈ range n, x i :=
    ((hsum.tendsto_sum_nat).eventually (lt_mem_nhds (show θ < 1 by linarith))).exists
  set r := ∑' i, x (i + n) with hr
  have hsplit : ∑ i ∈ range n, x i + r = 1 := by
    rw [hr, hs.sum_add_tsum_nat_add n, hsum.tsum_eq]
  -- The finite family `(x₀, …, x_{n−1}, r)`.
  set y : ℕ → ℝ := fun i => if i < n then x i else r with hy
  have hyx : ∀ i, i < n → y i = x i := fun i hi => by simp only [hy, hi, ↓reduceIte]
  have hyr : y n = r := by simp only [hy, lt_irrefl, ↓reduceIte]
  have hysum : ∑ i : Fin (n + 1), y i = 1 := by
    rw [Fin.sum_univ_castSucc, Fin.val_last, hyr]
    have h1 : ∑ i : Fin n, y (Fin.castSucc i : Fin (n + 1)) = ∑ i ∈ range n, x i := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact sum_congr rfl fun i _ => by rw [Fin.val_castSucc, hyx i i.2]
    rw [h1, hsplit]
  have hymax : ∀ i : Fin (n + 1), y i < 1 - θ := fun i => by
    by_cases hi : (i : ℕ) < n
    · rw [hyx i hi]; exact hmax i
    · simp only [hy, hi, ↓reduceIte]; linarith
  obtain ⟨I, h1, h2⟩ := subsum (fun i : Fin (n + 1) => y i) hysum hθ0 hθ hymax
  -- Transport `I` to `ℕ`.
  set J : Finset ℕ := I.image (fun i : Fin (n + 1) => (i : ℕ)) with hJ
  have hJsum : ∑ i ∈ I, y i = ∑ j ∈ J, y j :=
    (sum_image fun a _ b _ h => Fin.ext h).symm
  have hJsub : ∀ j ∈ J, j ≤ n := fun j hj => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hj
    exact Nat.lt_succ_iff.mp i.2
  have hJfilt : J.filter (fun j => ¬ j < n) = if n ∈ J then {n} else ∅ := by
    ext j
    simp only [mem_filter]
    split_ifs with h
    · simp only [mem_singleton]
      constructor
      · rintro ⟨hj, hjn⟩; have := hJsub j hj; omega
      · intro hj; rw [hj]; exact ⟨h, lt_irrefl n⟩
    · simp only [notMem_empty, iff_false, not_and, not_not]
      intro hj
      by_contra hjn
      have := hJsub j hj
      exact h (by rwa [show j = n by omega] at hj)
  have hJy : ∑ j ∈ J, y j = ∑ j ∈ J.filter (· < n), x j + (if n ∈ J then r else 0) := by
    rw [← sum_filter_add_sum_filter_not J (· < n), hJfilt]
    congr 1
    · exact sum_congr rfl fun j hj => hyx j (mem_filter.mp hj).2
    · split_ifs <;> simp [hyr]
  -- The set `S`.
  set S : Set ℕ := {i | i < n ∧ i ∈ J} ∪ {i | n ≤ i ∧ n ∈ J} with hS
  have hSx : ∑' i, S.indicator x i = ∑ j ∈ J.filter (· < n), x j + (if n ∈ J then r else 0) := by
    rw [← (hs.indicator S).sum_add_tsum_nat_add n]
    congr 1
    · rw [← sum_filter_add_sum_filter_not (range n) (· ∈ J)]
      have e1 : ∑ i ∈ (range n).filter (· ∈ J), S.indicator x i =
          ∑ j ∈ J.filter (· < n), x j := by
        have hset : (range n).filter (· ∈ J) = J.filter (· < n) := by
          ext i; simp only [mem_filter, mem_range]; tauto
        rw [hset]
        refine sum_congr rfl fun i hi => ?_
        obtain ⟨hiJ, hin⟩ := mem_filter.mp hi
        exact Set.indicator_of_mem (show i ∈ S from Or.inl ⟨hin, hiJ⟩) x
      have e2 : ∑ i ∈ (range n).filter (· ∉ J), S.indicator x i = 0 := by
        refine sum_eq_zero fun i hi => ?_
        obtain ⟨hin, hiJ⟩ := mem_filter.mp hi
        refine Set.indicator_of_notMem ?_ x
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hiJ h
        · have := mem_range.mp hin; omega
      rw [e1, e2, add_zero]
    · split_ifs with h
      · exact tsum_congr fun i => Set.indicator_of_mem (show i + n ∈ S from Or.inr ⟨by omega, h⟩) x
      · refine (tsum_congr fun i => Set.indicator_of_notMem ?_ x).trans tsum_zero
        rintro (⟨hi, -⟩ | ⟨-, hn⟩)
        · omega
        · exact h hn
  refine ⟨S, ?_, ?_⟩
  · rw [hSx, ← hJy, ← hJsum]; exact h1
  · rw [hSx, ← hJy, ← hJsum]; exact h2

end HubRemoval
