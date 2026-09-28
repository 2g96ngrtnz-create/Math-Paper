import HubRemoval.Core
import HubRemoval.FibreCount

/-!
# The arithmetic core with the paper's parameters (paper, Lemma 4.5(a)–(c))

Let `η ∈ (0,1)`, `s₀ ≥ 1` and `δ ∈ (0, η/8]`. Put
`M = N^{1−2δ}`, `Y = M/(2(K+1))`, `z = N^{δ/s₀}`, and assume

* **(H1)** `K ≤ N^{1−η}`,
* **(H2)** `N^{η/4} ≥ 4`,
* **(H3)** `z ≥ 2`.

`𝒰` is the set of integers `m` with `N^{1−δ} < m ≤ N`, `P⁺(m) ≤ Y` and `ω_z(m) ≥ s₀`.

**Lemma 4.5.**
* (a) `M ≥ 4(K+1)`.
* (b) `𝒰 ⊆ F₁`, and every `m ∈ 𝒰` has `m > M`.
* (c) `s(m) ≥ s₀ + 1` for every `m ∈ 𝒰`.

Part (c) applies `core_divisors` with `E₀ = N^{2δ}` and `E₁ = N^{1−δ}/(K+1)`. This file checks
each inequality that `core_divisors` needs. Part (d) needs Mertens' theorem and is not formalised
here.
-/

namespace HubRemoval

/-- The hypotheses of Lemma 4.5. -/
structure CoreHyp (N K s₀ : ℕ) (η δ : ℝ) : Prop where
  η_pos : 0 < η
  η_lt_one : η < 1
  s₀_pos : 1 ≤ s₀
  δ_pos : 0 < δ
  δ_le : δ ≤ η / 8
  H1 : (K : ℝ) ≤ (N : ℝ) ^ (1 - η)
  H2 : 4 ≤ (N : ℝ) ^ (η / 4)
  H3 : 2 ≤ (N : ℝ) ^ (δ / s₀)

/-- `m ∈ 𝒰`: `N^{1−δ} < m ≤ N`, `P⁺(m) ≤ Y` (as `2(K+1)p ≤ M` for `p ∣ m`), and `ω_z(m) ≥ s₀`. -/
def InU (N K s₀ : ℕ) (δ : ℝ) (m : ℕ) : Prop :=
  (N : ℝ) ^ (1 - δ) < m ∧ m ≤ N ∧
    (∀ p, p.Prime → p ∣ m → 2 * ((K : ℝ) + 1) * p ≤ (N : ℝ) ^ (1 - 2 * δ)) ∧
    s₀ ≤ omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m

variable {N K s₀ : ℕ} {η δ : ℝ}

/-- (H2) forces `N > 1`. -/
theorem CoreHyp.one_lt_N (h : CoreHyp N K s₀ η δ) : (1 : ℝ) < N := by
  by_contra hN
  push Not at hN
  have := Real.rpow_le_one (Nat.cast_nonneg N) hN (by linarith [h.η_pos] : 0 ≤ η / 4)
  linarith [h.H2]

theorem CoreHyp.N_pos (h : CoreHyp N K s₀ η δ) : (0 : ℝ) < N := by linarith [h.one_lt_N]

theorem CoreHyp.rpow_le (h : CoreHyp N K s₀ η δ) {a b : ℝ} (hab : a ≤ b) :
    (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le h.one_lt_N.le hab

theorem CoreHyp.rpow_add (h : CoreHyp N K s₀ η δ) (a b : ℝ) :
    (N : ℝ) ^ (a + b) = (N : ℝ) ^ a * (N : ℝ) ^ b :=
  Real.rpow_add h.N_pos a b

/-- `K + 1 ≤ 2N^{1−η}`, by (H1) and `N^{1−η} ≥ 1`. -/
theorem CoreHyp.K1_le (h : CoreHyp N K s₀ η δ) : (K : ℝ) + 1 ≤ 2 * (N : ℝ) ^ (1 - η) := by
  have := Real.one_le_rpow h.one_lt_N.le (by linarith [h.η_lt_one] : 0 ≤ 1 - η)
  linarith [h.H1]

/-- `(N^a)^n = N^{a n}`. -/
theorem CoreHyp.rpow_pow (h : CoreHyp N K s₀ η δ) (a : ℝ) (n : ℕ) :
    ((N : ℝ) ^ a) ^ n = (N : ℝ) ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.N_pos.le]

/-- **Lemma 4.5(a).** `M ≥ 4(K+1)`. In fact `M ≥ 32(K+1)`. -/
theorem core_a (h : CoreHyp N K s₀ η δ) : 4 * ((K : ℝ) + 1) ≤ (N : ℝ) ^ (1 - 2 * δ) := by
  have hsplit : (N : ℝ) ^ (1 - 2 * δ) = (N : ℝ) ^ (1 - η) * (N : ℝ) ^ (η - 2 * δ) := by
    rw [← h.rpow_add]
    congr 1
    ring
  have h3 : ((N : ℝ) ^ (η / 4)) ^ 3 ≤ (N : ℝ) ^ (η - 2 * δ) := by
    rw [h.rpow_pow]
    apply h.rpow_le
    push_cast
    linarith [h.δ_le]
  have h64 : (64 : ℝ) ≤ ((N : ℝ) ^ (η / 4)) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) h.H2 3
    norm_num at this
    exact this
  have hA : 0 ≤ (N : ℝ) ^ (1 - η) := by positivity
  rw [hsplit]
  nlinarith [h.K1_le]

/-- A number in `(K, N]` all of whose prime factors satisfy `2(K+1)p ≤ N` lies in `F₁`. -/
theorem mem_smoothFibre_of_primes {m : ℕ} (hKm : K < m) (hmN : m ≤ N)
    (hp : ∀ p, p.Prime → p ∣ m → 2 * ((K : ℝ) + 1) * p ≤ N) : m ∈ smoothFibre N K := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hKm, hmN⟩, ?_⟩
  refine Nat.mem_smoothNumbers'.mpr fun p hpp hpm => ?_
  have h1 := hp p hpp hpm
  have h2 : (K + 1) * p ≤ N := by
    have : ((K : ℝ) + 1) * p ≤ 2 * ((K : ℝ) + 1) * p := by
      have : (0 : ℝ) ≤ ((K : ℝ) + 1) * p := by positivity
      linarith
    exact_mod_cast this.trans h1
  have h3 : p ≤ N / (K + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [h2])
  omega

/-- **Lemma 4.5(b).** `𝒰 ⊆ F₁`, and every `m ∈ 𝒰` has `m > M`. -/
theorem core_b (h : CoreHyp N K s₀ η δ) {m : ℕ} (hm : InU N K s₀ δ m) :
    m ∈ smoothFibre N K ∧ (N : ℝ) ^ (1 - 2 * δ) < m := by
  obtain ⟨hm1, hmN, hmY, -⟩ := hm
  have hδη : δ ≤ η := by linarith [h.δ_le, h.η_pos]
  have hMm : (N : ℝ) ^ (1 - 2 * δ) < m :=
    lt_of_le_of_lt (h.rpow_le (by linarith [h.δ_pos])) hm1
  have hKm : K < m := by
    have : (K : ℝ) < m :=
      calc (K : ℝ) ≤ (N : ℝ) ^ (1 - η) := h.H1
        _ ≤ (N : ℝ) ^ (1 - δ) := h.rpow_le (by linarith)
        _ < m := hm1
    exact_mod_cast this
  have hMN : (N : ℝ) ^ (1 - 2 * δ) ≤ N :=
    calc (N : ℝ) ^ (1 - 2 * δ) ≤ (N : ℝ) ^ (1 : ℝ) := h.rpow_le (by linarith [h.δ_pos])
      _ = N := Real.rpow_one _
  exact ⟨mem_smoothFibre_of_primes hKm hmN fun p hp hpm => (hmY p hp hpm).trans hMN, hMm⟩

/-- **Lemma 4.5(c).** Every `m ∈ 𝒰` has `s(m) = |D(m)| ≥ s₀ + 1`, where
`D(m) = {d ∈ S_M : d ∣ m}` and `M = N^{1−2δ}`. -/
theorem core_c (h : CoreHyp N K s₀ η δ) {m : ℕ} (hm : InU N K s₀ δ m) :
    s₀ + 1 ≤ (lowerDivisors ((N : ℝ) ^ (1 - 2 * δ)) K m).card := by
  obtain ⟨hm1, hmN, hmY, hω⟩ := hm
  have hx0 := h.N_pos
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hs₀ : (1 : ℝ) ≤ s₀ := by exact_mod_cast h.s₀_pos
  have hzδ : δ / s₀ ≤ δ := div_le_self h.δ_pos.le hs₀
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := lt_trans (by positivity) hm1
    exact_mod_cast this
  refine core_divisors (z := (N : ℝ) ^ (δ / s₀)) (E₀ := (N : ℝ) ^ (2 * δ))
    (E₁ := (N : ℝ) ^ (1 - δ) / ((K : ℝ) + 1)) hm0 hmY hω ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `z ≥ 1`
    linarith [h.H3]
  · -- `E₀ > 1`
    exact Real.one_lt_rpow h.one_lt_N (by linarith [h.δ_pos])
  · -- `m ≤ M E₀ = N`
    rw [← h.rpow_add, show 1 - 2 * δ + 2 * δ = (1 : ℝ) by ring, Real.rpow_one]
    exact_mod_cast hmN
  · -- `(K+1) E₁ = N^{1−δ} < m`
    rw [mul_div_cancel₀ _ hK1.ne']
    exact hm1
  · -- `z M ≤ 2(K+1) E₁ = 2N^{1−δ}`
    rw [show 2 * ((K : ℝ) + 1) * ((N : ℝ) ^ (1 - δ) / ((K : ℝ) + 1)) = 2 * (N : ℝ) ^ (1 - δ) by
      field_simp, ← h.rpow_add]
    have h1 : (N : ℝ) ^ (δ / s₀ + (1 - 2 * δ)) ≤ (N : ℝ) ^ (1 - δ) := h.rpow_le (by linarith)
    have h2 : 0 ≤ (N : ℝ) ^ (1 - δ) := by positivity
    linarith
  · -- `z E₀² ≤ E₁`
    rw [le_div_iff₀ hK1]
    have hE : (N : ℝ) ^ (δ / s₀) * ((N : ℝ) ^ (2 * δ)) ^ 2 ≤ (N : ℝ) ^ (5 * δ) := by
      rw [h.rpow_pow, ← h.rpow_add]
      apply h.rpow_le
      push_cast
      linarith
    have hsplit : (N : ℝ) ^ (1 - δ) = (N : ℝ) ^ (1 - η + 5 * δ) * (N : ℝ) ^ (η - 6 * δ) := by
      rw [← h.rpow_add]
      congr 1
      ring
    have h5 : (N : ℝ) ^ (5 * δ) * (N : ℝ) ^ (1 - η) = (N : ℝ) ^ (1 - η + 5 * δ) := by
      rw [← h.rpow_add]
      congr 1
      ring
    have hbig : 4 ≤ (N : ℝ) ^ (η - 6 * δ) := h.H2.trans (h.rpow_le (by linarith [h.δ_le]))
    have hR : 0 ≤ (N : ℝ) ^ (1 - η + 5 * δ) := by positivity
    calc (N : ℝ) ^ (δ / s₀) * ((N : ℝ) ^ (2 * δ)) ^ 2 * ((K : ℝ) + 1)
        ≤ (N : ℝ) ^ (5 * δ) * ((K : ℝ) + 1) := mul_le_mul_of_nonneg_right hE hK1.le
      _ ≤ (N : ℝ) ^ (5 * δ) * (2 * (N : ℝ) ^ (1 - η)) :=
          mul_le_mul_of_nonneg_left h.K1_le (by positivity)
      _ = 2 * (N : ℝ) ^ (1 - η + 5 * δ) := by rw [← h5]; ring
      _ ≤ (N : ℝ) ^ (1 - η + 5 * δ) * (N : ℝ) ^ (η - 6 * δ) := by nlinarith
      _ = (N : ℝ) ^ (1 - δ) := hsplit.symm
  · -- `z^{s₀} E₀ = N^{3δ} ≤ N^{1−δ} < m`
    have hzs : ((N : ℝ) ^ (δ / s₀)) ^ s₀ = (N : ℝ) ^ δ := by
      rw [h.rpow_pow]
      congr 1
      field_simp
    rw [hzs, ← h.rpow_add]
    have : (N : ℝ) ^ (δ + 2 * δ) ≤ (N : ℝ) ^ (1 - δ) :=
      h.rpow_le (by linarith [h.δ_le, h.η_lt_one])
    linarith

end HubRemoval
