import HubRemoval.CoreParams
open HubRemoval

/-! ### Lemma 4.5(a)–(c): axioms -/

#print axioms CoreHyp.one_lt_N
#print axioms CoreHyp.K1_le
#print axioms core_a
#print axioms mem_smoothFibre_of_primes
#print axioms core_b
#print axioms core_c

/-! ### (H1)–(H3) hold together (non-vacuity)

`η = 1/2`, `δ = 1/16 = η/8`, `s₀ = 1`, `N = 2¹⁶ = 65536` and `K = 10`.
* (H1) `K = 10 ≤ N^{1/2} = 256`.
* (H2) `N^{η/4} = N^{1/8} = 4`.
* (H3) `z = N^{δ/s₀} = N^{1/16} = 2`.

Then `M = N^{7/8} = 2¹⁴`, and `m = 2¹⁶` lies in `𝒰`: `N^{15/16} = 2¹⁵ < m ≤ N`, `P⁺(m) = 2` with
`2 · 11 · 2 = 44 ≤ M`, and `ω₂(m) = 1 ≥ s₀`. -/

theorem N_rpow (a : ℝ) : (65536 : ℝ) ^ a = (2 : ℝ) ^ (16 * a) := by
  rw [Real.rpow_mul (by norm_num), show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

theorem two_rpow_nat (n : ℕ) : (2 : ℝ) ^ (n : ℝ) = 2 ^ n := Real.rpow_natCast 2 n

theorem hyp : CoreHyp 65536 10 1 (1 / 2) (1 / 16) where
  η_pos := by norm_num
  η_lt_one := by norm_num
  s₀_pos := le_rfl
  δ_pos := by norm_num
  δ_le := by norm_num
  H1 := by
    push_cast
    rw [N_rpow, show 16 * (1 - 1 / 2 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  H2 := by
    push_cast
    rw [N_rpow, show 16 * (1 / 2 / 4 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  H3 := by
    push_cast
    rw [N_rpow, show 16 * (1 / 16 / 1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num

theorem z_eq : ⌊((65536 : ℕ) : ℝ) ^ ((1 / 16 : ℝ) / ((1 : ℕ) : ℝ))⌋₊ = 2 := by
  push_cast
  rw [N_rpow, show 16 * (1 / 16 / 1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, two_rpow_nat]
  norm_num

#guard omegaZ 2 65536 = 1

theorem inU : InU 65536 10 1 (1 / 16) 65536 := by
  refine ⟨?_, le_rfl, fun p hp hpd => ?_, ?_⟩
  · push_cast
    rw [N_rpow, show 16 * (1 - 1 / 16 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 16 by norm_num; exact hpd)
    rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2]
    push_cast
    rw [N_rpow, show 16 * (1 - 2 * (1 / 16) : ℝ) = ((14 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  · rw [z_eq]
    decide

/-- (a): `M = 2¹⁴ ≥ 4 · 11`. -/
example : 4 * ((10 : ℕ) + 1 : ℝ) ≤ ((65536 : ℕ) : ℝ) ^ (1 - 2 * (1 / 16) : ℝ) := core_a hyp

/-- (b): `2¹⁶ ∈ F₁` and `2¹⁶ > M`. -/
example : 65536 ∈ smoothFibre 65536 10 ∧ ((65536 : ℕ) : ℝ) ^ (1 - 2 * (1 / 16) : ℝ) < 65536 :=
  core_b hyp inU

/-- (c): `s(2¹⁶) ≥ 2`. (By hand, `D(2¹⁶) = {2⁴, …, 2¹⁴}` has 11 elements.) -/
example : 2 ≤ (lowerDivisors (((65536 : ℕ) : ℝ) ^ (1 - 2 * (1 / 16) : ℝ)) 10 65536).card :=
  core_c hyp inU
