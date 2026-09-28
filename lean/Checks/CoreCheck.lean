import HubRemoval.Core
open HubRemoval

/-! ### Lemma 4.5(c), counting argument: axioms -/

#print axioms exists_dvd_mem_Ico
#print axioms prod_primes_dvd
#print axioms mem_lowerDivisors
#print axioms core_divisors

/-! ### The prime-chain step

`32 = 2⁵` has only the prime factor `2 < 3`, so it has a divisor in `[3, 9)`: `4` or `8`. -/

example : ∃ e : ℕ, e ∣ 32 ∧ (3 : ℝ) ≤ e ∧ (e : ℝ) < 3 ^ 2 := by
  refine exists_dvd_mem_Ico (E := 3) (by norm_num) 32 (by norm_num) fun p hp hpd => ?_
  have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 5 by norm_num; exact hpd)
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this]
  norm_num

/-! ### All hypotheses of `core_divisors` hold together (non-vacuity)

`K = 1`, `s₀ = 1`, `z = 2`, `E₀ = 2`, `E₁ = 8`, `M = 16` and `m = 24 = 2³ · 3`.
* `P⁺(24) = 3 ≤ Y = 16/4 = 4`, and `ω₂(24) = 1 ≥ s₀`.
* `m = 24 ≤ M E₀ = 32` and `(K+1) E₁ = 16 < 24`.
* `z M = 32 ≤ 2(K+1) E₁ = 32`, `z E₀² = 8 ≤ E₁` and `z^{s₀} E₀ = 4 ≤ 24`.

So `s(24) ≥ 2`. (By hand `D(24) = {2, 3, 4, 6, 8, 12}`, so `s(24) = 6`.) -/

#guard omegaZ 2 24 = 1

example : 2 ≤ (lowerDivisors 16 1 24).card := by
  refine core_divisors (K := 1) (s₀ := 1) (z := 2) (E₀ := 2) (E₁ := 8) (by norm_num) ?_ ?_
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  · intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 ^ 3 * 3 by norm_num; exact hpd) with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)]
      norm_num
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
      norm_num
  · rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num]
    decide

/-! A member of `D(24)`, checked directly: `12 ∣ 24`, `1 < 12 ≤ 16`, and its prime factors
`2, 3` satisfy `4p ≤ 16`. -/

example : 12 ∈ lowerDivisors 16 1 24 := by
  refine mem_lowerDivisors.mpr ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num,
    fun p hp hpd => ?_⟩
  rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 ^ 2 * 3 by norm_num; exact hpd) with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
    norm_num

/-! `24` itself is **not** in `D(24)`, because `24 > M = 16`. -/

example : 24 ∉ lowerDivisors 16 1 24 := fun h => by
  have := (mem_lowerDivisors.mp h).2.2.1
  norm_num at this
