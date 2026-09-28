import HubRemoval.Doubling
open HubRemoval

/-! ### Lemma 4.2: axioms -/

#print axioms reachable_two_pow_mul
#print axioms doubling
#print axioms doubling_connected

/-! ### A concrete application (non-vacuity)

`M = 100`, `K = 3`, so `Y = 100 / 8 = 12.5`. The numbers `9 = 3²` and `77 = 7 · 11` lie in `S_M`,
because all their prime factors are `≤ 12.5`. Lemma 4.2 therefore connects them in `G_{100,3}`. -/

theorem goodSet_9 : goodSet 100 3 9 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by norm_num; exact hpd)
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3]
  norm_num

theorem goodSet_77 : goodSet 100 3 77 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 7 * 11 by norm_num; exact hpd) with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]; norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]; norm_num

example : (divGraph ⌊(100 : ℝ)⌋₊ 3).Reachable 9 77 :=
  doubling_connected (by norm_num) goodSet_9 goodSet_77
