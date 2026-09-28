import Mathlib

/-!
# The variance of `ω_z` (paper, Lemma 2.4)

`ω_z(m)` is the number of primes `p ≤ z` dividing `m`, and `L = ∑_{p ≤ z} 1/p`.

**Lemma 2.4.** Let `2 ≤ z ≤ N`. Then `∑_{m ≤ N} (ω_z(m) − L)² ≤ 3NL`. Consequently, for every real
`s ≤ L/2`, `#{m ≤ N : ω_z(m) < s} ≤ 12N/L`.

The paper allows a real `z`. The primes `≤ z` are the primes `≤ ⌊z⌋`, so a natural number `z`
loses nothing. The variance bound needs only `z ≤ N`. The paper's hypothesis `0 ≤ s` is not
needed for the count.

The proof is the paper's:
* `S₁ = ∑ ω_z(m) = ∑_p ⌊N/p⌋ ≥ NL − π(z)`;
* `S₂ = ∑ ω_z(m)² = ∑_{p,q} #{m ≤ N : p ∣ m, q ∣ m} ≤ NL + NL²`, because distinct primes
  `p, q` both divide `m` exactly when `pq ∣ m`;
* `∑ (ω_z − L)² = S₂ − 2LS₁ + NL² ≤ NL + 2Lπ(z) ≤ 3NL`, using `π(z) ≤ z ≤ N`.
-/

namespace HubRemoval

open Finset

/-- The primes `p ≤ z`. -/
def primesUpTo (z : ℕ) : Finset ℕ := (range (z + 1)).filter Nat.Prime

/-- `ω_z(m)`: the number of primes `p ≤ z` dividing `m`. -/
def omegaZ (z m : ℕ) : ℕ := ((primesUpTo z).filter (· ∣ m)).card

/-- `L = ∑_{p ≤ z} 1/p`. It is defined over any division ring, so that it can be evaluated
exactly over `ℚ`. -/
def Lz {R : Type*} [DivisionRing R] (z : ℕ) : R := ∑ p ∈ primesUpTo z, (1 : R) / p

theorem mem_primesUpTo {z p : ℕ} : p ∈ primesUpTo z ↔ p.Prime ∧ p ≤ z := by
  simp [primesUpTo, and_comm]

/-- `π(z) ≤ z`. -/
theorem card_primesUpTo_le (z : ℕ) : (primesUpTo z).card ≤ z := by
  have h : primesUpTo z ⊆ Ioc 0 z := fun p hp => by
    rw [mem_primesUpTo] at hp
    exact mem_Ioc.mpr ⟨hp.1.pos, hp.2⟩
  simpa using card_le_card h

theorem Lz_nonneg (z : ℕ) : 0 ≤ (Lz z : ℝ) := sum_nonneg fun _ _ => by positivity

theorem omegaZ_cast (z m : ℕ) :
    (omegaZ z m : ℝ) = ∑ p ∈ primesUpTo z, if p ∣ m then (1 : ℝ) else 0 := by
  unfold omegaZ
  rw [natCast_card_filter]

/-- The number of multiples of `d` in `[1, N]` is `⌊N/d⌋`. -/
theorem sum_ind_dvd (N d : ℕ) :
    ∑ m ∈ Ioc 0 N, (if d ∣ m then (1 : ℝ) else 0) = ((N / d : ℕ) : ℝ) := by
  rw [← natCast_card_filter, Nat.Ioc_filter_dvd_card_eq_div]

/-- `⌊N/d⌋ ≥ N/d − 1`. -/
theorem natDiv_ge (N d : ℕ) : (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
  have h := Nat.lt_floor_add_one ((N : ℝ) / d)
  rw [Nat.floor_div_eq_div] at h
  linarith

/-- `S₁ = ∑_{m ≤ N} ω_z(m) = ∑_{p ≤ z} ⌊N/p⌋`. -/
theorem sum_omegaZ (z N : ℕ) :
    ∑ m ∈ Ioc 0 N, (omegaZ z m : ℝ) = ∑ p ∈ primesUpTo z, ((N / p : ℕ) : ℝ) := by
  simp_rw [omegaZ_cast]
  rw [sum_comm]
  exact sum_congr rfl fun p _ => sum_ind_dvd N p

/-- `S₁ ≥ NL − π(z)`. -/
theorem sum_omegaZ_ge (z N : ℕ) :
    (N : ℝ) * Lz z - (primesUpTo z).card ≤ ∑ m ∈ Ioc 0 N, (omegaZ z m : ℝ) := by
  rw [sum_omegaZ, Lz, mul_sum]
  have h : ∀ p ∈ primesUpTo z, (N : ℝ) * (1 / p) - 1 ≤ ((N / p : ℕ) : ℝ) := fun p _ => by
    rw [mul_one_div]
    exact natDiv_ge N p
  have hs := sum_le_sum h
  rw [sum_sub_distrib] at hs
  simpa using hs

/-- `#{m ≤ N : p ∣ m, q ∣ m} ≤ N/(pq) + [p = q] N/p` for primes `p, q`. -/
theorem count_two_dvd_le {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∑ m ∈ Ioc 0 N, (if p ∣ m ∧ q ∣ m then (1 : ℝ) else 0) ≤
      (N : ℝ) * ((1 / p) * (1 / q)) + if p = q then (N : ℝ) * (1 / p) else 0 := by
  by_cases hpq : p = q
  · subst hpq
    simp only [and_self, ↓reduceIte]
    rw [sum_ind_dvd]
    have h1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have h2 : (N : ℝ) * (1 / p) = N / p := mul_one_div _ _
    have : (0 : ℝ) ≤ N * ((1 / p) * (1 / p)) := by positivity
    linarith
  · have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
    have hiff : ∀ m, (p ∣ m ∧ q ∣ m) ↔ p * q ∣ m := fun m =>
      ⟨fun ⟨h1, h2⟩ => hcop.mul_dvd_of_dvd_of_dvd h1 h2,
        fun h => ⟨(Dvd.intro q rfl).trans h, (Dvd.intro_left p rfl).trans h⟩⟩
    simp only [hiff, hpq, ↓reduceIte, add_zero]
    rw [sum_ind_dvd]
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := p * q)
    push_cast at this
    calc ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / (p * q) := this
      _ = (N : ℝ) * ((1 / p) * (1 / q)) := by field_simp

/-- `S₂ = ∑_{m ≤ N} ω_z(m)² ≤ NL + NL²`. -/
theorem sum_omegaZ_sq_le (z N : ℕ) :
    ∑ m ∈ Ioc 0 N, (omegaZ z m : ℝ) ^ 2 ≤ N * Lz z + N * Lz z ^ 2 := by
  have hsq : ∀ m, (omegaZ z m : ℝ) ^ 2 = ∑ p ∈ primesUpTo z, ∑ q ∈ primesUpTo z,
      if p ∣ m ∧ q ∣ m then (1 : ℝ) else 0 := by
    intro m
    rw [omegaZ_cast, sq, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    split_ifs <;> simp_all
  simp_rw [hsq]
  rw [sum_comm]
  have hswap : ∀ p ∈ primesUpTo z, ∑ m ∈ Ioc 0 N, ∑ q ∈ primesUpTo z,
      (if p ∣ m ∧ q ∣ m then (1 : ℝ) else 0) =
      ∑ q ∈ primesUpTo z, ∑ m ∈ Ioc 0 N, (if p ∣ m ∧ q ∣ m then (1 : ℝ) else 0) :=
    fun p _ => sum_comm
  rw [sum_congr rfl hswap]
  calc ∑ p ∈ primesUpTo z, ∑ q ∈ primesUpTo z, ∑ m ∈ Ioc 0 N,
        (if p ∣ m ∧ q ∣ m then (1 : ℝ) else 0)
      ≤ ∑ p ∈ primesUpTo z, ∑ q ∈ primesUpTo z,
        ((N : ℝ) * ((1 / p) * (1 / q)) + if p = q then (N : ℝ) * (1 / p) else 0) :=
        sum_le_sum fun p hp => sum_le_sum fun q hq =>
          count_two_dvd_le (mem_primesUpTo.mp hp).1 (mem_primesUpTo.mp hq).1
    _ = ∑ p ∈ primesUpTo z, ((N : ℝ) * (1 / p) * Lz z + (N : ℝ) * (1 / p)) := by
        refine sum_congr rfl fun p hp => ?_
        rw [sum_add_distrib, sum_ite_eq]
        simp only [hp, ↓reduceIte]
        congr 1
        rw [Lz, mul_sum]
        exact sum_congr rfl fun q _ => by ring
    _ = N * Lz z + N * Lz z ^ 2 := by
        rw [sum_add_distrib, ← sum_mul, ← mul_sum]
        unfold Lz
        ring

/-- **Lemma 2.4, the variance bound.** For `z ≤ N`, `∑_{m ≤ N} (ω_z(m) − L)² ≤ 3NL`. -/
theorem turan_variance {z N : ℕ} (hzN : z ≤ N) :
    ∑ m ∈ Ioc 0 N, ((omegaZ z m : ℝ) - Lz z) ^ 2 ≤ 3 * (N : ℝ) * Lz z := by
  have hL0 := Lz_nonneg z
  have h1 := sum_omegaZ_sq_le z N
  have h2 := sum_omegaZ_ge z N
  have h3 : ((primesUpTo z).card : ℝ) ≤ N := by exact_mod_cast (card_primesUpTo_le z).trans hzN
  set L : ℝ := Lz z with hL
  have hexp : ∑ m ∈ Ioc 0 N, ((omegaZ z m : ℝ) - L) ^ 2 =
      ∑ m ∈ Ioc 0 N, (omegaZ z m : ℝ) ^ 2 - 2 * L * ∑ m ∈ Ioc 0 N, (omegaZ z m : ℝ) +
        N * L ^ 2 := by
    have h : ∀ m, ((omegaZ z m : ℝ) - L) ^ 2 =
        (omegaZ z m : ℝ) ^ 2 - (2 * L) * (omegaZ z m : ℝ) + L ^ 2 := fun m => by ring
    simp_rw [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Ioc,
      nsmul_eq_mul, Nat.sub_zero]
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * L),
    mul_le_mul_of_nonneg_left h3 hL0]

/-- **Lemma 2.4, the count.** For `2 ≤ z ≤ N` and `s ≤ L/2`,
`#{m ≤ N : ω_z(m) < s} ≤ 12N/L`. -/
theorem turan_count {z N : ℕ} (hz : 2 ≤ z) (hzN : z ≤ N) {s : ℝ} (hs : s ≤ Lz z / 2) :
    (((Ioc 0 N).filter (fun m => (omegaZ z m : ℝ) < s)).card : ℝ) ≤ 12 * (N : ℝ) / Lz z := by
  have hvar := turan_variance hzN
  set L : ℝ := Lz z with hL
  have hLpos : 0 < L := by
    have h2 : 2 ∈ primesUpTo z := mem_primesUpTo.mpr ⟨Nat.prime_two, hz⟩
    have := single_le_sum (f := fun p : ℕ => (1 : ℝ) / p) (fun p _ => by positivity) h2
    have h' : (0 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
    rw [hL, Lz]
    linarith
  set E := (Ioc 0 N).filter (fun m => (omegaZ z m : ℝ) < s)
  have hE : ∀ m ∈ E, (L / 2) ^ 2 ≤ ((omegaZ z m : ℝ) - L) ^ 2 := by
    intro m hm
    have hf := (mem_filter.mp hm).2
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 3 * L / 2 - omegaZ z m)
      (by linarith : (0 : ℝ) < L / 2 - omegaZ z m)]
  have hsum : (E.card : ℝ) * (L / 2) ^ 2 ≤ ∑ m ∈ Ioc 0 N, ((omegaZ z m : ℝ) - L) ^ 2 :=
    calc (E.card : ℝ) * (L / 2) ^ 2 = ∑ _m ∈ E, (L / 2) ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ E, ((omegaZ z m : ℝ) - L) ^ 2 := sum_le_sum hE
      _ ≤ ∑ m ∈ Ioc 0 N, ((omegaZ z m : ℝ) - L) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have key : (E.card : ℝ) * L * L ≤ 12 * N * L := by linarith
  rw [le_div_iff₀ hLpos]
  exact le_of_mul_le_mul_right key hLpos

end HubRemoval
