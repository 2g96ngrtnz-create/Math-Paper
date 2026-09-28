import HubRemoval.PsiUpper

/-!
# Mertens' estimate, part (a) (paper, Lemma 2.1(a))

**Lemma 2.1(a).** `∑_{p ≤ n} log p/(p − 1) ≤ log n + c₀` for all `n ≥ 1`, with `c₀ = log 4 + 2`.

The paper cites Mertens. Here it is proved from scratch, with an explicit constant.
* **Chebyshev:** `θ(n) = ∑_{p ≤ n} log p ≤ n log 4`, because the primorial is `≤ 4^n` (Mathlib).
* **Legendre:** `v_p(n!) ≥ ⌊n/p⌋`, so
  `∑_{p ≤ n} (n/p − 1) log p ≤ ∑_{p ≤ n} v_p(n!) log p = log n! ≤ n log n`. Hence
  `∑_{p ≤ n} log p/p ≤ log n + θ(n)/n ≤ log n + log 4`.
* **Telescoping:** `log k/(k(k − 1)) ≤ h(k − 1) − h(k)` with `h(k) = (log k + 2)/k`, so
  `∑_{p ≤ n} log p/(p(p − 1)) ≤ h(1) = 2`.
* `log p/(p − 1) = log p/p + log p/(p(p − 1))`.

With this, Lemma 2.3 holds unconditionally (`psi_upper'`).
-/

namespace HubRemoval

open Finset
open scoped Nat

/-- **Chebyshev's bound.** `θ(n) = ∑_{p ≤ n} log p ≤ n log 4`. -/
theorem theta_le (n : ℕ) : ∑ p ∈ primesUpTo n, Real.log p ≤ n * Real.log 4 := by
  have hprod : ((∏ p ∈ primesUpTo n, p : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by
    have := primorial_le_four_pow n
    unfold primorial at this
    exact_mod_cast this
  have hpos : ∀ p ∈ primesUpTo n, (p : ℝ) ≠ 0 := fun p hp => by
    have := (mem_primesUpTo.mp hp).1.pos
    positivity
  rw [← Real.log_prod hpos, ← Real.log_pow]
  push_cast at hprod
  exact Real.log_le_log (prod_pos fun p hp => by
    have := (mem_primesUpTo.mp hp).1.pos
    positivity) hprod

/-- **Legendre (first term).** For a prime `p ≤ n`, `⌊n/p⌋ ≤ v_p(n!)`. -/
theorem div_le_factorization_factorial {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    n / p ≤ (n !).factorization p := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, padicValNat_factorial (b := Nat.log p n + 1) (by omega)]
  have h1 : 1 ∈ Ico 1 (Nat.log p n + 1) := by
    have : 1 ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpn)
    exact mem_Ico.mpr ⟨le_rfl, by omega⟩
  simpa using single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1

/-- `n!` is `n`-smooth. -/
theorem factorial_mem_smoothNumbers (n : ℕ) : n ! ∈ Nat.smoothNumbers (n + 1) := by
  refine Nat.mem_smoothNumbers'.mpr fun p hp hpd => ?_
  have := (Nat.Prime.dvd_factorial hp).mp hpd
  omega

/-- **Mertens' first theorem, upper half.** `∑_{p ≤ n} log p/p ≤ log n + log 4` for `n ≥ 1`. -/
theorem sum_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ primesUpTo n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- `∑ (n/p − 1) log p ≤ ∑ v_p(n!) log p = log n! ≤ n log n`.
  have hlog : Real.log (n ! : ℕ) = ∑ p ∈ primesUpTo n, ((n !).factorization p : ℝ) * Real.log p :=
    log_eq_sum_primesUpTo (factorial_mem_smoothNumbers n)
  have hfact : Real.log (n ! : ℕ) ≤ n * Real.log n := by
    have h1 : ((n ! : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (0 : ℝ) < (n ! : ℕ) := by exact_mod_cast Nat.factorial_pos n
    calc Real.log (n ! : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
      _ = n * Real.log n := by rw [Real.log_pow]
  have hterm : ∀ p ∈ primesUpTo n, ((n : ℝ) / p - 1) * Real.log p ≤
      ((n !).factorization p : ℝ) * Real.log p := by
    intro p hp
    obtain ⟨hpp, hpn⟩ := mem_primesUpTo.mp hp
    refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
    have h1 : ((n / p : ℕ) : ℝ) ≤ (n !).factorization p := by
      exact_mod_cast div_le_factorization_factorial hpp hpn
    have h2 := Nat.lt_floor_add_one ((n : ℝ) / p)
    rw [Nat.floor_div_eq_div] at h2
    linarith
  have hsum := sum_le_sum hterm
  rw [← hlog] at hsum
  have htheta := theta_le n
  have e : ∑ p ∈ primesUpTo n, ((n : ℝ) / p - 1) * Real.log p =
      n * ∑ p ∈ primesUpTo n, Real.log p / p - ∑ p ∈ primesUpTo n, Real.log p := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
  rw [e] at hsum
  have key : (n : ℝ) * ∑ p ∈ primesUpTo n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left key hnR

/-- `h(k) = (log k + 2)/k`. -/
noncomputable def hTel (k : ℕ) : ℝ := (Real.log k + 2) / k

/-- **The telescoping step.** For `k ≥ 2`, `log k/(k(k − 1)) ≤ h(k − 1) − h(k)`. -/
theorem log_div_le_tel {k : ℕ} (hk : 2 ≤ k) :
    Real.log k / (k * ((k : ℝ) - 1)) ≤ hTel (k - 1) - hTel k := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  unfold hTel
  rw [hk1]
  have ha : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hb : (0 : ℝ) < k := by linarith
  -- `log((k−1)/k) ≥ 1 − k/(k−1)`.
  have hl : 1 - ((k : ℝ) - 1)⁻¹ * k ≤ Real.log (((k : ℝ) - 1) / k) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
    rwa [inv_div, div_eq_inv_mul] at this
  rw [Real.log_div ha.ne' hb.ne'] at hl
  rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hinv : ((k : ℝ) - 1)⁻¹ * k = 1 + ((k : ℝ) - 1)⁻¹ := by field_simp; ring
  have hinv2 : ((k : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  rw [hinv] at hl
  -- `k (log(k−1) − log k) ≥ −k/(k−1) ≥ −2`.
  have hmain : 0 ≤ (k : ℝ) * (Real.log ((k : ℝ) - 1) - Real.log k) + 2 := by
    have h1 : -((k : ℝ) - 1)⁻¹ ≤ Real.log ((k : ℝ) - 1) - Real.log k := by linarith
    have h2 : (k : ℝ) * ((k : ℝ) - 1)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ ha]
      linarith
    nlinarith
  have hpos : (0 : ℝ) < k * ((k : ℝ) - 1) := by positivity
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ k by linarith)]

/-- `∑_{2 ≤ k ≤ n} log k/(k(k − 1)) ≤ h(1) − h(n)`. -/
theorem sum_tel_le (n : ℕ) :
    ∑ k ∈ Icc 2 n, Real.log k / (k * ((k : ℝ) - 1)) ≤ hTel 1 - hTel n := by
  induction n with
  | zero => simp [hTel]
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    · obtain rfl : n = 0 := by omega
      simp [hTel]
    · rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp)]
      have := log_div_le_tel (k := n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this
      linarith

/-- `∑_{p ≤ n} log p/(p(p − 1)) ≤ 2`. -/
theorem sum_log_div_mul_le (n : ℕ) :
    ∑ p ∈ primesUpTo n, Real.log p / (p * ((p : ℝ) - 1)) ≤ 2 := by
  have hsub : primesUpTo n ⊆ Icc 2 n := fun p hp => by
    obtain ⟨hpp, hpn⟩ := mem_primesUpTo.mp hp
    exact mem_Icc.mpr ⟨hpp.two_le, hpn⟩
  have hnn : ∀ k ∈ Icc 2 n, k ∉ primesUpTo n → 0 ≤ Real.log k / (k * ((k : ℝ) - 1)) :=
    fun k hk _ => by
      have : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have : (0 : ℝ) ≤ k * ((k : ℝ) - 1) := by nlinarith
      exact div_nonneg (Real.log_natCast_nonneg k) this
  have h1 := sum_le_sum_of_subset_of_nonneg hsub hnn
  have h2 := sum_tel_le n
  have h3 : 0 ≤ hTel n := div_nonneg (by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Real.log_natCast_nonneg n
      linarith) (Nat.cast_nonneg n)
  have h4 : hTel 1 = 2 := by simp [hTel]
  linarith

/-- **Lemma 2.1(a).** `∑_{p ≤ n} log p/(p − 1) ≤ log n + (log 4 + 2)` for `n ≥ 1`. -/
theorem mertens_a (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) ≤ Real.log n + (Real.log 4 + 2) := by
  have hsplit : ∀ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) =
      Real.log p / p + Real.log p / (p * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesUpTo.mp hp).1.two_le
    have ha : (p : ℝ) - 1 ≠ 0 := by linarith
    have hb : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have h1 := sum_log_div_le n hn
  have h2 := sum_log_div_mul_le n
  linarith

/-- **Lemma 2.3, unconditional.** For `x ≥ 2` and `y ≥ 1`,
`Ψ(x, y) ≤ √x + 2x(log y + c₀)/log x` with `c₀ = log 4 + 2`. -/
theorem psi_upper' {x y : ℕ} (hx : 2 ≤ x) (hy : 1 ≤ y) :
    (psi x y : ℝ) ≤ Real.sqrt x + 2 * x * (Real.log y + (Real.log 4 + 2)) / Real.log x :=
  psi_upper hx (mertens_a y hy)

end HubRemoval
