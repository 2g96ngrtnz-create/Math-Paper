import HubRemoval.Mertens

/-!
# Mertens' estimates, parts (b)–(d) (paper, Lemma 2.1)

**Lemma 2.1.** There are absolute constants `c₀, C₁ ≥ 1` such that
* (a) `∑_{p ≤ y} log p/(p − 1) ≤ log y + c₀` for all `y ≥ 2`;
* (b) `|∑_{y < p ≤ w} 1/p − log(log w / log y)| ≤ C₁/log y` for all `2 ≤ y ≤ w`;
* (c) `∑_{p ≤ z} 1/p ≥ log log z − C₁` for all `z ≥ 2`;
* (d) `π(x) ≤ C₁ x/log x` for all `x ≥ 2`.

All four are proved here with explicit constants: `c₀ = log 4 + 2` and `C₁ = 18` (`lemma_2_1`).
The arguments `y, w, z, x` are real, and "`p ≤ y`" means `p ≤ ⌊y⌋`.

* **Mertens' first theorem, both sides.** With `S(n) = ∑_{p ≤ n} log p/p`,
  `|S(n) − log n| ≤ 3` for `n ≥ 1` (`abs_Smert_sub_log_le`). The upper half is in
  `HubRemoval/Mertens.lean`. The lower half uses `(p − 1) v_p(n!) ≤ n` (Legendre) and
  `n! ≥ nⁿ/eⁿ`: `n log n − n ≤ log n! ≤ n ∑_{p ≤ n} log p/(p − 1) ≤ n (S(n) + 2)`.
* **(b) by Abel summation.** `∑_{y<p≤w} 1/p = ∑_{y<k≤w} (S(k) − S(k−1))/log k`. Write
  `S(k) = log k + E(k)` with `|E(k)| ≤ 3`. The `E` part is at most `6/log y` by Abel summation
  (`abel_sum`, `abel_err_le`). The `log` part `∑ (log k − log(k−1))/log k` is within
  `1/log² y` of `log log w − log log y = ∑ (log log k − log log(k−1))`, because
  `(v−u)/v ≤ log(v/u) ≤ (v−u)/u`. For integers this gives `8/log y` (`mertens_b_nat`); passing
  to real `y, w` gives `18/log y` (`mertens_b`).
* **(c)** is (b) with `y = 2` (`mertens_c`).
* **(d)** `π(x) ≤ √x + 2θ(x)/log x ≤ √x + 2 log 4 · x/log x ≤ 5x/log x` (`mertens_d`).
-/

namespace HubRemoval

open Finset
open scoped Nat

/-! ### Mertens' first theorem, both sides -/

/-- `S(n) = ∑_{p ≤ n} log p/p`. -/
noncomputable def Smert (n : ℕ) : ℝ := ∑ p ∈ primesUpTo n, Real.log p / p

/-- Legendre: `(p − 1) v_p(n!) ≤ n`. -/
theorem sub_one_mul_factorization_factorial_le {n p : ℕ} (hp : p.Prime) :
    ((p : ℝ) - 1) * ((n !).factorization p : ℝ) ≤ n := by
  have := Fact.mk hp
  have h : (p - 1) * (n !).factorization p ≤ n := by
    rw [Nat.factorization_def _ hp, sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have h' : (((p - 1 : ℕ) : ℝ)) * ((n !).factorization p : ℝ) ≤ n := by exact_mod_cast h
  rwa [Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h'

/-- `log n! ≥ n log n − n`, from `nⁿ/n! ≤ eⁿ`. -/
theorem log_factorial_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ Real.log (n ! : ℕ) := by
  have h1 := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
  have hf : (0 : ℝ) < (n ! : ℕ) := by exact_mod_cast Nat.factorial_pos n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : Real.log ((n : ℝ) ^ n / (n ! : ℕ)) ≤ n := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_exp] at this
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow] at h2
  linarith

/-- **Mertens' first theorem, lower half.** `S(n) ≥ log n − 3` for `n ≥ 1`. -/
theorem Smert_ge (n : ℕ) (hn : 1 ≤ n) : Real.log n - 3 ≤ Smert n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (n ! : ℕ) =
      ∑ p ∈ primesUpTo n, ((n !).factorization p : ℝ) * Real.log p :=
    log_eq_sum_primesUpTo (factorial_mem_smoothNumbers n)
  -- `v_p(n!) log p ≤ n · log p/(p − 1)`.
  have hterm : ∀ p ∈ primesUpTo n, ((n !).factorization p : ℝ) * Real.log p ≤
      n * (Real.log p / ((p : ℝ) - 1)) := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      linarith
    have h := sub_one_mul_factorization_factorial_le (n := n) hpp
    have hv : ((n !).factorization p : ℝ) ≤ n / ((p : ℝ) - 1) := by
      rw [le_div_iff₀ hp1]
      linarith
    calc ((n !).factorization p : ℝ) * Real.log p ≤ n / ((p : ℝ) - 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hv (Real.log_natCast_nonneg p)
      _ = n * (Real.log p / ((p : ℝ) - 1)) := by ring
  have hupper : Real.log (n ! : ℕ) ≤ n * ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) := by
    rw [hlog, mul_sum]
    exact sum_le_sum hterm
  -- `∑ log p/(p − 1) = S(n) + ∑ log p/(p(p − 1)) ≤ S(n) + 2`.
  have hsplit : ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) ≤ Smert n + 2 := by
    have e : ∀ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) =
        Real.log p / p + Real.log p / (p * ((p : ℝ) - 1)) := by
      intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesUpTo.mp hp).1.two_le
      have ha : (p : ℝ) - 1 ≠ 0 := by linarith
      have hb : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [sum_congr rfl e, sum_add_distrib]
    have := sum_log_div_mul_le n
    unfold Smert
    linarith
  have hlow := log_factorial_ge n
  have key : (n : ℝ) * (Real.log n - 3) ≤ n * Smert n := by nlinarith
  exact le_of_mul_le_mul_left key hnR

/-- **Mertens' first theorem.** `|S(n) − log n| ≤ 3` for `n ≥ 1`. -/
theorem abs_Smert_sub_log_le (n : ℕ) (hn : 1 ≤ n) : |Smert n - Real.log n| ≤ 3 := by
  have h1 := sum_log_div_le n hn
  have h2 := Smert_ge n hn
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  rw [abs_le]
  unfold Smert at *
  constructor <;> linarith

/-- `S(n + 1) = S(n) + [n + 1 prime] · log(n + 1)/(n + 1)`. -/
theorem Smert_succ (n : ℕ) : Smert (n + 1) = Smert n +
    (if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) else 0) := by
  unfold Smert primesUpTo
  rw [range_add_one, filter_insert]
  split_ifs with hp
  · rw [sum_insert (by simp), add_comm]
  · simp

/-! ### Abel summation and telescoping -/

/-- **Abel summation.** `∑_{y<k≤w} (E k − E(k−1)) f k = E w f w − E y f y + ∑_{y<k≤w} E(k−1)(f(k−1) − f k)`. -/
theorem abel_sum (E f : ℕ → ℝ) {y w : ℕ} (h : y ≤ w) :
    ∑ k ∈ Ioc y w, (E k - E (k - 1)) * f k =
      E w * f w - E y * f y + ∑ k ∈ Ioc y w, E (k - 1) * (f (k - 1) - f k) := by
  induction w, h using Nat.le_induction with
  | base => simp
  | succ w hyw ih =>
    rw [← insert_Ioc_right_eq_Ioc_add_one hyw, sum_insert (by simp), sum_insert (by simp), ih,
      Nat.add_sub_cancel]
    ring

/-- **Telescoping.** `∑_{y<k≤w} (g(k−1) − g k) = g y − g w`. -/
theorem sum_Ioc_tel (g : ℕ → ℝ) {y w : ℕ} (h : y ≤ w) :
    ∑ k ∈ Ioc y w, (g (k - 1) - g k) = g y - g w := by
  induction w, h using Nat.le_induction with
  | base => simp
  | succ w hyw ih =>
    rw [← insert_Ioc_right_eq_Ioc_add_one hyw, sum_insert (by simp), ih, Nat.add_sub_cancel]
    ring

/-- **The Abel error bound.** If `|E k| ≤ 3` for `k ≥ y`, and `f ≥ 0` is non-increasing on
`[y, ∞)`, then `|∑_{y<k≤w} (E k − E(k−1)) f k| ≤ 6 f y`. -/
theorem abel_err_le {E f : ℕ → ℝ} {y w : ℕ} (h : y ≤ w) (hE : ∀ k, y ≤ k → |E k| ≤ 3)
    (hf0 : ∀ k, y ≤ k → 0 ≤ f k) (hfa : ∀ k, y < k → f k ≤ f (k - 1)) :
    |∑ k ∈ Ioc y w, (E k - E (k - 1)) * f k| ≤ 6 * f y := by
  rw [abel_sum E f h]
  have h1 : |E w * f w| ≤ 3 * f w := by
    rw [abs_mul, abs_of_nonneg (hf0 w h)]
    exact mul_le_mul_of_nonneg_right (hE w h) (hf0 w h)
  have h2 : |E y * f y| ≤ 3 * f y := by
    rw [abs_mul, abs_of_nonneg (hf0 y le_rfl)]
    exact mul_le_mul_of_nonneg_right (hE y le_rfl) (hf0 y le_rfl)
  have h3 : |∑ k ∈ Ioc y w, E (k - 1) * (f (k - 1) - f k)| ≤
      ∑ k ∈ Ioc y w, 3 * (f (k - 1) - f k) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    obtain ⟨hyk, -⟩ := mem_Ioc.mp hk
    have hd : 0 ≤ f (k - 1) - f k := by linarith [hfa k hyk]
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right (hE (k - 1) (by omega)) hd
  have h4 : ∑ k ∈ Ioc y w, 3 * (f (k - 1) - f k) = 3 * (f y - f w) := by
    rw [← mul_sum, sum_Ioc_tel f h]
  rw [h4] at h3
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### Part (b), for integers -/

/-- The prime reciprocal sum over `(y, w]` as an Abel sum of `S`. -/
theorem sum_inv_primes_eq {y w : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ (primesUpTo w).filter (fun p => y < p), (1 : ℝ) / p =
      ∑ k ∈ Ioc y w, (Smert k - Smert (k - 1)) * (1 / Real.log k) := by
  have hset : (primesUpTo w).filter (fun p => y < p) = (Ioc y w).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_primesUpTo, mem_Ioc]
    tauto
  rw [hset, sum_filter]
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨hyk, -⟩ := mem_Ioc.mp hk
  have hk1 : k - 1 + 1 = k := by omega
  have hS := Smert_succ (k - 1)
  rw [hk1] at hS
  rw [hS, add_sub_cancel_left]
  split_ifs with hp
  · have hk2 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    have hlog : Real.log k ≠ 0 := (Real.log_pos hk2).ne'
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    field_simp
  · simp

/-- The main-term comparison for one `k`: with `u = log(k−1)` and `v = log k`,
`0 ≤ log(v/u) − (v − u)/v ≤ 1/((k−1)² log² y)`. -/
theorem main_term_bounds {y k : ℕ} (hy : 2 ≤ y) (hyk : y < k) :
    0 ≤ (Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) -
        (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) * (1 / Real.log k) ∧
    (Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) -
        (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) * (1 / Real.log k) ≤
      1 / ((((k - 1 : ℕ) : ℝ)) ^ 2 * Real.log y ^ 2) := by
  set a : ℝ := ((k - 1 : ℕ) : ℝ) with ha
  have hk1 : (k : ℝ) = a + 1 := by rw [ha, Nat.cast_sub (by omega)]; simp
  have hya : (y : ℝ) ≤ a := by rw [ha]; exact_mod_cast (show y ≤ k - 1 by omega)
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  set u := Real.log a with hu
  set v := Real.log k with hv
  have ha0 : 0 < a := by linarith
  have hu0 : Real.log y ≤ u := Real.log_le_log (by linarith) hya
  have hupos : 0 < u := lt_of_lt_of_le hlogy hu0
  have huv : u < v := by rw [hu, hv, hk1]; exact Real.log_lt_log (by linarith) (by linarith)
  have hvpos : 0 < v := by linarith
  -- `v − u = log((a+1)/a) ≤ 1/a`.
  have hd : v - u ≤ 1 / a := by
    have h := Real.log_le_sub_one_of_pos (div_pos (show (0 : ℝ) < a + 1 by linarith) ha0)
    rw [Real.log_div (show (a + 1 : ℝ) ≠ 0 by linarith) ha0.ne'] at h
    rw [hv, hu, hk1]
    have e : (a + 1) / a - 1 = 1 / a := by rw [div_sub_one ha0.ne']; ring
    linarith
  have hlog_div : Real.log v - Real.log u = Real.log (v / u) := (Real.log_div hvpos.ne' hupos.ne').symm
  have hlow : 1 - (v / u)⁻¹ ≤ Real.log (v / u) := Real.one_sub_inv_le_log_of_pos (by positivity)
  have hup : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have e1 : 1 - (v / u)⁻¹ = (v - u) * (1 / v) := by field_simp
  have e2 : v / u - 1 - (v - u) * (1 / v) = (v - u) ^ 2 / (u * v) := by
    field_simp
  rw [hlog_div]
  refine ⟨by linarith, ?_⟩
  have hsq : (v - u) ^ 2 / (u * v) ≤ (1 / a) ^ 2 / (Real.log y) ^ 2 := by
    have hnum : (v - u) ^ 2 ≤ (1 / a) ^ 2 := pow_le_pow_left₀ (by linarith) hd 2
    have hden : Real.log y ^ 2 ≤ u * v := by nlinarith
    calc (v - u) ^ 2 / (u * v) ≤ (1 / a) ^ 2 / (u * v) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (1 / a) ^ 2 / (Real.log y) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have e3 : (1 / a) ^ 2 / (Real.log y) ^ 2 = 1 / (a ^ 2 * Real.log y ^ 2) := by
    field_simp
  linarith

/-- `∑_{y<k≤w} 1/(k−1)² ≤ 1` for `y ≥ 2`. -/
theorem sum_inv_sq_le {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    ∑ k ∈ Ioc y w, 1 / (((k - 1 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
  have hterm : ∀ k ∈ Ioc y w, 1 / (((k - 1 : ℕ) : ℝ)) ^ 2 ≤
      2 / (((k - 1 : ℕ) : ℝ)) - 2 / (k : ℝ) := by
    intro k hk
    obtain ⟨hyk, -⟩ := mem_Ioc.mp hk
    have hk1 : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by rw [Nat.cast_sub (by omega)]; simp
    have ha : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k - 1 by omega)
    rw [hk1, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have htel := sum_Ioc_tel (fun k => 2 / (k : ℝ)) hyw
  have h2 : 2 / (y : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (show 2 ≤ 1 * y by omega)
  have h3 : 0 ≤ 2 / (w : ℝ) := by positivity
  calc ∑ k ∈ Ioc y w, 1 / (((k - 1 : ℕ) : ℝ)) ^ 2
      ≤ ∑ k ∈ Ioc y w, (2 / (((k - 1 : ℕ) : ℝ)) - 2 / (k : ℝ)) := sum_le_sum hterm
    _ = 2 / (y : ℝ) - 2 / (w : ℝ) := htel
    _ ≤ 1 := by linarith

/-- **Lemma 2.1(b), integers.** For `2 ≤ y ≤ w`,
`|∑_{y<p≤w} 1/p − (log log w − log log y)| ≤ 8/log y`. -/
theorem mertens_b_nat {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |∑ p ∈ (primesUpTo w).filter (fun p => y < p), (1 : ℝ) / p -
        (Real.log (Real.log w) - Real.log (Real.log y))| ≤ 8 / Real.log y := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  set f : ℕ → ℝ := fun k => 1 / Real.log k with hf
  set E : ℕ → ℝ := fun k => Smert k - Real.log k with hE
  -- Split `S(k) − S(k−1)` into its `log` part and its `E` part.
  have hsplit : ∑ k ∈ Ioc y w, (Smert k - Smert (k - 1)) * (1 / Real.log k) =
      ∑ k ∈ Ioc y w, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) * (1 / Real.log k) +
        ∑ k ∈ Ioc y w, (E k - E (k - 1)) * f k := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [hE, hf]
    ring
  set T := ∑ k ∈ Ioc y w, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) * (1 / Real.log k)
  -- The `E` part.
  have herr : |∑ k ∈ Ioc y w, (E k - E (k - 1)) * f k| ≤ 6 * (1 / Real.log y) := by
    refine abel_err_le hyw (fun k hk => abs_Smert_sub_log_le k (by omega)) (fun k hk => ?_)
      (fun k hk => ?_)
    · have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      exact div_nonneg zero_le_one (Real.log_nonneg (by linarith))
    · have h1 : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k - 1 by omega)
      have h2 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      have hl1 : 0 < Real.log ((k - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le hl1 (Real.log_le_log (by linarith) h2)
  -- The `log` part.
  set L := Real.log (Real.log w) - Real.log (Real.log y)
  have hL : L = ∑ k ∈ Ioc y w,
      (Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) := by
    have := sum_Ioc_tel (fun k => Real.log (Real.log k)) hyw
    have e : ∑ k ∈ Ioc y w, (Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) =
        -∑ k ∈ Ioc y w, (Real.log (Real.log ((k - 1 : ℕ) : ℝ)) - Real.log (Real.log k)) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [e, this]
    ring
  have hLT0 : 0 ≤ L - T := by
    rw [hL, ← sum_sub_distrib]
    exact sum_nonneg fun k hk => (main_term_bounds hy (mem_Ioc.mp hk).1).1
  have hLT1 : L - T ≤ 1 / Real.log y ^ 2 := by
    rw [hL, ← sum_sub_distrib]
    calc ∑ k ∈ Ioc y w, ((Real.log (Real.log k) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) -
          (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) * (1 / Real.log k))
        ≤ ∑ k ∈ Ioc y w, 1 / ((((k - 1 : ℕ) : ℝ)) ^ 2 * Real.log y ^ 2) :=
          sum_le_sum fun k hk => (main_term_bounds hy (mem_Ioc.mp hk).1).2
      _ = (∑ k ∈ Ioc y w, 1 / (((k - 1 : ℕ) : ℝ)) ^ 2) * (1 / Real.log y ^ 2) := by
          rw [sum_mul]
          exact sum_congr rfl fun k _ => by rw [div_mul_div_comm, one_mul]
      _ ≤ 1 * (1 / Real.log y ^ 2) :=
          mul_le_mul_of_nonneg_right (sum_inv_sq_le hy hyw) (by positivity)
      _ = 1 / Real.log y ^ 2 := one_mul _
  -- Combine.
  have hsmall : 1 / Real.log y ^ 2 ≤ 2 / Real.log y := by
    have hl2 : (1 / 2 : ℝ) ≤ Real.log y := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log (by norm_num) hy2
      linarith
    rw [div_le_div_iff₀ (by positivity) hlogy]
    nlinarith
  rw [sum_inv_primes_eq (by omega), hsplit]
  have e : T + ∑ k ∈ Ioc y w, (E k - E (k - 1)) * f k - L =
      ∑ k ∈ Ioc y w, (E k - E (k - 1)) * f k - (L - T) := by ring
  rw [e]
  have h8 : 8 / Real.log y = 6 * (1 / Real.log y) + 2 / Real.log y := by ring
  rw [h8]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hLT0]
  linarith

/-! ### From integers to reals -/

/-- For real `x ≥ 2` and `n = ⌊x⌋`: `0 ≤ log log x − log log n ≤ 1/(2 log n)` and
`1/log n ≤ 2/log x`. -/
theorem loglog_floor {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ Real.log (Real.log x) - Real.log (Real.log (⌊x⌋₊ : ℝ)) ∧
    Real.log (Real.log x) - Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ 1 / (2 * Real.log (⌊x⌋₊ : ℝ)) ∧
    1 / Real.log (⌊x⌋₊ : ℝ) ≤ 2 / Real.log x := by
  set n := ⌊x⌋₊
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hln : 0 < Real.log n := Real.log_pos (by linarith)
  have hl2 : (1 / 2 : ℝ) < Real.log n := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hnR
    linarith
  have hlx : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
  -- `log x − log n ≤ x/n − 1 < 1/n ≤ 1/2`.
  have hdiff : Real.log x - Real.log n ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / n by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at h
    have : x / n - 1 ≤ 1 / 2 := by
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hlogx : 0 < Real.log x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := Real.log_le_log hln hlx
    linarith
  · rw [← Real.log_div hlogx.ne' hln.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log x / Real.log n by positivity)
    have : Real.log x / Real.log n - 1 ≤ 1 / (2 * Real.log n) := by
      rw [div_sub_one hln.ne', div_le_div_iff₀ hln (by positivity)]
      nlinarith
    linarith
  · rw [div_le_div_iff₀ hln hlogx]
    linarith

/-- For real `y ≥ 0` and natural `p`: `y < p ↔ ⌊y⌋ < p`. -/
theorem lt_iff_floor_lt {y : ℝ} (hy : 0 ≤ y) (p : ℕ) : y < p ↔ ⌊y⌋₊ < p :=
  (Nat.floor_lt hy).symm

/-- **Lemma 2.1(b).** For real `2 ≤ y ≤ w`,
`|∑_{y<p≤w} 1/p − log(log w / log y)| ≤ 18/log y`. -/
theorem mertens_b {y w : ℝ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |∑ p ∈ (primesUpTo ⌊w⌋₊).filter (fun p : ℕ => y < p), (1 : ℝ) / p -
        Real.log (Real.log w / Real.log y)| ≤ 18 / Real.log y := by
  set Y := ⌊y⌋₊
  set W := ⌊w⌋₊
  have hY2 : 2 ≤ Y := Nat.le_floor (by exact_mod_cast hy)
  have hYW : Y ≤ W := Nat.floor_le_floor hyw
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hset : (primesUpTo W).filter (fun p : ℕ => y < p) = (primesUpTo W).filter (fun p => Y < p) :=
    filter_congr fun p _ => lt_iff_floor_lt (by linarith) p
  rw [hset, Real.log_div hlogw.ne' hlogy.ne']
  have hb := mertens_b_nat hY2 hYW
  obtain ⟨hw0, hw1, -⟩ := loglog_floor (x := w) (by linarith)
  obtain ⟨hy0, hy1, hyY⟩ := loglog_floor hy
  have hlY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hWY : Real.log (Y : ℝ) ≤ Real.log (W : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hYW)
  have hW1 : 1 / (2 * Real.log (W : ℝ)) ≤ 1 / (2 * Real.log (Y : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e1 : 1 / (2 * Real.log (Y : ℝ)) = (1 / 2) * (1 / Real.log (Y : ℝ)) := by
    field_simp
  have e2 : 8 / Real.log (Y : ℝ) = 8 * (1 / Real.log (Y : ℝ)) := by ring
  have e3 : 18 / Real.log y = 9 * (2 / Real.log y) := by ring
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith

/-- **Lemma 2.1(c).** For real `z ≥ 2`, `∑_{p ≤ z} 1/p ≥ log log z − 13`. -/
theorem mertens_c {z : ℝ} (hz : 2 ≤ z) :
    Real.log (Real.log z) - 13 ≤ ∑ p ∈ primesUpTo ⌊z⌋₊, (1 : ℝ) / p := by
  set Z := ⌊z⌋₊
  have hZ2 : 2 ≤ Z := Nat.le_floor (by exact_mod_cast hz)
  have hb := mertens_b_nat (le_refl 2) hZ2
  obtain ⟨-, hz1, hzZ⟩ := loglog_floor hz
  have hsub : ∑ p ∈ (primesUpTo Z).filter (fun p => 2 < p), (1 : ℝ) / p ≤
      ∑ p ∈ primesUpTo Z, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => by positivity
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hll2 : Real.log (Real.log 2) < 0 := Real.log_neg (by linarith) (by linarith)
  have hlZ : Real.log 2 ≤ Real.log (Z : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hZ2)
  have h8 : 8 / Real.log 2 ≤ 12 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h1 : 1 / (2 * Real.log (Z : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  push_cast at hb
  rw [abs_le] at hb
  linarith [hb.1]

/-- **Lemma 2.1(d).** For real `x ≥ 2`, `π(x) ≤ 5x/log x`. -/
theorem mertens_d {x : ℝ} (hx : 2 ≤ x) :
    ((primesUpTo ⌊x⌋₊).card : ℝ) ≤ 5 * x / Real.log x := by
  set P := primesUpTo ⌊x⌋₊
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  -- Primes `≤ √x`: at most `√x` of them.
  have hsmall : ((P.filter fun p : ℕ => ¬ Real.sqrt x < p).card : ℝ) ≤ Real.sqrt x := by
    have hsub : P.filter (fun p : ℕ => ¬ Real.sqrt x < p) ⊆ Icc 1 ⌊Real.sqrt x⌋₊ := by
      intro p hp
      obtain ⟨hpP, hle⟩ := mem_filter.mp hp
      push Not at hle
      exact mem_Icc.mpr ⟨(mem_primesUpTo.mp hpP).1.one_lt.le, Nat.le_floor hle⟩
    have h1 := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hsqrt.le)
  -- Primes `> √x`: each has `log p ≥ ½ log x`, and `θ(x) ≤ x log 4`.
  have hbig : ((P.filter fun p : ℕ => Real.sqrt x < p).card : ℝ) * (Real.log x / 2) ≤
      x * Real.log 4 := by
    calc ((P.filter fun p : ℕ => Real.sqrt x < p).card : ℝ) * (Real.log x / 2)
        = ∑ _p ∈ P.filter (fun p : ℕ => Real.sqrt x < p), Real.log x / 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ P.filter (fun p : ℕ => Real.sqrt x < p), Real.log p := by
          refine sum_le_sum fun p hp => ?_
          rw [← Real.log_sqrt (by linarith)]
          exact Real.log_le_log hsqrt (mem_filter.mp hp).2.le
      _ ≤ ∑ p ∈ P, Real.log p :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ =>
            Real.log_natCast_nonneg p
      _ ≤ (⌊x⌋₊ : ℝ) * Real.log 4 := theta_le _
      _ ≤ x * Real.log 4 :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (Real.log_nonneg (by norm_num))
  have hsplit : (P.card : ℝ) = (P.filter fun p : ℕ => Real.sqrt x < p).card +
      (P.filter fun p : ℕ => ¬ Real.sqrt x < p).card := by
    exact_mod_cast (card_filter_add_card_filter_not (s := P) (fun p : ℕ => Real.sqrt x < p)).symm
  -- `√x ≤ 2x/log x`, since `log x = 2 log √x ≤ 2(√x − 1)`.
  have hsx : Real.sqrt x * Real.log x ≤ 2 * x := by
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt (by linarith)]
      ring
    have h2 := Real.log_le_sub_one_of_pos hsqrt
    have h3 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    nlinarith
  have hl4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  rw [le_div_iff₀ hlogx]
  nlinarith

/-- **Lemma 2.1(a), for real `y ≥ 2`.** -/
theorem mertens_a_real {y : ℝ} (hy : 2 ≤ y) :
    ∑ p ∈ primesUpTo ⌊y⌋₊, Real.log p / ((p : ℝ) - 1) ≤ Real.log y + (Real.log 4 + 2) := by
  have hn : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have h := mertens_a ⌊y⌋₊ hn
  have h2 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hn) (Nat.floor_le (by linarith))
  linarith

/-- **Lemma 2.1**, with `c₀ = log 4 + 2` and `C₁ = 18`. -/
theorem lemma_2_1 : ∃ c₀ C₁ : ℝ, 1 ≤ c₀ ∧ 1 ≤ C₁ ∧
    (∀ y : ℝ, 2 ≤ y → ∑ p ∈ primesUpTo ⌊y⌋₊, Real.log p / ((p : ℝ) - 1) ≤ Real.log y + c₀) ∧
    (∀ y w : ℝ, 2 ≤ y → y ≤ w →
      |∑ p ∈ (primesUpTo ⌊w⌋₊).filter (fun p : ℕ => y < p), (1 : ℝ) / p -
        Real.log (Real.log w / Real.log y)| ≤ C₁ / Real.log y) ∧
    (∀ z : ℝ, 2 ≤ z → Real.log (Real.log z) - C₁ ≤ ∑ p ∈ primesUpTo ⌊z⌋₊, (1 : ℝ) / p) ∧
    (∀ x : ℝ, 2 ≤ x → ((primesUpTo ⌊x⌋₊).card : ℝ) ≤ C₁ * x / Real.log x) := by
  refine ⟨Real.log 4 + 2, 18, by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)],
    by norm_num, fun y hy => mertens_a_real hy, fun y w hy hyw => mertens_b hy hyw,
    fun z hz => (by linarith : Real.log (Real.log z) - 18 ≤ Real.log (Real.log z) - 13).trans
      (mertens_c hz), fun x hx => ?_⟩
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  refine (mertens_d hx).trans ?_
  rw [div_le_div_iff_of_pos_right hlogx]
  linarith

end HubRemoval
