import HubRemoval.SubSum
import HubRemoval.RemarkClique

/-!
# Remark 7.2, second aside: for `θ < 1/3`, almost all of `F₁` has a divisor in `(K, √N]`

The remark contrasts the obstruction for `1/3 < θ < 1/2` (`remark_7_2`: a positive proportion
of `F₁` has no divisor in `(K, √N]`) with the case `θ < 1/3`, "compare the sub-sum lemma". The
precise statement proved here (`remark_7_2_small`) is: if `log(K + 1)/log N → θ < 1/3`, then all
but `o(N)` elements of `F₁` have a divisor in `(K, √N]`.

*Proof.* Fix `c > 0`, and take a small `ε`, `θ' = θ + ε/2` and `η = ε/8`.
* **Sub-sum ⇒ divisor** (`exists_divisor_of_subsum`). If every prime factor of `m ≥ 2` is
  `< m^{1−θ'}`, the sub-sum lemma applied to the multiset `{log p/log m}` (with multiplicity) gives
  a divisor `d` of `m` with `m^{θ'} ≤ d ≤ m^{1/2}`.
* For `m ∈ F₁` with `m ≥ N^{1−η}` and large `N`, `m^{θ'} > K`. So an `m` without a divisor in
  `(K, √N]` has a prime factor `p ≥ m^{1−θ'} > N^a`, where `a = (1 − η)(1 − θ − ε)`, and
  `p ≤ B ≤ N^b` with `b = 1 − θ + ε`.
* Hence the exceptional set has at most `N^{1−η} + N ∑_{N^a < p ≤ N^b} 1/p` elements, and by
  Lemma 2.1(b) the sum is at most `log(b/a) + 18/(a log N) ≤ 10ε + o(1)`.
-/

namespace HubRemoval

open Finset Filter Topology

/-- **Sub-sum ⇒ divisor.** If `m ≥ 2`, `0 < θ ≤ 1/3`, and every prime factor `p` of `m` has
`p < m^{1−θ}`, then `m` has a divisor `d` with `m^θ ≤ d ≤ m^{1/2}`. -/
theorem exists_divisor_of_subsum {m : ℕ} (hm : 2 ≤ m) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 3)
    (hp : ∀ p, p.Prime → p ∣ m → (p : ℝ) < (m : ℝ) ^ (1 - θ)) :
    ∃ d, d ∣ m ∧ (m : ℝ) ^ θ ≤ d ∧ (d : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) := by
  classical
  set L := m.primeFactorsList with hL
  have hm0 : m ≠ 0 := by omega
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0R : (0 : ℝ) < m := by linarith
  have hlogm : 0 < Real.log m := Real.log_pos hmR
  have hprime : ∀ i : Fin L.length, (L[i.1]).Prime := fun i =>
    Nat.prime_of_mem_primeFactorsList (List.getElem_mem _)
  have hdvd : ∀ i : Fin L.length, L[i.1] ∣ m := fun i =>
    Nat.dvd_of_mem_primeFactorsList (List.getElem_mem _)
  have hpos : ∀ i : Fin L.length, (0 : ℝ) < ((L[i.1] : ℕ) : ℝ) := fun i => by
    exact_mod_cast (hprime i).pos
  have hprod : ∏ i : Fin L.length, L[i.1] = m := by
    rw [Fin.prod_univ_getElem]
    exact Nat.prod_primeFactorsList hm0
  have hlogsum : ∀ s : Finset (Fin L.length),
      Real.log ((∏ i ∈ s, L[i.1] : ℕ) : ℝ) = ∑ i ∈ s, Real.log ((L[i.1] : ℕ) : ℝ) := fun s => by
    push_cast
    exact Real.log_prod fun i _ => (hpos i).ne'
  set x : Fin L.length → ℝ := fun i => Real.log ((L[i.1] : ℕ) : ℝ) / Real.log m with hx
  have hsum : ∑ i, x i = 1 := by
    simp only [hx]
    rw [← sum_div, ← hlogsum univ, hprod, div_self hlogm.ne']
  have hmax : ∀ i, x i < 1 - θ := fun i => by
    simp only [hx]
    rw [div_lt_iff₀ hlogm]
    have := Real.log_lt_log (hpos i) (hp _ (hprime i) (hdvd i))
    rwa [Real.log_rpow hm0R] at this
  obtain ⟨I, h1, h2⟩ := subsum x hsum hθ0 hθ hmax
  have hd0 : (0 : ℝ) < ((∏ i ∈ I, L[i.1] : ℕ) : ℝ) := by
    push_cast
    exact prod_pos fun i _ => hpos i
  have hsI : ∑ i ∈ I, x i = Real.log ((∏ i ∈ I, L[i.1] : ℕ) : ℝ) / Real.log m := by
    rw [hlogsum, sum_div]
  rw [hsI] at h1 h2
  rw [le_div_iff₀ hlogm] at h1
  rw [div_le_iff₀ hlogm] at h2
  refine ⟨∏ i ∈ I, L[i.1], ?_, ?_, ?_⟩
  · calc ∏ i ∈ I, L[i.1] ∣ ∏ i : Fin L.length, L[i.1] :=
          prod_dvd_prod_of_subset I univ _ (subset_univ I)
      _ = m := hprod
  · rw [Real.rpow_def_of_pos hm0R, ← Real.exp_log hd0]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [Real.rpow_def_of_pos hm0R, ← Real.exp_log hd0]
    exact Real.exp_le_exp.mpr (by linarith)

/-- **Remark 7.2, second aside.** If `log(K + 1)/log N → θ < 1/3`, then all but `o(N)` elements
of `F₁` have a divisor in `(K, √N]`. -/
theorem remark_7_2_small {θ : ℝ} (hθ : θ < 1 / 3) {K : ℕ → ℕ}
    (hK : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => (((smoothFibre N (K N)).filter
      fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N)).card : ℝ) / N) atTop (𝓝 0) := by
  -- `θ ≥ 0`, as a limit of nonnegative numbers.
  have hθ0 : 0 ≤ θ := by
    refine ge_of_tendsto hK (Eventually.of_forall fun N =>
      div_nonneg ?_ (Real.log_natCast_nonneg N))
    exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (K N)])
  rw [tendsto_order]
  refine ⟨fun c hc => Eventually.of_forall fun N => lt_of_lt_of_le hc (by positivity), ?_⟩
  intro c hc
  -- Parameters.
  set ε := min (min (2 * (1 / 3 - θ)) (1 / 3)) (c / 40) with hεdef
  have hε0 : 0 < ε := lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  have hε1 : ε ≤ 2 * (1 / 3 - θ) := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 3 := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ c / 40 := min_le_right _ _
  set θ' := θ + ε / 2 with hθ'
  set η := ε / 8 with hη
  set a := (1 - η) * (1 - θ - ε) with ha
  set b := 1 - θ + ε with hb
  have hθ'0 : 0 < θ' := by linarith
  have hθ'1 : θ' ≤ 1 / 3 := by linarith
  have ha0 : 3 / 10 ≤ a := by
    have h1 : 1 / 3 ≤ 1 - θ - ε := by linarith
    have h2 : 23 / 24 ≤ 1 - η := by linarith
    nlinarith
  have hab : a ≤ b := by nlinarith
  have hba : (b - a) / a ≤ c / 4 := by
    rw [div_le_iff₀ (by linarith)]
    have : b - a ≤ 3 * ε := by nlinarith
    nlinarith
  have hkey : θ + ε / 4 < (1 - η) * θ' := by nlinarith
  have hexp_lt : a < (1 - η) * (1 - θ') := by nlinarith
  -- The eventual conditions.
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hK.eventually (gt_mem_nhds (show θ < θ + ε / 4 by linarith)),
    hK.eventually (lt_mem_nhds (show θ - ε < θ by linarith)), eventually_ge_atTop 2,
    hN.eventually ((tendsto_rpow_atTop (show (0 : ℝ) < η by positivity)).eventually_ge_atTop
      (4 / c)),
    hN.eventually ((tendsto_rpow_atTop (show (0 : ℝ) < a by linarith)).eventually_ge_atTop 2),
    hN.eventually ((tendsto_rpow_atTop (show (0 : ℝ) < 1 - η by linarith)).eventually_ge_atTop 2),
    tendsto_log_nat.eventually_ge_atTop (72 / (a * c))] with N hup hlo hN2 hNη hNa hN1η hlogN
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) < N := by linarith
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hK0 : (0 : ℝ) < (K N : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hL] at hup
  rw [lt_div_iff₀ hL] at hlo
  -- `K + 1 ≤ N^{θ+ε/4}` and `N^{θ−ε} ≤ K + 1`.
  have hKup : (K N : ℝ) + 1 < (N : ℝ) ^ (θ + ε / 4) := by
    rw [← Real.log_lt_log_iff hK0 (by positivity), Real.log_rpow hN0]; linarith
  have hKlo : (N : ℝ) ^ (θ - ε) < (K N : ℝ) + 1 := by
    rw [← Real.log_lt_log_iff (by positivity) hK0, Real.log_rpow hN0]; linarith
  -- `B ≤ N^b`.
  have hB : ((N / (K N + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ b := by
    have h1 : ((N / (K N + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((K N : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := K N + 1)
      push_cast at this
      exact this
    have h2 : (N : ℝ) / ((K N : ℝ) + 1) ≤ (N : ℝ) / (N : ℝ) ^ (θ - ε) :=
      div_le_div_of_nonneg_left hN0.le (by positivity) hKlo.le
    have h3 : (N : ℝ) / (N : ℝ) ^ (θ - ε) = (N : ℝ) ^ b := by
      rw [div_eq_iff (by positivity), ← Real.rpow_add hN0, hb,
        show 1 - θ + ε + (θ - ε) = (1 : ℝ) by ring, Real.rpow_one]
    linarith
  -- The window of primes.
  set W := primesIn ((N : ℝ) ^ a) ((N : ℝ) ^ b) with hW
  -- Every exceptional `m ≥ N^{1−η}` has a prime factor in the window.
  have hexc : ∀ m ∈ (smoothFibre N (K N)).filter
      (fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N)),
      (m : ℝ) < (N : ℝ) ^ (1 - η) ∨ ∃ p ∈ W, p ∣ m := by
    intro m hm
    obtain ⟨hmF, hmd⟩ := mem_filter.mp hm
    obtain ⟨hmI, hmS⟩ := mem_filter.mp hmF
    obtain ⟨hKm, hmN⟩ := mem_Ioc.mp hmI
    by_contra hcon
    push Not at hcon
    obtain ⟨hmbig, hnoW⟩ := hcon
    have hm2 : 2 ≤ m := by
      have : (2 : ℝ) ≤ m := hN1η.trans hmbig
      exact_mod_cast this
    have hmR : (0 : ℝ) < m := by linarith [hN1η.trans hmbig]
    -- Every prime factor is `< m^{1−θ'}`.
    have hp : ∀ p, p.Prime → p ∣ m → (p : ℝ) < (m : ℝ) ^ (1 - θ') := by
      intro p hpp hpm
      by_contra hge
      push Not at hge
      have hpB : (p : ℝ) ≤ (N : ℝ) ^ b := by
        have h := Nat.mem_smoothNumbers'.mp hmS p hpp hpm
        have : p ≤ N / (K N + 1) := by omega
        exact (by exact_mod_cast this : (p : ℝ) ≤ ((N / (K N + 1) : ℕ) : ℝ)).trans hB
      have hpa : (N : ℝ) ^ a < p := by
        have h1 : (N : ℝ) ^ a < (N : ℝ) ^ ((1 - η) * (1 - θ')) :=
          Real.rpow_lt_rpow_of_exponent_lt hN1 hexp_lt
        have h2 : (N : ℝ) ^ ((1 - η) * (1 - θ')) ≤ (m : ℝ) ^ (1 - θ') := by
          rw [Real.rpow_mul hN0.le]
          exact Real.rpow_le_rpow (by positivity) hmbig (by linarith)
        linarith
      exact hnoW p ((mem_primesIn (by positivity)).mpr ⟨hpp, hpa, hpB⟩) hpm
    obtain ⟨d, hdm, hd1, hd2⟩ := exists_divisor_of_subsum hm2 hθ'0 hθ'1 hp
    refine hmd d (Nat.mem_divisors.mpr ⟨hdm, by omega⟩) ⟨?_, ?_⟩
    · -- `d ≥ m^{θ'} ≥ N^{(1−η)θ'} > N^{θ+ε/4} > K + 1`.
      have h1 : (N : ℝ) ^ ((1 - η) * θ') ≤ (m : ℝ) ^ θ' := by
        rw [Real.rpow_mul hN0.le]
        exact Real.rpow_le_rpow (by positivity) hmbig hθ'0.le
      have h2 : (N : ℝ) ^ (θ + ε / 4) < (N : ℝ) ^ ((1 - η) * θ') :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 hkey
      have : (K N : ℝ) < d := by linarith
      exact_mod_cast this
    · -- `d² ≤ m ≤ N`.
      have hmm : (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) = m := by
        rw [← Real.rpow_add hmR]; norm_num
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have h1 : (d : ℝ) * d ≤ m := by
        calc (d : ℝ) * d ≤ (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) :=
              mul_le_mul hd2 hd2 hd0 (by positivity)
          _ = m := hmm
      have : ((d * d : ℕ) : ℝ) ≤ N := by
        push_cast
        exact h1.trans (by exact_mod_cast hmN)
      exact_mod_cast this
  -- Count.
  have hsub : (smoothFibre N (K N)).filter (fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N)) ⊆
      (Icc 1 ⌊(N : ℝ) ^ (1 - η)⌋₊) ∪ W.biUnion (fun p => (Ioc 0 N).filter (p ∣ ·)) := by
    intro m hm
    have hm1 : 1 ≤ m := by
      obtain ⟨hmF, -⟩ := mem_filter.mp hm
      have := (mem_Ioc.mp (mem_filter.mp hmF).1).1
      omega
    have hmN : m ≤ N := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hm).1).1).2
    rcases hexc m hm with h | ⟨p, hpW, hpm⟩
    · exact mem_union_left _ (mem_Icc.mpr ⟨hm1, Nat.le_floor h.le⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p, hpW, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,
        hmN⟩, hpm⟩⟩)
  have hcard := card_le_card hsub
  have hc1 : ((Icc 1 ⌊(N : ℝ) ^ (1 - η)⌋₊).card : ℝ) ≤ (N : ℝ) ^ (1 - η) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le (by positivity)
  have hc2 : ((W.biUnion (fun p => (Ioc 0 N).filter (p ∣ ·))).card : ℝ) ≤
      N * ∑ p ∈ W, (1 : ℝ) / p := by
    have h := card_biUnion_le (s := W) (t := fun p => (Ioc 0 N).filter (p ∣ ·))
    have h' : (((W.biUnion (fun p => (Ioc 0 N).filter (p ∣ ·))).card : ℕ) : ℝ) ≤
        ∑ p ∈ W, (((Ioc 0 N).filter (p ∣ ·)).card : ℝ) := by exact_mod_cast h
    refine h'.trans ?_
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
    rw [mul_one_div]
    exact this
  -- Lemma 2.1(b) on the window.
  have hmert := mertens_b hNa (Real.rpow_le_rpow_of_exponent_le hN1.le hab)
  rw [Real.log_rpow hN0, Real.log_rpow hN0, mul_div_mul_right _ _ hL.ne'] at hmert
  have hWsum : ∑ p ∈ W, (1 : ℝ) / p ≤ (b - a) / a + c / 4 := by
    have h1 := (abs_le.mp hmert).2
    have h2 : Real.log (b / a) ≤ (b - a) / a := by
      have := Real.log_le_sub_one_of_pos (show 0 < b / a by apply div_pos <;> linarith)
      rwa [div_sub_one (by linarith)] at this
    have h3 : 18 / (a * Real.log N) ≤ c / 4 := by
      have ha' : 0 < a := by linarith
      rw [div_le_iff₀ (mul_pos ha' hL)]
      rw [div_le_iff₀ (mul_pos ha' hc)] at hlogN
      linarith
    have : ∑ p ∈ W, (1 : ℝ) / p = ∑ p ∈ (primesUpTo ⌊(N : ℝ) ^ b⌋₊).filter
        (fun p : ℕ => (N : ℝ) ^ a < p), (1 : ℝ) / p := rfl
    linarith
  have hNη' : (N : ℝ) ^ (1 - η) ≤ c / 4 * N := by
    rw [Real.rpow_sub hN0, Real.rpow_one, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hc] at hNη
    have := mul_le_mul_of_nonneg_left hNη hN0.le
    linarith
  have hW0 : 0 ≤ ∑ p ∈ W, (1 : ℝ) / p := sum_nonneg fun p _ => by positivity
  have hcardR : (((smoothFibre N (K N)).filter
      (fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N))).card : ℝ) ≤
      (N : ℝ) ^ (1 - η) + N * ∑ p ∈ W, (1 : ℝ) / p := by
    have h := (card_union_le (Icc 1 ⌊(N : ℝ) ^ (1 - η)⌋₊)
      (W.biUnion (fun p => (Ioc 0 N).filter (p ∣ ·))))
    have h' : (((smoothFibre N (K N)).filter
        (fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N))).card : ℝ) ≤
        ((Icc 1 ⌊(N : ℝ) ^ (1 - η)⌋₊).card : ℝ) +
          ((W.biUnion (fun p => (Ioc 0 N).filter (p ∣ ·))).card : ℝ) := by
      exact_mod_cast hcard.trans h
    linarith
  rw [div_lt_iff₀ hN0]
  have h1 := mul_le_mul_of_nonneg_left hWsum hN0.le
  have h2 := mul_le_mul_of_nonneg_left hba hN0.le
  have h3 := mul_pos hc hN0
  linarith

end HubRemoval
