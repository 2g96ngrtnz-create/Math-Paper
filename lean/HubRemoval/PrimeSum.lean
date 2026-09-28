import HubRemoval.Buchstab

/-!
# Prime sums as Riemann sums

For `x > 1` and `0 < s ≤ t`, `primesBetween x s t` is the set of primes `x^{1/t} < p ≤ x^{1/s}`.
For such `p`, `w_p := log x / log p ∈ [s, t)`.

**Prime-sum lemma** (`primeSum_integral`). Let `0 < a ≤ b`. Let `g` be continuous and
non-increasing on `[a, b]` with `0 ≤ g ≤ G`. Then, uniformly in `u ∈ [a, b]`,
`∑_{x^{1/u} < p ≤ x^{1/a}} g(w_p)/p → ∫_a^u g(w)/w dw` as `x → ∞`.

*Proof.* Split `[a, u]` into `m` equal steps `[s, t]`. On a step, `g(t) ≤ g(w_p) ≤ g(s)`, and
Lemma 2.1(b) gives `∑_{x^{1/t}<p≤x^{1/s}} 1/p = log(t/s) + O(b/log x)`. This brackets the
prime sum and the integral in the same interval, so they differ by at most
`(g(s) − g(t))(t − s)/a + G·18b/log x` (`step_bound`). Summing over the steps, the first terms
telescope to at most `G(b − a)/(ma)`, and the second give `m·G·18b/log x`. Fix `m` large, then
let `x → ∞`.
-/

namespace HubRemoval

open Finset Filter Topology intervalIntegral

/-- The primes `x^{1/t} < p ≤ x^{1/s}`. -/
noncomputable def primesBetween (x s t : ℝ) : Finset ℕ :=
  (primesUpTo ⌊x ^ (1 / s)⌋₊).filter (fun p : ℕ => x ^ (1 / t) < p)

theorem mem_primesBetween {x s t : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesBetween x s t ↔ p.Prime ∧ (p : ℝ) ≤ x ^ (1 / s) ∧ x ^ (1 / t) < p := by
  unfold primesBetween
  rw [mem_filter, mem_primesUpTo, Nat.le_floor_iff (Real.rpow_nonneg hx _), and_assoc]

theorem primesBetween_self {x s : ℝ} (hx : 0 ≤ x) : primesBetween x s s = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun p hp => by
    obtain ⟨-, h1, h2⟩ := (mem_primesBetween hx).mp hp
    linarith

/-- For `p ∈ primesBetween x s t`, `s ≤ log x / log p < t`. -/
theorem log_div_log_mem {x s t : ℝ} (hx : 1 < x) (hs : 0 < s) (hst : s ≤ t) {p : ℕ}
    (hp : p ∈ primesBetween x s t) :
    s ≤ Real.log x / Real.log p ∧ Real.log x / Real.log p < t := by
  obtain ⟨hpp, h1, h2⟩ := (mem_primesBetween (by linarith)).mp hp
  have hx0 : 0 < x := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
  have ht : 0 < t := hs.trans_le hst
  have l1 : Real.log p ≤ 1 / s * Real.log x := by
    rw [← Real.log_rpow hx0]
    exact Real.log_le_log hp0 h1
  have l2 : 1 / t * Real.log x < Real.log p := by
    rw [← Real.log_rpow hx0]
    exact Real.log_lt_log (Real.rpow_pos_of_pos hx0 _) h2
  constructor
  · rw [le_div_iff₀ hlp]
    have := mul_le_mul_of_nonneg_left l1 hs.le
    rwa [← mul_assoc, mul_one_div_cancel hs.ne', one_mul] at this
  · rw [div_lt_iff₀ hlp]
    have := mul_lt_mul_of_pos_left l2 ht
    rwa [← mul_assoc, mul_one_div_cancel ht.ne', one_mul] at this

/-- **Lemma 2.1(b) on `primesBetween`.** For `0 < s ≤ t` and `x^{1/t} ≥ 2`,
`|∑_{x^{1/t}<p≤x^{1/s}} 1/p − log(t/s)| ≤ 18t/log x`. -/
theorem sum_primesBetween_inv {x s t : ℝ} (hx : 1 < x) (hs : 0 < s) (hst : s ≤ t)
    (h2 : 2 ≤ x ^ (1 / t)) :
    |∑ p ∈ primesBetween x s t, (1 : ℝ) / p - Real.log (t / s)| ≤ 18 * t / Real.log x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have ht : 0 < t := hs.trans_le hst
  have hle : x ^ (1 / t) ≤ x ^ (1 / s) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (one_div_le_one_div_of_le hs hst)
  have h := mertens_b h2 hle
  rw [Real.log_rpow (by linarith), Real.log_rpow (by linarith)] at h
  have e1 : 1 / s * Real.log x / (1 / t * Real.log x) = t / s := by
    field_simp
  have e2 : 18 / (1 / t * Real.log x) = 18 * t / Real.log x := by
    field_simp
  rw [e1, e2] at h
  exact h

/-- Splitting `(x^{1/t}, x^{1/a}]` at `x^{1/s}`. -/
theorem sum_primesBetween_split {x a s t : ℝ} (hx : 1 ≤ x) (ha : 0 < a) (has : a ≤ s)
    (hst : s ≤ t) (f : ℕ → ℝ) :
    ∑ p ∈ primesBetween x a t, f p =
      ∑ p ∈ primesBetween x a s, f p + ∑ p ∈ primesBetween x s t, f p := by
  have hs : 0 < s := ha.trans_le has
  have h1 : x ^ (1 / t) ≤ x ^ (1 / s) :=
    Real.rpow_le_rpow_of_exponent_le hx (one_div_le_one_div_of_le hs hst)
  have h2 : x ^ (1 / s) ≤ x ^ (1 / a) :=
    Real.rpow_le_rpow_of_exponent_le hx (one_div_le_one_div_of_le ha has)
  have hx0 : 0 ≤ x := by linarith
  rw [← sum_filter_add_sum_filter_not (primesBetween x a t) (fun p : ℕ => x ^ (1 / s) < p)]
  congr 1
  · refine sum_congr ?_ fun _ _ => rfl
    ext p
    rw [mem_filter, mem_primesBetween hx0, mem_primesBetween hx0]
    constructor
    · rintro ⟨⟨hp, hpa, -⟩, hps⟩
      exact ⟨hp, hpa, hps⟩
    · rintro ⟨hp, hpa, hps⟩
      exact ⟨⟨hp, hpa, h1.trans_lt hps⟩, hps⟩
  · refine sum_congr ?_ fun _ _ => rfl
    ext p
    rw [mem_filter, mem_primesBetween hx0, mem_primesBetween hx0, not_lt]
    constructor
    · rintro ⟨⟨hp, -, hpt⟩, hps⟩
      exact ⟨hp, hps, hpt⟩
    · rintro ⟨hp, hps, hpt⟩
      exact ⟨⟨hp, hps.trans h2, hpt⟩, hps⟩

/-- `w ↦ g(w)/w` is interval integrable between points of `[a, b]`, for `a > 0`. -/
theorem intervalIntegrable_div_id {a b s t : ℝ} {g : ℝ → ℝ} (ha : 0 < a)
    (hgc : ContinuousOn g (Set.Icc a b)) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    IntervalIntegrable (fun w => g w / w) MeasureTheory.volume s t := by
  refine ContinuousOn.intervalIntegrable ((hgc.div continuousOn_id fun w hw => ?_).mono
    (Set.uIcc_subset_Icc hs ht))
  exact (ha.trans_le hw.1).ne'

/-- **One step.** For `a ≤ s ≤ t ≤ b`, the prime sum over `(x^{1/t}, x^{1/s}]` and the integral
over `[s, t]` differ by at most `(g(s) − g(t))(t − s)/a + G·18b/log x`. -/
theorem step_bound {x a b s t G : ℝ} {g : ℝ → ℝ} (ha : 0 < a) (hx : 1 < x)
    (hb2 : 2 ≤ x ^ (1 / b)) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hg : AntitoneOn g (Set.Icc a b)) (hg0 : ∀ w ∈ Set.Icc a b, 0 ≤ g w)
    (hgG : ∀ w ∈ Set.Icc a b, g w ≤ G) (hgc : ContinuousOn g (Set.Icc a b)) :
    |∑ p ∈ primesBetween x s t, g (Real.log x / Real.log p) / p - ∫ w in s..t, g w / w| ≤
      (g s - g t) * ((t - s) / a) + G * (18 * b / Real.log x) := by
  have hs : 0 < s := ha.trans_le has
  have ht : 0 < t := hs.trans_le hst
  have hL : 0 < Real.log x := Real.log_pos hx
  have hsm : s ∈ Set.Icc a b := ⟨has, hst.trans htb⟩
  have htm : t ∈ Set.Icc a b := ⟨has.trans hst, htb⟩
  have ht2 : 2 ≤ x ^ (1 / t) :=
    hb2.trans (Real.rpow_le_rpow_of_exponent_le hx.le (one_div_le_one_div_of_le ht htb))
  set A := ∑ p ∈ primesBetween x s t, (1 : ℝ) / p with hAdef
  set S := ∑ p ∈ primesBetween x s t, g (Real.log x / Real.log p) / p with hSdef
  set I := ∫ w in s..t, g w / w with hIdef
  set ℓ := Real.log (t / s) with hℓdef
  set η' := 18 * t / Real.log x with hη'def
  set η := 18 * b / Real.log x with hηdef
  have hA := abs_le.mp (sum_primesBetween_inv hx hs hst ht2)
  have hη' : η' ≤ η := div_le_div_of_nonneg_right (by linarith) hL.le
  have hη'0 : 0 ≤ η' := by positivity
  have hgts : g t ≤ g s := hg hsm htm hst
  have hgt0 : 0 ≤ g t := hg0 t htm
  have hgsG : g s ≤ G := hgG s hsm
  have hG : 0 ≤ G := hgt0.trans (hgts.trans hgsG)
  -- The prime sum is bracketed by `g(t) A` and `g(s) A`.
  have hwp : ∀ p ∈ primesBetween x s t, Real.log x / Real.log p ∈ Set.Icc a b ∧
      Real.log x / Real.log p ≤ t ∧ s ≤ Real.log x / Real.log p := fun p hp => by
    obtain ⟨h1, h2⟩ := log_div_log_mem hx hs hst hp
    exact ⟨⟨has.trans h1, h2.le.trans htb⟩, h2.le, h1⟩
  have hS1 : g t * A ≤ S := by
    rw [hAdef, mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hw, hwt, -⟩ := hwp p hp
    rw [div_eq_mul_one_div (g _)]
    exact mul_le_mul_of_nonneg_right (hg hw htm hwt) (by positivity)
  have hS2 : S ≤ g s * A := by
    rw [hAdef, mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hw, -, hsw⟩ := hwp p hp
    rw [div_eq_mul_one_div (g _)]
    exact mul_le_mul_of_nonneg_right (hg hsm hw hsw) (by positivity)
  -- The integral is bracketed by `g(t) ℓ` and `g(s) ℓ`.
  have h0 : (0 : ℝ) ∉ Set.uIcc s t := by
    rw [Set.uIcc_of_le hst]
    intro h
    linarith [h.1]
  have hconst : ∀ c : ℝ, ∫ w in s..t, c / w = c * ℓ := fun c => by
    rw [integral_congr (g := fun w => c * (1 / w)) (fun w _ => div_eq_mul_one_div c w),
      integral_const_mul, integral_one_div h0]
  have hint := intervalIntegrable_div_id ha hgc hsm htm
  have hcint : ∀ c : ℝ, IntervalIntegrable (fun w => c / w) MeasureTheory.volume s t :=
    fun c => ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id
      fun w hw => by
        rw [Set.uIcc_of_le hst] at hw
        exact (hs.trans_le hw.1).ne')
  have hI1 : g t * ℓ ≤ I := by
    rw [← hconst]
    refine integral_mono_on hst (hcint _) hint fun w hw => ?_
    exact div_le_div_of_nonneg_right (hg ⟨has.trans hw.1, hw.2.trans htb⟩ htm hw.2)
      (hs.trans_le hw.1).le
  have hI2 : I ≤ g s * ℓ := by
    rw [← hconst]
    refine integral_mono_on hst hint (hcint _) fun w hw => ?_
    exact div_le_div_of_nonneg_right (hg hsm ⟨has.trans hw.1, hw.2.trans htb⟩ hw.1)
      (hs.trans_le hw.1).le
  -- `0 ≤ ℓ ≤ (t − s)/a`.
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg ((one_le_div hs).mpr hst)
  have hℓ1 : ℓ ≤ (t - s) / a := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht hs)
    have h2 : t / s - 1 = (t - s) / s := by field_simp
    have h3 : (t - s) / s ≤ (t - s) / a := div_le_div_of_nonneg_left (by linarith) ha has
    linarith
  have p1 : g s * A ≤ g s * (ℓ + η') := mul_le_mul_of_nonneg_left (by linarith) (hgt0.trans hgts)
  have p2 : g t * (ℓ - η') ≤ g t * A := mul_le_mul_of_nonneg_left (by linarith) hgt0
  have p3 : g s * η' ≤ G * η := mul_le_mul hgsG hη' hη'0 hG
  have p4 : g t * η' ≤ G * η := mul_le_mul (hgts.trans hgsG) hη' hη'0 hG
  have p5 : (g s - g t) * ℓ ≤ (g s - g t) * ((t - s) / a) :=
    mul_le_mul_of_nonneg_left hℓ1 (by linarith)
  rw [abs_le]
  constructor <;> nlinarith

/-- **The prime-sum lemma.** For `0 < a ≤ b` and `g` continuous and non-increasing on `[a, b]`
with `0 ≤ g ≤ G`: for every `ε > 0`, eventually, for all `u ∈ [a, b]`,
`|∑_{x^{1/u} < p ≤ x^{1/a}} g(log x/log p)/p − ∫_a^u g(w)/w dw| ≤ ε`. -/
theorem primeSum_integral {a b G : ℝ} {g : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hg : AntitoneOn g (Set.Icc a b)) (hg0 : ∀ w ∈ Set.Icc a b, 0 ≤ g w)
    (hgG : ∀ w ∈ Set.Icc a b, g w ≤ G) (hgc : ContinuousOn g (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc a b,
      |∑ p ∈ primesBetween x a u, g (Real.log x / Real.log p) / p -
        ∫ w in a..u, g w / w| ≤ ε := by
  have hb : 0 < b := ha.trans_le hab
  have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hG : 0 ≤ G := (hg0 a hamem).trans (hgG a hamem)
  set m : ℕ := ⌈2 * G * (b - a) / (a * ε)⌉₊ + 1 with hm
  have hm_ge : 2 * G * (b - a) / (a * ε) + 1 ≤ m := by
    rw [hm]
    push_cast
    linarith [Nat.le_ceil (2 * G * (b - a) / (a * ε))]
  have hmpos : (0 : ℝ) < m := by
    have : 0 ≤ 2 * G * (b - a) / (a * ε) :=
      div_nonneg (by nlinarith) (by positivity)
    linarith
  have hm0 : m ≠ 0 := by positivity
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by positivity : 0 < 1 / b)).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (36 * b * m * G / ε)] with x hx hx2 hLx u hu
  have hL : 0 < Real.log x := Real.log_pos hx
  set F : ℝ → ℝ := fun t => ∑ p ∈ primesBetween x a t, g (Real.log x / Real.log p) / p
    with hFdef
  set I : ℝ → ℝ := fun t => ∫ w in a..t, g w / w with hIdef
  set E : ℝ → ℝ := fun t => F t - I t with hEdef
  set h := (u - a) / m with hhdef
  set tt : ℕ → ℝ := fun i => a + i * h with httdef
  have hh0 : 0 ≤ h := div_nonneg (by linarith [hu.1]) hmpos.le
  have hhb : h ≤ (b - a) / m := div_le_div_of_nonneg_right (by linarith [hu.2]) hmpos.le
  have htt_le : ∀ i ≤ m, tt i ≤ u := fun i hi => by
    have : (i : ℝ) * h ≤ m * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh0
    have e : (m : ℝ) * h = u - a := by rw [hhdef]; field_simp
    simp only [httdef]
    linarith
  have htt_ge : ∀ i, a ≤ tt i := fun i => by
    simp only [httdef]
    have : 0 ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg i) hh0
    linarith
  have htt_succ : ∀ i, tt (i + 1) - tt i = h := fun i => by
    simp only [httdef]
    push_cast
    ring
  have htt0 : tt 0 = a := by simp [httdef]
  have httm : tt m = u := by
    simp only [httdef, hhdef]
    field_simp
    ring
  have hE0 : E a = 0 := by
    simp [hEdef, hFdef, hIdef, primesBetween_self (by linarith : (0 : ℝ) ≤ x)]
  -- One step of the grid.
  have hstep : ∀ i < m, |E (tt (i + 1)) - E (tt i)| ≤
      (g (tt i) - g (tt (i + 1))) * (h / a) + G * (18 * b / Real.log x) := fun i hi => by
    have hs := htt_ge i
    have hst : tt i ≤ tt (i + 1) := by linarith [htt_succ i]
    have htb : tt (i + 1) ≤ b := (htt_le (i + 1) hi).trans hu.2
    have hsm : tt i ∈ Set.Icc a b := ⟨hs, hst.trans htb⟩
    have htm : tt (i + 1) ∈ Set.Icc a b := ⟨hs.trans hst, htb⟩
    have hF : F (tt (i + 1)) - F (tt i) =
        ∑ p ∈ primesBetween x (tt i) (tt (i + 1)), g (Real.log x / Real.log p) / p := by
      simp only [hFdef]
      rw [sum_primesBetween_split hx.le ha hs hst]
      ring
    have hI : I (tt (i + 1)) - I (tt i) = ∫ w in (tt i)..(tt (i + 1)), g w / w :=
      integral_interval_sub_left (intervalIntegrable_div_id ha hgc hamem htm)
        (intervalIntegrable_div_id ha hgc hamem hsm)
    have hEq : E (tt (i + 1)) - E (tt i) = (F (tt (i + 1)) - F (tt i)) -
        (I (tt (i + 1)) - I (tt i)) := by
      simp only [hEdef]
      ring
    rw [hEq, hF, hI, ← htt_succ i]
    exact step_bound ha hx hx2 hs hst htb hg hg0 hgG hgc
  -- Telescoping.
  have htel : E u = ∑ i ∈ range m, (E (tt (i + 1)) - E (tt i)) := by
    rw [sum_range_sub (fun i => E (tt i)) m, httm, htt0, hE0, sub_zero]
  have hgtel : ∑ i ∈ range m, ((g (tt i) - g (tt (i + 1))) * (h / a) +
      G * (18 * b / Real.log x)) = (g a - g u) * (h / a) + m * (G * (18 * b / Real.log x)) := by
    rw [sum_add_distrib, ← sum_mul, sum_range_sub' (fun i => g (tt i)) m, htt0, httm, sum_const,
      card_range, nsmul_eq_mul]
  have hbound : |E u| ≤ (g a - g u) * (h / a) + m * (G * (18 * b / Real.log x)) := by
    rw [htel, ← hgtel]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => hstep i (mem_range.mp hi))
  -- The two error terms are each at most `ε/2`.
  have humem : u ∈ Set.Icc a b := hu
  have hgau : 0 ≤ g a - g u := by linarith [hg hamem humem hu.1]
  have hgaG : g a - g u ≤ G := by linarith [hgG a hamem, hg0 u humem]
  have e1 : (g a - g u) * (h / a) ≤ G * ((b - a) / m / a) :=
    mul_le_mul hgaG (div_le_div_of_nonneg_right hhb ha.le) (div_nonneg hh0 ha.le) hG
  have e2 : G * ((b - a) / m / a) ≤ ε / 2 := by
    have h1 : 2 * G * (b - a) ≤ (m - 1) * (a * ε) := by
      have := (div_le_iff₀ (by positivity : 0 < a * ε)).mp (by linarith : 2 * G * (b - a) /
        (a * ε) ≤ m - 1)
      linarith
    have h2 : G * ((b - a) / m / a) = G * (b - a) / (m * a) := by field_simp
    rw [h2, div_le_iff₀ (by positivity)]
    nlinarith
  have e3 : (m : ℝ) * (G * (18 * b / Real.log x)) ≤ ε / 2 := by
    have h1 := (div_le_iff₀ hε).mp hLx
    have h2 : (m : ℝ) * (G * (18 * b / Real.log x)) = 18 * b * m * G / Real.log x := by ring
    rw [h2, div_le_iff₀ hL]
    linarith
  show |E u| ≤ ε
  linarith

end HubRemoval
