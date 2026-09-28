import Mathlib

/-!
# Dickman's function (paper, Lemma 2.2, first part)

**Lemma 2.2 (first part).** There is a unique continuous `ρ : [0, ∞) → ℝ` with `ρ(u) = 1` for
`0 ≤ u ≤ 1` and `u ρ'(u) = −ρ(u − 1)` for `u > 1`. It takes values in `(0, 1]`, satisfies
`ρ(u) = 1 − log u` for `1 ≤ u ≤ 2`, and is strictly decreasing on `[1, ∞)`.

The construction is by recursion on the intervals `[n, n + 1]`. `dickAux n` is correct on
`(−∞, n + 1]`:
`dickAux (n+1) u = dickAux n (min u (n+1)) − ∫_{n+1}^{max u (n+1)} dickAux n (w − 1)/max w 1 dw`.
`dickman u = dickAux ⌈u⌉ u`. The main identity is the integral equation
`ρ(u) = 1 − ∫_1^u ρ(w − 1)/w dw` for `u ≥ 1` (`dickman_integral`). From it come the
derivative (`dickman_hasDerivAt`), the formula on `[1, 2]`, and the integrated form
`u ρ(u) = ∫_{u−1}^u ρ` (`mul_dickman_eq_integral`). The integrated form gives positivity: at a
first zero `u₀`, `u₀ ρ(u₀) = ∫_{u₀−1}^{u₀} ρ > 0`.
-/

namespace HubRemoval

open Set Filter Topology intervalIntegral

/-- The recursion defining Dickman's function; `dickAux n` is correct on `(−∞, n + 1]`. -/
noncomputable def dickAux : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => dickAux n (min u ((n : ℝ) + 1)) -
      ∫ w in ((n : ℝ) + 1)..(max u ((n : ℝ) + 1)), dickAux n (w - 1) / max w 1

/-- **Dickman's function** `ρ`. -/
noncomputable def dickman (u : ℝ) : ℝ := dickAux ⌈u⌉₊ u

theorem dickAux_continuous : ∀ n, Continuous (dickAux n)
  | 0 => continuous_const
  | n + 1 => by
    have hc := dickAux_continuous n
    have hint : Continuous fun w : ℝ => dickAux n (w - 1) / max w 1 :=
      (hc.comp (continuous_id.sub continuous_const)).div
        (continuous_id.max continuous_const) fun w => by positivity
    have hprim := intervalIntegral.continuous_primitive (μ := MeasureTheory.volume)
      (fun a b => hint.intervalIntegrable a b) ((n : ℝ) + 1)
    exact (hc.comp (continuous_id.min continuous_const)).sub
      (hprim.comp (continuous_id.max continuous_const))

theorem dickAux_succ_of_le {n : ℕ} {u : ℝ} (hu : u ≤ n + 1) : dickAux (n + 1) u = dickAux n u := by
  show dickAux n (min u ((n : ℝ) + 1)) -
      ∫ w in ((n : ℝ) + 1)..(max u ((n : ℝ) + 1)), dickAux n (w - 1) / max w 1 = dickAux n u
  rw [min_eq_left hu, max_eq_right hu, integral_same, sub_zero]

theorem dickAux_stable {m n : ℕ} (hmn : m ≤ n) {u : ℝ} (hu : u ≤ m + 1) :
    dickAux n u = dickAux m u := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    rw [dickAux_succ_of_le (by linarith), ih]

/-- `ρ = dickAux n` on `(−∞, n + 1]`. -/
theorem dickman_eq_aux {n : ℕ} {u : ℝ} (hu : u ≤ n + 1) : dickman u = dickAux n u := by
  unfold dickman
  rcases le_or_gt ⌈u⌉₊ n with h | h
  · exact (dickAux_stable h (by linarith [Nat.le_ceil u])).symm
  · have hc : ⌈u⌉₊ ≤ n + 1 := Nat.ceil_le.mpr (by push_cast; linarith)
    have hceq : ⌈u⌉₊ = n + 1 := by omega
    rw [hceq]
    exact dickAux_succ_of_le hu

/-- `ρ(u) = 1` for `u ≤ 1`. -/
theorem dickman_eq_one {u : ℝ} (hu : u ≤ 1) : dickman u = 1 := by
  rw [dickman_eq_aux (n := 0) (by simpa using hu)]
  rfl

/-- `ρ` is continuous. -/
theorem dickman_continuous : Continuous dickman := by
  rw [continuous_iff_continuousAt]
  intro u
  set n := ⌈u⌉₊ + 1
  have hun : u < n + 1 := by
    have := Nat.le_ceil u
    simp only [n]
    push_cast
    linarith
  refine ((dickAux_continuous n).continuousAt).congr ?_
  filter_upwards [Iio_mem_nhds hun] with v hv
  exact (dickman_eq_aux (le_of_lt hv)).symm

/-- The integrand `w ↦ ρ(w − 1)/w`, made continuous everywhere by using `max w 1`. -/
noncomputable def dickInt (w : ℝ) : ℝ := dickman (w - 1) / max w 1

theorem dickInt_continuous : Continuous dickInt :=
  (dickman_continuous.comp (continuous_id.sub continuous_const)).div
    (continuous_id.max continuous_const) fun w => by positivity

theorem dickInt_eq {w : ℝ} (hw : 1 ≤ w) : dickInt w = dickman (w - 1) / w := by
  rw [dickInt, max_eq_left hw]

/-- The local step: for `n + 1 ≤ u ≤ n + 2`, `ρ(u) = ρ(n + 1) − ∫_{n+1}^u ρ(w − 1)/w dw`. -/
theorem dickman_local {n : ℕ} {u : ℝ} (h1 : (n : ℝ) + 1 ≤ u) (h2 : u ≤ n + 2) :
    dickman u = dickman ((n : ℝ) + 1) - ∫ w in ((n : ℝ) + 1)..u, dickInt w := by
  rw [dickman_eq_aux (n := n + 1) (by push_cast; linarith),
    dickman_eq_aux (n := n) (le_refl _)]
  show dickAux n (min u ((n : ℝ) + 1)) -
      ∫ w in ((n : ℝ) + 1)..(max u ((n : ℝ) + 1)), dickAux n (w - 1) / max w 1 = _
  rw [min_eq_right h1, max_eq_left h1]
  congr 1
  refine integral_congr fun w hw => ?_
  rw [uIcc_of_le h1] at hw
  simp only [dickInt]
  rw [dickman_eq_aux (n := n) (by linarith [hw.2])]

/-- **The integral equation.** `ρ(u) = 1 − ∫_1^u ρ(w − 1)/w dw` for `u ≥ 1`. -/
theorem dickman_integral' {u : ℝ} (hu : 1 ≤ u) : dickman u = 1 - ∫ w in (1 : ℝ)..u, dickInt w := by
  suffices H : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ n + 1 → dickman u = 1 - ∫ w in (1 : ℝ)..u, dickInt w
    from H ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])
  intro n
  induction n with
  | zero =>
    intro u h1 h2
    have : u = 1 := by push_cast at h2; linarith
    subst this
    rw [integral_same, sub_zero, dickman_eq_one le_rfl]
  | succ n ih =>
    intro u h1 h2
    rcases le_or_gt u ((n : ℝ) + 1) with h | h
    · exact ih u h1 h
    · push_cast at h2
      rw [dickman_local h.le (by linarith), ih _ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
        le_rfl, sub_sub, integral_add_adjacent_intervals
        (dickInt_continuous.intervalIntegrable _ _) (dickInt_continuous.intervalIntegrable _ _)]

/-- **The integral equation**, in the paper's form. -/
theorem dickman_integral {u : ℝ} (hu : 1 ≤ u) :
    dickman u = 1 - ∫ w in (1 : ℝ)..u, dickman (w - 1) / w := by
  rw [dickman_integral' hu]
  congr 1
  refine integral_congr fun w hw => ?_
  rw [uIcc_of_le hu] at hw
  exact dickInt_eq hw.1

/-- For `1 ≤ v ≤ u`, `ρ(u) = ρ(v) − ∫_v^u ρ(w − 1)/w dw`. -/
theorem dickman_sub {u v : ℝ} (hv : 1 ≤ v) (hvu : v ≤ u) :
    dickman u = dickman v - ∫ w in v..u, dickman (w - 1) / w := by
  have h1 := dickman_integral' (hv.trans hvu)
  have h2 := dickman_integral' hv
  have h3 : ∫ w in v..u, dickman (w - 1) / w = ∫ w in v..u, dickInt w := by
    refine integral_congr fun w hw => ?_
    rw [uIcc_of_le hvu] at hw
    exact (dickInt_eq (hv.trans hw.1)).symm
  rw [h3, h1, h2, ← integral_add_adjacent_intervals (b := v)
    (dickInt_continuous.intervalIntegrable _ _) (dickInt_continuous.intervalIntegrable _ _)]
  ring

/-- `ρ(u) = 1 − log u` for `1 ≤ u ≤ 2`. -/
theorem dickman_eq_one_sub_log {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2) :
    dickman u = 1 - Real.log u := by
  rw [dickman_integral h1]
  have : ∫ w in (1 : ℝ)..u, dickman (w - 1) / w = ∫ w in (1 : ℝ)..u, 1 / w := by
    refine integral_congr fun w hw => ?_
    rw [uIcc_of_le h1] at hw
    rw [dickman_eq_one (by linarith [hw.2])]
  rw [this, integral_one_div (by
    rw [uIcc_of_le h1]; intro h; linarith [h.1]), div_one]

/-- **The delay equation.** For `u > 1`, `ρ'(u) = −ρ(u − 1)/u`, i.e. `u ρ'(u) = −ρ(u − 1)`. -/
theorem dickman_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt dickman (-(dickman (u - 1) / u)) u := by
  have hF := (dickInt_continuous.integral_hasStrictDerivAt 1 u).hasDerivAt
  have h := (hasDerivAt_const u (1 : ℝ)).sub hF
  rw [zero_sub, dickInt_eq hu.le] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact dickman_integral' (le_of_lt hv)

/-- **The integrated form.** `u ρ(u) = ∫_{u−1}^u ρ` for `u ≥ 1`. -/
theorem mul_dickman_eq_integral {u : ℝ} (hu : 1 ≤ u) :
    u * dickman u = ∫ v in (u - 1)..u, dickman v := by
  set G : ℝ → ℝ := fun v => v * dickman v -
    ((∫ t in (0 : ℝ)..v, dickman t) - ∫ t in (0 : ℝ)..(v - 1), dickman t) with hG
  have hint : ∀ a b : ℝ, IntervalIntegrable dickman MeasureTheory.volume a b :=
    fun a b => dickman_continuous.intervalIntegrable a b
  have hGv : ∀ v, G v = v * dickman v - ∫ t in (v - 1)..v, dickman t := fun v => by
    simp only [hG]
    rw [← integral_interval_sub_left (hint 0 v) (hint 0 (v - 1))]
  suffices G u = G 1 by
    rw [hGv, hGv] at this
    have h0 : ∫ t in (1 - 1 : ℝ)..1, dickman t = 1 := by
      rw [show (1 - 1 : ℝ) = 0 by ring]
      rw [integral_congr (g := fun _ => (1 : ℝ)) fun t ht => by
        rw [uIcc_of_le zero_le_one] at ht; exact dickman_eq_one ht.2]
      simp
    rw [h0, dickman_eq_one le_rfl] at this
    linarith
  rcases eq_or_lt_of_le hu with rfl | hu'
  · rfl
  have hcont : Continuous G := by
    simp only [hG]
    exact (continuous_id.mul dickman_continuous).sub
      ((intervalIntegral.continuous_primitive hint 0).sub
        ((intervalIntegral.continuous_primitive hint 0).comp (continuous_id.sub continuous_const)))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G (fun _ => 0) hu'
    hcont.continuousOn fun x hx => by
      have hx1 : 1 < x := hx.1
      have hx0 : x ≠ 0 := by linarith
      have h1 := (hasDerivAt_id x).mul (dickman_hasDerivAt hx1)
      have h2 := (dickman_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
      have h3 := ((dickman_continuous.integral_hasStrictDerivAt 0 (x - 1)).hasDerivAt).comp x
        ((hasDerivAt_id x).sub_const 1)
      have h := h1.sub (h2.sub h3)
      convert h using 1
      · funext v
        simp only [hG, Pi.sub_apply, Pi.mul_apply, id_eq, Function.comp_apply]
      · simp only [id_eq]
        rw [mul_neg, mul_div_cancel₀ _ hx0]
        ring
  have hne : u - 1 ≠ 0 := by linarith
  have := hslope.symm
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · exact absurd h hne

/-- **Positivity.** `ρ(u) > 0` for all `u`. -/
theorem dickman_pos (u : ℝ) : 0 < dickman u := by
  by_contra hneg
  push Not at hneg
  set S := {v : ℝ | dickman v ≤ 0}
  have hne : S.Nonempty := ⟨u, hneg⟩
  have hbdd : BddBelow S := ⟨1, fun v hv => by
    by_contra h
    push Not at h
    have := dickman_eq_one h.le
    have hv' : dickman v ≤ 0 := hv
    linarith⟩
  have hclosed : IsClosed S := isClosed_le dickman_continuous continuous_const
  set u₀ := sInf S
  have hu₀ : dickman u₀ ≤ 0 := hclosed.csInf_mem hne hbdd
  have hu₀1 : 1 < u₀ := by
    by_contra h
    push Not at h
    have := dickman_eq_one h
    linarith
  have hbelow : ∀ v < u₀, 0 < dickman v := fun v hv => by
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h) (not_le.mpr hv)
  have hint := mul_dickman_eq_integral hu₀1.le
  have hpos : 0 < ∫ v in (u₀ - 1)..u₀, dickman v :=
    intervalIntegral_pos_of_pos_on (dickman_continuous.intervalIntegrable _ _)
      (fun v hv => hbelow v hv.2) (by linarith)
  nlinarith

/-- **Strictly decreasing on `[1, ∞)`.** -/
theorem dickman_strictAntiOn : StrictAntiOn dickman (Ici 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 1) dickman_continuous.continuousOn fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(dickman_hasDerivAt hx).deriv]
  have := dickman_pos (x - 1)
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  have : 0 < dickman (x - 1) / x := div_pos this hx0
  linarith

/-- `ρ` is non-increasing on `ℝ`. -/
theorem dickman_antitone : Antitone dickman := by
  intro u v huv
  rcases le_or_gt v 1 with hv | hv
  · rw [dickman_eq_one hv, dickman_eq_one (huv.trans hv)]
  rcases le_or_gt u 1 with hu | hu
  · rw [dickman_eq_one hu, ← dickman_eq_one (le_refl (1 : ℝ))]
    exact (dickman_strictAntiOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv).le
  · exact dickman_strictAntiOn.antitoneOn (mem_Ici.mpr hu.le) (mem_Ici.mpr hv.le) huv

/-- `ρ ≤ 1`. -/
theorem dickman_le_one (u : ℝ) : dickman u ≤ 1 := by
  rcases le_or_gt u 1 with h | h
  · rw [dickman_eq_one h]
  · rw [← dickman_eq_one (le_refl (1 : ℝ))]
    exact dickman_antitone h.le

/-- **Uniqueness.** A function continuous on `[0, ∞)`, equal to `1` on `[0, 1]`, with
`g'(u) = −g(u − 1)/u` for `u > 1`, is `ρ` on `[0, ∞)`. -/
theorem dickman_unique {g : ℝ → ℝ} (hcont : ContinuousOn g (Ici 0))
    (h01 : ∀ u ∈ Icc (0 : ℝ) 1, g u = 1)
    (hderiv : ∀ u : ℝ, 1 < u → HasDerivAt g (-(g (u - 1) / u)) u) :
    ∀ u : ℝ, 0 ≤ u → g u = dickman u := by
  suffices H : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u → u ≤ n + 1 → g u = dickman u from
    fun u hu => H ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])
  intro n
  induction n with
  | zero =>
    intro u h0 h1
    push_cast at h1
    rw [h01 u ⟨h0, by linarith⟩, dickman_eq_one (by linarith)]
  | succ n ih =>
    intro u h0 h1
    rcases le_or_gt u ((n : ℝ) + 1) with h | h
    · exact ih u h0 h
    · -- On `[n + 1, u]`, `g − ρ` has zero derivative.
      have hn1 : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun v => g v - dickman v)
        (fun _ => 0) h
        ((hcont.mono fun v hv => by simp only [mem_Ici]; linarith [hv.1]).sub
          dickman_continuous.continuousOn)
        fun x hx => by
          have hx1 : 1 < x := by linarith [hx.1]
          have hd := (hderiv x hx1).sub (dickman_hasDerivAt hx1)
          have heq : g (x - 1) = dickman (x - 1) :=
            ih (x - 1) (by linarith [hx.1]) (by push_cast at h1; linarith [hx.2])
          rw [heq, sub_self] at hd
          exact hd
      have hval := ih ((n : ℝ) + 1) (by linarith) le_rfl
      have hne : u - ((n : ℝ) + 1) ≠ 0 := by linarith
      have := hslope.symm
      rw [div_eq_zero_iff] at this
      rcases this with h' | h'
      · linarith
      · exact absurd h' hne

end HubRemoval
