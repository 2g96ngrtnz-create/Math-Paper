import HubRemoval.DickmanThm
open HubRemoval Finset Filter Topology

/-! ### Lemma 2.2: axioms -/

-- Dickman's function
#print axioms dickAux_continuous
#print axioms dickman_eq_aux
#print axioms dickman_eq_one
#print axioms dickman_continuous
#print axioms dickman_integral
#print axioms dickman_sub
#print axioms dickman_eq_one_sub_log
#print axioms dickman_hasDerivAt
#print axioms mul_dickman_eq_integral
#print axioms dickman_pos
#print axioms dickman_strictAntiOn
#print axioms dickman_antitone
#print axioms dickman_le_one
#print axioms dickman_unique
-- Buchstab's identity
#print axioms psi_prime_step
#print axioms psi_nonprime_step
#print axioms buchstab
#print axioms psi_eq_self_of_le
#print axioms buchstab_real
-- Prime sums as Riemann sums
#print axioms mem_primesBetween
#print axioms log_div_log_mem
#print axioms sum_primesBetween_inv
#print axioms sum_primesBetween_split
#print axioms step_bound
#print axioms primeSum_integral
-- Dickman's theorem
#print axioms psi_mono_right
#print axioms div_rpow_log_div
#print axioms psi_dickman_base
#print axioms psi_dickman_step
#print axioms psi_dickman_nat
#print axioms dickman_asymptotic
#print axioms dickman_tendstoUniformlyOn
#print axioms tendsto_psi_dickman
#print axioms dickman_le_two_div
#print axioms dickman_tendsto_zero

/-! ### The characterisation of `ρ` -/

/-- `ρ` is the unique solution: the defining properties hold. -/
example : ContinuousOn dickman (Set.Ici 0) ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, dickman u = 1) ∧
    ∀ u : ℝ, 1 < u → HasDerivAt dickman (-(dickman (u - 1) / u)) u :=
  ⟨dickman_continuous.continuousOn, fun _ hu => dickman_eq_one hu.2,
    fun _ hu => dickman_hasDerivAt hu⟩

/-- Any other solution agrees with `ρ` on `[0, ∞)`. -/
example {g : ℝ → ℝ} (hc : ContinuousOn g (Set.Ici 0)) (h1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u = 1)
    (hd : ∀ u : ℝ, 1 < u → HasDerivAt g (-(g (u - 1) / u)) u) : g 3 = dickman 3 :=
  dickman_unique hc h1 hd 3 (by norm_num)

/-- `ρ(2) = 1 − log 2 ≈ 0.307`. -/
example : dickman 2 = 1 - Real.log 2 := dickman_eq_one_sub_log (by norm_num) (by norm_num)

/-- `0 < ρ(3) < ρ(2) ≤ 1`, and `ρ(3) ≤ 2/3`. -/
example : 0 < dickman 3 ∧ dickman 3 < dickman 2 ∧ dickman 2 ≤ 1 ∧ dickman 3 ≤ 2 / 3 :=
  ⟨dickman_pos 3, dickman_strictAntiOn (by norm_num : (2 : ℝ) ∈ Set.Ici 1)
    (by norm_num : (3 : ℝ) ∈ Set.Ici 1) (by norm_num), dickman_le_one 2,
    dickman_le_two_div (by norm_num)⟩

/-! ### Buchstab's identity, on numbers -/

/-- Buchstab from `y = 3` to `z = 10` at `X = 100`. -/
example : psi 100 10 = psi 100 3 +
    ∑ p ∈ (primesUpTo 10).filter (fun p => 3 < p), psi (100 / p) p :=
  buchstab 100 (by norm_num)

-- `Ψ(100, 10) = 46 = 20 + 14 + 12 = Ψ(100, 3) + Ψ(20, 5) + Ψ(14, 7)`.
#guard psi 100 10 = 46
#guard psi 100 3 = 20 ∧ psi 20 5 = 14 ∧ psi 14 7 = 12
#guard psi 30 5 = psi 30 3 + psi 6 5

/-! ### The theorem, applied -/

/-- With `u = 2`: `Ψ(x, √x)/x → 1 − log 2`. -/
example : Tendsto (fun x : ℝ => (PsiR x (x ^ (1 / (2 : ℝ))) : ℝ) / x) atTop
    (𝓝 (1 - Real.log 2)) := by
  rw [← dickman_eq_one_sub_log (by norm_num) (by norm_num)]
  exact tendsto_psi_dickman (by norm_num)

/-- Uniformly on `[1, 5]`, to within `1/100`. -/
example : ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (1 : ℝ) 5,
    |(PsiR x (x ^ (1 / u)) : ℝ) / x - dickman u| ≤ 1 / 100 :=
  dickman_asymptotic 5 (by norm_num)

/-- The prime-sum lemma with `g ≡ 1` gives Mertens: `∑_{x^{1/u}<p≤x} 1/p → log u` on `[1, 3]`. -/
example : ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Icc (1 : ℝ) 3,
    |∑ p ∈ primesBetween x 1 u, (fun _ : ℝ => (1 : ℝ)) (Real.log x / Real.log p) / p -
      ∫ w in (1 : ℝ)..u, (fun _ : ℝ => (1 : ℝ)) w / w| ≤ 1 / 100 :=
  primeSum_integral (G := 1) (by norm_num) (by norm_num) (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) continuousOn_const (by norm_num)

/-! ### Numerics (not a proof)

`ρ` from the trapezoid rule for `u ρ'(u) = −ρ(u − 1)` with step `1/1000`: `ρ(2) = 0.306853`
(`= 1 − log 2`), `ρ(3) = 0.048608`, `ρ(4) = 0.004911`. The convergence in the theorem is slow
(the error is of order `1/log x`): `Ψ(10⁵, 316)/10⁵ = 0.358` against `ρ(2) = 0.307`, and
`Ψ(10⁵, 46)/10⁵ = 0.087` against `ρ(3) = 0.049`. -/

def rhoGrid (n : ℕ) : Array Float := Id.run do
  let h : Float := 1 / 1000
  let mut a : Array Float := Array.replicate 1001 1
  for i in [1000:n] do
    let t0 := i.toFloat * h
    let v := a[i]! - h / 2 * (a[i - 1000]! / t0 + a[i + 1 - 1000]! / (t0 + h))
    a := a.push v
  return a

#eval let a := rhoGrid 4000; (a[2000]!, 1 - Float.log 2, a[3000]!, a[4000]!)
#eval ((psi 100000 316).toFloat / 100000, (psi 100000 46).toFloat / 100000)
