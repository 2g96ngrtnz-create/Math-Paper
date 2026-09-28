import HubRemoval.Fibre

/-!
# Doubling connectivity (paper, Lemma 4.2)

`M` is a real number, `K` a natural number with `M ≥ 4(K+1)`, and `Y = M / (2(K+1))`.
`S_M = {x ∈ ℤ ∩ (K, M] : P⁺(x) ≤ Y}`, and `G_{M,K}` is the divisor graph on `ℤ ∩ (K, M]`,
which is `divGraph ⌊M⌋₊ K`.

**Lemma 4.2.** `S_M` lies in a single connected component of `G_{M,K}`. That component contains
the power of `2` in `(M/2, M]`, namely `2 ^ Nat.log 2 ⌊M⌋₊`.

The condition `P⁺(x) ≤ Y` is written without division as `2(K+1)p ≤ M` for every prime `p ∣ x`.
The proof is the paper's. Double `x` until it lands in `(M/2, M]`, divide by an odd prime, and
repeat. The odd part `ordCompl[2] x` strictly decreases at each division, which drives a strong
induction.
-/

namespace HubRemoval

open Nat

/-- The paper's `S_M`, for a real number `M`: integers `x ∈ (K, M]` all of whose prime factors
satisfy `p ≤ M / (2(K+1))`. -/
def goodSet (M : ℝ) (K x : ℕ) : Prop :=
  K < x ∧ (x : ℝ) ≤ M ∧ ∀ p, p.Prime → p ∣ x → 2 * ((K : ℝ) + 1) * p ≤ M

/-- Doubling chain: if `K < x` and `2^a x ≤ L`, then `x` is joined to `2^a x` in `G_{L,K}`. -/
theorem reachable_two_pow_mul {L K x : ℕ} (hKx : K < x) :
    ∀ a, 2 ^ a * x ≤ L → (divGraph L K).Reachable x (2 ^ a * x)
  | 0, _ => by simp
  | a + 1, h => by
    have e : 2 ^ (a + 1) * x = 2 * (2 ^ a * x) := by ring
    have hprev : 2 ^ a * x ≤ L := by omega
    have hxle : x ≤ 2 ^ a * x := Nat.le_mul_of_pos_left x (by positivity)
    refine (reachable_two_pow_mul hKx a hprev).trans (SimpleGraph.Adj.reachable ?_)
    refine ⟨by omega, by omega, hprev, by omega, h, Or.inl ⟨2, by rw [e]; ring⟩⟩

/-- **Lemma 4.2.** For real `M ≥ 4(K+1)`, every element of `S_M` is joined in `G_{M,K}` to the
power of two `2 ^ log₂ ⌊M⌋`. Hence `S_M` lies in one connected component. -/
theorem doubling {M : ℝ} {K : ℕ} (hM : 4 * ((K : ℝ) + 1) ≤ M) (x : ℕ) (hx : goodSet M K x) :
    (divGraph ⌊M⌋₊ K).Reachable x (2 ^ Nat.log 2 ⌊M⌋₊) := by
  set L := ⌊M⌋₊ with hLdef
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hL4 : 4 ≤ L := Nat.le_floor (by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    push_cast; linarith)
  -- Strong induction on the odd part `c = ordCompl[2] x`.
  suffices H : ∀ c x, ordCompl[2] x = c → goodSet M K x →
      (divGraph L K).Reachable x (2 ^ Nat.log 2 L) from H _ x rfl hx
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro x hc hx
  obtain ⟨hKx, hxM, hprimes⟩ := hx
  have hx0 : x ≠ 0 := by omega
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
  have hxL : x ≤ L := Nat.le_floor hxM
  -- Double `x` until it lands in `(L/2, L]`: `y = 2^a x` with `a` maximal.
  set a := Nat.log 2 (L / x) with hadef
  have hLx : L / x ≠ 0 := (Nat.div_pos hxL hxpos).ne'
  have h1 : 2 ^ a ≤ L / x := Nat.pow_log_le_self 2 hLx
  have h2 : L / x < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  set y := 2 ^ a * x with hydef
  have hyL : y ≤ L := (Nat.le_div_iff_mul_le hxpos).mp h1
  have hLy : L < 2 * y := by
    have := (Nat.div_lt_iff_lt_mul hxpos).mp h2
    have e : 2 ^ (a + 1) * x = 2 * y := by rw [hydef]; ring
    omega
  have hMy : M < 2 * (y : ℝ) := by
    have h3 : M < (L : ℝ) + 1 := Nat.lt_floor_add_one M
    have h4 : (L : ℝ) + 1 ≤ 2 * (y : ℝ) := by exact_mod_cast (show L + 1 ≤ 2 * y by omega)
    linarith
  have hreach1 : (divGraph L K).Reachable x y := reachable_two_pow_mul hKx a hyL
  have hcy : ordCompl[2] y = c := by
    rw [hydef, ordCompl_mul, ordCompl_self_pow prime_two, one_mul, hc]
  by_cases hc1 : c = 1
  · -- `y` is a power of two in `(L/2, L]`, so it is `2 ^ log₂ L`.
    have hy2 : y = 2 ^ (y.factorization 2) := by
      have := ordProj_mul_ordCompl_eq_self y 2
      rw [hcy, hc1, mul_one] at this
      exact this.symm
    have hlog : y.factorization 2 = Nat.log 2 L := by
      apply le_antisymm
      · have hpow : 2 ^ y.factorization 2 ≤ L := by rw [← hy2]; exact hyL
        exact Nat.le_log_of_pow_le (by norm_num) hpow
      · by_contra hlt
        push_neg at hlt
        have h5 : 2 ^ (y.factorization 2 + 1) ≤ 2 ^ Nat.log 2 L :=
          Nat.pow_le_pow_right (by norm_num) hlt
        have h6 : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 (by omega)
        have h7 : 2 ^ (y.factorization 2 + 1) = 2 * y := by rw [pow_succ, ← hy2]; ring
        omega
    have hyeq : y = 2 ^ Nat.log 2 L := by
      calc y = 2 ^ (y.factorization 2) := hy2
        _ = 2 ^ Nat.log 2 L := by rw [hlog]
    exact hyeq ▸ hreach1
  · -- Divide `y` by an odd prime `p ∣ c`.
    obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
    have hpc' : p ∣ ordCompl[2] x := by rw [hc]; exact hpc
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact not_dvd_ordCompl prime_two hx0 hpc'
    have hpx : p ∣ x := hpc'.trans (ordCompl_dvd x 2)
    have hpy : p ∣ y := hpx.trans (Dvd.intro_left _ rfl)
    obtain ⟨x1, hx1⟩ := hpy
    have hpY := hprimes p hp hpx
    have hy0 : 0 < y := by rw [hydef]; exact Nat.mul_pos (by positivity) hxpos
    have hx1pos : 0 < x1 := by
      rcases Nat.eq_zero_or_pos x1 with h0 | h0
      · rw [h0, mul_zero] at hx1; omega
      · exact h0
    -- `K + 1 < x1`: from `2y > M ≥ 2(K+1)p` and `y = p x1`.
    have hKx1 : K + 1 < x1 := by
      have hr : ((K : ℝ) + 1) * p < (x1 : ℝ) * p := by
        have : (y : ℝ) = (p : ℝ) * x1 := by exact_mod_cast hx1
        nlinarith
      have hn : (K + 1) * p < x1 * p := by exact_mod_cast hr
      exact Nat.lt_of_mul_lt_mul_right hn
    have hx1y : 2 * x1 ≤ y := by rw [hx1]; exact Nat.mul_le_mul_right x1 hp.two_le
    have hadj : (divGraph L K).Adj x1 y :=
      ⟨by omega, by omega, by omega, by omega, hyL, Or.inl ⟨p, by rw [hx1]; ring⟩⟩
    have hx1good : goodSet M K x1 := by
      refine ⟨by omega, ?_, fun q hq hqd => ?_⟩
      · have : (x1 : ℝ) ≤ L := by exact_mod_cast (show x1 ≤ L by omega)
        exact this.trans (Nat.floor_le hM0)
      · have hqy : q ∣ 2 ^ a * x := hqd.trans (Dvd.intro_left _ hx1.symm)
        rcases (Nat.Prime.dvd_mul hq).mp hqy with hq2 | hqx
        · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq prime_two).mp (hq.dvd_of_dvd_pow hq2)
          subst this
          push_cast
          linarith
        · exact hprimes q hq hqx
    -- The odd part strictly decreases.
    have hlt : ordCompl[2] x1 < c := by
      have hp2' : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq prime_two hp).mp h).symm
      have hpodd : ordCompl[2] p = p := by
        show p / 2 ^ p.factorization 2 = p
        rw [Nat.factorization_eq_zero_of_not_dvd hp2', pow_zero, Nat.div_one]
      have hmul : ordCompl[2] y = ordCompl[2] p * ordCompl[2] x1 := by rw [hx1, ordCompl_mul]
      rw [hcy, hpodd] at hmul
      have ho := ordCompl_pos 2 (Nat.pos_iff_ne_zero.mp hx1pos)
      calc ordCompl[2] x1 < 2 * ordCompl[2] x1 := by omega
        _ ≤ p * ordCompl[2] x1 := Nat.mul_le_mul_right _ hp.two_le
        _ = c := hmul.symm
    exact hreach1.trans (hadj.reachable.symm.trans (ih _ hlt x1 rfl hx1good))

/-- **Lemma 4.2, as stated in the paper.** Any two elements of `S_M` lie in the same connected
component of `G_{M,K}`. -/
theorem doubling_connected {M : ℝ} {K : ℕ} (hM : 4 * ((K : ℝ) + 1) ≤ M) {x x' : ℕ}
    (hx : goodSet M K x) (hx' : goodSet M K x') : (divGraph ⌊M⌋₊ K).Reachable x x' :=
  (doubling hM x hx).trans (doubling hM x' hx').symm

end HubRemoval
