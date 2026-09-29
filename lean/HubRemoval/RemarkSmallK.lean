import HubRemoval.Rate
import HubRemoval.Buchstab

/-!
# Remark 5.1 (Explicit form for `K ≤ √N − 1`)

**Remark 5.1.** Fix `ρ ∈ (0, 1)`. For `N ≥ N₀'(ρ)` and `0 ≤ K ≤ √N − 1`, with `B = ⌊N/(K + 1)⌋`,
`|1 − E[Φ_K]/N − log(log N/log B)| ≤ 31/log log N` (`remark_5_1`).

*Proof.* Since `(K + 1)² ≤ N`, every prime `p > B` has `p² > N`, so `Ψ(N/p, p) = ⌊N/p⌋`. Buchstab's
identity from `B` to `N` gives `N − Ψ(N, B) = ∑_{B<p≤N} ⌊N/p⌋`, which differs from
`N ∑_{B<p≤N} 1/p` by at most `π(N) ≤ 5N/log N` (Lemma 2.1(d)). Lemma 2.1(b) and `log B ≥ ¼ log N`
give `|1 − Ψ(N, B)/N − log(log N/log B)| ≤ 18/log B + 5/log N ≤ 77/log N ≤ 1/log log N` for large
`N` (`smallK_psi`). Theorem 1.3 adds at most `30/log log N`.
-/

namespace HubRemoval

open Finset Filter Topology

/-- For `(K + 1)² ≤ N`, every prime `p > B = ⌊N/(K + 1)⌋` has `p² > N`. -/
theorem sq_gt_of_gt_B {N K p : ℕ} (hK : (K + 1) ^ 2 ≤ N) (hp : N / (K + 1) < p) : N < p * p := by
  have h1 : N < (K + 1) * (N / (K + 1) + 1) := Nat.lt_mul_div_succ N (by omega)
  have h2 : N < p * (K + 1) := by
    rw [mul_comm] at h1
    exact h1.trans_le (Nat.mul_le_mul_right _ hp)
  have h3 : K + 1 < p := by
    by_contra hc
    push Not at hc
    have : p * (K + 1) ≤ (K + 1) * (K + 1) := Nat.mul_le_mul_right _ hc
    nlinarith
  exact h2.trans_le (Nat.mul_le_mul_left _ h3.le)

/-- **The deterministic identity.** For `(K + 1)² ≤ N`,
`N − Ψ(N, B) = ∑_{B<p≤N} ⌊N/p⌋`. -/
theorem N_sub_psi_eq {N K : ℕ} (hK : (K + 1) ^ 2 ≤ N) :
    (N : ℝ) - psi N (N / (K + 1)) =
      ∑ p ∈ (primesUpTo N).filter (fun p => N / (K + 1) < p), ((N / p : ℕ) : ℝ) := by
  have hB : N / (K + 1) ≤ N := Nat.div_le_self _ _
  have h := buchstab N hB
  rw [psi_eq_self_of_le le_rfl] at h
  have hterm : ∀ p ∈ (primesUpTo N).filter (fun p => N / (K + 1) < p), psi (N / p) p = N / p :=
    fun p hp => by
      have hpB := (mem_filter.mp hp).2
      have hpp := (mem_primesUpTo.mp (mem_filter.mp hp).1).1
      refine psi_eq_self_of_le ?_
      have := sq_gt_of_gt_B hK hpB
      exact (Nat.div_le_iff_le_mul_add_pred hpp.pos).mpr (by nlinarith)
  rw [sum_congr rfl hterm] at h
  have h' : (N : ℝ) = psi N (N / (K + 1)) +
      ∑ p ∈ (primesUpTo N).filter (fun p => N / (K + 1) < p), ((N / p : ℕ) : ℝ) := by
    exact_mod_cast h
  linarith

/-- **The arithmetic part of Remark 5.1.** For `N ≥ 16` and `(K + 1)² ≤ N`,
`|1 − Ψ(N, B)/N − log(log N/log B)| ≤ 77/log N`. -/
theorem smallK_psi {N K : ℕ} (hN : 16 ≤ N) (hK : (K + 1) ^ 2 ≤ N) :
    |1 - (psi N (N / (K + 1)) : ℝ) / N -
        Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ))| ≤ 77 / Real.log N := by
  set B := N / (K + 1) with hBdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  -- `B > √N − 1 ≥ √N/2 ≥ 2`, so `log B ≥ ¼ log N`.
  have hsq : Real.sqrt N ≤ (N : ℝ) / ((K : ℝ) + 1) := by
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hKs : (K : ℝ) + 1 ≤ Real.sqrt N :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast hK)
    rw [le_div_iff₀ hK1]
    calc Real.sqrt N * ((K : ℝ) + 1) ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hKs (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN0.le
  have hBgt : Real.sqrt N - 1 < (B : ℝ) := by
    have := Nat.sub_one_lt_floor ((N : ℝ) / ((K : ℝ) + 1))
    rw [show (K : ℝ) + 1 = ((K + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_div_eq_div] at this
    push_cast at this
    rw [hBdef]
    linarith
  have hs4 : 4 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hN)
  have hB2 : (2 : ℝ) ≤ B := by linarith
  have hBhalf : Real.sqrt N / 2 ≤ (B : ℝ) := by linarith
  have hlogB : Real.log N / 4 ≤ Real.log B := by
    have h1 : Real.log (Real.sqrt N / 2) ≤ Real.log B :=
      Real.log_le_log (by positivity) hBhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hN0.le] at h1
    have h2 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have h3 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlB : 0 < Real.log (B : ℝ) := Real.log_pos (by linarith)
  -- Lemma 2.1(b) with `y = B`, `w = N`, and Lemma 2.1(d).
  have hBN : (B : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N (K + 1)
  have hmb := mertens_b hB2 hBN
  rw [Nat.floor_natCast] at hmb
  have hset : (primesUpTo N).filter (fun p : ℕ => (B : ℝ) < p) =
      (primesUpTo N).filter (fun p => B < p) := filter_congr fun p _ => by exact_mod_cast Iff.rfl
  rw [hset] at hmb
  set P := (primesUpTo N).filter (fun p => B < p) with hP
  have hpi : (P.card : ℝ) ≤ 5 * N / Real.log N := by
    have h1 : P.card ≤ (primesUpTo N).card := card_filter_le _ _
    have h2 := mertens_d (x := (N : ℝ)) (by exact_mod_cast (show 2 ≤ N by omega))
    rw [Nat.floor_natCast] at h2
    exact (Nat.cast_le.mpr h1).trans h2
  -- `∑ ⌊N/p⌋` is within `|P|` of `N ∑ 1/p`.
  have hfl : |∑ p ∈ P, ((N / p : ℕ) : ℝ) - N * ∑ p ∈ P, (1 : ℝ) / p| ≤ P.card := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun p hp => (?_ : _ ≤ (1 : ℝ))).trans (by simp)
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (mem_primesUpTo.mp (mem_filter.mp hp).1).1.pos
    have h1 := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
    have h2 : (N : ℝ) / p - 1 < ((N / p : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor ((N : ℝ) / p)
      rwa [Nat.floor_div_eq_div] at this
    rw [mul_one_div, abs_le]
    constructor <;> linarith
  have hid := N_sub_psi_eq hK
  rw [← hBdef, ← hP] at hid
  -- Combine.
  have e : 1 - (psi N B : ℝ) / N - Real.log (Real.log N / Real.log B) =
      ((∑ p ∈ P, ((N / p : ℕ) : ℝ)) - N * ∑ p ∈ P, (1 : ℝ) / p) / N +
        (∑ p ∈ P, (1 : ℝ) / p - Real.log (Real.log N / Real.log B)) := by
    rw [← hid]
    field_simp
    ring
  rw [e]
  have t1 : |((∑ p ∈ P, ((N / p : ℕ) : ℝ)) - N * ∑ p ∈ P, (1 : ℝ) / p) / N| ≤ 5 / Real.log N := by
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    calc |∑ p ∈ P, ((N / p : ℕ) : ℝ) - N * ∑ p ∈ P, (1 : ℝ) / p| ≤ P.card := hfl
      _ ≤ 5 * N / Real.log N := hpi
      _ = 5 / Real.log N * N := by ring
  have t2 : |∑ p ∈ P, (1 : ℝ) / p - Real.log (Real.log N / Real.log B)| ≤ 72 / Real.log N := by
    refine hmb.trans ?_
    rw [div_le_div_iff₀ hlB hL]
    linarith
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 5 / Real.log N + 72 / Real.log N := add_le_add t1 t2
    _ = 77 / Real.log N := by ring

/-- **Remark 5.1.** Fix `ρ ∈ (0, 1)`. For all large `N` and all `K` with `(K + 1)² ≤ N`
(that is, `K ≤ √N − 1`), `|1 − E[Φ_K]/N − log(log N/log B)| ≤ 31/log log N`. -/
theorem remark_5_1 {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K : ℕ, (K + 1) ^ 2 ≤ N →
      |1 - expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) / N -
          Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ))| ≤
        31 / Real.log (Real.log N) := by
  have hbig := tendsto_log_nat.eventually (eventually_mul_log_pow_le 77 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_goodN hρ0 hρ1).and
    (hbig.and (eventually_ge_atTop 16)))
  refine ⟨N₀, fun N hN K hK => ?_⟩
  obtain ⟨hG, h77, hN16⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hKN : K < N := by nlinarith
  have hℓ : 1 < Real.log (Real.log N) := hG.p0
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  -- `77/log N ≤ 1/log log N`.
  have hsmall : 77 / Real.log N ≤ 1 / Real.log (Real.log N) := by
    rw [div_le_div_iff₀ hL (by linarith)]
    simpa using h77
  have hpsi := smallK_psi hN16 hK
  have hgap := gap_le_of_good hρ0 hρ1 hKN hG
  have hg0 := gap_nonneg hρ0.le hρ1.le N K
  have hgapN : gap ρ N K / N ≤ 30 / Real.log (Real.log N) := by
    rw [div_le_iff₀ hN0]
    calc gap ρ N K ≤ 30 * N / Real.log (Real.log N) := hgap
      _ = 30 / Real.log (Real.log N) * N := by ring
  have e : 1 - expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) / N -
      Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ)) =
      (1 - (psi N (N / (K + 1)) : ℝ) / N -
        Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ))) + gap ρ N K / N := by
    unfold gap
    field_simp
    ring
  rw [e]
  have hg0' : 0 ≤ gap ρ N K / N := div_nonneg hg0 hN0.le
  calc _ ≤ |1 - (psi N (N / (K + 1)) : ℝ) / N -
          Real.log (Real.log N / Real.log ((N / (K + 1) : ℕ) : ℝ))| + |gap ρ N K / N| :=
        abs_add_le _ _
    _ ≤ 1 / Real.log (Real.log N) + 30 / Real.log (Real.log N) := by
        rw [abs_of_nonneg hg0']
        exact add_le_add (hpsi.trans hsmall) hgapN
    _ = 31 / Real.log (Real.log N) := by ring

end HubRemoval
