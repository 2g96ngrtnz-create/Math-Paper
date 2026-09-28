import HubRemoval.Doubling
import HubRemoval.Turan

/-!
# The arithmetic core (paper, Lemma 4.5(c)): the abstract counting argument

For `m ∈ V_{N,K}` let `D(m) = {d ∈ S_M : d ∣ m}` and `s(m) = |D(m)|`. Lemma 4.5(c) says that every
`m ∈ 𝒰` has `s(m) ≥ s₀ + 1`.

This file proves the counting argument behind (c). The real parameters `M`, `z`, `E₀`, `E₁` are
kept abstract, and the exact inequalities the proof uses are hypotheses. In the paper
`M = N^{1−2δ}`, `z = N^{δ/s₀}`, `E₀ = N^{2δ}` and `E₁ = N^{1−δ}/(K+1)`. Deriving the inequalities
from (H1)–(H3) is a separate step.

The proof is the paper's.

* **Step 1.** A divisor `e ∣ m` with `E₀ ≤ e ≤ E₁` gives `m/e ∈ D(m)`.
* **Step 2.** Choose `s₀` distinct primes `pᵢ ≤ z` dividing `m`. Their product is `r ≤ z^{s₀}`,
  and `m' = m/r ≥ E₀`.
* **Step 3.** Find a divisor `e₀ ∣ m'` with `E₀ ≤ e₀` and `z e₀ ≤ E₁`. Either `m'` has a prime
  factor `q ≥ E₀`, which works because `q ≤ Y`, or all prime factors of `m'` are `< E₀`. In the
  second case a divisor lies in `[E₀, E₀²)` (`exists_dvd_mem_Ico`).
* **Step 4.** `e₀, e₀p₁, …, e₀p_{s₀}` are `s₀ + 1` distinct divisors of `m` in `[E₀, E₁]`.
-/

namespace HubRemoval

open Finset

/-- **Case (ii) of Step 3.** If `1 < E ≤ n` and every prime factor of `n` is `< E`, then `n` has a
divisor in `[E, E²)`. Divide off one prime at a time until the quotient drops below `E²`. -/
theorem exists_dvd_mem_Ico {E : ℝ} (hE : 1 < E) :
    ∀ n : ℕ, E ≤ n → (∀ p, p.Prime → p ∣ n → (p : ℝ) < E) →
      ∃ e, e ∣ n ∧ E ≤ e ∧ (e : ℝ) < E ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hprimes
  by_cases hlt : (n : ℝ) < E ^ 2
  · exact ⟨n, dvd_rfl, hn, hlt⟩
  push Not at hlt
  have hn1 : 1 < n := by
    have : (1 : ℝ) < n := by nlinarith
    exact_mod_cast this
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  obtain ⟨n', rfl⟩ := hpn
  have hpE := hprimes p hp (dvd_mul_right p n')
  have hp2 := hp.two_le
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · simp [h] at hn1
    · exact h
  have hlt' : n' < p * n' := by nlinarith
  have hn'E : E ≤ n' := by
    push_cast at hlt
    have h1 : (p : ℝ) * n' < E * n' := mul_lt_mul_of_pos_right hpE (by exact_mod_cast hn'pos)
    nlinarith
  obtain ⟨e, he, hEe, heE⟩ := ih n' hlt' hn'E fun q hq hqd => hprimes q hq (hqd.mul_left p)
  exact ⟨e, he.mul_left p, hEe, heE⟩

/-- A product of distinct primes dividing `m` divides `m`. -/
theorem prod_primes_dvd {T : Finset ℕ} {m : ℕ} (hT : ∀ p ∈ T, p.Prime) (hdvd : ∀ p ∈ T, p ∣ m) :
    ∏ p ∈ T, p ∣ m := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [prod_insert haT]
    have hcop : a.Coprime (∏ p ∈ T, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes (hT a (mem_insert_self a T)) (hT p (mem_insert_of_mem hp))).mpr
        fun h => haT (h ▸ hp)
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd a (mem_insert_self a T))
      (ih (fun p hp => hT p (mem_insert_of_mem hp)) fun p hp => hdvd p (mem_insert_of_mem hp))

open Classical in
/-- `D(m) = {d ∈ S_M : d ∣ m}`. -/
noncomputable def lowerDivisors (M : ℝ) (K m : ℕ) : Finset ℕ := m.divisors.filter (goodSet M K)

open Classical in
theorem mem_lowerDivisors {M : ℝ} {K m d : ℕ} :
    d ∈ lowerDivisors M K m ↔ (d ∣ m ∧ m ≠ 0) ∧ goodSet M K d := by
  unfold lowerDivisors
  rw [mem_filter, Nat.mem_divisors]

/-- **Lemma 4.5(c), the counting argument.** Under the listed inequalities, `s(m) ≥ s₀ + 1`.

* `hmY`: `P⁺(m) ≤ Y = M/(2(K+1))`.
* `hω`: `ω_z(m) ≥ s₀`, where `ω_z` counts primes `≤ z`, that is `≤ ⌊z⌋`.
* `hmE₀`: `m ≤ M E₀` (in the paper `M E₀ = N`).
* `hmE₁`: `(K+1) E₁ < m` (in the paper `(K+1) E₁ = N^{1−δ}`).
* `hYE₁`: `z M ≤ 2(K+1) E₁`, that is `Y ≤ E₁/z`.
* `hE₀E₁`: `z E₀² ≤ E₁`.
* `hmr`: `z^{s₀} E₀ ≤ m`, which gives `m' = m/r ≥ E₀`. -/
theorem core_divisors {K m s₀ : ℕ} {M z E₀ E₁ : ℝ} (hm0 : 0 < m)
    (hmY : ∀ p, p.Prime → p ∣ m → 2 * ((K : ℝ) + 1) * p ≤ M)
    (hω : s₀ ≤ omegaZ ⌊z⌋₊ m) (hz : 1 ≤ z) (hE₀ : 1 < E₀)
    (hmE₀ : (m : ℝ) ≤ M * E₀) (hmE₁ : ((K : ℝ) + 1) * E₁ < m)
    (hYE₁ : z * M ≤ 2 * ((K : ℝ) + 1) * E₁) (hE₀E₁ : z * E₀ ^ 2 ≤ E₁)
    (hmr : z ^ s₀ * E₀ ≤ m) :
    s₀ + 1 ≤ (lowerDivisors M K m).card := by
  classical
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hz0 : 0 < z := by linarith
  have hE₀0 : 0 < E₀ := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hM0 : 0 < M := by
    by_contra h
    push Not at h
    have : M * E₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hE₀0.le
    linarith
  -- Step 1: a divisor `e ∈ [E₀, E₁]` of `m` gives `m/e ∈ D(m)`.
  have step1 : ∀ e, e ∣ m → E₀ ≤ e → (e : ℝ) ≤ E₁ → m / e ∈ lowerDivisors M K m := by
    intro e he hE0e heE1
    obtain ⟨d, hd⟩ := he
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h, zero_mul] at hd
        omega
      · exact h
    have hdiv : m / e = d := by rw [hd, Nat.mul_div_cancel_left d he0]
    rw [hdiv]
    have hmr' : (m : ℝ) = e * d := by exact_mod_cast hd
    have her : (0 : ℝ) < e := by exact_mod_cast he0
    refine mem_lowerDivisors.mpr ⟨⟨Dvd.intro_left e hd.symm, hm0.ne'⟩, ?_, ?_, ?_⟩
    · have h1 : ((K : ℝ) + 1) * e < e * d :=
        calc ((K : ℝ) + 1) * e ≤ ((K : ℝ) + 1) * E₁ := mul_le_mul_of_nonneg_left heE1 hK1.le
          _ < m := hmE₁
          _ = e * d := hmr'
      have h2 : (K : ℝ) + 1 < d := by nlinarith
      have h3 : (K : ℝ) < d := by linarith
      exact_mod_cast h3
    · have h1 : (e : ℝ) * d ≤ e * M :=
        calc (e : ℝ) * d = m := hmr'.symm
          _ ≤ M * E₀ := hmE₀
          _ ≤ M * e := mul_le_mul_of_nonneg_left hE0e hM0.le
          _ = e * M := mul_comm _ _
      exact le_of_mul_le_mul_left h1 her
    · intro q hq hqd
      exact hmY q hq (hqd.trans (Dvd.intro_left e hd.symm))
  -- Step 2: the reserve primes `p₁, …, p_{s₀} ≤ z` and `r = p₁ ⋯ p_{s₀}`.
  obtain ⟨T, hTP, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := (primesUpTo ⌊z⌋₊).filter (· ∣ m)) (by exact hω)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (mem_primesUpTo.mp (mem_filter.mp (hTP hp)).1).1
  have hTle : ∀ p ∈ T, (p : ℝ) ≤ z := fun p hp =>
    (Nat.le_floor_iff (by linarith)).mp (mem_primesUpTo.mp (mem_filter.mp (hTP hp)).1).2
  have hTdvd : ∀ p ∈ T, p ∣ m := fun p hp => (mem_filter.mp (hTP hp)).2
  have hr : ∏ p ∈ T, p ∣ m := prod_primes_dvd hTprime hTdvd
  have hrle : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ z ^ s₀ := by
    rw [← hTcard]
    push_cast
    calc ∏ p ∈ T, (p : ℝ) ≤ ∏ _p ∈ T, z := prod_le_prod₀ (fun p _ => by positivity) hTle
      _ = z ^ T.card := prod_const z
  have hrpos : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hTprime p hp).pos
  obtain ⟨m', hm'⟩ := hr
  have hm'E : E₀ ≤ m' := by
    have h1 : (m : ℝ) = ((∏ p ∈ T, p : ℕ) : ℝ) * m' := by exact_mod_cast hm'
    have h2 : ((∏ p ∈ T, p : ℕ) : ℝ) * E₀ ≤ ((∏ p ∈ T, p : ℕ) : ℝ) * m' :=
      calc ((∏ p ∈ T, p : ℕ) : ℝ) * E₀ ≤ z ^ s₀ * E₀ := mul_le_mul_of_nonneg_right hrle hE₀0.le
        _ ≤ m := hmr
        _ = _ := h1
    exact le_of_mul_le_mul_left h2 (by exact_mod_cast hrpos)
  have hm'm : m' ∣ m := Dvd.intro_left _ hm'.symm
  -- Step 3: a base divisor `e₀ ∣ m'` with `E₀ ≤ e₀` and `z e₀ ≤ E₁`.
  have step3 : ∃ e₀, e₀ ∣ m' ∧ E₀ ≤ e₀ ∧ z * e₀ ≤ E₁ := by
    by_cases hbig : ∃ q, q.Prime ∧ q ∣ m' ∧ E₀ ≤ q
    · obtain ⟨q, hq, hqm', hEq⟩ := hbig
      refine ⟨q, hqm', hEq, ?_⟩
      have h1 := mul_le_mul_of_nonneg_left (hmY q hq (hqm'.trans hm'm)) hz0.le
      have h2 : z * q * (2 * ((K : ℝ) + 1)) ≤ E₁ * (2 * ((K : ℝ) + 1)) := by linarith
      exact le_of_mul_le_mul_right h2 (by positivity)
    · push Not at hbig
      obtain ⟨e, he, hEe, heE⟩ := exists_dvd_mem_Ico hE₀ m' hm'E fun p hp hpd => hbig p hp hpd
      refine ⟨e, he, hEe, ?_⟩
      have := mul_le_mul_of_nonneg_left heE.le hz0.le
      linarith
  -- Step 4: `e₀, e₀p₁, …, e₀p_{s₀}` are `s₀ + 1` distinct divisors of `m` in `[E₀, E₁]`.
  obtain ⟨e₀, he₀, hE₀e₀, hze₀⟩ := step3
  have he₀R : (0 : ℝ) < e₀ := by linarith
  have he₀pos : 0 < e₀ := by exact_mod_cast he₀R
  have he₀m : e₀ ∣ m := he₀.trans hm'm
  set Es := insert e₀ (T.image (e₀ * ·)) with hEsdef
  have hEs_card : Es.card = s₀ + 1 := by
    rw [card_insert_of_notMem, card_image_of_injOn, hTcard]
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left he₀pos hab
    · intro h
      obtain ⟨p, hp, hpe⟩ := mem_image.mp h
      have h1 : e₀ * p = e₀ * 1 := by rw [mul_one]; exact hpe
      exact (hTprime p hp).one_lt.ne' (Nat.eq_of_mul_eq_mul_left he₀pos h1)
  have hEs : ∀ e ∈ Es, e ∣ m ∧ E₀ ≤ (e : ℝ) ∧ (e : ℝ) ≤ E₁ := by
    intro e he
    rcases mem_insert.mp he with rfl | he
    · refine ⟨he₀m, hE₀e₀, ?_⟩
      nlinarith
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp he
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hTprime p hp).one_lt.le
      refine ⟨?_, ?_, ?_⟩
      · rw [hm', mul_comm (∏ p ∈ T, p) m']
        exact mul_dvd_mul he₀ (dvd_prod_of_mem _ hp)
      · push_cast
        nlinarith
      · push_cast
        have := mul_le_mul_of_nonneg_left (hTle p hp) he₀R.le
        linarith
  have hinj : Set.InjOn (fun e => m / e) Es := by
    intro a ha b hb hab
    simp only at hab
    rw [← Nat.div_div_self (hEs a ha).1 hm0.ne', hab, Nat.div_div_self (hEs b hb).1 hm0.ne']
  have hsub : Es.image (fun e => m / e) ⊆ lowerDivisors M K m := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := mem_image.mp hd
    obtain ⟨h1, h2, h3⟩ := hEs e he
    exact step1 e h1 h2 h3
  calc s₀ + 1 = Es.card := hEs_card.symm
    _ = (Es.image (fun e => m / e)).card := (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub

end HubRemoval
