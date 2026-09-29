import HubRemoval.Mertens2
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Remark 2.5 (The Turán–Kubilius inequality)

**Remark 2.5.** There is an absolute constant `C` such that for every complex additive function
`f` and every `x ≥ 2`,
`∑_{n≤x} |f(n) − A(x)|² ≤ C x B(x)²`, where `A(x) = ∑_{p^ν≤x} f(p^ν) p^{−ν}(1 − p^{−1})` and
`B(x)² = ∑_{p^ν≤x} |f(p^ν)|² p^{−ν}` (`turan_kubilius`, with `C = 130`).

Prime powers `p^ν ≤ N` are indexed by pairs `(p, ν)` (`ppIdx`), and `p^ν ‖ n` means
`v_p(n) = ν`. An additive `f` satisfies `f(n) = ∑_{p^ν ≤ N} f(p^ν) 1[v_p(n) = ν]` for
`1 ≤ n ≤ N` (`IsAdditive.eq_sum_ppIdx`).

*Proof.* Splitting `f` into real and imaginary parts, and each into positive and negative parts,
costs a factor 2 and reduces to weights `g ≥ 0` on prime powers. For those (`tk_core`),
expanding the square with the counts `#{n ≤ N : v_p(n) = ν} ≥ N w − 1` and, for `p ≠ r`,
`#{n ≤ N : v_p(n) = ν, v_r(n) = μ} ≤ N w w' + 2·1[p^ν r^μ ≤ N]` (inclusion–exclusion), where
`w = p^{−ν}(1 − p^{−1})`, gives `S ≤ N B² + 2E + 2AG` with `G = ∑ g(p^ν)` and
`E = ∑_{p^ν r^μ ≤ N} g(p^ν)g(r^μ)`. Cauchy–Schwarz bounds `E` and `AG` by `N B²` times an absolute
constant, using `#{p^ν ≤ Y} log 2Y ≤ 58Y` (Lemma 2.1(d) and a count of higher powers,
`card_ppIdx_mul_log_le`) and `∑_{p^ν ≤ M} p^{−ν} ≤ 1 + log M`.
-/

namespace HubRemoval

open Finset

/-! ### Prime powers as pairs `(p, ν)` -/

/-- The prime powers `p^ν ≤ N`, as pairs `(p, ν)` with `p` prime and `ν ≥ 1`. -/
def ppIdx (N : ℕ) : Finset (ℕ × ℕ) :=
  (primesUpTo N ×ˢ Icc 1 N).filter (fun i => i.1 ^ i.2 ≤ N)

/-- The prime power `q_i = p^ν` of `i = (p, ν)`. -/
def qi (i : ℕ × ℕ) : ℕ := i.1 ^ i.2

theorem mem_ppIdx {N : ℕ} {i : ℕ × ℕ} :
    i ∈ ppIdx N ↔ i.1.Prime ∧ 1 ≤ i.2 ∧ i.1 ^ i.2 ≤ N := by
  obtain ⟨p, ν⟩ := i
  simp only [ppIdx, mem_filter, mem_product, mem_primesUpTo, mem_Icc]
  constructor
  · rintro ⟨⟨⟨hp, -⟩, hν, -⟩, h⟩
    exact ⟨hp, hν, h⟩
  · rintro ⟨hp, hν, h⟩
    have h1 : p ≤ p ^ ν := Nat.le_self_pow (by omega) p
    have h2 : ν < 2 ^ ν := Nat.lt_two_pow_self
    have h3 : 2 ^ ν ≤ p ^ ν := Nat.pow_le_pow_left hp.two_le ν
    exact ⟨⟨⟨hp, by omega⟩, hν, by omega⟩, h⟩

theorem qi_pos {N : ℕ} {i : ℕ × ℕ} (hi : i ∈ ppIdx N) : 0 < qi i :=
  pow_pos (mem_ppIdx.mp hi).1.pos _

theorem two_le_qi {N : ℕ} {i : ℕ × ℕ} (hi : i ∈ ppIdx N) : 2 ≤ qi i := by
  obtain ⟨hp, hν, -⟩ := mem_ppIdx.mp hi
  calc 2 ≤ i.1 := hp.two_le
    _ ≤ qi i := Nat.le_self_pow (by omega) _

theorem qi_le {N : ℕ} {i : ℕ × ℕ} (hi : i ∈ ppIdx N) : qi i ≤ N := (mem_ppIdx.mp hi).2.2

/-- Distinct pairs give distinct prime powers. -/
theorem qi_injOn (N : ℕ) : Set.InjOn qi (ppIdx N : Set (ℕ × ℕ)) := by
  rintro ⟨p, ν⟩ hi ⟨r, μ⟩ hj h
  obtain ⟨hp, hν, -⟩ := mem_ppIdx.mp (mem_coe.mp hi)
  obtain ⟨hr, hμ, -⟩ := mem_ppIdx.mp (mem_coe.mp hj)
  simp only [qi] at h
  have hpr : p = r := by
    have : p ∣ r ^ μ := h ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow this)
  subst hpr
  rw [Nat.pow_right_injective hp.two_le h]

/-! ### Additive functions -/

/-- `f` is additive: `f(mn) = f(m) + f(n)` whenever `m` and `n` are coprime. -/
def IsAdditive (f : ℕ → ℂ) : Prop := ∀ m n : ℕ, m.Coprime n → f (m * n) = f m + f n

theorem IsAdditive.map_one {f : ℕ → ℂ} (hf : IsAdditive f) : f 1 = 0 := by
  have h := hf 1 1 (Nat.coprime_one_left 1)
  rw [mul_one] at h
  simpa using h

theorem IsAdditive.map_prod {f : ℕ → ℂ} (hf : IsAdditive f) {s : Finset ℕ} {a : ℕ → ℕ}
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (a i).Coprime (a j)) :
    f (∏ i ∈ s, a i) = ∑ i ∈ s, f (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf.map_one]
  | insert k s hk ih =>
    have hcop : (a k).Coprime (∏ i ∈ s, a i) := Nat.Coprime.prod_right fun j hj =>
      h k (mem_insert_self k s) j (mem_insert_of_mem hj) (fun e => hk (e ▸ hj))
    rw [prod_insert hk, sum_insert hk, hf _ _ hcop,
      ih fun i hi j hj => h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj)]

/-- `f(n) = ∑_{p ∣ n} f(p^{v_p(n)})`. -/
theorem IsAdditive.eq_sum_primeFactors {f : ℕ → ℂ} (hf : IsAdditive f) {n : ℕ} (hn : n ≠ 0) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  exact hf.map_prod fun p hp r hr hpr => Nat.coprime_pow_primes _ _
    (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hr) hpr

/-- **The representation.** For `1 ≤ n ≤ N`, `f(n) = ∑_{p^ν ≤ N} f(p^ν) 1[v_p(n) = ν]`. -/
theorem IsAdditive.eq_sum_ppIdx {f : ℕ → ℂ} (hf : IsAdditive f) {N n : ℕ} (hn : n ∈ Ioc 0 N) :
    f n = ∑ i ∈ ppIdx N, if n.factorization i.1 = i.2 then f (qi i) else 0 := by
  obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
  rw [hf.eq_sum_primeFactors (by omega), ← sum_filter]
  symm
  refine sum_nbij' (fun i => i.1) (fun p => (p, n.factorization p)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨hi, hv⟩ := mem_filter.mp hi
    obtain ⟨hp, hν, -⟩ := mem_ppIdx.mp hi
    exact Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_factorization_pos (by omega), by omega⟩
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpos := hp'.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    refine mem_filter.mpr ⟨mem_ppIdx.mpr ⟨hp', hpos, (Nat.ordProj_le p (by omega)).trans hnN⟩,
      rfl⟩
  · intro i hi
    exact Prod.ext rfl (mem_filter.mp hi).2
  · intro p _
    rfl
  · intro i hi
    simp only [qi, (mem_filter.mp hi).2]

/-! ### Counting `n ≤ N` by divisibility and valuation -/

/-- `D(m) = #{n ≤ N : m ∣ n}`. -/
def dcount (N m : ℕ) : ℕ := ((Ioc 0 N).filter (m ∣ ·)).card

/-- `N/m − 1 ≤ D(m) ≤ N/m`. -/
theorem dcount_bounds (N : ℕ) {m : ℕ} (hm : 0 < m) :
    (N : ℝ) / m - 1 ≤ (dcount N m : ℝ) ∧ (dcount N m : ℝ) ≤ (N : ℝ) / m := by
  unfold dcount
  rw [Nat.Ioc_filter_dvd_card_eq_div]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, Nat.cast_div_le⟩
  have h1 : N < m * (N / m + 1) := Nat.lt_mul_div_succ N hm
  have h1R : (N : ℝ) < m * (((N / m : ℕ) : ℝ) + 1) := by exact_mod_cast h1
  rw [div_sub_one hmR.ne', div_le_iff₀ hmR]
  linarith

/-- `v_p(n) = ν` if and only if `p^ν ∣ n` and `p^{ν+1} ∤ n`. -/
theorem factorization_eq_iff {p n ν : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    n.factorization p = ν ↔ p ^ ν ∣ n ∧ ¬ p ^ (ν + 1) ∣ n := by
  rw [hp.pow_dvd_iff_le_factorization hn, hp.pow_dvd_iff_le_factorization hn]
  omega

theorem mul_dvd_iff_of_coprime {x y n : ℕ} (h : x.Coprime y) : x * y ∣ n ↔ x ∣ n ∧ y ∣ n :=
  ⟨fun hd => ⟨dvd_of_mul_right_dvd hd, dvd_of_mul_left_dvd hd⟩,
    fun ⟨h1, h2⟩ => h.mul_dvd_of_dvd_of_dvd h1 h2⟩

/-- **Inclusion–exclusion.** If `B ∣ n` and `C ∣ n` each force `A ∣ n`, and `B ∣ n ∧ C ∣ n` is
`D ∣ n`, then `#{n ≤ N : A ∣ n, B ∤ n, C ∤ n} = D(A) − D(B) − D(C) + D(D)`. -/
theorem card_ie (N : ℕ) {A B C D : ℕ} (hAB : ∀ n, B ∣ n → A ∣ n) (hAC : ∀ n, C ∣ n → A ∣ n)
    (hBC : ∀ n, B ∣ n ∧ C ∣ n ↔ D ∣ n) :
    (((Ioc 0 N).filter (fun n => A ∣ n ∧ ¬ B ∣ n ∧ ¬ C ∣ n)).card : ℝ) =
      (dcount N A : ℝ) - dcount N B - dcount N C + dcount N D := by
  unfold dcount
  set T := (Ioc 0 N).filter (A ∣ ·) with hT
  have e0 : (Ioc 0 N).filter (fun n => A ∣ n ∧ ¬ B ∣ n ∧ ¬ C ∣ n) =
      T.filter (fun n => ¬ (B ∣ n ∨ C ∣ n)) := by
    ext n
    simp only [hT, mem_filter, not_or]
    tauto
  have eB : T.filter (B ∣ ·) = (Ioc 0 N).filter (B ∣ ·) := by
    ext n
    simp only [hT, mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hAB n h2⟩, h2⟩
  have eC : T.filter (C ∣ ·) = (Ioc 0 N).filter (C ∣ ·) := by
    ext n
    simp only [hT, mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hAC n h2⟩, h2⟩
  have eD : T.filter (B ∣ ·) ∩ T.filter (C ∣ ·) = (Ioc 0 N).filter (D ∣ ·) := by
    rw [eB, eC, ← filter_and]
    ext n
    simp only [mem_filter]
    rw [hBC]
  have h1 := card_filter_add_card_filter_not (s := T) (fun n => B ∣ n ∨ C ∣ n)
  have h2 := card_union_add_card_inter (T.filter (B ∣ ·)) (T.filter (C ∣ ·))
  rw [← filter_or, eD, eB, eC] at h2
  rw [e0]
  have h1R := congrArg (Nat.cast : ℕ → ℝ) h1
  have h2R := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h1R h2R
  linarith

/-- `X_i(n) = 1[v_p(n) = ν]` for `i = (p, ν)`. -/
noncomputable def Xi (i : ℕ × ℕ) (n : ℕ) : ℝ := if n.factorization i.1 = i.2 then 1 else 0

/-- `w_i = p^{−ν}(1 − p^{−1})`. -/
noncomputable def wi (i : ℕ × ℕ) : ℝ := 1 / (qi i : ℝ) * (1 - 1 / (i.1 : ℝ))

theorem Xi_nonneg (i : ℕ × ℕ) (n : ℕ) : 0 ≤ Xi i n := by unfold Xi; split_ifs <;> norm_num

theorem wi_nonneg {N : ℕ} {i : ℕ × ℕ} (hi : i ∈ ppIdx N) : 0 ≤ wi i := by
  have hp := (mem_ppIdx.mp hi).1
  have hp2 : (2 : ℝ) ≤ i.1 := by exact_mod_cast hp.two_le
  unfold wi
  have : 0 ≤ 1 - 1 / (i.1 : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  positivity

theorem wi_le {N : ℕ} {i : ℕ × ℕ} (hi : i ∈ ppIdx N) : wi i ≤ 1 / (qi i : ℝ) := by
  have hp := (mem_ppIdx.mp hi).1
  have hp2 : (2 : ℝ) ≤ i.1 := by exact_mod_cast hp.two_le
  have hq : (0 : ℝ) < qi i := by exact_mod_cast qi_pos hi
  unfold wi
  have : 0 ≤ 1 / (i.1 : ℝ) := by positivity
  have h1 : 0 ≤ 1 / (qi i : ℝ) := by positivity
  nlinarith

/-- **One valuation.** `N w_i − 1 ≤ #{n ≤ N : v_p(n) = ν} ≤ N/p^ν`. -/
theorem sum_Xi_bounds {N : ℕ} {i : ℕ × ℕ} (hi : i ∈ ppIdx N) :
    (N : ℝ) * wi i - 1 ≤ ∑ n ∈ Ioc 0 N, Xi i n ∧ ∑ n ∈ Ioc 0 N, Xi i n ≤ (N : ℝ) / qi i := by
  obtain ⟨hp, hν, -⟩ := mem_ppIdx.mp hi
  have hsum : ∑ n ∈ Ioc 0 N, Xi i n =
      (((Ioc 0 N).filter (fun n => i.1 ^ i.2 ∣ n ∧ ¬ i.1 ^ (i.2 + 1) ∣ n ∧
        ¬ i.1 ^ (i.2 + 1) ∣ n)).card : ℝ) := by
    unfold Xi
    rw [sum_boole]
    congr 2
    refine filter_congr fun n hn => ?_
    rw [factorization_eq_iff hp (by have := (mem_Ioc.mp hn).1; omega)]
    tauto
  have hdvd : ∀ n, i.1 ^ (i.2 + 1) ∣ n → i.1 ^ i.2 ∣ n := fun n h =>
    (pow_dvd_pow i.1 (Nat.le_succ _)).trans h
  rw [hsum, card_ie N hdvd hdvd (fun n => and_self_iff)]
  obtain ⟨l1, u1⟩ := dcount_bounds N (pow_pos hp.pos i.2)
  obtain ⟨l2, u2⟩ := dcount_bounds N (pow_pos hp.pos (i.2 + 1))
  have hp0 : (0 : ℝ) < i.1 := by exact_mod_cast hp.pos
  have e1 : ((i.1 ^ i.2 : ℕ) : ℝ) = (qi i : ℝ) := rfl
  have e2 : (N : ℝ) / ((i.1 ^ (i.2 + 1) : ℕ) : ℝ) = (N : ℝ) / qi i - (N : ℝ) * wi i := by
    unfold wi qi
    push_cast
    field_simp
    ring
  rw [e1] at l1 u1
  rw [e2] at l2 u2
  constructor <;> linarith

/-- **Two valuations at different primes.**
`#{n ≤ N : v_p(n) = ν, v_r(n) = μ} ≤ N w_i w_j + 2` for `p ≠ r`. -/
theorem sum_XiXj_le {N : ℕ} {i j : ℕ × ℕ} (hi : i ∈ ppIdx N) (hj : j ∈ ppIdx N)
    (hpr : i.1 ≠ j.1) : ∑ n ∈ Ioc 0 N, Xi i n * Xi j n ≤ (N : ℝ) * (wi i * wi j) + 2 := by
  obtain ⟨p, ν⟩ := i
  obtain ⟨r, μ⟩ := j
  obtain ⟨hp, hν, -⟩ := mem_ppIdx.mp hi
  obtain ⟨hr, hμ, -⟩ := mem_ppIdx.mp hj
  simp only at hpr hp hr hν hμ
  have cop : ∀ x y : ℕ, (p ^ x).Coprime (r ^ y) := fun x y => Nat.coprime_pow_primes x y hp hr hpr
  have hsum : ∑ n ∈ Ioc 0 N, Xi (p, ν) n * Xi (r, μ) n =
      (((Ioc 0 N).filter (fun n => p ^ ν * r ^ μ ∣ n ∧ ¬ p ^ (ν + 1) * r ^ μ ∣ n ∧
        ¬ p ^ ν * r ^ (μ + 1) ∣ n)).card : ℝ) := by
    unfold Xi
    simp only [ite_zero_mul_ite_zero, mul_one]
    rw [sum_boole]
    congr 2
    refine filter_congr fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (mem_Ioc.mp hn).1; omega
    rw [factorization_eq_iff hp hn0, factorization_eq_iff hr hn0, mul_dvd_iff_of_coprime (cop _ _),
      mul_dvd_iff_of_coprime (cop _ _), mul_dvd_iff_of_coprime (cop _ _)]
    tauto
  have hdp : ∀ n, p ^ (ν + 1) ∣ n → p ^ ν ∣ n := fun n h => (pow_dvd_pow p (Nat.le_succ _)).trans h
  have hdr : ∀ n, r ^ (μ + 1) ∣ n → r ^ μ ∣ n := fun n h => (pow_dvd_pow r (Nat.le_succ _)).trans h
  have hAB : ∀ n, p ^ (ν + 1) * r ^ μ ∣ n → p ^ ν * r ^ μ ∣ n := fun n h => by
    rw [mul_dvd_iff_of_coprime (cop _ _)] at h ⊢; exact ⟨hdp n h.1, h.2⟩
  have hAC : ∀ n, p ^ ν * r ^ (μ + 1) ∣ n → p ^ ν * r ^ μ ∣ n := fun n h => by
    rw [mul_dvd_iff_of_coprime (cop _ _)] at h ⊢; exact ⟨h.1, hdr n h.2⟩
  have hBC : ∀ n, p ^ (ν + 1) * r ^ μ ∣ n ∧ p ^ ν * r ^ (μ + 1) ∣ n ↔
      p ^ (ν + 1) * r ^ (μ + 1) ∣ n := fun n => by
    rw [mul_dvd_iff_of_coprime (cop _ _), mul_dvd_iff_of_coprime (cop _ _),
      mul_dvd_iff_of_coprime (cop _ _)]
    constructor
    · rintro ⟨⟨h1, -⟩, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hdr n h2⟩, hdp n h1, h2⟩
  rw [hsum, card_ie N hAB hAC hBC]
  have hpos : ∀ x y : ℕ, 0 < p ^ x * r ^ y := fun x y =>
    Nat.mul_pos (pow_pos hp.pos x) (pow_pos hr.pos y)
  obtain ⟨-, u1⟩ := dcount_bounds N (hpos ν μ)
  obtain ⟨l2, -⟩ := dcount_bounds N (hpos (ν + 1) μ)
  obtain ⟨l3, -⟩ := dcount_bounds N (hpos ν (μ + 1))
  obtain ⟨-, u4⟩ := dcount_bounds N (hpos (ν + 1) (μ + 1))
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have e : (N : ℝ) * (wi (p, ν) * wi (r, μ)) =
      (N : ℝ) / ((p ^ ν * r ^ μ : ℕ) : ℝ) - (N : ℝ) / ((p ^ (ν + 1) * r ^ μ : ℕ) : ℝ) -
        (N : ℝ) / ((p ^ ν * r ^ (μ + 1) : ℕ) : ℝ) +
        (N : ℝ) / ((p ^ (ν + 1) * r ^ (μ + 1) : ℕ) : ℝ) := by
    unfold wi qi
    push_cast
    field_simp
    ring
  rw [e]
  linarith

/-- **The pair counts.**
`∑_{n ≤ N} X_i(n) X_j(n) ≤ 1[i = j] N/q_i + N w_i w_j + 2·1[q_iq_j ≤ N]`. -/
theorem cij_le {N : ℕ} {i j : ℕ × ℕ} (hi : i ∈ ppIdx N) (hj : j ∈ ppIdx N) :
    ∑ n ∈ Ioc 0 N, Xi i n * Xi j n ≤
      (if i = j then (N : ℝ) / qi i else 0) + N * (wi i * wi j) +
        2 * (if qi i * qi j ≤ N then 1 else 0) := by
  have hw := mul_nonneg (wi_nonneg hi) (wi_nonneg hj)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNw : 0 ≤ (N : ℝ) * (wi i * wi j) := mul_nonneg hN hw
  have hite : (0 : ℝ) ≤ 2 * (if qi i * qi j ≤ N then 1 else 0) := by split_ifs <;> norm_num
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    have hXX : ∀ n, Xi i n * Xi i n = Xi i n := fun n => by unfold Xi; split_ifs <;> norm_num
    simp only [hXX]
    linarith [(sum_Xi_bounds hi).2]
  simp only [hij, ↓reduceIte]
  by_cases hpr : i.1 = j.1
  · -- Same prime, different exponents: the product vanishes.
    have hν : i.2 ≠ j.2 := fun h => hij (Prod.ext hpr h)
    have h0 : ∀ n ∈ Ioc 0 N, Xi i n * Xi j n = 0 := fun n _ => by
      unfold Xi
      by_cases h1 : n.factorization i.1 = i.2
      · have h2 : ¬ n.factorization j.1 = j.2 := by rw [← hpr, h1]; exact hν
        simp [h2]
      · simp [h1]
    rw [sum_eq_zero h0]
    linarith
  by_cases hqq : qi i * qi j ≤ N
  · simp only [hqq, ↓reduceIte]
    linarith [sum_XiXj_le hi hj hpr]
  · simp only [hqq, ↓reduceIte]
    -- `q_i q_j ∣ n` would force `n > N`.
    have h0 : ∀ n ∈ Ioc 0 N, Xi i n * Xi j n = 0 := fun n hn => by
      obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
      obtain ⟨hp, -, -⟩ := mem_ppIdx.mp hi
      obtain ⟨hr, -, -⟩ := mem_ppIdx.mp hj
      unfold Xi
      split_ifs with h1 h2 <;> try norm_num
      exfalso
      have d1 := ((factorization_eq_iff hp (by omega)).mp h1).1
      have d2 := ((factorization_eq_iff hr (by omega)).mp h2).1
      have d := (Nat.coprime_pow_primes _ _ hp hr hpr).mul_dvd_of_dvd_of_dvd d1 d2
      have := Nat.le_of_dvd hn0 d
      exact hqq (by unfold qi; omega)
    rw [sum_eq_zero h0]
    linarith

/-! ### The core inequality for nonnegative weights -/

/-- **The core.** For weights `g ≥ 0` on the prime powers `p^ν ≤ N`, with `F(n) = ∑ g_i X_i(n)`,
`A = ∑ g_i w_i`, `B² = ∑ g_i²/q_i`, `G = ∑ g_i` and `E = ∑_{q_iq_j ≤ N} g_i g_j`:
`∑_{n≤N} (F(n) − A)² ≤ N B² + 2E + 2AG`. -/
theorem tk_core (N : ℕ) (g : ℕ × ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ n ∈ Ioc 0 N, (∑ i ∈ ppIdx N, g i * Xi i n - ∑ i ∈ ppIdx N, g i * wi i) ^ 2 ≤
      N * ∑ i ∈ ppIdx N, g i ^ 2 / qi i +
      2 * ∑ i ∈ ppIdx N, ∑ j ∈ ppIdx N, g i * g j * (if qi i * qi j ≤ N then 1 else 0) +
      2 * (∑ i ∈ ppIdx N, g i * wi i) * ∑ i ∈ ppIdx N, g i := by
  set I := ppIdx N with hI
  set A := ∑ i ∈ I, g i * wi i with hA
  have hA0 : 0 ≤ A := sum_nonneg fun i hi => mul_nonneg (hg i) (wi_nonneg hi)
  -- Expand the square.
  have hexp : ∑ n ∈ Ioc 0 N, (∑ i ∈ I, g i * Xi i n - A) ^ 2 =
      ∑ n ∈ Ioc 0 N, (∑ i ∈ I, g i * Xi i n) ^ 2 -
        2 * A * ∑ n ∈ Ioc 0 N, ∑ i ∈ I, g i * Xi i n + N * A ^ 2 := by
    have e : ∀ n, (∑ i ∈ I, g i * Xi i n - A) ^ 2 =
        (∑ i ∈ I, g i * Xi i n) ^ 2 - 2 * A * ∑ i ∈ I, g i * Xi i n + A ^ 2 := fun n => by ring
    rw [sum_congr rfl fun n _ => e n, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
  -- The linear term: `∑_n F(n) ≥ N A − G`.
  have hlin : (N : ℝ) * A - ∑ i ∈ I, g i ≤ ∑ n ∈ Ioc 0 N, ∑ i ∈ I, g i * Xi i n := by
    rw [sum_comm, hA, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun i hi => ?_
    rw [← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (sum_Xi_bounds hi).1 (hg i)
    linarith
  -- The quadratic term.
  have hc : ∀ i ∈ I, ∀ j ∈ I, g i * g j * ∑ n ∈ Ioc 0 N, Xi i n * Xi j n ≤
      (if i = j then (N : ℝ) * (g i ^ 2 / qi i) else 0) + N * ((g i * wi i) * (g j * wi j)) +
        2 * (g i * g j * (if qi i * qi j ≤ N then 1 else 0)) := fun i hi j hj => by
    have h := mul_le_mul_of_nonneg_left (cij_le hi hj) (mul_nonneg (hg i) (hg j))
    refine h.trans (le_of_eq ?_)
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      ring
    · simp only [hij, ↓reduceIte]
      ring
  have hδ : ∑ i ∈ I, ∑ j ∈ I, (if i = j then (N : ℝ) * (g i ^ 2 / qi i) else 0) =
      N * ∑ i ∈ I, g i ^ 2 / qi i := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [sum_ite_eq]
    simp [hi]
  have hNA : ∑ i ∈ I, ∑ j ∈ I, (N : ℝ) * ((g i * wi i) * (g j * wi j)) = N * A ^ 2 := by
    rw [sq, hA, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
  have hquad : ∑ n ∈ Ioc 0 N, (∑ i ∈ I, g i * Xi i n) ^ 2 ≤
      N * ∑ i ∈ I, g i ^ 2 / qi i + N * A ^ 2 +
        2 * ∑ i ∈ I, ∑ j ∈ I, g i * g j * (if qi i * qi j ≤ N then 1 else 0) := by
    have e1 : ∀ n, (∑ i ∈ I, g i * Xi i n) ^ 2 =
        ∑ i ∈ I, ∑ j ∈ I, g i * g j * (Xi i n * Xi j n) := fun n => by
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    calc ∑ n ∈ Ioc 0 N, (∑ i ∈ I, g i * Xi i n) ^ 2
        = ∑ i ∈ I, ∑ j ∈ I, g i * g j * ∑ n ∈ Ioc 0 N, Xi i n * Xi j n := by
          rw [sum_congr rfl fun n _ => e1 n, sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [sum_comm]
          exact sum_congr rfl fun j _ => (mul_sum _ _ _).symm
      _ ≤ ∑ i ∈ I, ∑ j ∈ I, ((if i = j then (N : ℝ) * (g i ^ 2 / qi i) else 0) +
            N * ((g i * wi i) * (g j * wi j)) +
            2 * (g i * g j * (if qi i * qi j ≤ N then 1 else 0))) :=
          sum_le_sum fun i hi => sum_le_sum fun j hj => hc i hi j hj
      _ = N * ∑ i ∈ I, g i ^ 2 / qi i + N * A ^ 2 +
            2 * ∑ i ∈ I, ∑ j ∈ I, g i * g j * (if qi i * qi j ≤ N then 1 else 0) := by
          rw [← hδ, ← hNA, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  rw [hexp]
  have h2 := mul_le_mul_of_nonneg_left hlin (by linarith : (0 : ℝ) ≤ 2 * A)
  linarith

/-! ### Counting prime powers -/

/-- `(log y)² ≤ 16√y` for `y ≥ 1`. -/
theorem log_sq_le_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 16 * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  set t := y ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hy0 _
  have hlog : Real.log y = 4 * Real.log t := by rw [ht, Real.log_rpow hy0]; ring
  have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
  have h2 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hsq : t ^ 2 = Real.sqrt y := by
    rw [ht, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have h3 : Real.log y ≤ 4 * t := by linarith
  nlinarith

/-- **Chebyshev for prime powers.** `#{p^ν ≤ Y} · log 2Y ≤ 58Y`: the primes contribute `5Y/log Y`
(Lemma 2.1(d)), and the `p^ν` with `ν ≥ 2` have `p ≤ √Y` and `ν ≤ log₂ Y`. -/
theorem card_ppIdx_mul_log_le (Y : ℕ) : ((ppIdx Y).card : ℝ) * Real.log (2 * Y) ≤ 58 * Y := by
  rcases Nat.lt_or_ge Y 2 with hY | hY
  · have : ppIdx Y = ∅ := eq_empty_of_forall_notMem fun i hi => by
      have := two_le_qi hi
      have := qi_le hi
      omega
    rw [this, card_empty, Nat.cast_zero, zero_mul]
    positivity
  have hsub : ppIdx Y ⊆ primesUpTo Y ×ˢ {1} ∪ Icc 1 (Nat.sqrt Y) ×ˢ Icc 1 (Nat.log 2 Y) := by
    rintro ⟨p, ν⟩ hi
    obtain ⟨hp, hν, hle⟩ := mem_ppIdx.mp hi
    simp only at hp hν hle
    rcases Nat.lt_or_ge ν 2 with h1 | h2
    · have : ν = 1 := by omega
      subst this
      exact mem_union_left _ (mem_product.mpr
        ⟨mem_primesUpTo.mpr ⟨hp, by simpa using hle⟩, mem_singleton_self 1⟩)
    · refine mem_union_right _ (mem_product.mpr ⟨mem_Icc.mpr ⟨hp.one_lt.le, Nat.le_sqrt.mpr ?_⟩,
        mem_Icc.mpr ⟨hν, Nat.le_log_of_pow_le (by norm_num) ?_⟩⟩)
      · calc p * p = p ^ 2 := (sq p).symm
          _ ≤ p ^ ν := Nat.pow_le_pow_right hp.pos h2
          _ ≤ Y := hle
      · exact (Nat.pow_le_pow_left hp.two_le ν).trans hle
  have hcard : (ppIdx Y).card ≤ (primesUpTo Y).card + Nat.sqrt Y * Nat.log 2 Y := by
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    rw [card_product, card_product, card_singleton, Nat.card_Icc, Nat.card_Icc, mul_one,
      Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hYR : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith)
  have hπ : ((primesUpTo Y).card : ℝ) * Real.log Y ≤ 5 * Y := by
    have := mertens_d hYR
    rw [Nat.floor_natCast, le_div_iff₀ hlogY] at this
    linarith
  have hs : (Nat.sqrt Y : ℝ) ≤ Real.sqrt Y := Real.nat_sqrt_le_real_sqrt
  have hl : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log Y := by
    have h := Nat.pow_log_le_self 2 (show Y ≠ 0 by omega)
    have hR : (2 : ℝ) ^ (Nat.log 2 Y) ≤ Y := by exact_mod_cast h
    have := Real.log_le_log (by positivity) hR
    rwa [Real.log_pow] at this
  have hsq := log_sq_le_sqrt (show (1 : ℝ) ≤ Y by linarith)
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt (by linarith)
  have hk0 : (0 : ℝ) ≤ Nat.log 2 Y := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ Nat.sqrt Y := Nat.cast_nonneg _
  -- `⌊√Y⌋ ⌊log₂ Y⌋ log Y ≤ 24 Y`.
  have a1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hs0 hlogY.le)
  have a2 := mul_le_mul hs hsq (sq_nonneg _) (Real.sqrt_nonneg _)
  have hskL : 0 ≤ (Nat.sqrt Y : ℝ) * Nat.log 2 Y * Real.log Y :=
    mul_nonneg (mul_nonneg hs0 hk0) hlogY.le
  have a3 := mul_le_mul_of_nonneg_left hl2.le hskL
  have e2 : (Nat.sqrt Y : ℝ) * Nat.log 2 Y * Real.log Y ≤ 24 * Y := by nlinarith
  have hcR : ((ppIdx Y).card : ℝ) ≤ (primesUpTo Y).card + (Nat.sqrt Y : ℝ) * Nat.log 2 Y := by
    exact_mod_cast hcard
  have h29 := mul_le_mul_of_nonneg_right hcR hlogY.le
  have hlog2Y : Real.log (2 * Y) ≤ 2 * Real.log Y := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hYR
    linarith
  have hc0 : (0 : ℝ) ≤ (ppIdx Y).card := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hlog2Y hc0
  nlinarith

/-- `∑_{i ∈ S} 1/q_i ≤ 1 + log M` when every `q_i ≤ M`, since the `q_i` are distinct. -/
theorem sum_inv_qi_le {N M : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ ppIdx N)
    (hM : ∀ i ∈ S, qi i ≤ M) : ∑ i ∈ S, (1 : ℝ) / qi i ≤ 1 + Real.log M := by
  have hinj : Set.InjOn qi (S : Set (ℕ × ℕ)) := (qi_injOn N).mono (by exact_mod_cast hS)
  have himg : ∑ i ∈ S, (1 : ℝ) / qi i = ∑ m ∈ S.image qi, (1 : ℝ) / m :=
    (sum_image (f := fun m : ℕ => (1 : ℝ) / m) fun x hx y hy h => hinj hx hy h).symm
  have hsub : S.image qi ⊆ Icc 1 M := fun m hm => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr ⟨qi_pos (hS hi), hM i hi⟩
  rw [himg]
  calc ∑ m ∈ S.image qi, (1 : ℝ) / m ≤ ∑ m ∈ Icc 1 M, (1 : ℝ) / m :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 1 + Real.log M := by
        have := harmonic_le_one_add_log M
        rw [harmonic_eq_sum_Icc] at this
        push_cast at this
        simpa [one_div] using this

/-- **Cauchy–Schwarz.** `(∑ f)² ≤ (∑ f²/a)(∑ a)` for `a > 0`. -/
theorem sq_sum_le {ι : Type*} (s : Finset ι) (f a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, f i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2 / a i) * ∑ i ∈ s, a i := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun i => f i / Real.sqrt (a i)) (fun i => Real.sqrt (a i))
  have e1 : ∀ i ∈ s, f i / Real.sqrt (a i) * Real.sqrt (a i) = f i := fun i hi =>
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr (ha i hi)).ne'
  have e2 : ∀ i ∈ s, (f i / Real.sqrt (a i)) ^ 2 = f i ^ 2 / a i := fun i hi => by
    rw [div_pow, Real.sq_sqrt (ha i hi).le]
  have e3 : ∀ i ∈ s, Real.sqrt (a i) ^ 2 = a i := fun i hi => Real.sq_sqrt (ha i hi).le
  rwa [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h

/-! ### The error terms -/

/-- **The `AG` term.** `A · G ≤ 10 N B²`. -/
theorem tk_AG {N : ℕ} (hN : 2 ≤ N) (g : ℕ × ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (∑ i ∈ ppIdx N, g i * wi i) * (∑ i ∈ ppIdx N, g i) ≤
      10 * N * ∑ i ∈ ppIdx N, g i ^ 2 / qi i := by
  set I := ppIdx N with hI
  set B2 := ∑ i ∈ I, g i ^ 2 / qi i with hB2
  set A := ∑ i ∈ I, g i * wi i with hA
  set G := ∑ i ∈ I, g i with hG
  have hq : ∀ i ∈ I, (0 : ℝ) < qi i := fun i hi => by exact_mod_cast qi_pos hi
  have hB0 : 0 ≤ B2 := sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hq i hi).le
  have hA0 : 0 ≤ A := sum_nonneg fun i hi => mul_nonneg (hg i) (wi_nonneg hi)
  have hG0 : 0 ≤ G := sum_nonneg fun i _ => hg i
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hL2 : 0 < Real.log (2 * N) := Real.log_pos (by linarith)
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  -- `A² ≤ B²(1 + log N)`.
  have hA1 : A ≤ ∑ i ∈ I, g i / qi i := sum_le_sum fun i hi => by
    have := mul_le_mul_of_nonneg_left (wi_le hi) (hg i)
    rwa [mul_one_div] at this
  have hA2 : A ^ 2 ≤ B2 * (1 + Real.log N) := by
    have h := sq_sum_le I (fun i => g i / qi i) (fun i => 1 / (qi i : ℝ))
      (fun i hi => by have := hq i hi; positivity)
    have e : ∀ i ∈ I, (g i / qi i) ^ 2 / (1 / (qi i : ℝ)) = g i ^ 2 / qi i := fun i hi => by
      have := (hq i hi).ne'
      field_simp
    rw [sum_congr rfl e] at h
    have hH := sum_inv_qi_le (S := I) (M := N) subset_rfl fun i hi => qi_le hi
    calc A ^ 2 ≤ (∑ i ∈ I, g i / qi i) ^ 2 := pow_le_pow_left₀ hA0 hA1 2
      _ ≤ _ := h
      _ ≤ B2 * (1 + Real.log N) := mul_le_mul_of_nonneg_left hH hB0
  -- `G² log 2N ≤ 58 B² N²`.
  have hG2 : G ^ 2 * Real.log (2 * N) ≤ B2 * (58 * N ^ 2) := by
    have h := sq_sum_le I g (fun i => (qi i : ℝ)) hq
    have hT : ∑ i ∈ I, (qi i : ℝ) ≤ N * I.card := by
      calc ∑ i ∈ I, (qi i : ℝ) ≤ ∑ i ∈ I, (N : ℝ) :=
            sum_le_sum fun i hi => by exact_mod_cast qi_le hi
        _ = N * I.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
    have hc := card_ppIdx_mul_log_le N
    have h1 : G ^ 2 ≤ B2 * (N * I.card) := h.trans (mul_le_mul_of_nonneg_left hT hB0)
    have h2 := mul_le_mul_of_nonneg_right h1 hL2.le
    have h3 := mul_le_mul_of_nonneg_left hc (mul_nonneg hB0 (Nat.cast_nonneg N))
    linarith
  -- `(1 + log N) log 2 ≤ log 2N`.
  have s3 : (1 + Real.log N) * Real.log 2 ≤ Real.log (2 * N) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    nlinarith
  have s1 : (A * G) ^ 2 * Real.log (2 * N) ≤ B2 * (1 + Real.log N) * (B2 * (58 * N ^ 2)) := by
    rw [mul_pow, mul_assoc]
    exact mul_le_mul hA2 hG2 (mul_nonneg (sq_nonneg _) hL2.le) (mul_nonneg hB0 (by linarith))
  have s4 : (A * G) ^ 2 * Real.log 2 ≤ 58 * (B2 * N) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right s1 (by linarith : (0 : ℝ) ≤ Real.log 2)
    have h2 := mul_le_mul_of_nonneg_left s3
      (by positivity : (0 : ℝ) ≤ B2 * (B2 * (58 * N ^ 2)))
    have h3 : (A * G) ^ 2 * Real.log 2 * Real.log (2 * N) ≤
        58 * (B2 * N) ^ 2 * Real.log (2 * N) := by linarith
    exact le_of_mul_le_mul_right h3 hL2
  have hAG0 : 0 ≤ A * G := mul_nonneg hA0 hG0
  have s5 : (A * G) ^ 2 ≤ (10 * N * B2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hl2.le (sq_nonneg (A * G))
    nlinarith [sq_nonneg (B2 * N)]
  exact (pow_le_pow_iff_left₀ hAG0 (by positivity) two_ne_zero).mp s5

/-- For `q_i² ≤ N`: `q_i ∑_{q_iq_j ≤ N} q_j ≤ 116 N²/(q_i log N)`, since the `q_j ≤ N/q_i` number
`≤ 58 (N/q_i)/log(2N/q_i)` and `2⌊N/q_i⌋ > √N`. -/
theorem sum_q_le {N : ℕ} (hN : 2 ≤ N) {i : ℕ × ℕ} (hi : i ∈ ppIdx N) (hii : qi i * qi i ≤ N) :
    (qi i : ℝ) * ∑ j ∈ ppIdx N, (qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0) ≤
      116 * N ^ 2 / (qi i * Real.log N) := by
  set Y := N / qi i with hY
  have hq0 : 0 < qi i := qi_pos hi
  have hqR : (0 : ℝ) < qi i := by exact_mod_cast hq0
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hsum : ∑ j ∈ ppIdx N, (qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0) ≤
      Y * (ppIdx Y).card := by
    have e : ∑ j ∈ ppIdx N, (qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0) =
        ∑ j ∈ (ppIdx N).filter (fun j => qi j ≤ Y), (qi j : ℝ) := by
      rw [sum_filter]
      refine sum_congr rfl fun j _ => ?_
      have hiff : qi i * qi j ≤ N ↔ qi j ≤ Y := by rw [hY, Nat.le_div_iff_mul_le hq0, mul_comm]
      by_cases h : qi i * qi j ≤ N
      · simp [h, hiff.mp h]
      · simp [h, mt hiff.mpr h]
    rw [e]
    have hsub : (ppIdx N).filter (fun j => qi j ≤ Y) ⊆ ppIdx Y := fun j hj => by
      obtain ⟨hj, hjY⟩ := mem_filter.mp hj
      obtain ⟨hp, hν, -⟩ := mem_ppIdx.mp hj
      exact mem_ppIdx.mpr ⟨hp, hν, hjY⟩
    calc ∑ j ∈ (ppIdx N).filter (fun j => qi j ≤ Y), (qi j : ℝ)
        ≤ ∑ j ∈ (ppIdx N).filter (fun j => qi j ≤ Y), (Y : ℝ) :=
          sum_le_sum fun j hj => by exact_mod_cast (mem_filter.mp hj).2
      _ = Y * ((ppIdx N).filter (fun j => qi j ≤ Y)).card := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ Y * (ppIdx Y).card :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub) (Nat.cast_nonneg _)
  -- `log 2Y ≥ log N/2`.
  have hsq : qi i ≤ Nat.sqrt N := Nat.le_sqrt.mpr hii
  have hYs : Nat.sqrt N ≤ Y := by
    rw [hY, Nat.le_div_iff_mul_le hq0]
    calc Nat.sqrt N * qi i ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul_left _ hsq
      _ ≤ N := Nat.sqrt_le N
  have hs1 : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
  have hY2 : Real.sqrt N < 2 * (Y : ℝ) := by
    have h1 := Real.real_sqrt_lt_nat_sqrt_succ (a := N)
    have h2 : (Nat.sqrt N : ℝ) ≤ Y := by exact_mod_cast hYs
    have h3 : (1 : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hs1
    linarith
  have hlog2Y : Real.log N / 2 ≤ Real.log (2 * Y) := by
    rw [← Real.log_sqrt (Nat.cast_nonneg N)]
    exact Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) hY2.le
  have hc := card_ppIdx_mul_log_le Y
  have hc2 : ((ppIdx Y).card : ℝ) * Real.log N ≤ 116 * Y := by
    have := mul_le_mul_of_nonneg_left hlog2Y (Nat.cast_nonneg (ppIdx Y).card)
    linarith
  have hYle : (Y : ℝ) * qi i ≤ N := by exact_mod_cast Nat.div_mul_le_self N (qi i)
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
  rw [le_div_iff₀ (mul_pos hqR hlogN)]
  calc ((qi i : ℝ) * ∑ j ∈ ppIdx N, (qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0)) *
        (qi i * Real.log N)
      ≤ (qi i : ℝ) * (Y * (ppIdx Y).card) * (qi i * Real.log N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hqR.le)
          (mul_nonneg hqR.le hlogN.le)
    _ = (Y * qi i) * qi i * ((ppIdx Y).card * Real.log N) := by ring
    _ ≤ (Y * qi i) * qi i * (116 * Y) :=
        mul_le_mul_of_nonneg_left hc2 (mul_nonneg (mul_nonneg hY0 hqR.le) hqR.le)
    _ = 116 * (Y * qi i) ^ 2 := by ring
    _ ≤ 116 * N ^ 2 := by
        have := pow_le_pow_left₀ (mul_nonneg hY0 hqR.le) hYle 2
        linarith

/-- **The `E` term.** `∑_{q_iq_j ≤ N} g_i g_j ≤ 22 N B²`. -/
theorem tk_E {N : ℕ} (hN : 2 ≤ N) (g : ℕ × ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ ppIdx N, ∑ j ∈ ppIdx N, g i * g j * (if qi i * qi j ≤ N then 1 else 0) ≤
      22 * N * ∑ i ∈ ppIdx N, g i ^ 2 / qi i := by
  set I := ppIdx N with hI
  set B2 := ∑ i ∈ I, g i ^ 2 / qi i with hB2
  have hq : ∀ i ∈ I, (0 : ℝ) < qi i := fun i hi => by exact_mod_cast qi_pos hi
  have hB0 : 0 ≤ B2 := sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hq i hi).le
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogN2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  set P := (I ×ˢ I).filter (fun k => qi k.1 * qi k.2 ≤ N) with hP
  have hconv : ∀ F : ℕ × ℕ → ℕ × ℕ → ℝ,
      ∑ i ∈ I, ∑ j ∈ I, F i j * (if qi i * qi j ≤ N then 1 else 0) = ∑ k ∈ P, F k.1 k.2 := by
    intro F
    rw [hP, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    dsimp only
    split_ifs <;> simp
  have hE : ∑ i ∈ I, ∑ j ∈ I, g i * g j * (if qi i * qi j ≤ N then 1 else 0) =
      ∑ k ∈ P, g k.1 * g k.2 := hconv fun i j => g i * g j
  have hPpos : ∀ k ∈ P, (0 : ℝ) < (qi k.1 : ℝ) * qi k.2 := fun k hk => by
    obtain ⟨hk, -⟩ := mem_filter.mp hk
    obtain ⟨h1, h2⟩ := mem_product.mp hk
    exact mul_pos (hq _ h1) (hq _ h2)
  have hCS := sq_sum_le P (fun k => g k.1 * g k.2) (fun k => (qi k.1 : ℝ) * qi k.2) hPpos
  have hB4 : ∑ k ∈ P, (g k.1 * g k.2) ^ 2 / ((qi k.1 : ℝ) * qi k.2) ≤ B2 ^ 2 := by
    calc ∑ k ∈ P, (g k.1 * g k.2) ^ 2 / ((qi k.1 : ℝ) * qi k.2)
        ≤ ∑ k ∈ I ×ˢ I, (g k.1 * g k.2) ^ 2 / ((qi k.1 : ℝ) * qi k.2) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k hk _ => by
            obtain ⟨h1, h2⟩ := mem_product.mp hk
            have := hq _ h1
            have := hq _ h2
            positivity
      _ = B2 ^ 2 := by
          rw [sq B2, hB2, sum_mul_sum, sum_product]
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          dsimp only
          rw [mul_pow, mul_div_mul_comm]
  -- `W = ∑_{q_iq_j ≤ N} q_i q_j ≤ 464 N²`.
  have hW : ∑ k ∈ P, (qi k.1 : ℝ) * qi k.2 ≤ 464 * N ^ 2 := by
    rw [← hconv fun i j => (qi i : ℝ) * qi j]
    have hsplit : ∀ i ∈ I, ∀ j ∈ I,
        (qi i : ℝ) * qi j * (if qi i * qi j ≤ N then 1 else 0) ≤
          (if qi i * qi i ≤ N then 1 else 0) *
              ((qi i : ℝ) * ((qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0))) +
            (if qi j * qi j ≤ N then 1 else 0) *
              ((qi j : ℝ) * ((qi i : ℝ) * (if qi j * qi i ≤ N then 1 else 0))) := by
      intro i hi j hj
      have hi0 := hq i hi
      have hj0 := hq j hj
      by_cases h : qi i * qi j ≤ N
      · have h' : qi j * qi i ≤ N := by rwa [mul_comm]
        rcases le_total (qi i) (qi j) with hij | hij
        · have hii : qi i * qi i ≤ N := (Nat.mul_le_mul_left _ hij).trans h
          have hc : (0 : ℝ) ≤ if qi j * qi j ≤ N then 1 else 0 := by split_ifs <;> norm_num
          simp only [h, h', hii, ↓reduceIte, mul_one, one_mul]
          nlinarith [mul_pos hi0 hj0]
        · have hjj : qi j * qi j ≤ N := (Nat.mul_le_mul_left _ hij).trans h'
          have hc : (0 : ℝ) ≤ if qi i * qi i ≤ N then 1 else 0 := by split_ifs <;> norm_num
          simp only [h, h', hjj, ↓reduceIte, mul_one, one_mul]
          nlinarith [mul_pos hi0 hj0]
      · have h' : ¬ qi j * qi i ≤ N := by rwa [mul_comm]
        simp [h, h']
    have hsym : ∑ i ∈ I, ∑ j ∈ I, (if qi j * qi j ≤ N then (1 : ℝ) else 0) *
          ((qi j : ℝ) * ((qi i : ℝ) * (if qi j * qi i ≤ N then 1 else 0))) =
        ∑ i ∈ I, ∑ j ∈ I, (if qi i * qi i ≤ N then (1 : ℝ) else 0) *
          ((qi i : ℝ) * ((qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0))) := sum_comm
    have hC0 : 0 ≤ 116 * (N : ℝ) ^ 2 / Real.log N := div_nonneg (by positivity) hlogN.le
    have hW1 : ∑ i ∈ I, ∑ j ∈ I, (if qi i * qi i ≤ N then (1 : ℝ) else 0) *
          ((qi i : ℝ) * ((qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0))) ≤
        116 * N ^ 2 / Real.log N * (1 + Real.log N / 2) := by
      calc _ = ∑ i ∈ I, (if qi i * qi i ≤ N then (1 : ℝ) else 0) *
              ((qi i : ℝ) * ∑ j ∈ I, (qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0)) := by
            refine sum_congr rfl fun i _ => ?_
            rw [mul_sum, mul_sum]
        _ ≤ ∑ i ∈ I, (if qi i * qi i ≤ N then (1 : ℝ) else 0) *
              (116 * N ^ 2 / Real.log N * (1 / qi i)) := by
            refine sum_le_sum fun i hi => ?_
            by_cases h : qi i * qi i ≤ N
            · simp only [h, ↓reduceIte, one_mul]
              calc _ ≤ 116 * (N : ℝ) ^ 2 / (qi i * Real.log N) := sum_q_le hN hi h
                _ = _ := by rw [div_mul_div_comm, mul_one, mul_comm (Real.log (N : ℝ))]
            · simp [h]
        _ = 116 * N ^ 2 / Real.log N *
              ∑ i ∈ I.filter (fun i => qi i * qi i ≤ N), (1 : ℝ) / qi i := by
            rw [mul_sum, sum_filter]
            refine sum_congr rfl fun i _ => ?_
            split_ifs <;> simp
        _ ≤ 116 * N ^ 2 / Real.log N * (1 + Real.log N / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            have hH := sum_inv_qi_le (S := I.filter (fun i => qi i * qi i ≤ N))
              (M := Nat.sqrt N) (filter_subset _ _) fun i hi =>
                Nat.le_sqrt.mpr (mem_filter.mp hi).2
            have hs : Real.log (Nat.sqrt N) ≤ Real.log N / 2 := by
              rw [← Real.log_sqrt (Nat.cast_nonneg N)]
              exact Real.log_le_log (by exact_mod_cast Nat.sqrt_pos.mpr (by omega))
                Real.nat_sqrt_le_real_sqrt
            linarith
    have hfin : 116 * (N : ℝ) ^ 2 / Real.log N * (1 + Real.log N / 2) ≤ 232 * N ^ 2 := by
      have e : 116 * (N : ℝ) ^ 2 / Real.log N * (1 + Real.log N / 2) =
          116 * (N : ℝ) ^ 2 / Real.log N + 58 * N ^ 2 := by
        field_simp
        ring
      have h1 : 116 * (N : ℝ) ^ 2 / Real.log N ≤ 174 * N ^ 2 := by
        rw [div_le_iff₀ hlogN]
        nlinarith [sq_nonneg (N : ℝ)]
      linarith
    calc ∑ i ∈ I, ∑ j ∈ I, (qi i : ℝ) * qi j * (if qi i * qi j ≤ N then 1 else 0)
        ≤ ∑ i ∈ I, ∑ j ∈ I, ((if qi i * qi i ≤ N then 1 else 0) *
              ((qi i : ℝ) * ((qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0))) +
            (if qi j * qi j ≤ N then 1 else 0) *
              ((qi j : ℝ) * ((qi i : ℝ) * (if qi j * qi i ≤ N then 1 else 0)))) :=
          sum_le_sum fun i hi => sum_le_sum fun j hj => hsplit i hi j hj
      _ = 2 * ∑ i ∈ I, ∑ j ∈ I, (if qi i * qi i ≤ N then (1 : ℝ) else 0) *
            ((qi i : ℝ) * ((qi j : ℝ) * (if qi i * qi j ≤ N then 1 else 0))) := by
          simp only [sum_add_distrib]
          rw [hsym]
          ring
      _ ≤ 464 * N ^ 2 := by linarith
  -- `E² ≤ B⁴ W ≤ (22 N B²)²`.
  have hE0 : 0 ≤ ∑ k ∈ P, g k.1 * g k.2 := sum_nonneg fun k _ => mul_nonneg (hg _) (hg _)
  have hW0 : 0 ≤ ∑ k ∈ P, (qi k.1 : ℝ) * qi k.2 := sum_nonneg fun k hk => (hPpos k hk).le
  have hE2 : (∑ k ∈ P, g k.1 * g k.2) ^ 2 ≤ (22 * N * B2) ^ 2 := by
    have h1 := hCS.trans (mul_le_mul hB4 hW (hW0) (sq_nonneg _))
    nlinarith [sq_nonneg (B2 * N)]
  rw [hE]
  exact (pow_le_pow_iff_left₀ hE0 (by positivity) two_ne_zero).mp hE2

/-! ### Assembly -/

/-- `R_g(n) = ∑ g_i X_i(n) − ∑ g_i w_i`. -/
noncomputable def tkR (N : ℕ) (g : ℕ × ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ ppIdx N, g i * Xi i n - ∑ i ∈ ppIdx N, g i * wi i

/-- **Nonnegative weights.** `∑_{n≤N} R_g(n)² ≤ 65 N ∑ g_i²/q_i` for `g ≥ 0` and `N ≥ 2`. -/
theorem tk_nonneg {N : ℕ} (hN : 2 ≤ N) (g : ℕ × ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ n ∈ Ioc 0 N, tkR N g n ^ 2 ≤ 65 * N * ∑ i ∈ ppIdx N, g i ^ 2 / qi i := by
  have h := tk_core N g hg
  have hE := tk_E hN g hg
  have hAG := tk_AG hN g hg
  unfold tkR
  linarith

theorem tkR_sub (N : ℕ) (g h : ℕ × ℕ → ℝ) (n : ℕ) :
    tkR N (fun i => g i - h i) n = tkR N g n - tkR N h n := by
  unfold tkR
  simp only [sub_mul, sum_sub_distrib]
  ring

/-- **Real weights.** `∑_{n≤N} R_u(n)² ≤ 130 N ∑ u_i²/q_i`, by `u = u⁺ − u⁻`. -/
theorem tk_real {N : ℕ} (hN : 2 ≤ N) (u : ℕ × ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, tkR N u n ^ 2 ≤ 130 * N * ∑ i ∈ ppIdx N, u i ^ 2 / qi i := by
  set up : ℕ × ℕ → ℝ := fun i => max (u i) 0 with hup
  set um : ℕ × ℕ → ℝ := fun i => max (-u i) 0 with hum
  have hu : u = fun i => up i - um i := funext fun i => (max_zero_sub_eq_self (u i)).symm
  have hsq : ∀ i, up i ^ 2 + um i ^ 2 = u i ^ 2 := fun i => by
    simp only [hup, hum]
    rcases le_total 0 (u i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have h1 := tk_nonneg hN up fun i => le_max_right _ _
  have h2 := tk_nonneg hN um fun i => le_max_right _ _
  have hpt : ∀ n, tkR N u n ^ 2 ≤ 2 * tkR N up n ^ 2 + 2 * tkR N um n ^ 2 := fun n => by
    rw [hu, tkR_sub]
    nlinarith [sq_nonneg (tkR N up n + tkR N um n)]
  have hB : ∑ i ∈ ppIdx N, u i ^ 2 / qi i =
      ∑ i ∈ ppIdx N, up i ^ 2 / qi i + ∑ i ∈ ppIdx N, um i ^ 2 / qi i := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← add_div, hsq]
  calc ∑ n ∈ Ioc 0 N, tkR N u n ^ 2
      ≤ ∑ n ∈ Ioc 0 N, (2 * tkR N up n ^ 2 + 2 * tkR N um n ^ 2) := sum_le_sum fun n _ => hpt n
    _ = 2 * ∑ n ∈ Ioc 0 N, tkR N up n ^ 2 + 2 * ∑ n ∈ Ioc 0 N, tkR N um n ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 130 * N * ∑ i ∈ ppIdx N, u i ^ 2 / qi i := by rw [hB]; linarith

/-- `A(N) = ∑_{p^ν ≤ N} f(p^ν) p^{−ν}(1 − p^{−1})`. -/
noncomputable def tkA (f : ℕ → ℂ) (N : ℕ) : ℂ := ∑ i ∈ ppIdx N, f (qi i) * (wi i : ℂ)

/-- `B(N)² = ∑_{p^ν ≤ N} |f(p^ν)|² p^{−ν}`. -/
noncomputable def tkB2 (f : ℕ → ℂ) (N : ℕ) : ℝ := ∑ i ∈ ppIdx N, ‖f (qi i)‖ ^ 2 / qi i

/-- **Turán–Kubilius, integer form.** For additive `f : ℕ → ℂ` and `N ≥ 2`,
`∑_{n ≤ N} |f(n) − A(N)|² ≤ 130 N B(N)²`. -/
theorem turan_kubilius_nat {f : ℕ → ℂ} (hf : IsAdditive f) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ioc 0 N, ‖f n - tkA f N‖ ^ 2 ≤ 130 * N * tkB2 f N := by
  have hpt : ∀ n ∈ Ioc 0 N, ‖f n - tkA f N‖ ^ 2 =
      tkR N (fun i => (f (qi i)).re) n ^ 2 + tkR N (fun i => (f (qi i)).im) n ^ 2 := by
    intro n hn
    have e : f n - tkA f N = ∑ i ∈ ppIdx N, f (qi i) * ((Xi i n - wi i : ℝ) : ℂ) := by
      rw [hf.eq_sum_ppIdx hn, tkA, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      unfold Xi
      split_ifs <;> push_cast <;> ring
    rw [e, Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, zero_add]
    unfold tkR
    simp only [mul_sub, sum_sub_distrib]
    ring
  rw [sum_congr rfl hpt, sum_add_distrib]
  have h1 := tk_real hN fun i => (f (qi i)).re
  have h2 := tk_real hN fun i => (f (qi i)).im
  have hB : tkB2 f N = ∑ i ∈ ppIdx N, (f (qi i)).re ^ 2 / qi i +
      ∑ i ∈ ppIdx N, (f (qi i)).im ^ 2 / qi i := by
    unfold tkB2
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← add_div, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hB]
  linarith

/-- **Remark 2.5 (Turán–Kubilius).** For every complex additive `f` and every real `x ≥ 2`,
`∑_{n≤x} |f(n) − A(x)|² ≤ 130 x B(x)²`, with `A(x)` and `B(x)²` summed over the prime powers
`p^ν ≤ x`. -/
theorem turan_kubilius {f : ℕ → ℂ} (hf : IsAdditive f) {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, ‖f n - tkA f ⌊x⌋₊‖ ^ 2 ≤ 130 * x * tkB2 f ⌊x⌋₊ := by
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hIcc : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  have hB0 : 0 ≤ tkB2 f ⌊x⌋₊ := sum_nonneg fun i _ => by positivity
  rw [hIcc]
  calc _ ≤ 130 * (⌊x⌋₊ : ℝ) * tkB2 f ⌊x⌋₊ := turan_kubilius_nat hf hN
    _ ≤ 130 * x * tkB2 f ⌊x⌋₊ := by gcongr

/-- **Remark 2.5**, as stated: there is an absolute constant `C` (here `C = 130`). -/
theorem remark_2_5 : ∃ C : ℝ, ∀ f : ℕ → ℂ, IsAdditive f → ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Icc 1 ⌊x⌋₊, ‖f n - tkA f ⌊x⌋₊‖ ^ 2 ≤ C * x * tkB2 f ⌊x⌋₊ :=
  ⟨130, fun _ hf _ hx => turan_kubilius hf hx⟩

end HubRemoval
