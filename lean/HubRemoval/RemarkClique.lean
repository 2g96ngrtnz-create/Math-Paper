import HubRemoval.Mertens2
import HubRemoval.FibreCount
import HubRemoval.Doubling
import HubRemoval.Asymptotics

/-!
# Remark 7.2 (Why a hub clique does not suffice for `θ > 1/3`)

The remark says that, for `1/3 < θ < 1/2`, integers `m = p₁p₂p₃s` with primes
`p_i ∈ (N^{1/4}, N^{1/3}]` and a small cofactor `s` lie in `F₁`, have no divisor in
`(K, N^{1/2−δ}]`, and number `≫ N` "by a routine Mertens-type triple sum, which we do not write
out". Here the triple sum is written out.

**The obstruction set.** Fix `0 < γ < 1/4`. Split `(N^{(1−γ)/3}, N^{1/3}]` into three slices
`(N^{lo j}, N^{lo (j+1)}]` with `lo j = (1 − γ)/3 + jγ/9` (`slice`). Let `obst N γ` be the set of
`m = p₁p₂p₃s ≤ N` with `p_j` a prime in slice `j` and `s ≥ 1` (`tuples`, `obst`). Then:
* `p₁ < p₂ < p₃`, `p₁p₂p₃ > N^{1−γ}` and `s < N^γ` (`tuple_bounds`);
* `m` determines `(p₁, p₂, p₃, s)` (`prod4_injOn`);
* **the count**: `#obst ≥ cN` for large `N`, with `c > 0` depending on `γ` (`card_obst_ge`). Since
  `p₁p₂p₃ > N^{1−γ}`, the cofactor ranges over all of `[1, N/(p₁p₂p₃)]`, so
  `#obst = ∑ ⌊N/(p₁p₂p₃)⌋ ≥ (N/2) ∏_j ∑_{p ∈ slice j} 1/p`, and each factor tends to
  `log(lo (j+1)/lo j) > 0` by Lemma 2.1(b);
* every divisor `d` of `m` is a multiple of some `p_ip_j` or divides some `p_k s`
  (`dvd_three_primes`). So `d > √N` or `d < N^{1/3+γ}`.

**Remark 7.2** (`remark_7_2`). If `1/3 < θ < 1/2` and `log(K + 1)/log N → θ`, there is `c > 0` such
that for large `N` at least `cN` elements of `F₁` have no divisor in `(K, √N]`, hence none in
`(K, N^{1/2−δ}]`. Here `γ = (θ − 1/3)/3`.

**The way around it** (`obst_goodSet`). For `m ∈ obst`, the three divisors `m/p_i = p_jp_ks` are
distinct and lie in `S_M` for `M = N^{1−2δ}`, provided `(2 + γ)/3 ≤ 1 − 2δ`,
`2(K + 1)N^{1/3} ≤ M` and `K < N^{2(1−γ)/3}`; and `m ∈ S_M` itself if `m ≤ M`. So `s(m) ≥ 3`, and
`m` attaches as in Lemma 4.4.
-/

namespace HubRemoval

open Finset Filter Topology

/-! ### Primes in a range, and the divisors of `p₁p₂p₃s` -/

/-- The primes in `(y, w]`. -/
noncomputable def primesIn (y w : ℝ) : Finset ℕ := (primesUpTo ⌊w⌋₊).filter (fun p : ℕ => y < p)

theorem mem_primesIn {y w : ℝ} (hw : 0 ≤ w) {p : ℕ} :
    p ∈ primesIn y w ↔ p.Prime ∧ y < p ∧ (p : ℝ) ≤ w := by
  unfold primesIn
  rw [mem_filter, mem_primesUpTo, Nat.le_floor_iff hw]
  tauto

/-- If `d` is coprime to `x` and `y` and divides `xyz`, it divides `z`. -/
theorem dvd_of_coprime_of_dvd {d x y z : ℕ} (hx : d.Coprime x) (hy : d.Coprime y)
    (h : d ∣ x * y * z) : d ∣ z := by
  have hxy : d.Coprime (x * y) := Nat.Coprime.mul_right hx hy
  exact hxy.dvd_of_dvd_mul_left h

/-- **The divisors of `p₁p₂p₃s`.** For distinct primes `p₁, p₂, p₃`, a divisor `d` of `p₁p₂p₃s` is a
multiple of some `p_ip_j` (`i ≠ j`) or divides some `p_k s`. -/
theorem dvd_three_primes {p₁ p₂ p₃ s d : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (hd : d ∣ p₁ * p₂ * p₃ * s) :
    (p₁ * p₂ ∣ d ∨ p₁ * p₃ ∣ d ∨ p₂ * p₃ ∣ d) ∨ (d ∣ p₁ * s ∨ d ∣ p₂ * s ∨ d ∣ p₃ * s) := by
  have c12 : p₁.Coprime p₂ := (Nat.coprime_primes h₁ h₂).mpr h12
  have c13 : p₁.Coprime p₃ := (Nat.coprime_primes h₁ h₃).mpr h13
  have c23 : p₂.Coprime p₃ := (Nat.coprime_primes h₂ h₃).mpr h23
  have cop : ∀ {p : ℕ}, p.Prime → ¬ p ∣ d → d.Coprime p := fun hp h =>
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm
  have e1 : p₁ * p₂ * p₃ * s = p₂ * p₃ * (p₁ * s) := by ring
  have e2 : p₁ * p₂ * p₃ * s = p₁ * p₃ * (p₂ * s) := by ring
  have e3 : p₁ * p₂ * p₃ * s = p₁ * p₂ * (p₃ * s) := by ring
  by_cases d1 : p₁ ∣ d <;> by_cases d2 : p₂ ∣ d <;> by_cases d3 : p₃ ∣ d
  · exact Or.inl (Or.inl (c12.mul_dvd_of_dvd_of_dvd d1 d2))
  · exact Or.inl (Or.inl (c12.mul_dvd_of_dvd_of_dvd d1 d2))
  · exact Or.inl (Or.inr (Or.inl (c13.mul_dvd_of_dvd_of_dvd d1 d3)))
  · exact Or.inr (Or.inl (dvd_of_coprime_of_dvd (cop h₂ d2) (cop h₃ d3) (e1 ▸ hd)))
  · exact Or.inl (Or.inr (Or.inr (c23.mul_dvd_of_dvd_of_dvd d2 d3)))
  · exact Or.inr (Or.inr (Or.inl (dvd_of_coprime_of_dvd (cop h₁ d1) (cop h₃ d3) (e2 ▸ hd))))
  · exact Or.inr (Or.inr (Or.inr (dvd_of_coprime_of_dvd (cop h₁ d1) (cop h₂ d2) (e3 ▸ hd))))
  · exact Or.inr (Or.inl (dvd_of_coprime_of_dvd (cop h₂ d2) (cop h₃ d3) (e1 ▸ hd)))

/-! ### The obstruction set -/

/-- `lo γ j = (1 − γ)/3 + jγ/9`; so `lo γ 0 = (1 − γ)/3` and `lo γ 3 = 1/3`. -/
noncomputable def lo (γ : ℝ) (j : ℕ) : ℝ := (1 - γ) / 3 + j * (γ / 9)

/-- The `j`-th slice of primes, `(N^{lo j}, N^{lo (j+1)}]`. -/
noncomputable def slice (N : ℕ) (γ : ℝ) (j : ℕ) : Finset ℕ :=
  primesIn ((N : ℝ) ^ lo γ j) ((N : ℝ) ^ lo γ (j + 1))

/-- The tuples `(p₁, p₂, p₃, s)` with `p_j` in slice `j - 1`, `1 ≤ s` and `p₁p₂p₃s ≤ N`. -/
noncomputable def tuples (N : ℕ) (γ : ℝ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (slice N γ 0 ×ˢ slice N γ 1 ×ˢ slice N γ 2 ×ˢ Icc 1 N).filter
    (fun t => t.1 * t.2.1 * t.2.2.1 * t.2.2.2 ≤ N)

/-- `(p₁, p₂, p₃, s) ↦ p₁p₂p₃s`. -/
def prod4 (t : ℕ × ℕ × ℕ × ℕ) : ℕ := t.1 * t.2.1 * t.2.2.1 * t.2.2.2

/-- The obstruction set: the `m = p₁p₂p₃s ≤ N`. -/
noncomputable def obst (N : ℕ) (γ : ℝ) : Finset ℕ := (tuples N γ).image prod4

theorem mem_tuples {N : ℕ} {γ : ℝ} {p₁ p₂ p₃ s : ℕ} :
    (p₁, p₂, p₃, s) ∈ tuples N γ ↔ p₁ ∈ slice N γ 0 ∧ p₂ ∈ slice N γ 1 ∧ p₃ ∈ slice N γ 2 ∧
      s ∈ Icc 1 N ∧ p₁ * p₂ * p₃ * s ≤ N := by
  unfold tuples
  rw [mem_filter, mem_product, mem_product, mem_product]
  tauto

theorem mem_slice {N : ℕ} {γ : ℝ} {j p : ℕ} :
    p ∈ slice N γ j ↔ p.Prime ∧ (N : ℝ) ^ lo γ j < p ∧ (p : ℝ) ≤ (N : ℝ) ^ lo γ (j + 1) :=
  mem_primesIn (by positivity)

theorem lo_zero (γ : ℝ) : lo γ 0 = (1 - γ) / 3 := by simp [lo]

theorem lo_three (γ : ℝ) : lo γ 3 = 1 / 3 := by unfold lo; push_cast; ring

theorem lo_mono {γ : ℝ} (hγ : 0 ≤ γ) {i j : ℕ} (hij : i ≤ j) : lo γ i ≤ lo γ j := by
  unfold lo
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

/-- For `N ≥ 1`, `x ↦ N^x` is monotone. -/
theorem rpow_mono_N {N : ℕ} (hN : 1 ≤ N) {x y : ℝ} (h : x ≤ y) : (N : ℝ) ^ x ≤ (N : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

/-- `(N^{(1−γ)/3})³ = N^{1−γ}`. -/
theorem rpow_third_cube (N : ℕ) (γ : ℝ) :
    ((N : ℝ) ^ ((1 - γ) / 3)) ^ 3 = (N : ℝ) ^ (1 - γ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- **The shape of a tuple.** -/
theorem tuple_bounds {N : ℕ} {γ : ℝ} (hN : 1 ≤ N) (hγ0 : 0 < γ) {p₁ p₂ p₃ s : ℕ}
    (ht : (p₁, p₂, p₃, s) ∈ tuples N γ) :
    p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
    (p₁ : ℝ) ≤ (N : ℝ) ^ lo γ 1 ∧ (N : ℝ) ^ lo γ 1 < p₂ ∧
    (p₂ : ℝ) ≤ (N : ℝ) ^ lo γ 2 ∧ (N : ℝ) ^ lo γ 2 < p₃ ∧
    (N : ℝ) ^ ((1 - γ) / 3) < p₁ ∧ (N : ℝ) ^ ((1 - γ) / 3) < p₂ ∧
    (N : ℝ) ^ ((1 - γ) / 3) < p₃ ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
    (p₂ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧ (p₃ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
    1 ≤ s ∧ p₁ * p₂ * p₃ * s ≤ N ∧ (s : ℝ) < (N : ℝ) ^ γ := by
  obtain ⟨h1, h2, h3, hs, hle⟩ := mem_tuples.mp ht
  obtain ⟨hp₁, l1, u1⟩ := mem_slice.mp h1
  obtain ⟨hp₂, l2, u2⟩ := mem_slice.mp h2
  obtain ⟨hp₃, l3, u3⟩ := mem_slice.mp h3
  have hs1 := (mem_Icc.mp hs).1
  norm_num at u1 u2 u3 l1 l2 l3
  have hγ0' := hγ0.le
  have m01 := rpow_mono_N hN (lo_mono hγ0' (show 0 ≤ 1 by norm_num))
  have m02 := rpow_mono_N hN (lo_mono hγ0' (show 0 ≤ 2 by norm_num))
  have m13 := rpow_mono_N hN (lo_mono hγ0' (show 1 ≤ 3 by norm_num))
  have m23 := rpow_mono_N hN (lo_mono hγ0' (show 2 ≤ 3 by norm_num))
  rw [lo_zero] at l1 m01 m02
  rw [lo_three] at u3 m13 m23
  have hX0 : 0 < (N : ℝ) ^ ((1 - γ) / 3) := by positivity
  refine ⟨hp₁, hp₂, hp₃, u1, l2, u2, l3, l1, by linarith, by linarith, by linarith, by linarith,
    u3, hs1, hle, ?_⟩
  -- `s < N^γ`, since `s · p₁p₂p₃ ≤ N` and `p₁p₂p₃ > N^{1−γ}`.
  have hP : (N : ℝ) ^ (1 - γ) < (p₁ : ℝ) * p₂ * p₃ := by
    rw [← rpow_third_cube, pow_three, ← mul_assoc]
    exact mul_lt_mul'' (mul_lt_mul'' l1 (by linarith) hX0.le hX0.le) (by linarith)
      (by positivity) hX0.le
  have hleR : (p₁ : ℝ) * p₂ * p₃ * s ≤ N := by exact_mod_cast hle
  by_contra hc
  push Not at hc
  have hNγ : (N : ℝ) ^ γ * (N : ℝ) ^ (1 - γ) = N := by
    rw [← Real.rpow_add (by positivity), show γ + (1 - γ) = (1 : ℝ) by ring, Real.rpow_one]
  have hN0 : (0 : ℝ) < (N : ℝ) ^ (1 - γ) := by positivity
  have : (N : ℝ) < (p₁ : ℝ) * p₂ * p₃ * s := by
    calc (N : ℝ) = (N : ℝ) ^ (1 - γ) * (N : ℝ) ^ γ := by rw [mul_comm, hNγ]
      _ < (p₁ : ℝ) * p₂ * p₃ * s :=
          mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hP hc (by positivity) (by positivity)
  linarith

/-- `N^γ ≤ N^{(1−γ)/3}` for `γ ≤ 1/4`. -/
theorem rpow_gamma_le {N : ℕ} (hN : 1 ≤ N) {γ : ℝ} (hγ : γ ≤ 1 / 4) :
    (N : ℝ) ^ γ ≤ (N : ℝ) ^ ((1 - γ) / 3) :=
  rpow_mono_N hN (by linarith)

/-- A prime `q > N^{(1−γ)/3}` dividing `p₁p₂p₃s` is one of the `p_i`. -/
theorem big_prime_dvd {N : ℕ} {γ : ℝ} (hN : 1 ≤ N) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 4)
    {p₁ p₂ p₃ s : ℕ} (ht : (p₁, p₂, p₃, s) ∈ tuples N γ) {q : ℕ} (hq : q.Prime)
    (hqX : (N : ℝ) ^ ((1 - γ) / 3) < q) (hdvd : q ∣ p₁ * p₂ * p₃ * s) :
    q = p₁ ∨ q = p₂ ∨ q = p₃ := by
  obtain ⟨hp₁, hp₂, hp₃, -, -, -, -, -, -, -, -, -, -, hs1, -, hsγ⟩ :=
    tuple_bounds hN hγ0 ht
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
    · rcases (Nat.Prime.dvd_mul hq).mp h' with h'' | h''
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp₁).mp h'')
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp₂).mp h''))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp₃).mp h'))
  · exfalso
    have hqs : (q : ℝ) ≤ s := by exact_mod_cast Nat.le_of_dvd (by omega) h
    linarith [rpow_gamma_le hN hγ]

/-- **`m = p₁p₂p₃s` determines the tuple.** -/
theorem prod4_injOn {N : ℕ} {γ : ℝ} (hN : 1 ≤ N) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 4) :
    Set.InjOn prod4 (tuples N γ : Set (ℕ × ℕ × ℕ × ℕ)) := by
  rintro ⟨p₁, p₂, p₃, s⟩ ht ⟨q₁, q₂, q₃, t⟩ ht' heq
  simp only [mem_coe] at ht ht'
  simp only [prod4] at heq
  obtain ⟨hp₁, hp₂, hp₃, u1, l2, u2, l3, X1, X2, X3, -, -, -, hs1, -, -⟩ :=
    tuple_bounds hN hγ0 ht
  obtain ⟨hq₁, hq₂, hq₃, v1, k2, v2, k3, Y1, Y2, Y3, -, -, -, ht1, -, -⟩ :=
    tuple_bounds hN hγ0 ht'
  have d1 : q₁ ∣ p₁ * p₂ * p₃ * s := heq ▸ ⟨q₂ * q₃ * t, by ring⟩
  have d2 : q₂ ∣ p₁ * p₂ * p₃ * s := heq ▸ ⟨q₁ * q₃ * t, by ring⟩
  have d3 : q₃ ∣ p₁ * p₂ * p₃ * s := heq ▸ ⟨q₁ * q₂ * t, by ring⟩
  have e1 : q₁ = p₁ := by
    rcases big_prime_dvd hN hγ0 hγ ht hq₁ Y1 d1 with h | h | h
    · exact h
    · exfalso; rw [h] at v1; linarith
    · exfalso; rw [h] at v1; linarith
  have e2 : q₂ = p₂ := by
    rcases big_prime_dvd hN hγ0 hγ ht hq₂ Y2 d2 with h | h | h
    · exfalso; rw [h] at k2; linarith
    · exact h
    · exfalso; rw [h] at v2; linarith
  have e3 : q₃ = p₃ := by
    rcases big_prime_dvd hN hγ0 hγ ht hq₃ Y3 d3 with h | h | h
    · exfalso; rw [h] at k3; linarith
    · exfalso; rw [h] at k3; linarith
    · exact h
  subst e1 e2 e3
  have hP : 0 < q₁ * q₂ * q₃ := by
    have := hq₁.pos; have := hq₂.pos; have := hq₃.pos; positivity
  rw [Nat.eq_of_mul_eq_mul_left hP heq]

/-! ### Membership: in `F₁`, and no divisor in `(K, √N]` -/

/-- Every `m ∈ obst N γ` lies in `F₁` and has no divisor `d` with `K < d` and `d² ≤ N`, provided
`N^{1/3+γ} ≤ K < N^{1−γ}` and `N^{1/3} ≤ B`. -/
theorem obst_mem {N K : ℕ} {γ : ℝ} (hN : 1 ≤ N) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 4)
    (hK1 : (N : ℝ) ^ (1 / 3 + γ) ≤ K) (hK2 : (K : ℝ) < (N : ℝ) ^ (1 - γ))
    (hB : (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ)) {m : ℕ} (hm : m ∈ obst N γ) :
    m ∈ smoothFibre N K ∧ ∀ d ∈ m.divisors, ¬ (K < d ∧ d * d ≤ N) := by
  obtain ⟨⟨p₁, p₂, p₃, s⟩, ht, rfl⟩ := mem_image.mp hm
  obtain ⟨hp₁, hp₂, hp₃, u1, l2, u2, l3, X1, X2, X3, T1, T2, T3, hs1, hle, hsγ⟩ :=
    tuple_bounds hN hγ0 ht
  simp only [prod4]
  have hX0 : 0 < (N : ℝ) ^ ((1 - γ) / 3) := by positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hγX := rpow_gamma_le hN hγ
  have hT : (N : ℝ) ^ ((1 - γ) / 3) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := rpow_mono_N hN (by linarith)
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hP : (N : ℝ) ^ (1 - γ) < (p₁ : ℝ) * p₂ * p₃ := by
    rw [← rpow_third_cube, pow_three, ← mul_assoc]
    exact mul_lt_mul'' (mul_lt_mul'' X1 X2 hX0.le hX0.le) X3 (by positivity) hX0.le
  have hm0 : 0 < p₁ * p₂ * p₃ * s := by
    have := hp₁.pos; have := hp₂.pos; have := hp₃.pos; positivity
  refine ⟨?_, ?_⟩
  · -- `m ∈ F₁`: `K < m ≤ N`, and every prime factor is `≤ N^{1/3} ≤ B`.
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, hle⟩, ?_⟩
    · have : (K : ℝ) < (p₁ * p₂ * p₃ * s : ℕ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    · refine Nat.mem_smoothNumbers'.mpr fun q hq hqm => ?_
      have hqB : (q : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ) := by
        by_cases hqX : (N : ℝ) ^ ((1 - γ) / 3) < q
        · rcases big_prime_dvd hN hγ0 hγ ht hq hqX hqm with h | h | h <;> rw [h] <;> linarith
        · push Not at hqX
          linarith
      have : q ≤ N / (K + 1) := by exact_mod_cast hqB
      omega
  · -- No divisor in `(K, √N]`.
    intro d hd ⟨hKd, hdd⟩
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have h12 : p₁ ≠ p₂ := fun h => by rw [h] at u1; linarith
    have m12 := rpow_mono_N hN (lo_mono (γ := γ) hγ0.le (show 1 ≤ 2 by norm_num))
    have h13 : p₁ ≠ p₃ := fun h => by rw [h] at u1; linarith
    have h23 : p₂ ≠ p₃ := fun h => by rw [h] at u2; linarith
    have hddR : (d : ℝ) * d ≤ N := by exact_mod_cast hdd
    have hKdR : (K : ℝ) < d := by exact_mod_cast hKd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    -- `X⁴ ≥ N` for `X = N^{(1−γ)/3}`.
    have hX4 : (N : ℝ) ≤ ((N : ℝ) ^ ((1 - γ) / 3)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := rpow_mono_N hN (by push_cast; linarith)
    have hpair : ∀ a b : ℕ, (N : ℝ) ^ ((1 - γ) / 3) < a → (N : ℝ) ^ ((1 - γ) / 3) < b →
        a * b ∣ d → False := fun a b ha hb hab => by
      have h1 : ((a * b : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd0 hab
      push_cast at h1
      have h2 : (N : ℝ) ^ ((1 - γ) / 3) * (N : ℝ) ^ ((1 - γ) / 3) < d :=
        lt_of_lt_of_le (mul_lt_mul'' ha hb hX0.le hX0.le) h1
      nlinarith
    have hNK : (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ γ = (N : ℝ) ^ (1 / 3 + γ) := by
      rw [← Real.rpow_add (by positivity)]
    have hsingle : ∀ a : ℕ, 0 < a → (a : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) → d ∣ a * s → False :=
        fun a hapos ha h => by
      have ha0 : 0 < a * s := Nat.mul_pos hapos (by omega)
      have h1 : (d : ℝ) ≤ ((a * s : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_dvd ha0 h
      push_cast at h1
      have h2 : (a : ℝ) * s < (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ γ := by
        have ha0' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        calc (a : ℝ) * s ≤ (N : ℝ) ^ (1 / 3 : ℝ) * s := mul_le_mul_of_nonneg_right ha (by linarith)
          _ < (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ γ :=
              mul_lt_mul_of_pos_left hsγ (by positivity)
      linarith
    rcases dvd_three_primes hp₁ hp₂ hp₃ h12 h13 h23 hdm with
      (h | h | h) | (h | h | h)
    · exact hpair _ _ X1 X2 h
    · exact hpair _ _ X1 X3 h
    · exact hpair _ _ X2 X3 h
    · exact hsingle _ hp₁.pos T1 h
    · exact hsingle _ hp₂.pos T2 h
    · exact hsingle _ hp₃.pos T3 h

/-! ### The way around it: `s(m) ≥ 3` -/

/-- Every prime factor of `m = p₁p₂p₃s ∈ obst` is at most `N^{1/3}`. -/
theorem prime_factor_le {N : ℕ} {γ : ℝ} (hN : 1 ≤ N) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 4)
    {p₁ p₂ p₃ s : ℕ} (ht : (p₁, p₂, p₃, s) ∈ tuples N γ) {q : ℕ} (hq : q.Prime)
    (hqm : q ∣ p₁ * p₂ * p₃ * s) : (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, T1, T2, T3, -, -, -⟩ := tuple_bounds hN hγ0 ht
  have hT : (N : ℝ) ^ ((1 - γ) / 3) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := rpow_mono_N hN (by linarith)
  by_cases hqX : (N : ℝ) ^ ((1 - γ) / 3) < q
  · rcases big_prime_dvd hN hγ0 hγ ht hq hqX hqm with h | h | h <;> rw [h] <;> assumption
  · push Not at hqX
    linarith

/-- **The way around the obstruction.** For `m = p₁p₂p₃s ∈ obst N γ` and real `M` with
`N^{(2+γ)/3} ≤ M`, `2(K + 1)N^{1/3} ≤ M` and `K < N^{2(1−γ)/3}`: the three divisors
`m/p₁ = p₂p₃s`, `m/p₂ = p₁p₃s` and `m/p₃ = p₁p₂s` are distinct and lie in `S_M`, and `m ∈ S_M`
if `m ≤ M`. -/
theorem obst_goodSet {N K : ℕ} {γ M : ℝ} (hN : 1 ≤ N) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 4)
    (hM1 : (N : ℝ) ^ ((2 + γ) / 3) ≤ M) (hM2 : 2 * ((K : ℝ) + 1) * (N : ℝ) ^ (1 / 3 : ℝ) ≤ M)
    (hK : (K : ℝ) < (N : ℝ) ^ (2 * (1 - γ) / 3)) {p₁ p₂ p₃ s : ℕ}
    (ht : (p₁, p₂, p₃, s) ∈ tuples N γ) :
    goodSet M K (p₂ * p₃ * s) ∧ goodSet M K (p₁ * p₃ * s) ∧ goodSet M K (p₁ * p₂ * s) ∧
      p₂ * p₃ * s ≠ p₁ * p₃ * s ∧ p₂ * p₃ * s ≠ p₁ * p₂ * s ∧ p₁ * p₃ * s ≠ p₁ * p₂ * s ∧
      (((p₁ * p₂ * p₃ * s : ℕ) : ℝ) ≤ M → goodSet M K (p₁ * p₂ * p₃ * s)) := by
  obtain ⟨hp₁, hp₂, hp₃, u1, l2, u2, l3, X1, X2, X3, -, -, -, hs1, hle, -⟩ :=
    tuple_bounds hN hγ0 ht
  have hX0 : 0 < (N : ℝ) ^ ((1 - γ) / 3) := by positivity
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hleR : (p₁ : ℝ) * p₂ * p₃ * s ≤ N := by exact_mod_cast hle
  have hXX : (N : ℝ) ^ ((1 - γ) / 3) * (N : ℝ) ^ ((1 - γ) / 3) = (N : ℝ) ^ (2 * (1 - γ) / 3) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  have hXY : (N : ℝ) ^ ((1 - γ) / 3) * (N : ℝ) ^ ((2 + γ) / 3) = N := by
    rw [← Real.rpow_add (by positivity), show (1 - γ) / 3 + (2 + γ) / 3 = (1 : ℝ) by ring,
      Real.rpow_one]
  have hK1 : (K : ℝ) < (N : ℝ) ^ (1 - γ) :=
    hK.trans_le (rpow_mono_N hN (by linarith))
  -- Prime factors of divisors of `m`.
  have hprimes : ∀ x : ℕ, x ∣ p₁ * p₂ * p₃ * s →
      ∀ q, q.Prime → q ∣ x → 2 * ((K : ℝ) + 1) * q ≤ M := fun x hx q hq hqx => by
    have := prime_factor_le hN hγ0 hγ ht hq (hqx.trans hx)
    have hK0 : (0 : ℝ) ≤ 2 * ((K : ℝ) + 1) := by positivity
    exact (mul_le_mul_of_nonneg_left this hK0).trans hM2
  -- A pair times `s`: `K < p_j p_k s < N^{(2+γ)/3} ≤ M` when `p_i · (p_j p_k s) ≤ N`.
  have hpair : ∀ a b c : ℕ, (N : ℝ) ^ ((1 - γ) / 3) < a → (N : ℝ) ^ ((1 - γ) / 3) < b →
      (N : ℝ) ^ ((1 - γ) / 3) < c → (c : ℝ) * (a * b * s) ≤ N →
      a * b * s ∣ p₁ * p₂ * p₃ * s → goodSet M K (a * b * s) := fun a b c ha hb hc habc hdvd => by
    refine ⟨?_, ?_, hprimes _ hdvd⟩
    · have hab : (N : ℝ) ^ (2 * (1 - γ) / 3) < a * b := by
        rw [← hXX]; exact mul_lt_mul'' ha hb hX0.le hX0.le
      have : (K : ℝ) < ((a * b * s : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    · push_cast
      have h1 : (N : ℝ) ^ ((1 - γ) / 3) * (a * b * s) < c * (a * b * s) :=
        mul_lt_mul_of_pos_right hc (by
          have : (0 : ℝ) < a := lt_trans hX0 ha
          have : (0 : ℝ) < b := lt_trans hX0 hb
          positivity)
      have h2 : (N : ℝ) ^ ((1 - γ) / 3) * (a * b * s) < (N : ℝ) ^ ((1 - γ) / 3) * M := by
        nlinarith
      exact (lt_of_mul_lt_mul_left h2 hX0.le).le
  have d23 : p₂ * p₃ * s ∣ p₁ * p₂ * p₃ * s := ⟨p₁, by ring⟩
  have d13 : p₁ * p₃ * s ∣ p₁ * p₂ * p₃ * s := ⟨p₂, by ring⟩
  have d12 : p₁ * p₂ * s ∣ p₁ * p₂ * p₃ * s := ⟨p₃, by ring⟩
  have h12 : p₁ < p₂ := by exact_mod_cast u1.trans_lt l2
  have h23 : p₂ < p₃ := by exact_mod_cast u2.trans_lt l3
  have hp₃s : 0 < p₃ * s := Nat.mul_pos hp₃.pos (by omega)
  have hp₂s : 0 < p₂ * s := Nat.mul_pos hp₂.pos (by omega)
  refine ⟨hpair p₂ p₃ p₁ X2 X3 X1 (by linarith) d23, hpair p₁ p₃ p₂ X1 X3 X2 (by linarith) d13,
    hpair p₁ p₂ p₃ X1 X2 X3 (by linarith) d12, ?_, ?_, ?_, ?_⟩
  · intro h
    have : p₂ = p₁ := Nat.eq_of_mul_eq_mul_right hp₃s (by rw [← mul_assoc, ← mul_assoc]; exact h)
    omega
  · intro h
    have : p₃ = p₁ := Nat.eq_of_mul_eq_mul_left hp₂.pos
      (Nat.eq_of_mul_eq_mul_right (by omega : 0 < s) (by linarith [h]))
    omega
  · intro h
    have : p₃ = p₂ := Nat.eq_of_mul_eq_mul_left hp₁.pos
      (Nat.eq_of_mul_eq_mul_right (by omega : 0 < s) (by linarith [h]))
    omega
  · intro hmM
    refine ⟨?_, hmM, hprimes _ dvd_rfl⟩
    have hP : (N : ℝ) ^ (1 - γ) < (p₁ : ℝ) * p₂ * p₃ := by
      rw [← rpow_third_cube, pow_three, ← mul_assoc]
      exact mul_lt_mul'' (mul_lt_mul'' X1 X2 hX0.le hX0.le) X3 (by positivity) hX0.le
    have : (K : ℝ) < ((p₁ * p₂ * p₃ * s : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this

/-! ### The count -/

/-- `#{s ∈ [1, N] : Ps ≤ N} = ⌊N/P⌋` for `P > 0`. -/
theorem card_filter_mul_le {N P : ℕ} (hP : 0 < P) :
    ((Icc 1 N).filter (fun s => P * s ≤ N)).card = N / P := by
  have : (Icc 1 N).filter (fun s => P * s ≤ N) = Icc 1 (N / P) := by
    ext s
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hP).mpr (by rw [mul_comm]; exact h2)⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.le_div_iff_mul_le hP).mp h2
      exact ⟨⟨h1, h2.trans (Nat.div_le_self N P)⟩, by rw [mul_comm]; exact h3⟩
  rw [this, Nat.card_Icc, Nat.add_sub_cancel]

/-- `#tuples = ∑ ⌊N/(p₁p₂p₃)⌋`. -/
theorem card_tuples (N : ℕ) (γ : ℝ) :
    (tuples N γ).card = ∑ p₁ ∈ slice N γ 0, ∑ p₂ ∈ slice N γ 1, ∑ p₃ ∈ slice N γ 2,
      N / (p₁ * p₂ * p₃) := by
  unfold tuples
  rw [card_filter, sum_product]
  refine sum_congr rfl fun p₁ hp₁ => ?_
  rw [sum_product]
  refine sum_congr rfl fun p₂ hp₂ => ?_
  rw [sum_product]
  refine sum_congr rfl fun p₃ hp₃ => ?_
  have hP : 0 < p₁ * p₂ * p₃ := by
    have := (mem_slice.mp hp₁).1.pos
    have := (mem_slice.mp hp₂).1.pos
    have := (mem_slice.mp hp₃).1.pos
    positivity
  rw [← card_filter_mul_le hP, card_filter]

/-- `⌊N/P⌋ ≥ N/(2P)` for `0 < P ≤ N`. -/
theorem div_ge_half {N P : ℕ} (hP : 0 < P) (hPN : P ≤ N) :
    (N : ℝ) / (2 * P) ≤ ((N / P : ℕ) : ℝ) := by
  have h1 : N < P * (N / P + 1) := Nat.lt_mul_div_succ N hP
  have h2 : 1 ≤ N / P := (Nat.le_div_iff_mul_le hP).mpr (by omega)
  have h1R : (N : ℝ) < P * (((N / P : ℕ) : ℝ) + 1) := by exact_mod_cast h1
  have h2R : (1 : ℝ) ≤ ((N / P : ℕ) : ℝ) := by exact_mod_cast h2
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem sum_triple (A B C : Finset ℕ) (f g h : ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a * g b * h c =
      (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

/-- **Lemma 2.1(b) on a slice.** `∑_{p ∈ slice j} 1/p ≥ log(lo (j+1)/lo j) − 18/(lo j · log N)`
once `N^{lo j} ≥ 2`. -/
theorem slice_sum_ge {N : ℕ} {γ : ℝ} {j : ℕ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (h2 : 2 ≤ (N : ℝ) ^ lo γ j) :
    Real.log (lo γ (j + 1) / lo γ j) - 18 / (lo γ j * Real.log N) ≤
      ∑ p ∈ slice N γ j, (1 : ℝ) / p := by
  have hlo0 : 0 < lo γ j := by
    unfold lo
    have := mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (by positivity : (0 : ℝ) ≤ γ / 9)
    linarith
  have hmono : lo γ j ≤ lo γ (j + 1) := lo_mono hγ0.le (Nat.le_succ j)
  have hN1 : (1 : ℝ) < N := by
    by_contra hc
    push Not at hc
    have : (N : ℝ) ^ lo γ j ≤ 1 := Real.rpow_le_one (Nat.cast_nonneg _) hc hlo0.le
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hyw : (N : ℝ) ^ lo γ j ≤ (N : ℝ) ^ lo γ (j + 1) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le hmono
  have h := mertens_b h2 hyw
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have e1 : Real.log ((N : ℝ) ^ lo γ (j + 1)) / Real.log ((N : ℝ) ^ lo γ j) =
      lo γ (j + 1) / lo γ j := by
    rw [Real.log_rpow hN0, Real.log_rpow hN0, mul_div_mul_right _ _ hlogN.ne']
  have e2 : Real.log ((N : ℝ) ^ lo γ j) = lo γ j * Real.log N := Real.log_rpow hN0 _
  rw [e1, e2] at h
  unfold slice primesIn
  linarith [(abs_le.mp h).1]

/-- **The count.** For `0 < γ ≤ 1/4` there is `c > 0` with `#obst N γ ≥ cN` for all large `N`. -/
theorem card_obst_ge {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 4) :
    ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * N ≤ ((obst N γ).card : ℝ) := by
  have hlo0 : 0 < lo γ 0 := by rw [lo_zero]; linarith
  have hlopos : ∀ j, 0 < lo γ j := fun j => lt_of_lt_of_le hlo0 (lo_mono hγ0.le (Nat.zero_le j))
  have hc : ∀ j, 0 < Real.log (lo γ (j + 1) / lo γ j) := fun j => by
    have : lo γ j < lo γ (j + 1) := by unfold lo; push_cast; linarith
    exact Real.log_pos ((one_lt_div (hlopos j)).mpr this)
  obtain ⟨c0, hc0⟩ : ∃ c, c = Real.log (lo γ (0 + 1) / lo γ 0) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c, c = Real.log (lo γ (1 + 1) / lo γ 1) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = Real.log (lo γ (2 + 1) / lo γ 2) := ⟨_, rfl⟩
  have hc0p : 0 < c0 := hc0 ▸ hc 0
  have hc1p : 0 < c1 := hc1 ▸ hc 1
  have hc2p : 0 < c2 := hc2 ▸ hc 2
  refine ⟨c0 * c1 * c2 / 16, by positivity, ?_⟩
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,
    hN.eventually ((tendsto_rpow_atTop hlo0).eventually_ge_atTop 2),
    tendsto_log_nat.eventually_ge_atTop (36 / (lo γ 0 * c0)),
    tendsto_log_nat.eventually_ge_atTop (36 / (lo γ 0 * c1)),
    tendsto_log_nat.eventually_ge_atTop (36 / (lo γ 0 * c2))] with N hN1 hN2 hL0 hL1 hL2
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := by
    have := div_pos (by norm_num : (0 : ℝ) < 36) (mul_pos hlo0 hc0p)
    linarith
  -- The three slice sums are `≥ c_j/2`.
  have hslice : ∀ j, 2 ≤ (N : ℝ) ^ lo γ j → ∀ c, c = Real.log (lo γ (j + 1) / lo γ j) →
      36 / (lo γ 0 * c) ≤ Real.log N → c / 2 ≤ ∑ p ∈ slice N γ j, (1 : ℝ) / p := by
    intro j h2 c hcdef hL
    have hs := slice_sum_ge (N := N) (j := j) hγ0 (by linarith) h2
    rw [← hcdef] at hs
    have hcpos : 0 < c := hcdef ▸ hc j
    have hloj : lo γ 0 ≤ lo γ j := lo_mono hγ0.le (Nat.zero_le j)
    have h18 : 18 / (lo γ j * Real.log N) ≤ c / 2 := by
      rw [div_le_iff₀ (mul_pos (hlopos j) hlogN)]
      rw [div_le_iff₀ (mul_pos hlo0 hcpos)] at hL
      have := mul_le_mul_of_nonneg_left hloj (mul_nonneg hcpos.le hlogN.le)
      nlinarith
    linarith
  have h2j : ∀ j, 2 ≤ (N : ℝ) ^ lo γ j := fun j =>
    hN2.trans (rpow_mono_N hN1 (lo_mono hγ0.le (Nat.zero_le j)))
  have s0 := hslice 0 (h2j 0) c0 hc0 hL0
  have s1 := hslice 1 (h2j 1) c1 hc1 hL1
  have s2 := hslice 2 (h2j 2) c2 hc2 hL2
  -- `#obst = ∑ ⌊N/(p₁p₂p₃)⌋`, and each term is `≥ N/(2p₁p₂p₃)`.
  have hcard : ((obst N γ).card : ℝ) = ∑ p₁ ∈ slice N γ 0, ∑ p₂ ∈ slice N γ 1,
      ∑ p₃ ∈ slice N γ 2, ((N / (p₁ * p₂ * p₃) : ℕ) : ℝ) := by
    rw [obst, card_image_of_injOn (prod4_injOn hN1 hγ0 hγ), card_tuples]
    simp only [Nat.cast_sum]
  have hT : ∀ j ≤ 2, ∀ p ∈ slice N γ j, (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := fun j hj p hp => by
    have := (mem_slice.mp hp).2.2
    have hm : lo γ (j + 1) ≤ lo γ 3 := lo_mono hγ0.le (by omega)
    rw [lo_three] at hm
    exact this.trans (rpow_mono_N hN1 hm)
  have hN13 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hterm : ∀ p₁ ∈ slice N γ 0, ∀ p₂ ∈ slice N γ 1, ∀ p₃ ∈ slice N γ 2,
      (N : ℝ) / 2 * ((1 / p₁ : ℝ) * (1 / p₂) * (1 / p₃)) ≤ ((N / (p₁ * p₂ * p₃) : ℕ) : ℝ) := by
    intro p₁ h₁ p₂ h₂ p₃ h₃
    have q₁ := (mem_slice.mp h₁).1.pos
    have q₂ := (mem_slice.mp h₂).1.pos
    have q₃ := (mem_slice.mp h₃).1.pos
    have hP : 0 < p₁ * p₂ * p₃ := by positivity
    have hPN : p₁ * p₂ * p₃ ≤ N := by
      have t1 := hT 0 (by norm_num) p₁ h₁
      have t2 := hT 1 (by norm_num) p₂ h₂
      have t3 := hT 2 (by norm_num) p₃ h₃
      have : ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ N := by
        push_cast
        rw [← hN13, pow_three, ← mul_assoc]
        exact mul_le_mul (mul_le_mul t1 t2 (by positivity) (by positivity)) t3 (by positivity)
          (by positivity)
      exact_mod_cast this
    have r₁ : (p₁ : ℝ) ≠ 0 := by exact_mod_cast q₁.ne'
    have r₂ : (p₂ : ℝ) ≠ 0 := by exact_mod_cast q₂.ne'
    have r₃ : (p₃ : ℝ) ≠ 0 := by exact_mod_cast q₃.ne'
    have e : (N : ℝ) / 2 * ((1 / p₁ : ℝ) * (1 / p₂) * (1 / p₃)) =
        (N : ℝ) / (2 * ((p₁ * p₂ * p₃ : ℕ) : ℝ)) := by
      push_cast
      field_simp
    rw [e]
    exact div_ge_half hP hPN
  have hS0 : 0 ≤ ∑ p ∈ slice N γ 0, (1 : ℝ) / p := by linarith
  have hS1 : 0 ≤ ∑ p ∈ slice N γ 1, (1 : ℝ) / p := by linarith
  calc c0 * c1 * c2 / 16 * N = (N : ℝ) / 2 * (c0 / 2 * (c1 / 2) * (c2 / 2)) := by ring
    _ ≤ (N : ℝ) / 2 * ((∑ p ∈ slice N γ 0, (1 : ℝ) / p) * (∑ p ∈ slice N γ 1, (1 : ℝ) / p) *
          (∑ p ∈ slice N γ 2, (1 : ℝ) / p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul (mul_le_mul s0 s1 (by positivity) hS0) s2 (by positivity)
          (mul_nonneg hS0 hS1)
    _ = (N : ℝ) / 2 * ∑ p₁ ∈ slice N γ 0, ∑ p₂ ∈ slice N γ 1, ∑ p₃ ∈ slice N γ 2,
          (1 / p₁ : ℝ) * (1 / p₂) * (1 / p₃) := by rw [sum_triple]
    _ = ∑ p₁ ∈ slice N γ 0, ∑ p₂ ∈ slice N γ 1, ∑ p₃ ∈ slice N γ 2,
          (N : ℝ) / 2 * ((1 / p₁ : ℝ) * (1 / p₂) * (1 / p₃)) := by simp only [Finset.mul_sum]
    _ ≤ ∑ p₁ ∈ slice N γ 0, ∑ p₂ ∈ slice N γ 1, ∑ p₃ ∈ slice N γ 2,
          ((N / (p₁ * p₂ * p₃) : ℕ) : ℝ) :=
        sum_le_sum fun p₁ h₁ => sum_le_sum fun p₂ h₂ => sum_le_sum fun p₃ h₃ =>
          hterm p₁ h₁ p₂ h₂ p₃ h₃
    _ = ((obst N γ).card : ℝ) := hcard.symm

/-! ### Remark 7.2 -/

/-- **Remark 7.2.** Let `1/3 < θ < 1/2` and `log(K + 1)/log N → θ`. There is `c > 0` such that for
all large `N`, at least `cN` elements of `F₁` have no divisor in `(K, √N]` (so none in
`(K, N^{1/2−δ}]` for any `δ ≥ 0`): the hub set `(K, N^{1/2−δ}]` misses a positive proportion of
the giant. -/
theorem remark_7_2 {θ : ℝ} (hθ1 : 1 / 3 < θ) (hθ2 : θ < 1 / 2) {K : ℕ → ℕ}
    (hK : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * N ≤
      (((smoothFibre N (K N)).filter
        fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N)).card : ℝ) := by
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = (θ - 1 / 3) / 3 := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have hγ : γ ≤ 1 / 4 := by rw [hγdef]; linarith
  obtain ⟨c, hc, hev⟩ := card_obst_ge hγ0 hγ
  refine ⟨c, hc, ?_⟩
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlow := hK.eventually (lt_mem_nhds (show 1 / 3 + 2 * γ < θ by rw [hγdef]; linarith))
  have hup := hK.eventually (gt_mem_nhds hθ2)
  filter_upwards [hev, hlow, hup, eventually_ge_atTop 2,
    hN.eventually ((tendsto_rpow_atTop hγ0).eventually_ge_atTop 2),
    hN.eventually ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).eventually_ge_atTop 2)]
    with N hcN hlo hhi hN2 hNγ hN6
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hK0 : (0 : ℝ) < (K N : ℝ) + 1 := by positivity
  -- `N^{1/3+2γ} < K + 1 < N^{1/2}`.
  have hKlo : (N : ℝ) ^ (1 / 3 + 2 * γ) < (K N : ℝ) + 1 := by
    rw [lt_div_iff₀ hlogN] at hlo
    rw [← Real.log_lt_log_iff (by positivity) hK0, Real.log_rpow hN0]
    exact hlo
  have hKhi : (K N : ℝ) + 1 < (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hlogN] at hhi
    rw [← Real.log_lt_log_iff hK0 (by positivity), Real.log_rpow hN0]
    exact hhi
  -- `N^{1/3+γ} ≤ K`.
  have hsplit : (N : ℝ) ^ (1 / 3 + 2 * γ) = (N : ℝ) ^ γ * (N : ℝ) ^ (1 / 3 + γ) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 + γ) := Real.one_le_rpow (by linarith) (by linarith)
  have hK1 : (N : ℝ) ^ (1 / 3 + γ) ≤ K N := by nlinarith
  -- `K < N^{1−γ}`.
  have hK2 : (K N : ℝ) < (N : ℝ) ^ (1 - γ) :=
    (show (K N : ℝ) < (K N : ℝ) + 1 by linarith).trans
      (hKhi.trans_le (rpow_mono_N (by omega) (by linarith)))
  -- `N^{1/3} ≤ B`.
  have hB : (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((N / (K N + 1) : ℕ) : ℝ) := by
    have h1 : N < (K N + 1) * (N / (K N + 1) + 1) := Nat.lt_mul_div_succ N (by omega)
    have h1R : (N : ℝ) < ((K N : ℝ) + 1) * (((N / (K N + 1) : ℕ) : ℝ) + 1) := by
      exact_mod_cast h1
    have hs : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hN0]; norm_num
    have h13 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hB1 : (N : ℝ) ^ (1 / 2 : ℝ) < ((N / (K N + 1) : ℕ) : ℝ) + 1 := by
      by_contra hc
      push Not at hc
      have hB0 : (0 : ℝ) ≤ ((N / (K N + 1) : ℕ) : ℝ) + 1 := by positivity
      have : ((K N : ℝ) + 1) * (((N / (K N + 1) : ℕ) : ℝ) + 1) ≤
          (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul hKhi.le hc hB0 (by positivity)
      linarith
    nlinarith
  have hsub : obst N γ ⊆ (smoothFibre N (K N)).filter
      (fun m => ∀ d ∈ m.divisors, ¬ (K N < d ∧ d * d ≤ N)) := fun m hm => by
    obtain ⟨h1, h2⟩ := obst_mem (by omega) hγ0 hγ hK1 hK2 hB hm
    exact mem_filter.mpr ⟨h1, h2⟩
  exact hcN.trans (by exact_mod_cast card_le_card hsub)

/-! ### The pointwise claims for any distinct primes in `(N^{1/4}, N^{1/3}]` -/

/-- `(N^{1/4})⁴ = N`. -/
theorem rpow_quarter_pow_four (N : ℕ) : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

/-- A prime factor of `p₁p₂p₃s` is one of the `p_i` or divides `s`. -/
theorem prime_dvd_four {p₁ p₂ p₃ s q : ℕ} (hq : q.Prime) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hp₃ : p₃.Prime) (h : q ∣ p₁ * p₂ * p₃ * s) : q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q ∣ s := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
    · rcases (Nat.Prime.dvd_mul hq).mp h' with h'' | h''
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp₁).mp h'')
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp₂).mp h''))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp₃).mp h')))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **Remark 7.2, the pointwise claims.** Let `p₁, p₂, p₃` be distinct primes in
`(N^{1/4}, N^{1/3}]`, let `1 ≤ s ≤ N^γ` with `γ ≤ 1/3`, and let `m = p₁p₂p₃s ≤ N`. If
`N^{1/3+γ} ≤ K < N^{3/4}` and `N^{1/3} ≤ B`, then `m ∈ F₁`, and `m` has no divisor in `(K, √N]`. -/
theorem three_primes_mem {N K p₁ p₂ p₃ s : ℕ} {γ : ℝ} (hN : 1 ≤ N) (hγ : γ ≤ 1 / 3)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime) (h12 : p₁ ≠ p₂)
    (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (l1 : (N : ℝ) ^ (1 / 4 : ℝ) < p₁)
    (l2 : (N : ℝ) ^ (1 / 4 : ℝ) < p₂) (l3 : (N : ℝ) ^ (1 / 4 : ℝ) < p₃)
    (u1 : (p₁ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) (u2 : (p₂ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (u3 : (p₃ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) (hs1 : 1 ≤ s) (hsγ : (s : ℝ) ≤ (N : ℝ) ^ γ)
    (hle : p₁ * p₂ * p₃ * s ≤ N) (hK1 : (N : ℝ) ^ (1 / 3 + γ) ≤ K)
    (hK2 : (K : ℝ) < (N : ℝ) ^ (3 / 4 : ℝ))
    (hB : (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ)) :
    p₁ * p₂ * p₃ * s ∈ smoothFibre N K ∧
      ∀ d ∈ (p₁ * p₂ * p₃ * s).divisors, ¬ (K < d ∧ d * d ≤ N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hX0 : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hγT : (N : ℝ) ^ γ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := rpow_mono_N hN hγ
  have hX3 : (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
      (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
  have hP : (N : ℝ) ^ (3 / 4 : ℝ) < (p₁ : ℝ) * p₂ * p₃ := by
    rw [hX3]
    exact mul_lt_mul'' (mul_lt_mul'' l1 l2 hX0.le hX0.le) l3 (by positivity) hX0.le
  refine ⟨?_, ?_⟩
  · refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, hle⟩, ?_⟩
    · have : (K : ℝ) < ((p₁ * p₂ * p₃ * s : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    · refine Nat.mem_smoothNumbers'.mpr fun q hq hqm => ?_
      have hqB : (q : ℝ) ≤ ((N / (K + 1) : ℕ) : ℝ) := by
        rcases prime_dvd_four hq hp₁ hp₂ hp₃ hqm with h | h | h | h
        · rw [h]; linarith
        · rw [h]; linarith
        · rw [h]; linarith
        · have : (q : ℝ) ≤ s := by exact_mod_cast Nat.le_of_dvd (by omega) h
          linarith
      have : q ≤ N / (K + 1) := by exact_mod_cast hqB
      omega
  · intro d hd ⟨hKd, hdd⟩
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hddR : (d : ℝ) * d ≤ N := by exact_mod_cast hdd
    have hKdR : (K : ℝ) < d := by exact_mod_cast hKd
    have hX4 := rpow_quarter_pow_four N
    have hpair : ∀ a b : ℕ, (N : ℝ) ^ (1 / 4 : ℝ) < a → (N : ℝ) ^ (1 / 4 : ℝ) < b →
        a * b ∣ d → False := fun a b ha hb hab => by
      have h1 : ((a * b : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd0 hab
      push_cast at h1
      have h2 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) < d :=
        lt_of_lt_of_le (mul_lt_mul'' ha hb hX0.le hX0.le) h1
      nlinarith
    have hNK : (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ γ = (N : ℝ) ^ (1 / 3 + γ) := by
      rw [← Real.rpow_add hN0]
    have hsingle : ∀ a : ℕ, 0 < a → (a : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) → d ∣ a * s → False :=
        fun a hapos ha h => by
      have ha0 : 0 < a * s := Nat.mul_pos hapos (by omega)
      have h1 : (d : ℝ) ≤ ((a * s : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_dvd ha0 h
      push_cast at h1
      have h2 : (a : ℝ) * s ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ γ :=
        mul_le_mul ha hsγ (by linarith) (by positivity)
      linarith
    rcases dvd_three_primes hp₁ hp₂ hp₃ h12 h13 h23 hdm with (h | h | h) | (h | h | h)
    · exact hpair _ _ l1 l2 h
    · exact hpair _ _ l1 l3 h
    · exact hpair _ _ l2 l3 h
    · exact hsingle _ hp₁.pos u1 h
    · exact hsingle _ hp₂.pos u2 h
    · exact hsingle _ hp₃.pos u3 h

/-- **Remark 7.2, the way around it.** With `p_i`, `s` and `m = p₁p₂p₃s ≤ N` as in
`three_primes_mem`, and real `M` with `N^{3/4} ≤ M`, `2(K + 1)N^{1/3} ≤ M` and `K < N^{1/2}`: the
three divisors `m/p_i = p_jp_ks` are distinct and lie in `S_M` (so `s(m) ≥ 3`), and `m ∈ S_M` if
`m ≤ M`. -/
theorem three_primes_goodSet {N K p₁ p₂ p₃ s : ℕ} {γ M : ℝ} (hN : 1 ≤ N) (hγ : γ ≤ 1 / 3)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃)
    (h23 : p₂ ≠ p₃) (l1 : (N : ℝ) ^ (1 / 4 : ℝ) < p₁) (l2 : (N : ℝ) ^ (1 / 4 : ℝ) < p₂)
    (l3 : (N : ℝ) ^ (1 / 4 : ℝ) < p₃) (u1 : (p₁ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (u2 : (p₂ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) (u3 : (p₃ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hs1 : 1 ≤ s) (hsγ : (s : ℝ) ≤ (N : ℝ) ^ γ) (hle : p₁ * p₂ * p₃ * s ≤ N)
    (hM1 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ M) (hM2 : 2 * ((K : ℝ) + 1) * (N : ℝ) ^ (1 / 3 : ℝ) ≤ M)
    (hK : (K : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ)) :
    goodSet M K (p₂ * p₃ * s) ∧ goodSet M K (p₁ * p₃ * s) ∧ goodSet M K (p₁ * p₂ * s) ∧
      p₂ * p₃ * s ≠ p₁ * p₃ * s ∧ p₂ * p₃ * s ≠ p₁ * p₂ * s ∧ p₁ * p₃ * s ≠ p₁ * p₂ * s ∧
      (((p₁ * p₂ * p₃ * s : ℕ) : ℝ) ≤ M → goodSet M K (p₁ * p₂ * p₃ * s)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hX0 : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hleR : (p₁ : ℝ) * p₂ * p₃ * s ≤ N := by exact_mod_cast hle
  have hγT : (N : ℝ) ^ γ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := rpow_mono_N hN hγ
  have hXX : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hXY : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hhalf : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := rpow_mono_N hN (by norm_num)
  -- Prime factors of divisors of `m` are at most `N^{1/3}`.
  have hprimes : ∀ x : ℕ, x ∣ p₁ * p₂ * p₃ * s →
      ∀ q, q.Prime → q ∣ x → 2 * ((K : ℝ) + 1) * q ≤ M := fun x hx q hq hqx => by
    have hqT : (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
      rcases prime_dvd_four hq hp₁ hp₂ hp₃ (hqx.trans hx) with h | h | h | h
      · rw [h]; exact u1
      · rw [h]; exact u2
      · rw [h]; exact u3
      · have : (q : ℝ) ≤ s := by exact_mod_cast Nat.le_of_dvd (by omega) h
        linarith
    have hK0 : (0 : ℝ) ≤ 2 * ((K : ℝ) + 1) := by positivity
    exact (mul_le_mul_of_nonneg_left hqT hK0).trans hM2
  have hpair : ∀ a b c : ℕ, (N : ℝ) ^ (1 / 4 : ℝ) < a → (N : ℝ) ^ (1 / 4 : ℝ) < b →
      (N : ℝ) ^ (1 / 4 : ℝ) < c → (c : ℝ) * (a * b * s) ≤ N →
      a * b * s ∣ p₁ * p₂ * p₃ * s → goodSet M K (a * b * s) := fun a b c ha hb hc habc hdvd => by
    refine ⟨?_, ?_, hprimes _ hdvd⟩
    · have hab : (N : ℝ) ^ (1 / 2 : ℝ) < a * b := by
        rw [← hXX]; exact mul_lt_mul'' ha hb hX0.le hX0.le
      have : (K : ℝ) < ((a * b * s : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    · push_cast
      have ha0 : (0 : ℝ) < a := lt_trans hX0 ha
      have hb0 : (0 : ℝ) < b := lt_trans hX0 hb
      have h1 : (N : ℝ) ^ (1 / 4 : ℝ) * (a * b * s) < c * (a * b * s) :=
        mul_lt_mul_of_pos_right hc (by positivity)
      have h2 : (N : ℝ) ^ (1 / 4 : ℝ) * (a * b * s) < (N : ℝ) ^ (1 / 4 : ℝ) * M := by
        nlinarith
      exact (lt_of_mul_lt_mul_left h2 hX0.le).le
  have d23 : p₂ * p₃ * s ∣ p₁ * p₂ * p₃ * s := ⟨p₁, by ring⟩
  have d13 : p₁ * p₃ * s ∣ p₁ * p₂ * p₃ * s := ⟨p₂, by ring⟩
  have d12 : p₁ * p₂ * s ∣ p₁ * p₂ * p₃ * s := ⟨p₃, by ring⟩
  have hp₃s : 0 < p₃ * s := Nat.mul_pos hp₃.pos (by omega)
  refine ⟨hpair p₂ p₃ p₁ l2 l3 l1 (by linarith) d23, hpair p₁ p₃ p₂ l1 l3 l2 (by linarith) d13,
    hpair p₁ p₂ p₃ l1 l2 l3 (by linarith) d12, ?_, ?_, ?_, ?_⟩
  · intro h
    exact h12 (Nat.eq_of_mul_eq_mul_right hp₃s (by rw [← mul_assoc, ← mul_assoc]; exact h)).symm
  · intro h
    exact h13 (Nat.eq_of_mul_eq_mul_left hp₂.pos
      (Nat.eq_of_mul_eq_mul_right (by omega : 0 < s) (by linarith [h]))).symm
  · intro h
    exact h23 (Nat.eq_of_mul_eq_mul_left hp₁.pos
      (Nat.eq_of_mul_eq_mul_right (by omega : 0 < s) (by linarith [h]))).symm
  · intro hmM
    refine ⟨?_, hmM, hprimes _ dvd_rfl⟩
    have hP : (N : ℝ) ^ (1 / 2 : ℝ) < (p₁ : ℝ) * p₂ * p₃ := by
      rw [← hXX]
      have h1 := mul_lt_mul'' l1 l2 hX0.le hX0.le
      have h3 : (1 : ℝ) ≤ p₃ := by exact_mod_cast hp₃.one_lt.le
      nlinarith
    have : (K : ℝ) < ((p₁ * p₂ * p₃ * s : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this

/-- **Remark 7.2, the attachment condition.** If `log(K + 1)/log N → θ` and
`θ + 1/3 < 1 − 2δ`, then `2(K + 1)N^{1/3} ≤ N^{1−2δ} = M` for all large `N`. -/
theorem eventually_attach_cond {θ δ : ℝ} (hθδ : θ + 1 / 3 < 1 - 2 * δ) {K : ℕ → ℕ}
    (hK : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    ∀ᶠ N : ℕ in atTop,
      2 * ((K N : ℝ) + 1) * (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (1 - 2 * δ) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (1 - 2 * δ - θ - 1 / 3) / 2 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hK.eventually (gt_mem_nhds (show θ < θ + ε by linarith)),
    eventually_ge_atTop 2, hN.eventually ((tendsto_rpow_atTop hε).eventually_ge_atTop 2)]
    with N hhi hN2 hNε
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hK0 : (0 : ℝ) < (K N : ℝ) + 1 := by positivity
  have hKhi : (K N : ℝ) + 1 < (N : ℝ) ^ (θ + ε) := by
    rw [div_lt_iff₀ hlogN] at hhi
    rw [← Real.log_lt_log_iff hK0 (by positivity), Real.log_rpow hN0]
    exact hhi
  have hsplit : (N : ℝ) ^ (1 - 2 * δ) =
      (N : ℝ) ^ ε * ((N : ℝ) ^ (θ + ε) * (N : ℝ) ^ (1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    rw [hεdef]
    ring
  rw [hsplit]
  have hA : ((K N : ℝ) + 1) * (N : ℝ) ^ (1 / 3 : ℝ) ≤
      (N : ℝ) ^ (θ + ε) * (N : ℝ) ^ (1 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right hKhi.le (by positivity)
  calc 2 * ((K N : ℝ) + 1) * (N : ℝ) ^ (1 / 3 : ℝ)
      = 2 * (((K N : ℝ) + 1) * (N : ℝ) ^ (1 / 3 : ℝ)) := by ring
    _ ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (θ + ε) * (N : ℝ) ^ (1 / 3 : ℝ)) :=
        mul_le_mul hNε hA (by positivity) (by positivity)

end HubRemoval
