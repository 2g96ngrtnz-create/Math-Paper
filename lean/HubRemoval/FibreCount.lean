import HubRemoval.Fibre

/-!
# Fibre sizes (paper, Lemma 3.1(c))

`B = ⌊N/(K+1)⌋`, `V_{N,K} = {K+1, …, N}`, and `V_n = {v ∈ V_{N,K} : R_B(v) = n}`.

* The paper's `Ψ(x, y)` is the number of `1 ≤ n ≤ x` with every prime factor `≤ y`.
  Here it is `psi x y := #(Nat.smoothNumbersUpTo x (y + 1))`.
* The paper's smooth fibre is `F₁ = {v ∈ V_{N,K} : P⁺(v) ≤ B}`.

**Lemma 3.1(c).**
1. `|V_n| ≤ Ψ(N/n, B) ≤ Ψ(N, B)`.
2. `V_1 = F₁` and `|F₁| = Ψ(N, B) − Ψ(K, B)`.
3. `|V_n| ≤ K` for `n > 1`.
-/

namespace HubRemoval

/-- The `B`-smooth part of `n`: the product of `p ^ v_p(n)` over the primes `p ≤ B`
dividing `n`. -/
def smoothPart (B n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬ B < p), p ^ n.factorization p

/-- The paper's `Ψ(x, y)`: the number of `1 ≤ n ≤ x` all of whose prime factors are `≤ y`. -/
def psi (x y : ℕ) : ℕ := (Nat.smoothNumbersUpTo x (y + 1)).card

/-- The vertex set `V_{N,K} = {K+1, …, N}`. -/
def vertices (N K : ℕ) : Finset ℕ := Finset.Ioc K N

/-- The fibre `V_n = {v ∈ V_{N,K} : R_B(v) = n}`, `B = ⌊N/(K+1)⌋`. -/
def fibre (N K n : ℕ) : Finset ℕ :=
  (vertices N K).filter (fun v => roughPart (N / (K + 1)) v = n)

/-- The smooth fibre `F₁ = {v ∈ V_{N,K} : every prime factor of v is ≤ B}`. -/
def smoothFibre (N K : ℕ) : Finset ℕ :=
  (vertices N K).filter (fun v => v ∈ Nat.smoothNumbers (N / (K + 1) + 1))

/-- `R_B(n) · S_B(n) = n`, where `S_B` is the `B`-smooth part. -/
theorem roughPart_mul_smoothPart {B n : ℕ} (hn : n ≠ 0) :
    roughPart B n * smoothPart B n = n := by
  unfold roughPart smoothPart
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self hn

theorem roughPart_pos (B n : ℕ) : 0 < roughPart B n := by
  unfold roughPart
  refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

/-- `R_B(n)` divides `n`. -/
theorem roughPart_dvd (B n : ℕ) : roughPart B n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  · exact ⟨smoothPart B n, (roughPart_mul_smoothPart hn).symm⟩

/-- The `B`-smooth part has no prime factor `> B`. -/
theorem smoothPart_mem_smoothNumbers (B n : ℕ) :
    smoothPart B n ∈ Nat.smoothNumbers (B + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hqd
  unfold smoothPart at hqd
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqd
  have hp' := Finset.mem_filter.mp hp
  have hpp := Nat.prime_of_mem_primeFactors hp'.1
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).mp (hq.dvd_of_dvd_pow hqp)
  have := hp'.2
  omega

/-- If `R_B(n) ≠ 1` (with `n ≠ 0`), then `R_B(n) > B`. -/
theorem lt_roughPart_of_ne_one {B n : ℕ} (hn : n ≠ 0) (h1 : roughPart B n ≠ 1) :
    B < roughPart B n := by
  unfold roughPart at h1 ⊢
  obtain ⟨p, hp⟩ : (n.primeFactors.filter (B < ·)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact h1 (by rw [hne, Finset.prod_empty])
  have hp' := Finset.mem_filter.mp hp
  have hpp := Nat.prime_of_mem_primeFactors hp'.1
  have hpos : 0 < n.factorization p := hpp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp'.1)
  have hdvd : p ∣ ∏ q ∈ n.primeFactors.filter (B < ·), q ^ n.factorization q :=
    (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hpos)).trans (Finset.dvd_prod_of_mem _ hp)
  have hle := Nat.le_of_dvd (roughPart_pos B n) hdvd
  have := hp'.2
  omega

/-- For `n ≠ 0`: `R_B(n) = 1` if and only if every prime factor of `n` is `≤ B`. -/
theorem roughPart_eq_one_iff {B n : ℕ} (hn : n ≠ 0) :
    roughPart B n = 1 ↔ n ∈ Nat.smoothNumbers (B + 1) := by
  constructor
  · intro h1
    have hs := smoothPart_mem_smoothNumbers B n
    have hmul := roughPart_mul_smoothPart (B := B) hn
    rw [h1, one_mul] at hmul
    rwa [hmul] at hs
  · intro hs
    unfold roughPart
    apply Finset.prod_eq_one
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have := (Nat.mem_smoothNumbers'.mp hs) p (Nat.prime_of_mem_primeFactors hp'.1)
      (Nat.dvd_of_mem_primeFactors hp'.1)
    have := hp'.2
    omega

theorem psi_mono {x x' : ℕ} (h : x ≤ x') (y : ℕ) : psi x y ≤ psi x' y := by
  unfold psi
  apply Finset.card_le_card
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1.trans h, hn.2⟩

theorem psi_le_self (x y : ℕ) : psi x y ≤ x := by
  unfold psi
  calc (Nat.smoothNumbersUpTo x (y + 1)).card ≤ (Finset.Ioc 0 x).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Nat.mem_smoothNumbersUpTo] at hn
        rw [Finset.mem_Ioc]
        exact ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn.2), hn.1⟩
    _ = x := by simp

/-- **Lemma 3.1(c), first bound.** `|V_n| ≤ Ψ(N/n, B)`. -/
theorem card_fibre_le (N K n : ℕ) : (fibre N K n).card ≤ psi (N / n) (N / (K + 1)) := by
  unfold psi
  apply Finset.card_le_card_of_injOn (fun v => v / n)
  · intro v hv
    have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
    have hvI := Finset.mem_Ioc.mp hv'.1
    have hv0 : v ≠ 0 := by omega
    have hmul := roughPart_mul_smoothPart (B := N / (K + 1)) hv0
    rw [hv'.2] at hmul
    have hn : 0 < n := hv'.2 ▸ roughPart_pos _ v
    have hdiv : v / n = smoothPart (N / (K + 1)) v := by
      rw [← hmul, Nat.mul_div_cancel_left _ hn]
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo, hdiv]
    refine ⟨?_, smoothPart_mem_smoothNumbers _ _⟩
    rw [← hdiv]
    exact Nat.div_le_div_right hvI.2
  · intro v hv w hw hvw
    have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
    have hw' := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hvd : n ∣ v := hv'.2 ▸ roughPart_dvd _ v
    have hwd : n ∣ w := hw'.2 ▸ roughPart_dvd _ w
    exact (Nat.div_left_inj hvd hwd).mp hvw

/-- **Lemma 3.1(c), second bound.** `|V_n| ≤ Ψ(N, B)`. -/
theorem card_fibre_le_psi (N K n : ℕ) : (fibre N K n).card ≤ psi N (N / (K + 1)) :=
  (card_fibre_le N K n).trans (psi_mono (Nat.div_le_self N n) _)

/-- **Lemma 3.1(c).** `V_1 = F₁`. -/
theorem fibre_one (N K : ℕ) : fibre N K 1 = smoothFibre N K := by
  ext v
  simp only [fibre, smoothFibre, vertices, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hv, h1⟩
    exact ⟨hv, (roughPart_eq_one_iff (by omega)).mp h1⟩
  · rintro ⟨hv, hs⟩
    exact ⟨hv, (roughPart_eq_one_iff (by omega)).mpr hs⟩

/-- **Lemma 3.1(c).** `|F₁| = Ψ(N, B) − Ψ(K, B)` for `K ≤ N`. -/
theorem card_smoothFibre {N K : ℕ} (hKN : K ≤ N) :
    (smoothFibre N K).card = psi N (N / (K + 1)) - psi K (N / (K + 1)) := by
  unfold psi
  rw [← Finset.card_sdiff_of_subset]
  · congr 1
    ext v
    simp only [smoothFibre, vertices, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hKv, hvN⟩, hs⟩
      exact ⟨⟨hvN, hs⟩, fun h => by omega⟩
    · rintro ⟨⟨hvN, hs⟩, hn⟩
      refine ⟨⟨?_, hvN⟩, hs⟩
      by_contra hle
      exact hn ⟨by omega, hs⟩
  · intro v hv
    rw [Nat.mem_smoothNumbersUpTo] at hv ⊢
    exact ⟨hv.1.trans hKN, hv.2⟩

/-- **Lemma 3.1(c).** `|V_n| ≤ K` for `n > 1`. -/
theorem card_fibre_le_K {N K n : ℕ} (hn : 1 < n) : (fibre N K n).card ≤ K := by
  rcases (fibre N K n).eq_empty_or_nonempty with he | ⟨v, hv⟩
  · simp [he]
  have hv' := Finset.mem_filter.mp hv
  have hvI := Finset.mem_Ioc.mp hv'.1
  have hBn : N / (K + 1) < n := by
    rw [← hv'.2]
    exact lt_roughPart_of_ne_one (by omega) (by rw [hv'.2]; omega)
  calc (fibre N K n).card ≤ psi (N / n) (N / (K + 1)) := card_fibre_le N K n
    _ ≤ N / n := psi_le_self _ _
    _ ≤ K := by
        have hlt : N < (K + 1) * (N / (K + 1) + 1) := Nat.lt_mul_div_succ N (Nat.succ_pos K)
        have hle : N / n ≤ N / (N / (K + 1) + 1) := Nat.div_le_div_left hBn (Nat.succ_pos _)
        have : N / (N / (K + 1) + 1) < K + 1 :=
          (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr (by rw [Nat.mul_comm]; exact hlt)
        omega

end HubRemoval
