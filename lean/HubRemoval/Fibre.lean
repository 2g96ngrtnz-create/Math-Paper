import Mathlib

/-!
# Fibres of the divisor graph (paper, Lemma 3.1)

This file formalises Lemma 3.1 of `paper/hub_removal.tex`, one part at a time.
Contents: Lemma 3.1(a), both parts.

## Lemma 3.1(a), first part

Let `0 ≤ K < N` and `B = ⌊N/(K+1)⌋`. If `{d, m}` is an edge of the divisor graph on
`{K+1, …, N}` with `d < m`, then `m / d ≤ B`.

In Lean, natural-number division `N / (K + 1)` is exactly `⌊N/(K+1)⌋`, and the edge
hypothesis is `d ∣ m` with `K < d` and `m ≤ N`. The condition `d < m` is not needed.
-/

namespace HubRemoval

/-- **Lemma 3.1(a), first part.** If `d ∣ m`, `K < d` and `m ≤ N`, then
`m / d ≤ N / (K + 1)`, that is, the cofactor `m / d` is at most `B = ⌊N/(K+1)⌋`. -/
theorem cofactor_le_B {N K d m : ℕ} (hdm : d ∣ m) (hKd : K < d) (hmN : m ≤ N) :
    m / d ≤ N / (K + 1) := by
  obtain ⟨c, rfl⟩ := hdm
  have hd : 0 < d := by omega
  rw [Nat.mul_div_cancel_left c hd, Nat.le_div_iff_mul_le (Nat.succ_pos K)]
  calc c * (K + 1) ≤ c * d := Nat.mul_le_mul_left c (Nat.succ_le_of_lt hKd)
    _ = d * c := Nat.mul_comm c d
    _ ≤ N := hmN

/-!
## Lemma 3.1(a), second part

The `B`-rough part of `n` is `R_B(n) = ∏_{p^v ∥ n, p > B} p^v`. If `{d, m}` is an edge of the
divisor graph on `{K+1, …, N}` with `d < m`, then `R_B(d) = R_B(m)` for `B = ⌊N/(K+1)⌋`.

The argument is the paper's. By the first part, the cofactor `m / d` is at most `B`. So no
prime `p > B` divides it, and `m` and `d` have the same `p`-adic valuation for every prime
`p > B`.
-/

/-- The `B`-rough part of `n`: the product of `p ^ v_p(n)` over the primes `p > B`
dividing `n`. -/
def roughPart (B n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (B < ·), p ^ n.factorization p

/-- If `d ∣ m`, `m ≠ 0` and the cofactor `m / d` is at most `B`, then `m` and `d` have the
same `p`-adic valuation for every `p > B`. -/
theorem factorization_eq_of_cofactor_le {B d m p : ℕ} (hdm : d ∣ m) (hm : m ≠ 0)
    (hc : m / d ≤ B) (hp : B < p) : m.factorization p = d.factorization p := by
  obtain ⟨c, rfl⟩ := hdm
  have hd : d ≠ 0 := left_ne_zero_of_mul hm
  have hc0 : c ≠ 0 := right_ne_zero_of_mul hm
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hd)] at hc
  have hcp : c.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) h
    omega
  rw [Nat.factorization_mul hd hc0, Finsupp.add_apply, hcp, Nat.add_zero]

/-- If `d ∣ m`, `m ≠ 0` and the cofactor `m / d` is at most `B`, then `d` and `m` have the
same `B`-rough part. -/
theorem roughPart_eq_of_cofactor_le {B d m : ℕ} (hdm : d ∣ m) (hm : m ≠ 0)
    (hc : m / d ≤ B) : roughPart B d = roughPart B m := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact hm (Nat.eq_zero_of_zero_dvd hdm)
  have key : ∀ p, B < p → m.factorization p = d.factorization p :=
    fun p hp => factorization_eq_of_cofactor_le hdm hm hc hp
  have hS : d.primeFactors.filter (B < ·) = m.primeFactors.filter (B < ·) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpd, -⟩, hBp⟩
      exact ⟨⟨hp, dvd_trans hpd hdm, hm⟩, hBp⟩
    · rintro ⟨⟨hp, hpm, -⟩, hBp⟩
      refine ⟨⟨hp, ?_, hd⟩, hBp⟩
      have hpos : 0 < m.factorization p := hp.factorization_pos_of_dvd hm hpm
      rw [key p hBp] at hpos
      exact Nat.dvd_of_factorization_pos (Nat.pos_iff_ne_zero.mp hpos)
  unfold roughPart
  rw [hS]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [key p (Finset.mem_filter.mp hp).2]

/-- **Lemma 3.1(a), second part.** If `{d, m}` is an edge of the divisor graph on
`{K+1, …, N}` with `d < m` (that is, `d ∣ m`, `K < d < m ≤ N`), then `d` and `m` have the
same `B`-rough part for `B = ⌊N/(K+1)⌋`. -/
theorem roughPart_eq_of_edge {N K d m : ℕ} (hdm : d ∣ m) (hKd : K < d) (hdlt : d < m)
    (hmN : m ≤ N) : roughPart (N / (K + 1)) d = roughPart (N / (K + 1)) m :=
  roughPart_eq_of_cofactor_le hdm (by omega) (cofactor_le_B hdm hKd hmN)

/-!
## Lemma 3.1(b)

`R_B` is constant on every connected component of `G_{N,K}`.

We model `G_{N,K}` as a simple graph on `ℕ`. Two distinct numbers are adjacent when both lie in
`(K, N]` and one divides the other. Numbers outside `(K, N]` are isolated. So reachability
between vertices of `(K, N]` is exactly reachability in `G_{N,K}`.
-/

/-- The divisor graph `G_{N,K}` on `{K+1, …, N}`, as a simple graph on `ℕ` in which vertices
outside `(K, N]` are isolated. -/
def divGraph (N K : ℕ) : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ K < a ∧ a ≤ N ∧ K < b ∧ b ≤ N ∧ (a ∣ b ∨ b ∣ a)
  symm := fun _ _ ⟨h, ha, ha', hb, hb', hd⟩ => ⟨h.symm, hb, hb', ha, ha', hd.symm⟩
  loopless := fun _ h => h.1 rfl

/-- Adjacent vertices of `G_{N,K}` have the same `B`-rough part, `B = ⌊N/(K+1)⌋`. -/
theorem roughPart_eq_of_adj {N K a b : ℕ} (h : (divGraph N K).Adj a b) :
    roughPart (N / (K + 1)) a = roughPart (N / (K + 1)) b := by
  obtain ⟨hne, hKa, haN, hKb, hbN, hd | hd⟩ := h
  · have hlt : a < b := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) hne
    exact roughPart_eq_of_edge hd hKa hlt hbN
  · have hlt : b < a := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) (Ne.symm hne)
    exact (roughPart_eq_of_edge hd hKb hlt haN).symm

/-- **Lemma 3.1(b).** The `B`-rough part is constant on connected components of `G_{N,K}`:
reachable vertices have the same `B`-rough part, `B = ⌊N/(K+1)⌋`. -/
theorem roughPart_eq_of_reachable {N K a b : ℕ} (h : (divGraph N K).Reachable a b) :
    roughPart (N / (K + 1)) a = roughPart (N / (K + 1)) b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (roughPart_eq_of_adj hadj).trans ih

end HubRemoval
