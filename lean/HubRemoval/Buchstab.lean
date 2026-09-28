import HubRemoval.Mertens2

/-!
# Buchstab's identity

`Ψ(X, y)` counts `1 ≤ n ≤ X` with every prime factor `≤ y` (`psi X y`). For real arguments,
`PsiR x y = Ψ(⌊x⌋, ⌊y⌋)`, which is the paper's `Ψ(x, y)`.

**Buchstab's identity.** For `0 ≤ y ≤ z`, `Ψ(x, z) = Ψ(x, y) + ∑_{y < p ≤ z} Ψ(x/p, p)`
(`buchstab`, `buchstab_real`). The numbers counted on the right with a given `p` are those with
largest prime factor `p`: `n = p m` with `m ≤ x/p` and `P⁺(m) ≤ p`.

Also `Ψ(X, y) = X` when `y ≥ X` (`psi_eq_self_of_le`), since then every `n ≤ X` is `y`-smooth.
-/

namespace HubRemoval

open Finset

/-- One step for a prime `p`: `Ψ(X, p) = Ψ(X, p − 1) + Ψ(X/p, p)`. -/
theorem psi_prime_step (X : ℕ) {p : ℕ} (hp : p.Prime) :
    psi X p = psi X (p - 1) + psi (X / p) p := by
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  unfold psi
  rw [hp1]
  have hset : Nat.smoothNumbersUpTo X (p + 1) = Nat.smoothNumbersUpTo X p ∪
      (Nat.smoothNumbersUpTo (X / p) (p + 1)).image (p * ·) := by
    ext n
    simp only [mem_union, mem_image, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers']
    constructor
    · rintro ⟨hnX, hn⟩
      by_cases hsm : ∀ q, q.Prime → q ∣ n → q < p
      · exact Or.inl ⟨hnX, hsm⟩
      · right
        push Not at hsm
        obtain ⟨q, hq, hqn, hqp⟩ := hsm
        have hqp' : q = p := le_antisymm (Nat.lt_succ_iff.mp (hn q hq hqn)) hqp
        subst hqp'
        obtain ⟨m, rfl⟩ := hqn
        refine ⟨m, ⟨(Nat.le_div_iff_mul_le hq.pos).mpr (by rw [mul_comm]; exact hnX),
          fun r hr hrm => hn r hr (hrm.mul_left _)⟩, rfl⟩
    · rintro (⟨hnX, hn⟩ | ⟨m, ⟨hmX, hm⟩, rfl⟩)
      · exact ⟨hnX, fun q hq hqn => (hn q hq hqn).trans (Nat.lt_succ_self p)⟩
      · refine ⟨?_, fun q hq hqn => ?_⟩
        · calc p * m ≤ p * (X / p) := Nat.mul_le_mul_left p hmX
            _ ≤ X := Nat.mul_div_le X p
        · rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
          · rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]
            exact Nat.lt_succ_self p
          · exact hm q hq h
  have hdisj : Disjoint (Nat.smoothNumbersUpTo X p)
      ((Nat.smoothNumbersUpTo (X / p) (p + 1)).image (p * ·)) := by
    refine disjoint_left.mpr fun n hn hn' => ?_
    obtain ⟨m, -, rfl⟩ := mem_image.mp hn'
    have := (Nat.mem_smoothNumbers'.mp (Nat.mem_smoothNumbersUpTo.mp hn).2) p hp
      (dvd_mul_right p m)
    exact lt_irrefl p this
  rw [hset, card_union_of_disjoint hdisj,
    card_image_of_injective _ fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h]

/-- One step for a non-prime `k ≥ 1`: `Ψ(X, k) = Ψ(X, k − 1)`. -/
theorem psi_nonprime_step (X : ℕ) {k : ℕ} (hk : 1 ≤ k) (hkp : ¬ k.Prime) :
    psi X k = psi X (k - 1) := by
  unfold psi
  rw [Nat.sub_add_cancel hk]
  congr 1
  ext n
  simp only [Nat.mem_smoothNumbersUpTo, Nat.smoothNumbers_succ hkp]

/-- **Buchstab's identity.** For `Y ≤ Z`, `Ψ(X, Z) = Ψ(X, Y) + ∑_{Y < p ≤ Z} Ψ(X/p, p)`. -/
theorem buchstab (X : ℕ) {Y Z : ℕ} (hYZ : Y ≤ Z) :
    psi X Z = psi X Y + ∑ p ∈ (primesUpTo Z).filter (fun p => Y < p), psi (X / p) p := by
  induction Z, hYZ using Nat.le_induction with
  | base =>
    have : (primesUpTo Y).filter (fun p => Y < p) = ∅ :=
      filter_eq_empty_iff.mpr fun p hp => by have := (mem_primesUpTo.mp hp).2; omega
    rw [this, sum_empty, add_zero]
  | succ Z hYZ ih =>
    by_cases hZ : (Z + 1).Prime
    · have hset : (primesUpTo (Z + 1)).filter (fun p => Y < p) =
          insert (Z + 1) ((primesUpTo Z).filter (fun p => Y < p)) := by
        ext p
        rw [mem_insert, mem_filter, mem_filter, mem_primesUpTo, mem_primesUpTo]
        constructor
        · rintro ⟨⟨hpp, hpZ⟩, hYp⟩
          rcases Nat.lt_or_ge p (Z + 1) with h | h
          · exact Or.inr ⟨⟨hpp, by omega⟩, hYp⟩
          · exact Or.inl (by omega)
        · rintro (rfl | ⟨⟨hpp, hpZ⟩, hYp⟩)
          · exact ⟨⟨hZ, le_rfl⟩, by omega⟩
          · exact ⟨⟨hpp, by omega⟩, hYp⟩
      have hnot : Z + 1 ∉ (primesUpTo Z).filter (fun p => Y < p) := fun h => by
        have := (mem_primesUpTo.mp (mem_filter.mp h).1).2
        omega
      rw [hset, sum_insert hnot, psi_prime_step X hZ, Nat.add_sub_cancel, ih]
      ring
    · have hset : (primesUpTo (Z + 1)).filter (fun p => Y < p) =
          (primesUpTo Z).filter (fun p => Y < p) := by
        ext p
        rw [mem_filter, mem_filter, mem_primesUpTo, mem_primesUpTo]
        constructor
        · rintro ⟨⟨hpp, hpZ⟩, hYp⟩
          refine ⟨⟨hpp, ?_⟩, hYp⟩
          rcases Nat.lt_or_ge p (Z + 1) with h | h
          · omega
          · have hpeq : p = Z + 1 := by omega
            exact absurd (hpeq ▸ hpp) hZ
        · rintro ⟨⟨hpp, hpZ⟩, hYp⟩
          exact ⟨⟨hpp, by omega⟩, hYp⟩
      rw [hset, psi_nonprime_step X (by omega) hZ, Nat.add_sub_cancel, ih]

/-- `Ψ(X, Y) = X` when `Y ≥ X`: every `n ≤ X` is `Y`-smooth. -/
theorem psi_eq_self_of_le {X Y : ℕ} (hXY : X ≤ Y) : psi X Y = X := by
  unfold psi
  have hset : Nat.smoothNumbersUpTo X (Y + 1) = Ioc 0 X := by
    ext n
    simp only [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers', mem_Ioc]
    constructor
    · rintro ⟨hnX, hn⟩
      refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, hnX⟩
      subst h0
      obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (Y + 1)
      have := hn q hq (dvd_zero q)
      omega
    · rintro ⟨hn0, hnX⟩
      exact ⟨hnX, fun q hq hqn => by have := Nat.le_of_dvd hn0 hqn; omega⟩
  rw [hset, Nat.card_Ioc, Nat.sub_zero]

/-- `Ψ(x, y)` for real arguments: `Ψ(⌊x⌋, ⌊y⌋)`. -/
noncomputable def PsiR (x y : ℝ) : ℕ := psi ⌊x⌋₊ ⌊y⌋₊

/-- **Buchstab's identity, real form.** For `0 ≤ y ≤ z`,
`Ψ(x, z) = Ψ(x, y) + ∑_{y < p ≤ z} Ψ(x/p, p)`. -/
theorem buchstab_real {x y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    (PsiR x z : ℝ) = PsiR x y +
      ∑ p ∈ (primesUpTo ⌊z⌋₊).filter (fun p : ℕ => y < p), (PsiR (x / p) p : ℝ) := by
  have h := buchstab ⌊x⌋₊ (Nat.floor_le_floor hyz)
  have hset : (primesUpTo ⌊z⌋₊).filter (fun p : ℕ => y < p) =
      (primesUpTo ⌊z⌋₊).filter (fun p => ⌊y⌋₊ < p) :=
    filter_congr fun p _ => lt_iff_floor_lt hy p
  unfold PsiR
  rw [hset]
  have hterm : ∀ p ∈ (primesUpTo ⌊z⌋₊).filter (fun p => ⌊y⌋₊ < p),
      psi ⌊x / (p : ℝ)⌋₊ ⌊(p : ℝ)⌋₊ = psi (⌊x⌋₊ / p) p := fun p _ => by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have h' : (psi ⌊x⌋₊ ⌊z⌋₊ : ℝ) = psi ⌊x⌋₊ ⌊y⌋₊ +
      ∑ p ∈ (primesUpTo ⌊z⌋₊).filter (fun p => ⌊y⌋₊ < p), (psi (⌊x⌋₊ / p) p : ℝ) := by
    exact_mod_cast h
  rw [h']
  congr 1
  exact sum_congr rfl fun p hp => by rw [hterm p hp]

end HubRemoval
