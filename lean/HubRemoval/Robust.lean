import HubRemoval.Fibre

/-!
# Robust edges (paper, Lemma 4.1): the deterministic half

`M` is a real number and `G_{M,K}` is the divisor graph on `ℤ ∩ (K, M]`, which is
`divGraph ⌊M⌋₊ K`. An orientation of `G_{N,K}` is a relation `D` on `ℕ`.

The event `𝓡` says: for all `K < x < x' ≤ M` with `x ∣ x'`, there are vertices `y, y'` of
`V_{N,K}`, both multiples of `x'`, with `x → y → x'` and `x' → y' → x`.

This file proves the deterministic parts of Lemma 4.1:

* **On `𝓡`, both ends of every edge of `G_{M,K}` lie in the same SCC**, so every connected
  component of `G_{M,K}` lies in a single SCC (`robust_reachable`).
* **The count of witnesses.** For `0 < x'` the set `𝒴 = {y : x' < y ≤ N, x' ∣ y}` has exactly
  `⌊N/x'⌋ − 1` elements (`card_multiples_Ioc`). If `x' ≤ M`, this is `≥ N/M − 2`
  (`card_multiples_Ioc_ge`).

The probability bound `P(𝓡ᶜ) ≤ M²(1 − q)^{N^{2δ} − 2}` needs a model of the random orientation,
and is not formalised here.
-/

namespace HubRemoval

/-- The event `𝓡` of Lemma 4.1, for one orientation `D`. -/
def RobustEvent (D : ℕ → ℕ → Prop) (N K : ℕ) (M : ℝ) : Prop :=
  ∀ x x' : ℕ, K < x → x < x' → (x' : ℝ) ≤ M → x ∣ x' →
    (∃ y, K < y ∧ y ≤ N ∧ x' ∣ y ∧ D x y ∧ D y x') ∧
    (∃ y', K < y' ∧ y' ≤ N ∧ x' ∣ y' ∧ D x' y' ∧ D y' x)

/-- `a` and `b` are mutually reachable in `D`, that is, they lie in the same SCC. -/
def MutuallyReachable (D : ℕ → ℕ → Prop) (a b : ℕ) : Prop :=
  Relation.ReflTransGen D a b ∧ Relation.ReflTransGen D b a

theorem MutuallyReachable.refl (D : ℕ → ℕ → Prop) (a : ℕ) : MutuallyReachable D a a :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem MutuallyReachable.symm {D : ℕ → ℕ → Prop} {a b : ℕ} (h : MutuallyReachable D a b) :
    MutuallyReachable D b a :=
  ⟨h.2, h.1⟩

theorem MutuallyReachable.trans {D : ℕ → ℕ → Prop} {a b c : ℕ} (h : MutuallyReachable D a b)
    (h' : MutuallyReachable D b c) : MutuallyReachable D a c :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- On `𝓡`, the ends `x < x'` of a divisibility pair are mutually reachable, through the
witnesses `x → y → x'` and `x' → y' → x`. -/
theorem robust_pair {D : ℕ → ℕ → Prop} {N K : ℕ} {M : ℝ} (hR : RobustEvent D N K M)
    {x x' : ℕ} (hKx : K < x) (hxx' : x < x') (hx'M : (x' : ℝ) ≤ M) (hdvd : x ∣ x') :
    MutuallyReachable D x x' := by
  obtain ⟨⟨y, -, -, -, hxy, hyx'⟩, ⟨y', -, -, -, hx'y', hy'x⟩⟩ := hR x x' hKx hxx' hx'M hdvd
  exact ⟨(Relation.ReflTransGen.single hxy).tail hyx',
    (Relation.ReflTransGen.single hx'y').tail hy'x⟩

/-- **Lemma 4.1, deterministic part.** On `𝓡`, the two ends of every edge of `G_{M,K}` lie in
the same SCC of `D`. -/
theorem robust_adj {D : ℕ → ℕ → Prop} {N K : ℕ} {M : ℝ} (hR : RobustEvent D N K M) {a b : ℕ}
    (h : (divGraph ⌊M⌋₊ K).Adj a b) : MutuallyReachable D a b := by
  obtain ⟨hab, hKa, haM, hKb, hbM, hdvd⟩ := h
  have hM0 : 0 ≤ M := by
    by_contra hneg
    rw [Nat.floor_of_nonpos (le_of_lt (not_le.mp hneg))] at haM
    omega
  have hcast : ∀ n, n ≤ ⌊M⌋₊ → (n : ℝ) ≤ M := fun n hn => (Nat.le_floor_iff hM0).mp hn
  rcases hdvd with hd | hd
  · have hlt : a < b := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) hab
    exact robust_pair hR hKa hlt (hcast b hbM) hd
  · have hlt : b < a := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) (Ne.symm hab)
    exact (robust_pair hR hKb hlt (hcast a haM) hd).symm

/-- **Lemma 4.1.** On `𝓡`, every connected component of `G_{M,K}` lies in a single SCC of `D`. -/
theorem robust_reachable {D : ℕ → ℕ → Prop} {N K : ℕ} {M : ℝ} (hR : RobustEvent D N K M)
    {a b : ℕ} (h : (divGraph ⌊M⌋₊ K).Reachable a b) : MutuallyReachable D a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact MutuallyReachable.refl D a
  | tail _ hbc ih => exact ih.trans (robust_adj hR hbc)

/-- The witness set `𝒴 = {y : x' < y ≤ N, x' ∣ y}` has exactly `⌊N/x'⌋ − 1` elements. -/
theorem card_multiples_Ioc (N : ℕ) {x' : ℕ} (hx' : 0 < x') :
    ((Finset.Ioc x' N).filter (x' ∣ ·)).card = N / x' - 1 := by
  rcases Nat.lt_or_ge N x' with hN | hN
  · rw [Finset.Ioc_eq_empty (by omega), Nat.div_eq_of_lt hN]
    rfl
  have hset : (Finset.Ioc 0 N).filter (x' ∣ ·) =
      insert x' ((Finset.Ioc x' N).filter (x' ∣ ·)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hy0, hyN⟩, hdvd⟩
      have := Nat.le_of_dvd hy0 hdvd
      rcases Nat.eq_or_lt_of_le this with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨⟨h, hyN⟩, hdvd⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, hdvd⟩)
      · exact ⟨⟨hx', hN⟩, dvd_rfl⟩
      · exact ⟨⟨by omega, h2⟩, hdvd⟩
  have hcard := Nat.Ioc_filter_dvd_card_eq_div N x'
  rw [hset, Finset.card_insert_of_notMem (by simp)] at hcard
  omega

/-- The count used in Lemma 4.1: if `0 < x' ≤ M`, then `|𝒴| ≥ N/M − 2`. -/
theorem card_multiples_Ioc_ge (N : ℕ) {x' : ℕ} (hx' : 0 < x') {M : ℝ} (hx'M : (x' : ℝ) ≤ M) :
    (N : ℝ) / M - 2 ≤ ((Finset.Ioc x' N).filter (x' ∣ ·)).card := by
  rw [card_multiples_Ioc N hx']
  have hx'r : (0 : ℝ) < x' := by exact_mod_cast hx'
  -- `⌊N/x'⌋ > N/x' − 1`.
  have hfloor : (N : ℝ) / x' - 1 < (N / x' : ℕ) := by
    have h1 : N < (N / x' + 1) * x' := by
      have := Nat.lt_div_mul_add (a := N) hx'
      linarith
    have h2 : (N : ℝ) < ((N / x' : ℕ) + 1) * x' := by exact_mod_cast h1
    rw [div_sub_one hx'r.ne', div_lt_iff₀ hx'r]
    linarith
  have hsub : ((N / x' : ℕ) : ℝ) - 1 ≤ ((N / x' - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N / x') with h | h
    · simp [h]
    · rw [Nat.cast_sub h]
      simp
  have hmono : (N : ℝ) / M ≤ (N : ℝ) / x' :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hx'r hx'M
  linarith

end HubRemoval
