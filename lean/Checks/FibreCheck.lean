import HubRemoval.Fibre
open HubRemoval

#print axioms cofactor_le_B
#check @cofactor_le_B

-- Concrete instance where the bound is attained: N = 100, K = 10, so B = 100 / 11 = 9;
-- the edge 11 ∣ 99 has cofactor 99 / 11 = 9 = B.
example : 99 / 11 ≤ 100 / (10 + 1) := cofactor_le_B ⟨9, rfl⟩ (by norm_num) (by norm_num)
example : (99 / 11 : ℕ) = 100 / (10 + 1) := by norm_num

-- K = 0 (vertex 1 kept): B = N, and the bound is m / d ≤ N.
example (N d m : ℕ) (h : d ∣ m) (hd : 0 < d) (hm : m ≤ N) : m / d ≤ N / (0 + 1) :=
  cofactor_le_B h hd hm

/-! ### Lemma 3.1(a), second part -/

#print axioms roughPart_eq_of_edge
#check @roughPart_eq_of_edge

-- Values of the rough part (B = 9): R_9(11) = 11, R_9(99) = R_9(9 * 11) = 11,
-- R_9(2) = 1, R_9(22) = 11, R_9(1) = 1.
#eval (roughPart 9 11, roughPart 9 99, roughPart 9 2, roughPart 9 22, roughPart 9 1)

-- The edge 11 ∣ 99 in the graph on {11, …, 100} (N = 100, K = 10, B = 9):
-- the lemma gives R_9(11) = R_9(99).
example : roughPart (100 / (10 + 1)) 11 = roughPart (100 / (10 + 1)) 99 :=
  roughPart_eq_of_edge ⟨9, rfl⟩ (by norm_num) (by norm_num) (by norm_num)

-- The cofactor hypothesis matters: 2 ∣ 22 with B = 9 has cofactor 11 > 9, and the rough
-- parts differ (R_9(2) = 1, R_9(22) = 11). In the paper this pair is never an edge,
-- since vertices are > K = 10.
-- (A test assertion, evaluated like `#eval`; the kernel cannot reduce `Nat.factorization`.)
#guard roughPart 9 2 ≠ roughPart 9 22

/-! ### Lemma 3.1(b) -/

#print axioms roughPart_eq_of_reachable

-- A walk 22 — 11 — 99 in G_{100,10} (both are edges: 11 ∣ 22 and 11 ∣ 99), so R_9(22) = R_9(99).
example : roughPart (100 / (10 + 1)) 22 = roughPart (100 / (10 + 1)) 99 := by
  have h1 : (divGraph 100 10).Adj 22 11 := ⟨by decide, by decide, by decide, by decide,
    by decide, Or.inr ⟨2, rfl⟩⟩
  have h2 : (divGraph 100 10).Adj 11 99 := ⟨by decide, by decide, by decide, by decide,
    by decide, Or.inl ⟨9, rfl⟩⟩
  exact roughPart_eq_of_reachable (h1.reachable.trans h2.reachable)
