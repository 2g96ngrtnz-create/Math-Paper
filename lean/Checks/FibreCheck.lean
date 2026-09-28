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
