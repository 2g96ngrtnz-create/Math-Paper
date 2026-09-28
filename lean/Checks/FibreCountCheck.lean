import HubRemoval.FibreCount
open HubRemoval

/-! ### Lemma 3.1(c): axioms -/

#print axioms card_fibre_le
#print axioms card_fibre_le_psi
#print axioms fibre_one
#print axioms card_smoothFibre
#print axioms card_fibre_le_K

/-! ### Concrete values (N = 100, K = 10, so B = 9) -/

-- Ψ(100, 9), Ψ(10, 9), |F₁|: the lemma says |F₁| = Ψ(100,9) − Ψ(10,9).
#eval (psi 100 9, psi 10 9, (smoothFibre 100 10).card)
#guard (smoothFibre 100 10).card = psi 100 9 - psi 10 9

-- V₁ = F₁, checked extensionally.
#guard fibre 100 10 1 = smoothFibre 100 10

-- The fibre of n = 11 is {11, 22, …, 99}: 9 elements, at most Ψ(100/11, 9) = Ψ(9, 9) = 9 and ≤ K = 10.
#eval ((fibre 100 10 11).card, psi (100 / 11) 9)
#guard (fibre 100 10 11).card ≤ psi (100 / 11) 9
#guard (fibre 100 10 11).card ≤ 10

/-! ### Cross-check with the independent Python computation of the audit (red-team RT-3)

For N = 1000, K = 10 and for N = 10000, K = 31 the largest fibre `V_n` with `n > 1` has exactly
`K` elements, so the bound `|V_n| ≤ K` is attained. -/

def maxNonSmoothFibre (N K : ℕ) : ℕ :=
  ((vertices N K).image (roughPart (N / (K + 1)))).sup
    (fun n => if n = 1 then 0 else (fibre N K n).card)

#eval maxNonSmoothFibre 1000 10
#guard maxNonSmoothFibre 1000 10 = 10
