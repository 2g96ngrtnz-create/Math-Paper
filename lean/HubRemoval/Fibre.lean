import Mathlib

/-!
# Fibres of the divisor graph (paper, Lemma 3.1)

This file formalises Lemma 3.1 of `paper/hub_removal.tex`, one part at a time.

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

end HubRemoval
