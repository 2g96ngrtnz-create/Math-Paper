# Hub removal in randomly oriented divisor graphs

A solution of Question 20 of Kim–Phillips, *On the largest strongly connected component of randomly oriented divisor graphs* (arXiv:2604.05176v2).

**Main result.** Delete the vertices 1,…,K from the randomly oriented divisor graph 𝒟_ρ(N), for fixed ρ ∈ (0,1). The expected size of the largest strongly connected component is then

  Ψ(N, N/(K+1)) + O(N / log log N), uniformly in K.

Here Ψ(x, y) counts the y-smooth integers up to x. For K = N^{θ+o(1)} the limit profile is therefore ρ_Dick(1/(1−θ)) on [0,1), where ρ_Dick is Dickman's function.

- `paper/hub_removal.tex`, `paper/hub_removal.pdf`: paper draft with complete proofs.
- `STATUS.md`: report by target (T1–T5) and a status table for every claim.
- `lean/`: Lean 4 + Mathlib formalisation of every numbered statement of the paper (no `sorry`, standard axioms only); `lean/README.md` maps each statement to its Lean names. Check it with `cd lean && lake build HubRemoval`.

Build the paper with `cd paper && pdflatex hub_removal.tex && pdflatex hub_removal.tex`.
