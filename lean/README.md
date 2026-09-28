# Lean 4 formalisation of `paper/hub_removal.tex`

The lemmas are formalised one at a time. Each is compiled and checked before it is marked proved.

## Setup

- **Versions:** Lean `v4.34.1` (`lean-toolchain`) and Mathlib `v4.34.1` (`lakefile.toml`). The exact dependency revisions are in `lake-manifest.json`.
- **Getting Mathlib:** `lake exe cache get` downloads the prebuilt Mathlib, 8,908 files in about 80 seconds. This needs `cache.mathlib.org` to be reachable. `lake build Mathlib --no-build` then confirms that all 8,923 targets are up to date. Without the cache, `lake build Mathlib` builds it from source: 8,930 jobs, about 2 h 38 min on 4 cores. That was done once in this project, with 0 errors.
- **Getting Lean:** elan installs Lean from `release.lean-lang.org`. The same release is also published on GitHub, at `https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.zip` (sha256 `3013aba0…1ddac`). It can be unpacked into `~/.elan/toolchains/leanprover--lean4---v4.34.1` if the usual host is blocked.

To build and check:

```sh
lake build HubRemoval                   # the formalised lemmas
lake env lean InstallCheck.lean         # install sanity checks (must succeed)
lake env lean Checks/NegativeCheck.lean # a false statement (must FAIL)
lake env lean Checks/FibreCheck.lean    # axioms and concrete instances
lake env lean Checks/FibreCountCheck.lean
lake env lean Checks/UpperBoundCheck.lean
lake env lean Checks/DoublingCheck.lean
```

## Status

"Standard axioms" means that `#print axioms` shows only a subset of Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. In particular there is no `sorryAx`.

| Paper result | Lean name | File | Status |
|---|---|---|---|
| Lemma 3.1(a), part 1: if d ∣ m, K < d and m ≤ N, then m/d ≤ ⌊N/(K+1)⌋ | `cofactor_le_B` | `HubRemoval/Fibre.lean` | **Proved.** Axioms: `propext`, `Quot.sound`. |
| Lemma 3.1(a), part 2: along an edge (d ∣ m, K < d < m ≤ N), R_B(d) = R_B(m) | `roughPart_eq_of_edge` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(b): R_B is constant on connected components of G_{N,K} | `roughPart_eq_of_reachable` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(c): \|V_n\| ≤ Ψ(N/n,B) ≤ Ψ(N,B); V_1 = F_1; \|F_1\| = Ψ(N,B) − Ψ(K,B); \|V_n\| ≤ K for n > 1 | `card_fibre_le`, `card_fibre_le_psi`, `fibre_one`, `card_smoothFibre`, `card_fibre_le_K` | `HubRemoval/FibreCount.lean` | **Proved.** Standard axioms. Checks in `Checks/FibreCountCheck.lean` |
| Proposition 3.2: for any orientation of G_{N,K}, a strongly connected set lies in one fibre and has ≤ Ψ(N,B) and ≤ max(\|F_1\|, K) elements | `stronglyConnected_subset_fibre`, `stronglyConnected_card_le_psi`, `stronglyConnected_card_le_max` | `HubRemoval/UpperBound.lean` | **Proved.** Standard axioms. The orientation is modelled as any relation whose arcs are edges, which is slightly more general. Checks in `Checks/UpperBoundCheck.lean` |
| Lemma 4.2: for real M ≥ 4(K+1), all x ∈ (K, M] with P⁺(x) ≤ M/(2(K+1)) lie in one component of G_{M,K} | `doubling`, `doubling_connected` | `HubRemoval/Doubling.lean` | **Proved.** Standard axioms. Checks in `Checks/DoublingCheck.lean` |
| Lemma A.1: sub-sum lemma, and its sharpness at 1/3 | | `HubRemoval/SubSum.lean` | Draft, not yet compiled |

All other lemmas of the paper are not yet formalised.
