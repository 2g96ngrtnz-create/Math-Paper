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
```

## Status

"Standard axioms" means that `#print axioms` shows only a subset of Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. In particular there is no `sorryAx`.

| Paper result | Lean name | File | Status |
|---|---|---|---|
| Lemma 3.1(a), part 1: if d ∣ m, K < d and m ≤ N, then m/d ≤ ⌊N/(K+1)⌋ | `cofactor_le_B` | `HubRemoval/Fibre.lean` | **Proved.** Axioms: `propext`, `Quot.sound`. |
| Lemma 3.1(a), part 2: along an edge (d ∣ m, K < d < m ≤ N), R_B(d) = R_B(m) | `roughPart_eq_of_edge` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(b): R_B is constant on connected components of G_{N,K} | `roughPart_eq_of_reachable` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(c): fibre sizes | | `HubRemoval/FibreCount.lean` | Draft, not yet compiled |
| Proposition 3.2: upper bound for any orientation | | `HubRemoval/UpperBound.lean` | Draft, not yet compiled |
| Lemma 4.2: doubling connectivity | | `HubRemoval/Doubling.lean` | Draft, not yet compiled |
| Lemma A.1: sub-sum lemma, and its sharpness at 1/3 | | `HubRemoval/SubSum.lean` | Draft, not yet compiled |

All other lemmas of the paper are not yet formalised.
