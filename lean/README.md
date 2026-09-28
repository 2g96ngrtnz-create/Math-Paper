# Lean 4 formalisation of `paper/hub_removal.tex`

The lemmas are formalised one at a time, each checked before the next is started.

## Setup

- **Versions:** Lean `v4.34.1` (`lean-toolchain`) and Mathlib `v4.34.1` (`lakefile.toml`). The exact dependency revisions are in `lake-manifest.json`.
- **Mathlib was built from source:** `lake build Mathlib`, 8,930 jobs, 0 errors, about 2 h 38 min on 4 cores. The Mathlib build cache was not reachable from the build environment.
- **The official Lean release is also published on GitHub.** In that environment elan's usual download host was blocked, so the toolchain came from `https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.zip` (sha256 `3013aba0…1ddac`). It was unpacked into `~/.elan/toolchains/leanprover--lean4---v4.34.1`.

To build and check:

```sh
lake build HubRemoval                   # the formalised lemmas
lake env lean InstallCheck.lean         # install sanity checks (must succeed)
lake env lean Checks/NegativeCheck.lean # a false statement (must FAIL)
lake env lean Checks/FibreCheck.lean    # axioms and concrete instances
```

## Status

| Paper result | Lean name | File | Status |
|---|---|---|---|
| Lemma 3.1(a), first part: if d ∣ m, K < d and m ≤ N, then m/d ≤ ⌊N/(K+1)⌋ | `HubRemoval.cofactor_le_B` | `HubRemoval/Fibre.lean` | **Proved.** No `sorry`; axioms are `propext` and `Quot.sound` only. |

All other lemmas of the paper are not yet formalised.
