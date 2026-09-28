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
lake env lean Checks/SubSumCheck.lean
lake env lean Checks/MonotoneCheck.lean
lake env lean Checks/RobustCheck.lean
lake env lean Checks/SigmaCheck.lean
lake env lean Checks/AttachCheck.lean
lake env lean Checks/TuranCheck.lean
lake env lean Checks/CoreCheck.lean
lake env lean Checks/CoreParamsCheck.lean
```

## Status

"Standard axioms" means that `#print axioms` shows only a subset of Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. In particular there is no `sorryAx`.

| Paper result | Lean name | File | Status |
|---|---|---|---|
| Lemma 2.4: for z ≤ N, ∑_{m≤N} (ω_z(m) − L)² ≤ 3NL; for 2 ≤ z ≤ N and s ≤ L/2, #{m ≤ N : ω_z(m) < s} ≤ 12N/L | `turan_variance`, `turan_count` | `HubRemoval/Turan.lean` | **Proved.** Standard axioms. z is a natural number, which loses nothing because the primes ≤ z are the primes ≤ ⌊z⌋. The hypothesis 0 ≤ s is not needed. Checks in `Checks/TuranCheck.lean`, including an exact evaluation over ℚ for N = 100, z = 7 |
| Lemma 3.1(a), part 1: if d ∣ m, K < d and m ≤ N, then m/d ≤ ⌊N/(K+1)⌋ | `cofactor_le_B` | `HubRemoval/Fibre.lean` | **Proved.** Axioms: `propext`, `Quot.sound`. |
| Lemma 3.1(a), part 2: along an edge (d ∣ m, K < d < m ≤ N), R_B(d) = R_B(m) | `roughPart_eq_of_edge` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(b): R_B is constant on connected components of G_{N,K} | `roughPart_eq_of_reachable` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(c): \|V_n\| ≤ Ψ(N/n,B) ≤ Ψ(N,B); V_1 = F_1; \|F_1\| = Ψ(N,B) − Ψ(K,B); \|V_n\| ≤ K for n > 1 | `card_fibre_le`, `card_fibre_le_psi`, `fibre_one`, `card_smoothFibre`, `card_fibre_le_K` | `HubRemoval/FibreCount.lean` | **Proved.** Standard axioms. Checks in `Checks/FibreCountCheck.lean` |
| Proposition 3.2: for any orientation of G_{N,K}, a strongly connected set lies in one fibre and has ≤ Ψ(N,B) and ≤ max(\|F_1\|, K) elements | `stronglyConnected_subset_fibre`, `stronglyConnected_card_le_psi`, `stronglyConnected_card_le_max` | `HubRemoval/UpperBound.lean` | **Proved.** Standard axioms. The orientation is modelled as any relation whose arcs are edges, which is slightly more general. Checks in `Checks/UpperBoundCheck.lean` |
| Lemma 4.1, deterministic part: on the event 𝓡, both ends of each edge of G_{M,K} lie in one SCC, so each component of G_{M,K} lies in one SCC; and \|𝒴\| = ⌊N/x'⌋ − 1 ≥ N/M − 2 | `robust_adj`, `robust_reachable`, `card_multiples_Ioc`, `card_multiples_Ioc_ge` | `HubRemoval/Robust.lean` | **Proved.** Standard axioms. The probability bound P(𝓡ᶜ) ≤ M²(1 − q)^{N^{2δ} − 2} is **not** formalised; it needs a model of the random orientation. Checks in `Checks/RobustCheck.lean` |
| Lemma 4.2: for real M ≥ 4(K+1), all x ∈ (K, M] with P⁺(x) ≤ M/(2(K+1)) lie in one component of G_{M,K} | `doubling`, `doubling_connected` | `HubRemoval/Doubling.lean` | **Proved.** Standard axioms. Checks in `Checks/DoublingCheck.lean` |
| Corollary 4.3: if M ≥ 4(K+1), then on 𝓡 all of S_M lies in one SCC Σ; if also M ≤ N, then Σ ⊆ F_1 | `sigma_mutual`, `goodSet_mem_smoothFibre`, `sigma_subset_smoothFibre` | `HubRemoval/Sigma.lean` | **Proved.** Standard axioms. Checks in `Checks/SigmaCheck.lean` |
| Lemma 4.4: on A_m ∩ 𝓡, m ∈ Σ; and P(A_m) = 1 − ρ^s − (1 − ρ)^s ≥ 1 − 2λ^s for s ≥ 1 | `attach_mutual`, `sum_weight`, `prob_attach`, `prob_attach_ge` | `HubRemoval/Attach.lean` | **Proved.** Standard axioms. The probability is proved in the finite product model on the s edges {d, m}. The product measure on all orientations of G_{N,K}, and the marginalisation to these s edges, are **not** formalised. Checks in `Checks/AttachCheck.lean`, including a brute-force evaluation over ℚ |
| Lemma 4.5(c), counting argument: if P⁺(m) ≤ Y and ω_z(m) ≥ s₀, then s(m) ≥ s₀ + 1, given the inequalities between M, z, E₀, E₁ that the proof uses | `core_divisors`, `exists_dvd_mem_Ico` | `HubRemoval/Core.lean` | **Proved.** Standard axioms. M, z, E₀, E₁ are abstract reals, and the inequalities between them are hypotheses; the next row discharges them. Checks in `Checks/CoreCheck.lean` |
| Lemma 4.5(a)–(c) with the paper's parameters: from (H1) K ≤ N^{1−η}, (H2) N^{η/4} ≥ 4, (H3) N^{δ/s₀} ≥ 2 and 0 < δ ≤ η/8: (a) M ≥ 4(K+1); (b) 𝒰 ⊆ F_1 and m > M on 𝒰; (c) s(m) ≥ s₀ + 1 on 𝒰 | `core_a`, `core_b`, `core_c` | `HubRemoval/CoreParams.lean` | **Proved.** Standard axioms. Part (d) needs Mertens' theorem and is **not** formalised. Checks in `Checks/CoreParamsCheck.lean` (N = 2¹⁶, η = 1/2, δ = 1/16, K = 10) |
| Lemma 6.1: if U ⊆ V(D), the largest SCC of D[U] is at most the largest SCC of D; so Φ_{K'} ≤ Φ_K for K ≤ K' and a fixed orientation | `maxSCC_mono`, `maxSCC_Ioc_antitone` | `HubRemoval/Monotone.lean` | **Proved.** Standard axioms. `maxSCC` is the largest strongly connected set, which equals the largest SCC. Checks in `Checks/MonotoneCheck.lean` |
| Lemma A.1: if x₁, …, xₙ sum to 1, 0 < θ ≤ 1/3 and every xᵢ < 1 − θ, some sub-sum lies in [θ, 1/2]; the bound 1/3 is sharp | `subsum`, `subsum_of_mem_Icc`, `subsum_sharp` | `HubRemoval/SubSum.lean` | **Proved.** Standard axioms. Only finite sequences are covered; the paper also allows infinite ones. Neither monotonicity nor xᵢ ≥ 0 is needed. Checks in `Checks/SubSumCheck.lean` |

All other lemmas of the paper are not yet formalised.
