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
lake env lean Checks/DivisorCheck.lean
lake env lean Checks/SandwichCheck.lean
lake env lean Checks/PsiUpperCheck.lean
lake env lean Checks/CoreDCheck.lean
lake env lean Checks/FiniteProbCheck.lean
lake env lean Checks/OrientationCheck.lean
lake env lean Checks/RobustProbCheck.lean
lake env lean Checks/AttachProbCheck.lean
lake env lean Checks/LowerBoundCheck.lean
lake env lean Checks/MertensCheck.lean
lake env lean Checks/Mertens2Check.lean
lake env lean Checks/UnconditionalCheck.lean
```

## Status

"Standard axioms" means that `#print axioms` shows only a subset of Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. In particular there is no `sorryAx`.

| Paper result | Lean name | File | Status |
|---|---|---|---|
| Lemma 2.1(a), Mertens-type: ∑_{p≤n} log p/(p−1) ≤ log n + c₀ for n ≥ 1, with c₀ = log 4 + 2 | `mertens_a`, `sum_log_div_le`, `theta_le` | `HubRemoval/Mertens.lean` | **Proved from scratch.** Standard axioms. The paper cites Mertens. Here: θ(n) ≤ n log 4 (primorial ≤ 4ⁿ, from Mathlib); Legendre plus n! ≤ nⁿ gives ∑ log p/p ≤ log n + log 4; and a telescoping bound gives ∑ log p/(p(p−1)) ≤ 2. Parts (b)–(d) are in the next row. Checks in `Checks/MertensCheck.lean` |
| Lemma 2.1(b)–(d), and the full Lemma 2.1: for real 2 ≤ y ≤ w, \|∑_{y<p≤w} 1/p − log(log w/log y)\| ≤ C₁/log y; ∑_{p≤z} 1/p ≥ log log z − C₁ for z ≥ 2; π(x) ≤ C₁x/log x for x ≥ 2; with c₀ = log 4 + 2 and C₁ = 18 | `lemma_2_1`, `mertens_b`, `mertens_b_nat`, `mertens_c`, `mertens_d`, `abs_Smert_sub_log_le` | `HubRemoval/Mertens2.lean` | **Proved from scratch.** Standard axioms. Mertens' first theorem \|∑_{p≤n} log p/p − log n\| ≤ 3 comes from Legendre and nⁿ/eⁿ ≤ n! ≤ nⁿ. (b) follows by Abel summation: 8/log y for integers, 18/log y for reals. (c) has constant 13 and (d) has constant 5. Checks in `Checks/Mertens2Check.lean`, including a floating-point sanity check of the constants |
| Lemma 2.3: for x ≥ 2, Ψ(x,y) ≤ √x + 2x(log y + c₀)/log x | `psi_upper`, `psi_upper'`, `sum_log_smooth_le` | `HubRemoval/PsiUpper.lean` | **Proved.** Standard axioms. `psi_upper` takes Mertens' estimate as a hypothesis. `psi_upper'` is unconditional, with c₀ = log 4 + 2 from the proof of Lemma 2.1(a) in the next row. Legendre's theorem comes from Mathlib. The consequence ρ(u) ≤ 2/u needs Dickman's theorem and is **not** formalised. Checks in `Checks/PsiUpperCheck.lean` |
| Lemma 2.4: for z ≤ N, ∑_{m≤N} (ω_z(m) − L)² ≤ 3NL; for 2 ≤ z ≤ N and s ≤ L/2, #{m ≤ N : ω_z(m) < s} ≤ 12N/L | `turan_variance`, `turan_count` | `HubRemoval/Turan.lean` | **Proved.** Standard axioms. z is a natural number, which loses nothing because the primes ≤ z are the primes ≤ ⌊z⌋. The hypothesis 0 ≤ s is not needed. Checks in `Checks/TuranCheck.lean`, including an exact evaluation over ℚ for N = 100, z = 7 |
| Lemma 2.5: for every ε > 0 there is C_ε > 0 with τ(n) ≤ C_ε n^ε for all n ≥ 1 | `divisor_bound` | `HubRemoval/Divisor.lean` | **Proved.** Standard axioms. Explicit constant C_ε = max(1, 1/(ε log 2))^{⌈2^{1/ε}⌉}. Checks in `Checks/DivisorCheck.lean` |
| Lemma 3.1(a), part 1: if d ∣ m, K < d and m ≤ N, then m/d ≤ ⌊N/(K+1)⌋ | `cofactor_le_B` | `HubRemoval/Fibre.lean` | **Proved.** Axioms: `propext`, `Quot.sound`. |
| Lemma 3.1(a), part 2: along an edge (d ∣ m, K < d < m ≤ N), R_B(d) = R_B(m) | `roughPart_eq_of_edge` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(b): R_B is constant on connected components of G_{N,K} | `roughPart_eq_of_reachable` | `HubRemoval/Fibre.lean` | **Proved.** Standard axioms. |
| Lemma 3.1(c): \|V_n\| ≤ Ψ(N/n,B) ≤ Ψ(N,B); V_1 = F_1; \|F_1\| = Ψ(N,B) − Ψ(K,B); \|V_n\| ≤ K for n > 1 | `card_fibre_le`, `card_fibre_le_psi`, `fibre_one`, `card_smoothFibre`, `card_fibre_le_K` | `HubRemoval/FibreCount.lean` | **Proved.** Standard axioms. Checks in `Checks/FibreCountCheck.lean` |
| Proposition 3.2: for any orientation of G_{N,K}, a strongly connected set lies in one fibre and has ≤ Ψ(N,B) and ≤ max(\|F_1\|, K) elements | `stronglyConnected_subset_fibre`, `stronglyConnected_card_le_psi`, `stronglyConnected_card_le_max` | `HubRemoval/UpperBound.lean` | **Proved.** Standard axioms. The orientation is modelled as any relation whose arcs are edges, which is slightly more general. Checks in `Checks/UpperBoundCheck.lean` |
| Lemma 4.1, deterministic part: on the event 𝓡, both ends of each edge of G_{M,K} lie in one SCC, so each component of G_{M,K} lies in one SCC; and \|𝒴\| = ⌊N/x'⌋ − 1 ≥ N/M − 2 | `robust_adj`, `robust_reachable`, `card_multiples_Ioc`, `card_multiples_Ioc_ge` | `HubRemoval/Robust.lean` | **Proved.** Standard axioms. The probability bound is in the row "Lemma 4.1, probability bound". Checks in `Checks/RobustCheck.lean` |
| Lemma 4.1, probability bound: in 𝒟_ρ(N,K), P(𝓡ᶜ) ≤ M²(1 − q)^{N/M − 2}, and ≤ N² exp(−q(N/M − 2)) if M ≤ N, where q = ρ(1−ρ) | `prob_not_robust`, `prob_not_robust_exp`, `prob_pat`, `prob_no_pat` | `HubRemoval/RobustProb.lean` | **Proved.** Standard axioms. The witnesses for a fixed pair are independent, by `expectP_prod_of_pairwiseDisjoint` on disjoint edge blocks. Then a union bound over at most ⌊M⌋²/2 pairs. Checks in `Checks/RobustProbCheck.lean`, e.g. P(𝓡ᶜ) < 10⁻¹⁰ in 𝒟_{1/2}(400,1) with M = 4 |
| Lemma 4.2: for real M ≥ 4(K+1), all x ∈ (K, M] with P⁺(x) ≤ M/(2(K+1)) lie in one component of G_{M,K} | `doubling`, `doubling_connected` | `HubRemoval/Doubling.lean` | **Proved.** Standard axioms. Checks in `Checks/DoublingCheck.lean` |
| Corollary 4.3: if M ≥ 4(K+1), then on 𝓡 all of S_M lies in one SCC Σ; if also M ≤ N, then Σ ⊆ F_1 | `sigma_mutual`, `goodSet_mem_smoothFibre`, `sigma_subset_smoothFibre` | `HubRemoval/Sigma.lean` | **Proved.** Standard axioms. Checks in `Checks/SigmaCheck.lean` |
| Lemma 4.4: on A_m ∩ 𝓡, m ∈ Σ; and P(A_m) = 1 − ρ^s − (1 − ρ)^s ≥ 1 − 2λ^s for s ≥ 1 | `attach_mutual`, `sum_weight`, `prob_attach`, `prob_attach_ge` | `HubRemoval/Attach.lean` | **Proved.** Standard axioms. The probability is computed exactly on the s edges {d, m}. The next row proves it in the full model 𝒟_ρ(N,K). Checks in `Checks/AttachCheck.lean`, including a brute-force evaluation over ℚ |
| Lemma 4.4 in the full model: for M < m ≤ N, P(A_m) ≥ 1 − ρ^s − (1−ρ)^s ≥ 1 − 2λ^s in 𝒟_ρ(N,K) | `prob_attachEv`, `prob_attachEv_ge`, `prob_all_bit` | `HubRemoval/AttachProb.lean` | **Proved.** Standard axioms. The complement of A_m lies in two cylinders on the s edges (d, m). Checks in `Checks/AttachProbCheck.lean` (m = 30 in 𝒟_{1/2}(48,1)) |
| Lemma 4.5(c), counting argument: if P⁺(m) ≤ Y and ω_z(m) ≥ s₀, then s(m) ≥ s₀ + 1, given the inequalities between M, z, E₀, E₁ that the proof uses | `core_divisors`, `exists_dvd_mem_Ico` | `HubRemoval/Core.lean` | **Proved.** Standard axioms. M, z, E₀, E₁ are abstract reals, and the inequalities between them are hypotheses; the next row discharges them. Checks in `Checks/CoreCheck.lean` |
| Lemma 4.5(a)–(c) with the paper's parameters: from (H1) K ≤ N^{1−η}, (H2) N^{η/4} ≥ 4, (H3) N^{δ/s₀} ≥ 2 and 0 < δ ≤ η/8: (a) M ≥ 4(K+1); (b) 𝒰 ⊆ F_1 and m > M on 𝒰; (c) s(m) ≥ s₀ + 1 on 𝒰 | `core_a`, `core_b`, `core_c` | `HubRemoval/CoreParams.lean` | **Proved.** Standard axioms. Part (d) is in the next row. Checks in `Checks/CoreParamsCheck.lean` (N = 2¹⁶, η = 1/2, δ = 1/16, K = 10) |
| Lemma 4.5(d): \|F_1 \ 𝒰\| ≤ N^{1−δ} + N(4δ/η + 2(1+C₁)/(η log N)) + #{m ≤ N : ω_z(m) < s₀} | `core_d`, `core_d'`, `CoreHyp.log_Y_ge`, `CoreHyp.log_B_sub_log_Y` | `HubRemoval/CoreD.lean` | **Proved.** Standard axioms. `core_d` takes the instance of Lemma 2.1(b) at y = Y, w = B as a hypothesis. `core_d'` in `HubRemoval/Unconditional.lean` discharges it with C₁ = 18. Checks in `Checks/CoreDCheck.lean` and `Checks/UnconditionalCheck.lean` |
| Proposition 4.6, eq. (4.1): in 𝒟_ρ(N,K) under the hypotheses of Lemma 4.5, E[Φ_K] ≥ Ψ(N,B) − K − \|F_1 \ 𝒰\| − 2λ^{s₀+1}N − N·P(𝓡ᶜ); in the paper's form, E[Φ_K] ≥ Ψ(N,B) − K − Err − N·P(𝓡ᶜ); with Lemma 4.1, Ψ(N,B) − K − Err − N³exp(−q(N^{2δ}−2)) ≤ E[Φ_K] ≤ Ψ(N,B) | `lower_bound`, `lower_bound_err'`, `fixedN_sandwich'`, `expect_PhiK_le_psi` | `HubRemoval/LowerBound.lean` | **Proved, unconditionally.** Standard axioms. `lower_bound_err'` and `fixedN_sandwich'` (in `HubRemoval/Unconditional.lean`) need no hypotheses beyond the paper's, with C₁ = 18. The unprimed versions take the Mertens instance as a hypothesis. Eq. (4.2), E[\|F_1 \ Σ\|·1_𝓡] ≤ Err, is **not** yet formalised. Checks in `Checks/LowerBoundCheck.lean` (𝒟_{1/2}(2¹⁶, 10), with the Mertens instance proved) |
| Lemma 6.1: if U ⊆ V(D), the largest SCC of D[U] is at most the largest SCC of D; so Φ_{K'} ≤ Φ_K for K ≤ K' and a fixed orientation | `maxSCC_mono`, `maxSCC_Ioc_antitone` | `HubRemoval/Monotone.lean` | **Proved.** Standard axioms. `maxSCC` is the largest strongly connected set, which equals the largest SCC. Checks in `Checks/MonotoneCheck.lean` |
| Lemma 6.2: if 0 < ε ≤ 1/2, 1 ≤ K < N and (N/K)(ε/2) ≥ τ̂ + 5, where τ̂ bounds τ(n) for n ≤ N, then a static or adaptive top-K set T satisfies {v ≥ 1 : v ≤ (1−ε)K} ⊆ T ⊆ {t : t ≤ (1+ε)K} | `sandwich_static`, `sandwich_adaptive` | `HubRemoval/Sandwich.lean` | **Proved.** Standard axioms. Degrees are cardinalities of explicit neighbour sets in G_N − T. Checks in `Checks/SandwichCheck.lean`, including the paper's degree formula for all m ≤ 100 |
| Lemma A.1: if x₁, …, xₙ sum to 1, 0 < θ ≤ 1/3 and every xᵢ < 1 − θ, some sub-sum lies in [θ, 1/2]; the bound 1/3 is sharp | `subsum`, `subsum_of_mem_Icc`, `subsum_sharp` | `HubRemoval/SubSum.lean` | **Proved.** Standard axioms. Only finite sequences are covered; the paper also allows infinite ones. Neither monotonicity nor xᵢ ≥ 0 is needed. Checks in `Checks/SubSumCheck.lean` |
| Infrastructure: finite product probability (the model of a random orientation) | `sum_wt`, `prob_cylinder`, `expectP_mul_of_disjoint`, `expectP_prod_of_pairwiseDisjoint`, `prob_exists_le`, `prob_and_ge` | `HubRemoval/FiniteProb.lean` | **Proved.** Standard axioms. Outcomes are ω : ι → Bool with independent Bernoulli(ρ) coordinates, and expectations are finite sums. Includes cylinder probabilities, independence for functions of disjoint coordinate blocks, and the union bound. Checks in `Checks/FiniteProbCheck.lean`, including a case showing disjointness is needed |
| Infrastructure: the random orientation 𝒟_ρ(N,K), and Proposition 3.2 in it: Φ_K(ω) ≤ Ψ(N,B) and Φ_K(ω) ≤ max(\|F_1\|, K) for every outcome ω | `edges`, `arc`, `PhiK`, `PhiK_le_psi`, `PhiK_le_max`, `card_le_PhiK` | `HubRemoval/Orientation.lean` | **Proved.** Standard axioms. An outcome is ω : Edge N K → Bool, where true means reversed. Checks in `Checks/OrientationCheck.lean` (a directed 3-cycle in G_{4,0}) |

All other lemmas of the paper are not yet formalised.
