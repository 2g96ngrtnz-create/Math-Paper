# PROOF_SKELETON — `hub_removal.tex`

Phase 0.5 proof-obligation ledger for the `proof-checker` run of 2026-09-28 (run 01).
Input: `paper/hub_removal.tex` at commit `055505f` (sha256 `4d562ccc…0090`). Line numbers refer to that version.

Labels such as Lemma 4.5 refer to the compiled numbering. Lemma 2.7 (`lem:psi-limit`) is introduced by Fix F6 during this run.

---

## 0. Section map

| Lines | Block | Label | Key claim |
|---|---|---|---|
| 57 | Question 1.1 | `q:KP` | Kim–Phillips Question 20 (quoted) |
| 88 | Theorem 1.2 | `thm:main` | Φ_K ≤ Ψ(N,B) pointwise; (Ψ − EΦ_K)/N → 0 uniformly in K |
| 95 | Theorem 1.3 | `thm:rate` | 0 ≤ Ψ(N,B) − EΦ_K ≤ 30N/log log N for N ≥ N₀(ρ), all K |
| 108 | Corollary 1.4 | `cor:profile` | EΦ_K/N → ρ_Dick(1/(1−θ)) |
| 116 | Corollary 1.5 | `cor:structure` | giant ≈ F₁; second SCC ≤ K + o(N) |
| 127 | Corollary 1.6 | `cor:degree` | same limit for degree attacks (θ < 1) |
| 179–257 | Lemmas 2.1–2.6 | `lem:mertens` … `lem:divisor` | arithmetic inputs |
| 265–302 | Lemma 3.1, Prop 3.2, Cor 3.3, Rem 3.4 | `lem:fibres`, `prop:upper`, … | upper bound |
| 316–466 | Lemmas 4.1–4.5, Cor 4.3, Prop 4.6 | `lem:robust` … `prop:lower` | lower bound |
| 472–557 | proofs; Remarks 5.1–5.3 | `rem:smallK`, `rem:second`, `rem:rho` | main proofs and extensions |
| 563–616 | Lemmas 6.1–6.2, proof of Cor 1.6 | `lem:mono`, `lem:sandwich` | degree attacks |
| 622–641 | Remarks 7.1–7.3, (O1)–(O5) | `rem:edges`, `rem:clique` | remarks, open problems |
| 650 | Lemma A.1 | `lem:subsum` | sub-sum lemma (not used) |

## 1. Dependency DAG

Edges read "A → B" meaning "B uses A". External inputs are marked [ext].

```
[ext] Mertens I/II, Chebyshev ──► L2.1
[ext] Dickman, de Bruijn, Hildebrand ──► L2.2
L2.1(a) ─► L2.3 ◄─ L2.2 (only for the consequence ρ_Dick(u) ≤ 2/u)
(counting only) ─► L2.4
(counting only) ─► L2.6
(counting only) ─► L3.1 ─► P3.2
L2.2, L2.3 ─► L2.7 [added by Fix F6] ─► C3.3, C1.4
(counting, independence of distinct edges) ─► L4.1
(counting only) ─► L4.2
L4.1, L4.2, P3.2 ─► C4.3 ─► L4.4
L2.1(b) ─► L4.5
L4.1, L4.4, L4.5, C4.3, L3.1 ─► P4.6
P3.2, P4.6, L2.1(c), L2.3, L2.4, L4.5 ─► T1.3 ─► T1.2
T1.3, L2.1(b),(d) ─► R5.1
T1.2, L2.7 ─► C1.4
P3.2, P4.6, C4.3, L3.1, T1.3 ─► C1.5
T1.2, L2.1(b), L3.1, [ext] KP Cor. 2, [ext] Bertrand ─► R5.2
P4.6, L2.1(c), L2.3, L2.4 ─► R5.3
L2.6, L6.1, L6.2, C1.4 ─► C1.6
(counting only) ─► R7.1, A.1
R7.2: SKETCH, no outgoing edges
```

**Cycle check.** A topological order exists:
L2.1, L2.2, L2.3, L2.4, L2.6, L2.7, L3.1, P3.2, C3.3, L4.1, L4.2, C4.3, L4.4, L4.5, P4.6, T1.3, T1.2, R5.1, C1.4, C1.5, R5.2, R5.3, L6.1, L6.2, C1.6.
So there is no cycle.

**Semantic circularity.** In the input version, C3.3 cited "the computation inside the proof of C1.4". The proof of C1.4 begins with T1.2, which depends on P3.2 but not on C3.3. So there was no cycle, only a forward reference. Fix F6 replaces it with L2.7.

## 2. Assumption ledger (hypothesis discharge at every application)

| Applied result | Where applied | Hypotheses | Discharged by |
|---|---|---|---|
| L2.1(a) | L2.3 | y ≥ 2 | L2.3 hypothesis 2 ≤ y ✓ |
| L2.1(b) | L4.5(d) | 2 ≤ Y ≤ B | Y ≥ 16 by L4.5(a); Y ≤ B in the non-empty case ✓ |
| L2.1(b) | R5.1 | 2 ≤ B ≤ N | B ≥ N^{1/4} ≥ 2 for N ≥ 16 ✓ |
| L2.1(b) | R5.2 | 2 ≤ √N ≤ N | N ≥ 25 ✓ |
| L2.1(c) | T1.3 (R2); R5.3 | z ≥ 2 | (R1); N large ✓ |
| L2.1(d) | R5.1 | x = N ≥ 2 | ✓ |
| L2.2 | L2.3 consequence | fixed u ≥ 1, U = u | ✓ |
| L2.2 | L2.7 (and so C1.4) | u_N ∈ [1, U], U = u+1 | u_N → u, so this holds for large N ✓ |
| L2.3 | T1.3 (K > N^{1−η}) | 2 ≤ B ≤ N | the case B ≥ 2; B ≤ N ✓ |
| L2.3 | L2.7 (θ = 1) | 2 ≤ y ≤ N | the case y ≥ 2 ✓ |
| L2.3 | R5.3 | 2 ≤ N^η ≤ N | monotonicity Ψ(N,B) ≤ Ψ(N,N^η) ✓ |
| L2.4 | T1.3 | N ∈ ℤ, 2 ≤ z ≤ N, s₀ ≤ L/2 | z = N^{δ/s₀} ≤ N; (R1); (R2) ✓ |
| L2.4 | R5.3 | same | L ≥ 2s₀ for large N ✓ |
| L2.6 | C1.6 | ε > 0 | ε = (1−θ)/2 > 0 because θ < 1; ε = κ in the last claim ✓ |
| L3.1 | P3.2, C1.5, R5.2 | 0 ≤ K < N | standing ✓ |
| P3.2 | C4.3, T1.3, C1.5 | none | ✓ |
| L4.1 | C4.3 | standing: N ≥ 2, 0 ≤ K < N, 0 < δ ≤ 1/8 | ✓ |
| L4.2 | C4.3 | M ≥ 4(K+1) | hypothesis of C4.3, discharged in P4.6 by L4.5(a) ✓ |
| C4.3 | L4.4 | M ≥ 4(K+1) | L4.5(a) ✓ |
| L4.4 | P4.6 | m ∈ V_{N,K}, m > M, s(m) ≥ 1 | L4.5(b), (c) ✓ |
| L4.5 | P4.6 | η ∈ (0,1), s₀ ∈ ℕ, 0 < δ ≤ η/8, (H1)–(H3) | hypotheses of P4.6 ✓ |
| L4.5 | T1.3 | same, plus δ ≤ 1/8 | η = 1/ℓ ∈ (0,1) for N > e^e; δ = 1/(8ℓ²) ≤ η/8; (H1) is the case split; (H2), (H3) by (R1) ✓ |
| P4.6 | T1.3, C1.5, R5.3 | as L4.5 | as above ✓ |
| T1.3 | T1.2, R5.1, C1.5 | N ≥ N₀(ρ) | T1.2 is a limit; R5.1 and C1.5 assume N ≥ N₀ ✓ |
| T1.2 | C1.4, R5.2 | fixed ρ ∈ (0,1) | ✓ |
| C1.4 | C1.6 | log(K_±+1)/log N → θ ∈ [0,1) | K_± = ⌊(1 ± ¼)K⌋ ✓ |
| L6.1 | C1.6 | T independent of the orientation | T is a function of G_N only ✓ |
| L6.2 | C1.6 | 0 < ε ≤ ½, 1 ≤ K < N, (N/K)(ε/2) ≥ τ_N + 5 | ε = ¼; N/K = N^{1−θ+o(1)} ≫ τ_N ✓ |
| [ext] KP Cor. 2 | R5.2 | fixed ρ ∈ (0,1), N′ → ∞ | N′ ≥ ⌊(K+1)/2⌋ → ∞ ✓ |
| [ext] Hildebrand 1986 | L2.2 | x ≥ 3, exp((log log x)^{5/3+ε}) ≤ y ≤ x | y = x^{1/u} ≥ x^{1/U} for large x ✓ |
| [ext] Bertrand | R5.2 | B ≥ 1 | ✓ |
| [ext] PNT (Fix F3) | discussion, (O1) | none | ✓ |

**Usage-minimal assumption sets.** Below, "section" means the standing assumptions of §4 (N ≥ 2, 0 ≤ K < N, 0 < δ ≤ 1/8).

| Result | Stated hypotheses | Used |
|---|---|---|
| L4.1 | section | section only; all three used |
| L4.2 | section + M ≥ 4(K+1) | same (M ≥ 4(K+1) gives Y ≥ 2 and 2^b > K) |
| L4.5 | (H1)–(H3), δ ≤ η/8 | all used: (H1) for K+1 ≤ 2N^{1−η}; (H2) in (a), (c)(ii), (d); (H3) for Step 2 to be meaningful; δ ≤ η/8 throughout |
| T1.3 | ρ ∈ (0,1) | q > 0 is used in (R5); λ < 1 is used for s₀ |

## 3. Typed symbol table

| Symbol | Type | Depends on | Notes |
|---|---|---|---|
| N | integer ≥ 2 | — | |
| K | integer, 0 ≤ K < N | — | |
| ρ | real ∈ (0,1) | — | reversal probability |
| q = ρ(1−ρ) | real ∈ (0, ¼] | ρ | |
| λ = max(ρ, 1−ρ) | real ∈ [½, 1) | ρ | |
| B = ⌊N/(K+1)⌋ | integer ≥ 1 | N, K | Ψ(N, N/(K+1)) = Ψ(N, B) |
| V_{N,K}, G_{N,K}, 𝒟_ρ(N,K) | vertex set / graph / random digraph | N, K, ρ | |
| Φ_K | random integer in [1, N−K] | N, K, ρ | a **size** |
| Φ*_K | random vertex set | N, K, ρ | a **set** (distinct symbol) |
| Φ^{(2)}_K | random integer ≥ 0 | N, K, ρ | |
| Ψ(x, y) | ℝ_{≥0} × ℝ_{≥1} → ℤ_{≥0} | — | Ψ(x, y) = 0 for x < 1 |
| P⁺(n) | ℕ → ℕ | — | P⁺(1) = 1 |
| ω_z(n) | ℕ → ℤ_{≥0} | z | |
| ρ_Dick | [0, ∞) → (0, 1], continuous | — | never abbreviated ρ |
| R_B(n), V_n | integer; set | N, K | fibres |
| F₁ | set ⊂ V_{N,K} | N, K | F₁ = V₁ |
| δ | real ∈ (0, 1/8] | chosen | |
| M = N^{1−2δ} | real | N, δ | G_{M,K} lives on ℤ ∩ (K, M] |
| Y = M/(2(K+1)) | real | N, K, δ | |
| S_M | set | N, K, δ | |
| ℛ | event | N, K, δ | |
| Σ | random set; ∅ on ℛᶜ | N, K, δ, ρ | |
| D(m), s(m) | set; integer | m, N, K, δ | defined for m > M only |
| A_m | event | m, N, K, δ | |
| η | real ∈ (0,1) | chosen | |
| s₀ | integer ≥ 1 | chosen | |
| z = N^{δ/s₀} | real ≥ 2 | N, δ, s₀ | |
| L = Σ_{p≤z} 1/p | real > 0 | z | |
| 𝒰 | set | N, K, δ, η, s₀ | |
| E₀ = N^{2δ}, E₁ = N^{1−δ}/(K+1) | reals | N, K, δ | |
| ℓ = log log N | real > 1 | N | used in T1.3 |
| c₀, C₁ | absolute constants ≥ 1 | — | not computed |
| τ(n), τ_N | integers | n; N | |
| deg, deg_T | integers | N, T | degrees in the undirected graph |
| ε (§6) | real ∈ (0, ½] | chosen | **clashed** with ϵ in C1.6; renamed κ by Fix F7 |
| u_N, u | reals ≥ 1 | N, K; θ | |

**Flags.**
- ε/ϵ clash (Fix F7).
- "K = N^{θ+o(1)}" in the abstract and Table 1, versus log(K+1)/log N → θ in the theorems (Fix F11).
- No other symbol changes meaning.

## 4. Canonical quantified statements

- **T1.2.** ∀ρ ∈ (0,1): [∀N ≥ 2, ∀K ∈ {0,…,N−1}: Φ_K ≤ Ψ(N,B) surely] ∧ [lim_{N→∞} max_{0≤K<N} (Ψ(N,B) − EΦ_K)/N = 0].
- **T1.3.** ∀ρ ∈ (0,1) ∃N₀(ρ) ∀N ≥ N₀(ρ) ∀K ∈ {0,…,N−1}: 0 ≤ Ψ(N,B) − EΦ_K ≤ 30N/log log N.
  - The constant 30 is absolute.
  - N₀ depends on ρ (through λ and q) and on the absolute constants c₀, C₁.
- **C1.4.** ∀ρ ∈ (0,1) ∀θ ∈ [0,1], for every sequence K(N) ∈ {0,…,N−1} with log(K+1)/log N → θ: EΦ_K/N → ρ_Dick(1/(1−θ)), where ρ_Dick(∞) := 0.
- **C1.5.** ∀ρ ∃N₀(ρ) (the same one) ∀N ≥ N₀ ∀K ∈ {0,…,N−1}:
  - (a) E|Φ_K − Ψ(N,B)| ≤ 30N/log log N;
  - (b) E|F₁ △ Φ*_K| ≤ 2K + 30N/log log N, for every selection rule for Φ*_K;
  - (c) EΦ^{(2)}_K ≤ K + 30N/log log N.
- **C1.6.** ∀ρ ∈ (0,1) ∀θ ∈ [0,1), for every sequence K(N) with log(K+1)/log N → θ, and every sequence of sets T(N) ⊂ [N] with |T| = K that is static or adaptive and is a function of G_N alone: E#Φ(𝒟_ρ(N) − T)/N → ρ_Dick(1/(1−θ)).
  - Also: ∀κ ∈ (0, ½) ∃N₁(κ) ∀N ≥ N₁ ∀K ∈ [1, N^{1/2−κ}], the static top-K set is unique and equals {1,…,K}.
- **R5.1.** ∀ρ ∃N₀′(ρ) ∀N ≥ N₀′ ∀K ∈ {0,…,⌊√N−1⌋}: |1 − EΦ_K/N − log(log N/log B)| ≤ 31/log log N.
- **R5.2.** ∀ρ, for every sequence K(N) with K → ∞ and K ≤ √N/2: liminf_N EΦ^{(2)}_K/K ≥ ½.
- **R5.3.**
  - (i) ∀ρ₀ ∈ (0, ½] ∃N₀(ρ₀) ∀ρ ∈ [ρ₀, 1−ρ₀] ∀N ≥ N₀ ∀K: the bound of T1.3 holds.
  - (ii) For every sequence ρ_N with min(ρ_N, 1−ρ_N) · log log N → ∞: max_K (Ψ(N,B) − EΦ_K)/N → 0.
- **L4.5.** ∀N ≥ 2 ∀K ∀η ∈ (0,1) ∀s₀ ∈ ℕ ∀δ ∈ (0, η/8] with (H1)–(H3): statements (a)–(d). All of them are deterministic and non-asymptotic.
- **P4.6.** Same quantifiers; the two displayed inequalities hold for each fixed N (non-asymptotic).

Every statement could be restated with explicit quantifiers, so none is UNCLEAR.

## 5. Micro-claim inventory (sequent form)

| ID | Context | Goal | Rule | Side conditions |
|---|---|---|---|---|
| MC-1 | L3.1, {d,m} edge, d ≥ K+1 | m/d ≤ B | m/d integer ≤ N/(K+1) | ✓ |
| MC-2 | MC-1 | R_B(d) = R_B(m) | m/d is B-smooth ⇒ v_p equal for p > B | ✓ |
| MC-3 | MC-2 | R_B is constant on components | induction on path length | ✓ |
| MC-4 | v ∈ V_n | v ↦ v/n injects into B-smooth s ≤ N/n | unique factorisation | ✓ |
| MC-5 | n > 1 | \|V_n\| ≤ K | n ≥ B+1 > N/(K+1) | ✓ |
| MC-6 | P3.2 | SCC ⊂ component ⊂ fibre | strong ⇒ weak connectivity | ✓ |
| MC-7 | L4.1, fixed (x,x′) | \|𝒴\| ≥ N^{2δ} − 2 | ⌊t⌋ ≥ t − 1, x′ ≤ M | ✓ |
| MC-8 | MC-7 | P(E_y) = q and the E_y are independent | disjoint edge pairs; independent orientations | ✓ |
| MC-9 | MC-8 | P(no E_y) ≤ (1−q)^{N^{2δ}−2} | (1−q)^t decreasing in t | ✓ |
| MC-10 | MC-9 | P(ℛᶜ) ≤ M²(1−q)^{N^{2δ}−2} | union bound over < M² events | ✓ |
| MC-11 | MC-10 | ≤ N² exp(−q(N^{2δ}−2)) | M ≤ N; 1−q ≤ e^{−q} needs t ≥ 0 (**R1-05**) | t < 0 case trivial |
| MC-12 | ℛ | component of G_{M,K} ⊂ one SCC | equivalence relation | ✓ |
| MC-13 | L4.2 | 2^b ∈ S_M | M/2 ≥ 2(K+1) > K, Y ≥ 2 | ✓ |
| MC-14 | x ∈ S_M | the doubling chain lies in S_M | P⁺(2^i x) ≤ max(2, P⁺(x)) ≤ Y | ✓ |
| MC-15 | y ∈ (M/2, M], p ≤ Y | y/p > K+1 | division | ✓ |
| MC-16 | MC-15 | Ω′ drops by 1 | p odd | induction measure ✓ |
| MC-17 | C4.3 | Σ ⊂ F₁ | S_M ⊂ V₁; SCC in one fibre | ✓ |
| MC-18 | L4.4 | P(A_m) = 1 − ρ^s − (1−ρ)^s | De Morgan; disjoint union | s ≥ 1 ✓ |
| MC-19 | A_m ∩ ℛ | m ∈ Σ | closed walk | ✓ |
| MC-20 | L4.5 | K+1 ≤ 2N^{1−η} | (H1); N^{1−η} ≥ 1 | ✓ |
| MC-21 | L4.5(a) | M ≥ 32(K+1) | (H2), η − 2δ ≥ ¾η | ✓ |
| MC-22 | L4.5(b) | 𝒰 ⊂ F₁ ∩ (M, N] | N^{1−δ} > M; Y < N/(K+1) | ✓ |
| MC-23 | Step 1 | e ∈ [E₀, E₁] ⇒ m/e ∈ D(m) | m ≤ N, m > N^{1−δ} | ✓ |
| MC-24 | Step 2 | r ≤ N^δ, m′ > N^{1−2δ} | p_i ≤ z | ✓ |
| MC-25 | Step 3(i) | q ≤ Y ≤ E₁/z | δ/s₀ ≤ δ | ✓ |
| MC-26 | Step 3(ii) | e₀ = π_j ∈ [E₀, N^{4δ}) ⊂ [E₀, E₁/z] | minimality of j; (H2) | ✓ |
| MC-27 | Step 4 | s₀+1 distinct divisors in [E₀, E₁] | e₀r ∣ m; p_i ≤ z | ✓ |
| MC-28 | (d) | three-set union bound | definition of 𝒰 | ✓ |
| MC-29 | (d) | Σ_{Y<p≤B} 1/p ≤ 4δ/η + 2(1+C₁)/(η log N) | L2.1(b); log(1+t) ≤ t; (H2) | ✓ |
| MC-30 | P4.6 | Φ_K ≥ X surely | MC-19, MC-22 | ✓ |
| MC-31 | P4.6 | EX ≥ Σ(P(A_m) − P(ℛᶜ)) | P(A∩ℛ) ≥ P(A) − P(ℛᶜ); linearity | ✓ |
| MC-32 | P4.6 | \|𝒰\|(1−c) ≥ \|𝒰\| − cN | \|𝒰\| ≤ N, c ≥ 0 | ✓ even if 1−c < 0 |
| MC-33 | P4.6(2) | F₁∖Σ ⊂ (F₁∖𝒰) ∪ {A_mᶜ} on ℛ | MC-19 | ✓ |
| MC-34 | T1.3 | λ^{s₀} ≤ 1/ℓ | definition of s₀ | ✓ |
| MC-35 | T1.3 | (R1)–(R6) hold for N ≥ N₀(ρ) | s₀ = O_ρ(log ℓ); N^{2δ} = e^{log N/(4ℓ²)} | ✓ |
| MC-36 | T1.3 | the sum is ≤ 29N/ℓ + 1 ≤ 30N/ℓ | arithmetic; N/ℓ ≥ 1 | ✓ |
| MC-37 | T1.3, K > N^{1−η} | Ψ(N,B) ≤ 3N/ℓ | L2.3; (R6) | ✓ |
| MC-38 | L2.7 | Ψ(N, N^{1/u_N})/N → ρ_Dick(u) | uniform Dickman on [1, u+1]; continuity | ✓ |
| MC-39 | C1.5 | three-case bound on ℛ | fibres; \|Φ*\| ≥ \|Σ\| | ✓ |
| MC-40 | R5.1 | N − Ψ(N,B) = Σ_{B<p≤N} ⌊N/p⌋ | p > √N | ✓ |
| MC-41 | R5.2 | V_p = {ps : s ≤ N′} | s < √N < B < p | N ≥ 25 ✓ |
| MC-42 | R5.2 | P(Φ_K ≤ K) → 0 | Markov; Ψ(N,B) ≥ N/4 | ✓ |
| MC-43 | L6.2 static | inclusions | degree formula; 1/(1−ε) − 1/(1−ε/2) ≥ ε/2 | ✓ |
| MC-44 | L6.2 adaptive | induction on j | N ≥ 20K from the hypothesis | ✓ |
| MC-45 | C1.6 | Φ_{K₊} ≤ #Φ(𝒟−T) ≤ Φ_{K₋} | L6.1; coupling on one sample | T independent of the orientation ✓ |
| MC-46 | A.1 | first partial sum ≥ θ is < 2θ ≤ 1−θ | θ ≤ 1/3 | ✓ |

## 6. Limit-order map

| Statement | Limit | Uniformity / dependence |
|---|---|---|
| L2.1 O(·) terms | x → ∞ | absolute constants c₀, C₁ |
| L2.2 | x → ∞ | uniform in u ∈ [1, U]; rate depends on U |
| L2.3 | none (explicit for all x ≥ 2, 2 ≤ y ≤ x) | absolute c₀ |
| L2.4 | none (explicit) | absolute |
| L2.6 | none | C_ε depends on ε only |
| T1.2 | N → ∞ | uniform in K; depends on ρ |
| T1.3 | N ≥ N₀(ρ) | uniform in K; constant 30 absolute; N₀ depends on ρ, c₀, C₁. Non-trivial only when log log N > 30 (**R1-13**). |
| eq. (1), R5.1 | N ≥ N₀′(ρ) | uniform in 0 ≤ K ≤ √N − 1; O_ρ |
| C1.4 | N → ∞ along the sequence K(N) | pointwise in the sequence; depends on ρ, θ |
| C1.5 | N ≥ N₀(ρ) | uniform in K and in the selection rule for Φ* |
| C1.5 prose "w.h.p. up to o(N)" | N → ∞ along K(N) = o(N) | means ∀ε > 0: P(\|F₁ △ Φ*\| > εN) → 0 (**R1-12**) |
| R3.4 | N → ∞ along K(N) = o(N) | same reading as above |
| R5.2 "(½ − o(1))K" | N → ∞ along K(N) → ∞, K ≤ √N/2 | depends on ρ and on the sequence (**R1-09**) |
| R5.3(i) | N ≥ N₀(ρ₀) | uniform in ρ ∈ [ρ₀, 1−ρ₀] (needs **R1-04**) |
| R5.3(ii) | N → ∞ | depends on the sequence ρ_N |
| C1.6 | N → ∞ along K(N) | τ_N = O_θ(N^{(1−θ)/2}) |
| R7.1 O(N) | none | absolute, uniform in 1 ≤ K ≤ N |
| "∼ N/(c log N)" in §1.4, (O1) | N → ∞ | needs PNT (**R1-03**) |
