# Kim–Phillips Question 20: status report

Paper draft: [`paper/hub_removal.tex`](paper/hub_removal.tex) (compiled: [`paper/hub_removal.pdf`](paper/hub_removal.pdf), 16 pages).
Numbering below refers to the compiled PDF.

## Headline result (PROVEN, new)

Fix a flip probability ρ ∈ (0,1). Let Φ_K be the size of the largest SCC of 𝒟_ρ(N) after the vertices 1,…,K are deleted, and let B = ⌊N/(K+1)⌋.

1. **Deterministic upper bound.** Φ_K ≤ Ψ(N, B) for every orientation.
2. **Theorem 1.3 (rate).** For N ≥ N₀(ρ) and **every** 0 ≤ K < N,

   0 ≤ Ψ(N, N/(K+1)) − E[Φ_K] ≤ 30 N / log log N.

3. **Corollary 1.4 (limit profile).** If log(K+1)/log N → θ ∈ [0,1], then

   E[Φ_K]/N → ρ_Dick(1/(1−θ)), with ρ_Dick(∞) = 0.

   So **the conjecture of the brief holds for every θ ∈ [0,1)**, not only θ ≤ 1/3.
4. **Structure (Cor. 1.5).** W.h.p. the giant SCC equals the smooth fibre F₁ up to o(N) + O(K) vertices, and E[second-largest SCC] ≤ K + o(N).
5. **Degree attacks (Cor. 1.6).** For θ < 1, the same limit holds for static and adaptive highest-degree attacks.
6. **Explicit loss (Remark 5.1).** For K ≤ √N − 1,

   1 − E[Φ_K]/N = log(log N / log B) + O(1/log log N).

   This is an additive approximation. The main term dominates the error only when log K ≫ log N / log log N, so for bounded K the loss is not determined to within a factor 1 + o(1).

### The key new idea (Lemmas 4.1 and 4.2)

The argument needs no hub clique and no Poisson–Dirichlet input.

- **Robust edges (Lemma 4.1).** Put M = N^{1−2δ}. Every divisibility edge x | x′ with K < x < x′ ≤ M is shadowed by at least N^{2δ} − 2 independent directed 2-paths x → y → x′ through multiples y of x′. A union bound over all such pairs shows that w.h.p. every connected component of the **deterministic** graph G_{M,K} lies inside one SCC.
- **Doubling (Lemma 4.2).** All x ∈ (K, M] with P⁺(x) ≤ M/(2(K+1)) lie in one component of G_{M,K}. To see this, multiply by 2 up to (M/2, M], divide by an odd prime, and repeat.
- **Attachment.** Almost every m ∈ F₁ ∩ (M, N] has at least s₀ divisors in that set (Lemma 4.5, elementary). So m joins the giant with probability ≥ 1 − ρ^{s₀} − (1−ρ)^{s₀}.

## Report by target

| Target | Outcome | Where |
|---|---|---|
| **T1** F1–F4, F7 rigorous; Turán–Kubilius and Dickman stated precisely | **Done.** F1–F2: Lemma 3.1, Prop. 3.2 (we prove the sharper Φ_K ≤ Ψ(N,B)). F3: Cor. 3.3. F4: Remark 3.4. F5: Cor. 1.6 and Lemma 6.2. F6: Remark 7.1. F7 is the case θ = 0 of Cor. 1.4. Turán–Kubilius: Remark 2.5, with the special case proved (Lemma 2.4). Dickman: Lemma 2.2. | §§2–3, 5, 6 |
| **T2** sharp for 0 ≤ θ ≤ 1/3 | **Done**, as a special case of Cor. 1.4. The intended route (hub window + PD) was **not needed**; the replacement is fully elementary (Lemma 4.5). Steps 1–2 of the intended route are correct. We did not prove the step-3 density claim for the hub window; our proof bypasses it. The Sub-sum Lemma is proven (Appendix A, sharp). | §4, App. A |
| **T3** 1/3 < θ < 1/2 | **Sharp constant proven** (Cor. 1.4). So c_H(θ) is moot as a lower bound and was not computed. Remark 7.2 explains why the one-step hub clique loses for θ > 1/3; it is a SKETCH, not used. | §4, Rem. 7.2 |
| **T4** θ ≥ 1/2 | **Resolved** (Cor. 1.4): the profile is ρ_Dick(1/(1−θ)) on all of [1/2, 1), and 0 at θ = 1. The "copies" idea was not needed. | §4 |
| **T5** rates | **Done.** Uniform error O(N/log log N) (Thm. 1.3) and explicit form for K ≤ √N − 1 (Rem. 5.1). The suggested shape O((log K/log N)^c) cannot hold for bounded K, because the error term includes an additive O(1/log log N). The natural statement is Rem. 5.1. The true order of the error is OPEN; a lower bound ≫ N/log N holds for K ∈ {0,1}. | §5, (O1) |

## Status table

| Claim | Status | Notes / gaps |
|---|---|---|
| Lemma 2.1 (Mertens, Chebyshev) | PROVEN (cited) | classical |
| Lemma 2.2 (Dickman, uniform on [1,U]) | PROVEN (cited) | Dickman 1930, de Bruijn 1951, Hildebrand 1986; used only to identify the limit |
| Lemma 2.3 (Ψ(x,y) ≤ √x + 2x(log y + c₀)/log x; ρ_Dick(u) ≤ 2/u) | PROVEN | standard |
| Lemma 2.4 (variance of ω_z) | PROVEN | special case of Turán–Kubilius |
| Lemma 2.6 (τ(n) ≪_ε n^ε) | PROVEN | standard |
| Lemma 2.7 (limit of Ψ(N, N/(K+1))/N) | PROVEN | standard; added by the proof-checker audit (F6) |
| Lemma 3.1 (fibres of the B-rough part) | PROVEN | essentially known (cf. McNew 2021) |
| Prop. 3.2 (Φ_K ≤ Ψ(N,B); Φ_K ≤ max(\|F₁\|, K)) | PROVEN | deterministic |
| Cor. 3.3 (limsup bound) | PROVEN | |
| Remark 3.4 (F4 equivalences) | PROVEN | Markov |
| Lemma 4.1 (robust edges) | PROVEN | new; union bound, independence only within a fixed pair |
| Lemma 4.2 (doubling connectivity) | PROVEN | new in this form; deterministic |
| Cor. 4.3 | PROVEN | |
| Lemma 4.4 (attachment) | PROVEN | uses only P(A ∩ R) ≥ P(A) − P(Rᶜ) |
| Lemma 4.5 (arithmetic core) | PROVEN | new; deterministic, explicit exceptional set |
| Prop. 4.6 (explicit non-asymptotic lower bound) | PROVEN | |
| Theorem 1.3 (rate 30N/log log N, uniform in K) | PROVEN | new |
| Theorem 1.2 (uniform asymptotic) | PROVEN | new; answers KP Question 20 |
| Remark 5.1 (explicit loss for K ≤ √N − 1) | PROVEN | new |
| Cor. 1.4 (profile ρ_Dick(1/(1−θ)), θ ∈ [0,1]) | PROVEN | new; all θ, including θ ≥ 1/2 |
| Cor. 1.5 (giant ≈ F₁; second SCC ≤ K + o(N)) | PROVEN | new |
| Remark 5.2 (term K is necessary) | PROVEN | uses KP Cor. 2 and Bertrand |
| Remark 5.3 (uniform in ρ ∈ [ρ₀, 1−ρ₀]; ρ_N ≫ 1/log log N) | PROVEN | s₀ chosen from λ₀ = 1 − ρ₀ (audit fix F4) |
| Lemma 6.1, Lemma 6.2 (monotonicity, sandwich) | PROVEN | |
| Cor. 1.6 (static/adaptive degree attacks) | PROVEN | degrees taken in the undirected G_N |
| Remark 7.1 (edge share θ) | PROVEN | |
| Remark 7.2 (a hub clique loses for θ > 1/3) | SKETCH | gap: the ≫ N count of m = p₁p₂p₃s is not written out; not used anywhere |
| Lemma A.1 (Sub-sum Lemma, sharp at 1/3) | PROVEN | not needed for the main results |
| (O1) true error order; (O2) fluctuations; (O3) in/out-degree attacks; (O4) ρ_N → 0 fast; (O5) diameter | OPEN | |

## Referee notes and caveats

- **Independence** is used only in two places: among the 2-paths for one fixed pair (x, x′) (Lemma 4.1), and among the edges at one vertex m (Lemma 4.4). The dependence between the event R and the attachment events A_m is handled by P(A_m ∩ R) ≥ P(A_m) − P(Rᶜ).
- **No limit interchanges.** Prop. 4.6 is non-asymptotic, and all parameters depend only on N. So the bounds are uniform in K by construction.
- **Citation hygiene.** Theorem numbers are given only for Hardy–Wright (Thm. 7, Chebyshev; Thm. 315, divisor bound). They should be checked against the edition used. The other classical inputs are cited by author and work, without theorem numbers.
- **Sanity check (not a result).** At N = 10⁵, one random sample was run for each of K ∈ {1, 10, 46, 316, 1000, 2154}. In every sample the set S_M from Lemma 4.2 was connected in G_{M,K} and lay inside the giant SCC, and the observed Φ/N matched the background table of the brief.

## Proof-checker audit (2026-09-28, run 01)

The `proof-checker` workflow was run on the paper. Outputs are in `paper/`:
- `PROOF_SKELETON.md`: obligation ledger, dependency DAG, symbol table, micro-claims;
- `PROOF_AUDIT.md`: round log;
- `PROOF_AUDIT.json`, `PROOF_CHECK_STATE.json`: machine-readable verdict and state;
- `proof_audit_report.pdf`: before/after report;
- `.aris/traces/proof-checker/2026-09-28_run01/`: scripts and outputs.

- **Verdict: ERROR (`reviewer_error`).** The skill's cross-model reviewer (Codex MCP) was not available in this session, so both review rounds were self-reviews.
- **Self-review result.** 0 FATAL, 0 CRITICAL, 4 MAJOR and 10 MINOR issues, all fixed. The self-review acceptance gate passes.
- **The four MAJOR issues** were all overstatements or missing citations in prose and remarks:
  - a ratio asymptotic stated where only an additive bound is proved;
  - the abstract's degree-attack claim at θ = 1;
  - the prime number theorem was uncited;
  - uniformity in ρ was not derived.
- **No proof of a theorem or corollary changed.** No counterexample was found. Two bounds (Lemma 3.1(c), Lemma 4.5(c)) were shown numerically to be attained.
- Re-run the skill with a Codex reviewer connected to obtain a cross-model verdict.
