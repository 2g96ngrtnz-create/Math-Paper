# PROOF_AUDIT — `hub_removal.tex`

This is the cumulative log of the `proof-checker` run of 2026-09-28 (run 01).

- **Input:** `paper/hub_removal.tex` at commit `055505f` (sha256 `4d562ccc4cb4f3c3ec830aecaae155ca88f1cbce73577c0b8702e1a930ae0090`). Line numbers in Round 1 refer to this version.
- **Ledger:** `PROOF_SKELETON.md`.
- **Traces and scripts:** `.aris/traces/proof-checker/2026-09-28_run01/`.

## Reviewer backend: unavailable

The skill prescribes an adversarial review by an external model through the Codex MCP server (tools `mcp__codex__codex` and `mcp__codex__codex-reply`). **That server is not connected in this session**; a tool search for "codex" returned nothing. The following substitutions were made:

- **Phases 1 and 3** (review and re-review) were carried out as a self-review by the executing agent. It used the mandatory checklist A–H verbatim and the two-axis severity system.
- **Phase 3.5, the independent blind second review,** is required only for fixes of FATAL or CRITICAL issues. This run has none, so the requirement is vacuous. Even so, no independent reviewer was consulted.
- **The cross-model protocol ("Claude analyzes, Codex reviews") was not met.** Following the skill's verdict table, `PROOF_AUDIT.json` therefore records the verdict **`ERROR` / `reason_code: reviewer_error`**. It separately records the self-review outcome as `self_review_verdict`. This run does not claim a cross-model PASS.
- The `/render-html` step is non-blocking and was skipped: that skill is not available here. `PROOF_AUDIT.md` and `PROOF_AUDIT.json` are the canonical outputs.

---

## Round 1: review (checklist A–H)

**A. Definitions.**
- Symbol clash: ϵ (Cor 1.6, last claim) versus ε (Lemma 6.2 and its proof). See R1-07.
- "K = N^{θ+o(1)}" in the abstract and Table 1 is not defined for K = 0, while the theorems use log(K+1)/log N → θ. See R1-11.
- No other drift (see the symbol table in `PROOF_SKELETON.md` §3).

**B. Hypothesis discharge.** All applications are ledgered in `PROOF_SKELETON.md` §2 and every entry is discharged. One exception: the uniform-in-ρ claim of Remark 5.3 does not say how N₀ is chosen uniformly (R1-04).

**C. Inequality audit.**
- All inequality chains were re-derived; their directions are correct.
- In Lemma 4.1, (1−q)^t ≤ e^{−qt} is used without the condition t ≥ 0 (R1-05).
- In Proposition 4.6, |𝒰|(1−c) ≥ |𝒰| − cN is valid even when 1−c < 0 (MC-32).

**D. Interchange audit.** The paper contains no interchange of limit, expectation, derivative or integral beyond the following:
- linearity of expectation over finite sums;
- passing to the limit in an inequality (the consequence in Lemma 2.3);
- the squeeze in Corollary 1.6.

Corollary 1.4 applies Dickman with u_N varying; the uniform version on [1, U] (Lemma 2.2) covers this. No DCT, MCT or Fubini is invoked.

**E. Probability mode.**
- Expectation bounds are upgraded to convergence in probability only via Markov's inequality applied to non-negative variables (Cor 1.5(a), Rem 3.4, Rem 5.2), which is correct.
- The prose "w.h.p. up to o(N)" after Corollary 1.5 is not quantified (R1-12).

**F. Uniformity and constants.**
- Theorem 1.3: uniform in K. The constant 30 is absolute; N₀ depends on ρ, c₀ and C₁. The bound is non-trivial only when log log N > 30 (R1-13).
- Remark 5.2: the o(1) is not declared (R1-09).
- Remark 5.3: uniformity in ρ is not justified (R1-04).
- Everything else is declared (`PROOF_SKELETON.md` §6).

**G. Edge and degenerate cases.** Checked: K = 0; K ≥ N/2; K = N−1; B = 1; empty sets; s(m) = 0; ⌊(1−ε)K⌋ = 0; the boundaries M = 4(K+1), δ = η/8 and K = ⌊N^{1−η}⌋; θ ∈ {1/3, 1/2, 1}. The only problem found is θ = 1, which is claimed for degree attacks in the abstract but not proved (R1-02).

**H. Dependency consistency.** The DAG is acyclic. One forward reference exists (Cor 3.3 cites a step inside the proof of Cor 1.4); it is not circular (R1-06).

### Issue list

Severity follows the skill's two-axis system. Every issue is Group D (scope), a notation issue or a gap in a side remark. **None affects Theorems 1.2 or 1.3 or Corollaries 1.4–1.6 as stated.**

| ID | Severity | Status / Impact | Category | Location (v055505f) |
|---|---|---|---|---|
| R1-01 | MAJOR | UNJUSTIFIED / LOCAL | SCOPE_OVERCLAIM | l.106 (sentence after eq. (1)) |
| R1-02 | MAJOR | UNJUSTIFIED / LOCAL | SCOPE_OVERCLAIM | l.40–41 (abstract) |
| R1-03 | MAJOR | UNJUSTIFIED / LOCAL | REFERENCE_MISMATCH | l.156 (§1.4), l.636 ((O1)) |
| R1-04 | MAJOR | UNJUSTIFIED / LOCAL | QUANTIFIER_ERROR | l.556 (Remark 5.3) |
| R1-05 | MINOR | UNCLEAR / COSMETIC | CASE_INCOMPLETE | l.332 (Lemma 4.1) |
| R1-06 | MINOR | UNCLEAR / COSMETIC | CIRCULAR_DEPENDENCY (forward reference; verified acyclic) | l.297 (Cor 3.3) |
| R1-07 | MINOR | UNCLEAR / COSMETIC | NORMALIZATION_MISMATCH (symbol reuse) | l.133, l.612 |
| R1-08 | MINOR | OVERSTATED / COSMETIC | SCOPE_OVERCLAIM | l.156 |
| R1-09 | MINOR | UNCLEAR / COSMETIC | CONSTANT_DEPENDENCE_HIDDEN | l.541 (Remark 5.2) |
| R1-10 | MINOR | UNCLEAR / COSMETIC | UNJUSTIFIED_ASSERTION (inside a SKETCH remark) | l.627 (Remark 7.2) |
| R1-11 | MINOR | UNCLEAR / COSMETIC | NORMALIZATION_MISMATCH | l.40, l.151 |
| R1-12 | MINOR | UNCLEAR / COSMETIC | STOCHASTIC_MODE_CONFUSION | l.125 |
| R1-13 | MINOR | UNCLEAR / COSMETIC | CONSTANT_DEPENDENCE_HIDDEN | l.95–100 (Theorem 1.3) |

**R1-01. The sentence after eq. (1) overstates the explicit form.**
- *Claim:* "the expected fraction lost … is asymptotically log(log N/log(N/K)), which is about log K/log N when K = N^{o(1)}".
- *Why:* Remark 5.1 proves only an additive error of 31/log log N. The ratio asymptotic is unproven whenever log(log N/log(N/K)) = O(1/log log N), that is, whenever log K ≲ log N/log log N. This includes every fixed K.
- *Counterexample:* CANDIDATE only. At K = 1 the main term is about 0.693/log N and the proven lower bound on the loss is about 0.667/log N. This does not disprove the claim, but nothing proves it.
- *Affects:* nothing downstream; the sentence is prose.
- *Minimal fix:* restate it as an additive approximation.

**R1-02. The abstract extends the degree-attack claim to θ = 1.**
- *Claim:* the abstract states the profile for 0 ≤ θ ≤ 1 and then "The same limit holds if the K vertices of largest degree are deleted".
- *Why:* Corollary 1.6 requires θ < 1. Its sandwich lemma needs N/K ≫ τ_N, which fails for K = N^{1−o(1)}.
- *Counterexample:* NO. For θ = 1 the limit is plausibly 0 for static attacks, but it is not proved.
- *Affects:* the abstract only.
- *Minimal fix:* restrict the sentence to θ < 1.

**R1-03. Two prime-counting asymptotics need the prime number theorem.**
- *Claim:* π(N/2) − π(N/3) ∼ N/(6 log N) (§1.4, (O1)) and π(N) − π(N/2) ∼ N/(2 log N) ((O1)).
- *Why:* these are consequences of the prime number theorem. Lemma 2.1 cites only Chebyshev's *upper* bound.
- *Counterexample:* NO. The claims are true, but not supported by the cited inputs.
- *Affects:* the discussion and (O1) only. The exact inequalities in those places, such as "≥ π(N/2) − π(N/3)", are correct as stated.
- *Minimal fix:* cite the prime number theorem (Hadamard; de la Vallée Poussin, 1896).

**R1-04. Uniformity in ρ is asserted without saying how N₀ is chosen.**
- *Claim:* "Theorems 1.2 and 1.3 hold uniformly for ρ ∈ [ρ₀, 1−ρ₀], with N₀ = N₀(ρ₀)".
- *Why:* in the proof of Theorem 1.3, s₀ is defined from λ(ρ). The claim needs an explicit choice that works for all ρ in the interval.
- *Counterexample:* NO. The claim is true, as the fix shows.
- *Affects:* Remark 5.3(i) only.
- *Minimal fix:* define s₀ from λ₀ := 1−ρ₀ ≥ λ(ρ) and use q ≥ q₀ := ρ₀(1−ρ₀). Conditions (R1)–(R6) then depend only on ρ₀.

**R1-05. Lemma 4.1 uses an inequality outside its range.**
- *Claim:* M²(1−q)^t ≤ N² e^{−qt} for t = N^{2δ} − 2, via 1−q ≤ e^{−q}.
- *Why:* (1−q)^t ≤ e^{−qt} holds only for t ≥ 0.
- *Counterexample:* for t < 0 that step reverses. The *stated* bound on P(ℛᶜ) nevertheless still holds, because the right-hand side exceeds 1.
- *Minimal fix:* add one clause covering t < 0.

**R1-06. Forward reference in Corollary 3.3.**
- *Claim:* Corollary 3.3 cites "the computation … in the proof of Corollary 1.4". That proof opens by invoking Theorem 1.2.
- *Why:* the DAG check shows the reference is not circular, but the dependency is obscured.
- *Minimal fix:* extract the computation as a standalone Lemma 2.7 (`lem:psi-limit`), and cite it in both places.

**R1-07. The symbol ϵ is reused.**
- *Where:* ϵ in "K ≤ N^{1/2−ϵ}" (Cor 1.6 and its proof) sits beside ε = ¼ in the same proof and ε in Lemma 6.2.
- *Minimal fix:* rename the first one κ.

**R1-08. "Far more damaging" is overstated for small θ.**
- *Claim:* "hub removal is far more damaging than the loss of edges alone suggests".
- *Why:* at θ = 0.1 the giant keeps 0.895 of the vertices while 0.90 of the edges survive. The claim is only true for moderate θ.
- *Minimal fix:* qualify the sentence with the θ = 1/2 example.

**R1-09. The o(1) in Remark 5.2 has undeclared dependence.**
- *Claim:* "E Φ^{(2)}_K ≥ (½ − o(1))K".
- *Why:* the o(1) depends on ρ and on the sequence K(N), and this is not stated. The remark also relies on the external [KP, Cor. 2], although Theorem 1.2 with K = 0 would do.
- *Minimal fix:* declare the limit and the dependence, and mention the internal alternative.

**R1-10. Remark 7.2 describes attachment through one divisor.**
- *Claim:* "attaches through its divisor d = m/p₁".
- *Why:* attachment needs several divisors, with one edge pointing each way. This is inside a SKETCH remark.
- *Minimal fix:* change the wording.

**R1-11. "K = N^{θ+o(1)}" without its meaning.**
- *Where:* the abstract and Table 1.
- *Why:* for K = 0 the expression is meaningless; the theorems use log(K+1)/log N → θ.
- *Minimal fix:* add "(that is, log(K+1)/log N → θ)".

**R1-12. Unquantified "w.h.p. up to o(N)".**
- *Where:* the prose after Corollary 1.5.
- *Minimal fix:* spell it out as "for every fixed ε > 0, with probability 1 − o(1), at most εN vertices".

**R1-13. Theorem 1.3 is vacuous at any computable size.**
- *Why:* 30/log log N < 1 only when N > e^{e^{30}}. Nothing false is claimed, but a reader could mistake the rate for a numerically meaningful bound.
- *Minimal fix:* add one sentence after Theorem 1.3.

---

## Phase 1.5: counterexample red team

Scripts and raw outputs are in `.aris/traces/proof-checker/2026-09-28_run01/`:
- `audit_checks.py`, `audit_degree.py`: from the earlier audit, re-run in this session.
- `redteam.py`, `redteam_rt4.py`: new.

A counterexample is labelled "found" only if verified exactly. **None was found.**

| Target | Strategy | Result |
|---|---|---|
| Lemma 2.3 | numeric falsification: smallest c₀ needed on a grid with x ≤ 2·10⁵ | c₀ ≥ −0.71 suffices, while the Mertens constant in Lemma 2.1(a) is ≥ 0.144, so no counterexample |
| Lemma 2.4 | extreme parameters z = 2 and z = N, with N ≤ 2·10⁴ | holds, with a factor of 6–10 to spare |
| Lemma 3.1(c) | tightness | the bound \|V_n\| ≤ K is **attained** (e.g. N = 10⁴, K ∈ {3, 10, 31}), so it is sharp; no counterexample |
| Lemma 3.1 and Prop 3.2 | exhaustive, N ≤ 3000, K ∈ {0, 1, 2, 3, N/10, √N, N/3, N/2 − 1, N/2, N − 2, N − 1} | 0 failures |
| Lemma 4.2 | exhaustive on 1,643 cases; boundary M = 4(K+1) exactly, with δ up to 1/8 (20 cases) | 0 failures. At the boundary, S_M is the two powers of 2, which is trivially connected. |
| Lemma 4.5(c) | exhaustive over 𝒰 (67,921 integers); extreme K = ⌊N^{1−η}⌋ and δ = η/8 | 0 failures; min s(m) = s₀ + 1 is **attained**, so the bound is sharp |
| Lemma 4.5(d) | union-bound containment, checked exactly | holds |
| Lemma 6.2 | static and adaptive, N = 10⁵, all 1 ≤ K ≤ 187 (the maximum the hypothesis allows), two tie-break rules | 0 failures. Beyond the hypothesis, the static upper inclusion first fails at K = 833 (not a counterexample, since the hypothesis is violated there). |
| Remark 5.1 identity | exhaustive, N ≤ 2·10⁴, K + 1 ≤ √N | 0 failures |
| Lemma A.1 | 20,000 random cases; exact rational search at θ = 1/3 over all partitions of 1 into ≤ 5 parts from the grid 1/24, …, 23/24 (280 cases) | 0 counterexamples; the sharpness example (⅓, ⅓, ⅓) is confirmed |
| Theorem 1.3 | adversarial scaling of constants | not falsifiable numerically, because it is vacuous below N ≈ 10^{4.6·10¹²}. This is logged as R1-13, not as a counterexample. |
| Table 1 (ρ_Dick values) | independent recomputation | all 12 entries reproduce (e.g. ρ(10) = 2.7701718·10⁻¹¹, ρ(20) = 2.4617829·10⁻²⁹) |
| Lemma 4.1 plus Cor 4.3 | Monte Carlo at N = 10⁵, one sample for each of 6 values of K | S_M lies inside the giant SCC in every sample (a sanity check only) |

---

## Phase 2: fixes

The fixes were applied to `hub_removal.tex` in order of severity: all MAJOR issues first, then all MINOR ones. LaTeX compiles cleanly (17 pages, no errors, warnings, undefined references or overfull boxes). Every existing `\label` keeps its number; the new label `lem:psi-limit` becomes Lemma 2.7.

**No theorem's hypotheses were strengthened.**

### Fix F1: explicit form stated as an additive approximation
- **Issue:** R1-01, SCOPE_OVERCLAIM. **Severity:** MAJOR (UNJUSTIFIED / LOCAL). **Strategy:** WEAKEN_CLAIM. **Location:** §1.3, sentence after eq. (1).
- **Before:** "the fraction lost is asymptotically log(log N/log(N/K)), about log K/log N for K = N^{o(1)}".
- **After:** "up to an additive O_ρ(1/log log N), uniform in 0 ≤ K ≤ √N − 1, the fraction lost equals log(log N/log B). This main term dominates only when log K ≫ log N/log log N; for bounded K we do not determine the loss to within a factor 1+o(1)."
- **Key equation:** unchanged. It is Remark 5.1, \|1 − EΦ_K/N − log(log N/log B)\| ≤ 31/log log N.
- **Downstream:** none.

### Fix F2: degree-attack claim restricted to θ < 1 in the abstract
- **Issue:** R1-02. **Severity:** MAJOR (UNJUSTIFIED / LOCAL). **Strategy:** WEAKEN_CLAIM. **Location:** abstract.
- **After:** "For 0 ≤ θ < 1 the same limit holds if the K vertices of largest degree are deleted instead".
- This now matches the hypotheses of Corollary 1.6. **Downstream:** none.

### Fix F3: prime number theorem cited
- **Issue:** R1-03. **Severity:** MAJOR (UNJUSTIFIED / LOCAL). **Strategy:** ADD_REFERENCE. **Locations:** §1.4 and (O1).
- **After:** the two "∼ N/(c log N)" statements are now attributed to the prime number theorem [Hadamard 1896; de la Vallée Poussin 1896], and both are added to the bibliography.
- The inequalities "≥ π(N/2) − π(N/3)" and "≥ π(N) − π(N/2)" are exact and need no citation.
- **Hypothesis check:** the prime number theorem has none beyond x → ∞.

### Fix F4: uniformity in ρ derived
- **Issue:** R1-04. **Severity:** MAJOR (UNJUSTIFIED / LOCAL). **Strategy:** ADD_DERIVATION. **Location:** Remark 5.3.
- **Derivation:** let ρ ∈ [ρ₀, 1−ρ₀]. Then λ ≤ λ₀ := 1−ρ₀ and q ≥ q₀ := ρ₀(1−ρ₀).
  1. Define s₀ from λ₀. Then λ^{s₀} ≤ λ₀^{s₀} ≤ 1/ℓ.
  2. Conditions (R1)–(R4) and (R6) depend only on N and on s₀(λ₀).
  3. The left side of (R5), N³exp(−q(N^{2δ}−2)), decreases in q once N^{2δ} ≥ 2, so (R5) for q₀ implies it for every q ≥ q₀.
  4. All other ρ-dependence goes through P(A_m) ≥ 1 − 2λ^{s(m)} ≥ 1 − 2λ₀^{s₀+1}.
  So a single N₀(ρ₀) works for every ρ in the interval.
- **Downstream:** none.

### Fix F5: case t < 0 in Lemma 4.1
- **Issue:** R1-05. **Severity:** MINOR. **Strategy:** ADD_DERIVATION.
- **After:** "(1−q)^t ≤ e^{−qt} for t = N^{2δ} − 2 ≥ 0. If N^{2δ} < 2 the right-hand side exceeds 1 and there is nothing to prove."

### Fix F6: forward reference replaced by Lemma 2.7
- **Issue:** R1-06. **Severity:** MINOR. **Strategy:** ADD_DERIVATION (restructure).
- **After:** new Lemma 2.7 (`lem:psi-limit`): if log(K+1)/log N → θ ∈ [0,1], then Ψ(N, N/(K+1))/N → ρ_Dick(1/(1−θ)).
  - Its proof is the former computation inside the proof of Corollary 1.4. It adds one clause: y > 1 for large N when θ < 1, so u_N is defined.
  - Corollary 3.3 now reads "Prop 3.2 + Lemma 2.7", and the proof of Corollary 1.4 reads "Thm 1.2 + Lemma 2.7".
- **DAG:** L2.2, L2.3 → L2.7 → {C3.3, C1.4}. It remains acyclic.

### Fix F7: symbol ϵ renamed κ
- **Issue:** R1-07. **Severity:** MINOR. **Strategy:** notation.
- **After:** Corollary 1.6 now reads "for fixed κ ∈ (0, ½) and N ≥ N₁(κ), if 1 ≤ K ≤ N^{1/2−κ}". The proof adds the note N/(K(K+1)) ≥ ½N^{2κ}.
- The ranges κ ∈ (0, ½) and K ≥ 1 were implicit before (the claim is empty otherwise), so no real hypothesis was added.

### Fix F8: "far more damaging" qualified
- **Issue:** R1-08. **Severity:** MINOR. **Strategy:** WEAKEN_CLAIM.
- **After:** "for moderate θ … at θ = ½ about half of the edges disappear, but only 30.7% of the vertices remain in the giant."

### Fix F9: o(1) declared in Remark 5.2
- **Issue:** R1-09. **Severity:** MINOR. **Strategy:** notation plus an internal alternative.
- **After:** the statement reads "Fix ρ; K(N) → ∞, K ≤ √N/2 ⇒ liminf EΦ^{(2)}_K/K ≥ ½. All o(1) terms are along the sequence and depend on ρ and on the sequence."
- The proof now notes that Theorem 1.2 with K = 0 (where Ψ(N′,N′) = N′) can replace [KP, Cor. 2].

### Fix F10: wording of the sketch in Remark 7.2
- **Issue:** R1-10. **Severity:** MINOR. **Strategy:** WEAKEN_CLAIM.
- **After:** "Such an m lies in S_M if m ≤ M. Otherwise, if the p_i are distinct, its three divisors m/p_i lie in S_M, so s(m) ≥ 3, and m attaches as in Lemma 4.4; further divisors come from the small prime factors of s."
- The remark stays SKETCH and unused.

### Fix F11: "K = N^{θ+o(1)}" given its meaning
- **Issue:** R1-11. **Severity:** MINOR. **Strategy:** notation.
- **After:** the abstract adds "(that is, log(K+1)/log N → θ)". The Table 1 caption reads "when log(K+1)/log N → θ".

### Fix F12: "w.h.p." quantified
- **Issue:** R1-12. **Severity:** MINOR. **Strategy:** notation.
- **After:** "when K = o(N), the following holds for every fixed ε > 0 with probability 1 − o(1), by Markov's inequality applied to (b) and (c): the largest SCC differs from the smooth set in ≤ εN vertices, and every other SCC has ≤ εN vertices."

### Fix F13: vacuity threshold of Theorem 1.3 stated
- **Issue:** R1-13. **Severity:** MINOR. **Strategy:** notation.
- **After:** "The bound is non-trivial only when log log N > 30. Its content is the uniformity in K and the explicit rate, not the numerical constant."

---

## Round 2: re-review of the fixed file (self-review, checklist A–H)

This round covers the full diff against `055505f` and every passage that references a changed label.

- **A. Definitions.** ε and κ are now distinct. "N^{θ+o(1)}" is defined wherever it appears.
- **B. Hypothesis discharge.** Each new application was checked:
  - Lemma 2.7 invokes Lemma 2.2 with U = u + 1 and u_N ∈ [1, U] for large N, and Lemma 2.3 with 2 ≤ y ≤ N.
  - Remark 5.3 invokes the proof of Theorem 1.3 with s₀(λ₀); every condition (R1)–(R6) is re-checked in F4.
  - Remark 5.2's alternative uses Theorem 1.2 with K = 0 as N′ → ∞.
- **C. Inequalities.**
  - N/(K(K+1)) ≥ ½N^{2κ}, because K(K+1) ≤ 2K² ≤ 2N^{1−2κ}.
  - For t < 0, N²e^{−qt} > N² ≥ 4 > 1.
  - The left side of (R5) is decreasing in q because N^{2δ} − 2 ≥ 0.
- **D. Interchanges.** None was introduced.
- **E. Probability mode.** The new F12 sentence goes from expectation to probability via Markov's inequality on the non-negative variables \|F₁ △ Φ*\| and Φ^{(2)}, which is correct.
- **F. Uniformity.** Every o(·) and O(·) touched by the fixes now declares its scope (see `PROOF_SKELETON.md` §6).
- **G. Edge cases.**
  - Lemma 2.7 at θ = 0 with K = 0 gives y = N, u_N = 1, and Ψ(N,N)/N = 1 = ρ_Dick(1).
  - Lemma 2.7 at θ = 1 is covered by its second case.
  - F10's new qualifier "if the p_i are distinct" closes the degenerate case p_i = p_j, which was caught in this round.
- **H. Dependencies.** The DAG was re-checked and is acyclic; the topological order is in `PROOF_SKELETON.md` §1.

**New issues found in Round 2:** one, the degenerate case p_i = p_j in F10's new wording. It was fixed in the same round, is MINOR, and sits inside a SKETCH remark. **Open issues after Round 2:** none.

---

## Phase 3.5: global closure and regression

- **Statement–conclusion match.** The final line of each proof was re-read against its statement:
  - T1.3's proof ends with "0 ≤ Ψ − EΦ_K ≤ 30N/ℓ" for both cases of K;
  - C1.4 ends with the limit;
  - C1.5 ends with (a)–(c) for both cases of K;
  - C1.6 ends with the sandwich limit plus the exact identification of the static set;
  - R5.2 ends with the liminf bound.
- **All obligations discharged.** Every node of the DAG is proved or is an explicitly cited external result (Mertens, Chebyshev, Dickman/de Bruijn/Hildebrand, PNT, Bertrand, [KP, Cor. 2]).
- **Case coverage.** The main case splits partition their domains:
  - K ≤ N^{1−η} versus K > N^{1−η};
  - B < 2 versus B ≥ 2;
  - cases (i)/(ii) of Lemma 4.5;
  - the three positions of Φ* in Corollary 1.5;
  - θ < 1 versus θ = 1.
- **Induction correctness.**
  - Lemma 4.2 inducts on Ω′(x), the number of odd prime factors counted with multiplicity. It is a non-negative integer that strictly decreases, and the base case Ω′ = 0 is handled.
  - The adaptive part of Lemma 6.2 inducts on j < K; the base case is T₀ = ∅.
- **WLOG reductions:** none are used.
- **No silent strengthening of assumptions.** Every fix is WEAKEN_CLAIM, ADD_REFERENCE, ADD_DERIVATION or a notation change.
- **Independent blind second review.** Required only for fixes of FATAL or CRITICAL issues; there were none. No blind review was run, and none was available.
- **Regression.**
  - The DAG is acyclic.
  - The counterexample suite was re-run on the downstream lemmas of modified results. Their mathematical content is unchanged, and the scripts in the trace directory reproduce their Round 1 outputs.
  - New trend check for Lemma 2.7 (`regression_psi_limit.py`): Ψ(N, N^{1/u})/N − ρ_Dick(u) decreases steadily for N = 10⁴ … 10⁷ at u ∈ {1.5, 2, 3}. For example, at u = 2 the gap is +0.065, +0.051, +0.037, +0.029, consistent with the expected O(1/log N) rate. This is a sanity check, not a proof.
- **Assumption delta.** Every change goes in the weaker direction:
  - the abstract's claim about degree attacks now covers θ < 1 only;
  - the prose after eq. (1) is additive rather than a ratio asymptotic;
  - Remark 5.2 is restated as a liminf, which is equivalent to the old form;
  - Remark 5.3 has the same statement with a new proof.
  No theorem gained a hypothesis.

## Acceptance gate (self-review)

1. Zero open FATAL or CRITICAL issues: ✓ (none were found at any point).
2. Every theorem and lemma has explicit hypotheses, justified interchanges and discharged applications: ✓ (`PROOF_SKELETON.md` §2).
3. Every big-O, Θ or o statement declares its parameter dependence and uniformity: ✓ (after F9, F12 and F13).
4. The counterexample pass was run on every key lemma: ✓ (Phase 1.5; no counterexamples; two bounds shown to be sharp).

**Self-review gate: PASS.**

## Verdict

**The overall verdict is ERROR, with reason code `reviewer_error`.** The skill's required cross-model reviewer (the Codex MCP server) was unavailable, so the independent-review invariant was not met.

The self-review found and fixed:
- 0 FATAL issues;
- 0 CRITICAL issues;
- 4 MAJOR issues, all scope or citation problems in prose and remarks;
- 10 MINOR issues: 9 from Round 1 and 1 from Round 2.

No issue touched the proofs of Theorems 1.2 and 1.3 or Corollaries 1.4–1.6. **Re-run this skill once a Codex reviewer is connected, to obtain a cross-model verdict.**
