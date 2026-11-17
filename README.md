# Keevash, *The existence of designs II*: Lemma `e|E` (two-sided) and the thinning probability

A Lean 4 / Mathlib formalization of two probabilistic estimates in the random algebraic template
of P. Keevash, [*The existence of designs II*](https://arxiv.org/abs/1802.05900), as explicit
finite-`N` inequalities:

* `DesignsII.TParams.lemma_e_E` — Lemma 3.6 (`e|E`) with Remark 3.7(i), two-sided: conditionally
  on the values of the colours at the fixed vertices `U`, a copy meeting `U` in at most `r − 1`
  vertices (non-degenerate revealed values) passes the tests of colour `j` with probability
  between `(1 − δ)ρ₀(k)` and `ρ₀(k)/(1 − δ)`, `δ = (q² + q|U|)/N`.
* `DesignsII.TParams.thinning_probability` — the probability `P(φ ∈ Φ')` computed in the proof
  of Lemma 3.9 (nibble): for families of copies of pairwise distinct colours with covering
  masses `μ_i ≤ 1`, thinning parameters with `μ_i q_i = t` and independent thinning coins, it
  is `(1 − t)^m` up to `2^m ((∑ μ_i)² + (m + 1) errMax)` (explicit second-order error).

* **Challenge:** [`DesignsIIThinChallenge.lean`](DesignsIIThinChallenge.lean) — the definitions
  (repeated verbatim from the dependency and from
  [`DesignsIIThin/ThinDefs.lean`](DesignsIIThin/ThinDefs.lean)) and the two statements.
* **Solution:** [`DesignsIIThinSolution.lean`](DesignsIIThinSolution.lean), proved in
  [`DesignsIIThin/ThinPaper.lean`](DesignsIIThin/ThinPaper.lean).

## Structure of the proof

| File | Content |
|---|---|
| `PassUpper`, `PassUpperAsymp`, `PassSharp`, `PassMean` | upper half of Lemma `e|E`, sharp two-sided form, first moment |
| `PairPass`, `PairCompat`, `PairAsymp`, `CoverEdge` | joint passing probability of two copies, covering probability of an edge |
| `Bonferroni`, `Complement`, `CoverJoint`, `GroupJoint`, `CoverJointGe`, `TuplePairs`, `TupleBad`, `CoverAllGe` | joint covering of several edges with distinct colours (two-sided, explicit errors) |
| `ThinAlg`, `PatternAlg`, `PatternCover` | probability of a covering pattern |
| `SumSpace`, `ThinMix`, `PhiProb`, `ThinDefs`, `ThinPaper` | the joint space with thinning coins, the thinning probability, the statements |

Depends on [keevash-designs-ii-extension-lemma](https://github.com/jtraverso/keevash-designs-ii-extension-lemma)
(PALOMAR-2026-11-17-000009) for the template space and Lemma `e|E` (lower bound). Lean
`v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

Scope and divergences from the paper are described in [`formalization.yaml`](formalization.yaml).

License: Apache 2.0. Author: Juan Pablo Traverso Gianini.
