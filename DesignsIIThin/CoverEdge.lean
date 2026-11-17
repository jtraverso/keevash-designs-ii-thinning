/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PairAsymp
public import DesignsIIThin.Bonferroni

/-!
# The covering probability of an edge (Remark 3.7(i), two-sided)

For a family `C` of injective copies `φ_b` of colour `j` (thresholds `k_b`), conditionally on
the values at the fixed vertices `U`, the probability that some copy of the family is in the
template satisfies

  `(1 - δ) ∑_b ρ₀(k_b) - ½ ∑_{b ≠ b'} P(φ_b, φ_{b'} both pass) ≤ P(cover) ≤ ∑_b ρ₀(k_b)/(1 - δ)`,

`δ = (q² + q|U|)/N`; the pair probabilities are bounded by `probG_pair_cond_le_explicit`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Upper bound for the covering probability.** -/
theorem probG_cover_edge_le {β : Type*} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (j : Fin P.z) (a₀ : Fin P.NA) (C : Finset β)
    (kk : β → ℕ) (hk : ∀ b, kk b ≤ P.Nact) (φ : β → Fin P.q → Fin P.n)
    (hφ : ∀ b, Function.Injective (φ b)) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : ∀ b ∈ C, (univ.filter fun i => φ b i ∈ U).card ≤ P.r)
    (hN : P.q ^ 2 + P.q * U.card < P.N) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => ∃ b ∈ C, CopyOK M κ j a₀ (kk b) (φ b) (liftPi (fixedPos U) v τ)) ≤
      (∑ b ∈ C, P.rho0 (kk b)) / (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) := by
  refine (probG_exists_le _ _).trans ?_
  rw [← meanG_count]
  exact meanG_pass_le hM κ hK a₀ C (fun _ => j) kk hk φ hφ U v hs hN

open Classical in
/-- **Lower bound for the covering probability** (second Bonferroni inequality). -/
theorem probG_cover_edge_ge {β : Type*} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (j : Fin P.z)
    (a₀ : Fin P.NA) (C : Finset β) (kk : β → ℕ) (hk : ∀ b, kk b ≤ P.Nact)
    (φ : β → Fin P.q → Fin P.n) (hφ : ∀ b, Function.Injective (φ b)) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : ∀ b ∈ C, (univ.filter fun i => φ b i ∈ U).card + 1 ≤ P.r)
    (hc : ∀ b ∈ C, LinearIndependent F fun t : Fin (I₀ (fixedPos U (.inl j))
        (wEmb (hφ b))).card =>
      cval (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb (hφ b))
        ((I₀ (fixedPos U (.inl j)) (wEmb (hφ b))).orderEmbOfFin rfl t))
    (hN : P.q ^ 2 + P.q * U.card ≤ P.N) (hUq : U.card + P.q ≤ P.N) :
    (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) * ∑ b ∈ C, P.rho0 (kk b) -
        (∑ p ∈ C.offDiag, probG (a := fun c => P.size c - (fixedPos U c).card)
          (fun τ => CopyOK M κ j a₀ (kk p.1) (φ p.1) (liftPi (fixedPos U) v τ) ∧
            CopyOK M κ j a₀ (kk p.2) (φ p.2) (liftPi (fixedPos U) v τ))) / 2 ≤
      probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => ∃ b ∈ C, CopyOK M κ j a₀ (kk b) (φ b) (liftPi (fixedPos U) v τ)) := by
  refine le_trans ?_ (probG_exists_ge_bonferroni C
    (fun b τ => CopyOK M κ j a₀ (kk b) (φ b) (liftPi (fixedPos U) v τ)))
  have h := meanG_pass_ge hM hrows κ hK a₀ C (fun _ => j) kk hk φ hφ U v hs hc hN hUq
  rw [meanG_count] at h
  linarith

end TParams

end DesignsII
