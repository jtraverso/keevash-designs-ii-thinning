/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PassSharp
public import DesignsIIThin.ThinDefs

/-!
# Expected number of passing copies (sharp, weighted by the activation thresholds)

For a family of injective copies `φ_b` (`b ∈ C`) with colours `j_b` and activation thresholds
`k_b`, conditionally on the values at the fixed vertices `U`, the expected number of copies in
the template is `(1 ± O(δ)) ∑_b ρ₀(k_b)`, `δ = (q² + q|U|)/N`, where

  `ρ₀(k) = N^{r-q} z^{-Q} ((q-r)!/q!)^Q |𝒜|^{-1} k/N_act`.

This is the first-moment input of the nibble (N4): with `k_b/N_act` proportional to the
regularity weights `y_φ`, the expectation is proportional to `∑_{φ ⊇ ψ} y_φ`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

theorem rho0_nonneg (k : ℕ) : 0 ≤ P.rho0 k := by unfold rho0; positivity

open Classical in
/-- **Upper bound for the expected number of passing copies.** -/
theorem meanG_pass_le {β : Type*} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (a₀ : Fin P.NA) (C : Finset β)
    (j : β → Fin P.z) (kk : β → ℕ) (hk : ∀ b, kk b ≤ P.Nact) (φ : β → Fin P.q → Fin P.n)
    (hφ : ∀ b, Function.Injective (φ b)) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : ∀ b ∈ C, (univ.filter fun i => φ b i ∈ U).card ≤ P.r)
    (hN : P.q ^ 2 + P.q * U.card < P.N) :
    meanG (a := fun c => P.size c - (fixedPos U c).card)
        (countVar C fun b τ => CopyOK M κ (j b) a₀ (kk b) (φ b) (liftPi (fixedPos U) v τ)) ≤
      (∑ b ∈ C, P.rho0 (kk b)) / (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) := by
  rw [meanG_count, sum_div]
  refine sum_le_sum fun b hb => ?_
  have h := probG_copyOK_cond_le_sharp hM κ hK (j b) a₀ (hk b) (hφ b) U v (hs b hb) hN
  refine h.trans (le_of_eq ?_)
  unfold rho0
  have hX : (0 : ℝ) < P.N := by exact_mod_cast (show 0 < P.N by omega)
  have hδ : ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N < 1 := by
    rw [div_lt_one hX]; exact_mod_cast hN
  have h1 : (1 : ℝ) - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N ≠ 0 := by linarith
  have h2 : (P.N : ℝ) ^ (P.q - P.r) ≠ 0 := by positivity
  field_simp

open Classical in
/-- **Lower bound for the expected number of passing copies** (copies with at most `r - 1`
fixed vertices, whose colours are non-degenerate at the fixed vertices). -/
theorem meanG_pass_ge {β : Type*} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (a₀ : Fin P.NA)
    (C : Finset β) (j : β → Fin P.z) (kk : β → ℕ) (hk : ∀ b, kk b ≤ P.Nact)
    (φ : β → Fin P.q → Fin P.n) (hφ : ∀ b, Function.Injective (φ b)) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : ∀ b ∈ C, (univ.filter fun i => φ b i ∈ U).card + 1 ≤ P.r)
    (hc : ∀ b ∈ C, LinearIndependent F fun t : Fin (I₀ (fixedPos U (.inl (j b)))
        (wEmb (hφ b))).card =>
      cval (fixedPos U (.inl (j b))) (v (.inl (j b))) κ (wEmb (hφ b))
        ((I₀ (fixedPos U (.inl (j b))) (wEmb (hφ b))).orderEmbOfFin rfl t))
    (hN : P.q ^ 2 + P.q * U.card ≤ P.N) (hUq : U.card + P.q ≤ P.N) :
    (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) * ∑ b ∈ C, P.rho0 (kk b) ≤
      meanG (a := fun c => P.size c - (fixedPos U c).card)
        (countVar C fun b τ => CopyOK M κ (j b) a₀ (kk b) (φ b) (liftPi (fixedPos U) v τ)) := by
  rw [meanG_count, mul_sum]
  refine sum_le_sum fun b hb => ?_
  have hI := I₀_fixedPos (P := P) U (j b) (hφ b)
  have hlo := passLB_ge_sharp (K := K) hK U (j b) (hφ b) (kk b) (hs b hb) hN hUq
  have hge := probG_copyOK_cond_ge hM hrows κ (j b) a₀ (hk b) (hφ b) U v
    (by rw [hI]; exact hs b hb) (hc b hb)
  refine le_trans (le_of_eq ?_) (hlo.trans ?_)
  · unfold rho0; ring
  · unfold passLB; exact hge

end TParams

end DesignsII
