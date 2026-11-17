/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtStar

/-!
# Upper bound for the conditional passing probability (Lemma `e|E`, upper half)

`probG_copyOK_cond_le`: a copy with `s = |I₀| ≤ r` fixed vertices passes, given the values at the
fixed vertices, with probability at most
`N^{r-s} (N-|U|-#new)!/(N-|U|)! · z^{-Q} ((q-r)!/q!)^Q |𝒜|^{-1} k/N_act`
(no independence assumption is needed for the upper bound). Together with
`probG_copyOK_cond_ge` this is the two-sided Lemma `e|E` used by the nibble.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Upper bound of Lemma `e|E`.** -/
theorem probG_copyOK_cond_le {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (j : Fin P.z) (a₀ : Fin P.NA) {k : ℕ}
    (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hI : (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card ≤ P.r) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) ≤
      ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) *
        (((P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
          ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) *
        (1 / (P.z : ℝ)) ^ (edges φ).card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by
  have hr : ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
      ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
        mvec M y i) =
      (((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card *
        (P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) :=
    ratio_compat_cond hM κ j hφ U (v (.inl j))
  rw [probG_copyOK_cond M κ j a₀ hk hφ U v, hr]
  have hY := card_Yc_le (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb hφ) hM P.hrq hI
  have hY' : ((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card : ℝ) ≤
      ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) := by
    exact_mod_cast hY
  have hpos : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ (edges φ).card *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by positivity
  have hfac : (0 : ℝ) ≤ (((P.N - (fixedPos U (.inl j)).card -
      Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
      ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) := by positivity
  have key : (((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card *
        (P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) ≤
      ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) *
        ((((P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
          ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ)) := by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hY' hfac)
    push_cast
    ring
  have := mul_le_mul_of_nonneg_right key hpos
  calc _ = (((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card *
        (P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) *
        ((1 / (P.z : ℝ)) ^ (edges φ).card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact)) := by ring
    _ ≤ _ := by convert this using 1; ring

end TParams

end DesignsII
