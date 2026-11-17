/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PairCompat

/-!
# Joint passing probability in closed form

`probG_pair_cond_le_explicit`: two distinct copies `φ ≠ φ'` of colour `j`, meeting the fixed set
in `s, s' ≤ r` vertices, both pass (given the values at the fixed vertices) with probability at
most

  `N^{r-s} N^{r-s'} (N-|U|-|W ∪ W'|)!/(N-|U|)! · z^{-|E∪E'|} ((q-r)!/q!)^{|E∪E'|}
    |𝒜|^{-2} (k/N_act)(k'/N_act)`,

`W, W'` the new positions of the copies. For copies sharing only the fixed vertices this is
`(1 + O(1/N)) ρ₀(k) ρ₀(k') (z q!/(q-r)!)^{|E ∩ E'|}`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Joint passing probability, closed form.** -/
theorem probG_pair_cond_le_explicit {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (j : Fin P.z) (a₀ : Fin P.NA) {k k' : ℕ} (hk : k ≤ P.Nact)
    (hk' : k' ≤ P.Nact) {φ φ' : Fin P.q → Fin P.n} (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (hne : φ ≠ φ') (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hI : (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card ≤ P.r)
    (hI' : (I₀ (fixedPos U (.inl j)) (wEmb hφ')).card ≤ P.r) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ) ∧
          CopyOK M κ j a₀ k' φ' (liftPi (fixedPos U) v τ)) ≤
      ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) *
          Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ')).card) *
          (P.N - (fixedPos U (.inl j)).card -
            (newSet2 (fixedPos U (.inl j)) (wEmb hφ) (wEmb hφ')).card).factorial : ℕ) : ℝ) /
          ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) *
        (1 / (P.z : ℝ)) ^ (edges φ ∪ edges φ').card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ ∪ edges φ').card *
        (1 / (P.NA : ℝ)) ^ 2 * (((k : ℝ) / P.Nact) * ((k' : ℝ) / P.Nact)) := by
  refine (probG_pair_cond_le M κ j a₀ hk hk' hφ hφ' hne U v).trans ?_
  have hr : ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
      (∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
        mvec M y i) ∧
      ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ' i))) =
        mvec M y i) ≤
      ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) *
          Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ')).card) *
          (P.N - (fixedPos U (.inl j)).card -
            (newSet2 (fixedPos U (.inl j)) (wEmb hφ) (wEmb hφ')).card).factorial : ℕ) : ℝ) /
          ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) := by
    unfold ratio
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hc := card_cond_compat_pair_le (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)
      (wEmb hφ')
    have hY := card_Yc_le (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb hφ) hM P.hrq hI
    have hY' := card_Yc_le (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb hφ') hM P.hrq hI'
    have h3 := hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hY hY'))
    norm_cast
    convert h3 using 3
    · exact Iff.rfl
    · rfl
  have hrest : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ (edges φ ∪ edges φ').card *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ ∪ edges φ').card *
      (1 / (P.NA : ℝ)) ^ 2 * (((k : ℝ) / P.Nact) * ((k' : ℝ) / P.Nact)) := by positivity
  have := mul_le_mul_of_nonneg_right hr hrest
  convert this using 1 <;> ring

end TParams

end DesignsII
