/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PassMean

/-!
# Joint passing probability of two copies of the same colour

`probG_pair_cond_le`: in the space conditioned on the values at the fixed vertices `U`, two
distinct injective copies `φ ≠ φ'` of the same colour `j` both pass with probability at most

  `P_f^{pair} · z^{-|E ∪ E'|} ((q-r)!/q!)^{|E ∪ E'|} |𝒜|^{-2} (k/N_act)(k'/N_act)`,

where `E, E'` are their edge sets and `P_f^{pair}` is the conditional probability that `f_j` is
compatible with both. Shared edges are counted once: this is what makes the Bonferroni
correction of the covering probability of lower order.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

theorem ratio_mono {m : ℕ} {E E' : Perm (Fin m) → Prop} (h : ∀ σ, E σ → E' σ) :
    ratio E ≤ ratio E' := by
  classical
  unfold ratio
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_le_card fun σ hσ => mem_filter.2 ⟨mem_univ _, h σ (mem_filter.1 hσ).2⟩

theorem ratio_nonneg {m : ℕ} (E : Perm (Fin m) → Prop) : 0 ≤ ratio E := by
  unfold ratio; positivity

theorem ratio_le_one {m : ℕ} (E : Perm (Fin m) → Prop) : ratio E ≤ 1 := by
  rw [← ratio_true' (fun _ : Perm (Fin m) => True) fun _ => trivial]
  exact ratio_mono fun _ _ => trivial

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Joint passing probability of two copies of the same colour** (upper bound). -/
theorem probG_pair_cond_le (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) {k k' : ℕ} (hk : k ≤ P.Nact) (hk' : k' ≤ P.Nact)
    {φ φ' : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (hne : φ ≠ φ') (U : Finset (Fin P.n)) (v : ∀ c, fixedPos U c ↪ Fin (P.size c)) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ) ∧
          CopyOK M κ j a₀ k' φ' (liftPi (fixedPos U) v τ)) ≤
      ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
          (∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
            mvec M y i) ∧
          ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ' i))) =
            mvec M y i) *
        (1 / (P.z : ℝ)) ^ (edges φ ∪ edges φ').card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ ∪ edges φ').card *
        (1 / (P.NA : ℝ)) ^ 2 * (((k : ℝ) / P.Nact) * ((k' : ℝ) / P.Nact)) := by
  set L := fun c => liftC (fixedPos U c) (v c)
  have hiff : (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ) ∧
      CopyOK M κ j a₀ k' φ' (liftPi (fixedPos U) v τ)) =
      fun τ => ∀ c, copyEv M κ j a₀ k φ c (L c (τ c)) ∧ copyEv M κ j a₀ k' φ' c (L c (τ c)) := by
    funext τ
    rw [copyOK_iff M κ j a₀ k φ, copyOK_iff M κ j a₀ k' φ']
    exact propext ⟨fun h c => ⟨h.1 c, h.2 c⟩, fun h => ⟨fun c => (h c).1, fun c => (h c).2⟩⟩
  rw [hiff, probG_pi (fun c σ => copyEv M κ j a₀ k φ c (L c σ) ∧ copyEv M κ j a₀ k' φ' c (L c σ))]
  -- the bounding function
  set g : P.Coord → ℝ := fun c => match c with
    | .inl j' => if j' = j then ratio (fun σ : Perm (Fin (P.size (.inl j) -
          (fixedPos U (.inl j)).card)) =>
          (∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
            mvec M y i) ∧
          ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ' i))) =
            mvec M y i) else 1
    | .inr (.inl e) => if e ∈ edges φ ∪ edges φ' then 1 / (P.z : ℝ) else 1
    | .inr (.inr (.inl e)) => if e ∈ edges φ ∪ edges φ' then
        ((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ) else 1
    | .inr (.inr (.inr (.inl ψ))) => if ψ = φ then 1 / (P.NA : ℝ) else
        if ψ = φ' then 1 / (P.NA : ℝ) else 1
    | .inr (.inr (.inr (.inr ψ))) => if ψ = φ then (k : ℝ) / P.Nact else
        if ψ = φ' then (k' : ℝ) / P.Nact else 1 with hg
  have hle : ∀ c, ratio (fun σ => copyEv M κ j a₀ k φ c (L c σ) ∧
      copyEv M κ j a₀ k' φ' c (L c σ)) ≤ g c := by
    intro c
    rcases c with j' | e | e | ψ | ψ
    · simp only [hg]
      by_cases h : j' = j
      · rw [if_pos h]; subst h
        exact le_of_eq (ratio_congr fun σ =>
          ⟨fun h => ⟨h.1 rfl, h.2 rfl⟩, fun h => ⟨fun _ => h.1, fun _ => h.2⟩⟩)
      · rw [if_neg h]; exact ratio_le_one _
    · simp only [hg]
      by_cases h1 : e ∈ edges φ
      · rw [if_pos (mem_union_left _ h1)]
        refine (ratio_mono fun σ h => h.1).trans (le_of_eq ?_)
        rw [ratio_liftC_of_empty (fixedPos U (.inr (.inl e))) rfl, ratio_T, if_pos h1]
      · by_cases h2 : e ∈ edges φ'
        · rw [if_pos (mem_union_right _ h2)]
          refine (ratio_mono fun σ h => h.2).trans (le_of_eq ?_)
          rw [ratio_liftC_of_empty (fixedPos U (.inr (.inl e))) rfl, ratio_T, if_pos h2]
        · rw [if_neg (by simp [h1, h2])]; exact ratio_le_one _
    · simp only [hg]
      by_cases h1 : e ∈ edges φ
      · rw [if_pos (mem_union_left _ h1)]
        refine (ratio_mono fun σ h => h.1).trans (le_of_eq ?_)
        rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inl e)))) rfl, ratio_pi κ j a₀ k hφ,
          if_pos h1]
      · by_cases h2 : e ∈ edges φ'
        · rw [if_pos (mem_union_right _ h2)]
          refine (ratio_mono fun σ h => h.2).trans (le_of_eq ?_)
          rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inl e)))) rfl,
            ratio_pi κ j a₀ k' hφ', if_pos h2]
        · rw [if_neg (by simp [h1, h2])]; exact ratio_le_one _
    · simp only [hg]
      by_cases h1 : ψ = φ
      · rw [if_pos h1]
        refine (ratio_mono fun σ h => h.1).trans (le_of_eq ?_)
        rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inr (.inl ψ))))) rfl, ratio_A,
          if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : ψ = φ'
        · rw [if_pos h2]
          refine (ratio_mono fun σ h => h.2).trans (le_of_eq ?_)
          rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inr (.inl ψ))))) rfl, ratio_A,
            if_pos h2]
        · rw [if_neg h2]; exact ratio_le_one _
    · simp only [hg]
      by_cases h1 : ψ = φ
      · rw [if_pos h1]
        refine (ratio_mono fun σ h => h.1).trans (le_of_eq ?_)
        rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inr (.inr ψ))))) rfl,
          ratio_act M κ j a₀ hk, if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : ψ = φ'
        · rw [if_pos h2]
          refine (ratio_mono fun σ h => h.2).trans (le_of_eq ?_)
          rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inr (.inr ψ))))) rfl,
            ratio_act M κ j a₀ hk', if_pos h2]
        · rw [if_neg h2]; exact ratio_le_one _
  refine (prod_le_prod₀ (fun c _ => ratio_nonneg _) fun c _ => hle c).trans (le_of_eq ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [hg]
  rw [prod_ite_eq' univ j, prod_ite_mem, prod_ite_mem, univ_inter, prod_const, prod_const]
  have hA : ∏ ψ : Fin P.q → Fin P.n, (if ψ = φ then 1 / (P.NA : ℝ) else
      if ψ = φ' then 1 / (P.NA : ℝ) else 1) = (1 / (P.NA : ℝ)) ^ 2 := by
    rw [← prod_mul_prod_compl {φ}, prod_singleton, if_pos rfl]
    rw [prod_congr rfl fun ψ hψ => if_neg (by simpa using hψ),
      prod_ite_eq' _ φ', if_pos (by simpa using hne.symm)]
    ring
  have hact : ∏ ψ : Fin P.q → Fin P.n, (if ψ = φ then (k : ℝ) / P.Nact else
      if ψ = φ' then (k' : ℝ) / P.Nact else 1) = (k : ℝ) / P.Nact * ((k' : ℝ) / P.Nact) := by
    rw [← prod_mul_prod_compl {φ}, prod_singleton, if_pos rfl]
    rw [prod_congr rfl fun ψ hψ => if_neg (by simpa using hψ),
      prod_ite_eq' _ φ', if_pos (by simpa using hne.symm)]
  rw [hA, hact]
  simp only [mem_univ, if_true]
  ring

end TParams

end DesignsII
