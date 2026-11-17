/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ManyDeg

/-!
# Second Bonferroni inequality

`probG_exists_ge_bonferroni`: `P(⋃ A_b) ≥ ∑ P(A_b) - ½ ∑_{b ≠ b'} P(A_b ∩ A_{b'})`.
Together with the union bound `probG_exists_le` it gives the covering probability of an edge
(Remark 3.7(i) of Designs II) from first and second moments of the passing copies through it.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-- Pointwise: `k - k(k-1)/2 ≤ [k > 0]`. -/
theorem bonf_pointwise (k : ℕ) :
    (k : ℝ) - ((k * k - k : ℕ) : ℝ) / 2 ≤ if k = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [if_neg hk.ne']
    have h : k ≤ k * k := Nat.le_mul_self k
    rw [Nat.cast_sub h]
    push_cast
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; norm_num
    · have : (2 : ℝ) ≤ k := by exact_mod_cast h2
      nlinarith

open Classical in
/-- **Second Bonferroni inequality** under independent uniform permutations. -/
theorem probG_exists_ge_bonferroni {β : Type*} (S : Finset β)
    (A : β → (∀ c, Perm (Fin (a c))) → Prop) :
    ∑ b ∈ S, probG (a := a) (A b) -
        (∑ p ∈ S.offDiag, probG (a := a) (fun ω => A p.1 ω ∧ A p.2 ω)) / 2 ≤
      probG (a := a) (fun ω => ∃ b ∈ S, A b ω) := by
  unfold probG
  set D : ℝ := ∏ i, ((a i).factorial : ℝ)
  have hD : 0 < D := by positivity
  have pt : ∀ ω, (∑ b ∈ S, (if A b ω then (1 : ℝ) else 0)) -
      (∑ p ∈ S.offDiag, (if A p.1 ω ∧ A p.2 ω then (1 : ℝ) else 0)) / 2 ≤
      (if ∃ b ∈ S, A b ω then (1 : ℝ) else 0) := by
    intro ω
    set T := S.filter fun b => A b ω with hT
    have h1 : ∑ b ∈ S, (if A b ω then (1 : ℝ) else 0) = T.card := by
      rw [hT, card_filter]; push_cast; rfl
    have h2 : ∑ p ∈ S.offDiag, (if A p.1 ω ∧ A p.2 ω then (1 : ℝ) else 0) =
        ((T.card * T.card - T.card : ℕ) : ℝ) := by
      rw [← offDiag_card, Finset.sum_boole, hT]
      congr 2
      ext p
      simp only [mem_filter, mem_offDiag]
      tauto
    have h3 : (if ∃ b ∈ S, A b ω then (1 : ℝ) else 0) = if T.card = 0 then 0 else 1 := by
      by_cases h : ∃ b ∈ S, A b ω
      · rw [if_pos h, if_neg]
        obtain ⟨b, hb, hA⟩ := h
        exact (card_pos.2 ⟨b, mem_filter.2 ⟨hb, hA⟩⟩).ne'
      · rw [if_neg h, if_pos]
        rw [card_eq_zero, filter_eq_empty_iff]
        exact fun b hb hA => h ⟨b, hb, hA⟩
    rw [h1, h2, h3]
    exact bonf_pointwise _
  have key : (∑ b ∈ S, ((univ.filter (A b)).card : ℝ)) -
      (∑ p ∈ S.offDiag, ((univ.filter fun ω => A p.1 ω ∧ A p.2 ω).card : ℝ)) / 2 ≤
      ((univ.filter fun ω => ∃ b ∈ S, A b ω).card : ℝ) := by
    simp_rw [card_filter]
    push_cast
    rw [sum_comm, sum_comm (s := S.offDiag), sum_div, ← sum_sub_distrib]
    refine sum_le_sum fun ω _ => ?_
    exact pt ω
  have := div_le_div_of_nonneg_right key hD.le
  convert this using 1
  · simp only [← sum_div]
    field_simp
    congr!
  · congr!

end DesignsII
