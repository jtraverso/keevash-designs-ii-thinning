/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PatternAlg

/-!
# Sums over pairs of tuples

`sum_offDiag_tuples`: for families `C_i` and weights `f_i(x, y)`,

  `∑_{t ≠ t' ∈ ∏ C_i} ∏_i f_i(t_i, t'_i) = ∏_i ∑_{x, y ∈ C_i} f_i(x, y) - ∏_i ∑_{x ∈ C_i} f_i(x, x)`.

With `f_i(x, x) = P(x)` and `f_i(x, y) = P(x, y both pass)` the Bonferroni correction of
`probG_cover_all_ge` is at most `∏_i (μ_i + π_i) - ∏_i μ_i`, `π_i = ∑_{x ≠ y ∈ C_i} P(x, y)`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {α : Type*} [DecidableEq α]

theorem sum_product_tuples {m : ℕ} (C : Fin m → Finset α) (f : Fin m → α → α → ℝ) :
    ∑ p ∈ Fintype.piFinset C ×ˢ Fintype.piFinset C, ∏ i, f i (p.1 i) (p.2 i) =
      ∏ i, ∑ x ∈ C i, ∑ y ∈ C i, f i x y := by
  rw [sum_product, prod_univ_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_univ_sum]

theorem sum_diag_tuples {m : ℕ} (C : Fin m → Finset α) (f : Fin m → α → α → ℝ) :
    ∑ p ∈ (Fintype.piFinset C).diag, ∏ i, f i (p.1 i) (p.2 i) =
      ∏ i, ∑ x ∈ C i, f i x x := by
  rw [prod_univ_sum, diag, sum_map]
  rfl

/-- **Sum over pairs of distinct tuples.** -/
theorem sum_offDiag_tuples {m : ℕ} (C : Fin m → Finset α) (f : Fin m → α → α → ℝ) :
    ∑ p ∈ (Fintype.piFinset C).offDiag, ∏ i, f i (p.1 i) (p.2 i) =
      ∏ i, ∑ x ∈ C i, ∑ y ∈ C i, f i x y - ∏ i, ∑ x ∈ C i, f i x x := by
  rw [← sum_product_tuples, ← sum_diag_tuples, ← diag_union_offDiag,
    sum_union (disjoint_diag_offDiag _)]
  ring

/-- **The Bonferroni correction is at most `∏ (μ_i + π_i) - ∏ μ_i`.** -/
theorem sum_offDiag_tuples_le {m : ℕ} (C : Fin m → Finset α) (f : Fin m → α → α → ℝ)
    (T : Finset (Fin m → α)) (hT : T ⊆ Fintype.piFinset C)
    (hf : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, 0 ≤ f i x y) :
    ∑ p ∈ T.offDiag, ∏ i, f i (p.1 i) (p.2 i) ≤
      ∏ i, (∑ x ∈ C i, f i x x + ∑ q ∈ (C i).offDiag, f i q.1 q.2) - ∏ i, ∑ x ∈ C i, f i x x := by
  have hsplit : ∀ i, ∑ x ∈ C i, ∑ y ∈ C i, f i x y =
      ∑ x ∈ C i, f i x x + ∑ q ∈ (C i).offDiag, f i q.1 q.2 := by
    intro i
    rw [← sum_product' (f := f i), ← diag_union_offDiag, sum_union (disjoint_diag_offDiag _)]
    congr 1
    rw [diag, sum_map]
    rfl
  simp_rw [← hsplit]
  rw [← sum_offDiag_tuples]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_offDiag.1 hp
    exact mem_offDiag.2 ⟨hT h1, hT h2, h3⟩
  · obtain ⟨h1, h2, -⟩ := mem_offDiag.1 hp
    exact prod_nonneg fun i _ => hf i _ (Fintype.mem_piFinset.1 h1 i) _
      (Fintype.mem_piFinset.1 h2 i)

end DesignsII
