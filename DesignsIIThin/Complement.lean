/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.Bonferroni

/-!
# Patterns with uncovered edges (Bonferroni for complements)

* `probG_split`: `P(A) = P(A ∧ X) + P(A ∧ ¬X)`;
* `probG_and_none_ge`: `P(A ∧ no B_i) ≥ P(A) - ∑_i P(A ∧ B_i)`;
* `probG_and_none_le`: `P(A ∧ no B_i) ≤ P(A) - ∑_i P(A ∧ B_i) + ½ ∑_{i ≠ i'} P(A ∧ B_i ∧ B_{i'})`.

For a covering pattern `v` of the edges of a copy, `A` is "the edges with `v_e = 1` are covered"
and the `B_i` are "the edge `i` with `v_i = 0` is covered"; every term on the right is then an
all-covered event, estimated by `probG_cover_all_le` / `probG_cover_all_ge`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

open Classical in
/-- **Additivity.** -/
theorem probG_split (A X : (∀ c, Perm (Fin (a c))) → Prop) :
    probG (a := a) A = probG (a := a) (fun ω => A ω ∧ X ω) +
      probG (a := a) (fun ω => A ω ∧ ¬ X ω) := by
  unfold probG
  rw [← add_div]
  congr 1
  have h := card_filter_add_card_filter_not (s := univ.filter A) X
  rw [filter_filter, filter_filter] at h
  calc (((univ.filter A).card : ℕ) : ℝ) = ((_ + _ : ℕ) : ℝ) := by rw [h]
    _ = _ := by push_cast; congr!

/-- **Lower bound for a pattern with uncovered edges.** -/
theorem probG_and_none_ge {β : Type*} (R : Finset β) (A : (∀ c, Perm (Fin (a c))) → Prop)
    (B : β → (∀ c, Perm (Fin (a c))) → Prop) :
    probG (a := a) A - ∑ i ∈ R, probG (a := a) (fun ω => A ω ∧ B i ω) ≤
      probG (a := a) (fun ω => A ω ∧ ¬ ∃ i ∈ R, B i ω) := by
  have hs := probG_split A (fun ω => ∃ i ∈ R, B i ω)
  have hu : probG (a := a) (fun ω => A ω ∧ ∃ i ∈ R, B i ω) ≤
      ∑ i ∈ R, probG (a := a) (fun ω => A ω ∧ B i ω) := by
    refine le_trans (le_of_eq ?_) (probG_exists_le R fun i ω => A ω ∧ B i ω)
    congr 1
    funext ω
    exact propext ⟨fun ⟨hA, i, hi, hB⟩ => ⟨i, hi, hA, hB⟩, fun ⟨i, hi, hA, hB⟩ => ⟨hA, i, hi, hB⟩⟩
  linarith

/-- **Upper bound for a pattern with uncovered edges.** -/
theorem probG_and_none_le {β : Type*} (R : Finset β) (A : (∀ c, Perm (Fin (a c))) → Prop)
    (B : β → (∀ c, Perm (Fin (a c))) → Prop) :
    probG (a := a) (fun ω => A ω ∧ ¬ ∃ i ∈ R, B i ω) ≤
      probG (a := a) A - ∑ i ∈ R, probG (a := a) (fun ω => A ω ∧ B i ω) +
        (∑ p ∈ R.offDiag, probG (a := a) (fun ω => A ω ∧ B p.1 ω ∧ B p.2 ω)) / 2 := by
  have hs := probG_split A (fun ω => ∃ i ∈ R, B i ω)
  have hb := probG_exists_ge_bonferroni R fun i ω => A ω ∧ B i ω
  have he : probG (a := a) (fun ω => ∃ i ∈ R, A ω ∧ B i ω) =
      probG (a := a) (fun ω => A ω ∧ ∃ i ∈ R, B i ω) := by
    congr 1
    funext ω
    exact propext ⟨fun ⟨i, hi, hA, hB⟩ => ⟨hA, i, hi, hB⟩, fun ⟨hA, i, hi, hB⟩ => ⟨i, hi, hA, hB⟩⟩
  have hp : ∑ p ∈ R.offDiag, probG (a := a) (fun ω => (A ω ∧ B p.1 ω) ∧ A ω ∧ B p.2 ω) =
      ∑ p ∈ R.offDiag, probG (a := a) (fun ω => A ω ∧ B p.1 ω ∧ B p.2 ω) := by
    refine sum_congr rfl fun p _ => ?_
    congr 1
    funext ω
    exact propext ⟨fun h => ⟨h.1.1, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩⟩
  rw [he, hp] at hb
  linarith

end DesignsII
