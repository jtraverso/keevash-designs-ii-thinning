/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.CoverJointGe
public import DesignsIIThin.TupleBad

/-!
# Joint covering, explicit lower bound

`probG_cover_all_ge_explicit`: for families `C_i` of copies of pairwise distinct colours `j_i`,

  `P(every family has a passing copy) ≥ ∏ μ_i - (∏ (μ_i + π_i) - ∏ μ_i)/2
     - ∑_{i ≠ i'} X_{i i'} ∏_{l ∉ {i, i'}} μ_l`,

with `μ_i = ∑_{x ∈ C_i} P(x)`, `π_i = ∑_{x ≠ y ∈ C_i} P(x, y)` and the conflict masses
`X_{i i'} = ∑ P(x) P(y)` over `x ∈ C_i`, `y ∈ C_{i'}` sharing an edge.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Joint covering, explicit lower bound.** -/
theorem probG_cover_all_ge_explicit {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (hj : Function.Injective j) (a₀ : Fin P.NA)
    (kk : (Fin P.q → Fin P.n) → ℕ) (C : Fin m → Finset (Fin P.q → Fin P.n))
    (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ)
    (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c)) :
    let Pr : Fin m → (Fin P.q → Fin P.n) → ℝ := fun i x =>
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) a₀ (kk x) x (liftPi S v τ))
    let Pr2 : Fin m → (Fin P.q → Fin P.n) → (Fin P.q → Fin P.n) → ℝ := fun i x y =>
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) a₀ (kk x) x (liftPi S v τ) ∧
          CopyOK M κ (j i) a₀ (kk y) y (liftPi S v τ))
    let μ : Fin m → ℝ := fun i => ∑ x ∈ C i, Pr i x
    let π : Fin m → ℝ := fun i => ∑ q ∈ (C i).offDiag, Pr2 i q.1 q.2
    let X : Fin m → Fin m → ℝ := fun i i' => ∑ x ∈ C i, ∑ y ∈ C i',
      if ¬ Disjoint (edges x) (edges y) then Pr i x * Pr i' y else 0
    ∏ i, μ i - (∏ i, (μ i + π i) - ∏ i, μ i) / 2 -
        ∑ p ∈ (univ : Finset (Fin m)).offDiag,
          X p.1 p.2 * ∏ l ∈ (univ.erase p.1).erase p.2, μ l ≤
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) := by
  intro Pr Pr2 μ π X
  set conf : (Fin P.q → Fin P.n) → (Fin P.q → Fin P.n) → Prop :=
    fun x y => ¬ Disjoint (edges x) (edges y)
  set T := (Fintype.piFinset C).filter fun t => ¬ ∃ i i', i ≠ i' ∧ conf (t i) (t i')
  have hT : ∀ t ∈ T, (∀ i, t i ∈ C i ∧ Function.Injective (t i)) ∧ Function.Injective t ∧
      ∀ i i', i ≠ i' → Disjoint (edges (t i)) (edges (t i')) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := mem_filter.1 ht
    have hmem := Fintype.mem_piFinset.1 ht1
    have hdisj : ∀ i i', i ≠ i' → Disjoint (edges (t i)) (edges (t i')) := by
      intro i i' hne
      by_contra h
      exact ht2 ⟨i, i', hne, h⟩
    refine ⟨fun i => ⟨hmem i, hC i _ (hmem i)⟩, fun i i' h => ?_, hdisj⟩
    by_contra hne
    obtain ⟨g, hg⟩ := edges_nonempty (P := P) (hC i _ (hmem i))
    exact disjoint_left.1 (hdisj i i' hne) hg (h ▸ hg)
  have hge := probG_cover_all_ge M κ j hj a₀ kk C T hT S v
  -- main term
  have hmain : ∏ i, μ i - ∑ p ∈ (univ : Finset (Fin m)).offDiag,
      X p.1 p.2 * ∏ l ∈ (univ.erase p.1).erase p.2, μ l ≤
      ∑ t ∈ T, ∏ i, Pr i (t i) := by
    have hsplit := sum_filter_add_sum_filter_not (Fintype.piFinset C)
      (fun t => ∃ i i', i ≠ i' ∧ conf (t i) (t i')) (fun t => ∏ i, Pr i (t i))
    have hall : ∑ t ∈ Fintype.piFinset C, ∏ i, Pr i (t i) = ∏ i, μ i := by
      rw [← prod_univ_sum]
    have hbad := sum_tuples_bad_le C Pr (fun l z _ => probG_nonneg _) conf
    have hX : ∀ p ∈ (univ : Finset (Fin m)).offDiag,
        (∑ x ∈ C p.1, ∑ y ∈ C p.2, if conf x y then Pr p.1 x * Pr p.2 y else 0) *
          ∏ l ∈ (univ.erase p.1).erase p.2, ∑ z ∈ C l, Pr l z =
        X p.1 p.2 * ∏ l ∈ (univ.erase p.1).erase p.2, μ l := fun p _ => rfl
    rw [sum_congr rfl hX] at hbad
    have : ∑ t ∈ T, ∏ i, Pr i (t i) = ∏ i, μ i -
        ∑ t ∈ (Fintype.piFinset C).filter (fun t => ∃ i i', i ≠ i' ∧ conf (t i) (t i')),
          ∏ i, Pr i (t i) := by
      rw [← hall]; linarith
    rw [this]
    linarith
  -- pair term
  have hpair : ∑ p ∈ T.offDiag, ∏ i, Pr2 i (p.1 i) (p.2 i) ≤ ∏ i, (μ i + π i) - ∏ i, μ i := by
    have hd : ∀ i, ∀ x ∈ C i, Pr2 i x x = Pr i x := by
      intro i x _
      simp only [Pr2, Pr, and_self]
    have h := sum_offDiag_tuples_le C Pr2 T (filter_subset _ _)
      (fun i x _ y _ => probG_nonneg _)
    have hμ : ∀ i, ∑ x ∈ C i, Pr2 i x x = μ i := fun i => sum_congr rfl (hd i)
    simp only [hμ] at h
    exact h
  have hge' : ∑ t ∈ T, ∏ i, Pr i (t i) - (∑ p ∈ T.offDiag, ∏ i, Pr2 i (p.1 i) (p.2 i)) / 2 ≤
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) := hge
  linarith

end TParams

end DesignsII
