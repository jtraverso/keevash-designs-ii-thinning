/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.CoverEdge

/-!
# Joint covering of several edges with distinct colours (upper bound)

`probG_cover_all_le`: in the space conditioned on the values at the fixed vertices, if the
families `C_i` (`i < m`) are to be covered by copies of pairwise distinct colours `j_i`, then

  `P(every family has a passing copy) ≤ ∏_i ∑_{φ ∈ C_i} P(φ passes)`.

Two copies of distinct colours sharing an edge `g` cannot both pass (`T_g` would take two
values), so only edge-disjoint tuples contribute, and for those the joint probability is the
product (`probG_copyOK_joint_cond`). This is the upper half of the "repeated application of
Lemma `e|E`" for the covering patterns of the nibble.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

theorem probG_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}
    (A : (∀ c, Perm (Fin (a c))) → Prop) : 0 ≤ probG (a := a) A := by
  unfold probG; positivity

theorem probG_false {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} :
    probG (a := a) (fun _ => False) = 0 := by
  unfold probG; simp

namespace TParams

variable {P : TParams}

theorem tval_of_copyOK {M : Matrix (Fin P.q) (Fin P.r) F} {κ : Fin P.N ≃ K} {j : Fin P.z}
    {a₀ : Fin P.NA} {k : ℕ} {φ : Fin P.q → Fin P.n} {ω : P.Ω} (h : CopyOK M κ j a₀ k φ ω)
    {g : Finset (Fin P.n)} (hg : g ∈ edges φ) : Tval ω g = j :=
  h.2.2.1 g hg

theorem edges_nonempty {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) :
    (edges φ).Nonempty := by
  rw [← card_pos, card_edges hφ]
  exact Nat.choose_pos P.hrq

open Classical in
/-- **Joint covering, upper bound.** -/
theorem probG_cover_all_le {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (hj : Function.Injective j) (a₀ : Fin P.NA)
    (kk : (Fin P.q → Fin P.n) → ℕ) (C : Fin m → Finset (Fin P.q → Fin P.n))
    (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ) (S : ∀ c : P.Coord, Finset (Fin (P.size c)))
    (v : ∀ c, S c ↪ Fin (P.size c)) :
    probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) ≤
      ∏ i, ∑ φ ∈ C i, probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) := by
  rw [prod_univ_sum]
  calc _ ≤ probG (a := fun c => P.size c - (S c).card) (fun τ => ∃ t ∈ Fintype.piFinset C,
        ∀ i, CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) := by
        refine probG_mono fun τ h => ?_
        choose t ht using h
        exact ⟨t, Fintype.mem_piFinset.2 fun i => (ht i).1, fun i => (ht i).2⟩
    _ ≤ ∑ t ∈ Fintype.piFinset C, probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) :=
        probG_exists_le _ _
    _ ≤ _ := by
        refine sum_le_sum fun t ht => ?_
        have htC := Fintype.mem_piFinset.1 ht
        by_cases hd : ∀ i i', i ≠ i' → Disjoint (edges (t i)) (edges (t i'))
        · have htinj : Function.Injective t := by
            intro i i' h
            by_contra hne
            obtain ⟨g, hg⟩ := edges_nonempty (P := P) (hC i (t i) (htC i))
            have := disjoint_left.1 (hd i i' hne) hg
            exact this (h ▸ hg)
          exact le_of_eq (probG_copyOK_joint_cond S v M κ j (fun _ => a₀) (fun i => kk (t i)) t
            hj htinj hd)
        · push_neg at hd
          obtain ⟨i, i', hne, hnd⟩ := hd
          obtain ⟨g, hg1, hg2⟩ := not_disjoint_iff.1 hnd
          refine le_trans (probG_mono fun τ h => ?_) (le_of_eq_of_le probG_false
            (prod_nonneg fun i _ => probG_nonneg _))
          exact hne (hj ((tval_of_copyOK (h i) hg1).symm.trans (tval_of_copyOK (h i') hg2)))

end TParams

end DesignsII
