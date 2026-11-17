/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.CoverJoint

/-!
# Independence of groups of copies with distinct colours

`probG_group_joint_cond`: in the conditioned space, groups `G_i` of copies, group `i` of colour
`j_i` (pairwise distinct), with no edge shared between different groups and no copy in two
groups, pass independently:

  `P(∀ i, ∀ φ ∈ G_i, φ passes in colour j_i) = ∏_i P(∀ φ ∈ G_i, φ passes in colour j_i)`.

This generalizes `probG_copyOK_joint_cond` (singleton groups) and is used for the second moment
of the joint covering of several edges.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams} (S : ∀ c : P.Coord, Finset (Fin (P.size c)))
  (v : ∀ c, S c ↪ Fin (P.size c))

omit [Fintype K] [DecidableEq K] in
/-- **Groups of copies with distinct colours pass independently.** -/
theorem probG_group_joint_cond {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (hj : Function.Injective j) (a₀ : Fin P.NA)
    (kk : (Fin P.q → Fin P.n) → ℕ) (G : Fin m → Finset (Fin P.q → Fin P.n))
    (hcopy : ∀ i i', i ≠ i' → Disjoint (G i) (G i'))
    (hedge : ∀ i i', i ≠ i' → ∀ φ ∈ G i, ∀ φ' ∈ G i', Disjoint (edges φ) (edges φ')) :
    probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) =
      ∏ i, probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) := by
  set E : Fin m → ∀ c : P.Coord, Perm (Fin (P.size c - (S c).card)) → Prop :=
    fun i c σ => ∀ φ ∈ G i, copyEv M κ (j i) a₀ (kk φ) φ c (liftC (S c) (v c) σ)
  have hiff : ∀ i τ, (∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) ↔
      ∀ c, E i c (τ c) := by
    intro i τ
    constructor
    · intro h c φ hφ
      exact (copyOK_iff M κ (j i) a₀ (kk φ) φ _).1 (h φ hφ) c
    · intro h φ hφ
      exact (copyOK_iff M κ (j i) a₀ (kk φ) φ _).2 fun c => h c φ hφ
  have hall : (fun τ => ∀ i, ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) =
      fun τ => ∀ i c, E i c (τ c) :=
    funext fun τ => propext (forall_congr' fun i => hiff i τ)
  have hone : ∀ i, (fun τ => ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) =
      fun τ => ∀ c, E i c (τ c) := fun i => funext fun τ => propext (hiff i τ)
  rw [hall]
  simp_rw [hone]
  refine probG_forall_indep E fun c i i' hii => ?_
  rcases c with j' | e | e | ψ | ψ
  · by_cases h : j i = j'
    · right; intro σ φ _ hh; exact absurd (hj (h.trans hh)) hii
    · left; intro σ φ _ hh; exact absurd hh.symm h
  · by_cases h : ∃ φ ∈ G i, e ∈ edges φ
    · obtain ⟨φ, hφ, he⟩ := h
      right; intro σ φ' hφ' he'
      exact absurd he' (disjoint_left.1 (hedge i i' hii φ hφ φ' hφ') he)
    · push_neg at h
      left; intro σ φ hφ he; exact absurd he (h φ hφ)
  · by_cases h : ∃ φ ∈ G i, e ∈ edges φ
    · obtain ⟨φ, hφ, he⟩ := h
      right; intro σ φ' hφ' he'
      exact absurd he' (disjoint_left.1 (hedge i i' hii φ hφ φ' hφ') he)
    · push_neg at h
      left; intro σ φ hφ he; exact absurd he (h φ hφ)
  · by_cases h : ψ ∈ G i
    · right; intro σ φ' hφ' hh
      exact absurd (hh ▸ h) (disjoint_left.1 (hcopy i i' hii) · hφ')
    · left; intro σ φ hφ hh; exact absurd (hh ▸ hφ) h
  · by_cases h : ψ ∈ G i
    · right; intro σ φ' hφ' hh
      exact absurd (hh ▸ h) (disjoint_left.1 (hcopy i i' hii) · hφ')
    · left; intro σ φ hφ hh; exact absurd (hh ▸ hφ) h

end TParams

end DesignsII
