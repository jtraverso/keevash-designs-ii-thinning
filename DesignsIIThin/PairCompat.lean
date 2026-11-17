/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PairPass

/-!
# Joint compatibility with `f_j` of two copies

`card_cond_compat_pair_le`: in the conditioned space, the number of `τ` making both copies (at
positions `w`, `w'`) compatible with `M` is at most `#Y(w) · #Y(w') · (N - |S| - |W ∪ W'|)!`,
where `W, W'` are the new positions of the two copies. Hence the joint colour factor is about
`#Y(w) #Y(w') N^{-|W ∪ W'|}`: a shared new vertex is paid for once.

* `card_perm_agree_le`: permutations with prescribed values at the positions `pos x`
  (`x ∈ α`) number at most `(m - |pos(α)|)!`.
-/

@[expose] public section

namespace DesignsII

open Finset Matrix Equiv

/-- **Prescribed values on a set of positions.** -/
theorem card_perm_agree_le {α : Type*} [Fintype α] {m : ℕ} (pos val : α → Fin m) :
    (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (pos x) = val x).card ≤
      (m - (univ.image pos).card).factorial := by
  classical
  by_cases hne : (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (pos x) = val x).Nonempty
  · obtain ⟨σ₀, hσ₀⟩ := hne
    have hσ₀' := (mem_filter.1 hσ₀).2
    set T := univ.image pos
    have hset : (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (pos x) = val x) =
        univ.filter fun σ : Perm (Fin m) => ∀ t : T, σ t = σ₀ t := by
      ext σ
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro h ⟨t, ht⟩
        obtain ⟨x, -, rfl⟩ := mem_image.1 ht
        rw [h x, hσ₀' x]
      · intro h x
        rw [← hσ₀' x]
        exact h ⟨pos x, mem_image_of_mem _ (mem_univ x)⟩
    rw [hset]
    have := card_perm_fix' (Function.Embedding.subtype (· ∈ T))
      ((Function.Embedding.subtype (· ∈ T)).trans σ₀.toEmbedding)
    rw [Fintype.card_coe] at this
    rw [← this]
    apply le_of_eq
    congr 1
  · rw [not_nonempty_iff_eq_empty.1 hne, card_empty]
    exact Nat.zero_le _

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r : ℕ}

section Cond

variable {N : ℕ} (S : Finset (Fin N)) (v : S ↪ Fin N) (κ : Fin N ≃ K)
  (M : Matrix (Fin q) (Fin r) F)

/-- A compatible `τ` agrees at the new positions with the values given by some `y ∈ Y'`. -/
theorem exists_Yc_of_compat (w : Fin q ↪ Fin N) {τ : Perm (Fin (N - S.card))}
    (h : ∃ y, ∀ i, κ (liftC S v τ (w i)) = mvec M y i) :
    ∃ y : Yc S v κ M w, ∀ i, τ (newPos S w i) = newVal S v κ M w y i := by
  classical
  obtain ⟨y, hy⟩ := h
  have hYc : y ∈ Yc S v κ M w := by
    refine mem_filter.2 ⟨mem_univ _, fun i hi => ?_, fun i i' h => ?_, fun i hi => ?_⟩
    · rw [← hy i, liftC_apply_mem S v τ hi]; simp [cval, hi]
    · rw [← hy i, ← hy i'] at h
      exact w.injective ((liftC S v τ).injective (κ.injective h))
    · rw [← hy i, liftC_apply_not_mem S v τ hi]
      intro hf
      obtain ⟨x, hx, hxe⟩ := mem_image.1 hf
      exact eVal_not_mem_vImg S v _ (κ.injective hxe ▸ hx)
  refine ⟨⟨y, hYc⟩, fun i => ?_⟩
  have h1 := hy i
  rw [liftC_apply_not_mem S v τ i.2] at h1
  show τ ((ePos S).symm ⟨w i, mem_compl.2 i.2⟩) = (eVal S v).symm ⟨κ.symm (mvec M y i), _⟩
  symm
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext (by show κ.symm (mvec M y i) = _; rw [← h1, κ.symm_apply_apply])

/-- The new positions of two copies. -/
noncomputable def newSet2 (w w' : Fin q ↪ Fin N) : Finset (Fin (N - S.card)) :=
  univ.image (Sum.elim (newPos S w) (newPos S w'))

/-- **Joint compatibility count.** -/
theorem card_cond_compat_pair_le (w w' : Fin q ↪ Fin N) :
    (univ.filter fun τ : Perm (Fin (N - S.card)) =>
      (∃ y, ∀ i, κ (liftC S v τ (w i)) = mvec M y i) ∧
        ∃ y, ∀ i, κ (liftC S v τ (w' i)) = mvec M y i).card ≤
      (Yc S v κ M w).card * (Yc S v κ M w').card *
        (N - S.card - (newSet2 S w w').card).factorial := by
  classical
  have hsub : (univ.filter fun τ : Perm (Fin (N - S.card)) =>
      (∃ y, ∀ i, κ (liftC S v τ (w i)) = mvec M y i) ∧
        ∃ y, ∀ i, κ (liftC S v τ (w' i)) = mvec M y i) ⊆
      ((Yc S v κ M w).attach ×ˢ (Yc S v κ M w').attach).biUnion fun yy =>
        univ.filter fun τ : Perm (Fin (N - S.card)) =>
          ∀ x, τ (Sum.elim (newPos S w) (newPos S w') x) =
            Sum.elim (newVal S v κ M w yy.1) (newVal S v κ M w' yy.2) x := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := (mem_filter.1 hτ).2
    obtain ⟨y, hy⟩ := exists_Yc_of_compat S v κ M w h1
    obtain ⟨y', hy'⟩ := exists_Yc_of_compat S v κ M w' h2
    refine mem_biUnion.2 ⟨(y, y'), mem_product.2 ⟨mem_attach _ _, mem_attach _ _⟩, ?_⟩
    refine mem_filter.2 ⟨mem_univ _, fun x => ?_⟩
    rcases x with i | i
    · exact hy i
    · exact hy' i
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine (sum_le_sum fun yy _ => card_perm_agree_le _ _).trans (le_of_eq ?_)
  rw [sum_const, card_product, card_attach, card_attach, smul_eq_mul]
  rfl

theorem ePos_newPos (w : Fin q ↪ Fin N) (i : {i // w i ∉ S}) :
    ((ePos S (newPos S w i)) : Fin N) = w i := by
  show ((ePos S ((ePos S).symm ⟨w i, mem_compl.2 i.2⟩)) : Fin N) = w i
  rw [OrderIso.apply_symm_apply]

/-- `|W ∪ W'|` in terms of the images: the new positions of the two copies are the positions of
`Im w ∪ Im w'` outside `S`. -/
theorem card_newSet2 (w w' : Fin q ↪ Fin N) :
    (newSet2 S w w').card = ((univ.image w ∪ univ.image w') \ S).card := by
  classical
  set g : Fin (N - S.card) → Fin N := fun p => (ePos S p : Fin N)
  have hg : Function.Injective g := fun p p' h =>
    (ePos S).injective (Subtype.ext h)
  have hout : ∀ p, g p ∉ S := fun p => mem_compl.1 (ePos S p).2
  rw [← card_image_of_injective _ hg]
  congr 1
  ext x
  simp only [newSet2, mem_image, mem_univ, true_and, mem_sdiff, mem_union]
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
    refine ⟨?_, hout _⟩
    rcases i with i | i
    · exact Or.inl ⟨i, (ePos_newPos S w i).symm⟩
    · exact Or.inr ⟨i, (ePos_newPos S w' i).symm⟩
  · rintro ⟨h | h, hx⟩
    · obtain ⟨i, rfl⟩ := h
      exact ⟨newPos S w ⟨i, hx⟩, ⟨Sum.inl ⟨i, hx⟩, rfl⟩, ePos_newPos S w ⟨i, hx⟩⟩
    · obtain ⟨i, rfl⟩ := h
      exact ⟨newPos S w' ⟨i, hx⟩, ⟨Sum.inr ⟨i, hx⟩, rfl⟩, ePos_newPos S w' ⟨i, hx⟩⟩

end Cond

end DesignsII
