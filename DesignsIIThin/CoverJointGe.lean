/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.GroupJoint

/-!
# Joint covering of several edges with distinct colours (lower bound)

* `probG_tuple_pair_le`: for two tuples `t, t'` of copies (component `i` of colour `j_i`),
  `P(both tuples pass) ≤ ∏_i P(t_i and t'_i pass)` (groups `{t_i, t'_i}` are independent across
  colours, or the event is empty);
* `probG_cover_all_ge`: for a set `T` of edge-disjoint tuples with `t_i ∈ C_i`,

  `P(every family has a passing copy) ≥ ∑_{t ∈ T} ∏_i P(t_i) - ½ ∑_{t ≠ t'} ∏_i P(t_i, t'_i)`.

With `probG_cover_all_le` this is the two-sided joint covering estimate (all `v_e = 1`) of the
"repeated application of Lemma `e|E`" in Lemma `nibble`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Two tuples both pass.** -/
theorem probG_tuple_pair_le {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (hj : Function.Injective j) (a₀ : Fin P.NA)
    (kk : (Fin P.q → Fin P.n) → ℕ) (t t' : Fin m → Fin P.q → Fin P.n)
    (ht : ∀ i, Function.Injective (t i)) (ht' : ∀ i, Function.Injective (t' i))
    (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c)) :
    probG (a := fun c => P.size c - (S c).card) (fun τ =>
        (∀ i, CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) ∧
          ∀ i, CopyOK M κ (j i) a₀ (kk (t' i)) (t' i) (liftPi S v τ)) ≤
      ∏ i, probG (a := fun c => P.size c - (S c).card) (fun τ =>
        CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ) ∧
          CopyOK M κ (j i) a₀ (kk (t' i)) (t' i) (liftPi S v τ)) := by
  set G : Fin m → Finset (Fin P.q → Fin P.n) := fun i => {t i, t' i}
  have hinj : ∀ i, ∀ φ ∈ G i, Function.Injective φ := by
    intro i φ hφ
    rcases mem_insert.1 hφ with rfl | h
    · exact ht i
    · rw [mem_singleton.1 h]; exact ht' i
  have hev : ∀ τ, ((∀ i, CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) ∧
      ∀ i, CopyOK M κ (j i) a₀ (kk (t' i)) (t' i) (liftPi S v τ)) ↔
      ∀ i, ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ) := by
    intro τ
    constructor
    · rintro ⟨h1, h2⟩ i φ hφ
      rcases mem_insert.1 hφ with rfl | h
      · exact h1 i
      · rw [mem_singleton.1 h]; exact h2 i
    · intro h
      exact ⟨fun i => h i (t i) (mem_insert_self _ _),
        fun i => h i (t' i) (mem_insert_of_mem (mem_singleton_self _))⟩
  have hfac : ∀ i, probG (a := fun c => P.size c - (S c).card) (fun τ =>
      ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) =
      probG (a := fun c => P.size c - (S c).card) (fun τ =>
        CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ) ∧
          CopyOK M κ (j i) a₀ (kk (t' i)) (t' i) (liftPi S v τ)) := by
    intro i
    congr 1
    funext τ
    apply propext
    constructor
    · intro h
      exact ⟨h (t i) (mem_insert_self _ _), h (t' i) (mem_insert_of_mem (mem_singleton_self _))⟩
    · rintro ⟨h1, h2⟩ φ hφ
      rcases mem_insert.1 hφ with rfl | h
      · exact h1
      · rw [mem_singleton.1 h]; exact h2
  rw [show (fun τ => (∀ i, CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) ∧
      ∀ i, CopyOK M κ (j i) a₀ (kk (t' i)) (t' i) (liftPi S v τ)) =
      fun τ => ∀ i, ∀ φ ∈ G i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ) from
    funext fun τ => propext (hev τ)]
  simp_rw [← hfac]
  by_cases hgood : ∀ i i', i ≠ i' → ∀ φ ∈ G i, ∀ φ' ∈ G i', Disjoint (edges φ) (edges φ')
  · have hcopy : ∀ i i', i ≠ i' → Disjoint (G i) (G i') := by
      intro i i' hne
      rw [disjoint_left]
      intro φ h1 h2
      obtain ⟨g, hg⟩ := edges_nonempty (P := P) (hinj i φ h1)
      exact disjoint_left.1 (hgood i i' hne φ h1 φ h2) hg hg
    exact le_of_eq (probG_group_joint_cond S v M κ j hj a₀ kk G hcopy hgood)
  · push_neg at hgood
    obtain ⟨i, i', hne, φ, hφ, φ', hφ', hnd⟩ := hgood
    obtain ⟨g, hg1, hg2⟩ := not_disjoint_iff.1 hnd
    refine le_trans (probG_mono fun τ h => ?_) (le_of_eq_of_le probG_false
      (prod_nonneg fun i _ => probG_nonneg _))
    exact hne (hj ((tval_of_copyOK (h i φ hφ) hg1).symm.trans (tval_of_copyOK (h i' φ' hφ') hg2)))

open Classical in
/-- **Joint covering, lower bound.** -/
theorem probG_cover_all_ge {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (hj : Function.Injective j) (a₀ : Fin P.NA)
    (kk : (Fin P.q → Fin P.n) → ℕ) (C : Fin m → Finset (Fin P.q → Fin P.n))
    (T : Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ t ∈ T, (∀ i, t i ∈ C i ∧ Function.Injective (t i)) ∧ Function.Injective t ∧
      ∀ i i', i ≠ i' → Disjoint (edges (t i)) (edges (t i')))
    (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c)) :
    ∑ t ∈ T, ∏ i, probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) -
      (∑ p ∈ T.offDiag, ∏ i, probG (a := fun c => P.size c - (S c).card) (fun τ =>
        CopyOK M κ (j i) a₀ (kk (p.1 i)) (p.1 i) (liftPi S v τ) ∧
          CopyOK M κ (j i) a₀ (kk (p.2 i)) (p.2 i) (liftPi S v τ))) / 2 ≤
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) := by
  set A : (Fin m → Fin P.q → Fin P.n) → (∀ c : P.Coord, Perm (Fin (P.size c - (S c).card))) →
      Prop := fun t τ => ∀ i, CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)
  have hb := probG_exists_ge_bonferroni T A
  have hsing : ∀ t ∈ T, probG (a := fun c => P.size c - (S c).card) (A t) =
      ∏ i, probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) a₀ (kk (t i)) (t i) (liftPi S v τ)) := by
    intro t ht
    obtain ⟨-, hinj, hdisj⟩ := hT t ht
    exact probG_copyOK_joint_cond S v M κ j (fun _ => a₀) (fun i => kk (t i)) t hj hinj hdisj
  have hpair : ∀ p ∈ T.offDiag, probG (a := fun c => P.size c - (S c).card)
      (fun τ => A p.1 τ ∧ A p.2 τ) ≤ ∏ i, probG (a := fun c => P.size c - (S c).card) (fun τ =>
        CopyOK M κ (j i) a₀ (kk (p.1 i)) (p.1 i) (liftPi S v τ) ∧
          CopyOK M κ (j i) a₀ (kk (p.2 i)) (p.2 i) (liftPi S v τ)) := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := mem_offDiag.1 hp
    exact probG_tuple_pair_le M κ j hj a₀ kk p.1 p.2 (fun i => ((hT _ h1).1 i).2)
      (fun i => ((hT _ h2).1 i).2) S v
  have hmono : probG (a := fun c => P.size c - (S c).card) (fun τ => ∃ t ∈ T, A t τ) ≤
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) :=
    probG_mono fun τ ⟨t, ht, h⟩ i => ⟨t i, ((hT t ht).1 i).1, h i⟩
  rw [sum_congr rfl hsing] at hb
  have hps := sum_le_sum hpair
  linarith

end TParams

end DesignsII
