/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Joint
public import DesignsIIThin.ThinDefs

/-!
# Independent extension of the template space

The thinning of Lemma `nibble` uses coins independent of the template. We model them as further
independent uniform permutations: the joint space has coordinates `ι ⊕ ι'`.

* `probG_sum_indep`: an event of the left coordinates and an event of the right coordinates are
  independent: `P(A ∘ left ∧ B ∘ right) = P(A) P(B)`;
* `probG_sum_left`: the marginal of the left coordinates is the old space.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {a : ι → ℕ} {b : ι' → ℕ}

open Classical in
/-- **Independence of the two parts.** -/
theorem probG_sum_indep (A : (∀ c : ι, Perm (Fin (a c))) → Prop)
    (B : (∀ c : ι', Perm (Fin (b c))) → Prop) :
    probG (a := Sum.elim a b) (fun ω => A (leftPart ω) ∧ B (rightPart ω)) =
      probG (a := a) A * probG (a := b) B := by
  unfold probG
  set e := Equiv.sumPiEquivProdPi (fun c : ι ⊕ ι' => Perm (Fin (Sum.elim a b c)))
  have hcard : (univ.filter fun ω : (∀ c : ι ⊕ ι', Perm (Fin (Sum.elim a b c))) =>
      A (leftPart ω) ∧ B (rightPart ω)).card = (univ.filter A).card * (univ.filter B).card := by
    rw [← card_product]
    refine card_bij (fun ω _ => (leftPart ω, rightPart ω)) ?_ ?_ ?_
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp only [mem_product, mem_filter, mem_univ, true_and]
      exact hω
    · intro ω _ ω' _ h
      simp only [Prod.mk.injEq] at h
      funext c
      rcases c with c | c
      · exact congrFun h.1 c
      · exact congrFun h.2 c
    · rintro ⟨x, y⟩ hxy
      simp only [mem_product, mem_filter, mem_univ, true_and] at hxy
      refine ⟨fun c => match c with | Sum.inl c => x c | Sum.inr c => y c, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      exact hxy
  rw [Fintype.prod_sum_type, div_mul_div_comm, ← Nat.cast_mul, ← hcard]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr! 2
  exact Finset.card_bij (fun x _ => x) (fun x hx => by simpa using hx) (fun _ _ _ _ h => h)
    (fun y hy => ⟨y, by simpa using hy, rfl⟩)

open Classical in
/-- **The marginal of the left coordinates.** -/
theorem probG_sum_left (A : (∀ c : ι, Perm (Fin (a c))) → Prop) :
    probG (a := Sum.elim a b) (fun ω => A (leftPart ω)) = probG (a := a) A := by
  have h := probG_sum_indep (a := a) (b := b) A (fun _ => True)
  have h1 : probG (a := b) (fun _ => True) = 1 := by
    unfold probG
    rw [filter_true, card_univ, Fintype.card_pi]
    push_cast
    simp only [Fintype.card_perm, Fintype.card_fin]
    exact div_self (prod_ne_zero_iff.2 fun c _ => by exact_mod_cast (Nat.factorial_pos _).ne')
  rw [h1, mul_one] at h
  simpa only [and_true] using h

open Classical in
/-- **Mixture over disjoint patterns.** If the template events `E v` are pairwise disjoint, the
probability that some pattern `v` occurs and its coin event `Cn v` holds is
`∑_v P(E v) P(Cn v)` (the thinning probability of Lemma `nibble`). -/
theorem probG_mix {κ : Type*} (S : Finset κ) (E : κ → (∀ c : ι, Perm (Fin (a c))) → Prop)
    (Cn : κ → (∀ c : ι', Perm (Fin (b c))) → Prop)
    (hdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → ∀ ω, E v ω → E v' ω → False) :
    probG (a := Sum.elim a b) (fun ω => ∃ v ∈ S, E v (leftPart ω) ∧ Cn v (rightPart ω)) =
      ∑ v ∈ S, probG (a := a) (E v) * probG (a := b) (Cn v) := by
  rw [probG_exists_disjoint S (fun v ω => E v (leftPart ω) ∧ Cn v (rightPart ω))
    (fun v hv v' hv' hne ω h h' => hdisj v hv v' hv' hne _ h.1 h'.1)]
  exact sum_congr rfl fun v _ => probG_sum_indep (E v) (Cn v)

end DesignsII
