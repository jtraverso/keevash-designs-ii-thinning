/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.TuplePairs

/-!
# Tuples with a conflicting pair of coordinates

`sum_tuples_bad_le`: for weights `g_l ≥ 0` on families `C_l` and a symmetric "conflict" relation,
the weight `∑ ∏_l g_l(t_l)` of the tuples having two conflicting coordinates is at most

  `∑_{i ≠ i'} (∑_{x ∈ C_i, y ∈ C_{i'}, conflict x y} g_i(x) g_{i'}(y)) ∏_{l ∉ {i, i'}} ∑_{C_l} g_l`.

In `probG_cover_all_ge` the main term is over edge-disjoint tuples; the missing tuples are those
with two copies sharing an edge, of total weight `O(n^{q-r-1})`-type by `card_image_superset_le`.

* `sum_tuples_fix2`: fixing coordinates `i ≠ i'` factors the sum.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Fixing two coordinates.** -/
theorem sum_tuples_fix2 {m : ℕ} (C : Fin m → Finset α) (g : Fin m → α → ℝ) {i i' : Fin m}
    (hii : i ≠ i') (x y : α) :
    ∑ t ∈ Fintype.piFinset C, (if t i = x ∧ t i' = y then ∏ l, g l (t l) else 0) =
      (if x ∈ C i then g i x else 0) * (if y ∈ C i' then g i' y else 0) *
        ∏ l ∈ univ.erase i |>.erase i', ∑ z ∈ C l, g l z := by
  set h : Fin m → α → ℝ := fun l z =>
    if l = i then (if z = x then g l z else 0) else if l = i' then (if z = y then g l z else 0)
      else g l z
  have hpt : ∀ t : Fin m → α, (if t i = x ∧ t i' = y then ∏ l, g l (t l) else 0) =
      ∏ l, h l (t l) := by
    intro t
    by_cases hxy : t i = x ∧ t i' = y
    · rw [if_pos hxy]
      refine prod_congr rfl fun l _ => ?_
      simp only [h]
      by_cases hl : l = i
      · subst hl; simp [hxy.1]
      · by_cases hl' : l = i'
        · subst hl'; simp [hl, hxy.2]
        · simp [hl, hl']
    · rw [if_neg hxy]
      symm
      by_cases hx : t i = x
      · have hy : t i' ≠ y := fun hy => hxy ⟨hx, hy⟩
        exact prod_eq_zero (mem_univ i') (by simp [h, hii.symm, hy])
      · exact prod_eq_zero (mem_univ i) (by simp [h, hx])
  simp_rw [hpt]
  rw [← prod_univ_sum]
  rw [← mul_prod_erase univ _ (mem_univ i),
    ← mul_prod_erase (univ.erase i) _ (mem_erase.2 ⟨hii.symm, mem_univ i'⟩)]
  have hi : ∑ z ∈ C i, h i z = if x ∈ C i then g i x else 0 := by
    simp only [h, if_true]
    rw [sum_ite_eq']
  have hi' : ∑ z ∈ C i', h i' z = if y ∈ C i' then g i' y else 0 := by
    simp only [h, if_neg hii.symm, if_true]
    rw [sum_ite_eq']
  rw [hi, hi', ← mul_assoc]
  congr 1
  refine prod_congr rfl fun l hl => ?_
  have h1 : l ≠ i' := (mem_erase.1 hl).1
  have h2 : l ≠ i := (mem_erase.1 (mem_erase.1 hl).2).1
  simp only [h, if_neg h1, if_neg h2]

/-- **Weight of the tuples with a conflicting pair.** -/
theorem sum_tuples_bad_le {m : ℕ} (C : Fin m → Finset α) (g : Fin m → α → ℝ)
    (hg : ∀ l, ∀ z ∈ C l, 0 ≤ g l z) (conf : α → α → Prop) [DecidableRel conf] :
    ∑ t ∈ (Fintype.piFinset C).filter (fun t => ∃ i i', i ≠ i' ∧ conf (t i) (t i')),
        ∏ l, g l (t l) ≤
      ∑ p ∈ (univ : Finset (Fin m)).offDiag,
        (∑ x ∈ C p.1, ∑ y ∈ C p.2, if conf x y then g p.1 x * g p.2 y else 0) *
          ∏ l ∈ univ.erase p.1 |>.erase p.2, ∑ z ∈ C l, g l z := by
  have hnn : ∀ t ∈ Fintype.piFinset C, 0 ≤ ∏ l, g l (t l) := fun t ht =>
    prod_nonneg fun l _ => hg l _ (Fintype.mem_piFinset.1 ht l)
  -- union bound over the conflicting pair
  calc _ ≤ ∑ p ∈ (univ : Finset (Fin m)).offDiag, ∑ t ∈ Fintype.piFinset C,
        (if conf (t p.1) (t p.2) then ∏ l, g l (t l) else 0) := by
        rw [sum_comm]
        rw [sum_filter]
        refine sum_le_sum fun t ht => ?_
        split_ifs with hb
        · obtain ⟨i, i', hne, hc⟩ := hb
          have hmem : (i, i') ∈ (univ : Finset (Fin m)).offDiag := by simp [hne]
          refine le_trans ?_ (single_le_sum (f := fun p : Fin m × Fin m =>
            if conf (t p.1) (t p.2) then ∏ l, g l (t l) else 0)
            (fun p _ => by split_ifs <;> [exact hnn t ht; exact le_rfl]) hmem)
          simp [hc]
        · exact sum_nonneg fun p _ => by split_ifs <;> [exact hnn t ht; exact le_rfl]
    _ = _ := by
        refine sum_congr rfl fun p hp => ?_
        have hne : p.1 ≠ p.2 := (mem_offDiag.1 hp).2.2
        -- decompose by the values at the two coordinates
        have hdec : ∀ t ∈ Fintype.piFinset C,
            (if conf (t p.1) (t p.2) then ∏ l, g l (t l) else 0) =
            ∑ x ∈ C p.1, ∑ y ∈ C p.2, if conf x y then
              (if t p.1 = x ∧ t p.2 = y then ∏ l, g l (t l) else 0) else 0 := by
          intro t ht
          have h1 := Fintype.mem_piFinset.1 ht p.1
          have h2 := Fintype.mem_piFinset.1 ht p.2
          rw [sum_eq_single_of_mem (t p.1) h1, sum_eq_single_of_mem (t p.2) h2]
          · simp
          · intro y _ hy; simp [Ne.symm hy]
          · intro x _ hx
            refine sum_eq_zero fun y _ => ?_
            simp [Ne.symm hx]
        rw [sum_congr rfl hdec, sum_comm]
        rw [sum_mul]
        refine sum_congr rfl fun x hx => ?_
        rw [sum_comm, sum_mul]
        refine sum_congr rfl fun y hy => ?_
        split_ifs with hc
        · rw [sum_tuples_fix2 C g hne x y, if_pos hx, if_pos hy]
        · simp

end DesignsII
