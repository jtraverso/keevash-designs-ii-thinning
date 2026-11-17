/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.SumSpace
public import DesignsIIThin.ThinAlg

/-!
# The thinning probability (mixture form)

`thin_mix_approx`: in the joint space (template ⊕ thinning coins), if the covering patterns
`E v` (`v : Fin m → Bool`) are disjoint template events with
`|P(E v) - ∏_i p^{v_i}_i| ≤ err v`, and the coin event of pattern `v` has probability
`θ_v = ∏_i (1 - v_i q_i)`, then

  `|P(∃ v, E v ∧ coin_v) - c^m| ≤ ∑_v err v`,   `c = p⁰_i + p¹_i (1 - q_i)` for all `i`.

In Lemma `nibble` `c = 1 - zρ`, so `P(φ ∈ Φ') = (1 - zρ)^{Q-1} ± ∑_v err v`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {a : ι → ℕ} {b : ι' → ℕ}

open Classical in
/-- **The thinning probability.** -/
theorem thin_mix_approx {m : ℕ} (E : (Fin m → Bool) → (∀ c : ι, Perm (Fin (a c))) → Prop)
    (Cn : (Fin m → Bool) → (∀ c : ι', Perm (Fin (b c))) → Prop)
    (hdisj : ∀ v v', v ≠ v' → ∀ ω, E v ω → E v' ω → False)
    (p0 p1 q : Fin m → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) {c : ℝ}
    (hc : ∀ i, p0 i + p1 i * (1 - q i) = c)
    (hθ : ∀ v, probG (a := b) (Cn v) = ∏ i, (if v i then 1 - q i else 1))
    (err : (Fin m → Bool) → ℝ)
    (hE : ∀ v, |probG (a := a) (E v) - ∏ i, (if v i then p1 i else p0 i)| ≤ err v) :
    |probG (a := Sum.elim a b)
        (fun ω => ∃ v ∈ (univ : Finset (Fin m → Bool)), E v (leftPart ω) ∧ Cn v (rightPart ω)) -
      c ^ m| ≤ ∑ v, err v := by
  rw [probG_mix univ E Cn (fun v _ v' _ hne ω h h' => hdisj v v' hne ω h h')]
  have hexp : ∑ v : Fin m → Bool, (∏ i, (if v i then p1 i else p0 i)) *
      ∏ i, (if v i then 1 - q i else 1) = c ^ m := by
    have : ∀ v : Fin m → Bool, (∏ i, (if v i then p1 i else p0 i)) *
        ∏ i, (if v i then 1 - q i else 1) =
        ∏ i, (if v i then p1 i * (1 - q i) else p0 i) := fun v => by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      split_ifs <;> ring
    simp_rw [this]
    rw [sum_prod_pattern]
    simp_rw [hc]
    rw [prod_const, card_univ, Fintype.card_fin]
  have hθ01 : ∀ v : Fin m → Bool, 0 ≤ ∏ i, (if v i then 1 - q i else 1) ∧
      ∏ i, (if v i then 1 - q i else 1) ≤ 1 := by
    intro v
    constructor
    · exact prod_nonneg fun i _ => by split_ifs <;> linarith [hq1 i]
    · exact prod_le_one₀ (fun i _ => by split_ifs <;> linarith [hq1 i])
        (fun i _ => by split_ifs <;> linarith [hq0 i])
  simp_rw [hθ]
  rw [← hexp, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
  rw [← sub_mul, abs_mul, abs_of_nonneg (hθ01 v).1]
  calc |probG (a := a) (E v) - ∏ i, (if v i then p1 i else p0 i)| *
        ∏ i, (if v i then 1 - q i else 1) ≤ err v * 1 :=
        mul_le_mul (hE v) (hθ01 v).2 (hθ01 v).1 ((abs_nonneg _).trans (hE v))
    _ = err v := mul_one _

end DesignsII
