/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.Bonferroni

/-!
# The thinning probabilities of Lemma `nibble` (algebraic part)

In the proof of Lemma `nibble`, `φ` enters `Φ'` with probability `p^v_φ = ∏_e (1 - v_e q_e)`
given the covering pattern `v ∈ {0,1}^{Q'}`, where `q_e = 1/G^{t_e}_{ψ_e}` (or `zρ` if
`t_e = 0`), and the pattern has probability `(1 ± ε) ∏_e p^{v_e}_e` with
`p^1_e = zρ G^{t_e}_{ψ_e}`, `p^0_e = 1 - p^1_e` (or `p^1_e = 1`, `p^0_e = 0` if `t_e = 0`).

* `thin_identity`, `thin_identity_zero`: `p^0_e + p^1_e (1 - q_e) = 1 - zρ` in both cases;
* `sum_prod_pattern`: `∑_v ∏_e (v_e ? p^1_e (1-q_e) : p^0_e) = ∏_e (p^0_e + p^1_e (1-q_e))`;
* `thin_prob_bounds`: if every pattern probability is `(1 ± ε) ∏_e p^{v_e}_e`, then
  `P(φ ∈ Φ') = (1 ± ε)(1 - zρ)^{|Q'|}`.
-/

@[expose] public section

namespace DesignsII

open Finset

/-- `p^0 + p^1 (1 - q) = 1 - zρ` for `t_e ≠ 0` (`p^1 = zρG`, `q = 1/G`). -/
theorem thin_identity {zρ G : ℝ} (hG : G ≠ 0) :
    (1 - zρ * G) + zρ * G * (1 - 1 / G) = 1 - zρ := by
  field_simp
  ring

/-- `p^0 + p^1 (1 - q) = 1 - zρ` for `t_e = 0` (`p^1 = 1`, `p^0 = 0`, `q = zρ`). -/
theorem thin_identity_zero (zρ : ℝ) : (0 : ℝ) + 1 * (1 - zρ) = 1 - zρ := by ring

/-- Expanding the product over the edges as a sum over covering patterns. -/
theorem sum_prod_pattern {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) :
    ∑ v : ι → Bool, ∏ e, (if v e then a e else b e) = ∏ e, (b e + a e) := by
  have h : ∏ e, (b e + a e) = ∏ e, ∑ x : Bool, (if x then a e else b e) := by
    refine prod_congr rfl fun e _ => ?_
    rw [Fintype.sum_bool]; simp [add_comm]
  rw [h, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The thinning probability.** If each pattern `v` has probability `(1 ± ε) ∏_e p^{v_e}_e`
and `p^0_e + p^1_e (1 - q_e) = c` for every edge, then
`∑_v P(v) ∏_e (1 - v_e q_e) = (1 ± ε) c^{|ι|}`. -/
theorem thin_prob_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] (p0 p1 q : ι → ℝ)
    (hp0 : ∀ e, 0 ≤ p0 e) (hp1 : ∀ e, 0 ≤ p1 e) (hq : ∀ e, q e ≤ 1) {c ε : ℝ}
    (hc : ∀ e, p0 e + p1 e * (1 - q e) = c) (P : (ι → Bool) → ℝ)
    (hP : ∀ v, |P v - ∏ e, (if v e then p1 e else p0 e)| ≤
      ε * ∏ e, (if v e then p1 e else p0 e)) :
    |∑ v : ι → Bool, P v * ∏ e, (if v e then 1 - q e else 1) - c ^ Fintype.card ι| ≤
      ε * c ^ Fintype.card ι := by
  have hexp : ∑ v : ι → Bool, (∏ e, (if v e then p1 e else p0 e)) *
      ∏ e, (if v e then 1 - q e else 1) = c ^ Fintype.card ι := by
    have : ∀ v : ι → Bool, (∏ e, (if v e then p1 e else p0 e)) *
        ∏ e, (if v e then 1 - q e else 1) =
        ∏ e, (if v e then p1 e * (1 - q e) else p0 e) := fun v => by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun e _ => ?_
      split_ifs <;> ring
    simp_rw [this]
    rw [sum_prod_pattern]
    simp_rw [hc]
    rw [prod_const, card_univ]
  have hw : ∀ v : ι → Bool, 0 ≤ ∏ e, (if v e then 1 - q e else 1) := fun v =>
    prod_nonneg fun e _ => by split_ifs <;> linarith [hq e]
  have hm : ∀ v : ι → Bool, 0 ≤ ∏ e, (if v e then p1 e else p0 e) := fun v =>
    prod_nonneg fun e _ => by split_ifs <;> simp [hp0 e, hp1 e]
  rw [← hexp, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
  rw [← sub_mul, abs_mul, abs_of_nonneg (hw v), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hP v) (hw v)

end DesignsII
