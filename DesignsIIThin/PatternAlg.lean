/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.ThinAlg

/-!
# Probability of a covering pattern (algebraic assembly)

Let `m ≈ ∏_{e ∈ S} μ_e` be the probability that the edges `S` (with `v_e = 1`) are covered,
and `R` the edges with `v_e = 0`. From the Bonferroni bounds for complements
(`probG_and_none_ge` / `probG_and_none_le`) and approximations of the all-covered
probabilities, `pattern_prob_approx` gives

  `|P(v) - m ∏_{e ∈ R} (1 - μ_e)| ≤ m (∑_R μ)² + d₀ + |R| d₁ + |R|² d₂`.

* `prod_one_sub_ge`: `∏ (1 - μ) ≥ 1 - ∑ μ` (Weierstrass);
* `prod_one_sub_le`: `∏ (1 - μ) ≤ 1 - ∑ μ + (∑ μ)²/2`;
* `sum_offDiag_mul_le`: `∑_{i ≠ i'} μ_i μ_{i'} ≤ (∑ μ)²`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem prod_one_sub_ge (R : Finset ι) (μ : ι → ℝ) (h0 : ∀ e ∈ R, 0 ≤ μ e)
    (h1 : ∀ e ∈ R, μ e ≤ 1) : 1 - ∑ e ∈ R, μ e ≤ ∏ e ∈ R, (1 - μ e) := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert x R hx ih =>
    rw [sum_insert hx, prod_insert hx]
    have ih' := ih (fun e he => h0 e (mem_insert_of_mem he)) (fun e he => h1 e (mem_insert_of_mem he))
    have hm0 := h0 x (mem_insert_self _ _)
    have hm1 := h1 x (mem_insert_self _ _)
    have hs : 0 ≤ ∑ e ∈ R, μ e := sum_nonneg fun e he => h0 e (mem_insert_of_mem he)
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 - μ x)]

theorem prod_one_sub_le (R : Finset ι) (μ : ι → ℝ) (h0 : ∀ e ∈ R, 0 ≤ μ e)
    (h1 : ∀ e ∈ R, μ e ≤ 1) :
    ∏ e ∈ R, (1 - μ e) ≤ 1 - ∑ e ∈ R, μ e + (∑ e ∈ R, μ e) ^ 2 / 2 := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert x R hx ih =>
    rw [sum_insert hx, prod_insert hx]
    have ih' := ih (fun e he => h0 e (mem_insert_of_mem he)) (fun e he => h1 e (mem_insert_of_mem he))
    have hm0 := h0 x (mem_insert_self _ _)
    have hm1 := h1 x (mem_insert_self _ _)
    have hs : 0 ≤ ∑ e ∈ R, μ e := sum_nonneg fun e he => h0 e (mem_insert_of_mem he)
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 - μ x),
      mul_nonneg hm0 (sq_nonneg (∑ e ∈ R, μ e)), sq_nonneg (μ x)]

theorem sum_offDiag_mul_le (R : Finset ι) (μ : ι → ℝ) (h0 : ∀ e ∈ R, 0 ≤ μ e) :
    ∑ p ∈ R.offDiag, μ p.1 * μ p.2 ≤ (∑ e ∈ R, μ e) ^ 2 := by
  rw [sq, sum_mul_sum, ← sum_product']
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_
  · obtain ⟨h1, h2, -⟩ := mem_offDiag.1 hp
    exact mem_product.2 ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_product.1 hp
    exact mul_nonneg (h0 _ h1) (h0 _ h2)

/-- **Probability of a covering pattern.** -/
theorem pattern_prob_approx (R : Finset ι) (μ : ι → ℝ) (h0 : ∀ e ∈ R, 0 ≤ μ e)
    (h1 : ∀ e ∈ R, μ e ≤ 1) {m Pv PA d₀ d₁ d₂ : ℝ} (hm : 0 ≤ m) (PAB : ι → ℝ)
    (PABB : ι × ι → ℝ)
    (hlow : PA - ∑ e ∈ R, PAB e ≤ Pv)
    (hup : Pv ≤ PA - ∑ e ∈ R, PAB e + (∑ p ∈ R.offDiag, PABB p) / 2)
    (hA : |PA - m| ≤ d₀) (hAB : ∀ e ∈ R, |PAB e - m * μ e| ≤ d₁)
    (hABB : ∀ p ∈ R.offDiag, PABB p ≤ m * μ p.1 * μ p.2 + d₂) (hd₂ : 0 ≤ d₂) :
    |Pv - m * ∏ e ∈ R, (1 - μ e)| ≤
      m * (∑ e ∈ R, μ e) ^ 2 + d₀ + R.card * d₁ + R.card ^ 2 * d₂ := by
  have hs := sum_nonneg h0
  have hge := prod_one_sub_ge R μ h0 h1
  have hle := prod_one_sub_le R μ h0 h1
  have hA' := abs_le.1 hA
  -- `∑ PAB` within `|R| d₁` of `m ∑ μ`
  have hsAB : |∑ e ∈ R, PAB e - m * ∑ e ∈ R, μ e| ≤ R.card * d₁ := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ R, |PAB e - m * μ e| ≤ ∑ _e ∈ R, d₁ := sum_le_sum hAB
      _ = R.card * d₁ := by rw [sum_const, nsmul_eq_mul]
  have hsAB' := abs_le.1 hsAB
  -- the pair term
  have hpair : (∑ p ∈ R.offDiag, PABB p) ≤ m * (∑ e ∈ R, μ e) ^ 2 + R.card ^ 2 * d₂ := by
    calc ∑ p ∈ R.offDiag, PABB p ≤ ∑ p ∈ R.offDiag, (m * (μ p.1 * μ p.2) + d₂) :=
          sum_le_sum fun p hp => by have := hABB p hp; linarith
      _ = m * ∑ p ∈ R.offDiag, μ p.1 * μ p.2 + R.offDiag.card * d₂ := by
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ m * (∑ e ∈ R, μ e) ^ 2 + R.card ^ 2 * d₂ := by
          have hoff : (R.offDiag.card : ℝ) ≤ R.card ^ 2 := by
            rw [offDiag_card]
            have : R.card * R.card - R.card ≤ R.card ^ 2 := by rw [sq]; exact Nat.sub_le _ _
            exact_mod_cast this
          have := mul_le_mul_of_nonneg_left (sum_offDiag_mul_le R μ h0) hm
          nlinarith
  have hcard : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hd₁ : 0 ≤ d₁ ∨ R = ∅ := by
    rcases R.eq_empty_or_nonempty with h | ⟨e, he⟩
    · exact Or.inr h
    · exact Or.inl ((abs_nonneg _).trans (hAB e he))
  have hsq : 0 ≤ m * (∑ e ∈ R, μ e) ^ 2 := mul_nonneg hm (sq_nonneg _)
  rw [abs_le]
  constructor
  · -- lower side
    have := mul_le_mul_of_nonneg_left hle hm
    nlinarith
  · -- upper side
    have := mul_le_mul_of_nonneg_left hge hm
    nlinarith

end DesignsII
