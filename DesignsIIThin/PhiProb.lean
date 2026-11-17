/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PatternCover
public import DesignsIIThin.ThinMix

/-!
# The probability that a copy enters the thinned family `Φ'`

`probG_inPhi_approx`: let the edges of `φ` (other than the conditioned one) carry families `C_i`
of copies of pairwise distinct colours, with covering masses `μ_i ≤ 1`, and thinning parameters
`q_i ∈ [0,1]` with `μ_i q_i = t` for all `i` (in the paper `q_e = 1/G` and `μ_e ≈ zρG`, so
`t = zρ`). If the coin of pattern `v` has probability `∏_i (1 - v_i q_i)`, then

  `|P(φ ∈ Φ') - (1 - t)^m| ≤ 2^m ((∑ μ)² + (m + 1) D)`,

`D = max_T Err(T)` the largest joint-covering error over subsets of the families.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

variable {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
  (j : Fin m → Fin P.z) (a₀ : Fin P.NA) (kk : (Fin P.q → Fin P.n) → ℕ)
  (C : Fin m → Finset (Fin P.q → Fin P.n))
  (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c))

theorem errSet_le_errMax (T : Finset (Fin m)) :
    errSet M κ j a₀ kk C S v T ≤ errMax M κ j a₀ kk C S v :=
  le_sup' (fun T => errSet M κ j a₀ kk C S v T) (mem_univ T)

open Classical in
/-- **The probability that `φ` enters `Φ'`.** -/
theorem probG_inPhi_approx {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {b : ι' → ℕ}
    (hj : Function.Injective j) (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ)
    (hμ1 : ∀ i, mu1 M κ j a₀ kk C S v i ≤ 1) (q : Fin m → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) {t : ℝ} (hμq : ∀ i, mu1 M κ j a₀ kk C S v i * q i = t)
    (Cn : (Fin m → Bool) → (∀ c : ι', Perm (Fin (b c))) → Prop)
    (hθ : ∀ w, probG (a := b) (Cn w) = ∏ i, (if w i then 1 - q i else 1)) :
    |probG (a := Sum.elim (fun c => P.size c - (S c).card) b)
        (fun ω => ∃ w ∈ (univ : Finset (Fin m → Bool)),
          (∀ i, (∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v (leftPart ω))) ↔ w i = true) ∧
            Cn w (rightPart ω)) - (1 - t) ^ m| ≤
      2 ^ m * ((∑ i, mu1 M κ j a₀ kk C S v i) ^ 2 + (m + 1) * errMax M κ j a₀ kk C S v) := by
  set μ := mu1 M κ j a₀ kk C S v
  set D := errMax M κ j a₀ kk C S v
  set cov : Fin m → (∀ c : P.Coord, Perm (Fin (P.size c - (S c).card))) → Prop :=
    fun i τ => ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)
  set E : (Fin m → Bool) → (∀ c : P.Coord, Perm (Fin (P.size c - (S c).card))) → Prop :=
    fun w τ => ∀ i, cov i τ ↔ w i = true
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => mu1_nonneg M κ j a₀ kk C S v i
  have hD0 : 0 ≤ D := by
    have h := probG_cover_set_le M κ j a₀ kk C S v hj hC ∅
    have h2 := probG_cover_set_ge M κ j a₀ kk C S v hj hC ∅
    exact (by linarith : (0:ℝ) ≤ errSet M κ j a₀ kk C S v ∅).trans (errSet_le_errMax _ _ _ _ _ _ _ _ _)
  -- the error of each pattern
  set err : (Fin m → Bool) → ℝ := fun _ => (∑ i, μ i) ^ 2 + (m + 1) * D
  have hE : ∀ w, |probG (a := fun c => P.size c - (S c).card) (E w) -
      ∏ i, (if w i then μ i else 1 - μ i)| ≤ err w := by
    intro w
    set T := univ.filter fun i => w i = true
    have hev : E w = fun τ => (∀ i ∈ T, cov i τ) ∧ ¬ ∃ i ∈ univ \ T, cov i τ := by
      funext τ
      apply propext
      constructor
      · intro h
        refine ⟨fun i hi => (h i).2 (mem_filter.1 hi).2, ?_⟩
        rintro ⟨i, hi, hc⟩
        have := (h i).1 hc
        exact (mem_sdiff.1 hi).2 (mem_filter.2 ⟨mem_univ _, this⟩)
      · rintro ⟨h1, h2⟩ i
        constructor
        · intro hc
          by_contra hw
          exact h2 ⟨i, mem_sdiff.2 ⟨mem_univ _, fun hi => hw (mem_filter.1 hi).2⟩, hc⟩
        · intro hw; exact h1 i (mem_filter.2 ⟨mem_univ _, hw⟩)
    have hprod : ∏ i, (if w i then μ i else 1 - μ i) =
        (∏ i ∈ T, μ i) * ∏ e ∈ univ \ T, (1 - μ e) := by
      rw [prod_ite, filter_not]
    have h := probG_pattern_approx M κ j a₀ kk C S v hj hC T (d₁ := D)
      (fun e _ => errSet_le_errMax _ _ _ _ _ _ _ _ _) (fun e _ => hμ1 e)
    rw [hev, hprod]
    refine h.trans ?_
    have hT1 : ∏ i ∈ T, μ i ≤ 1 := prod_le_one₀ (fun i _ => hμ0 i) (fun i _ => hμ1 i)
    have hsR : ∑ e ∈ univ \ T, μ e ≤ ∑ i, μ i :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hμ0 i
    have hsR0 : 0 ≤ ∑ e ∈ univ \ T, μ e := sum_nonneg fun i _ => hμ0 i
    have hRm : ((univ \ T).card : ℝ) ≤ m := by
      have := card_le_univ (univ \ T); rw [Fintype.card_fin] at this; exact_mod_cast this
    have hET : errSet M κ j a₀ kk C S v T ≤ D := errSet_le_errMax _ _ _ _ _ _ _ _ _
    have hsq : (∑ e ∈ univ \ T, μ e) ^ 2 ≤ (∑ i, μ i) ^ 2 := pow_le_pow_left₀ hsR0 hsR 2
    have hprodnn : 0 ≤ ∏ i ∈ T, μ i := prod_nonneg fun i _ => hμ0 i
    simp only [err]
    nlinarith [mul_le_mul hT1 hsq (sq_nonneg _) zero_le_one]
  have hdisj : ∀ w w', w ≠ w' → ∀ ω, E w ω → E w' ω → False := by
    intro w w' hne ω h h'
    apply hne
    funext i
    have := (h i).symm.trans (h' i)
    cases hw : w i <;> cases hw' : w' i <;> simp_all
  have hc : ∀ i, (1 - μ i) + μ i * (1 - q i) = 1 - t := fun i => by
    have := hμq i; linarith
  have := thin_mix_approx E Cn hdisj (fun i => 1 - μ i) μ q hq0 hq1 hc hθ err hE
  refine this.trans (le_of_eq ?_)
  simp only [err, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

end TParams

end DesignsII
