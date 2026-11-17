/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.CoverAllGe
public import DesignsIIThin.Complement

/-!
# Probability of a covering pattern

For families `C_i` (`i < m`) of copies of pairwise distinct colours, the covering pattern
`(S, R = Sᶜ)` (the families in `S` covered, those in `R` not) has probability

  `|P - ∏_S μ ∏_R (1 - μ)| ≤ ∏_S μ (∑_R μ)² + Err(S) + |R| d₁`,

where `Err(S)` is the explicit error of the joint covering of `S`
(`probG_cover_all_ge_explicit`, reindexed) and `d₁` bounds `Err(S ∪ {e})`, `e ∈ R`.

* `probG_cover_set_le` / `probG_cover_set_ge`: the joint covering of a subset `S`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

section Set

variable {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
  (j : Fin m → Fin P.z) (a₀ : Fin P.NA) (kk : (Fin P.q → Fin P.n) → ℕ)
  (C : Fin m → Finset (Fin P.q → Fin P.n))
  (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c))

theorem emb_injective (T : Finset (Fin m)) : Function.Injective (emb T) := fun k k' h =>
  (T.orderIsoOfFin rfl).injective (Subtype.ext h)

theorem forall_mem_iff_emb (T : Finset (Fin m)) (Q : Fin m → Prop) :
    (∀ i ∈ T, Q i) ↔ ∀ k, Q (emb T k) := by
  constructor
  · intro h k; exact h _ (T.orderIsoOfFin rfl k).2
  · intro h i hi
    obtain ⟨k, hk⟩ := (T.orderIsoOfFin rfl).surjective ⟨i, hi⟩
    have := h k
    simp only [emb, hk] at this
    exact this

theorem prod_emb (T : Finset (Fin m)) (g : Fin m → ℝ) :
    ∏ k, g (emb T k) = ∏ i ∈ T, g i := by
  rw [← prod_coe_sort T]
  exact Equiv.prod_comp (T.orderIsoOfFin rfl).toEquiv (fun x : T => g x)

open Classical in
/-- **Joint covering of a subset, upper bound.** -/
theorem probG_cover_set_le (hj : Function.Injective j) (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ)
    (T : Finset (Fin m)) :
    probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i ∈ T, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) ≤
      ∏ i ∈ T, mu1 M κ j a₀ kk C S v i := by
  have h := probG_cover_all_le M κ (j ∘ emb T) (hj.comp (emb_injective T)) a₀ kk (C ∘ emb T)
    (fun k => hC (emb T k)) S v
  rw [← prod_emb]
  refine le_trans (le_of_eq ?_) h
  congr 1
  funext τ
  exact propext (forall_mem_iff_emb T _)

open Classical in
/-- **Joint covering of a subset, lower bound.** -/
theorem probG_cover_set_ge (hj : Function.Injective j) (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ)
    (T : Finset (Fin m)) :
    ∏ i ∈ T, mu1 M κ j a₀ kk C S v i - errSet M κ j a₀ kk C S v T ≤
      probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i ∈ T, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) := by
  have h := probG_cover_all_ge_explicit M κ (j ∘ emb T) (hj.comp (emb_injective T)) a₀ kk
    (C ∘ emb T) (fun k => hC (emb T k)) S v
  simp only at h
  rw [← prod_emb]
  have he : (fun τ => ∀ i ∈ T, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) =
      fun τ => ∀ k, ∃ φ ∈ C (emb T k), CopyOK M κ (j (emb T k)) a₀ (kk φ) φ (liftPi S v τ) :=
    funext fun τ => propext (forall_mem_iff_emb T _)
  rw [he]
  refine le_trans (le_of_eq ?_) h
  unfold errSet mu1 pi1 X1
  simp only [Function.comp]
  ring

theorem mu1_nonneg (i : Fin m) : 0 ≤ mu1 M κ j a₀ kk C S v i :=
  sum_nonneg fun _ _ => probG_nonneg _

open Classical in
/-- **Probability of a covering pattern.** The families in `T` are covered and those in
`R = Tᶜ` are not. -/
theorem probG_pattern_approx (hj : Function.Injective j)
    (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ) (T : Finset (Fin m)) {d₁ : ℝ}
    (hd₁ : ∀ e ∈ univ \ T, errSet M κ j a₀ kk C S v (insert e T) ≤ d₁)
    (hμ1 : ∀ e ∈ univ \ T, mu1 M κ j a₀ kk C S v e ≤ 1) :
    |probG (a := fun c => P.size c - (S c).card) (fun τ =>
        (∀ i ∈ T, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) ∧
          ¬ ∃ i ∈ univ \ T, ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)) -
      (∏ i ∈ T, mu1 M κ j a₀ kk C S v i) *
        ∏ e ∈ univ \ T, (1 - mu1 M κ j a₀ kk C S v e)| ≤
      (∏ i ∈ T, mu1 M κ j a₀ kk C S v i) * (∑ e ∈ univ \ T, mu1 M κ j a₀ kk C S v e) ^ 2 +
        errSet M κ j a₀ kk C S v T + (univ \ T).card * d₁ := by
  set μ := mu1 M κ j a₀ kk C S v
  set R := univ \ T
  set cov : Fin m → (∀ c : P.Coord, Perm (Fin (P.size c - (S c).card))) → Prop :=
    fun i τ => ∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v τ)
  set A : (∀ c : P.Coord, Perm (Fin (P.size c - (S c).card))) → Prop := fun τ => ∀ i ∈ T, cov i τ
  have hlow := probG_and_none_ge R A cov
  have hup := probG_and_none_le R A cov
  have hm : 0 ≤ ∏ i ∈ T, μ i := prod_nonneg fun i _ => mu1_nonneg M κ j a₀ kk C S v i
  have hset : ∀ T' : Finset (Fin m), |probG (a := fun c => P.size c - (S c).card)
      (fun τ => ∀ i ∈ T', cov i τ) - ∏ i ∈ T', μ i| ≤ errSet M κ j a₀ kk C S v T' := by
    intro T'
    have h1 := probG_cover_set_le M κ j a₀ kk C S v hj hC T'
    have h2 := probG_cover_set_ge M κ j a₀ kk C S v hj hC T'
    rw [abs_le]; constructor <;> linarith
  have hA := hset T
  have hins : ∀ e ∈ R, (fun τ => A τ ∧ cov e τ) = fun τ => ∀ i ∈ insert e T, cov i τ := by
    intro e _
    funext τ
    apply propext
    constructor
    · rintro ⟨hA, he⟩ i hi
      rcases mem_insert.1 hi with rfl | hi
      · exact he
      · exact hA i hi
    · intro h; exact ⟨fun i hi => h i (mem_insert_of_mem hi), h e (mem_insert_self _ _)⟩
  have hnotin : ∀ e ∈ R, e ∉ T := fun e he => (mem_sdiff.1 he).2
  have hAB : ∀ e ∈ R, |probG (a := fun c => P.size c - (S c).card) (fun τ => A τ ∧ cov e τ) -
      (∏ i ∈ T, μ i) * μ e| ≤ d₁ := by
    intro e he
    rw [hins e he, show (∏ i ∈ T, μ i) * μ e = ∏ i ∈ insert e T, μ i by
      rw [prod_insert (hnotin e he), mul_comm]]
    exact (hset _).trans (hd₁ e he)
  have hABB : ∀ p ∈ R.offDiag, probG (a := fun c => P.size c - (S c).card)
      (fun τ => A τ ∧ cov p.1 τ ∧ cov p.2 τ) ≤ (∏ i ∈ T, μ i) * μ p.1 * μ p.2 + 0 := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := mem_offDiag.1 hp
    have heq : (fun τ => A τ ∧ cov p.1 τ ∧ cov p.2 τ) =
        fun τ => ∀ i ∈ insert p.1 (insert p.2 T), cov i τ := by
      funext τ
      apply propext
      constructor
      · rintro ⟨hA, h1', h2'⟩ i hi
        rcases mem_insert.1 hi with rfl | hi
        · exact h1'
        rcases mem_insert.1 hi with rfl | hi
        · exact h2'
        · exact hA i hi
      · intro h
        exact ⟨fun i hi => h i (mem_insert_of_mem (mem_insert_of_mem hi)),
          h _ (mem_insert_self _ _), h _ (mem_insert_of_mem (mem_insert_self _ _))⟩
    rw [heq, add_zero]
    refine (probG_cover_set_le M κ j a₀ kk C S v hj hC _).trans (le_of_eq ?_)
    have hn1 : p.1 ∉ insert p.2 T := by
      rw [mem_insert]; push_neg; exact ⟨hne, hnotin _ h1⟩
    rw [prod_insert hn1, prod_insert (hnotin _ h2)]
    ring
  have := pattern_prob_approx R μ (fun e _ => mu1_nonneg M κ j a₀ kk C S v e) hμ1 hm
    (fun e => probG (a := fun c => P.size c - (S c).card) (fun τ => A τ ∧ cov e τ))
    (fun p => probG (a := fun c => P.size c - (S c).card) (fun τ => A τ ∧ cov p.1 τ ∧ cov p.2 τ))
    hlow hup hA hAB hABB le_rfl
  rw [mul_zero, add_zero] at this
  exact this

end Set

end TParams

end DesignsII
