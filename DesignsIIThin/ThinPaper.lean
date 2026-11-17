/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PhiProb

/-!
# Lemma `e|E` (two-sided) and the thinning probability of Lemma `nibble`

* `lemma_e_E`: in the template space conditioned on the values of the colours at the fixed
  vertices `U`, a copy `φ` meeting `U` in at most `r - 1` vertices (with non-degenerate revealed
  values) passes the tests of colour `j` with probability `(1 ± O(δ)) ρ₀(k)`,
  `δ = (q² + q|U|)/N` (Keevash, *Designs II*, Lemma 3.6 and Remark 3.7(i), sharp form);
* `thinning_probability`: the probability that a copy enters the thinned family `Φ'` of the
  proof of Lemma 3.9 is `(1 - t)^m` up to `2^m ((∑ μ)² + (m + 1) errMax)` (`probG_inPhi_approx`).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Lemma `e|E`, two-sided.** -/
theorem e_E_two_sided {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (j : Fin P.z)
    (a₀ : Fin P.NA) {k : ℕ} (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n}
    (hφ : Function.Injective φ) (U : Finset (Fin P.n)) (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : (univ.filter fun i => φ i ∈ U).card + 1 ≤ P.r)
    (hc : LinearIndependent F fun t : Fin (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card =>
      cval (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb hφ)
        ((I₀ (fixedPos U (.inl j)) (wEmb hφ)).orderEmbOfFin rfl t))
    (hN : P.q ^ 2 + P.q * U.card < P.N) (hUq : U.card + P.q ≤ P.N) :
    (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) * P.rho0 k ≤
        probG (a := fun c => P.size c - (fixedPos U c).card)
          (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) ∧
      probG (a := fun c => P.size c - (fixedPos U c).card)
          (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) ≤
        P.rho0 k / (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) := by
  have hI := I₀_fixedPos (P := P) U j hφ
  constructor
  · have hlo := passLB_ge_sharp (K := K) hK U j hφ k hs hN.le hUq
    have hge := probG_copyOK_cond_ge hM hrows κ j a₀ hk hφ U v (by rw [hI]; exact hs) hc
    refine le_trans (le_of_eq ?_) (hlo.trans ?_)
    · unfold rho0; ring
    · unfold passLB; exact hge
  · have hup := probG_copyOK_cond_le_sharp hM κ hK j a₀ hk hφ U v (by omega) hN
    refine hup.trans (le_of_eq ?_)
    have hX : (0 : ℝ) < P.N := by exact_mod_cast (show 0 < P.N by omega)
    have hδ : ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N < 1 := by
      rw [div_lt_one hX]; exact_mod_cast hN
    have h1 : (1 : ℝ) - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N ≠ 0 := by linarith
    unfold rho0
    field_simp

open Classical in
/-- **The thinning probability of Lemma `nibble`.** -/
theorem thinning_prob {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (a₀ : Fin P.NA) (kk : (Fin P.q → Fin P.n) → ℕ)
    (C : Fin m → Finset (Fin P.q → Fin P.n))
    (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c))
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {b : ι' → ℕ}
    (hj : Function.Injective j) (hC : ∀ i, ∀ φ ∈ C i, Function.Injective φ)
    (hμ1 : ∀ i, mu1 M κ j a₀ kk C S v i ≤ 1) (q : Fin m → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) {t : ℝ} (hμq : ∀ i, mu1 M κ j a₀ kk C S v i * q i = t)
    (Cn : (Fin m → Bool) → (∀ c : ι', Perm (Fin (b c))) → Prop)
    (hθ : ∀ w, probG (a := b) (Cn w) = ∏ i, (if w i then 1 - q i else 1)) :
    |probG (a := Sum.elim (fun c => P.size c - (S c).card) b)
        (fun ω => ∃ w ∈ (univ : Finset (Fin m → Bool)),
          (∀ i, (∃ φ ∈ C i, CopyOK M κ (j i) a₀ (kk φ) φ (liftPi S v (leftPart ω))) ↔ w i = true) ∧
            Cn w (rightPart ω)) - (1 - t) ^ m| ≤
      2 ^ m * ((∑ i, mu1 M κ j a₀ kk C S v i) ^ 2 + (m + 1) * errMax M κ j a₀ kk C S v) :=
  probG_inPhi_approx M κ j a₀ kk C S v hj hC hμ1 q hq0 hq1 hμq Cn hθ

end TParams

end DesignsII
