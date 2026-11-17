/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CondPerm

/-!
# Definitions for the thinning statements of Lemma `nibble`

The base passing rate `ρ₀`, the two parts of the joint space (template ⊕ thinning coins), and the
single, pair and conflict masses of families of copies with the explicit joint-covering errors
(`errSet`, `errMax`). Shared by the development and by the statements.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

section Joint

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {a : ι → ℕ} {b : ι' → ℕ}

/-- The left coordinates of a point of the joint space. -/
def leftPart (ω : ∀ c : ι ⊕ ι', Perm (Fin (Sum.elim a b c))) : ∀ c : ι, Perm (Fin (a c)) :=
  fun c => ω (Sum.inl c)

/-- The right coordinates of a point of the joint space. -/
def rightPart (ω : ∀ c : ι ⊕ ι', Perm (Fin (Sum.elim a b c))) : ∀ c : ι', Perm (Fin (b c)) :=
  fun c => ω (Sum.inr c)

end Joint

namespace TParams

/-- The base passing rate `ρ₀(k)`. -/
noncomputable def rho0 (P : TParams) (k : ℕ) : ℝ :=
  1 / (P.N : ℝ) ^ (P.q - P.r) * (1 / (P.z : ℝ)) ^ P.q.choose P.r *
    (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
    (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact)

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

variable {P : TParams}

section Masses

variable {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
  (j : Fin m → Fin P.z) (a₀ : Fin P.NA) (kk : (Fin P.q → Fin P.n) → ℕ)
  (C : Fin m → Finset (Fin P.q → Fin P.n))
  (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c))

open Classical in
/-- The single, pair and conflict masses. -/
noncomputable def mu1 (i : Fin m) : ℝ := ∑ x ∈ C i, probG (a := fun c => P.size c - (S c).card)
  (fun τ => CopyOK M κ (j i) a₀ (kk x) x (liftPi S v τ))

open Classical in
noncomputable def pi1 (i : Fin m) : ℝ := ∑ q ∈ (C i).offDiag,
  probG (a := fun c => P.size c - (S c).card)
    (fun τ => CopyOK M κ (j i) a₀ (kk q.1) q.1 (liftPi S v τ) ∧
      CopyOK M κ (j i) a₀ (kk q.2) q.2 (liftPi S v τ))

open Classical in
noncomputable def X1 (i i' : Fin m) : ℝ := ∑ x ∈ C i, ∑ y ∈ C i',
  if ¬ Disjoint (edges x) (edges y) then
    probG (a := fun c => P.size c - (S c).card)
      (fun τ => CopyOK M κ (j i) a₀ (kk x) x (liftPi S v τ)) *
    probG (a := fun c => P.size c - (S c).card)
      (fun τ => CopyOK M κ (j i') a₀ (kk y) y (liftPi S v τ))
  else 0

/-- The reindexing of a subset. -/
noncomputable def emb (T : Finset (Fin m)) : Fin T.card → Fin m := fun k => (T.orderIsoOfFin rfl k)

open Classical in
/-- The explicit error of the joint covering of a subset `T`. -/
noncomputable def errSet (T : Finset (Fin m)) : ℝ :=
  (∏ k, (mu1 M κ j a₀ kk C S v (emb T k) + pi1 M κ j a₀ kk C S v (emb T k)) -
      ∏ k, mu1 M κ j a₀ kk C S v (emb T k)) / (1 + 1) +
    ∑ p ∈ (univ : Finset (Fin T.card)).offDiag,
      X1 M κ j a₀ kk C S v (emb T p.1) (emb T p.2) *
        ∏ l ∈ (univ.erase p.1).erase p.2, mu1 M κ j a₀ kk C S v (emb T l)

open Classical in
/-- The largest joint-covering error over subsets of the families. -/
noncomputable def errMax : ℝ :=
  (univ : Finset (Finset (Fin m))).sup' ⟨∅, mem_univ _⟩ fun T => errSet M κ j a₀ kk C S v T

end Masses

end TParams

end DesignsII
