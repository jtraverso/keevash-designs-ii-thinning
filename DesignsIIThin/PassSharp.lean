/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PassUpperAsymp

/-!
# Sharp two-sided Lemma `e|E`

With `δ = (q² + q|U|)/N` and the base rate

  `ρ₀ = N^{r-q} · z^{-Q} ((q-r)!/q!)^Q |𝒜|^{-1} k/N_act`,  `Q = C(q,r)`,

* `passLB_ge_sharp`: `(1 - δ) ρ₀ ≤ passLB` (copies with `s + 1 ≤ r` fixed vertices);
* `probG_copyOK_cond_le_sharp`: the conditional passing probability is `≤ ρ₀ / (1 - δ)`
  (copies with `s ≤ r` fixed vertices, `δ < 1`).

Together with `probG_copyOK_cond_ge` this is Lemma `e|E` in the form `(1 ± O(1/N)) ρ₀` needed by
the nibble (Remark 3.7(i)).
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

/-- `N^w (1 - w(u+w)/N) ≤ (N-u)^{\underline w}`. -/
theorem pow_mul_one_sub_le_descFactorial (N u w : ℕ) (huw : u + w ≤ N) (hN : 0 < N) :
    (N : ℝ) ^ w * (1 - w * ((u + w : ℝ) / N)) ≤ ((N - u).descFactorial w : ℝ) := by
  have hX : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((N - u - w + 1) ^ w : ℕ) ≤ (N - u).descFactorial w := by
    have := Nat.pow_sub_le_descFactorial (N - u) w
    rw [show N - u + 1 - w = N - u - w + 1 by omega] at this
    exact this
  have h1' : ((N : ℝ) - (u + w)) ^ w ≤ ((N - u).descFactorial w : ℝ) := by
    refine le_trans ?_ (by exact_mod_cast h1 : (((N - u - w + 1) ^ w : ℕ) : ℝ) ≤ _)
    push_cast
    refine pow_le_pow_left₀ (by
      have : ((u + w : ℕ) : ℝ) ≤ N := by exact_mod_cast huw
      push_cast at this; linarith) ?_ w
    have : ((N - u - w : ℕ) : ℝ) = N - u - w := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [this]; linarith
  have hx1 : -2 ≤ -((u + w : ℝ) / N) := by
    have : ((u + w : ℕ) : ℝ) ≤ N := by exact_mod_cast huw
    push_cast at this
    have : (u + w : ℝ) / N ≤ 1 := (div_le_one hX).2 this
    linarith
  have hb := one_add_mul_le_pow hx1 w
  have hfac : ((N : ℝ) - (u + w)) ^ w = (N : ℝ) ^ w * (1 + -((u + w : ℝ) / N)) ^ w := by
    rw [← mul_pow]; congr 1; field_simp; ring
  rw [hfac] at h1'
  have hpw : (0 : ℝ) < (N : ℝ) ^ w := by positivity
  have := mul_le_mul_of_nonneg_left hb hpw.le
  refine le_trans (le_of_eq ?_) (this.trans h1')
  ring

/-- Sharp upper core: `N^a (N-u-w)!/(N-u)! ≤ 1/((1 - w(u+w)/N) N^{w-a})`. -/
theorem core_le_sharp (N u w a : ℕ) (haw : a ≤ w) (h : w * (u + w) < N) :
    ((N ^ a : ℕ) : ℝ) * (((N - u - w).factorial : ℕ) : ℝ) / ((N - u).factorial : ℝ) ≤
      1 / ((1 - w * ((u + w : ℝ) / N)) * (N : ℝ) ^ (w - a)) := by
  have hN : 0 < N := by omega
  have hX : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have ha : a = 0 := by omega
    subst ha
    have : (0 : ℝ) < ((N - u).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    simp [this.ne']
  have huw : u + w ≤ N := by nlinarith
  have hx : (w : ℝ) * ((u + w : ℝ) / N) < 1 := by
    have : ((w * (u + w) : ℕ) : ℝ) < N := by exact_mod_cast h
    push_cast at this
    rw [mul_div_assoc', div_lt_one hX]; exact this
  have hpos : (0 : ℝ) < 1 - w * ((u + w : ℝ) / N) := by linarith
  have hfac : ((N - u).factorial : ℝ) =
      ((N - u - w).factorial : ℝ) * ((N - u).descFactorial w : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial (by omega : w ≤ N - u)).symm
  have hdpos : (0 : ℝ) < ((N - u).descFactorial w : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  have hfpos : (0 : ℝ) < ((N - u - w).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : ((N ^ a : ℕ) : ℝ) * ((((N - u - w).factorial : ℕ) : ℝ)) / ((N - u).factorial : ℝ) =
      (N : ℝ) ^ a / ((N - u).descFactorial w : ℝ) := by
    rw [hfac]; push_cast; field_simp
  rw [h2, div_le_div_iff₀ hdpos (by positivity)]
  have hd := pow_mul_one_sub_le_descFactorial N u w huw hN
  have hsplit : (N : ℝ) ^ w = (N : ℝ) ^ (w - a) * (N : ℝ) ^ a := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at hd
  nlinarith [pow_pos hX a, pow_pos hX (w - a)]

/-- Sharp lower core: `(1 - c/N)/N^{w-a} ≤ (N^a - c N^{a-1}) (N-u-w)!/(N-u)!`. -/
theorem core_ge_sharp (N u w a c : ℕ) (ha : 1 ≤ a) (haw : a ≤ w) (hc : c ≤ N)
    (huw : u + w ≤ N) :
    (1 - (c : ℝ) / N) / (N : ℝ) ^ (w - a) ≤
      (((N ^ a : ℕ) : ℝ) - ((c * N ^ (a - 1) : ℕ) : ℝ)) *
        (((N - u - w).factorial : ℕ) : ℝ) / ((N - u).factorial : ℝ) := by
  have hN : 0 < N := by omega
  have hX : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ a = N * (N : ℝ) ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 : ((N ^ a : ℕ) : ℝ) - ((c * N ^ (a - 1) : ℕ) : ℝ) = (N : ℝ) ^ a * (1 - (c : ℝ) / N) := by
    push_cast; rw [hpow]; field_simp
  have hc' : (0 : ℝ) ≤ 1 - (c : ℝ) / N := by
    have : (c : ℝ) ≤ N := by exact_mod_cast hc
    have : (c : ℝ) / N ≤ 1 := (div_le_one hX).2 this
    linarith
  have hfac : ((N - u).factorial : ℝ) =
      ((N - u - w).factorial : ℝ) * ((N - u).descFactorial w : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial (by omega : w ≤ N - u)).symm
  have hdesc : ((N - u).descFactorial w : ℝ) ≤ (N : ℝ) ^ w := by
    exact_mod_cast (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  have hdpos : (0 : ℝ) < ((N - u).descFactorial w : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  have hfpos : (0 : ℝ) < ((N - u - w).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : ((((N - u - w).factorial : ℕ) : ℝ)) / ((N - u).factorial : ℝ) =
      1 / ((N - u).descFactorial w : ℝ) := by
    rw [hfac]; field_simp
  rw [mul_div_assoc, h2, h1]
  have hsplit : (N : ℝ) ^ w = (N : ℝ) ^ (w - a) * (N : ℝ) ^ a := by
    rw [← pow_add]; congr 1; omega
  calc (1 - (c : ℝ) / N) / (N : ℝ) ^ (w - a)
        = (N : ℝ) ^ a * (1 - (c : ℝ) / N) * (1 / (N : ℝ) ^ w) := by
          rw [hsplit]; field_simp
    _ ≤ (N : ℝ) ^ a * (1 - (c : ℝ) / N) * (1 / ((N - u).descFactorial w : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact one_div_le_one_div_of_le hdpos hdesc

open Classical in
/-- **Sharp lower half of Lemma `e|E`:** `passLB ≥ (1 - δ) ρ₀`. -/
theorem passLB_ge_sharp (hK : Fintype.card K = P.N) (U : Finset (Fin P.n)) (j : Fin P.z)
    {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (k : ℕ)
    (hs : (univ.filter fun i => φ i ∈ U).card + 1 ≤ P.r)
    (hN : P.q ^ 2 + P.q * U.card ≤ P.N) (hUq : U.card + P.q ≤ P.N) :
    (1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) / (P.N : ℝ) ^ (P.q - P.r) *
        (1 / (P.z : ℝ)) ^ P.q.choose P.r *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) ≤
      passLB (K := K) U j hφ k := by
  have hI := I₀_fixedPos (P := P) U j hφ
  set s := (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card with hsdef
  have hs' : s + 1 ≤ P.r := by rw [hsdef, hI]; exact hs
  have hS : (fixedPos U (.inl j)).card = U.card := card_map _
  have hnew : Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)} = P.q - s := by
    rw [Fintype.card_subtype]
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin P.q)))
      (fun i => wEmb hφ i ∈ fixedPos U (.inl j))
    rw [card_univ, Fintype.card_fin] at h
    have h' : (univ.filter fun i => wEmb hφ i ∈ fixedPos U (.inl j)).card = s := by
      rw [hsdef]; unfold I₀; congr 1; ext; simp only [mem_filter, mem_univ, true_and]; exact Iff.rfl
    have h'' : (univ.filter fun i => wEmb hφ i ∉ fixedPos U (.inl j)).card =
        (univ.filter fun i => ¬ wEmb hφ i ∈ fixedPos U (.inl j)).card := by congr 1
    omega
  have hrq := P.hrq
  have hcore := core_ge_sharp P.N U.card (P.q - s) (P.r - s) (P.q ^ 2 + P.q * U.card)
    (by omega) (by omega) hN (by omega)
  rw [show P.q - s - (P.r - s) = P.q - P.r by omega] at hcore
  have hrest : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ P.q.choose P.r *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by positivity
  have := mul_le_mul_of_nonneg_right hcore hrest
  unfold passLB
  rw [hK, hS, hnew, card_edges hφ, ← hsdef]
  convert this using 1 <;> ring

open Classical in
/-- **Sharp upper half of Lemma `e|E`:** the conditional passing probability is
`≤ ρ₀ / (1 - δ)`. -/
theorem probG_copyOK_cond_le_sharp {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (j : Fin P.z) (a₀ : Fin P.NA) {k : ℕ}
    (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : (univ.filter fun i => φ i ∈ U).card ≤ P.r)
    (hN : P.q ^ 2 + P.q * U.card < P.N) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) ≤
      1 / ((1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) * (P.N : ℝ) ^ (P.q - P.r)) *
        (1 / (P.z : ℝ)) ^ P.q.choose P.r *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by
  have hI := I₀_fixedPos (P := P) U j hφ
  set s := (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card with hsdef
  have hs' : s ≤ P.r := by rw [hsdef, hI]; exact hs
  have hS : (fixedPos U (.inl j)).card = U.card := card_map _
  have hnew : Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)} = P.q - s := by
    rw [Fintype.card_subtype]
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin P.q)))
      (fun i => wEmb hφ i ∈ fixedPos U (.inl j))
    rw [card_univ, Fintype.card_fin] at h
    have h' : (univ.filter fun i => wEmb hφ i ∈ fixedPos U (.inl j)).card = s := by
      rw [hsdef]; unfold I₀; congr 1; ext; simp only [mem_filter, mem_univ, true_and]; exact Iff.rfl
    have h'' : (univ.filter fun i => wEmb hφ i ∉ fixedPos U (.inl j)).card =
        (univ.filter fun i => ¬ wEmb hφ i ∈ fixedPos U (.inl j)).card := by congr 1
    omega
  have hrq := P.hrq
  have hup := probG_copyOK_cond_le hM κ j a₀ hk hφ U v (by rw [← hsdef]; exact hs')
  rw [hK, hS, hnew, card_edges hφ, ← hsdef] at hup
  have hNpos : 0 < P.N := by omega
  have hX : (0 : ℝ) < P.N := by exact_mod_cast hNpos
  have hw : (P.q - s) * (U.card + (P.q - s)) ≤ P.q ^ 2 + P.q * U.card := by
    have h1 : P.q - s ≤ P.q := Nat.sub_le _ _
    calc (P.q - s) * (U.card + (P.q - s)) ≤ P.q * (U.card + P.q) :=
          Nat.mul_le_mul h1 (by omega)
      _ = P.q ^ 2 + P.q * U.card := by ring
  have hcore := core_le_sharp P.N U.card (P.q - s) (P.r - s) (by omega) (by omega)
  rw [show P.q - s - (P.r - s) = P.q - P.r by omega] at hcore
  -- replace `w(u+w)/N` by `δ`
  have hxle : ((P.q - s : ℕ) : ℝ) * ((U.card + (P.q - s : ℕ) : ℝ) / P.N) ≤
      ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hX]
    exact_mod_cast hw
  have hδ : ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N < 1 := by
    rw [div_lt_one hX]; exact_mod_cast hN
  have hmono : 1 / ((1 - ((P.q - s : ℕ) : ℝ) * ((U.card + (P.q - s : ℕ) : ℝ) / P.N)) *
        (P.N : ℝ) ^ (P.q - P.r)) ≤
      1 / ((1 - ((P.q ^ 2 + P.q * U.card : ℕ) : ℝ) / P.N) * (P.N : ℝ) ^ (P.q - P.r)) := by
    apply one_div_le_one_div_of_le
    · exact mul_pos (by linarith) (by positivity)
    · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hrest : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ P.q.choose P.r *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by positivity
  have := mul_le_mul_of_nonneg_right (hcore.trans hmono) hrest
  refine hup.trans ?_
  convert this using 1 <;> ring

end TParams

end DesignsII
