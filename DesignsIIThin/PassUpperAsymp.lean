/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsIIThin.PassUpper
public import DesignsII.PassAsymp

/-!
# Size of the conditional passing probability: upper bound

`probG_copyOK_cond_le_asymp`: if a copy meets the fixed set `U` in `s ≤ r` vertices and
`2q(|U| + q) ≤ N = |K|`, then the conditional passing probability is at most

  `2/N^{q-r} · z^{-Q} ((q-r)!/q!)^Q |𝒜|^{-1} k/N_act`,  `Q = C(q,r)`,

matching `passLB_ge` up to the factor `4`: the two-sided Lemma `e|E` up to constants.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

/-- The descending factorial is at least half the power when `2 w (u + w) ≤ N`. -/
theorem half_pow_le_descFactorial (N u w : ℕ) (h : 2 * w * (u + w) ≤ N) :
    (N : ℝ) ^ w / 2 ≤ ((N - u).descFactorial w : ℝ) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp; norm_num
  have hN : 0 < N := by nlinarith
  have hX : (0 : ℝ) < N := by exact_mod_cast hN
  have huw : u + w ≤ N := by nlinarith
  -- (N - u - w + 1)^w ≤ descFactorial
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
  -- Bernoulli: (1 - x)^w ≥ 1 - w x
  have hx : (0 : ℝ) ≤ (u + w) / N := by positivity
  have hx1 : -2 ≤ -((u + w : ℝ) / N) := by
    have : ((u + w : ℕ) : ℝ) ≤ N := by exact_mod_cast huw
    push_cast at this
    have : (u + w : ℝ) / N ≤ 1 := (div_le_one hX).2 this
    linarith
  have hb := one_add_mul_le_pow hx1 w
  have hwx : (w : ℝ) * ((u + w) / N) ≤ 1 / 2 := by
    have : ((2 * w * (u + w) : ℕ) : ℝ) ≤ N := by exact_mod_cast h
    push_cast at this
    rw [mul_div_assoc', div_le_iff₀ hX]; linarith
  have hfac : ((N : ℝ) - (u + w)) ^ w = (N : ℝ) ^ w * (1 + -((u + w : ℝ) / N)) ^ w := by
    rw [← mul_pow]; congr 1; field_simp; ring
  rw [hfac] at h1'
  have hpw : (0 : ℝ) < (N : ℝ) ^ w := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hb hpw.le]

/-- Real arithmetic core: `N^a (N-u-w)!/(N-u)! ≤ 2/N^{w-a}`. -/
theorem core_le (N u w a : ℕ) (haw : a ≤ w) (h : 2 * w * (u + w) ≤ N) (hN : 0 < N) :
    ((N ^ a : ℕ) : ℝ) * (((N - u - w).factorial : ℕ) : ℝ) / ((N - u).factorial : ℝ) ≤
      2 / (N : ℝ) ^ (w - a) := by
  have hX : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have ha : a = 0 := by omega
    subst ha
    have : (0 : ℝ) < ((N - u).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    simp [this.ne']
  have huw : u + w ≤ N := by nlinarith
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
  have hd := half_pow_le_descFactorial N u w h
  have hsplit : (N : ℝ) ^ w = (N : ℝ) ^ (w - a) * (N : ℝ) ^ a := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at hd
  nlinarith [pow_pos hX a, pow_pos hX (w - a)]

open Classical in
/-- **The conditional passing probability is at most `2 N^{r-q} · …`** (upper half of Lemma
`e|E`, asymptotic form). -/
theorem probG_copyOK_cond_le_asymp {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N) (j : Fin P.z) (a₀ : Fin P.NA) {k : ℕ}
    (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hs : (univ.filter fun i => φ i ∈ U).card ≤ P.r)
    (hN : 2 * P.q * (U.card + P.q) ≤ P.N) (hNpos : 0 < P.N) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) ≤
      2 / (P.N : ℝ) ^ (P.q - P.r) * (1 / (P.z : ℝ)) ^ P.q.choose P.r *
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
  have hcore := core_le P.N U.card (P.q - s) (P.r - s) (by omega)
    (by nlinarith [Nat.sub_le P.q s]) hNpos
  rw [show P.q - s - (P.r - s) = P.q - P.r by omega] at hcore
  have hrest : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ P.q.choose P.r *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by positivity
  have := mul_le_mul_of_nonneg_right hcore hrest
  refine hup.trans ?_
  convert this using 1 <;> ring

end TParams

end DesignsII
