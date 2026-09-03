/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.OneNormScaling
public import CQM1.TrotterError.OrderingRemoval
public import CQM1.TrotterError.CommutatorScaling

import CQM1.TrotterError.ListProd

/-!
# Main theorem: commutator scaling of Trotter error

The main theorems of *A Theory of Trotter Error* (arXiv:1912.08854): the norm bound for the
additive kernel `𝒯(τ)` and the commuting-scaling bounds for the Trotter error
`thm:trotter_error_comm_scaling` together with the Trotter-number corollary
`cor:trotter_number_comm_scaling` (anti-Hermitian branch).

Supporting steps live in dedicated files:
* `OrderingRemoval.lean` — `αCommConj_sum_le_αComm` (`papers/rep.tex` lines 129–139).
* `CommutatorScaling.lean` — the `additiveKernel = Σ multiConj − multiConj` bridge and the
  order-condition cancellation `additiveKernel_eq_commutatorRemainder_sum`
  (`papers/theory.tex` lines 251–266).

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open TrotterError.List
open scoped Topology BigOperators algebraMap

/-! ### R3: the skew-adjoint norm bound -/

/-- Shared skeleton of the additive-kernel norm bound (`thm:trotter_error_order_cond`): from
per-remainder bounds `‖remᵢ(−τ)‖ ≤ αᵢ · C` and `‖rem_all(−τ)‖ ≤ α_all · C` with `0 ≤ C`, and the
coefficient bound `Σᵢ αᵢ + α_all ≤ 2 Υ Σ_γ α_γ`, conclude
`‖additiveKernel P H τ‖ ≤ 2 Υ (Σ_γ α_γ) · C`. -/
lemma norm_additiveKernel_le_of_rem_bound (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrem_i : ∀ i : Fin P.Υ × Fin P.Γ,
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
    (hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖ ≤
        αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C)
    (hcoeff : (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
        + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
        ≤ 2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) :
    ‖additiveKernel P H τ‖ ≤
      2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by
  have hR2 := additiveKernel_eq_commutatorRemainder_sum P H p hp h_order τ
  calc
    ‖additiveKernel P H τ‖
        = ‖(∑ i : Fin P.Υ × Fin P.Γ,
              commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
            - commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖ := by
              rw [hR2]
    _ ≤ ‖∑ i : Fin P.Υ × Fin P.Γ,
            commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖
          + ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖ :=
              norm_sub_le _ _
    _ ≤ (∑ i : Fin P.Υ × Fin P.Γ,
            ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
          + ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖ := by
              gcongr
              exact norm_sum_le univ
                (fun i => commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
    _ ≤ (∑ i : Fin P.Υ × Fin P.Γ,
            αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C := by
              refine add_le_add (sum_le_sum (fun i _ => hrem_i i)) hrem_all
    _ = ((∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p) * C := by
              rw [← sum_mul, ← add_mul]
    _ ≤ (2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) * C :=
              mul_le_mul_of_nonneg_right hcoeff hC
    _ = 2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by ring

/-- `thm:trotter_error_order_cond` (anti-Hermitian branch): the spectral norm of the additive
kernel is bounded by `2 Υ (Σ_γ α_comm) |τ|^p / p!`. -/
theorem norm_additiveKernel_le_of_skewAdjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin P.Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < P.Υ) (τ : ℝ) :
    ‖additiveKernel P H τ‖ ≤
      2 * (P.Υ : ℝ) * (∑ γ, αCommConj (orderedSummandsEval P H) (H γ) p) *
        |τ| ^ p / (Nat.factorial p : ℝ) := by
  have h_skew_suffix : ∀ i k, star (suffixGenerators P H i k) = -(suffixGenerators P H i k) := by
    intro i k
    exact star_generator_of_skew P H h_skew
      ((P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).get k)
  have h_skew_ordered : ∀ k, star (orderedGenerators P H k) = -(orderedGenerators P H k) := by
    intro k
    exact star_generator_of_skew P H h_skew (P.evalIndexList.get k)
  have hrem_i : ∀ i : Fin P.Υ × Fin P.Γ,
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p *
          (|τ| ^ p / (Nat.factorial p : ℝ)) := by
    intro i
    simpa [abs_neg, div_eq_mul_inv, mul_assoc] using
      norm_commutatorRemainder_le_of_skewAdjoint (suffixGenerators P H i) (P.generator H i) p
        (-τ) (h_skew_suffix i)
  have hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖ ≤
      αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p *
        (|τ| ^ p / (Nat.factorial p : ℝ)) := by
    simpa [abs_neg, div_eq_mul_inv, mul_assoc] using
      norm_commutatorRemainder_le_of_skewAdjoint (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
        (-τ) h_skew_ordered
  simpa [div_eq_mul_inv, mul_assoc] using
    norm_additiveKernel_le_of_rem_bound P H p hp h_order τ (|τ| ^ p / (Nat.factorial p : ℝ))
      (by positivity) hrem_i hrem_all (sum_αCommConj_suffix_add_ordered_le P H p hΥ)

/-! ### R3g: the general-operator norm bound -/

/-- `thm:trotter_error_comm_scaling` (general branch): the spectral norm of the additive kernel is
bounded by `2 Υ (Σ_γ α_comm) |τ|^p / p! · exp(2|τ| Υ Σ ‖H_γ‖)`. -/
theorem norm_additiveKernel_le (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ) (τ : ℝ) :
    ‖additiveKernel P H τ‖ ≤
      2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) *
        |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (2 * |τ| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  let N : ℝ := (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖
  let C : ℝ := |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * N)
  have hrem_i : ∀ i : Fin P.Υ × Fin P.Γ,
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C := by
    intro i
    have hsum : (∑ k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length,
        ‖suffixGenerators P H i k‖) ≤ N := by
      dsimp [N]
      exact sum_norm_suffixGenerators_le P H i
    have hexp : Real.exp (2 * |τ| *
        ∑ k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length,
          ‖suffixGenerators P H i k‖) ≤ Real.exp (2 * |τ| * N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity))
    calc
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖
          ≤ αCommConj (suffixGenerators P H i) (P.generator H i) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| *
                ∑ k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length,
                  ‖suffixGenerators P H i k‖) := by
              simpa [abs_neg] using
                norm_commutatorRemainder_le (suffixGenerators P H i) (P.generator H i) p (-τ)
      _ ≤ αCommConj (suffixGenerators P H i) (P.generator H i) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * N) := by
              exact mul_le_mul_of_nonneg_left hexp
                (div_nonneg (mul_nonneg
                  (αCommConj_nonneg (suffixGenerators P H i) (P.generator H i) p)
                  (pow_nonneg (abs_nonneg τ) p)) (Nat.cast_nonneg _))
      _ = αCommConj (suffixGenerators P H i) (P.generator H i) p * C := by
              dsimp [C]
              ring_nf
  have hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖ ≤
      αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C := by
    have hsum : (∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖) ≤ N := by
      dsimp [N]
      exact sum_norm_orderedGenerators_le P H
    have hexp : Real.exp (2 * |τ| * ∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖) ≤
        Real.exp (2 * |τ| * N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity))
    calc
      ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖
          ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| *
                ∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖) := by
              simpa [abs_neg] using
                norm_commutatorRemainder_le (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)
      _ ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * N) := mul_le_mul_of_nonneg_left hexp
                (div_nonneg (mul_nonneg
                  (αCommConj_nonneg (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p)
                  (pow_nonneg (abs_nonneg τ) p)) (Nat.cast_nonneg _))
      _ = αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C := by
              dsimp [C]
              ring_nf
  have hC : 0 ≤ C := by positivity
  simpa [C, N, div_eq_mul_inv, mul_assoc] using
    norm_additiveKernel_le_of_rem_bound P H p hp h_order τ C hC hrem_i hrem_all
      (sum_αCommConj_suffix_add_ordered_le P H p hΥ)

/-! ### R3g-residual: the telescoped residual bound -/

/-- The single suffix-remainder summand, scaled by `P.eval H τ`, telescopes to a single exponential
`exp (|τ| · Υ · Σ ‖H γ‖)` (rep.tex:50–113). -/
lemma norm_eval_mul_commutatorRemainderTerm_le (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (p : ℕ)
    (j : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length)
    (q : Fin (j + 1) → ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖P.eval H τ * commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖ ≤
      ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
          (P.generator H i)‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
        Real.exp (|τ| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  let Cprefix : ℝ := ((P.evalIndexList.take (P.evalIndexList.idxOf i)).map
    (fun j => ‖H (P.perm j.1 j.2)‖)).sum + ‖H (P.perm i.1 i.2)‖
  have hL : ‖prefixFactorProd P H i τ * P.evalFactor H i τ‖ ≤ Real.exp (|τ| * Cprefix) := by
    dsimp [Cprefix]
    exact norm_prefixFactorProd_mul_evalFactor_le P H i τ
  have hstrict : strictSuffixFactorProd P H i τ =
      (List.ofFn (fun k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length =>
        exp (τ • suffixGenerators P H i k))).prod := by
    dsimp [strictSuffixFactorProd, factorProdOver, suffixGenerators]
    congr 1
    change (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).map (fun j => P.evalFactor H j τ) =
      List.ofFn (fun k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length =>
        exp (τ • P.generator H ((P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).get k)))
    rw [← List.ofFn_get (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)), List.map_ofFn]
    simp [ProductFormulaData.evalFactor]
  have hdec : P.eval H τ = prefixFactorProd P H i τ * P.evalFactor H i τ *
      strictSuffixFactorProd P H i τ := by
    rw [← factorProdOver_evalIndexList P H τ]
    simpa only [prefixFactorProd, strictSuffixFactorProd, factorProdOver] using
      (prod_map_eq_take_mul_get_mul_drop (l := P.evalIndexList) (f := fun j => P.evalFactor H j τ)
        i (evalIndexList_mem P i))
  have hdecomp : P.eval H τ = (prefixFactorProd P H i τ * P.evalFactor H i τ) *
      (List.ofFn (fun k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length =>
        exp (τ • suffixGenerators P H i k))).prod := by
    calc
      P.eval H τ = prefixFactorProd P H i τ * P.evalFactor H i τ * strictSuffixFactorProd P H i τ :=
        hdec
      _ = (prefixFactorProd P H i τ * P.evalFactor H i τ) * strictSuffixFactorProd P H i τ := by
        ac_rfl
      _ = (prefixFactorProd P H i τ * P.evalFactor H i τ) *
          (List.ofFn (fun k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length =>
            exp (τ • suffixGenerators P H i k))).prod := by rw [hstrict]
  have hCsum : Cprefix + (∑ k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length,
      ‖suffixGenerators P H i k‖) ≤ (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
    dsimp [Cprefix]
    exact prefix_point_suffix_norm_sum_le P H i
  have hterm := norm_mul_commutatorRemainderTerm_le (A := suffixGenerators P H i)
    (B := P.generator H i) (L := prefixFactorProd P H i τ * P.evalFactor H i τ) (C := Cprefix)
    (p := p) (j := j) (q := q) (τ := τ) hτ hq hlast hL
  calc
    ‖P.eval H τ * commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖
        = ‖(prefixFactorProd P H i τ * P.evalFactor H i τ) *
            (List.ofFn (fun k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length =>
              exp (τ • suffixGenerators P H i k))).prod *
            commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖ := by
              rw [hdecomp]
    _ ≤ ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (P.generator H i)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (Cprefix + (∑ k : Fin
            (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length,
            ‖suffixGenerators P H i k‖))) := hterm
    _ ≤ ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (P.generator H i)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · exact Real.exp_le_exp.mpr
                  (by nlinarith [mul_le_mul_of_nonneg_left hCsum (abs_nonneg τ)])
              · positivity

/-- The single ordered-remainder summand, scaled by `P.eval H τ`, telescopes to a single exponential
`exp (|τ| · Υ · Σ ‖H γ‖)`. -/
lemma norm_eval_mul_commutatorRemainderTerm_ordered_le (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (j : Fin P.evalIndexList.length) (q : Fin (j + 1) → ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖P.eval H τ * commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) (-τ) j q‖ ≤
      ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
          (∑ γ : Fin P.Γ, H γ)‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
        Real.exp (|τ| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  have hL : ‖(1 : 𝔸)‖ ≤ Real.exp (|τ| * 0) := by simp
  have hdecomp : P.eval H τ = (1 : 𝔸) * (List.ofFn (fun k : Fin P.evalIndexList.length =>
      exp (τ • orderedGenerators P H k))).prod := by
    rw [one_mul]
    calc
      P.eval H τ = (P.evalIndexList.map (fun i => P.evalFactor H i τ)).prod := rfl
      _ = (P.evalIndexList.map (fun i => exp (τ • P.generator H i))).prod := by
              simp [ProductFormulaData.evalFactor]
      _ = (List.ofFn (fun k : Fin P.evalIndexList.length =>
            exp (τ • P.generator H (P.evalIndexList.get k)))).prod := by
              congr 1
              change P.evalIndexList.map (fun i => exp (τ • P.generator H i)) =
                List.ofFn ((fun i => exp (τ • P.generator H i)) ∘ P.evalIndexList.get)
              rw [← List.map_ofFn, List.ofFn_get]
      _ = (List.ofFn (fun k : Fin P.evalIndexList.length =>
            exp (τ • orderedGenerators P H k))).prod := by rfl
  have hsum : (0 : ℝ) + (∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖) ≤
      (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
    simpa using sum_norm_orderedGenerators_le P H
  have hterm := norm_mul_commutatorRemainderTerm_le (A := orderedGenerators P H)
    (B := ∑ γ : Fin P.Γ, H γ) (L := (1 : 𝔸)) (C := 0) (p := p) (j := j) (q := q) (τ := τ)
    hτ hq hlast hL
  calc
    ‖P.eval H τ * commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) (-τ) j q‖
        = ‖(1 : 𝔸) * (List.ofFn (fun k : Fin P.evalIndexList.length =>
            exp (τ • orderedGenerators P H k))).prod *
            commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) (-τ) j q‖ := by
              rw [hdecomp]
    _ ≤ ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (∑ γ : Fin P.Γ, H γ)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (0 + (∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖))) :=
          hterm
    _ ≤ ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (∑ γ : Fin P.Γ, H γ)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · exact Real.exp_le_exp.mpr
                  (by nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg τ)])
              · positivity

/-- Shared skeleton of the additive-residual norm bound: from per-remainder bounds of the scaled
`P.eval H τ · remᵢ(-τ)` terms and the coefficient bound, conclude the telescoped residual bound. -/
lemma norm_additiveResidual_le_of_rem_bound (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrem_i : ∀ i : Fin P.Υ × Fin P.Γ,
      ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
    (hrem_all : ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
        (-τ)‖ ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C)
    (hcoeff : (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
        + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
        ≤ 2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) :
    ‖additiveResidual P H τ‖ ≤
      2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by
  rw [additiveResidual_eq_eval_mul_kernel P H τ]
  have hR2 := additiveKernel_eq_commutatorRemainder_sum P H p hp h_order τ
  rw [hR2, mul_sub, Finset.mul_sum]
  calc
    ‖(∑ i : Fin P.Υ × Fin P.Γ,
          P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
        - P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖
        ≤ ‖∑ i : Fin P.Υ × Fin P.Γ,
              P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖
          + ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
              (-τ)‖ :=
              norm_sub_le _ _
    _ ≤ (∑ i : Fin P.Υ × Fin P.Γ,
            ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
          + ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
              (-τ)‖ := by
              gcongr
              exact norm_sum_le univ
                (fun i => P.eval H τ * commutatorRemainder (suffixGenerators P H i)
                  (P.generator H i) p (-τ))
    _ ≤ (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C := by
              refine add_le_add (sum_le_sum (fun i _ => hrem_i i)) hrem_all
    _ = ((∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p) * C := by
              rw [← sum_mul, ← add_mul]
    _ ≤ (2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) * C :=
              mul_le_mul_of_nonneg_right hcoeff hC
    _ = 2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by ring

/-- `thm:trotter_error_comm_scaling` (general branch): the additive residual telescopes to
`2 Υ (Σ_γ α_comm) |τ|^p / p! · exp(|τ| Υ Σ ‖H_γ‖)` (rep.tex:96–113). -/
theorem norm_additiveResidual_le (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖additiveResidual P H τ‖ ≤
      2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) *
        |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  let N : ℝ := (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖
  let C : ℝ := |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * N)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrem_i : ∀ i : Fin P.Υ × Fin P.Γ,
      ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C := by
    intro i
    have hbound := norm_mul_commutatorRemainder_le_of_term_bound (M := P.eval H τ)
      (A := suffixGenerators P H i) (B := P.generator H i) (p := p) (τ := -τ)
      (F := Real.exp (|τ| * N)) (by positivity) ?_
    · simpa [C, N, abs_neg, div_eq_mul_inv, mul_assoc] using hbound
    · intro j q hq
      have hqf := mem_filter.mp hq
      simpa [abs_neg, N, mul_assoc] using
        norm_eval_mul_commutatorRemainderTerm_le P H i p j q τ hτ hqf.1 hqf.2
  have hrem_all : ‖P.eval H τ * commutatorRemainder (orderedGenerators P H)
      (∑ γ : Fin P.Γ, H γ) p (-τ)‖ ≤
      αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p * C := by
    have hbound := norm_mul_commutatorRemainder_le_of_term_bound (M := P.eval H τ)
      (A := orderedGenerators P H) (B := ∑ γ : Fin P.Γ, H γ) (p := p) (τ := -τ)
      (F := Real.exp (|τ| * N)) (by positivity) ?_
    · simpa [C, N, abs_neg, div_eq_mul_inv, mul_assoc] using hbound
    · intro j q hq
      have hqf := mem_filter.mp hq
      simpa [abs_neg, N, mul_assoc] using
        norm_eval_mul_commutatorRemainderTerm_ordered_le P H p j q τ hτ hqf.1 hqf.2
  simpa [C, N, div_eq_mul_inv, mul_assoc] using
    norm_additiveResidual_le_of_rem_bound P H p hp h_order τ C hC hrem_i hrem_all
      (sum_αCommConj_suffix_add_ordered_le P H p hΥ)

/-! ### R3g-final: pointwise and asymptotic commuting-scaling bounds -/

/-- The additive error as an integral of the additive residual (the unfactored form of
`errorType_additive`). -/
lemma eval_sub_exp_eq_integral_residual (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (t : ℝ) :
    P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ) =
      ∫ τ in 0..t, exp ((t - τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ := by
  have h := errorType_additive P H t
  rw [h, add_sub_cancel_left]
  refine intervalIntegral.integral_congr_uIoo ?_
  intro τ _
  change exp ((t - τ) • (∑ γ : Fin P.Γ, H γ)) * P.eval H τ * additiveKernel P H τ =
    exp ((t - τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ
  rw [mul_assoc, additiveResidual_eq_eval_mul_kernel P H τ]

/-- `thm:trotter_error_comm_scaling` (general branch): the explicit pointwise commuting-scaling
bound with the exponential prefactor `exp (2 t Υ Σ ‖H_γ‖)`. -/
theorem trotter_error_bound_comm_scaling (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  let S : 𝔸 := ∑ γ : Fin P.Γ, H γ
  let N : ℝ := ∑ γ : Fin P.Γ, ‖H γ‖
  let sAlpha : ℝ := ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (P.Υ : ℝ) * sAlpha
  have hS_le : ‖S‖ ≤ N := by
    dsimp [S, N]
    exact norm_sum_le univ H
  have hR3 : ∀ τ, 0 ≤ τ → ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (|τ| * (P.Υ : ℝ) * N) := by
    intro τ hτ
    simpa [C, sAlpha, N] using norm_additiveResidual_le P H p hp h_order hΥ τ hτ
  have hintegral (t : ℝ) (ht : 0 ≤ t) :
      ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) =
        (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (P.Υ : ℝ) * N) *
          (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) :=
    intervalIntegral_const_mul_abs_pow_div_factorial_mul C (Real.exp (2 * t * (P.Υ : ℝ) * N)) p t ht
  intro t ht
  calc
    ‖P.eval H t - exp (t • S)‖
        = ‖∫ τ in 0..t, exp ((t - τ) • S) * additiveResidual P H τ‖ := by
            rw [eval_sub_exp_eq_integral_residual P H t]
    _ ≤ ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) := by
            have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
                ‖exp ((t - τ) • S) * additiveResidual P H τ‖ ≤
                  C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) := by
              intro τ hτ
              have hτpos : 0 ≤ τ := le_of_lt hτ.1
              have hexpS : ‖exp ((t - τ) • S)‖ ≤ Real.exp (|t - τ| * N) := by
                calc
                  ‖exp ((t - τ) • S)‖ ≤ Real.exp (‖(t - τ) • S‖) := norm_exp_le _
                  _ = Real.exp (|t - τ| * ‖S‖) := by rw [norm_smul, Real.norm_eq_abs]
                  _ ≤ Real.exp (|t - τ| * N) :=
                      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS_le (abs_nonneg _))
              have hres : ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
                  Real.exp (|τ| * (P.Υ : ℝ) * N) := hR3 τ hτpos
              have harg : |t - τ| * N + |τ| * (P.Υ : ℝ) * N ≤ 2 * t * (P.Υ : ℝ) * N := by
                have hN : 0 ≤ N := by dsimp [N]; exact sum_nonneg (fun γ _ => norm_nonneg _)
                have hΥR : 1 ≤ (P.Υ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hΥ)
                have harg' : |t - τ| + |τ| * (P.Υ : ℝ) ≤ 2 * t * (P.Υ : ℝ) := by
                  rw [abs_of_nonneg hτpos, abs_of_nonneg (sub_nonneg.mpr hτ.2)]
                  nlinarith [hτ.1.le, hτ.2, hΥR, ht]
                nlinarith [mul_le_mul_of_nonneg_left harg' hN]
              calc
                ‖exp ((t - τ) • S) * additiveResidual P H τ‖
                    ≤ ‖exp ((t - τ) • S)‖ * ‖additiveResidual P H τ‖ := norm_mul_le _ _
                _ ≤ Real.exp (|t - τ| * N) * (C * |τ| ^ p / (Nat.factorial p : ℝ) *
                      Real.exp (|τ| * (P.Υ : ℝ) * N)) :=
                      mul_le_mul hexpS hres (norm_nonneg _) (Real.exp_pos _).le
                _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * (Real.exp (|t - τ| * N) *
                      Real.exp (|τ| * (P.Υ : ℝ) * N)) := by ring
                _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|t - τ| * N +
                      |τ| * (P.Υ : ℝ) * N) := by rw [← Real.exp_add]
                _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) := by
                      refine mul_le_mul_of_nonneg_left ?_ ?_
                      · exact Real.exp_le_exp.mpr harg
                      · have hC_nonneg : 0 ≤ C := by
                          dsimp [C, sAlpha]
                          exact mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
                            (sum_nonneg (fun γ _ => αCommConj_nonneg _ _ _))
                        exact div_nonneg (mul_nonneg hC_nonneg (pow_nonneg (abs_nonneg τ) p))
                          (Nat.cast_nonneg _)
            have hg_cont : Continuous (fun τ : ℝ => C * |τ| ^ p / (Nat.factorial p : ℝ) *
                Real.exp (2 * t * (P.Υ : ℝ) * N)) := by fun_prop
            exact intervalIntegral.norm_integral_le_of_norm_le ht
              (by filter_upwards with τ hτ; exact hpoint τ hτ) (hg_cont.intervalIntegrable 0 t)
    _ = (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (P.Υ : ℝ) * N) *
          (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := hintegral t ht
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (P.Υ : ℝ) * N) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                Real.exp (2 * t * (P.Υ : ℝ) * N) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (P.Υ : ℝ) * N) *
                  (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  = (C / (Nat.factorial p : ℝ)) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                      Real.exp (2 * t * (P.Υ : ℝ) * N)) := by ring
              _ ≤ (2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                    Real.exp (2 * t * (P.Υ : ℝ) * N)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
                    Real.exp (2 * t * (P.Υ : ℝ) * N) := by ring

/-- `thm:trotter_error_comm_scaling` (general branch): the commuting-scaling bound as `t → ∞`. -/
theorem trotter_error_comm_scaling (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ) :
    (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1) *
        Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1))) (Real.exp_pos _).le)]
  calc
    ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
            Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) :=
            trotter_error_bound_comm_scaling P H p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) *
          (αComm p H * t ^ (p + 1) * Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by ring

/-! ### R4: commuting-scaling bound and Trotter number -/

/-- `eq:trotter_error_comm_scaling_bound` (anti-Hermitian): the explicit pointwise commuting-scaling
bound, valid for all `t ≥ 0`. -/
theorem trotter_error_bound_comm_scaling_of_skewAdjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin P.Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < P.Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
  let S : 𝔸 := ∑ γ : Fin P.Γ, H γ
  let sAlpha : ℝ := ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (P.Υ : ℝ) * sAlpha
  have hS_skew : star S = -S := sum_skewAdjoint H h_skew
  have hR3 : ∀ τ, ‖additiveKernel P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) := by
    intro τ
    simpa [C, sAlpha] using norm_additiveKernel_le_of_skewAdjoint P H h_skew p hp h_order hΥ τ
  have hintegral (t : ℝ) (ht : 0 ≤ t) :
      ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) =
        (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) :=
    intervalIntegral_const_mul_abs_pow_div_factorial C p t ht
  intro t ht
  calc
    ‖P.eval H t - exp (t • S)‖
        = ‖exp (t • S) * ∫ τ in 0..t, (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ := by
            rw [eval_sub_exp_eq_exp_mul_integral P H t]
    _ ≤ ‖exp (t • S)‖ * ‖∫ τ in 0..t, (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ :=
            norm_mul_le _ _
    _ = ‖∫ τ in 0..t, (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ := by
            rw [norm_exp_smul_of_skewAdjoint hS_skew t, one_mul]
    _ ≤ ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) := by
            have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
                ‖(exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ ≤
                  C * |τ| ^ p / (Nat.factorial p : ℝ) := by
              intro τ hτ
              have hfac : ‖exp ((-τ) • S) * P.eval H τ‖ ≤ 1 := by
                calc
                  ‖exp ((-τ) • S) * P.eval H τ‖ ≤ ‖exp ((-τ) • S)‖ * ‖P.eval H τ‖ := norm_mul_le _ _
                  _ = 1 * ‖P.eval H τ‖ := by rw [norm_exp_smul_of_skewAdjoint hS_skew (-τ)]
                  _ = ‖P.eval H τ‖ := one_mul _
                  _ ≤ 1 := norm_eval_le_one_of_skew P H h_skew τ
              calc
                ‖(exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖
                    ≤ ‖exp ((-τ) • S) * P.eval H τ‖ * ‖additiveKernel P H τ‖ := norm_mul_le _ _
                _ ≤ 1 * ‖additiveKernel P H τ‖ := mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
                _ = ‖additiveKernel P H τ‖ := one_mul _
                _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) := hR3 τ
            have hg_cont : Continuous (fun τ : ℝ => C * |τ| ^ p / (Nat.factorial p : ℝ)) := by
              fun_prop
            exact intervalIntegral.norm_integral_le_of_norm_le ht
              (by filter_upwards with τ hτ; exact hpoint τ hτ) (hg_cont.intervalIntegrable 0 t)
    _ = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := hintegral t ht
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ t ^ (p + 1) / ((p + 1 : ℕ) : ℝ) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              C / (Nat.factorial p : ℝ) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  ≤ 2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H *
                      (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
                      ring

/-- `thm:trotter_error_comm_scaling` (anti-Hermitian): the commuting-scaling bound as `t → ∞`. -/
theorem trotter_error_comm_scaling_of_skewAdjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin P.Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < P.Υ) :
    (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1)))]
  calc
    ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) :=
            trotter_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) * (αComm p H * t ^ (p + 1)) := by ring

/-- `cor:trotter_number_comm_scaling`: for anti-Hermitian summands, the `r`-step Trotter error with
the commuting-scaling bound decays as `O(r^{-p})` as `r → ∞`. -/
theorem trotter_number_comm_scaling (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ) (t : ℝ) (ht : 0 ≤ t) :
    (fun r : ℕ => ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ : Fin P.Γ, H γ)‖) =O[Filter.atTop]
      (fun r : ℕ => ((r : ℝ) ^ p)⁻¹) := by
  let S : 𝔸 := ∑ γ : Fin P.Γ, H γ
  let α : ℝ := αComm p H
  have hS_skew : star S = -S := sum_skewAdjoint H h_skew
  have hα : 0 ≤ α := by dsimp [α]; exact αComm_nonneg p H
  have hO' : (fun r : ℕ => ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)‖) =O[Filter.atTop]
      (fun r : ℕ => α * (t / (r : ℝ)) ^ (p + 1)) := by
    refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    have hrpos : 0 < (r : ℝ) := mod_cast (Nat.lt_of_lt_of_le zero_lt_one hr)
    have hnonneg_arg : 0 ≤ α * (t / (r : ℝ)) ^ (p + 1) :=
      mul_nonneg hα (pow_nonneg (div_nonneg ht (le_of_lt hrpos)) (p + 1))
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hnonneg_arg]
    simpa [S, α] using
      (trotter_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp h_order hΥ
        (t / (r : ℝ)) (div_nonneg ht (le_of_lt hrpos))).trans_eq (by push_cast; ring)
  obtain ⟨C, hC⟩ := hO'.bound
  refine IsBigO.of_bound (C * α * t ^ (p + 1)) ?_
  filter_upwards [hC, (Filter.eventually_ge_atTop 1)] with r hr_le hr1
  have hrpos_nat : 0 < r := Nat.lt_of_lt_of_le zero_lt_one hr1
  have hrpos : 0 < (r : ℝ) := mod_cast hrpos_nat
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hr_nonneg : 0 ≤ (r : ℝ) := le_of_lt hrpos
  have hA_le : ‖P.eval H (t / (r : ℝ))‖ ≤ 1 :=
    norm_eval_le_one_of_skew P H h_skew (t / (r : ℝ))
  have hB_le : ‖exp ((t / (r : ℝ)) • S)‖ ≤ 1 :=
    le_of_eq (norm_exp_smul_of_skewAdjoint hS_skew (t / (r : ℝ)))
  have hnonneg_arg : 0 ≤ α * (t / (r : ℝ)) ^ (p + 1) :=
    mul_nonneg hα (pow_nonneg (div_nonneg ht hr_nonneg) (p + 1))
  have hr_le' : ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)‖ ≤
      C * ‖α * (t / (r : ℝ)) ^ (p + 1)‖ := by
    rwa [← Real.norm_of_nonneg (norm_nonneg (P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)))]
  rw [Real.norm_of_nonneg (norm_nonneg ((P.eval H (t / (r : ℝ))) ^ r - exp (t • S)))]
  calc
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • S)‖
        = ‖(P.eval H (t / (r : ℝ))) ^ r - exp ((t / (r : ℝ)) • S) ^ r‖ := by
            rw [exp_smul_eq_pow_of_div S t hrpos_nat]
    _ ≤ (r : ℝ) * ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)‖ :=
            norm_pow_sub_pow_le_of_norm_le_one (P.eval H (t / (r : ℝ)))
              (exp ((t / (r : ℝ)) • S)) r hA_le hB_le
    _ ≤ (r : ℝ) * (C * ‖α * (t / (r : ℝ)) ^ (p + 1)‖) :=
            mul_le_mul_of_nonneg_left hr_le' hr_nonneg
    _ = C * α * t ^ (p + 1) * ‖((r : ℝ) ^ p)⁻¹‖ := by
            rw [Real.norm_of_nonneg hnonneg_arg,
              Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hr_nonneg p))]
            calc
              (r : ℝ) * (C * (α * (t / (r : ℝ)) ^ (p + 1)))
                  = C * (α * ((r : ℝ) * (t / (r : ℝ)) ^ (p + 1))) := by ring
              _ = C * (α * (t ^ (p + 1) * ((r : ℝ) ^ p)⁻¹)) := by
                      rw [natCast_mul_pow_div_pow_succ t r p hr_ne]
              _ = C * α * t ^ (p + 1) * ((r : ℝ) ^ p)⁻¹ := by ring

/-! ### R3g-multiplicative: the multiplicative error commuting-scaling bound -/

/-- The multiplicative error as an integral of the additive residual (rep.tex:115-123):
`ℳ(t) = ∫₀ᵗ e^{-τH} ℛ(τ) dτ`. Follows from `errorType_multiplicative` together with the additive
representation `𝒮(t) − e^{tH} = e^{tH} ∫₀ᵗ e^{-τH} ℛ(τ) dτ`. -/
lemma multiplicativeError_eq_integral_residual (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (t : ℝ) :
    multiplicativeError P H t =
      ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ := by
  have hM : P.eval H t - exp (t • (∑ γ : Fin P.Γ, H γ)) =
      exp (t • (∑ γ : Fin P.Γ, H γ)) * multiplicativeError P H t := by
    rw [errorType_multiplicative P H t]
    noncomm_ring
  have hR : P.eval H t - exp (t • (∑ γ : Fin P.Γ, H γ)) =
      exp (t • (∑ γ : Fin P.Γ, H γ)) *
        ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ := by
    rw [eval_sub_exp_eq_exp_mul_integral P H t]
    congr 1
    refine intervalIntegral.integral_congr_uIoo ?_
    intro τ _
    change exp ((-τ) • (∑ γ : Fin P.Γ, H γ)) * P.eval H τ * additiveKernel P H τ =
      exp ((-τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ
    rw [mul_assoc, additiveResidual_eq_eval_mul_kernel P H τ]
  have he : exp ((-t) • (∑ γ : Fin P.Γ, H γ)) * exp (t • (∑ γ : Fin P.Γ, H γ)) = 1 := by
    simpa [neg_smul] using exp_neg_mul_self (t • (∑ γ : Fin P.Γ, H γ))
  calc
    multiplicativeError P H t
        = exp ((-t) • (∑ γ : Fin P.Γ, H γ)) *
            (exp (t • (∑ γ : Fin P.Γ, H γ)) * multiplicativeError P H t) := by
            rw [← mul_assoc, he, one_mul]
    _ = exp ((-t) • (∑ γ : Fin P.Γ, H γ)) * (P.eval H t - exp (t • (∑ γ : Fin P.Γ, H γ))) := by
            rw [hM.symm]
    _ = exp ((-t) • (∑ γ : Fin P.Γ, H γ)) * (exp (t • (∑ γ : Fin P.Γ, H γ)) *
            ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ) := by
            rw [hR]
    _ = ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin P.Γ, H γ)) * additiveResidual P H τ := by
            rw [← mul_assoc, he, one_mul]

/-- `thm:trotter_error_comm_scaling` (general branch, multiplicative): the explicit pointwise
commuting-scaling bound for the multiplicative error with exponential prefactor
`exp (2 t Υ Σ ‖H_γ‖)`. -/
theorem multiplicative_error_bound_comm_scaling (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖multiplicativeError P H t‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  let S : 𝔸 := ∑ γ : Fin P.Γ, H γ
  let N : ℝ := ∑ γ : Fin P.Γ, ‖H γ‖
  let sAlpha : ℝ := ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (P.Υ : ℝ) * sAlpha
  have hS_le : ‖S‖ ≤ N := by
    dsimp [S, N]
    exact norm_sum_le univ H
  have hres : ∀ τ, 0 ≤ τ → ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (|τ| * (P.Υ : ℝ) * N) := by
    intro τ hτ
    simpa [C, sAlpha, N] using norm_additiveResidual_le P H p hp h_order hΥ τ hτ
  have hintegral (t : ℝ) (ht : 0 ≤ t) :
      ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) =
        (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (P.Υ : ℝ) * N) *
          (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) :=
    intervalIntegral_const_mul_abs_pow_div_factorial_mul C (Real.exp (2 * t * (P.Υ : ℝ) * N)) p t ht
  intro t ht
  calc
    ‖multiplicativeError P H t‖
        = ‖∫ τ in 0..t, exp ((-τ) • S) * additiveResidual P H τ‖ := by
            rw [multiplicativeError_eq_integral_residual P H t]
    _ ≤ ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) := by
            have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
                ‖exp ((-τ) • S) * additiveResidual P H τ‖ ≤
                  C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) := by
              intro τ hτ
              have hτpos : 0 ≤ τ := le_of_lt hτ.1
              have hexpS : ‖exp ((-τ) • S)‖ ≤ Real.exp (|τ| * N) := by
                calc
                  ‖exp ((-τ) • S)‖ ≤ Real.exp (‖(-τ) • S‖) := norm_exp_le _
                  _ = Real.exp (|τ| * ‖S‖) := by rw [norm_smul, Real.norm_eq_abs, abs_neg]
                  _ ≤ Real.exp (|τ| * N) :=
                      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS_le (abs_nonneg _))
              have hresτ : ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
                  Real.exp (|τ| * (P.Υ : ℝ) * N) := hres τ hτpos
              have harg : |τ| * N + |τ| * (P.Υ : ℝ) * N ≤ 2 * t * (P.Υ : ℝ) * N := by
                have hN : 0 ≤ N := by dsimp [N]; exact sum_nonneg (fun γ _ => norm_nonneg _)
                have hΥR : 1 ≤ (P.Υ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hΥ)
                have harg' : |τ| + |τ| * (P.Υ : ℝ) ≤ 2 * t * (P.Υ : ℝ) := by
                  rw [abs_of_nonneg hτpos]
                  nlinarith [hτ.1.le, hτ.2, hΥR, ht]
                nlinarith [mul_le_mul_of_nonneg_left harg' hN]
              calc
                ‖exp ((-τ) • S) * additiveResidual P H τ‖
                    ≤ ‖exp ((-τ) • S)‖ * ‖additiveResidual P H τ‖ := norm_mul_le _ _
                _ ≤ Real.exp (|τ| * N) * (C * |τ| ^ p / (Nat.factorial p : ℝ) *
                      Real.exp (|τ| * (P.Υ : ℝ) * N)) :=
                      mul_le_mul hexpS hresτ (norm_nonneg _) (Real.exp_pos _).le
                _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * (Real.exp (|τ| * N) *
                      Real.exp (|τ| * (P.Υ : ℝ) * N)) := by ring
                _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * N +
                      |τ| * (P.Υ : ℝ) * N) := by rw [← Real.exp_add]
                _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (P.Υ : ℝ) * N) := by
                      refine mul_le_mul_of_nonneg_left ?_ ?_
                      · exact Real.exp_le_exp.mpr harg
                      · have hC_nonneg : 0 ≤ C := by
                          dsimp [C, sAlpha]
                          exact mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
                            (sum_nonneg (fun γ _ => αCommConj_nonneg _ _ _))
                        exact div_nonneg (mul_nonneg hC_nonneg (pow_nonneg (abs_nonneg τ) p))
                          (Nat.cast_nonneg _)
            have hg_cont : Continuous (fun τ : ℝ => C * |τ| ^ p / (Nat.factorial p : ℝ) *
                Real.exp (2 * t * (P.Υ : ℝ) * N)) := by fun_prop
            exact intervalIntegral.norm_integral_le_of_norm_le ht
              (by filter_upwards with τ hτ; exact hpoint τ hτ) (hg_cont.intervalIntegrable 0 t)
    _ = (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (P.Υ : ℝ) * N) *
          (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := hintegral t ht
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (P.Υ : ℝ) * N) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                Real.exp (2 * t * (P.Υ : ℝ) * N) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (P.Υ : ℝ) * N) *
                  (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  = (C / (Nat.factorial p : ℝ)) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                      Real.exp (2 * t * (P.Υ : ℝ) * N)) := by ring
              _ ≤ (2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                    Real.exp (2 * t * (P.Υ : ℝ) * N)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
                    Real.exp (2 * t * (P.Υ : ℝ) * N) := by ring

/-- `thm:trotter_error_comm_scaling` (general branch, multiplicative): the multiplicative-error
commuting-scaling bound as `t → ∞`. -/
theorem multiplicative_error_comm_scaling (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < P.Υ) :
    (fun t : ℝ ↦ ‖multiplicativeError P H t‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1) *
        Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1))) (Real.exp_pos _).le)]
  calc
    ‖multiplicativeError P H t‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
            Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) :=
            multiplicative_error_bound_comm_scaling P H p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) *
          (αComm p H * t ^ (p + 1) * Real.exp (2 * t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by ring

/-- `thm:trotter_error_comm_scaling` (anti-Hermitian branch, multiplicative): the multiplicative
error pointwise commuting-scaling bound, valid for all `t ≥ 0` (no exponential prefactor). -/
theorem multiplicative_error_bound_comm_scaling_of_skewAdjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin P.Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < P.Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖multiplicativeError P H t‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
  let S : 𝔸 := ∑ γ : Fin P.Γ, H γ
  let sAlpha : ℝ := ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (P.Υ : ℝ) * sAlpha
  have hS_skew : star S = -S := sum_skewAdjoint H h_skew
  have hkernel : ∀ τ, ‖additiveKernel P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) := by
    intro τ
    simpa [C, sAlpha] using norm_additiveKernel_le_of_skewAdjoint P H h_skew p hp h_order hΥ τ
  have hintegral (t : ℝ) (ht : 0 ≤ t) :
      ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) =
        (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) :=
    intervalIntegral_const_mul_abs_pow_div_factorial C p t ht
  intro t ht
  calc
    ‖multiplicativeError P H t‖
        = ‖∫ τ in 0..t, exp ((-τ) • S) * additiveResidual P H τ‖ := by
            rw [multiplicativeError_eq_integral_residual P H t]
    _ = ‖∫ τ in 0..t, (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ := by
            congr 1
            refine intervalIntegral.integral_congr_uIoo ?_
            intro τ _
            change exp ((-τ) • S) * additiveResidual P H τ =
              (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ
            rw [additiveResidual_eq_eval_mul_kernel P H τ, ← mul_assoc]
    _ ≤ ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) := by
            have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
                ‖(exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ ≤
                  C * |τ| ^ p / (Nat.factorial p : ℝ) := by
              intro τ hτ
              have hfac : ‖exp ((-τ) • S) * P.eval H τ‖ ≤ 1 := by
                calc
                  ‖exp ((-τ) • S) * P.eval H τ‖ ≤ ‖exp ((-τ) • S)‖ * ‖P.eval H τ‖ := norm_mul_le _ _
                  _ = 1 * ‖P.eval H τ‖ := by rw [norm_exp_smul_of_skewAdjoint hS_skew (-τ)]
                  _ = ‖P.eval H τ‖ := one_mul _
                  _ ≤ 1 := norm_eval_le_one_of_skew P H h_skew τ
              calc
                ‖(exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖
                    ≤ ‖exp ((-τ) • S) * P.eval H τ‖ * ‖additiveKernel P H τ‖ := norm_mul_le _ _
                _ ≤ 1 * ‖additiveKernel P H τ‖ := mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
                _ = ‖additiveKernel P H τ‖ := one_mul _
                _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) := hkernel τ
            have hg_cont : Continuous (fun τ : ℝ => C * |τ| ^ p / (Nat.factorial p : ℝ)) := by
              fun_prop
            exact intervalIntegral.norm_integral_le_of_norm_le ht
              (by filter_upwards with τ hτ; exact hpoint τ hτ) (hg_cont.intervalIntegrable 0 t)
    _ = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := hintegral t ht
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ t ^ (p + 1) / ((p + 1 : ℕ) : ℝ) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              C / (Nat.factorial p : ℝ) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  ≤ 2 * (P.Υ : ℝ) ^ (p + 1) * αComm p H *
                      (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
                      ring

/-- `thm:trotter_error_comm_scaling` (anti-Hermitian branch, multiplicative): the
multiplicative-error commuting-scaling bound as `t → ∞`. -/
theorem multiplicative_error_comm_scaling_of_skewAdjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin P.Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < P.Υ) :
    (fun t : ℝ ↦ ‖multiplicativeError P H t‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1)))]
  calc
    ‖multiplicativeError P H t‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) :=
            multiplicative_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (P.Υ : ℝ) ^ (p + 1)) * (αComm p H * t ^ (p + 1)) := by ring

end TrotterError
