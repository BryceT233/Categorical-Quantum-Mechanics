/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.CommutatorExpansion
public import CQM1.TrotterError.OrderCondition

import CQM1.TrotterError.ListProd

/-!
# Commutator scaling bridge

The bridge from the additive kernel `𝒯(τ)` to the commutator expansion:
`additiveKernel = Σ multiConj − multiConj` (`papers/rep.tex` lines 5-12) and the
order-condition cancellation `𝒯 = Σ commutatorRemainder − commutatorRemainder`
(`papers/theory.tex` lines 251-266). These are shared by the anti-Hermitian and
general-operator branches of `thm:trotter_error_comm_scaling`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open TrotterError.List
open scoped Topology BigOperators algebraMap

/-! ### M5 bridge: `additiveKernel` is a sum of `multiConj` at `-τ` -/

/-- A `multiConj` whose `A` sequence is `gen ∘ l.get` equals the `List.prod`-form
`(l.reverse.map (exp (τ • gen ·))).prod * B * (l.map (exp (-τ • gen ·))).prod`. -/
lemma multiConj_ofFn_get {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {ι : Type*}
    (l : List ι) (gen : ι → 𝔸) (B : 𝔸) (τ : ℝ) :
    multiConj (fun k : Fin l.length => gen (l.get k)) B τ =
      (l.reverse.map (fun j => exp (τ • gen j))).prod * B *
        (l.map (fun j => exp (-τ • gen j))).prod := by
  unfold multiConj
  rw [ofFn_get_comp l (fun j => exp (τ • gen j)), ofFn_get_comp l (fun j => exp (-τ • gen j)),
    List.map_reverse]

/-- Each additive-kernel summand is the `multiConj` of its suffix generators at `-τ`
(rep.tex:9, the `(υ,γ)`-th term of `𝒯`). -/
lemma additiveKernel_summand_eq_multiConj (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (τ : ℝ) :
    invStrictSuffixFactorProd P H i τ * P.generator H i * strictSuffixFactorProd P H i τ
      = multiConj (suffixGenerators P H i) (P.generator H i) (-τ) := by
  unfold invStrictSuffixFactorProd strictSuffixFactorProd factorProdOver suffixGenerators
  rw [multiConj_ofFn_get (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1))
    (fun j => P.generator H j) (P.generator H i) (-τ)]
  simp [ProductFormulaData.evalFactor]

/-- The full-product term of `additiveKernel` is the `multiConj` of all generators at `-τ`
(rep.tex:10). -/
lemma additiveKernel_full_eq_multiConj (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (τ : ℝ) :
    factorProdOver P H (-τ) (P.evalIndexList.reverse) * (∑ γ : Fin P.Γ, H γ) *
        factorProdOver P H τ (P.evalIndexList)
      = multiConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) (-τ) := by
  unfold factorProdOver orderedGenerators
  rw [multiConj_ofFn_get P.evalIndexList (fun j => P.generator H j) (∑ γ : Fin P.Γ, H γ) (-τ)]
  simp [ProductFormulaData.evalFactor]

/-- `additiveKernel P H τ = Σ_i multiConj A_i (gen_i) (-τ) − multiConj A_all (ΣH) (-τ)`
(rep.tex:5-12, the bridge to the commutator expansion). -/
lemma additiveKernel_eq_sum_multiConj (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (τ : ℝ) :
    additiveKernel P H τ =
      (∑ i : Fin P.Υ × Fin P.Γ,
        multiConj (suffixGenerators P H i) (P.generator H i) (-τ))
        - multiConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) (-τ) := by
  unfold additiveKernel
  congr 1
  · apply sum_congr rfl
    intro i _
    exact additiveKernel_summand_eq_multiConj P H i τ
  · exact additiveKernel_full_eq_multiConj P H τ

/-! ### R2: order-condition cancellation -/

/-- The commutator remainder `𝒞(τ)` is `O(τ^p)` as `τ → 0` (the exponential factor tends to
`1`). -/
lemma commutatorRemainder_isBigO {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) :
    (fun τ : ℝ => ‖commutatorRemainder A B p τ‖) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
  let g : ℝ → ℝ := fun τ => αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
    Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖)
  have hle : (fun τ : ℝ => ‖commutatorRemainder A B p τ‖) =O[𝓝 (0 : ℝ)] g := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with τ
    have hg_nonneg : 0 ≤ g τ := by
      dsimp [g]
      exact mul_nonneg (div_nonneg (mul_nonneg (αCommConj_nonneg A B p)
        (pow_nonneg (abs_nonneg τ) p)) (Nat.cast_nonneg _)) (le_of_lt (Real.exp_pos _))
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hg_nonneg, one_mul]
    simpa [g] using norm_commutatorRemainder_le A B p τ
  have hpow : (fun τ : ℝ => |τ| ^ p) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with τ
    rw [one_mul]
    exact le_of_eq (by
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg τ) p), Real.norm_eq_abs (τ ^ p),
        abs_pow τ p])
  have hexp : (fun τ : ℝ => Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖)) =O[𝓝 (0 : ℝ)]
      (fun _ => (1 : ℝ)) := by
    simpa [Real.norm_eq_abs] using
      (isBigO_norm_one_of_continuous (F := fun τ : ℝ => Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖))
        (by fun_prop))
  have hg : g =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
    dsimp [g]
    have hprod : (fun τ : ℝ => |τ| ^ p * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖))
        =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p * (1 : ℝ)) := hpow.mul hexp
    have hprod' : (fun τ : ℝ => |τ| ^ p * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖))
        =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) :=
      hprod.congr_right (fun τ => by simp)
    exact (hprod'.const_mul_left (αCommConj A B p / (Nat.factorial p : ℝ))).congr_left
      (fun τ => by ring)
  exact hle.trans hg

/-- `thm:trotter_error_order_cond` cancellation step (theory.tex:258-264): under the order condition
`P.IsOrderOf p H`, the additive kernel is exactly the difference of the commutator remainders. -/
lemma additiveKernel_eq_commutatorRemainder_sum (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) :
    additiveKernel P H τ =
      (∑ i : Fin P.Υ × Fin P.Γ,
        commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
        - commutatorRemainder (orderedGenerators P H) (∑ γ, H γ) p (-τ) := by
  let T : ℕ → 𝔸 := fun j =>
    (∑ i : Fin P.Υ × Fin P.Γ, conjCoeff (suffixGenerators P H i) (P.generator H i) j)
      - conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j
  let poly : ℝ → 𝔸 := fun σ => ∑ j ∈ range p, T j * (σ ^ j : 𝔸)
  let remSum : ℝ → 𝔸 := fun σ =>
    ∑ i : Fin P.Υ × Fin P.Γ, commutatorRemainder (suffixGenerators P H i) (P.generator H i) p σ
  let remAll : ℝ → 𝔸 := fun σ =>
    commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p σ
  have h_rearrange (τ : ℝ) :
      (∑ i : Fin P.Υ × Fin P.Γ, ((∑ j ∈ range p,
            conjCoeff (suffixGenerators P H i) (P.generator H i) j * (τ ^ j : 𝔸))
          + commutatorRemainder (suffixGenerators P H i) (P.generator H i) p τ))
        - ((∑ j ∈ range p,
            conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j * (τ ^ j : 𝔸))
          + commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p τ)
        = (∑ j ∈ range p, T j * (τ ^ j : 𝔸))
          + (∑ i : Fin P.Υ × Fin P.Γ,
              commutatorRemainder (suffixGenerators P H i) (P.generator H i) p τ)
          - commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p τ := by
    dsimp [T]
    rw [sum_add_distrib]
    have hpoly : (∑ i : Fin P.Υ × Fin P.Γ, ∑ j ∈ range p,
          conjCoeff (suffixGenerators P H i) (P.generator H i) j * (τ ^ j : 𝔸))
        - (∑ j ∈ range p,
          conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j * (τ ^ j : 𝔸))
        = ∑ j ∈ range p,
          ((∑ i : Fin P.Υ × Fin P.Γ, conjCoeff (suffixGenerators P H i) (P.generator H i) j)
            - conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j) * (τ ^ j : 𝔸) := by
      rw [sum_comm, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      rw [← sum_mul, sub_mul]
    calc
      (∑ i : Fin P.Υ × Fin P.Γ, ∑ j ∈ range p,
          conjCoeff (suffixGenerators P H i) (P.generator H i) j * (τ ^ j : 𝔸))
        + (∑ i : Fin P.Υ × Fin P.Γ,
              commutatorRemainder (suffixGenerators P H i) (P.generator H i) p τ)
        - ((∑ j ∈ range p,
          conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j * (τ ^ j : 𝔸))
        + commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p τ)
          = ((∑ i : Fin P.Υ × Fin P.Γ, ∑ j ∈ range p,
              conjCoeff (suffixGenerators P H i) (P.generator H i) j * (τ ^ j : 𝔸))
            - (∑ j ∈ range p,
              conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j * (τ ^ j : 𝔸)))
            + (∑ i : Fin P.Υ × Fin P.Γ,
              commutatorRemainder (suffixGenerators P H i) (P.generator H i) p τ)
            - commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p τ := by abel
      _ = (∑ j ∈ range p,
            ((∑ i : Fin P.Υ × Fin P.Γ, conjCoeff (suffixGenerators P H i) (P.generator H i) j)
              - conjCoeff (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) j) * (τ ^ j : 𝔸))
          + (∑ i : Fin P.Υ × Fin P.Γ,
              commutatorRemainder (suffixGenerators P H i) (P.generator H i) p τ)
          - commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p τ := by rw [hpoly]
  have h_expand : ∀ τ : ℝ, additiveKernel P H τ = poly (-τ) + remSum (-τ) - remAll (-τ) := by
    intro τ
    dsimp [poly, remSum, remAll]
    rw [additiveKernel_eq_sum_multiConj P H τ]
    conv_lhs =>
      rw [sum_congr rfl (fun i _ =>
        commutatorExpansion_conj (suffixGenerators P H i) (P.generator H i) p (-τ) hp)]
      rw [commutatorExpansion_conj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ) hp]
    exact h_rearrange (-τ)
  have hkernel : (fun τ : ℝ => ‖additiveKernel P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) :=
    (errorOrderCond_additive_iff P p H).mp h_order
  have hrem_i : ∀ i : Fin P.Υ × Fin P.Γ,
      (fun τ : ℝ => ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
        =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
    intro i
    have hcomp := (commutatorRemainder_isBigO (suffixGenerators P H i)
      (P.generator H i) p).comp_tendsto tendsto_neg_nhds_zero
    exact hcomp.trans (neg_pow_isBigO p)
  have hremSum : (fun τ : ℝ => ‖∑ i : Fin P.Υ × Fin P.Γ,
      commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
      =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
    have htri : (fun τ : ℝ => ‖∑ i : Fin P.Υ × Fin P.Γ,
        commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
        =O[𝓝 (0 : ℝ)] (fun τ : ℝ => ∑ i : Fin P.Υ × Fin P.Γ,
        ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards with τ
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)), one_mul]
      exact norm_sum_le univ
        (fun i => commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
    have hsum : (fun τ : ℝ => ∑ i : Fin P.Υ × Fin P.Γ,
        ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
        =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
      simpa [Finset.sum_fn] using IsBigO.sum (s := (univ : Finset (Fin P.Υ × Fin P.Γ)))
        (fun i _ => hrem_i i)
    exact htri.trans hsum
  have hremAll :
      (fun τ : ℝ => ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ)‖)
      =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
    have hcomp := (commutatorRemainder_isBigO (orderedGenerators P H)
      (∑ γ : Fin P.Γ, H γ) p).comp_tendsto tendsto_neg_nhds_zero
    exact hcomp.trans (neg_pow_isBigO p)
  have hpoly_neg : (fun τ : ℝ => ‖poly (-τ)‖) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
    have htri : (fun τ : ℝ => ‖poly (-τ)‖) =O[𝓝 (0 : ℝ)]
        (fun τ : ℝ => ‖additiveKernel P H τ‖ + ‖remSum (-τ)‖ + ‖remAll (-τ)‖) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards with τ
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg
          (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)),
        one_mul]
      have hpoly_pt : poly (-τ) = additiveKernel P H τ - remSum (-τ) + remAll (-τ) := by
        have h := h_expand τ
        calc
          poly (-τ) = (poly (-τ) + remSum (-τ) - remAll (-τ)) - remSum (-τ) + remAll (-τ) := by abel
          _ = additiveKernel P H τ - remSum (-τ) + remAll (-τ) := by rw [h]
      calc
        ‖poly (-τ)‖ = ‖additiveKernel P H τ - remSum (-τ) + remAll (-τ)‖ := by
              rw [hpoly_pt]
        _ ≤ ‖additiveKernel P H τ - remSum (-τ)‖ + ‖remAll (-τ)‖ := norm_add_le _ _
        _ ≤ ‖additiveKernel P H τ‖ + ‖remSum (-τ)‖ + ‖remAll (-τ)‖ := by
              gcongr
              exact norm_sub_le _ _
    have hsum : (fun τ : ℝ => ‖additiveKernel P H τ‖ + ‖remSum (-τ)‖ + ‖remAll (-τ)‖)
        =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := (hkernel.add hremSum).add hremAll
    exact htri.trans hsum
  have hpoly_big : (fun σ : ℝ => ‖poly σ‖) =O[𝓝 (0 : ℝ)] (fun σ : ℝ => σ ^ p) := by
    have hcomp := hpoly_neg.comp_tendsto tendsto_neg_nhds_zero
    exact (hcomp.trans (neg_pow_isBigO p)).congr_left (fun σ => by simp)
  have hT_zero : ∀ j : ℕ, j < p → T j = 0 :=
    (polynomial_isBigO_iff_coeffs_zero p T).mp hpoly_big
  have hpoly_zero : poly = 0 := by
    funext σ
    dsimp [poly]
    apply sum_eq_zero
    intro j hj
    simp [hT_zero j (mem_range.mp hj)]
  calc
    additiveKernel P H τ = poly (-τ) + remSum (-τ) - remAll (-τ) := h_expand τ
    _ = remSum (-τ) - remAll (-τ) := by simp [hpoly_zero]
    _ = (∑ i : Fin P.Υ × Fin P.Γ,
        commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
        - commutatorRemainder (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p (-τ) := rfl

end TrotterError
