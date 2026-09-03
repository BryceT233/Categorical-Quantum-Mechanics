/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.Commutator
public import CQM1.TrotterError.Calculus

import CQM1.TrotterError.ListProd

/-!
# Product formulas

We define the general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of arXiv:1912.08854 (§2.3) and the associated
`p`-th order condition.

Following the paper's convention (`papers/prelim.tex` §2.1), the product
`∏_{γ=1}^{Γ} A_γ` denotes `A_Γ ⋯ A_2 A_1`, i.e. increasing indices from right to
left; we implement this with a reversed `List.finRange`. Since the factors
`e^{t a H}` do not commute, the product is taken with `List.prod` (ordered) rather
than `prod` (commutative) or `noncommProd` (which requires pairwise
commutativity).

## Main definitions

* `ProductFormulaData`: the data of a product formula `𝒮(t)` (stages `Υ`, summands `Γ`,
  coefficients `coeff`, permutations `perm`).
* `evalFactor`, `eval`, `generator`: the single factor, the full product, and the generator
  `a_{(υ,γ)} H_{π_υ(γ)}`.
* `evalIndexList`: the flattened factor-index order used by `eval`.
* `orderedSummands`, `orderedSummandsEval`, `reverseStages`: the permuted summands and the
  stage-reversal structure map.
* `orderedGenerators`, `suffixGenerators`, `fullGenerators`: the generators of the product
  formula in `evalIndexList` order.

## Main results

* `ProductFormulaData.eval_iteratedDeriv_succ`: the `(p + 1)`-st iterated derivative
  of `eval`, expanded as a multinomial Leibniz sum over `Fin P.Υ × Fin P.Γ`.
* `evalIndexList_eq_ofFn`, `evalIndexList_length`: the flattened index list as `List.ofFn`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace Finset
open TrotterError.List
open scoped Topology

/-- The data of a general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` (`eq:pf`): `Υ` stages, `Γ` summands, real coefficients
`a_{(υ,γ)}` uniformly bounded by `1` in absolute value, and per-stage permutations
`π_υ`. -/
structure ProductFormulaData where
  /-- Number of stages `Υ`. -/
  Υ : ℕ
  /-- Number of summands `Γ`. -/
  Γ : ℕ
  /-- Real coefficients `a_{(υ,γ)}`. -/
  coeff : Fin Υ × Fin Γ → ℝ
  /-- Permutation `π_υ` of the summands within stage `υ`. -/
  perm : Fin Υ → Equiv.Perm (Fin Γ)
  /-- The coefficients are uniformly bounded by `1` in absolute value. -/
  coeff_abs_le_one : ∀ i : Fin Υ × Fin Γ, |coeff i| ≤ 1

namespace ProductFormulaData

/-- The flattened list of factor indices `(υ, γ)`, in `eval`'s product order: the outer `Υ`-layer
runs right-to-left and, within each stage, the inner `Γ`-layer runs right-to-left. -/
def evalIndexList (P : ProductFormulaData) : List (Fin P.Υ × Fin P.Γ) :=
  List.product (List.finRange P.Υ).reverse (List.finRange P.Γ).reverse

/-- The `(υ,γ)`-th generator `a_{(υ,γ)} H_{π_υ(γ)}`: the coefficient-scaled, permuted summand. -/
noncomputable def generator (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) : 𝔸 :=
  P.coeff i • H (P.perm i.1 i.2)

/-- The `(υ, γ)`-th factor `e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of the product formula. -/
noncomputable def evalFactor (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  exp (t • P.generator H i)

/-- The product formula `𝒮(t)` evaluated on summands `H` at time `t`. The product
is taken in the paper's right-to-left order `∏_{γ=1}^{Γ} A_γ = A_Γ ⋯ A_1`. -/
noncomputable def eval (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  (P.evalIndexList.map (fun i => P.evalFactor H i t)).prod

/-- The product formula at time `0` is the identity: `𝒮(0) = I`. -/
@[simp]
theorem eval_zero (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) : P.eval H 0 = 1 := by simp [eval, evalFactor]

/-- The product over the flattened index list equals the nested product in `eval`'s order. -/
lemma evalIndexList_map_prod (P : ProductFormulaData) {M : Type*} [Monoid M]
    (g : Fin P.Υ × Fin P.Γ → M) : (P.evalIndexList.map g).prod =
      (((List.finRange P.Υ).reverse).map (fun υ =>
        (((List.finRange P.Γ).reverse).map (fun γ => g (υ, γ))).prod)).prod := by
  unfold evalIndexList List.product
  rw [List.flatMap_def, List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
  congr; funext a
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- The `k`-th iterated derivative of a single factor `P.evalFactor H i`. -/
lemma evalFactor_iteratedDeriv (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ)
    (k : ℕ) (t : ℝ) : iteratedDeriv k (fun t : ℝ => P.evalFactor H i t) t =
      P.generator H i ^ k * P.evalFactor H i t := by
  dsimp [evalFactor]
  rw [iteratedDeriv_exp_smul_const (P.generator H i) k]

/-- The `(p + 1)`-st iterated derivative of `eval`, expanded as a multinomial Leibniz sum over
multi-indices on `Fin P.Υ × Fin P.Γ` (the paper's `𝒮^{(p+1)}(ut)` expansion, prelim.tex:174–178). -/
theorem eval_iteratedDeriv_succ (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin P.Γ → 𝔸) (p : ℕ) (t : ℝ) :
    iteratedDeriv (p + 1) (fun t : ℝ => P.eval H t) t =
      ∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
        (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) •
          (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
            (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
              ((P.generator H (υ, γ)) ^ (q (υ, γ))) *
                exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod := by
  let l : List (Fin P.Υ × Fin P.Γ) := P.evalIndexList
  let f : Fin P.Υ × Fin P.Γ → ℝ → 𝔸 := fun i t => P.evalFactor H i t
  have hf : ∀ i ∈ l, ContDiffAt ℝ (p + 1) (f i) t := by
    intro i _
    simpa [f, evalFactor] using contDiffAt_exp_smul_const (P.generator H i) (p + 1) t
  rw [show (fun t : ℝ => P.eval H t) = fun t : ℝ => (l.map (fun i => f i t)).prod by rfl,
    iteratedDeriv_list_prod_general l f (p + 1) t hf]
  have hnodup : l.Nodup := (List.nodup_reverse.mpr (List.nodup_finRange P.Υ)).product
      (List.nodup_reverse.mpr (List.nodup_finRange P.Γ))
  have hmem : ∀ x : Fin P.Υ × Fin P.Γ, x ∈ l := by simp [l, evalIndexList]
  let e : Fin l.length ≃ Fin P.Υ × Fin P.Γ :=
    List.Nodup.getEquivOfForallMemList l hnodup hmem
  rw [sum_piAntidiag_univ_equiv e (p + 1)
    (fun q : Fin l.length → ℕ =>
      (Nat.multinomial (univ : Finset (Fin l.length)) q : ℝ) •
        (List.ofFn (fun j : Fin l.length =>
          iteratedDeriv (q j) (f (l.get j)) t)).prod)]
  apply sum_congr rfl
  intro q' hq'
  rw [← multinomial_univ_equiv e q']
  congr 1
  have hfac : (fun i : Fin P.Υ × Fin P.Γ => iteratedDeriv (q' i) (f i) t) =
      fun i : Fin P.Υ × Fin P.Γ =>
        P.generator H i ^ (q' i) * P.evalFactor H i t := by
    funext i; rw [evalFactor_iteratedDeriv P H i (q' i) t]
  calc
    (List.ofFn (fun j : Fin l.length => iteratedDeriv ((q' ∘ e) j) (f (l.get j)) t)).prod
        = (l.map (fun i => iteratedDeriv (q' i) (f i) t)).prod := by
            congr 1
            rw [show (fun j : Fin l.length => iteratedDeriv ((q' ∘ e) j) (f (l.get j)) t) =
                fun j : Fin l.length => iteratedDeriv (q' (l.get j)) (f (l.get j)) t by
              funext j
              rw [show ((q' ∘ e) j) = q' (l.get j) by rfl]]
            simpa using (List.ofFn_getElem_eq_map l (fun i => iteratedDeriv (q' i) (f i) t))
    _ = (l.map (fun i => P.generator H i ^ (q' i) *
          P.evalFactor H i t)).prod := by rw [hfac]
    _ = (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
            (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
              P.generator H (υ, γ) ^ (q' (υ, γ)) *
                P.evalFactor H (υ, γ) t)).prod)).prod := by
            rw [evalIndexList_map_prod P (fun i =>
              P.generator H i ^ (q' i) * P.evalFactor H i t)]
    _ = (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
            (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
              ((P.generator H (υ, γ)) ^ (q' (υ, γ))) *
                exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod := by
            simp [evalFactor, generator, mul_smul]

/-! ### Norm bounds for the derivative expansion (prelim.tex:182–188) -/

/-- Per-factor norm bound: `‖(a • H)^q * exp (u t a • H)‖ ≤ ‖H‖^q * Real.exp (t * ‖H‖)`
(prelim.tex:183–184). -/
lemma norm_factor_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (q : ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(P.generator H i) ^ q *
        exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖
      ≤ ‖H (P.perm i.1 i.2)‖ ^ q * Real.exp (t * ‖H (P.perm i.1 i.2)‖) := by
  have hA := norm_smul_le_of_abs_le_one (P.coeff i) (H (P.perm i.1 i.2))
    (P.coeff_abs_le_one i)
  have harg := norm_smul_exp_arg_le (P.coeff i) (H (P.perm i.1 i.2))
    (P.coeff_abs_le_one i) u t ht hu1
  calc
    ‖(P.generator H i) ^ q *
        exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖
        ≤ ‖P.generator H i‖ ^ q *
            Real.exp ((u * t) * ‖P.generator H i‖) := by
            rw [mul_smul]
            exact norm_pow_mul_exp_le (P.generator H i) q (u * t)
              (mul_nonneg hu0 ht)
    _ ≤ ‖H (P.perm i.1 i.2)‖ ^ q * Real.exp (t * ‖H (P.perm i.1 i.2)‖) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA q) (Real.exp_le_exp.mpr harg)
          (Real.exp_nonneg _) (pow_nonneg (norm_nonneg _) q)

/-- The ordered product in `𝔸` of the `(υ, γ)`-factors `A^{q} * exp (r • A)` in `eval`'s order. -/
noncomputable def derivProd (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (q : Fin P.Υ × Fin P.Γ → ℕ) (t : ℝ) : 𝔸 :=
  (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
    (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
      ((P.generator H (υ, γ)) ^ (q (υ, γ))) *
        exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod

/-- The product over the nested `List.finRange` lists equals the `prod` over the product
index type (the reverse order is irrelevant in a commutative monoid). -/
lemma nested_prod_eq_finset_prod {M : Type*} [CommMonoid M] {Υ Γ : ℕ} (f : Fin Υ × Fin Γ → M) :
    (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
      (((List.finRange Γ).reverse).map (fun γ : Fin Γ => f (υ, γ))).prod)).prod =
        ∏ i : Fin Υ × Fin Γ, f i := by
  simp only [List.map_reverse, List.prod_reverse]
  simp_rw [← Fin.prod_univ_def]
  rw [← univ_product_univ, prod_product]

/-- The norm of the product over the `(υ, γ)`-factors is bounded by the product of the per-factor
bounds `‖H_π‖^q * Real.exp (t * ‖H_π‖)`. -/
lemma norm_derivProd_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (q : Fin P.Υ × Fin P.Γ → ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖P.derivProd H q (u * t)‖ ≤
      ∏ i : Fin P.Υ × Fin P.Γ,
        ‖H (P.perm i.1 i.2)‖ ^ q i * Real.exp (t * ‖H (P.perm i.1 i.2)‖) := by
  let g : Fin P.Υ × Fin P.Γ → 𝔸 := fun i =>
    (P.generator H i) ^ q i *
      exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))
  have hflat : P.derivProd H q (u * t) = (P.evalIndexList.map g).prod :=
    (evalIndexList_map_prod P g).symm
  calc
    ‖P.derivProd H q (u * t)‖ = ‖(P.evalIndexList.map g).prod‖ := by rw [hflat]
    _ ≤ (P.evalIndexList.map (fun i => ‖g i‖)).prod := by
        simpa [List.map_map, Function.comp_def] using List.norm_prod_le (P.evalIndexList.map g)
    _ = ∏ i : Fin P.Υ × Fin P.Γ, ‖g i‖ := by
        rw [evalIndexList_map_prod P (fun i => ‖g i‖), nested_prod_eq_finset_prod (fun i => ‖g i‖)]
    _ ≤ ∏ i : Fin P.Υ × Fin P.Γ,
          ‖H (P.perm i.1 i.2)‖ ^ q i * Real.exp (t * ‖H (P.perm i.1 i.2)‖) :=
        prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_factor_le P H i (q i) u t ht hu0 hu1)

/-- `∑_γ ‖H_{π_υ(γ)}‖` is invariant under the stage permutation `π_υ`. -/
lemma sum_norm_perm (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    (H : Fin P.Γ → 𝔸) (υ : Fin P.Υ) :
    (∑ γ : Fin P.Γ, ‖H (P.perm υ γ)‖) = ∑ γ : Fin P.Γ, ‖H γ‖ :=
  Equiv.sum_comp (P.perm υ) (fun γ => ‖H γ‖)

/-- `∑_{i : Fin Υ × Fin Γ} ‖H_{π_{i.1}(i.2)}‖ = Υ * ∑_γ ‖H_γ‖`. -/
lemma sum_norm_prod (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    (H : Fin P.Γ → 𝔸) :
    (∑ i : Fin P.Υ × Fin P.Γ, ‖H (P.perm i.1 i.2)‖) = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
  calc
    (∑ i : Fin P.Υ × Fin P.Γ, ‖H (P.perm i.1 i.2)‖)
        = ∑ υ : Fin P.Υ, ∑ γ : Fin P.Γ, ‖H (P.perm υ γ)‖ := by
            rw [← univ_product_univ, sum_product]
    _ = ∑ υ : Fin P.Υ, ∑ γ : Fin P.Γ, ‖H γ‖ := by
            apply sum_congr rfl
            intro υ hυ
            exact sum_norm_perm P H υ
    _ = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The `(p + 1)`-st iterated derivative norm bound (prelim.tex:182–185):
`‖𝒮^{(p+1)}(ut)‖ ≤ (Υ · Σ_γ ‖H_γ‖)^{p+1} · Real.exp (t · Υ · Σ_γ ‖H_γ‖)`. -/
theorem eval_iteratedDeriv_norm_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ ≤
      ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
        Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  let B : Fin P.Υ × Fin P.Γ → ℝ := fun i => ‖H (P.perm i.1 i.2)‖
  have hB : (∑ i : Fin P.Υ × Fin P.Γ, B i) = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := sum_norm_prod P H
  have hE : (∑ i : Fin P.Υ × Fin P.Γ, t * B i) = t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
    rw [← mul_sum, hB]; ring
  rw [eval_iteratedDeriv_succ]
  calc
    ‖∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
        (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) •
          P.derivProd H q (u * t)‖
        ≤ ∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
            ‖(Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) •
              P.derivProd H q (u * t)‖ := norm_sum_le _ _
    _ = ∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
            (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
              ‖P.derivProd H q (u * t)‖ := by
            apply sum_congr rfl
            intro q hq
            rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
            (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
              (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i * Real.exp (t * B i)) := by
            apply sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_left (norm_derivProd_le P H q u t ht hu0 hu1)
              (Nat.cast_nonneg _)
    _ = ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
          Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
        calc
          (∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
              (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
                (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i * Real.exp (t * B i)))
              = (∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
                  (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
                    (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i) *
                      Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by
                  apply sum_congr rfl
                  intro q hq
                  rw [prod_mul_distrib, (Real.exp_sum univ (fun i => t * B i)).symm,
                    hE]
                  ring
          _ = (∑ q ∈ piAntidiag (univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
                  (Nat.multinomial (univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
                    (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i)) *
                Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by rw [← sum_mul]
          _ = (∑ i : Fin P.Υ × Fin P.Γ, B i) ^ (p + 1) *
                Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
                  rw [← sum_pow_eq_sum_piAntidiag
                    (univ : Finset (Fin P.Υ × Fin P.Γ)) B (p + 1)]
          _ = ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
                Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by rw [hB]

end ProductFormulaData

/-! ### The ordered summands and generators -/

/-- The product formula's permuted summands `H_{π_υ(γ)}`, as a `Fin (Υ * Γ)`-indexed list in
`evalIndexList` order (the paper's `\overrightarrow{\{H_{π_υ(γ)}\}}`). The index
`i = υ * Γ + γ` carries the summand `H_{π_υ(γ)}`; `i.divNat` is the stage and `i.modNat` the
summand index within the stage. -/
noncomputable def orderedSummands (P : ProductFormulaData) {𝔸 : Type*} (H : Fin P.Γ → 𝔸) :
    Fin (P.Υ * P.Γ) → 𝔸 :=
  fun i => H (P.perm (i.divNat) (i.modNat))

/-- The generators of the product formula in `evalIndexList` order (each carrying its coefficient
`a_{(υ,γ)}`). -/
noncomputable def orderedGenerators (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) : Fin P.evalIndexList.length → 𝔸 :=
  fun k => P.generator H (P.evalIndexList.get k)

/-- The generators strictly after `i` in `evalIndexList` order (each carrying its coefficient). -/
noncomputable def suffixGenerators (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) :
    Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length → 𝔸 :=
  fun k => P.generator H ((P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).get k)

/-- `evalIndexList` is the reversed canonical enumeration. -/
lemma evalIndexList_eq_ofFn (P : ProductFormulaData) :
    P.evalIndexList = List.ofFn (fun k : Fin (P.Υ * P.Γ) =>
      (Fin.revPerm k.divNat, Fin.revPerm k.modNat)) := by
  rw [ProductFormulaData.evalIndexList, List.finRange_reverse, List.finRange_reverse, List.finRange,
    List.finRange, List.map_ofFn, List.map_ofFn, product_ofFn]
  rfl

/-- The product formula data with stages and summands reversed, whose canonical order coincides
with the `evalIndexList` order of `P`. -/
def reverseStages (P : ProductFormulaData) : ProductFormulaData where
  Υ := P.Υ
  Γ := P.Γ
  coeff := P.coeff
  perm := fun υ => Fin.revPerm.trans (P.perm (Fin.revPerm υ))
  coeff_abs_le_one := P.coeff_abs_le_one

/-- The summands (coefficient dropped) in `evalIndexList` order, canonically indexed. -/
noncomputable def orderedSummandsEval (P : ProductFormulaData) {𝔸 : Type*} (H : Fin P.Γ → 𝔸) :
    Fin (P.Υ * P.Γ) → 𝔸 :=
  fun k => H (P.perm (Fin.revPerm k.divNat) (Fin.revPerm k.modNat))

/-- `orderedSummands (reverseStages P) H = orderedSummandsEval P H`. -/
lemma orderedSummands_reverseStages (P : ProductFormulaData) {𝔸 : Type*} (H : Fin P.Γ → 𝔸) :
    orderedSummands (reverseStages P) H = orderedSummandsEval P H := rfl

/-- The coefficient-free generators in `evalIndexList` order (each `H_{π_υ(γ)}` without its
coefficient `a_{(υ,γ)}`). -/
noncomputable def fullGenerators (P : ProductFormulaData) {𝔸 : Type*} (H : Fin P.Γ → 𝔸) :
    Fin P.evalIndexList.length → 𝔸 :=
  fun k => H (P.perm (P.evalIndexList.get k).1 (P.evalIndexList.get k).2)

/-- `evalIndexList` has length `Υ * Γ`. -/
lemma evalIndexList_length (P : ProductFormulaData) : P.evalIndexList.length = P.Υ * P.Γ := by
  rw [evalIndexList_eq_ofFn P]
  simp

/-- The `fullGenerators` are a `Fin.cast` reindexing of `orderedSummandsEval`. -/
lemma fullGenerators_eq_orderedSummandsEval (P : ProductFormulaData) {𝔸 : Type*}
    (H : Fin P.Γ → 𝔸) :
    (fun i : Fin (P.Υ * P.Γ) => fullGenerators P H (Fin.cast (evalIndexList_length P).symm i)) =
      orderedSummandsEval P H := by
  funext i
  simp [fullGenerators, orderedSummandsEval, evalIndexList_eq_ofFn]

/-- Reindex a `Fin`-indexed `ℝ`-sum along `Fin.cast`. -/
lemma sum_fin_cast {s t : ℕ} (h : s = t) (f : Fin s → ℝ) :
    (∑ i : Fin t, f (Fin.cast h.symm i)) = ∑ i : Fin s, f i := by
  subst h
  simp

/-- `Σ_k ‖fullGenerators P H k‖ = Υ · Σ_γ ‖H γ‖`: the sum of the norms of the
coefficient-free generators (in `evalIndexList` order) is the stage count times the total
summand norm. -/
lemma sum_norm_fullGenerators_eq (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    (H : Fin P.Γ → 𝔸) :
    (∑ k : Fin P.evalIndexList.length, ‖fullGenerators P H k‖) =
      (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
  calc
    (∑ k : Fin P.evalIndexList.length, ‖fullGenerators P H k‖)
        = (∑ i : Fin (P.Υ * P.Γ),
            ‖fullGenerators P H (Fin.cast (evalIndexList_length P).symm i)‖) :=
            (sum_fin_cast (evalIndexList_length P) (fun k => ‖fullGenerators P H k‖)).symm
    _ = (∑ i : Fin (P.Υ * P.Γ), ‖orderedSummandsEval P H i‖) := by
            apply sum_congr rfl
            intro i _
            exact congrArg (norm : 𝔸 → ℝ) (congr_fun (fullGenerators_eq_orderedSummandsEval P H) i)
    _ = (∑ i : Fin (P.Υ * P.Γ), ‖orderedSummands (reverseStages P) H i‖) := by
            apply sum_congr rfl
            intro i _
            exact congrArg (norm : 𝔸 → ℝ) (congr_fun (orderedSummands_reverseStages P H).symm i)
    _ = (∑ i : Fin P.Υ × Fin P.Γ, ‖H ((reverseStages P).perm i.1 i.2)‖) := by
            change (∑ x : Fin (P.Υ * P.Γ), ‖H ((reverseStages P).perm x.divNat x.modNat)‖) =
                ∑ i : Fin P.Υ × Fin P.Γ, ‖H ((reverseStages P).perm i.1 i.2)‖
            simpa [finProdFinEquiv_symm_apply] using
              (Equiv.sum_comp (finProdFinEquiv.symm)
                (fun i : Fin P.Υ × Fin P.Γ => ‖H ((reverseStages P).perm i.1 i.2)‖))
    _ = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := (reverseStages P).sum_norm_prod H

/-- `Σ_k ‖orderedGenerators P H k‖ ≤ Υ · Σ_γ ‖H γ‖` (the coefficients `|a| ≤ 1` drop out). -/
lemma sum_norm_orderedGenerators_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) :
    (∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖) ≤
      (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
  have hle : ∀ k : Fin P.evalIndexList.length,
      ‖orderedGenerators P H k‖ ≤ ‖fullGenerators P H k‖ := by
    intro k
    unfold orderedGenerators fullGenerators ProductFormulaData.generator
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (P.coeff_abs_le_one (P.evalIndexList.get k))
  calc
    (∑ k : Fin P.evalIndexList.length, ‖orderedGenerators P H k‖)
        ≤ ∑ k : Fin P.evalIndexList.length, ‖fullGenerators P H k‖ :=
            sum_le_sum (fun k _ => hle k)
    _ = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := sum_norm_fullGenerators_eq P H

/-- `Σ_k ‖suffixGenerators P H i k‖ ≤ Υ · Σ_γ ‖H γ‖` (a suffix of the generators, with
coefficients dropped). -/
lemma sum_norm_suffixGenerators_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) :
    (∑ k : Fin (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).length,
        ‖suffixGenerators P H i k‖) ≤ (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
  let drop := P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)
  let g : Fin P.Υ × Fin P.Γ → ℝ := fun j => ‖H (P.perm j.1 j.2)‖
  have hcoeff : ∀ k : Fin drop.length, ‖suffixGenerators P H i k‖ ≤ g (drop.get k) := by
    intro k
    unfold suffixGenerators ProductFormulaData.generator g
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (P.coeff_abs_le_one (drop.get k))
  calc
    (∑ k : Fin drop.length, ‖suffixGenerators P H i k‖)
        ≤ ∑ k : Fin drop.length, g (drop.get k) := sum_le_sum (fun k _ => hcoeff k)
    _ = (drop.map g).sum := by
            simp
    _ ≤ (P.evalIndexList.map g).sum := by
            refine ((List.drop_sublist (P.evalIndexList.idxOf i + 1) P.evalIndexList).map
              g).sum_le_sum ?_
            intro a ha
            rw [List.mem_map] at ha
            rcases ha with ⟨j, _, rfl⟩
            dsimp [g]
            exact norm_nonneg _
    _ = ∑ k : Fin P.evalIndexList.length, ‖fullGenerators P H k‖ := by
            rw [← List.sum_ofFn]
            congr 1
            rw [← List.ofFn_getElem_eq_map P.evalIndexList g]
            congr 1
    _ = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := sum_norm_fullGenerators_eq P H

/-- The norm of the product formula is bounded by `exp (|s| · Υ · Σ ‖H γ‖)`: each factor
`e^{s a H}` has norm at most `exp (|s| ‖H‖)`, and the coefficient `|a| ≤ 1` drops out. -/
lemma norm_eval_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (H : Fin P.Γ → 𝔸) (s : ℝ) :
    ‖P.eval H s‖ ≤ Real.exp (|s| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  calc
    ‖P.eval H s‖ = ‖(P.evalIndexList.map (fun i => P.evalFactor H i s)).prod‖ := rfl
    _ ≤ (P.evalIndexList.map (fun i => ‖P.evalFactor H i s‖)).prod := by
            simpa [List.map_map, Function.comp_def] using
              List.norm_prod_le (P.evalIndexList.map (fun i => P.evalFactor H i s))
    _ ≤ (P.evalIndexList.map (fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖))).prod := by
            refine List.prod_map_le_prod_map₀ (f := fun i => ‖P.evalFactor H i s‖)
              (g := fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖)) (s := P.evalIndexList) ?_ ?_
            · intro i _
              exact norm_nonneg _
            · intro i _
              have hgen : ‖P.generator H i‖ ≤ ‖H (P.perm i.1 i.2)‖ := by
                unfold ProductFormulaData.generator
                rw [norm_smul, Real.norm_eq_abs]
                exact mul_le_of_le_one_left (norm_nonneg _) (P.coeff_abs_le_one i)
              calc
                ‖P.evalFactor H i s‖ = ‖exp (s • P.generator H i)‖ := rfl
                _ ≤ Real.exp (‖s • P.generator H i‖) := norm_exp_le _
                _ = Real.exp (|s| * ‖P.generator H i‖) := by rw [norm_smul, Real.norm_eq_abs]
                _ ≤ Real.exp (|s| * ‖H (P.perm i.1 i.2)‖) :=
                    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgen (abs_nonneg s))
    _ = ∏ i : Fin P.Υ × Fin P.Γ, Real.exp (|s| * ‖H (P.perm i.1 i.2)‖) := by
            rw [P.evalIndexList_map_prod (fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖))]
            rw [ProductFormulaData.nested_prod_eq_finset_prod
              (fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖))]
    _ = Real.exp (|s| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
            rw [(Real.exp_sum (univ : Finset (Fin P.Υ × Fin P.Γ))
              (fun i => |s| * ‖H (P.perm i.1 i.2)‖)).symm]
            congr 1
            calc
              (∑ i : Fin P.Υ × Fin P.Γ, |s| * ‖H (P.perm i.1 i.2)‖)
                  = |s| * ∑ i : Fin P.Υ × Fin P.Γ, ‖H (P.perm i.1 i.2)‖ := by rw [← mul_sum]
              _ = |s| * ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by rw [P.sum_norm_prod H]
              _ = |s| * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by ring

/-- `∑_i αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p = Υ · ∑_γ …`. -/
lemma sum_αCommConj_perm (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) :
    (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p)
      = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
  rw [← univ_product_univ, sum_product]
  rw [sum_congr rfl (fun υ _ => Equiv.sum_comp (P.perm υ)
    (fun γ => αCommConj (orderedSummandsEval P H) (H γ) p))]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `star (P.generator H j) = -(P.generator H j)` whenever each `H γ` is anti-Hermitian. -/
lemma star_generator_of_skew (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] [Star 𝔸] [StarModule ℝ 𝔸] (H : Fin P.Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (j : Fin P.Υ × Fin P.Γ) :
    star (P.generator H j) = -(P.generator H j) := by
  unfold ProductFormulaData.generator
  exact star_smul_of_skew (h_skew (P.perm j.1 j.2))

/-- `αCommConj` of `fullGenerators` equals that of `orderedSummandsEval`. -/
lemma αCommConj_fullGenerators_eq (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (B : 𝔸) (p : ℕ) :
    αCommConj (fullGenerators P H) B p = αCommConj (orderedSummandsEval P H) B p := by
  have hlen := evalIndexList_length P
  calc
    αCommConj (fullGenerators P H) B p
        = αCommConj
            (fun i : Fin (P.Υ * P.Γ) => fullGenerators P H (Fin.cast hlen.symm i)) B p :=
            (αCommConj_cast hlen (fullGenerators P H) B p).symm
    _ = αCommConj (orderedSummandsEval P H) B p := by
            rw [fullGenerators_eq_orderedSummandsEval P H]

/-- Dropping the coefficients of `orderedGenerators` does not increase `αCommConj`. -/
lemma αCommConj_orderedGenerators_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (B : 𝔸) (p : ℕ) :
    αCommConj (orderedGenerators P H) B p ≤ αCommConj (fullGenerators P H) B p := by
  have hord : orderedGenerators P H =
      fun k : Fin P.evalIndexList.length =>
        P.coeff (P.evalIndexList.get k) • fullGenerators P H k := by
    funext k
    simp [orderedGenerators, fullGenerators, ProductFormulaData.generator]
  rw [hord]
  exact αCommConj_smul_fun_le
    (fun k : Fin P.evalIndexList.length => P.coeff (P.evalIndexList.get k))
    (fullGenerators P H) (fun k => P.coeff_abs_le_one (P.evalIndexList.get k)) B p

/-- Dropping the coefficients and extending the suffix to the full list does not increase
`αCommConj` of the suffix generators. -/
lemma αCommConj_suffixGenerators_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (p : ℕ) :
    αCommConj (suffixGenerators P H i) (P.generator H i) p
      ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := by
  let drop := P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)
  let suffixFull : Fin drop.length → 𝔸 := fun k => H (P.perm (drop.get k).1 (drop.get k).2)
  have h1 : αCommConj (suffixGenerators P H i) (P.generator H i) p
      ≤ αCommConj suffixFull (P.generator H i) p := by
    have hsuffix : suffixGenerators P H i =
        fun k : Fin drop.length => P.coeff (drop.get k) • suffixFull k := by
      funext k
      simp [suffixGenerators, suffixFull, drop, ProductFormulaData.generator]
    rw [hsuffix]
    exact αCommConj_smul_fun_le (fun k : Fin drop.length => P.coeff (drop.get k)) suffixFull
      (fun k => P.coeff_abs_le_one (drop.get k)) (P.generator H i) p
  let m := P.evalIndexList.idxOf i + 1
  let n := P.evalIndexList.length - m
  have hi_mem : i ∈ P.evalIndexList := by
    rw [ProductFormulaData.evalIndexList]
    rcases i with ⟨υ, γ⟩
    simp
  have hm : P.evalIndexList.idxOf i < P.evalIndexList.length := List.idxOf_lt_length_of_mem hi_mem
  have hmn : m + n = P.evalIndexList.length := by
    dsimp [m, n]
    exact Nat.add_sub_cancel' (Nat.succ_le_of_lt hm)
  have hlen : drop.length = n := by
    dsimp [drop, n, m]
    rw [List.length_drop]
  have hsuffixFull :
      (fun k : Fin n => suffixFull (Fin.cast hlen.symm k)) =
        fullGenerators P H ∘ Fin.cast hmn ∘ Fin.natAdd m := by
    funext k
    have hget : drop.get (Fin.cast hlen.symm k) =
        P.evalIndexList.get (Fin.cast hmn (Fin.natAdd m k)) := by
      dsimp [drop]
      change (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1))[(Fin.cast hlen.symm k).val] =
        P.evalIndexList[(Fin.cast hmn (Fin.natAdd m k)).val]
      rw [List.getElem_drop]
      congr 1
    simpa [suffixFull, fullGenerators] using
      (congrArg (fun x : Fin P.Υ × Fin P.Γ => H (P.perm x.1 x.2)) hget)
  have h2 : αCommConj suffixFull (P.generator H i) p
      ≤ αCommConj (fullGenerators P H) (P.generator H i) p := by
    calc
      αCommConj suffixFull (P.generator H i) p
          = αCommConj
              (fun k : Fin n => suffixFull (Fin.cast hlen.symm k)) (P.generator H i) p :=
              (αCommConj_cast hlen suffixFull (P.generator H i) p).symm
      _ = αCommConj (fullGenerators P H ∘ Fin.cast hmn ∘ Fin.natAdd m) (P.generator H i) p := by
              rw [hsuffixFull]
      _ = αCommConj ((fullGenerators P H ∘ Fin.cast hmn) ∘ Fin.natAdd m)
            (P.generator H i) p := rfl
      _ ≤ αCommConj (fullGenerators P H ∘ Fin.cast hmn) (P.generator H i) p :=
              αCommConj_natAdd_le (fullGenerators P H ∘ Fin.cast hmn) (P.generator H i) p
      _ = αCommConj (fullGenerators P H) (P.generator H i) p :=
              αCommConj_cast hmn.symm (fullGenerators P H) (P.generator H i) p
  have h3 : αCommConj (fullGenerators P H) (P.generator H i) p
      ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := by
    simpa [ProductFormulaData.generator] using
      (αCommConj_smul_le (fullGenerators P H) (P.coeff i) (P.coeff_abs_le_one i)
        (H (P.perm i.1 i.2)) p)
  calc
    αCommConj (suffixGenerators P H i) (P.generator H i) p
        ≤ αCommConj suffixFull (P.generator H i) p := h1
    _ ≤ αCommConj (fullGenerators P H) (P.generator H i) p := h2
    _ ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := h3

/-- The sum of the conjugation scalings of the suffix generators and of the full ordered
generators is bounded by `2 · Υ · Σ_γ α_comm(H, H_γ)`: the coefficient-drop, suffix-extension,
permutation-reindexing, and `ΣH`-splitting steps shared by both branches of the additive-kernel
norm bound. -/
lemma sum_αCommConj_suffix_add_ordered_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (H : Fin P.Γ → 𝔸) (p : ℕ) (hΥ : 0 < P.Υ) :
    (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
      + αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
      ≤ 2 * (P.Υ : ℝ) * (∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p) := by
  have hsum_i :
      (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
      ≤ (P.Υ : ℝ) * ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
    calc
      (∑ i : Fin P.Υ × Fin P.Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
          ≤ ∑ i : Fin P.Υ × Fin P.Γ,
              αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := by
              gcongr with i
              exact αCommConj_suffixGenerators_le P H i p
      _ = ∑ i : Fin P.Υ × Fin P.Γ,
            αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p := by
              apply sum_congr rfl
              intro i _
              exact αCommConj_fullGenerators_eq P H (H (P.perm i.1 i.2)) p
      _ = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p :=
              sum_αCommConj_perm P H p
  have hordered : αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
      ≤ (P.Υ : ℝ) * ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
    calc
      αCommConj (orderedGenerators P H) (∑ γ : Fin P.Γ, H γ) p
          ≤ αCommConj (fullGenerators P H) (∑ γ : Fin P.Γ, H γ) p :=
              αCommConj_orderedGenerators_le P H (∑ γ : Fin P.Γ, H γ) p
      _ = αCommConj (orderedSummandsEval P H) (∑ γ : Fin P.Γ, H γ) p :=
              αCommConj_fullGenerators_eq P H (∑ γ : Fin P.Γ, H γ) p
      _ ≤ ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p :=
              αCommConj_sum_le (orderedSummandsEval P H) H p
      _ ≤ (P.Υ : ℝ) * ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
              have h1 : (1 : ℝ) ≤ (P.Υ : ℝ) := mod_cast hΥ
              have hnonneg : 0 ≤ ∑ γ : Fin P.Γ, αCommConj (orderedSummandsEval P H) (H γ) p :=
                sum_nonneg (fun γ _ => αCommConj_nonneg _ _ _)
              simpa using mul_le_mul_of_nonneg_right h1 hnonneg
  linarith

end TrotterError
