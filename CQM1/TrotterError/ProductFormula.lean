/-
Copyright (c) 2026 The Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.Calculus

/-!
# Product formulas

We define the general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of arXiv:1912.08854 (§2.3) and the associated
`p`-th order condition.

Following the paper's convention (`papers/prelim.tex` §2.1), the product
`∏_{γ=1}^{Γ} A_γ` denotes `A_Γ ⋯ A_2 A_1`, i.e. increasing indices from right to
left; we implement this with a reversed `List.finRange`. Since the factors
`e^{t a H}` do not commute, the product is taken with `List.prod` (ordered) rather
than `Finset.prod` (commutative) or `Finset.noncommProd` (which requires pairwise
commutativity).

## Main results

* `ProductFormulaData.eval_iteratedDeriv_succ`: the `(p + 1)`-st iterated derivative
  of `eval`, expanded as a multinomial Leibniz sum over `Fin P.Υ × Fin P.Γ`.
* `ProductFormulaData.IsOrderOf`: the `p`-th order condition `𝒮(t) = e^{tH} + O(t^{p+1})`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace
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
  coeff : Fin Υ → Fin Γ → ℝ
  /-- Permutation `π_υ` of the summands within stage `υ`. -/
  perm : Fin Υ → Equiv.Perm (Fin Γ)
  /-- The coefficients are uniformly bounded by `1` in absolute value. -/
  coeff_abs_le_one : ∀ υ γ, |coeff υ γ| ≤ 1

namespace ProductFormulaData

/-- The product formula `𝒮(t)` evaluated on summands `H` at time `t`. The product
is taken in the paper's right-to-left order `∏_{γ=1}^{Γ} A_γ = A_Γ ⋯ A_1`. -/
noncomputable def eval (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ((List.finRange P.Υ).reverse.map fun υ =>
    ((List.finRange P.Γ).reverse.map fun γ =>
      exp ((t * P.coeff υ γ) • H (P.perm υ γ))).prod).prod

/-- `P` is a `p`-th order formula on summands `H` if `‖𝒮(t) − e^{tH}‖ = O(t^{p+1})`
as `t → 0` (`prelim.tex:150`). -/
def IsOrderOf (P : ProductFormulaData) (p : ℕ) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) : Prop :=
  (fun t : ℝ => ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖)
    =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1))

/-- The product formula at time `0` is the identity: `𝒮(0) = I`. -/
theorem eval_zero (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) : P.eval H 0 = 1 := by
  simp [eval]

/-- The flattened list of factor indices `(υ, γ)`, in `eval`'s product order: the outer `Υ`-layer
runs right-to-left and, within each stage, the inner `Γ`-layer runs right-to-left. -/
def evalIndexList (P : ProductFormulaData) : List (Fin P.Υ × Fin P.Γ) :=
  List.product (List.finRange P.Υ).reverse (List.finRange P.Γ).reverse

/-- The `(υ, γ)`-th factor `e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of the product formula. -/
noncomputable def evalFactor (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  exp ((t * P.coeff i.1 i.2) • H (P.perm i.1 i.2))

/-- A factor `P.evalFactor H (υ, γ)` equals `exp` of a scalar-multiplied element of `𝔸`. -/
lemma evalFactor_eq_exp_smul (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (υ : Fin P.Υ) (γ : Fin P.Γ) :
    (fun t : ℝ => P.evalFactor H (υ, γ) t) =
      fun t : ℝ => exp (t • (P.coeff υ γ • H (P.perm υ γ))) := by
  funext t
  simp [evalFactor, mul_smul]

/-- The product over the flattened index list equals the nested product in `eval`'s order. -/
lemma evalIndexList_map_prod (P : ProductFormulaData) {M : Type*} [Monoid M]
    (g : Fin P.Υ × Fin P.Γ → M) : (P.evalIndexList.map g).prod =
      (((List.finRange P.Υ).reverse).map (fun υ =>
        (((List.finRange P.Γ).reverse).map (fun γ => g (υ, γ))).prod)).prod := by
  unfold evalIndexList List.product
  rw [List.flatMap_def, List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
  congr; funext a
  simp only [Function.comp_apply]
  congr 1
  rw [List.map_map]
  rfl

/-- `eval` as a product over the flattened index list. -/
lemma eval_eq_flat_prod (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (t : ℝ) :
    P.eval H t = (P.evalIndexList.map (fun i => P.evalFactor H i t)).prod := by
  rw [eval, evalIndexList_map_prod P (fun i => P.evalFactor H i t)]
  simp [evalFactor]

/-- The `k`-th iterated derivative of a single factor `P.evalFactor H i`. -/
lemma evalFactor_iteratedDeriv (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => P.evalFactor H i t) t =
      (P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ k * P.evalFactor H i t := by
  rcases i with ⟨υ, γ⟩
  rw [evalFactor_eq_exp_smul P H υ γ,
    iteratedDeriv_exp_smul_const (P.coeff υ γ • H (P.perm υ γ)) k, evalFactor, mul_smul]

/-- The `(p + 1)`-st iterated derivative of `eval`, expanded as a multinomial Leibniz sum over
multi-indices on `Fin P.Υ × Fin P.Γ` (the paper's `𝒮^{(p+1)}(ut)` expansion, prelim.tex:174–178). -/
theorem eval_iteratedDeriv_succ (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (t : ℝ) :
    iteratedDeriv (p + 1) (fun t : ℝ => P.eval H t) t =
      ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
        (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) •
          (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
            (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
              ((P.coeff υ γ • H (P.perm υ γ)) ^ (q (υ, γ))) *
                exp ((t * P.coeff υ γ) • H (P.perm υ γ)))).prod)).prod := by
  classical
  let l : List (Fin P.Υ × Fin P.Γ) := P.evalIndexList
  let f : Fin P.Υ × Fin P.Γ → ℝ → 𝔸 := fun i t => P.evalFactor H i t
  have hf : ∀ i ∈ l, ContDiffAt ℝ (p + 1) (f i) t := by
    intro i _
    rcases i with ⟨υ, γ⟩
    dsimp [f]
    rw [evalFactor_eq_exp_smul P H υ γ]
    exact contDiffAt_exp_smul_const (P.coeff υ γ • H (P.perm υ γ)) (p + 1) t
  rw [show (fun t : ℝ => P.eval H t) =
      fun t : ℝ => (P.evalIndexList.map (fun i => P.evalFactor H i t)).prod by
    funext t
    rw [eval_eq_flat_prod P H t]]
  rw [iteratedDeriv_list_prod_general l f (p + 1) t hf]
  have hnodup : l.Nodup := (List.nodup_reverse.mpr (List.nodup_finRange P.Υ)).product
      (List.nodup_reverse.mpr (List.nodup_finRange P.Γ))
  have hmem : ∀ x : Fin P.Υ × Fin P.Γ, x ∈ l := by
    rintro ⟨a, b⟩; simp [l, evalIndexList]
  let e : Fin l.length ≃ Fin P.Υ × Fin P.Γ :=
    List.Nodup.getEquivOfForallMemList l hnodup hmem
  rw [sum_piAntidiag_univ_equiv e (p + 1)
    (fun q : Fin l.length → ℕ =>
      (Nat.multinomial (Finset.univ : Finset (Fin l.length)) q : ℝ) •
        (List.ofFn (fun j : Fin l.length =>
          iteratedDeriv (q j) (f (l.get j)) t)).prod)]
  apply Finset.sum_congr rfl
  intro q' hq'
  rw [← multinomial_univ_equiv e q']
  congr 1
  have hfac : (fun i : Fin P.Υ × Fin P.Γ => iteratedDeriv (q' i) (f i) t) =
      fun i : Fin P.Υ × Fin P.Γ =>
        (P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ (q' i) * P.evalFactor H i t := by
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
    _ = (l.map (fun i => (P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ (q' i) *
          P.evalFactor H i t)).prod := by
            rw [hfac]
    _ = (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
            (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
              (P.coeff υ γ • H (P.perm υ γ)) ^ (q' (υ, γ)) *
                P.evalFactor H (υ, γ) t)).prod)).prod := by
            rw [evalIndexList_map_prod P (fun i =>
              (P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ (q' i) * P.evalFactor H i t)]
    _ = (((List.finRange P.Υ).reverse).map (fun υ : Fin P.Υ =>
            (((List.finRange P.Γ).reverse).map (fun γ : Fin P.Γ =>
              ((P.coeff υ γ • H (P.perm υ γ)) ^ (q' (υ, γ))) *
                exp ((t * P.coeff υ γ) • H (P.perm υ γ)))).prod)).prod := by
            simp [evalFactor]

/-! ### Norm bounds for the derivative expansion (prelim.tex:182–188) -/

/-- `|c| ≤ 1` implies `‖c • A‖ ≤ ‖A‖` in any normed algebra. -/
lemma norm_smul_le_of_abs_le_one {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]
    (c : ℝ) (A : 𝔸) (hc : |c| ≤ 1) : ‖c • A‖ ≤ ‖A‖ := by
  calc
    ‖c • A‖ = |c| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖A‖ := one_mul _

/-- For `u ≤ 1`, `0 ≤ t`, and `|c| ≤ 1`, the exponential argument `(u * t) * ‖c • A‖` is at
most `t * ‖A‖`. -/
lemma norm_smul_exp_arg_le {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]
    (c : ℝ) (A : 𝔸) (hc : |c| ≤ 1) (u t : ℝ) (ht : 0 ≤ t) (hu1 : u ≤ 1) :
    (u * t) * ‖c • A‖ ≤ t * ‖A‖ := by
  have hc' : u * |c| ≤ 1 := by
    simpa using mul_le_mul hu1 hc (abs_nonneg _) zero_le_one
  have hle : u * t * |c| ≤ t := by
    calc
      u * t * |c| = t * (u * |c|) := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hc' ht
      _ = t := mul_one _
  calc
    (u * t) * ‖c • A‖ = u * t * |c| * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ ≤ t * ‖A‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- Per-factor norm bound: `‖(a • H)^q * exp (u t a • H)‖ ≤ ‖H‖^q * Real.exp (t * ‖H‖)`
(prelim.tex:183–184). -/
lemma norm_factor_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (q : ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ q *
        exp ((u * t * P.coeff i.1 i.2) • H (P.perm i.1 i.2))‖
      ≤ ‖H (P.perm i.1 i.2)‖ ^ q * Real.exp (t * ‖H (P.perm i.1 i.2)‖) := by
  have hA := norm_smul_le_of_abs_le_one (P.coeff i.1 i.2) (H (P.perm i.1 i.2))
    (P.coeff_abs_le_one i.1 i.2)
  have harg := norm_smul_exp_arg_le (P.coeff i.1 i.2) (H (P.perm i.1 i.2))
    (P.coeff_abs_le_one i.1 i.2) u t ht hu1
  calc
    ‖(P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ q *
        exp ((u * t * P.coeff i.1 i.2) • H (P.perm i.1 i.2))‖
        ≤ ‖P.coeff i.1 i.2 • H (P.perm i.1 i.2)‖ ^ q *
            Real.exp ((u * t) * ‖P.coeff i.1 i.2 • H (P.perm i.1 i.2)‖) := by
            rw [mul_smul]
            exact norm_pow_mul_exp_le (P.coeff i.1 i.2 • H (P.perm i.1 i.2)) q (u * t)
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
      ((P.coeff υ γ • H (P.perm υ γ)) ^ (q (υ, γ))) *
        exp ((t * P.coeff υ γ) • H (P.perm υ γ)))).prod)).prod

/-- The product over the nested `List.finRange` lists equals the `Finset.prod` over the product
index type (ℝ is commutative, so the order does not matter). -/
lemma nested_prod_eq_finset_prod {Υ Γ : ℕ} (f : Fin Υ × Fin Γ → ℝ) :
    (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
      (((List.finRange Γ).reverse).map (fun γ : Fin Γ => f (υ, γ))).prod)).prod =
        ∏ i : Fin Υ × Fin Γ, f i := by
  simp only [List.map_reverse, List.prod_reverse]
  simp_rw [← Fin.prod_univ_def]
  rw [← Finset.univ_product_univ, Finset.prod_product]

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
    (P.coeff i.1 i.2 • H (P.perm i.1 i.2)) ^ q i *
      exp ((u * t * P.coeff i.1 i.2) • H (P.perm i.1 i.2))
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
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
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
            rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ υ : Fin P.Υ, ∑ γ : Fin P.Γ, ‖H γ‖ := by
            apply Finset.sum_congr rfl
            intro υ hυ
            exact sum_norm_perm P H υ
    _ = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

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
    rw [← Finset.mul_sum, hB]
    ring
  rw [eval_iteratedDeriv_succ]
  calc
    ‖∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
        (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) •
          P.derivProd H q (u * t)‖
        ≤ ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
            ‖(Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) •
              P.derivProd H q (u * t)‖ := norm_sum_le _ _
    _ = ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
            (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
              ‖P.derivProd H q (u * t)‖ := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
            (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
              (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i * Real.exp (t * B i)) := by
            apply Finset.sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_left (norm_derivProd_le P H q u t ht hu0 hu1)
              (Nat.cast_nonneg _)
    _ = ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
          Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
        calc
          (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
              (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
                (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i * Real.exp (t * B i)))
              = (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
                  (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
                    (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i) *
                      Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  rw [Finset.prod_mul_distrib, (Real.exp_sum Finset.univ (fun i => t * B i)).symm,
                    hE]
                  ring
          _ = (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) (p + 1),
                  (Nat.multinomial (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) q : ℝ) *
                    (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i)) *
                Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
                  rw [← Finset.sum_mul]
          _ = (∑ i : Fin P.Υ × Fin P.Γ, B i) ^ (p + 1) *
                Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
                  rw [← Finset.sum_pow_eq_sum_piAntidiag
                    (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) B (p + 1)]
          _ = ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
                Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) := by
                  rw [hB]

end ProductFormulaData

end TrotterError
