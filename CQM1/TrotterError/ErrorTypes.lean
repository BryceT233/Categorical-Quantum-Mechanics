/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.ProductFormula
public import CQM1.TrotterError.TimeOrderedExp

import CQM1.TrotterError.ListProd

/-!
# Three types of Trotter error

This file formalizes `thm:error_type` of arXiv:1912.08854 (Appendix A): the three equivalent
representations of the product formula `𝒮(t) = P.eval H t` relative to the ideal evolution
`e^{tH}`, `H = ∑ γ H γ`:

* *additive*: `𝒮(t) = e^{tH} + ∫₀ᵗ e^{(t−τ)H} 𝒮(τ) 𝒯(τ) dτ` (`errorType_additive`);
* *exponentiated*: `𝒮(t) = exp_T(∫₀ᵗ (H + ℰ(τ)) dτ)` (`errorType_exponentiated`);
* *multiplicative*: `𝒮(t) = e^{tH} (1 + ℳ(t))` (`errorType_multiplicative`).

The lexicographic order `(υ,γ) ≻ (υ',γ')` of the paper (`papers/type.tex`) is exactly the
left-to-right order of `ProductFormulaData.evalIndexList`, so the prefix / suffix products
`∏_{j ≻ i}`, `∏_{j ≤ i}` are implemented with `List.take` / `List.drop` at `List.idxOf i`.

## Main results

* `eval_hasDerivAt`: the product-rule derivative of `𝒮(t)`.
* `eval_hasDerivAt_additive`, `eval_hasDerivAt_exponentiated`: the two rearranged ODEs.
* `additiveResidual`, `additiveKernel`, `exponentiatedGenerator`, `exponentiatedError`,
  `multiplicativeError`: the residual `ℛ` and the three error operators `𝒯`, `ℰ`, `ℳ` of the paper.
* `errorType_additive`, `errorType_exponentiated`, `errorType_multiplicative`: `thm:error_type`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### Basic ingredients -/

/-- The ordered product `∏_{j ∈ l} e^{s a_j H_j}` of the product-formula factors over a sublist `l`
of `evalIndexList`. -/
noncomputable def factorProdOver (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (s : ℝ) (l : List (Fin P.Υ × Fin P.Γ)) : 𝔸 :=
  (l.map (fun j => P.evalFactor H j s)).prod

/-- `∏_{j ≻ i}^{←} e^{t a_j H_j}`, the product of the factors strictly before `i`. -/
noncomputable def prefixFactorProd (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H t (P.evalIndexList.take (P.evalIndexList.idxOf i))

/-- `∏_{j ≺ i}^{←} e^{t a_j H_j}`, the product of the factors strictly after `i`. -/
noncomputable def strictSuffixFactorProd (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H t (P.evalIndexList.drop (P.evalIndexList.idxOf i + 1))

/-- `∏_{j ≤ i}^{←} e^{t a_j H_j}`, the product of the factor `i` and everything after it. -/
noncomputable abbrev suffixFactorProd (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  P.evalFactor H i t * strictSuffixFactorProd P H i t

/-- `∏_{j ≻ i}^{→} e^{-t a_j H_j}`, the inverse of `prefixFactorProd`. -/
noncomputable def invPrefixFactorProd (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H (-t) ((P.evalIndexList.take (P.evalIndexList.idxOf i)).reverse)

/-- `∏_{j ≺ i}^{→} e^{-t a_j H_j}`, the inverse of `strictSuffixFactorProd`. -/
noncomputable def invStrictSuffixFactorProd (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H (-t) ((P.evalIndexList.drop (P.evalIndexList.idxOf i + 1)).reverse)

/-- `factorProdOver` over the full index list is `eval`. -/
lemma factorProdOver_evalIndexList (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin P.Γ → 𝔸) (τ : ℝ) :
    factorProdOver P H τ (P.evalIndexList) = P.eval H τ := rfl

/-- `evalIndexList` has no duplicates. -/
lemma evalIndexList_nodup (P : ProductFormulaData) : P.evalIndexList.Nodup :=
  (List.nodup_reverse.mpr (List.nodup_finRange P.Υ)).product
    (List.nodup_reverse.mpr (List.nodup_finRange P.Γ))

/-- Every factor index `i : Fin P.Υ × Fin P.Γ` occurs in `evalIndexList`. -/
lemma evalIndexList_mem (P : ProductFormulaData) (i : Fin P.Υ × Fin P.Γ) : i ∈ P.evalIndexList := by
  rcases i with ⟨a, b⟩
  simp [ProductFormulaData.evalIndexList]

/-! ### Continuity of the building blocks -/

/-- `t ↦ exp (t • A)` is continuous (over `ℝ`). -/
lemma continuous_exp_smul_const (A : 𝔸) : Continuous (fun t : ℝ => exp (t • A)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (contDiffAt_exp_smul_const A 1 t).continuousAt

/-- Each factor `t ↦ P.evalFactor H i t` is continuous. -/
@[fun_prop]
lemma continuous_evalFactor (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) : Continuous (fun t : ℝ => P.evalFactor H i t) := by
  simpa [ProductFormulaData.evalFactor] using continuous_exp_smul_const (P.generator H i)

/-- `s ↦ factorProdOver P H s l` is continuous. -/
@[fun_prop]
lemma continuous_factorProdOver (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (l : List (Fin P.Υ × Fin P.Γ)) : Continuous (fun s : ℝ => factorProdOver P H s l) := by
  unfold factorProdOver
  induction l with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (1 : 𝔸)))
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (continuous_evalFactor P H a).mul ih

/-- The product formula `t ↦ P.eval H t` is continuous. -/
@[fun_prop]
lemma continuous_eval (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) :
    Continuous (fun t : ℝ => P.eval H t) :=
  continuous_factorProdOver P H P.evalIndexList

/-! ### Elementary `exp` identities (need `ℚ`-algebra) -/

omit [NormedAlgebra ℝ 𝔸] in
/-- `exp (-x) * exp x = 1`. -/
lemma exp_neg_mul_self [NormedAlgebra ℚ 𝔸] (x : 𝔸) : exp (-x) * exp x = 1 := by
  simpa using (exp_add_of_commute (Commute.refl x).neg_left).symm

omit [NormedAlgebra ℝ 𝔸] in
/-- `exp x * exp (-x) = 1`. -/
lemma exp_mul_neg_self [NormedAlgebra ℚ 𝔸] (x : 𝔸) : exp x * exp (-x) = 1 := by
  simpa using (exp_add_of_commute (Commute.refl x).neg_right).symm

omit [NormedAlgebra ℝ 𝔸] in
/-- `∏_{j} e^{A_j} · ∏_{j}^{←} e^{-A_j} = 1` (a telescoping product of unit factors). -/
lemma List.prod_exp_mul_rev_neg [NormedAlgebra ℚ 𝔸] {ι : Type*} (l : List ι) (A : ι → 𝔸) :
    (l.map (fun i => exp (A i))).prod * ((l.reverse).map (fun i => exp (-A i))).prod = 1 :=
  prod_mul_rev_eq_one_of_mul_eq_one l (fun i => exp (A i)) (fun i => exp (-A i))
    (fun i => exp_mul_neg_self (A i))

omit [NormedAlgebra ℝ 𝔸] in
/-- `∏_{j}^{←} e^{-A_j} · ∏_{j} e^{A_j} = 1` (a telescoping product of unit factors). -/
lemma List.prod_map_neg_exp_mul_prod [NormedAlgebra ℚ 𝔸] {ι : Type*} (l : List ι) (A : ι → 𝔸) :
    (l.reverse.map (fun i => exp (-A i))).prod * (l.map (fun i => exp (A i))).prod = 1 :=
  rev_mul_prod_eq_one_of_mul_eq_one l (fun i => exp (A i)) (fun i => exp (-A i))
    (fun i => exp_neg_mul_self (A i))

omit [CompleteSpace 𝔸] in
/-- `(s • A)` commutes with `A`. -/
lemma commute_smul_self (A : 𝔸) (s : ℝ) : Commute (s • A) A := by
  rw [commute_iff_eq, smul_mul_assoc, mul_smul_comm]

omit [CompleteSpace 𝔸] in
/-- `exp (s • A)` commutes with `A`. -/
lemma exp_smul_commute_self (A : 𝔸) (s : ℝ) : Commute (exp (s • A)) A :=
  (commute_smul_self A s).exp_left

omit [CompleteSpace 𝔸] in
/-- The factor `e^{t a_i H_i}` commutes with its generator `a_i H_i`. -/
lemma evalFactor_commute_coeffOp (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) (t : ℝ) : P.evalFactor H i t * (P.generator H i) =
      (P.generator H i) * P.evalFactor H i t := exp_smul_commute_self (P.generator H i) t

/-! ### The first derivative of the product formula -/

/-- The derivative of a single factor: `d/dt e^{t a_i H_i} = (a_i H_i) · e^{t a_i H_i}`. -/
lemma evalFactor_hasDerivAt (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.evalFactor H i s)
      ((P.generator H i) * P.evalFactor H i t) t := by
  simpa [ProductFormulaData.evalFactor] using hasDerivAt_exp_smul_const' (P.generator H i) t

/-- The position-indexed derivative sum of the product formula. -/
noncomputable def posDerivSum (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ∑ k : Fin P.evalIndexList.length,
    ((P.evalIndexList.take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod
      * ((P.generator H (P.evalIndexList.get k)) *
        P.evalFactor H (P.evalIndexList.get k) t)
      * ((P.evalIndexList.drop ((k : ℕ) + 1)).map (fun i => P.evalFactor H i t)).prod

/-- The factor-indexed derivative of `P.eval H` at time `t` (the paper's `d/dt 𝒮`). -/
noncomputable def evalDeriv (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ∑ i : Fin P.Υ × Fin P.Γ,
    prefixFactorProd P H i t * (P.generator H i) * suffixFactorProd P H i t

omit [CompleteSpace 𝔸] in
/-- The position-indexed derivative sum equals the factor-indexed derivative sum. -/
lemma posDerivSum_eq_evalDeriv (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) :
    posDerivSum P H t = evalDeriv P H t := by
  let l : List (Fin P.Υ × Fin P.Γ) := P.evalIndexList
  have hnodup : l.Nodup := evalIndexList_nodup P
  have hmem : ∀ i : Fin P.Υ × Fin P.Γ, i ∈ l := evalIndexList_mem P
  have hpos : posDerivSum P H t = ∑ k : Fin l.length,
      ((l.take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod *
        (P.generator H (l.get k)) *
        ((l.drop (k : ℕ)).map (fun i => P.evalFactor H i t)).prod := by
    simp only [posDerivSum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      ((P.evalIndexList.take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod *
          ((P.generator H (P.evalIndexList.get k)) *
            P.evalFactor H (P.evalIndexList.get k) t) *
          ((P.evalIndexList.drop ((k : ℕ) + 1)).map (fun i => P.evalFactor H i t)).prod
          = ((P.evalIndexList.take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod *
              (P.generator H (P.evalIndexList.get k)) *
              (P.evalFactor H (P.evalIndexList.get k) t *
                ((P.evalIndexList.drop ((k : ℕ) + 1)).map (fun i => P.evalFactor H i t)).prod) := by
            noncomm_ring
      _ = ((P.evalIndexList.take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod *
              (P.generator H (P.evalIndexList.get k)) *
              ((P.evalIndexList.drop (k : ℕ)).map (fun i => P.evalFactor H i t)).prod := by
            rw [← prod_drop_eq_get_mul P.evalIndexList (fun i => P.evalFactor H i t) k]
  have hreindex := sum_get_eq_sum_idxOf (hnodup := hnodup) (hmem := hmem)
    (G := fun i j => ((l.take j).map (fun i => P.evalFactor H i t)).prod *
      (P.generator H i) * ((l.drop j).map (fun i => P.evalFactor H i t)).prod)
  calc
    posDerivSum P H t = ∑ k : Fin l.length,
        ((l.take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod *
          (P.generator H (l.get k)) *
          ((l.drop (k : ℕ)).map (fun i => P.evalFactor H i t)).prod := by simpa [l] using hpos
    _ = ∑ i : Fin P.Υ × Fin P.Γ,
        ((l.take (l.idxOf i)).map (fun i => P.evalFactor H i t)).prod *
          (P.generator H i) *
          ((l.drop (l.idxOf i)).map (fun i => P.evalFactor H i t)).prod := by simpa using hreindex
    _ = evalDeriv P H t := by
        simp only [l, evalDeriv, prefixFactorProd, suffixFactorProd, strictSuffixFactorProd,
          factorProdOver]
        apply Finset.sum_congr rfl
        intro i _
        have hidx : P.evalIndexList.idxOf i < P.evalIndexList.length :=
          List.idxOf_lt_length_iff.mpr (evalIndexList_mem P i)
        rw [prod_drop_eq_get_mul (l := P.evalIndexList) (f := fun i => P.evalFactor H i t)
          ⟨P.evalIndexList.idxOf i, hidx⟩, List.idxOf_get hidx]

/-- The first derivative of the product formula (`d/dt 𝒮` in `type.tex:47-48`). -/
theorem eval_hasDerivAt (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.eval H s) (evalDeriv P H t) t := by
  have hpos : HasDerivAt (fun s : ℝ => P.eval H s) (posDerivSum P H t) t := by
    have h := hasDerivAt_list_prod P.evalIndexList (fun i => P.evalFactor H i)
      (fun i s => (P.generator H i) * P.evalFactor H i s)
      (fun i _ s => evalFactor_hasDerivAt P H i s) t
    change HasDerivAt (fun s : ℝ => (P.evalIndexList.map (fun i => P.evalFactor H i s)).prod)
      (posDerivSum P H t) t
    simpa only [posDerivSum] using h
  simpa only [evalDeriv, posDerivSum_eq_evalDeriv P H t] using hpos

/-! ### The additive residual and the exponentiated generator -/

/-- The additive residual `ℛ(t)` of `type.tex:17-20`: `ℛ(t) = 𝒮'(t) - H·𝒮(t)`, so that
`d/dt 𝒮 = H·𝒮 + ℛ` (`type.tex:12`). -/
noncomputable def additiveResidual (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  evalDeriv P H t - (∑ γ, H γ) * P.eval H t

/-- `d/dt 𝒮 = H·𝒮 + additiveResidual` (`type.tex:12`). -/
theorem eval_hasDerivAt_additive (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.eval H s) ((∑ γ, H γ) * P.eval H t + additiveResidual P H t) t := by
  have hkey : (∑ γ, H γ) * P.eval H t + additiveResidual P H t = evalDeriv P H t := by
    dsimp [additiveResidual]; abel
  simpa only [hkey] using (eval_hasDerivAt P H t)

/-- The exponentiated generator `ℱ(t)` of `type.tex:54`. -/
noncomputable def exponentiatedGenerator (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ∑ i : Fin P.Υ × Fin P.Γ,
    prefixFactorProd P H i t * P.generator H i * invPrefixFactorProd P H i t

omit [CompleteSpace 𝔸] in
/-- `e^{-t A_j} = exp (-(t · a_j • H_j))`. -/
lemma evalFactor_neg_eq_exp_neg (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (j : Fin P.Υ × Fin P.Γ) (t : ℝ) :
    P.evalFactor H j (-t) = exp (-((t * P.coeff j) • H (P.perm j.1 j.2))) := by
  rw [ProductFormulaData.evalFactor, ProductFormulaData.generator, mul_smul, neg_smul]

/-- `invPrefixFactorProd · prefixFactorProd = 1`. -/
lemma invPrefix_mul_prefix [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) (t : ℝ) :
    invPrefixFactorProd P H i t * prefixFactorProd P H i t = 1 := by
  unfold invPrefixFactorProd prefixFactorProd factorProdOver
  have h := List.prod_map_neg_exp_mul_prod (l := P.evalIndexList.take (P.evalIndexList.idxOf i))
    (A := fun j => (t * P.coeff j) • H (P.perm j.1 j.2))
  simpa [ProductFormulaData.evalFactor, ProductFormulaData.generator, mul_smul,
    evalFactor_neg_eq_exp_neg] using h

/-- `strictSuffixFactorProd · invStrictSuffixFactorProd = 1`. -/
lemma strictSuffix_mul_invStrictSuffix [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData)
    (H : Fin P.Γ → 𝔸) (i : Fin P.Υ × Fin P.Γ) (τ : ℝ) :
    strictSuffixFactorProd P H i τ * invStrictSuffixFactorProd P H i τ = 1 := by
  unfold strictSuffixFactorProd invStrictSuffixFactorProd factorProdOver
  have h := List.prod_exp_mul_rev_neg (l := P.evalIndexList.drop (P.evalIndexList.idxOf i + 1))
    (A := fun j => (τ * P.coeff j) • H (P.perm j.1 j.2))
  simpa [ProductFormulaData.evalFactor, ProductFormulaData.generator, mul_smul,
    evalFactor_neg_eq_exp_neg] using h

/-- `P.eval H τ · invStrictSuffixFactorProd = prefixFactorProd · evalFactor`. -/
lemma eval_mul_invStrictSuffix [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) (τ : ℝ) :
    P.eval H τ * invStrictSuffixFactorProd P H i τ =
      prefixFactorProd P H i τ * P.evalFactor H i τ := by
  have hdec : P.eval H τ = prefixFactorProd P H i τ * P.evalFactor H i τ *
      strictSuffixFactorProd P H i τ := by
    rw [← factorProdOver_evalIndexList P H τ]
    simpa only [prefixFactorProd, strictSuffixFactorProd, factorProdOver] using
      (prod_map_eq_take_mul_get_mul_drop (l := P.evalIndexList) (f := fun j => P.evalFactor H j τ)
        i (evalIndexList_mem P i))
  rw [hdec, mul_assoc, strictSuffix_mul_invStrictSuffix P H i τ, mul_one]

/-- `P.eval H τ · invPrefixFactorProd = suffixFactorProd`. -/
lemma invPrefix_mul_eval [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) (t : ℝ) :
    invPrefixFactorProd P H i t * P.eval H t = suffixFactorProd P H i t := by
  have hdec : P.eval H t = prefixFactorProd P H i t * P.evalFactor H i t *
      strictSuffixFactorProd P H i t := by
    rw [← factorProdOver_evalIndexList P H t]
    simpa only [prefixFactorProd, strictSuffixFactorProd, factorProdOver] using
      (prod_map_eq_take_mul_get_mul_drop (l := P.evalIndexList) (f := fun j => P.evalFactor H j t)
        i (evalIndexList_mem P i))
  rw [hdec, ← mul_assoc, ← mul_assoc, invPrefix_mul_prefix P H i t, one_mul]

/-- `d/dt 𝒮 = ℱ · 𝒮` (`type.tex:49`). -/
theorem eval_hasDerivAt_exponentiated [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData)
    (H : Fin P.Γ → 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.eval H s) (exponentiatedGenerator P H t * P.eval H t) t := by
  have hgen : exponentiatedGenerator P H t * P.eval H t = evalDeriv P H t := by
    unfold exponentiatedGenerator evalDeriv
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc, invPrefix_mul_eval P H i t]
  simpa only [hgen] using (eval_hasDerivAt P H t)

/-! ### The three error operators -/

/-- The additive kernel `𝒯(τ)` of `type.tex:33-35`. -/
noncomputable def additiveKernel (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) : ℝ → 𝔸 := fun τ =>
  (∑ i : Fin P.Υ × Fin P.Γ,
    invStrictSuffixFactorProd P H i τ * (P.generator H i) *
      strictSuffixFactorProd P H i τ)
  - factorProdOver P H (-τ) (P.evalIndexList.reverse) * (∑ γ, H γ) *
      factorProdOver P H τ (P.evalIndexList)

/-- The exponentiated error `ℰ(τ) = ℱ(τ) - H` of `type.tex:62`. -/
noncomputable def exponentiatedError (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) : ℝ → 𝔸 :=
  fun τ => exponentiatedGenerator P H τ - (∑ γ, H γ)

/-- The interaction-picture generator `τ ↦ e^{-τH} ℰ(τ) e^{τH}` used in `multiplicativeError`. -/
noncomputable def interactionGenerator (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) : ℝ → 𝔸 :=
  fun τ => exp ((-τ) • (∑ γ, H γ)) * exponentiatedError P H τ * exp (τ • (∑ γ, H γ))

/-- The multiplicative error `ℳ(t)` of `type.tex:72`. -/
noncomputable def multiplicativeError (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (t : ℝ) : 𝔸 :=
  timeOrderedExp (interactionGenerator P H) 0 t - 1

/-- `P.eval H τ · invFull = 1`, where `invFull = ∏^{→} e^{-τ a_j H_j}`. -/
lemma eval_mul_invFull [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) (τ : ℝ) :
    P.eval H τ * factorProdOver P H (-τ) (P.evalIndexList.reverse) = 1 := by
  rw [← factorProdOver_evalIndexList P H τ]
  unfold factorProdOver
  have h := List.prod_exp_mul_rev_neg (l := P.evalIndexList)
    (A := fun j => (τ * P.coeff j) • H (P.perm j.1 j.2))
  rw [show (fun j => P.evalFactor H j (-τ)) = fun j =>
      exp (-((τ * P.coeff j) • H (P.perm j.1 j.2))) by
    funext j; exact evalFactor_neg_eq_exp_neg P H j τ]
  simpa [ProductFormulaData.evalFactor, ProductFormulaData.generator, mul_smul] using h

/-- The per-summand identity behind `additiveResidual = 𝒮 · additiveKernel`. -/
lemma eval_mul_kernel_term [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (i : Fin P.Υ × Fin P.Γ) (τ : ℝ) :
    P.eval H τ * (invStrictSuffixFactorProd P H i τ * (P.generator H i) *
        strictSuffixFactorProd P H i τ)
      = prefixFactorProd P H i τ * (P.generator H i) *
          suffixFactorProd P H i τ := by
  have hkey1 := eval_mul_invStrictSuffix P H i τ
  have hcomm := evalFactor_commute_coeffOp P H i τ
  calc
    P.eval H τ * (invStrictSuffixFactorProd P H i τ * (P.generator H i) *
        strictSuffixFactorProd P H i τ)
        = (P.eval H τ * invStrictSuffixFactorProd P H i τ) *
            ((P.generator H i) * strictSuffixFactorProd P H i τ) := by noncomm_ring
    _ = (prefixFactorProd P H i τ * P.evalFactor H i τ) *
            ((P.generator H i) * strictSuffixFactorProd P H i τ) := by rw [hkey1]
    _ = prefixFactorProd P H i τ * (P.generator H i) *
            P.evalFactor H i τ * strictSuffixFactorProd P H i τ := by
            calc
              (prefixFactorProd P H i τ * P.evalFactor H i τ) *
                  ((P.generator H i) * strictSuffixFactorProd P H i τ)
                  = prefixFactorProd P H i τ * (P.evalFactor H i τ *
                      (P.generator H i)) * strictSuffixFactorProd P H i τ := by noncomm_ring
              _ = prefixFactorProd P H i τ * ((P.generator H i) *
                      P.evalFactor H i τ) * strictSuffixFactorProd P H i τ := by rw [hcomm]
              _ = prefixFactorProd P H i τ * (P.generator H i) *
                      P.evalFactor H i τ * strictSuffixFactorProd P H i τ := by noncomm_ring
    _ = prefixFactorProd P H i τ * (P.generator H i) *
            (P.evalFactor H i τ * strictSuffixFactorProd P H i τ) := by noncomm_ring
    _ = prefixFactorProd P H i τ * (P.generator H i) *
            suffixFactorProd P H i τ := by rfl

/-- The additive residual equals `𝒮(τ) · 𝒯(τ)`. -/
lemma additiveResidual_eq_eval_mul_kernel [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData)
    (H : Fin P.Γ → 𝔸) (τ : ℝ) :
    additiveResidual P H τ = P.eval H τ * additiveKernel P H τ := by
  unfold additiveResidual additiveKernel
  rw [mul_sub, Finset.mul_sum]
  have hB : P.eval H τ * (factorProdOver P H (-τ) (P.evalIndexList.reverse) * (∑ γ, H γ) *
      factorProdOver P H τ (P.evalIndexList)) = (∑ γ, H γ) * P.eval H τ := by
    rw [← mul_assoc, ← mul_assoc, eval_mul_invFull P H τ, one_mul,
      show factorProdOver P H τ (P.evalIndexList) = P.eval H τ by
        exact factorProdOver_evalIndexList P H τ]
  rw [hB]; congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (eval_mul_kernel_term P H i τ).symm

/-- The additive kernel is continuous. -/
@[fun_prop]
lemma continuous_additiveKernel (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) :
    Continuous (additiveKernel P H) := by
  unfold additiveKernel invStrictSuffixFactorProd strictSuffixFactorProd
  fun_prop

/-- The exponentiated error is continuous. -/
@[fun_prop]
lemma continuous_exponentiatedError (P : ProductFormulaData) (H : Fin P.Γ → 𝔸) :
    Continuous (exponentiatedError P H) := by
  unfold exponentiatedError exponentiatedGenerator prefixFactorProd invPrefixFactorProd
  fun_prop

/-! ### The three representations of `thm:error_type` -/

/-- `thm:error_type` (additive): `𝒮(t) = e^{tH} + ∫₀ᵗ e^{(t−τ)H} 𝒮(τ) 𝒯(τ) dτ`. -/
theorem errorType_additive [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (t : ℝ) :
    P.eval H t = exp (t • (∑ γ, H γ)) + ∫ τ in 0..t,
      exp ((t - τ) • (∑ γ, H γ)) * P.eval H τ * additiveKernel P H τ := by
  have hH : Continuous (fun _ : ℝ => (∑ γ, H γ)) := continuous_const
  have hR : Continuous (fun τ : ℝ => P.eval H τ * additiveKernel P H τ) :=
    (continuous_eval P H).mul (continuous_additiveKernel P H)
  have hU : ∀ s : ℝ, HasDerivAt (fun r : ℝ => P.eval H r)
      ((fun _ : ℝ => (∑ γ, H γ)) s * P.eval H s +
        (fun τ : ℝ => P.eval H τ * additiveKernel P H τ) s) s := by
    intro s
    have hderiv := eval_hasDerivAt_additive P H s
    have hkey : (∑ γ, H γ) * P.eval H s + P.eval H s * additiveKernel P H s =
        (∑ γ, H γ) * P.eval H s + additiveResidual P H s := by
      rw [additiveResidual_eq_eval_mul_kernel P H s]
    simpa using (hkey ▸ hderiv)
  have hU0 : P.eval H 0 = (1 : 𝔸) := ProductFormulaData.eval_zero P H
  have hduhamel := timeOrderedExp_duhamel (fun _ : ℝ => (∑ γ, H γ))
    (fun τ : ℝ => P.eval H τ * additiveKernel P H τ) hH hR (U := fun τ => P.eval H τ) 1 hU hU0 t
  simp only [hduhamel, timeOrderedExp_const ((∑ γ, H γ)), sub_zero, mul_one]
  congr 1; refine intervalIntegral.integral_congr ?_
  intro τ _; simp [mul_assoc]

/-- `thm:error_type` (exponentiated): `𝒮(t) = exp_T(∫₀ᵗ (H + ℰ(τ)) dτ)`. -/
theorem errorType_exponentiated [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (t : ℝ) :
    P.eval H t = timeOrderedExp (fun τ : ℝ => (∑ γ, H γ) + exponentiatedError P H τ) 0 t := by
  let Hc : ℝ → 𝔸 := fun τ => (∑ γ, H γ) + exponentiatedError P H τ
  have hH : Continuous Hc := continuous_const.add (continuous_exponentiatedError P H)
  have hf : ∀ s : ℝ, HasDerivAt (fun r : ℝ => P.eval H r) (Hc s * P.eval H s) s := by
    intro s
    have hkey : Hc s = exponentiatedGenerator P H s := by
      dsimp [Hc, exponentiatedError]; abel
    simpa [hkey] using (eval_hasDerivAt_exponentiated P H s)
  have hg : ∀ s : ℝ, HasDerivAt (fun r : ℝ => timeOrderedExp Hc 0 r)
      (Hc s * timeOrderedExp Hc 0 s) s :=
    fun s => timeOrderedExp_hasDerivAt Hc hH 0 s
  have heq0 : P.eval H 0 = timeOrderedExp Hc 0 0 := by
    rw [ProductFormulaData.eval_zero P H, timeOrderedExp_initial Hc 0]
  have h := ode_solution_unique Hc hH hf hg 0 heq0
  simpa [Hc] using congr_fun h t

/-- `thm:error_type` (multiplicative): `𝒮(t) = e^{tH} (1 + ℳ(t))`. -/
theorem errorType_multiplicative [NormedAlgebra ℚ 𝔸] (P : ProductFormulaData) (H : Fin P.Γ → 𝔸)
    (t : ℝ) :
    P.eval H t = exp (t • (∑ γ, H γ)) * (1 + multiplicativeError P H t) := by
  let A : ℝ → 𝔸 := fun _ => (∑ γ, H γ)
  let B : ℝ → 𝔸 := exponentiatedError P H
  have hA : Continuous A := continuous_const
  have hB : Continuous B := continuous_exponentiatedError P H
  have hgen : (fun τ : ℝ => timeOrderedExp A τ 0 * B τ * timeOrderedExp A 0 τ) =
      interactionGenerator P H := by
    funext τ
    simp [A, B, interactionGenerator, timeOrderedExp_const ((∑ γ, H γ)) τ 0,
      timeOrderedExp_const ((∑ γ, H γ)) 0 τ]
  rw [errorType_exponentiated P H t, timeOrderedExp_interaction_picture A B hA hB t,
    timeOrderedExp_const ((∑ γ, H γ)) 0 t, hgen]
  unfold multiplicativeError
  simp [show (1 : 𝔸) + (timeOrderedExp (interactionGenerator P H) 0 t - 1) =
      timeOrderedExp (interactionGenerator P H) 0 t by abel]

end TrotterError
