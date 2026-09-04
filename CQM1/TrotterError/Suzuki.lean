/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.ProductFormula

/-!
# The Lie-Trotter and Suzuki formulas

The first-order Lie-Trotter formula `∏_{γ=1}^Γ e^{t K_γ}` (`eq:pf1`) and the higher-order Suzuki
formulas `S_{2k}` (`eq:pf2k`) of arXiv:1912.08854 (`papers/prelim.tex` §2.3), in the paper's
`∏_{γ=1}^Γ A_γ = A_Γ ⋯ A_1` convention (0-based `Fin Γ` here), together with their representation
as `ProductFormulaData` (`lieTrotterData`, `suzuki2Data`, `suzukiData`) and the proof that the two
presentations evaluate identically.

## Main definitions

* `lieTrotter`, `suzuki2`, `suzukiU`, `suzuki`: the recursive closed forms.
* `lieTrotterData`, `suzuki2Data`, `suzukiData`: the `ProductFormulaData` forms.

## Main results

* `lieTrotter_eq_eval`: `lieTrotter K t = (lieTrotterData Γ).eval K t` (`prelim.tex:127,142`).
* `suzuki2_eq_eval`: `suzuki2 K t = (suzuki2Data Γ).eval K t` (`prelim.tex:136,142`).
* `suzuki_eq_eval`: `suzuki k K t = (suzukiData k Γ).eval K t` for `1 ≤ k`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace Finset
open scoped Topology

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]
variable (P : ProductFormulaData Υ Γ)

/-! ### The Lie-Trotter and Suzuki formulas (`prelim.tex:127-146`) -/

/-- The first-order Lie-Trotter formula `∏_{γ=1}^Γ e^{t K_γ} = e^{t K_{Γ-1}} ⋯ e^{t K_0}` (the
paper's `∏_{γ=1}^Γ A_γ = A_Γ ⋯ A_1` convention, in 0-based `Fin Γ`), defined by peeling the
innermost (rightmost) factor `K 0`. -/
noncomputable def lieTrotter {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  match Γ with
  | 0 => 1
  | n + 1 => lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0)

/-- The second-order Suzuki formula, defined recursively by peeling the outermost (index-`0`)
factor: `S₂(K, t) = e^{(t/2)K₀} · S₂(K ∘ Fin.succ, t) · e^{(t/2)K₀}`. This is the ordered product
`e^{(t/2)K₀} ⋯ e^{(t/2)K_{Γ-1}} · e^{(t/2)K_{Γ-1}} ⋯ e^{(t/2)K₀}` (the paper's
`∏_{γ=Γ}^1 e^{(t/2)K_γ} · ∏_{γ=1}^Γ e^{(t/2)K_γ}`, in anti-Hermitian-generator form). -/
noncomputable def suzuki2 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  match Γ with
  | 0 => 1
  | n + 1 => exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0)

/-- `u_k = 1 / (4 - 4^{1/(2k-1)})`, the `eq:pf2k` scaling constant (meaningful for `k ≥ 2`; the
recursion `suzuki (k+2)` below only applies it to an argument `≥ 2`). -/
noncomputable def suzukiU (k : ℕ) : ℝ :=
  (1 : ℝ) / (4 - 4 ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)))

/-- The higher-order Suzuki formula `S_{2k}` (`eq:pf2k`): `suzuki 1 = suzuki2`, and for `k ≥ 2`
`suzuki k K t = suzuki (k-1) K (u_k t)² · suzuki (k-1) K ((1-4u_k) t) · suzuki (k-1) K (u_k t)²`.
The `suzuki 0` case is a junk identity. -/
noncomputable def suzuki {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] :
    ℕ → {Γ : ℕ} → (Fin Γ → 𝔸) → ℝ → 𝔸
  | 0 => fun _ _ => 1
  | 1 => suzuki2
  | k + 2 => fun K t =>
      suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2 *
        suzuki (k + 1) K ((1 - 4 * suzukiU (k + 2)) * t) *
        suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2

/-- The Lie-Trotter formula as a `ProductFormulaData`: `Υ = 1`, all coefficients `1`, identity
permutation (`eq:pf1`). -/
@[reducible] def lieTrotterData (Γ : ℕ) : ProductFormulaData 1 Γ where
  coeff := fun _ => 1
  perm := fun _ => Equiv.refl (Fin Γ)
  coeff_abs_le_one := by intro i; simp

/-- The second-order Suzuki formula as a `ProductFormulaData`: `Υ = 2`, all coefficients `1/2`,
stage `0` in order and stage `1` reversed (`eq:pf2k`). -/
@[reducible] noncomputable def suzuki2Data (Γ : ℕ) : ProductFormulaData 2 Γ where
  coeff := fun _ => (1 / 2 : ℝ)
  perm := fun υ => if υ = 0 then Equiv.refl (Fin Γ) else Fin.revPerm
  coeff_abs_le_one := by intro i; norm_num

/-- `lieTrotterData Γ`'s index list: the single stage `0` in reversed order. -/
lemma lieTrotterData_evalIndexList :
    ProductFormulaData.evalIndexList 1 Γ =
      ((List.finRange Γ).reverse).map (fun γ => ((0 : Fin 1), γ)) := by
  unfold ProductFormulaData.evalIndexList
  have h1 : (List.finRange 1).reverse = [0] := by decide
  rw [h1]
  simp [List.product]

/-- `lieTrotterData Γ` evaluates to `∏_{γ=Γ-1}^0 e^{t H_γ}`. -/
lemma lieTrotterData_eval_eq [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (t : ℝ) :
    (lieTrotterData Γ).eval H t =
      (((List.finRange Γ).reverse).map (fun γ => exp (t • H γ))).prod := by
  change ((ProductFormulaData.evalIndexList 1 Γ).map
      (fun i => (lieTrotterData Γ).evalFactor H i t)).prod =
    (((List.finRange Γ).reverse).map (fun γ => exp (t • H γ))).prod
  rw [lieTrotterData_evalIndexList]
  rw [List.map_map]
  congr 1
  congr 1
  funext γ
  simp [ProductFormulaData.evalFactor, ProductFormulaData.generator]

/-- `lieTrotter` equals the reversed `finRange` product. -/
lemma lieTrotter_eq_prod [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    lieTrotter K t = (((List.finRange Γ).reverse).map (fun γ => exp (t • K γ))).prod := by
  induction Γ with
  | zero => simp [lieTrotter]
  | succ n ih =>
      rw [lieTrotter, ih]
      have hfin : (List.finRange (n + 1)).reverse =
          ((List.finRange n).reverse).map Fin.succ ++ [0] := by
        rw [List.finRange_succ, List.reverse_cons, List.map_reverse]
      rw [hfin, List.map_append, List.prod_append]
      simp only [List.map_map, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Function.comp_def]

/-- `lieTrotter` is `(lieTrotterData Γ).eval` (`prelim.tex:127,142`). -/
theorem lieTrotter_eq_eval [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    lieTrotter K t = (lieTrotterData Γ).eval K t := by
  rw [lieTrotter_eq_prod, lieTrotterData_eval_eq]

/-- Mapping `g ∘ Fin.revPerm` over the reversed `finRange` is mapping `g` over `finRange`. -/
lemma finRange_reverse_map_comp_revPerm {α : Type*} (g : Fin Γ → α) :
    ((List.finRange Γ).reverse).map (g ∘ Fin.revPerm) = (List.finRange Γ).map g := by
  rw [List.finRange_reverse, List.map_map]
  congr 1
  funext γ
  change g (Fin.revPerm (Fin.rev γ)) = g γ
  rw [Fin.revPerm_apply, Fin.rev_rev]

/-- `suzuki2Data Γ`'s index list: stage `1` (reversed) followed by stage `0` (in order). -/
lemma suzuki2Data_evalIndexList :
    ProductFormulaData.evalIndexList 2 Γ =
      ((List.finRange Γ).reverse).map (fun γ => ((1 : Fin 2), γ)) ++
        ((List.finRange Γ).reverse).map (fun γ => ((0 : Fin 2), γ)) := by
  unfold ProductFormulaData.evalIndexList
  have h2 : (List.finRange 2).reverse = [1, 0] := by decide
  rw [h2]
  simp [List.product]

/-- `suzuki2Data Γ` evaluates to the increasing-times-decreasing product. -/
lemma suzuki2Data_eval_eq [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (t : ℝ) :
    (suzuki2Data Γ).eval H t =
      (((List.finRange Γ).map (fun γ => exp ((t / 2) • H γ))).prod) *
        (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • H γ))).prod := by
  change ((ProductFormulaData.evalIndexList 2 Γ).map
    (fun i => (suzuki2Data Γ).evalFactor H i t)).prod =
    (((List.finRange Γ).map (fun γ => exp ((t / 2) • H γ))).prod) *
      (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • H γ))).prod
  rw [suzuki2Data_evalIndexList]
  rw [List.map_append, List.prod_append]
  congr 1
  · rw [List.map_map]
    have hfac : ((List.finRange Γ).reverse).map
        ((fun i => (suzuki2Data Γ).evalFactor H i t) ∘ (fun γ => ((1 : Fin 2), γ))) =
        ((List.finRange Γ).reverse).map ((fun γ : Fin Γ => exp ((t / 2) • H γ)) ∘ Fin.revPerm) := by
      apply congrArg (fun f : Fin Γ → 𝔸 => List.map f ((List.finRange Γ).reverse))
      funext γ
      simp [ProductFormulaData.evalFactor, ProductFormulaData.generator, smul_smul,
        div_eq_mul_inv]
    rw [hfac]
    rw [finRange_reverse_map_comp_revPerm (g := fun γ : Fin Γ => exp ((t / 2) • H γ))]
  · rw [List.map_map]
    congr 1
    apply congrArg (fun f : Fin Γ → 𝔸 => List.map f ((List.finRange Γ).reverse))
    funext γ
    simp [ProductFormulaData.evalFactor, ProductFormulaData.generator, smul_smul,
      div_eq_mul_inv]

/-- `suzuki2` equals the increasing-times-decreasing product. -/
lemma suzuki2_eq_prod [NormedAlgebra ℝ 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    suzuki2 K t = (((List.finRange Γ).map (fun γ => exp ((t / 2) • K γ))).prod) *
        (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • K γ))).prod := by
  induction Γ with
  | zero => simp [suzuki2]
  | succ n ih =>
      rw [suzuki2, ih]
      have hfwd : (List.finRange (n + 1)).map (fun γ => exp ((t / 2) • K γ)) =
          exp ((t / 2) • K 0) :: ((List.finRange n).map (fun γ => exp ((t / 2) • K γ.succ))) := by
        rw [List.finRange_succ]
        simp
      have hrev : (List.finRange (n + 1)).reverse.map (fun γ => exp ((t / 2) • K γ)) =
          ((List.finRange n).reverse.map (fun γ => exp ((t / 2) • K γ.succ))) ++
            [exp ((t / 2) • K 0)] := by
        rw [List.finRange_succ]
        simp
      rw [hfwd, hrev, List.prod_cons, List.prod_append, List.prod_singleton]
      noncomm_ring

/-- `suzuki2` is `(suzuki2Data Γ).eval` (`prelim.tex:136,142`). -/
theorem suzuki2_eq_eval [NormedAlgebra ℝ 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    suzuki2 K t = (suzuki2Data Γ).eval K t := by
  rw [suzuki2_eq_prod, suzuki2Data_eval_eq]

/-! ### The higher-order Suzuki formula as a `ProductFormulaData` -/

/-- For `k ≥ 2`, `4 ^ (1 / (2k-1)) ≤ 2`. -/
lemma suzukiU_rpow_le_two (k : ℕ) (hk : 2 ≤ k) :
    (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ 2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : (1 : ℝ) / (2 * (k : ℝ) - 1) ≤ 1 / 2 := by
    have hdenom : 0 < 2 * (k : ℝ) - 1 := by nlinarith [hk']
    rw [div_le_iff₀ hdenom]
    nlinarith [hk']
  have hrpow : (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (4 : ℝ)) hx
  have h4half : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    have hsq : (√(4:ℝ)) ^ 2 = 2 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : 0 ≤ (4:ℝ))]
      norm_num
    have hnn : 0 ≤ √(4:ℝ) := Real.sqrt_nonneg 4
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right (by intro h; linarith [hnn])
  calc
    (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := hrpow
    _ = 2 := h4half

/-- For `k ≥ 2`, the `suzukiU k` denominator is positive. -/
lemma suzukiU_denom_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < (4 : ℝ) - (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) := by
  have hle := suzukiU_rpow_le_two k hk
  linarith

/-- For `k ≥ 2`, `0 < suzukiU k`. -/
lemma suzukiU_pos (k : ℕ) (hk : 2 ≤ k) : 0 < suzukiU k := by
  unfold suzukiU
  exact div_pos (by norm_num : 0 < (1 : ℝ)) (suzukiU_denom_pos k hk)

/-- For `k ≥ 2`, `suzukiU k ≤ 1 / 2`. -/
lemma suzukiU_le_one_half (k : ℕ) (hk : 2 ≤ k) : suzukiU k ≤ 1 / 2 := by
  unfold suzukiU
  rw [div_le_iff₀ (suzukiU_denom_pos k hk)]
  have hle := suzukiU_rpow_le_two k hk
  nlinarith [hle]

/-- For `k ≥ 2`, `|suzukiU k| ≤ 1`. -/
lemma abs_suzukiU_le_one (k : ℕ) (hk : 2 ≤ k) : |suzukiU k| ≤ 1 := by
  have hpos : 0 ≤ suzukiU k := le_of_lt (suzukiU_pos k hk)
  have hle : suzukiU k ≤ 1 / 2 := suzukiU_le_one_half k hk
  rw [abs_of_nonneg hpos]
  linarith

/-- For `k ≥ 2`, `|1 - 4 * suzukiU k| ≤ 1`. -/
lemma abs_one_sub_four_mul_suzukiU_le_one (k : ℕ) (hk : 2 ≤ k) : |1 - 4 * suzukiU k| ≤ 1 := by
  have hpos : 0 ≤ suzukiU k := le_of_lt (suzukiU_pos k hk)
  have hle : suzukiU k ≤ 1 / 2 := suzukiU_le_one_half k hk
  have h0 : 0 ≤ 4 * suzukiU k := mul_nonneg (by norm_num) hpos
  have h2 : 4 * suzukiU k ≤ 2 := by nlinarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The number of stages `Υ = 2 · 5^{k-1}` of the `k`-th Suzuki formula (`eq:pf2k`). -/
def suzukiStages : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 5 * suzukiStages (k + 1)

/-- The five-fold stage sum produced by the `concat` recursion is `suzukiStages (k + 2)`. -/
lemma suzukiStages_five (k : ℕ) :
    ((((suzukiStages (k + 1) + suzukiStages (k + 1)) + suzukiStages (k + 1))
        + suzukiStages (k + 1)) + suzukiStages (k + 1)) = suzukiStages (k + 2) := by
  rw [show suzukiStages (k + 2) = 5 * suzukiStages (k + 1) from rfl]
  ring

/-- The higher-order Suzuki formula `S_{2k}` as a `ProductFormulaData` (`eq:pf2k`, with
`Υ = 2 · 5^{k-1}` stages and alternately reversed permutations). -/
noncomputable def suzukiData : (k : ℕ) → (Γ : ℕ) → ProductFormulaData (suzukiStages k) Γ
  | 0, Γ => lieTrotterData Γ
  | 1, Γ => suzuki2Data Γ
  | k + 2, Γ =>
      let u := suzukiU (k + 2)
      let P := suzukiData (k + 1) Γ
      let A := ProductFormulaData.scale P u (abs_suzukiU_le_one (k + 2) (by lia))
      let B := ProductFormulaData.scale P (1 - 4 * u)
        (abs_one_sub_four_mul_suzukiU_le_one (k + 2) (by lia))
      ProductFormulaData.castStages (suzukiStages_five k)
        (ProductFormulaData.concat A
          (ProductFormulaData.concat A
            (ProductFormulaData.concat B (ProductFormulaData.concat A A))))

/-- The `(k + 2)`-nd Suzuki data evaluates as the paper's `S_{2k}` recursion
(`eq:pf2k`): `S_{2k}(t) = S_{2k-2}(u_k t)² · S_{2k-2}((1-4u_k) t) · S_{2k-2}(u_k t)²`. -/
lemma suzukiData_succ_eval (k : ℕ) [NormedSpace ℝ 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    (suzukiData (k + 2) Γ).eval K t =
      (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 *
        (suzukiData (k + 1) Γ).eval K ((1 - 4 * suzukiU (k + 2)) * t) *
        (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 := by
  let u : ℝ := suzukiU (k + 2)
  let P : ProductFormulaData (suzukiStages (k + 1)) Γ := suzukiData (k + 1) Γ
  let A : ProductFormulaData (suzukiStages (k + 1)) Γ :=
    ProductFormulaData.scale P u (abs_suzukiU_le_one (k + 2) (by lia))
  let B : ProductFormulaData (suzukiStages (k + 1)) Γ :=
    ProductFormulaData.scale P (1 - 4 * u) (abs_one_sub_four_mul_suzukiU_le_one (k + 2) (by lia))
  change (ProductFormulaData.castStages (suzukiStages_five k)
    (ProductFormulaData.concat A
      (ProductFormulaData.concat A
        (ProductFormulaData.concat B (ProductFormulaData.concat A A))))).eval K t =
    (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 *
      (suzukiData (k + 1) Γ).eval K ((1 - 4 * suzukiU (k + 2)) * t) *
      (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2
  rw [ProductFormulaData.castStages_eval]
  rw [ProductFormulaData.concat_eval, ProductFormulaData.concat_eval,
    ProductFormulaData.concat_eval, ProductFormulaData.concat_eval]
  dsimp only [A, B]
  simp only [ProductFormulaData.scale_eval]
  noncomm_ring

/-- `suzuki (k + 1)` is `(suzukiData (k + 1) Γ).eval`, by induction on `k`. -/
lemma suzuki_succ_eq_eval [NormedAlgebra ℝ 𝔸]
    (K : Fin Γ → 𝔸) (k : ℕ) (t : ℝ) :
    suzuki (k + 1) K t = (suzukiData (k + 1) Γ).eval K t := by
  induction k generalizing t with
  | zero =>
      change suzuki2 K t = (suzuki2Data Γ).eval K t
      exact suzuki2_eq_eval K t
  | succ k ih =>
      rw [show suzuki (k + 2) K t =
          suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2 *
            suzuki (k + 1) K ((1 - 4 * suzukiU (k + 2)) * t) *
            suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2 from rfl]
      rw [ih (suzukiU (k + 2) * t), ih ((1 - 4 * suzukiU (k + 2)) * t)]
      rw [suzukiData_succ_eval]

/-- `suzuki` is `(suzukiData k Γ).eval` (`prelim.tex:136,142`), for the meaningful range `1 ≤ k`
(the `suzuki 0` case is a junk identity). -/
theorem suzuki_eq_eval [NormedAlgebra ℝ 𝔸]
    (K : Fin Γ → 𝔸) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    suzuki k K t = (suzukiData k Γ).eval K t := by
  cases k with
  | zero => lia
  | succ k => exact suzuki_succ_eq_eval K k t

end TrotterError
