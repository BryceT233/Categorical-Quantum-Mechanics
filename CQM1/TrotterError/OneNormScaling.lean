/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.Integrals
public import CQM1.TrotterError.ProductFormula
public import CQM1.TrotterError.OrderCondition

/-!
# Trotter error with `1`-norm scaling

This file states `lem:trotter_error_one_norm_scaling` and
`cor:trotter_number_one_norm_scaling` of arXiv:1912.08854 (§2.3): the Trotter
error of a `p`-th order product formula is bounded by a `1`-norm scaling, and the
corresponding Trotter number.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace
open Asymptotics
open scoped Topology BigOperators ContDiff

/-! ### Smoothness of the exponential -/

/-- `t ↦ exp (t • Σ_i H_i)` is smooth. -/
lemma contDiff_exp_sum {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {ι : Type*} [Fintype ι] (H : ι → 𝔸) :
    ContDiff ℝ ∞ (fun t : ℝ => exp (t • ∑ i : ι, H i)) :=
  contDiff_exp_smul_const (∑ i : ι, H i)

/-! ### Norm bounds for the derivatives -/

/-- Norm bound for the `(p+1)`-st derivative of `s ↦ exp (s • Σ_i H_i)`, valid for all `s`. -/
lemma norm_iteratedDeriv_exp_sum_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] {ι : Type*} [Fintype ι]
    (H : ι → 𝔸) (p : ℕ) (s : ℝ) :
    ‖iteratedDeriv (p + 1) (fun r : ℝ => exp (r • ∑ i : ι, H i)) s‖ ≤
      (∑ i : ι, ‖H i‖) ^ (p + 1) * Real.exp (|s| * ∑ i : ι, ‖H i‖) := by
  rw [iteratedDeriv_exp_smul_const (A := ∑ i : ι, H i) (q := p + 1)]
  calc
    ‖(∑ i : ι, H i) ^ (p + 1) * exp (s • ∑ i : ι, H i)‖
        ≤ ‖(∑ i : ι, H i) ^ (p + 1)‖ * ‖exp (s • ∑ i : ι, H i)‖ := norm_mul_le _ _
    _ ≤ ‖∑ i : ι, H i‖ ^ (p + 1) * Real.exp ‖s • ∑ i : ι, H i‖ := mul_le_mul (norm_pow_le _ _)
          (norm_exp_le (s • ∑ i : ι, H i)) (norm_nonneg _) (pow_nonneg (norm_nonneg _) (p + 1))
    _ = ‖∑ i : ι, H i‖ ^ (p + 1) * Real.exp (|s| * ‖∑ i : ι, H i‖) := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (∑ i : ι, ‖H i‖) ^ (p + 1) * Real.exp (|s| * ∑ i : ι, ‖H i‖) := by
        have hsum : ‖∑ i : ι, H i‖ ≤ ∑ i : ι, ‖H i‖ := norm_sum_le Finset.univ H
        have hS : 0 ≤ ∑ i : ι, ‖H i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsum (p + 1))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (abs_nonneg s)))
          (Real.exp_nonneg _) (pow_nonneg hS (p + 1))

/-- Norm bound for the `(p+1)`-st derivative of `s ↦ exp (s • Σ_i H_i)` for `0 ≤ u ≤ 1`, `0 ≤ t`. -/
lemma norm_iteratedDeriv_exp_sum_le_of_nonneg {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    {ι : Type*} [Fintype ι]
    (H : ι → 𝔸) (p : ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖iteratedDeriv (p + 1) (fun r : ℝ => exp (r • ∑ i : ι, H i)) (u * t)‖ ≤
      (∑ i : ι, ‖H i‖) ^ (p + 1) * Real.exp (t * ∑ i : ι, ‖H i‖) := by
  have h := norm_iteratedDeriv_exp_sum_le H p (u * t)
  refine h.trans ?_
  have hS : 0 ≤ ∑ i : ι, ‖H i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have harg : |u * t| * ∑ i : ι, ‖H i‖ ≤ t * ∑ i : ι, ‖H i‖ := by
    have habs : |u * t| ≤ t := by
      rw [abs_of_nonneg (mul_nonneg hu0 ht)]
      simpa using mul_le_mul_of_nonneg_right hu1 ht
    exact mul_le_mul_of_nonneg_right habs hS
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (pow_nonneg hS (p + 1))

/-- The `(p+1)`-st derivative of the error `F = eval − exp` is bounded by the paper's
two-term bound (prelim.tex:186–187), valid for `0 ≤ u ≤ 1`, `0 ≤ t`. -/
lemma norm_iteratedDeriv_F_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s - exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t)‖ ≤
      ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)
        + (∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * ∑ γ : Fin P.Γ, ‖H γ‖) := by
  have hsub : iteratedDeriv (p + 1)
      (fun s : ℝ => P.eval H s - exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t) =
      iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t) -
        iteratedDeriv (p + 1) (fun s : ℝ => exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t) :=
        iteratedDeriv_sub ((contDiff_eval P H).of_le (mod_cast le_top)).contDiffAt
          ((contDiff_exp_sum H).of_le (mod_cast le_top)).contDiffAt
  rw [hsub]
  calc
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t) -
        iteratedDeriv (p + 1) (fun s : ℝ => exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t)‖
        ≤ ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ +
            ‖iteratedDeriv (p + 1) (fun s : ℝ => exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t)‖ :=
              norm_sub_le _ _
    _ ≤ ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
        Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)
          + (∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * ∑ γ : Fin P.Γ, ‖H γ‖) := add_le_add
          (P.eval_iteratedDeriv_norm_le H p u t ht hu0 hu1)
          (norm_iteratedDeriv_exp_sum_le_of_nonneg H p u t ht hu0 hu1)

/-- If the first `p` iterated derivatives of `F` vanish at `0` and `F⁽ᵖ⁺¹⁾` is bounded by `D`
on `u·t` for `u ∈ [0,1]`, then `‖F t‖ ≤ t^(p+1)/(p+1)! · D` for `t ≥ 0`
(Taylor's theorem with integral remainder, prelim.tex:168–172). -/
lemma norm_taylor_le_of_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ (p + 1) F)
    (h0 : ∀ k ≤ p, iteratedDeriv k F 0 = 0) (t : ℝ) (ht : 0 ≤ t) {D : ℝ}
    (hD : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDeriv (p + 1) F (u * t)‖ ≤ D) :
    ‖F t‖ ≤ t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * D := by
  let C : ℝ := t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ)
  have hC : 0 ≤ C := div_nonneg (pow_nonneg ht (p + 1)) (by positivity)
  have hTaylor := taylor_integral_remainder_iteratedDeriv_zero_paper (p := p) (t := t) hF h0
  rw [hTaylor]
  have hderiv_cont : Continuous (fun s : ℝ => iteratedDeriv (p + 1) F s) :=
    hF.continuous_iteratedDeriv'
  have hf_cont : Continuous (fun u : ℝ => (1 - u) ^ p * C * ‖iteratedDeriv (p + 1) F (u * t)‖) := by
    fun_prop
  have hg_cont : Continuous (fun u : ℝ => (1 - u) ^ p * C * D) := by fun_prop
  have hmono : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (1 - u) ^ p * C * ‖iteratedDeriv (p + 1) F (u * t)‖ ≤ (1 - u) ^ p * C * D := by
    intro u hu
    have hscalar : 0 ≤ (1 - u) ^ p * C := mul_nonneg (pow_nonneg (by linarith [hu.2]) p) hC
    exact mul_le_mul_of_nonneg_left (hD u hu) hscalar
  calc
    ‖(p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
        ((1 - u) ^ p * C) • iteratedDeriv (p + 1) F (u * t)‖
        = (p + 1 : ℝ) * ‖∫ u in (0 : ℝ)..(1 : ℝ),
            ((1 - u) ^ p * C) • iteratedDeriv (p + 1) F (u * t)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (p + 1 : ℝ))]
    _ ≤ (p + 1 : ℝ) * ∫ u in (0 : ℝ)..(1 : ℝ),
            ‖((1 - u) ^ p * C) • iteratedDeriv (p + 1) F (u * t)‖ := mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm (show (0 : ℝ) ≤ 1 by norm_num))
              (by positivity)
    _ = (p + 1 : ℝ) * ∫ u in (0 : ℝ)..(1 : ℝ),
            (1 - u) ^ p * C * ‖iteratedDeriv (p + 1) F (u * t)‖ := by
            congr 1
            apply intervalIntegral.integral_congr_uIoo
            intro u hu
            rw [Set.uIoo_of_lt (show (0 : ℝ) < 1 by norm_num)] at hu
            have hscalar : 0 ≤ (1 - u) ^ p * C := mul_nonneg (pow_nonneg (by linarith [hu.2]) p) hC
            simp only
            rw [norm_smul, Real.norm_of_nonneg hscalar]
    _ ≤ (p + 1 : ℝ) * ∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p * C * D :=
            mul_le_mul_of_nonneg_left
              (intervalIntegral.integral_mono_on
              (a := 0) (b := 1) (by norm_num) (hf_cont.intervalIntegrable 0 1)
              (hg_cont.intervalIntegrable 0 1) hmono) (by positivity)
    _ = t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * D := by
        have hconst : (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p * C * D) =
            C * D * (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p) := by
          rw [show (fun u => (1 - u) ^ p * C * D) = fun u => (C * D) * (1 - u) ^ p by
            funext u; ring]
          simp only [intervalIntegral.integral_const_mul]
        rw [hconst, intervalIntegral_one_sub_pow]
        dsimp [C]; field_simp
        push_cast; ring

/-- For `t ≤ 0` near `0`, the target `(S·t)^{p+1} e^{t·a}` dominates `t^{p+1}`. -/
lemma isBigO_pow_le_target_left {a S : ℝ} (p : ℕ) (hS : 0 < S) (ha : 0 ≤ a) :
    (fun t : ℝ => t ^ (p + 1)) =O[𝓝[≤] (0 : ℝ)]
      (fun t : ℝ => (S * t) ^ (p + 1) * Real.exp (t * a)) := by
  refine IsBigO.of_bound (Real.exp a / S ^ (p + 1)) ?_
  have ht_nonpos : ∀ᶠ t in 𝓝[≤] (0 : ℝ), t ≤ 0 := self_mem_nhdsWithin
  have ht_ge : ∀ᶠ t in 𝓝[≤] (0 : ℝ), -(1 : ℝ) ≤ t :=
    ((eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono nhdsWithin_le_nhds).mono
      (fun t ht => le_of_lt ht)
  filter_upwards [ht_nonpos, ht_ge] with t ht0 ht1
  have hgnorm : ‖(S * t) ^ (p + 1) * Real.exp (t * a)‖ =
      S ^ (p + 1) * |t| ^ (p + 1) * Real.exp (t * a) := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Real.exp_nonneg (t * a)),
      abs_mul, abs_of_nonneg hS.le, mul_pow]
  have hexp : 1 ≤ Real.exp a * Real.exp (t * a) := by
    rw [← Real.exp_zero, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (show 0 ≤ 1 + t by linarith)])
  rw [norm_pow, Real.norm_eq_abs, hgnorm]
  calc
    |t| ^ (p + 1) = 1 * |t| ^ (p + 1) := by ring
    _ ≤ (Real.exp a * Real.exp (t * a)) * |t| ^ (p + 1) := by gcongr
    _ = (Real.exp a / S ^ (p + 1)) * (S ^ (p + 1) * |t| ^ (p + 1) * Real.exp (t * a)) := by
          field_simp [hS.ne']

/-- The paper's explicit bound (eq:trotter_error_one_norm_scaling_bound), simplified to the
target scaling for `0 ≤ t ≤ 1`. -/
lemma paper_bound_le_target (Υ : ℕ) (S : ℝ) (p : ℕ) (t : ℝ) (hS : 0 ≤ S) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
        (((Υ : ℝ) * S) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * S) + S ^ (p + 1) * Real.exp (t * S))
      ≤ (S * t) ^ (p + 1) *
          (((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) + Real.exp S) /
            (Nat.factorial (p + 1) : ℝ)) *
        Real.exp (t * (Υ : ℝ) * S) := by
  have h_expΥ : Real.exp (t * (Υ : ℝ) * S) ≤ Real.exp ((Υ : ℝ) * S) := Real.exp_le_exp.mpr
    (by calc
      t * (Υ : ℝ) * S = t * ((Υ : ℝ) * S) := by ring
      _ ≤ 1 * ((Υ : ℝ) * S) := by gcongr
      _ = (Υ : ℝ) * S := by ring)
  have h_expS : Real.exp (t * S) ≤ Real.exp S := Real.exp_le_exp.mpr
    (by calc
      t * S ≤ 1 * S := by gcongr
      _ = S := by ring)
  have h_exp_ge_one : 1 ≤ Real.exp (t * (Υ : ℝ) * S) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hpow : ((Υ : ℝ) * S) ^ (p + 1) = (Υ : ℝ) ^ (p + 1) * S ^ (p + 1) := by
    rw [mul_pow]
  calc
    t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
        (((Υ : ℝ) * S) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * S) + S ^ (p + 1) * Real.exp (t * S))
        = (S * t) ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
            ((Υ : ℝ) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * S) + Real.exp (t * S)) := by
            rw [hpow, mul_pow]
            ring
    _ ≤ (S * t) ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
            ((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) + Real.exp S) := by
            gcongr
    _ ≤ (S * t) ^ (p + 1) * (((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) + Real.exp S) /
      (Nat.factorial (p + 1) : ℝ))
          * Real.exp (t * (Υ : ℝ) * S) := by
            have hA : 0 ≤ (S * t) ^ (p + 1) *
                (((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) + Real.exp S) /
                  (Nat.factorial (p + 1) : ℝ)) := by
              positivity
            rw [show (S * t) ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
                ((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) + Real.exp S)
                = (S * t) ^ (p + 1) * (((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) +
                    Real.exp S) / (Nat.factorial (p + 1) : ℝ)) by ring]
            simpa using (mul_le_mul_of_nonneg_left h_exp_ge_one hA)

/-- `eq:trotter_error_one_norm_scaling_bound`: the explicit pointwise Trotter-error bound,
valid for all `t ≥ 0`. -/
theorem trotter_error_bound_one_norm_scaling (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (h_order : P.IsOrderOf p H) :
    ∀ t : ℝ, 0 ≤ t →
      ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖ ≤
        t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
          (((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) *
              Real.exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) +
            (∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * ∑ γ : Fin P.Γ, ‖H γ‖)) := by
  let F : ℝ → 𝔸 := fun t => P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)
  have hF_smooth : ContDiff ℝ ∞ F := (contDiff_eval P H).sub (contDiff_exp_sum H)
  have h0 : ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0 :=
    (isBigO_norm_iff_iteratedDeriv_eq_zero F p hF_smooth).1 h_order
  have hF_p1 : ContDiff ℝ (p + 1) F := hF_smooth.of_le (mod_cast le_top)
  intro t ht
  refine norm_taylor_le_of_deriv_bound F p hF_p1 h0 t ht ?_
  intro u hu
  exact norm_iteratedDeriv_F_le P H p u t ht hu.1 hu.2

/-- `lem:trotter_error_one_norm_scaling` (general branch): for a `p`-th order product
formula, `‖𝒮(t) − e^{tH}‖ = 𝒪((Σ_γ ‖H_γ‖ t)^{p+1} e^{tΥ Σ_γ ‖H_γ‖})` as `t → 0`. -/
theorem trotter_error_one_norm_scaling (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (h_order : P.IsOrderOf p H) :
    (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖) =O[𝓝 (0 : ℝ)]
      (fun t : ℝ ↦ ((∑ γ : Fin P.Γ, ‖H γ‖) * t) ^ (p + 1) *
        exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)) := by
  let S : ℝ := ∑ γ : Fin P.Γ, ‖H γ‖
  let F : ℝ → 𝔸 := fun t => P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)
  let g : ℝ → ℝ := fun t => (S * t) ^ (p + 1) * Real.exp (t * (P.Υ : ℝ) * S)
  by_cases hS : S = 0
  · have hH_zero : ∀ γ : Fin P.Γ, H γ = 0 := by
      intro γ
      have hle : ‖H γ‖ ≤ S := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
      have hnorm : ‖H γ‖ = 0 := by
        have : ‖H γ‖ ≤ 0 := by simpa [hS] using hle
        exact le_antisymm this (norm_nonneg _)
      exact norm_eq_zero.mp hnorm
    have hF_zero : ∀ t : ℝ, F t = 0 := by
      intro t
      simp [F, ProductFormulaData.eval, ProductFormulaData.evalFactor,
        ProductFormulaData.generator, hH_zero]
    refine IsBigO.of_bound 1 ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg (F t)), hF_zero t]
    simpa using (norm_nonneg (((∑ γ : Fin P.Γ, ‖H γ‖) * t) ^ (p + 1) *
      exp (t * (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖)))
  · have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun γ _ => norm_nonneg _)
    let C₁ : ℝ := ((P.Υ : ℝ) ^ (p + 1) * Real.exp ((P.Υ : ℝ) * S) + Real.exp S) /
      (Nat.factorial (p + 1) : ℝ)
    have hO_ge : (fun t : ℝ => ‖F t‖) =O[𝓝[≥] (0 : ℝ)] g := by
      refine IsBigO.of_bound C₁ ?_
      have ht_le_one : ∀ᶠ t in 𝓝[≥] (0 : ℝ), t ≤ 1 :=
        ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds).mono
          (fun t ht => le_of_lt ht)
      have ht_nonneg : ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ t := self_mem_nhdsWithin
      filter_upwards [ht_nonneg, ht_le_one] with t ht0 ht1
      rw [Real.norm_of_nonneg (norm_nonneg (F t))]
      calc
        ‖F t‖ ≤ t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
            (((P.Υ : ℝ) * S) ^ (p + 1) * Real.exp (t * (P.Υ : ℝ) * S) +
              S ^ (p + 1) * Real.exp (t * S)) :=
              trotter_error_bound_one_norm_scaling P H p h_order t ht0
        _ ≤ (S * t) ^ (p + 1) * C₁ * Real.exp (t * (P.Υ : ℝ) * S) :=
              paper_bound_le_target P.Υ S p t hS_nonneg ht0 ht1
        _ = C₁ * ‖g t‖ := by
              change (S * t) ^ (p + 1) * C₁ * Real.exp (t * (P.Υ : ℝ) * S) =
                C₁ * ‖(S * t) ^ (p + 1) * Real.exp (t * (P.Υ : ℝ) * S)‖
              rw [Real.norm_of_nonneg (by positivity)]
              ring
    have hO_le : (fun t : ℝ => ‖F t‖) =O[𝓝[≤] (0 : ℝ)] g := by
      have h1 : (fun t : ℝ => t ^ (p + 1)) =O[𝓝[≤] (0 : ℝ)] g := by
        refine (isBigO_pow_le_target_left p (lt_of_le_of_ne hS_nonneg (Ne.symm hS))
          (mul_nonneg (Nat.cast_nonneg P.Υ) hS_nonneg)).trans_eventuallyEq ?_
        filter_upwards with t
        dsimp [g]
        rw [show t * ((P.Υ : ℝ) * S) = t * (P.Υ : ℝ) * S by ring]
      exact (h_order.mono nhdsWithin_le_nhds).trans h1
    have hO_sup : (fun t : ℝ => ‖F t‖) =O[𝓝[≥] (0 : ℝ) ⊔ 𝓝[≤] (0 : ℝ)] g :=
      IsBigO.sup hO_ge hO_le
    have hsup_eq : 𝓝[≥] (0 : ℝ) ⊔ 𝓝[≤] (0 : ℝ) = 𝓝 (0 : ℝ) := by
      rw [sup_comm]
      simpa using (nhdsWithinLE_sup_nhdsWithinGE (a := (0 : ℝ)) (s := Set.univ))
    simpa [hsup_eq, F, g, S, Real.exp_eq_exp_ℝ] using hO_sup

/-- Per-factor norm bound in the anti-Hermitian case: the exponential factor is unitary. -/
lemma norm_factor_le_skew (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (i : Fin P.Υ × Fin P.Γ) (q : ℕ) (u t : ℝ) :
    ‖(P.generator H i) ^ q *
        exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖
      ≤ ‖H (P.perm i.1 i.2)‖ ^ q := by
  have hA_skew : star (P.generator H i) =
      -(P.generator H i) :=
    star_smul_of_skew (h_skew (P.perm i.1 i.2))
  have hnorm_exp : ‖exp ((u * t) • (P.generator H i))‖ = 1 :=
    norm_exp_smul_of_skewAdjoint hA_skew (u * t)
  have hA_le : ‖P.generator H i‖ ≤ ‖H (P.perm i.1 i.2)‖ :=
    norm_smul_le_of_abs_le_one (P.coeff i)
      (H (P.perm i.1 i.2)) (P.coeff_abs_le_one i)
  have harg : (u * t * P.coeff i) • H (P.perm i.1 i.2) =
      (u * t) • (P.generator H i) := by
    rw [mul_smul, ProductFormulaData.generator]
  rw [harg]
  calc
    ‖(P.generator H i) ^ q *
        exp ((u * t) • (P.generator H i))‖
        ≤ ‖(P.generator H i) ^ q‖ *
            ‖exp ((u * t) • (P.generator H i))‖ := norm_mul_le
              ((P.generator H i) ^ q)
              (exp ((u * t) • (P.generator H i)))
    _ ≤ ‖P.generator H i‖ ^ q := by
            rw [hnorm_exp, mul_one]
            exact norm_pow_le (P.generator H i) q
    _ ≤ ‖H (P.perm i.1 i.2)‖ ^ q := pow_le_pow_left₀ (norm_nonneg _) hA_le q

/-- The norm of the product in `𝔸` of the derivative factors is bounded by the product of the
per-factor norms, in the anti-Hermitian case (no exponential factor). -/
lemma norm_derivProd_le_skew (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (q : Fin P.Υ × Fin P.Γ → ℕ) (u t : ℝ) :
    ‖P.derivProd H q (u * t)‖ ≤
      ∏ i : Fin P.Υ × Fin P.Γ, ‖H (P.perm i.1 i.2)‖ ^ q i := by
  let g : Fin P.Υ × Fin P.Γ → 𝔸 := fun i =>
    (P.generator H i) ^ q i *
      exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))
  have hflat : P.derivProd H q (u * t) = (P.evalIndexList.map g).prod :=
    (ProductFormulaData.evalIndexList_map_prod P g).symm
  calc
    ‖P.derivProd H q (u * t)‖ = ‖(P.evalIndexList.map g).prod‖ := by rw [hflat]
    _ ≤ (P.evalIndexList.map (fun i => ‖g i‖)).prod := by
        simpa [List.map_map, Function.comp_def] using List.norm_prod_le (P.evalIndexList.map g)
    _ = ∏ i : Fin P.Υ × Fin P.Γ, ‖g i‖ := by
        rw [ProductFormulaData.evalIndexList_map_prod P (fun i => ‖g i‖),
          ProductFormulaData.nested_prod_eq_finset_prod (fun i => ‖g i‖)]
    _ ≤ ∏ i : Fin P.Υ × Fin P.Γ, ‖H (P.perm i.1 i.2)‖ ^ q i := Finset.prod_le_prod
      (fun i _ => norm_nonneg _) (fun i _ => norm_factor_le_skew P H h_skew i (q i) u t)

/-- The `(p+1)`-st derivative of `eval` is bounded by `(Υ·Σ_γ ‖H_γ‖)^{p+1}` in the
anti-Hermitian case. -/
lemma eval_iteratedDeriv_norm_le_skew (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (p : ℕ) (u t : ℝ) :
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ ≤
      ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) := by
  let B : Fin P.Υ × Fin P.Γ → ℝ := fun i => ‖H (P.perm i.1 i.2)‖
  have hB : (∑ i : Fin P.Υ × Fin P.Γ, B i) = (P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖ :=
    ProductFormulaData.sum_norm_prod P H
  rw [P.eval_iteratedDeriv_succ H p (u * t)]
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
              (∏ i : Fin P.Υ × Fin P.Γ, B i ^ q i) := by
            apply Finset.sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_left (norm_derivProd_le_skew P H h_skew q u t)
              (Nat.cast_nonneg _)
    _ = ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) := by
        rw [← Finset.sum_pow_eq_sum_piAntidiag
          (Finset.univ : Finset (Fin P.Υ × Fin P.Γ)) B (p + 1), hB]

/-- Norm bound for the `(p+1)`-st derivative of `s ↦ exp (s • Σ_i H_i)` in the
anti-Hermitian case. -/
lemma norm_iteratedDeriv_exp_sum_le_skew {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] {ι : Type*} [Fintype ι]
    (H : ι → 𝔸) (p : ℕ) (h_skew_sum : star (∑ i : ι, H i) = -(∑ i : ι, H i)) (s : ℝ) :
    ‖iteratedDeriv (p + 1) (fun r : ℝ => exp (r • ∑ i : ι, H i)) s‖ ≤
      (∑ i : ι, ‖H i‖) ^ (p + 1) := by
  rw [iteratedDeriv_exp_smul_const (A := ∑ i : ι, H i) (q := p + 1)]
  calc
    ‖(∑ i : ι, H i) ^ (p + 1) * exp (s • ∑ i : ι, H i)‖
        ≤ ‖(∑ i : ι, H i) ^ (p + 1)‖ * ‖exp (s • ∑ i : ι, H i)‖ := norm_mul_le _ _
    _ ≤ ‖∑ i : ι, H i‖ ^ (p + 1) * 1 := mul_le_mul (norm_pow_le _ _)
          (le_of_eq (norm_exp_smul_of_skewAdjoint h_skew_sum s))
          (norm_nonneg _) (pow_nonneg (norm_nonneg _) (p + 1))
    _ ≤ (∑ i : ι, ‖H i‖) ^ (p + 1) := by
        have hsum : ‖∑ i : ι, H i‖ ≤ ∑ i : ι, ‖H i‖ := norm_sum_le Finset.univ H
        simpa using (pow_le_pow_left₀ (norm_nonneg _) hsum (p + 1))

/-- The `(p+1)`-st derivative of the error is bounded by `(ΥS)^{p+1} + S^{p+1}` in the
anti-Hermitian case, for all `u`, `t`. -/
lemma norm_iteratedDeriv_F_le_skew (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (p : ℕ) (u t : ℝ) :
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s - exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t)‖ ≤
      ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) + (∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) := by
  have h_skew_sum : star (∑ γ : Fin P.Γ, H γ) = -(∑ γ : Fin P.Γ, H γ) :=
    sum_skewAdjoint H h_skew
  have hsub : iteratedDeriv (p + 1)
      (fun s : ℝ => P.eval H s - exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t) =
      iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t) -
        iteratedDeriv (p + 1) (fun s : ℝ => exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t) :=
    iteratedDeriv_sub ((contDiff_eval P H).of_le (mod_cast le_top)).contDiffAt
      ((contDiff_exp_sum H).of_le (mod_cast le_top)).contDiffAt
  rw [hsub]
  calc
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t) -
        iteratedDeriv (p + 1) (fun s : ℝ => exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t)‖
        ≤ ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ +
            ‖iteratedDeriv (p + 1) (fun s : ℝ => exp (s • ∑ γ : Fin P.Γ, H γ)) (u * t)‖ :=
              norm_sub_le _ _
    _ ≤ ((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) + (∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) :=
        add_le_add (eval_iteratedDeriv_norm_le_skew P H h_skew p u t)
          (norm_iteratedDeriv_exp_sum_le_skew H p h_skew_sum (u * t))

/-- `eq:trotter_error_one_norm_scaling_bound` in the anti-Hermitian case: the explicit pointwise
bound, valid for all `t ≥ 0`. -/
theorem trotter_error_bound_one_norm_scaling_of_skew_adjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (h_order : P.IsOrderOf p H) :
    ∀ t : ℝ, 0 ≤ t →
      ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖ ≤
        t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
          (((P.Υ : ℝ) * ∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1) +
            (∑ γ : Fin P.Γ, ‖H γ‖) ^ (p + 1)) := by
  let F : ℝ → 𝔸 := fun t => P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)
  have hF_smooth : ContDiff ℝ ∞ F := (contDiff_eval P H).sub (contDiff_exp_sum H)
  have h0 : ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0 :=
    (isBigO_norm_iff_iteratedDeriv_eq_zero F p hF_smooth).1 h_order
  have hF_p1 : ContDiff ℝ (p + 1) F := hF_smooth.of_le (mod_cast le_top)
  intro t ht
  refine norm_taylor_le_of_deriv_bound F p hF_p1 h0 t ht ?_
  intro u hu
  exact norm_iteratedDeriv_F_le_skew P H h_skew p u t

/-- `lem:trotter_error_one_norm_scaling` (anti-Hermitian branch): the exponential
factor drops out when the `H_γ` are anti-Hermitian. -/
theorem trotter_error_one_norm_scaling_of_skew_adjoint (P : ProductFormulaData) {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (h_order : P.IsOrderOf p H) :
    (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)‖) =O[𝓝 (0 : ℝ)]
      (fun t : ℝ ↦ ((∑ γ : Fin P.Γ, ‖H γ‖) * t) ^ (p + 1)) := by
  let S : ℝ := ∑ γ : Fin P.Γ, ‖H γ‖
  let F : ℝ → 𝔸 := fun t => P.eval H t - exp (t • ∑ γ : Fin P.Γ, H γ)
  let g : ℝ → ℝ := fun t => (S * t) ^ (p + 1)
  by_cases hS : S = 0
  · have hH_zero : ∀ γ : Fin P.Γ, H γ = 0 := by
      intro γ
      have hle : ‖H γ‖ ≤ S := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
      have hnorm : ‖H γ‖ = 0 := by
        have : ‖H γ‖ ≤ 0 := by simpa [hS] using hle
        exact le_antisymm this (norm_nonneg _)
      exact norm_eq_zero.mp hnorm
    have hF_zero : ∀ t : ℝ, F t = 0 := by
      intro t
      dsimp [F]
      simp [ProductFormulaData.eval, ProductFormulaData.evalFactor,
        ProductFormulaData.generator, hH_zero]
    refine IsBigO.of_bound 1 ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg (F t)), hF_zero t]
    simpa using (norm_nonneg (((∑ γ : Fin P.Γ, ‖H γ‖) * t) ^ (p + 1)))
  · have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun γ _ => norm_nonneg _)
    let C₁ : ℝ := ((P.Υ : ℝ) ^ (p + 1) + 1) / (Nat.factorial (p + 1) : ℝ)
    have hO_ge : (fun t : ℝ => ‖F t‖) =O[𝓝[≥] (0 : ℝ)] g := by
      refine IsBigO.of_bound C₁ ?_
      have ht_nonneg : ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ t := self_mem_nhdsWithin
      filter_upwards [ht_nonneg] with t ht0
      rw [Real.norm_of_nonneg (norm_nonneg (F t))]
      calc
        ‖F t‖ ≤ t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) *
            (((P.Υ : ℝ) * S) ^ (p + 1) + S ^ (p + 1)) :=
              trotter_error_bound_one_norm_scaling_of_skew_adjoint P H p h_skew h_order t ht0
        _ = (S * t) ^ (p + 1) * C₁ := by
              simp_rw [mul_pow]
              dsimp [C₁]
              field_simp
        _ = C₁ * ‖g t‖ := by
              change (S * t) ^ (p + 1) * C₁ = C₁ * ‖(S * t) ^ (p + 1)‖
              rw [Real.norm_of_nonneg (by positivity : 0 ≤ (S * t) ^ (p + 1))]
              ring
    have hO_le : (fun t : ℝ => ‖F t‖) =O[𝓝[≤] (0 : ℝ)] g := by
      have h1 : (fun t : ℝ => t ^ (p + 1)) =O[𝓝[≤] (0 : ℝ)] g := by
        refine (isBigO_pow_le_target_left p (lt_of_le_of_ne hS_nonneg (Ne.symm hS))
          (le_refl 0)).trans_eventuallyEq ?_
        filter_upwards with t
        dsimp [g]
        rw [mul_zero, Real.exp_zero, mul_one]
      exact (h_order.mono nhdsWithin_le_nhds).trans h1
    have hO_sup : (fun t : ℝ => ‖F t‖) =O[𝓝[≥] (0 : ℝ) ⊔ 𝓝[≤] (0 : ℝ)] g :=
      IsBigO.sup hO_ge hO_le
    have hsup_eq : 𝓝[≥] (0 : ℝ) ⊔ 𝓝[≤] (0 : ℝ) = 𝓝 (0 : ℝ) := by
      rw [sup_comm]
      simpa using (nhdsWithinLE_sup_nhdsWithinGE (a := (0 : ℝ)) (s := Set.univ))
    simpa [hsup_eq, F, g, S] using hO_sup

/-- Telescoping bound: if `‖A‖ ≤ 1` and `‖B‖ ≤ 1`, then `‖A^r − B^r‖ ≤ r · ‖A − B‖`. -/
lemma norm_pow_sub_pow_le_of_norm_le_one {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    (A B : 𝔸) (r : ℕ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A ^ r - B ^ r‖ ≤ (r : ℝ) * ‖A - B‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hBpow : ‖B ^ r‖ ≤ 1 := (norm_pow_le B r).trans (by
          simpa using pow_le_pow_left₀ (norm_nonneg B) hB r)
      calc
        ‖A ^ (r + 1) - B ^ (r + 1)‖
            = ‖(A ^ r - B ^ r) * A + B ^ r * (A - B)‖ := by
                congr 1
                rw [pow_succ, pow_succ, sub_mul, mul_sub]
                abel
        _ ≤ ‖(A ^ r - B ^ r) * A‖ + ‖B ^ r * (A - B)‖ := norm_add_le _ _
        _ ≤ ‖A ^ r - B ^ r‖ * ‖A‖ + ‖B ^ r‖ * ‖A - B‖ :=
                add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ‖A ^ r - B ^ r‖ + ‖A - B‖ := by
                refine add_le_add ?_ ?_
                · simpa using mul_le_mul_of_nonneg_left hA (norm_nonneg (A ^ r - B ^ r))
                · simpa using mul_le_mul_of_nonneg_right hBpow (norm_nonneg (A - B))
        _ ≤ (r : ℝ) * ‖A - B‖ + ‖A - B‖ := by linarith [ih]
        _ = ((r + 1 : ℕ) : ℝ) * ‖A - B‖ := by
                rw [Nat.cast_succ]
                ring

/-- `exp (t • x) = exp ((t / (r : ℝ)) • x) ^ r` for `r > 0`. -/
lemma exp_smul_eq_pow_of_div {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    [NormedSpace ℝ 𝔸] (x : 𝔸) (t : ℝ) {r : ℕ} (hr : 0 < r) :
    exp (t • x) = exp ((t / (r : ℝ)) • x) ^ r := by
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hsmul : t • x = r • ((t / (r : ℝ)) • x) := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℝ) r ((t / (r : ℝ)) • x), smul_smul,
      mul_div_cancel₀ t hr']
  rw [hsmul]
  exact NormedSpace.exp_nsmul r ((t / (r : ℝ)) • x)

/-- In the anti-Hermitian case, every factor of `P.eval H s` is unitary, so `‖P.eval H s‖ ≤ 1`. -/
lemma norm_eval_le_one_of_skew (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ)) (s : ℝ) :
    ‖P.eval H s‖ ≤ 1 := by
  calc
    ‖P.eval H s‖
        ≤ (P.evalIndexList.map (fun i => ‖P.evalFactor H i s‖)).prod := by
            simpa [ProductFormulaData.eval, List.map_map, Function.comp_def] using
              List.norm_prod_le (P.evalIndexList.map (fun i => P.evalFactor H i s))
    _ = 1 := by
        have hfac : ∀ i : Fin P.Υ × Fin P.Γ, ‖P.evalFactor H i s‖ = 1 := by
          rintro ⟨υ, γ⟩
          have hA_skew : star (P.generator H (υ, γ)) = -(P.generator H (υ, γ)) :=
            star_smul_of_skew (h_skew (P.perm υ γ))
          rw [ProductFormulaData.evalFactor]
          exact norm_exp_smul_of_skewAdjoint hA_skew s
        exact List.prod_eq_one (by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨i, hi, hxi⟩ := hx
          rw [← hxi]
          exact hfac i)

/-- The real identity `r · (a / r)^(p+1) = a^(p+1) · (r^p)⁻¹`, for `r ≠ 0`. -/
lemma natCast_mul_pow_div_pow_succ (a : ℝ) (r p : ℕ) (hr : (r : ℝ) ≠ 0) :
    (r : ℝ) * (a / (r : ℝ)) ^ (p + 1) = a ^ (p + 1) * ((r : ℝ) ^ p)⁻¹ := by
  rw [div_pow]
  field_simp [hr, pow_ne_zero p hr]
  ring

/-- `cor:trotter_number_one_norm_scaling`: for anti-Hermitian summands, the `r`-step
Trotter error decays as `O(r^{-p})` as `r → ∞`; equivalently, `r = O(ε^{-1/p})` steps
suffice for accuracy `ε`. -/
theorem trotter_number_one_norm_scaling (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸]
    [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) (h_skew : ∀ γ : Fin P.Γ, star (H γ) = -(H γ))
    (h_order : P.IsOrderOf p H) (t : ℝ) (ht : 0 ≤ t) :
    (fun r : ℕ => ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ : Fin P.Γ, H γ)‖) =O[Filter.atTop]
      (fun r : ℕ => ((r : ℝ) ^ p)⁻¹) := by
  let S : 𝔸 := ∑ γ : Fin P.Γ, H γ
  let Snorm : ℝ := ∑ γ : Fin P.Γ, ‖H γ‖
  have hS_skew : star S = -S := sum_skewAdjoint H h_skew
  have hSnorm : 0 ≤ Snorm := Finset.sum_nonneg (fun γ _ => norm_nonneg _)
  have hO : (fun s : ℝ => ‖P.eval H s - exp (s • S)‖) =O[𝓝 (0 : ℝ)]
      (fun s : ℝ => (Snorm * s) ^ (p + 1)) := by
    simpa [S, Snorm] using trotter_error_one_norm_scaling_of_skew_adjoint P H p h_skew h_order
  have htend : Filter.Tendsto (fun r : ℕ => t / (r : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hO' : (fun r : ℕ => ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)‖) =O[Filter.atTop]
      (fun r : ℕ => (Snorm * (t / (r : ℝ))) ^ (p + 1)) :=
    hO.comp_tendsto htend
  obtain ⟨C, hC⟩ := hO'.bound
  refine IsBigO.of_bound (C * (Snorm * t) ^ (p + 1)) ?_
  filter_upwards [hC, (Filter.eventually_ge_atTop 1)] with r hr_le hr1
  have hrpos_nat : 0 < r := Nat.lt_of_lt_of_le zero_lt_one hr1
  have hrpos : 0 < (r : ℝ) := mod_cast hrpos_nat
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hr_nonneg : 0 ≤ (r : ℝ) := le_of_lt hrpos
  have hA_le : ‖P.eval H (t / (r : ℝ))‖ ≤ 1 :=
    norm_eval_le_one_of_skew P H h_skew (t / (r : ℝ))
  have hB_le : ‖exp ((t / (r : ℝ)) • S)‖ ≤ 1 :=
    le_of_eq (norm_exp_smul_of_skewAdjoint hS_skew (t / (r : ℝ)))
  have hnonneg_arg : 0 ≤ Snorm * (t / (r : ℝ)) :=
    mul_nonneg hSnorm (div_nonneg ht hr_nonneg)
  have hr_le' : ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)‖ ≤
      C * ‖(Snorm * (t / (r : ℝ))) ^ (p + 1)‖ := by
    rwa [← Real.norm_of_nonneg (norm_nonneg (P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)))]
  rw [Real.norm_of_nonneg (norm_nonneg ((P.eval H (t / (r : ℝ))) ^ r - exp (t • S)))]
  calc
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • S)‖
        = ‖(P.eval H (t / (r : ℝ))) ^ r - exp ((t / (r : ℝ)) • S) ^ r‖ := by
            rw [exp_smul_eq_pow_of_div S t hrpos_nat]
    _ ≤ (r : ℝ) * ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • S)‖ :=
            norm_pow_sub_pow_le_of_norm_le_one (P.eval H (t / (r : ℝ)))
              (exp ((t / (r : ℝ)) • S)) r hA_le hB_le
    _ ≤ (r : ℝ) * (C * ‖(Snorm * (t / (r : ℝ))) ^ (p + 1)‖) :=
            mul_le_mul_of_nonneg_left hr_le' hr_nonneg
    _ = C * (Snorm * t) ^ (p + 1) * ‖((r : ℝ) ^ p)⁻¹‖ := by
            rw [Real.norm_of_nonneg (pow_nonneg hnonneg_arg (p + 1)),
              Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hr_nonneg p))]
            calc
              (r : ℝ) * (C * (Snorm * (t / (r : ℝ))) ^ (p + 1))
                  = C * ((r : ℝ) * ((Snorm * t) / (r : ℝ)) ^ (p + 1)) := by
                      rw [show Snorm * (t / (r : ℝ)) = (Snorm * t) / (r : ℝ) by
                        field_simp [hr_ne]]
                      ring
              _ = C * (Snorm * t) ^ (p + 1) * ((r : ℝ) ^ p)⁻¹ := by
                      rw [natCast_mul_pow_div_pow_succ (Snorm * t) r p hr_ne]
                      ring

end TrotterError
