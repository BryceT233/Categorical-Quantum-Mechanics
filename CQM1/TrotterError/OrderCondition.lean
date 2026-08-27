/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.Calculus
public import CQM1.TrotterError.TimeOrderedExp

/-!
# Order conditions for Trotter error

The order-condition calculus of arXiv:1912.08854, `prop:order_cond_rule` (order.tex:76-86).
An operator-valued function `F` satisfies `F = O(τ^p)` (the italic `O`, limit `τ → 0`) when
`(fun τ => ‖F τ‖) =O[𝓝 (0:ℝ)] (fun τ => τ^p)`; the `IsBigO` relation norm-wraps its right-hand
side, so `τ^p` acts as `|τ|^p`.

## Main results

* `orderCond_add`, `orderCond_mul`: the addition and multiplication rules.
* `orderCond_deriv_iff`: `F = O(τ^{p+1})` iff `F 0 = 0` and `F' = O(τ^p)`.
* `orderCond_integral_iff`: `F = O(τ^p)` iff `∫₀ᵗ F = O(t^{p+1})`.
* `orderCond_exp_iff`: `F = G + O(τ^p)` iff `exp_T(∫₀ᵗ F) = exp_T(∫₀ᵗ G) + O(t^{p+1})`.
* `monomial_integral_order`: the canonical nested integral of a monomial is `O(t^{Σp + Γ})`
  (`lem:monomial`).

All rules are stated for smooth generators (the paper's standing hypothesis "infinitely
differentiable", order.tex:78).

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open Asymptotics
open scoped Topology ContDiff

/-! ### Auxiliary order estimates -/

/-- For `|τ| ≤ 1` in a neighborhood of `0`, the function `|τ|^n` is bounded by `|τ|^m` whenever
`m ≤ n`. -/
lemma eventually_abs_le_one_nhds_zero : ∀ᶠ τ in 𝓝 (0 : ℝ), |τ| ≤ 1 := by
  refine Filter.mem_of_superset
    (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ))) ?_
  intro τ hτ
  simpa [Metric.closedBall, dist_eq_norm, sub_zero] using hτ

/-- For `m ≤ n`, `|τ|^n = O(|τ|^m)` as `τ → 0`. -/
lemma isBigO_abs_pow_abs_pow_of_le {m n : ℕ} (hmn : m ≤ n) :
    (fun τ : ℝ => |τ| ^ n) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => |τ| ^ m) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_abs_le_one_nhds_zero] with τ hτ
  have hnn : 0 ≤ |τ| := abs_nonneg τ
  rw [Real.norm_of_nonneg (pow_nonneg hnn n), Real.norm_of_nonneg (pow_nonneg hnn m), one_mul]
  exact pow_le_pow_of_le_one hnn hτ hmn

/-- `lem:order_cond_deriv` in the `O(τ^p)` form: a smooth `F` satisfies `F = O(τ^p)` iff all its
iterated derivatives of order `< p` vanish at `0`. For `p = 0` both sides hold automatically. -/
lemma isBigO_norm_iff_iteratedDeriv_lt_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      ∀ j : ℕ, j < p → iteratedDeriv j F 0 = 0 := by
  by_cases hp : p = 0
  · subst p
    constructor
    · intro _ j hj
      exact (Nat.not_lt_zero j hj).elim
    · intro _
      exact (hF.continuous.norm.continuousAt).isBigO_one (F := ℝ)
  · have hsub : (p - 1) + 1 = p := Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hp))
    constructor
    · intro hbig
      have hmain : ∀ j ≤ p - 1, iteratedDeriv j F 0 = 0 :=
        (isBigO_norm_iff_iteratedDeriv_eq_zero F (p - 1) hF).mp (by
          simpa [hsub] using hbig)
      intro j hj
      exact hmain j (Nat.lt_succ_iff.mp (by simpa [hsub] using hj))
    · intro h
      simpa [hsub] using
        (isBigO_norm_iff_iteratedDeriv_eq_zero F (p - 1) hF).mpr (fun j hj =>
          h j (by simpa [hsub] using (Nat.lt_succ_iff.mpr hj)))

/-! ### Addition and multiplication -/

/-- Addition rule (order.tex:80): `F = O(τ^p)` and `G = O(τ^q)` imply `F + G = O(τ^{min p q})`. -/
theorem orderCond_add {𝔸 : Type*} [NormedRing 𝔸] (F G : ℝ → 𝔸) (p q : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) :
    (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ min p q) := by
  have htri : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => ‖F τ‖ + ‖G τ‖) := by
    refine Filter.Eventually.isBigO ?_
    filter_upwards with τ
    simpa [Real.norm_eq_abs] using (norm_add_le (F τ) (G τ))
  have hsum : (fun τ => ‖F τ‖ + ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ p + |τ| ^ q) := by
    simpa [Real.norm_eq_abs, norm_pow] using hF.add_add hG
  have hlast : (fun τ => |τ| ^ p + |τ| ^ q) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) := by
    have hp : (fun τ => |τ| ^ p) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
      isBigO_abs_pow_abs_pow_of_le (Nat.min_le_left p q)
    have hq : (fun τ => |τ| ^ q) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
      isBigO_abs_pow_abs_pow_of_le (Nat.min_le_right p q)
    exact hp.add hq
  have hbig : (fun τ => ‖F τ‖ + ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
    hsum.trans hlast
  have hres : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
    htri.trans hbig
  have hres' : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => ‖τ ^ min p q‖) := by
    simpa [Real.norm_eq_abs, norm_pow] using hres
  exact isBigO_norm_right.mp hres'

/-- Multiplication rule (order.tex:81): `F = O(τ^p)` and `G = O(τ^q)` imply
`F * G = O(τ^{p+q})`. -/
theorem orderCond_mul {𝔸 : Type*} [NormedRing 𝔸] (F G : ℝ → 𝔸) (p q : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) :
    (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + q)) := by
  have htri : (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => ‖F τ‖ * ‖G τ‖) := by
    refine Filter.Eventually.isBigO ?_
    filter_upwards with τ
    simpa [Real.norm_eq_abs] using (norm_mul_le (F τ) (G τ))
  have hbig : (fun τ => ‖F τ‖ * ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + q)) :=
    (hF.mul hG).congr_right (fun τ => (pow_add τ p q).symm)
  exact htri.trans hbig

/-! ### Differentiation -/

/-- Differentiation rule (order.tex:82): `F = O(τ^{p+1})` iff `F 0 = 0` and `F' = O(τ^p)`. -/
theorem orderCond_deriv_iff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (F : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + 1)) ↔
      F 0 = 0 ∧ (fun τ => ‖deriv F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  have hFderiv : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  constructor
  · intro hbig
    have hvan : ∀ j ≤ p, iteratedDeriv j F 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_eq_zero F p hF).mp hbig
    refine ⟨?_, ?_⟩
    · simpa using hvan 0 (Nat.zero_le p)
    · exact (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (deriv F) p hFderiv).mpr
        (fun j hj => by
          simpa [iteratedDeriv_succ'] using hvan (j + 1) (Nat.succ_le_iff.mpr hj))
  · rintro ⟨hF0, hderiv_big⟩
    have hderiv_van : ∀ j < p, iteratedDeriv j (deriv F) 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (deriv F) p hFderiv).mp hderiv_big
    exact (isBigO_norm_iff_iteratedDeriv_eq_zero F p hF).mpr (fun j hj => by
      cases j with
      | zero => simpa using hF0
      | succ k => simpa [iteratedDeriv_succ'] using hderiv_van k (by lia))

/-! ### Integration -/

/-- For smooth `F`, the function `t ↦ ∫₀ᵗ F` is smooth. -/
lemma contDiff_integral_of_contDiff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (F : ℝ → 𝔸) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun t => ∫ τ in 0..t, F τ) := by
  let IF : ℝ → 𝔸 := fun t => ∫ τ in 0..t, F τ
  have hcont : Continuous F := hF.continuous
  have hHasDeriv : ∀ t, HasDerivAt IF (F t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hderiv : deriv IF = F := by
    funext t
    exact (hHasDeriv t).deriv
  have hdiff : Differentiable ℝ IF := fun t => (hHasDeriv t).differentiableAt
  exact (contDiff_infty_iff_deriv (f := IF)).mpr ⟨hdiff, by simpa [hderiv] using hF⟩

/-- Integration rule (order.tex:83): `F = O(τ^p)` iff `∫₀ᵗ F = O(t^{p+1})`. -/
theorem orderCond_integral_iff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (F : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      (fun t => ‖∫ τ in 0..t, F τ‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1)) := by
  let IF : ℝ → 𝔸 := fun t => ∫ τ in 0..t, F τ
  have hIF : ContDiff ℝ ∞ IF := contDiff_integral_of_contDiff F hF
  have hderiv : deriv IF = F := by
    funext t
    exact intervalIntegral.deriv_integral_right (hF.continuous.intervalIntegrable 0 t)
      hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuous.continuousAt
  have hiter : ∀ j, iteratedDeriv (j + 1) IF 0 = iteratedDeriv j F 0 := by
    intro j
    rw [iteratedDeriv_succ', hderiv]
  constructor
  · intro hFbig
    have hvan : ∀ j < p, iteratedDeriv j F 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_lt_eq_zero F p hF).mp hFbig
    exact (isBigO_norm_iff_iteratedDeriv_eq_zero IF p hIF).mpr (fun j hj => by
      cases j with
      | zero => simp [IF]
      | succ k =>
          have hk : k < p := Nat.lt_of_succ_le hj
          rw [hiter k]
          exact hvan k hk)
  · intro hIFbig
    have hvan : ∀ j ≤ p, iteratedDeriv j IF 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_eq_zero IF p hIF).mp hIFbig
    exact (isBigO_norm_iff_iteratedDeriv_lt_eq_zero F p hF).mpr (fun j hj => by
      have hle : j + 1 ≤ p := Nat.succ_le_iff.mpr hj
      simpa [hiter j] using hvan (j + 1) hle)

/-! ### Exponentiation -/

/-- For smooth `H`, the solution `t ↦ exp_T(∫₀ᵗ H)` is smooth. -/
lemma contDiff_timeOrderedExp_of_contDiff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (H : ℝ → 𝔸) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun t => timeOrderedExp H 0 t) := by
  let U : ℝ → 𝔸 := fun t => timeOrderedExp H 0 t
  have hcont : Continuous H := hH.continuous
  have hHasDeriv : ∀ t, HasDerivAt U (H t * U t) t := fun t =>
    timeOrderedExp_hasDerivAt H hcont 0 t
  have hU : ∀ n : ℕ, ContDiff ℝ n U := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr (continuous_timeOrderedExp H hcont 0)
    | succ n ih =>
        have hHn : ContDiff ℝ n H := hH.of_le (mod_cast le_top)
        have hfn : ContDiff ℝ n (fun t => H t * U t) := hHn.mul ih
        have hspan : ContDiff ℝ n
            (fun t => (ContinuousLinearMap.toSpanSingletonCLE : 𝔸 ≃L[ℝ] (ℝ →L[ℝ] 𝔸))
              (H t * U t)) :=
          (ContinuousLinearMap.toSpanSingletonCLE : 𝔸 ≃L[ℝ] (ℝ →L[ℝ] 𝔸)).contDiff.comp hfn
        exact (contDiff_succ_iff_hasFDerivAt (f := U) (n := n)).mpr
          ⟨fun t => (ContinuousLinearMap.toSpanSingletonCLE : 𝔸 ≃L[ℝ] (ℝ →L[ℝ] 𝔸)) (H t * U t),
            hspan, fun t => (hHasDeriv t).hasFDerivAt⟩
  rwa [contDiff_infty]

/-- The recurrence for iterated derivatives of `t ↦ exp_T(∫₀ᵗ H)` at `0`: the `(j+1)`-st
iterated derivative is `iteratedDeriv j H 0` plus terms built from strictly lower derivatives of
`H` and lower iterated derivatives of the time-ordered exponential. -/
lemma iteratedDeriv_timeOrderedExp_succ {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (H : ℝ → 𝔸) (hH : ContDiff ℝ ∞ H) (j : ℕ) :
    iteratedDeriv (j + 1) (fun t => timeOrderedExp H 0 t) 0 =
      (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 *
        iteratedDeriv (j - i) (fun t => timeOrderedExp H 0 t) 0) + iteratedDeriv j H 0 := by
  let U : ℝ → 𝔸 := fun t => timeOrderedExp H 0 t
  have hU : ContDiff ℝ ∞ U := contDiff_timeOrderedExp_of_contDiff H hH
  have hderiv : deriv U = fun t => H t * U t := by
    funext t
    exact (timeOrderedExp_hasDerivAt H hH.continuous 0 t).deriv
  calc
    iteratedDeriv (j + 1) U 0
        = iteratedDeriv j (deriv U) 0 := by rw [iteratedDeriv_succ']
    _ = iteratedDeriv j (fun t => H t * U t) 0 := by rw [hderiv]
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : 𝔸) * iteratedDeriv i H 0 *
          iteratedDeriv (j - i) U 0 := by
            change iteratedDeriv j (H * U) 0 =
              ∑ i ∈ Finset.range (j + 1), (j.choose i : 𝔸) * iteratedDeriv i H 0 *
                iteratedDeriv (j - i) U 0
            rw [iteratedDeriv_mul (hH.contDiffAt.of_le (mod_cast le_top))
              (hU.contDiffAt.of_le (mod_cast le_top))]
    _ = (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 *
          iteratedDeriv (j - i) U 0) + (j.choose j : 𝔸) * iteratedDeriv j H 0 *
          iteratedDeriv 0 U 0 := by
            rw [Finset.sum_range_succ, Nat.sub_self]
    _ = (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 *
          iteratedDeriv (j - i) U 0) + iteratedDeriv j H 0 := by
            rw [Nat.choose_self]
            simp [U, timeOrderedExp_initial]

/-- The derivative-comparison heart of the exponentiation rule: the generators agree to order
`p - 1` (all iterated derivatives of order `< p` coincide at `0`) iff the associated time-ordered
exponentials agree to order `p` (all iterated derivatives of order `≤ p` coincide at `0`). -/
lemma timeOrderedExp_iteratedDeriv_eq_iff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (F G : ℝ → 𝔸) (p : ℕ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (∀ j, j < p → iteratedDeriv j F 0 = iteratedDeriv j G 0) ↔
      (∀ j, j ≤ p → iteratedDeriv j (fun t => timeOrderedExp F 0 t) 0 =
        iteratedDeriv j (fun t => timeOrderedExp G 0 t) 0) := by
  by_cases hp : p = 0
  · subst p
    constructor
    · intro _ j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simp [timeOrderedExp_initial]
    · intro _ j hj
      exact (Nat.not_lt_zero j hj).elim
  · constructor
    · intro hD j hj
      induction j using Nat.strong_induction_on with
      | h j ih =>
        cases j with
        | zero => simp [timeOrderedExp_initial]
        | succ k =>
            have hk : k < p := Nat.lt_of_succ_le hj
            rw [iteratedDeriv_timeOrderedExp_succ F hF k,
              iteratedDeriv_timeOrderedExp_succ G hG k]
            apply congrArg₂ (fun x y => x + y)
            · apply Finset.sum_congr rfl
              intro i hi
              have hi_lt : i < k := Finset.mem_range.mp hi
              have hDF : iteratedDeriv i F 0 = iteratedDeriv i G 0 :=
                hD i (Nat.lt_trans hi_lt hk)
              have hDU : iteratedDeriv (k - i) (fun t => timeOrderedExp F 0 t) 0 =
                  iteratedDeriv (k - i) (fun t => timeOrderedExp G 0 t) 0 :=
                ih (k - i) (Nat.lt_of_le_of_lt (Nat.sub_le k i) (Nat.lt_succ_self k))
                  (Nat.le_trans (Nat.sub_le k i) (Nat.le_of_lt hk))
              rw [hDF, hDU]
            · exact hD k hk
    · intro hDU j hj
      induction j using Nat.strong_induction_on with
      | h j ih =>
        cases j with
        | zero =>
            have h1 : iteratedDeriv 1 (fun t => timeOrderedExp F 0 t) 0 =
                iteratedDeriv 1 (fun t => timeOrderedExp G 0 t) 0 :=
              hDU 1 (Nat.succ_le_iff.mpr hj)
            have hF1 : iteratedDeriv 1 (fun t => timeOrderedExp F 0 t) 0 = iteratedDeriv 0 F 0 := by
              simpa using iteratedDeriv_timeOrderedExp_succ F hF 0
            have hG1 : iteratedDeriv 1 (fun t => timeOrderedExp G 0 t) 0 = iteratedDeriv 0 G 0 := by
              simpa using iteratedDeriv_timeOrderedExp_succ G hG 0
            rwa [hF1, hG1] at h1
        | succ k =>
            have hfull : iteratedDeriv (k + 2) (fun t => timeOrderedExp F 0 t) 0 =
                iteratedDeriv (k + 2) (fun t => timeOrderedExp G 0 t) 0 := hDU (k + 2) (by lia)
            rw [iteratedDeriv_timeOrderedExp_succ F hF (k + 1),
              iteratedDeriv_timeOrderedExp_succ G hG (k + 1)] at hfull
            have hsum : (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i F 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp F 0 t) 0) =
                ∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i G 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi_le : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              have hDF : iteratedDeriv i F 0 = iteratedDeriv i G 0 :=
                ih i (Nat.lt_of_le_of_lt hi_le (Nat.lt_succ_self k))
                  (Nat.lt_of_le_of_lt hi_le (Nat.lt_of_succ_lt hj))
              have hDUi : iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp F 0 t) 0 =
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0 :=
                hDU (k + 1 - i) (Nat.le_trans (Nat.sub_le (k + 1) i) (Nat.le_of_lt hj))
              rw [hDF, hDUi]
            have hfull' : (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i G 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0) +
                    iteratedDeriv (k + 1) F 0 =
                (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i G 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0) +
                    iteratedDeriv (k + 1) G 0 := by
              simpa [hsum] using hfull
            exact add_left_cancel hfull'

/-- Exponentiation rule (order.tex:84): `F = G + O(τ^p)` iff
`exp_T(∫₀ᵗ F) = exp_T(∫₀ᵗ G) + O(t^{p+1})`. -/
theorem orderCond_exp_iff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (F G : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (fun τ => ‖F τ - G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      (fun t => ‖timeOrderedExp F 0 t - timeOrderedExp G 0 t‖) =O[𝓝 (0 : ℝ)]
        (fun t => t ^ (p + 1)) := by
  let UF : ℝ → 𝔸 := fun t => timeOrderedExp F 0 t
  let UG : ℝ → 𝔸 := fun t => timeOrderedExp G 0 t
  have hUF : ContDiff ℝ ∞ UF := contDiff_timeOrderedExp_of_contDiff F hF
  have hUG : ContDiff ℝ ∞ UG := contDiff_timeOrderedExp_of_contDiff G hG
  have hdiff : ContDiff ℝ ∞ (UF - UG) := hUF.sub hUG
  have hcore := timeOrderedExp_iteratedDeriv_eq_iff F G p hF hG
  constructor
  · intro hbig
    have hD : ∀ j < p, iteratedDeriv j F 0 = iteratedDeriv j G 0 := by
      intro j hj
      have hzero : iteratedDeriv j (F - G) 0 = 0 :=
        (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (F - G) p (hF.sub hG)).mp hbig j hj
      rw [iteratedDeriv_sub (hF.contDiffAt.of_le (mod_cast le_top))
        (hG.contDiffAt.of_le (mod_cast le_top))] at hzero
      exact sub_eq_zero.mp hzero
    have hDU : ∀ j ≤ p, iteratedDeriv j UF 0 = iteratedDeriv j UG 0 := hcore.mp hD
    exact (isBigO_norm_iff_iteratedDeriv_eq_zero (UF - UG) p hdiff).mpr (fun j hj => by
      have heq : iteratedDeriv j UF 0 = iteratedDeriv j UG 0 := hDU j hj
      rw [iteratedDeriv_sub (hUF.contDiffAt.of_le (mod_cast le_top))
        (hUG.contDiffAt.of_le (mod_cast le_top))]
      exact sub_eq_zero.mpr heq)
  · intro hbig
    have hDU : ∀ j ≤ p, iteratedDeriv j UF 0 = iteratedDeriv j UG 0 := by
      intro j hj
      have hzero : iteratedDeriv j (UF - UG) 0 = 0 :=
        (isBigO_norm_iff_iteratedDeriv_eq_zero (UF - UG) p hdiff).mp hbig j hj
      rw [iteratedDeriv_sub (hUF.contDiffAt.of_le (mod_cast le_top))
        (hUG.contDiffAt.of_le (mod_cast le_top))] at hzero
      exact sub_eq_zero.mp hzero
    have hD : ∀ j < p, iteratedDeriv j F 0 = iteratedDeriv j G 0 := hcore.mpr hDU
    exact (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (F - G) p (hF.sub hG)).mpr (fun j hj => by
      rw [iteratedDeriv_sub (hF.contDiffAt.of_le (mod_cast le_top))
        (hG.contDiffAt.of_le (mod_cast le_top))]
      exact sub_eq_zero.mpr (hD j hj))

/-! ### Integration of a monomial -/

/-- The canonical nested iterated integral of a monomial: `Γ` nested integrals, the `(i+1)`-st
integration variable carrying the power `p i`, each integral running from `0` to the immediately
preceding variable (the outermost from `0` to `t`). This is the sequential specialization of the
paper's `lem:monomial`; the general form (each inner upper limit an arbitrary earlier variable)
has the same order `t^{Σp + Γ}` by the same induction. -/
noncomputable def iteratedIntegralMonomial (Γ : ℕ) (p : Fin Γ → ℕ) : ℝ → ℝ :=
  match Γ with
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ τ in 0..t, τ ^ p 0 * iteratedIntegralMonomial n (Fin.tail p) τ

/-- The scalar constant in the closed form of `iteratedIntegralMonomial`: the nested integral of
the monomial equals `monomialConstant Γ p * t ^ ((∑ i, p i) + Γ)`. -/
noncomputable def monomialConstant (Γ : ℕ) (p : Fin Γ → ℕ) : ℝ :=
  match Γ with
  | 0 => 1
  | n + 1 => monomialConstant n (Fin.tail p) / (((∑ i : Fin (n + 1), p i) + (n + 1)) : ℝ)

/-- Closed form of the canonical nested monomial integral. -/
lemma iteratedIntegralMonomial_eq (Γ : ℕ) (p : Fin Γ → ℕ) (t : ℝ) :
    iteratedIntegralMonomial Γ p t = monomialConstant Γ p * t ^ ((∑ i : Fin Γ, p i) + Γ) := by
  induction Γ generalizing t with
  | zero => simp [iteratedIntegralMonomial, monomialConstant]
  | succ n ih =>
      change (∫ τ in 0..t, τ ^ p 0 * iteratedIntegralMonomial n (Fin.tail p) τ) =
        monomialConstant n (Fin.tail p) / (((∑ i : Fin (n + 1), p i) + (n + 1)) : ℝ) *
          t ^ ((∑ i : Fin (n + 1), p i) + (n + 1))
      simp_rw [ih (Fin.tail p)]
      have hsum : (∑ i : Fin (n + 1), p i) = p 0 + ∑ i : Fin n, Fin.tail p i := by
        rw [Fin.sum_univ_succ]
        rfl
      calc
        (∫ τ in 0..t, τ ^ p 0 * (monomialConstant n (Fin.tail p) *
              τ ^ ((∑ i : Fin n, Fin.tail p i) + n)))
            = ∫ τ in 0..t, monomialConstant n (Fin.tail p) *
                τ ^ ((∑ i : Fin (n + 1), p i) + n) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ
                change τ ^ p 0 * (monomialConstant n (Fin.tail p) *
                    τ ^ ((∑ i : Fin n, Fin.tail p i) + n)) =
                  monomialConstant n (Fin.tail p) * τ ^ ((∑ i : Fin (n + 1), p i) + n)
                rw [hsum]; ring
        _ = monomialConstant n (Fin.tail p) *
              ∫ τ in 0..t, τ ^ ((∑ i : Fin (n + 1), p i) + n) := by
                rw [intervalIntegral.integral_const_mul]
        _ = monomialConstant n (Fin.tail p) * (t ^ (((∑ i : Fin (n + 1), p i) + n) + 1) /
              ((((∑ i : Fin (n + 1), p i) + n) + 1 : ℕ) : ℝ)) := by simp
        _ = (monomialConstant n (Fin.tail p) / (((∑ i : Fin (n + 1), p i) + (n + 1)) : ℝ)) *
              t ^ ((∑ i : Fin (n + 1), p i) + (n + 1)) := by
                rw [Nat.add_assoc]; ring_nf; norm_num

/-- `lem:monomial`: the canonical nested iterated integral of a monomial is `O(t^{Σp + Γ})`. -/
theorem monomial_integral_order (Γ : ℕ) (p : Fin Γ → ℕ) :
    (fun t : ℝ => iteratedIntegralMonomial Γ p t) =O[𝓝 (0 : ℝ)]
      (fun t => t ^ ((∑ i : Fin Γ, p i) + Γ)) := by
  have h : (fun t : ℝ => iteratedIntegralMonomial Γ p t) =
      fun t => monomialConstant Γ p * t ^ ((∑ i : Fin Γ, p i) + Γ) := by
    funext t
    exact iteratedIntegralMonomial_eq Γ p t
  exact h ▸ isBigO_const_mul_self (monomialConstant Γ p)
    (fun t => t ^ ((∑ i : Fin Γ, p i) + Γ)) (𝓝 (0 : ℝ))

end TrotterError
