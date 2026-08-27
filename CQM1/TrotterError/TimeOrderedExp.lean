/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Time-ordered exponential

The time-ordered exponential `exp_T(∫ H dτ)` of arXiv:1912.08854 §2.2, defined via the Dyson
(Neumann/Picard) series `∑' n, D_n` with `D₀ = 1` and `D_{n+1}(t) = ∫ τ in t₁..t, H τ * D_n τ`.
The interval integral carries the orientation, so the definition is automatically two-sided.

## Main results

* `timeOrderedExp_initial`: `exp_T H t₁ t₁ = 1`.
* `timeOrderedExp_hasDerivAt`, `timeOrderedExp_hasDerivAt_lower`: the two differentiation rules
  `∂/∂t₂ exp_T = H·exp_T` and `∂/∂t₁ exp_T = -exp_T·H` (`prelim.tex:44-49`).
* `timeOrderedExp_mul`: the multiplicative property
  `exp_T H t₁ t₃ = exp_T H t₂ t₃ · exp_T H t₁ t₂` (`prelim.tex:52`).
* `timeOrderedExp_mul_inv_self`, `timeOrderedExp_inv_mul_self`, `isUnit_timeOrderedExp`:
  every `exp_T H t₁ t₂` is a unit with inverse `exp_T H t₂ t₁`.
* `timeOrderedExp_eq_integral`: the integral equation `U = 1 + ∫ H·U` (`eq:int_eq`).
* `timeOrderedExp_duhamel`: the variation-of-parameters formula (`lem:td_Duhamel`).
* `timeOrderedExp_interaction_picture`: time-ordered evolution in the interaction picture
  (`lem:interaction_picture`).
* `fundamentalTheorem_timeOrderedExp`, `fundamentalTheorem_timeOrderedExp_unique`: the
  fundamental theorem of time-ordered evolution and the uniqueness of its generator (`lem:fte`).
* `timeOrderedExp_const`: `exp_T (fun _ => H) t₁ t₂ = exp ((t₂ - t₁) • H)` (`prelim.tex:41`).
* `timeOrderedExp_norm_le`, `timeOrderedExp_norm_eq_one_of_skewAdjoint`:
  `‖exp_T H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖|`, and `= 1` when `H` is skew-adjoint
  (`lem:time_ordered_norm_bound`).
* `timeOrderedExp_dist_le`, `timeOrderedExp_dist_le_of_skewAdjoint`: distance bounds between
  two evolutions (`cor:time_ordered_distance_bound`).
* `ode_solution_unique`: uniqueness of solutions to `U' = H·U`.
* `continuous_timeOrderedExp`, `continuous_timeOrderedExp_lower`, `contDiff_timeOrderedExp`:
  continuity/smoothness of the solution in its upper and lower limits.
* `timeOrderedExp_sub`: the difference identity between two evolutions
  (`cor:time_ordered_distance_bound`).

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace
open scoped Topology BigOperators Interval

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### The Dyson series -/

/-- The `n`-th term of the Dyson (Neumann/Picard) series for the time-ordered exponential:
`D₀ = 1` and `D_{n+1}(t) = ∫ τ in t₁..t, H τ * D_n τ`. The interval integral is oriented,
so this is defined for every `t : ℝ` (not only `t ≥ t₁`). -/
noncomputable def dysonTerm (H : ℝ → 𝔸) (t₁ : ℝ) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ τ in t₁..t, H τ * dysonTerm H t₁ n τ

/-- The time-ordered exponential `exp_T(∫_{t₁}^{t₂} H(τ) dτ)`, defined for a continuous
generator `H` as the sum of the Dyson series. For `t₁ ≤ t₂` this is the unique solution of
`U' = H·U`, `U(t₁) = 1`; for `t₂ < t₁` it is the inverse evolution (a theorem, not
built into the definition). -/
noncomputable def timeOrderedExp (H : ℝ → 𝔸) (t₁ t₂ : ℝ) : 𝔸 :=
  ∑' n : ℕ, dysonTerm H t₁ n t₂

/-! ### Continuity of the Dyson terms -/

/-- Each Dyson term `D_n` is continuous (as a function of `t`) when `H` is continuous. -/
lemma continuous_dysonTerm (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) (n : ℕ) :
    Continuous (dysonTerm H t₁ n) := by
  induction n with
  | zero => simpa [dysonTerm] using continuous_const
  | succ n ih =>
      have hg : Continuous fun τ : ℝ => H τ * dysonTerm H t₁ n τ := hH.mul ih
      rw [dysonTerm]
      exact (intervalIntegral.differentiable_integral_of_continuous hg).continuous

/-! ### The fundamental-theorem identity behind the norm bound -/

/-- For continuous `f`, the iterated-integral identity
`∫ τ in a..b, f τ * (∫ u in a..τ, f u)^n / n! = (∫ u in a..b, f u)^(n+1) / (n+1)!`
(valid for all `a b`, with the interval integral carrying the orientation).
This is the FTC applied to `t ↦ (∫_a^t f)^(n+1)/(n+1)!` and is the key step in bounding the
Dyson terms by `(∫ ‖H‖)^n/n!`. -/
lemma integral_mul_integral_pow_div_factorial (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n) =
      (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1) := by
  let F : ℝ → ℝ := fun t => ∫ u in a..t, f u
  let G : ℝ → ℝ := fun t => F t ^ (n + 1) / Nat.factorial (n + 1)
  have hFderiv : ∀ t : ℝ, HasDerivAt F (f t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hGderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt G (f t * F t ^ n / Nat.factorial n) t := by
    intro t _
    have hdiff : DifferentiableAt ℝ G t := ((hFderiv t).differentiableAt.pow (n + 1)).div_const
      (Nat.factorial (n + 1) : ℝ)
    have hderiv : deriv G t = f t * F t ^ n / Nat.factorial n := by
      dsimp [G]
      rw [deriv_div_const]
      change deriv (F ^ (n + 1)) t / (Nat.factorial (n + 1) : ℝ) = _
      rw [deriv_pow (hFderiv t).differentiableAt (n + 1), (hFderiv t).deriv, Nat.add_one_sub_one,
        Nat.factorial_succ, Nat.cast_mul]
      field_simp
    simpa [hderiv] using hdiff.hasDerivAt
  have hFcont : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hint : IntervalIntegrable (fun τ => f τ * F τ ^ n / Nat.factorial n)
      MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun τ => f τ * F τ ^ n / Nat.factorial n).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G)
    (f' := fun τ => f τ * F τ ^ n / Nat.factorial n) hGderiv hint
  calc
    (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n)
        = ∫ τ in a..b, f τ * F τ ^ n / Nat.factorial n := rfl
    _ = G b - G a := hFTC
    _ = (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1) := by simp [G, F]

/-- For continuous nonnegative `g`, the two-sided FTC identity
`|∫ τ in a..b, g τ * |∫ u in a..τ, g u|^n / n!| = |∫ u in a..b, g u|^(n+1) / (n+1)!`.
This is the "backward" companion of `integral_mul_integral_pow_div_factorial`. -/
lemma abs_integral_mul_abs_integral_pow_div_factorial (g : ℝ → ℝ) (hg : Continuous g)
    (hgnn : ∀ τ, 0 ≤ g τ) (a b : ℝ) (n : ℕ) :
    |∫ τ in a..b, g τ * |∫ u in a..τ, g u| ^ n / Nat.factorial n| =
      |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
  let F : ℝ → ℝ := fun τ => ∫ u in a..τ, g u
  by_cases hab : a ≤ b
  · -- forward: `F τ ≥ 0` on `[a, b]`, so `|F τ| = F τ` and the integral is nonnegative.
    have hFnn_interval : ∀ τ ∈ Set.Icc a b, 0 ≤ F τ := by
      intro τ hτ
      exact intervalIntegral.integral_nonneg hτ.1 (fun u _ => hgnn u)
    have hFnn_uIoo : ∀ τ ∈ Set.uIoo a b, 0 ≤ F τ := by
      intro τ hτ
      have hmin : min a b < τ := hτ.1
      have haτ : a ≤ τ := by simpa [min_eq_left hab] using le_of_lt hmin
      exact intervalIntegral.integral_nonneg haτ (fun u _ => hgnn u)
    have heq : (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n) =
        ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
      apply intervalIntegral.integral_congr_uIoo
      intro τ hτ
      simp [abs_of_nonneg (hFnn_uIoo τ hτ)]
    have hnonneg : 0 ≤ ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n :=
      intervalIntegral.integral_nonneg hab (fun τ hτ =>
        div_nonneg (mul_nonneg (hgnn τ) (pow_nonneg (hFnn_interval τ hτ) n)) (by positivity))
    calc
      |∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n|
          = ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by rw [heq, abs_of_nonneg hnonneg]
      _ = F b ^ (n + 1) / Nat.factorial (n + 1) :=
          integral_mul_integral_pow_div_factorial g hg a b n
      _ = |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [show F b = ∫ u in a..b, g u by rfl,
            abs_of_nonneg (intervalIntegral.integral_nonneg hab (fun u _ => hgnn u))]
  · -- backward: `b ≤ a`, so `F τ ≤ 0` on `[b, a]`, `|F τ| = -F τ`.
    have hba : b ≤ a := le_of_not_ge hab
    have hFnonpos_uIoo : ∀ τ ∈ Set.uIoo a b, F τ ≤ 0 := by
      intro τ hτ
      have hmax : τ < max a b := hτ.2
      have hτa : τ ≤ a := by simpa [max_eq_left hba] using le_of_lt hmax
      calc
        F τ = ∫ u in a..τ, g u := rfl
        _ ≤ 0 := by
          have hnonneg : 0 ≤ ∫ u in τ..a, g u :=
            intervalIntegral.integral_nonneg hτa (fun u _ => hgnn u)
          rw [intervalIntegral.integral_symm]
          linarith
    have heq : (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n) =
        (-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
      calc
        (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n)
            = ∫ τ in a..b, (-1 : ℝ) ^ n * (g τ * F τ ^ n / Nat.factorial n) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ; simp only
                rw [abs_of_nonpos (hFnonpos_uIoo τ hτ), neg_pow]
                ring
        _ = (-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
                rw [intervalIntegral.integral_const_mul]
    calc
      |∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n|
          = |(-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n| := by rw [heq]
      _ = |(-1 : ℝ) ^ n * (F b ^ (n + 1) / Nat.factorial (n + 1))| := by
          rw [integral_mul_integral_pow_div_factorial g hg a b n]
      _ = |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial (n + 1) : ℝ))]

/-! ### Norm bound of the Dyson terms -/

omit [CompleteSpace 𝔸] in
/-- The `n`-th Dyson term is bounded by `‖1‖ · |∫_{t₁}^{t} ‖H‖|^n / n!` for all `t` (both
orientations), valid without `NormOneClass`. -/
lemma norm_dysonTerm_le_abs (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) (n : ℕ) (t : ℝ) :
    ‖dysonTerm H t₁ n t‖ ≤ ‖(1 : 𝔸)‖ * |∫ u in t₁..t, ‖H u‖| ^ n / Nat.factorial n := by
  induction n generalizing t with
  | zero => simp [dysonTerm]
  | succ n ih =>
      rw [dysonTerm]
      let B : ℝ → ℝ := fun τ =>
        ‖H τ‖ * (‖(1 : 𝔸)‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n)
      calc
        ‖∫ τ in t₁..t, H τ * dysonTerm H t₁ n τ‖
            ≤ |∫ τ in t₁..t, B τ| := by
                refine intervalIntegral.norm_integral_le_abs_of_norm_le
                  (f := fun τ => H τ * dysonTerm H t₁ n τ) (g := B) ?_ ?_
                · filter_upwards with τ
                  calc
                    ‖H τ * dysonTerm H t₁ n τ‖ ≤ ‖H τ‖ * ‖dysonTerm H t₁ n τ‖ := norm_mul_le _ _
                    _ ≤ B τ := mul_le_mul_of_nonneg_left (ih τ) (norm_nonneg (H τ))
                · exact (by fun_prop : Continuous B).intervalIntegrable t₁ t
        _ = ‖(1 : 𝔸)‖ * |∫ τ in t₁..t, ‖H τ‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n| := by
                rw [show (fun τ => B τ) =
                    fun τ => ‖(1 : 𝔸)‖ * (‖H τ‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n) by
                  funext τ; dsimp [B]; ring, intervalIntegral.integral_const_mul, abs_mul,
                  abs_of_nonneg (norm_nonneg (1 : 𝔸))]
        _ = ‖(1 : 𝔸)‖ * |∫ u in t₁..t, ‖H u‖| ^ (n + 1) / Nat.factorial (n + 1) := by
                rw [abs_integral_mul_abs_integral_pow_div_factorial (fun u => ‖H u‖) hH.norm
                  (fun _ => norm_nonneg _) t₁ t n]
                ring

/-- The Dyson series is summable for all `t₁ t₂` (both orientations), without `NormOneClass`. -/
lemma summable_dysonTerm_abs (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    Summable (fun n : ℕ => dysonTerm H t₁ n t₂) := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial |(∫ τ in t₁..t₂, ‖H τ‖)|).mul_left ‖(1 : 𝔸)‖) ?_
  intro n
  simpa [mul_div_assoc'] using norm_dysonTerm_le_abs H hH t₁ n t₂

/-! ### The norm bound -/

/-- `Real.exp x = ∑' n, x^n / n!` (the exponential series), in `HasSum` form. -/
lemma Real.hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / Nat.factorial n) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]
  exact (Real.summable_pow_div_factorial x).hasSum

omit [CompleteSpace 𝔸] in
/-- `lem:time_ordered_norm_bound`: `‖exp_T H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖|`
(the two-sided form, valid for both time orderings). -/
lemma timeOrderedExp_norm_le [NormOneClass 𝔸] (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖| := by
  rw [timeOrderedExp]
  refine tsum_of_norm_bounded (f := fun n : ℕ => dysonTerm H t₁ n t₂)
    (g := fun n : ℕ => |∫ τ in t₁..t₂, ‖H τ‖| ^ n / Nat.factorial n)
    (a := Real.exp |∫ τ in t₁..t₂, ‖H τ‖|) ?_ ?_
  · exact Real.hasSum_pow_div_factorial |∫ τ in t₁..t₂, ‖H τ‖|
  · intro n
    simpa using norm_dysonTerm_le_abs H hH t₁ n t₂

/-! ### The initial condition -/

omit [CompleteSpace 𝔸] in
/-- `exp_T H t₁ t₁ = 1`: the `D₀` term is `1` and all higher terms vanish because the
interval `[t₁, t₁]` has integral `0`. -/
lemma timeOrderedExp_initial (H : ℝ → 𝔸) (t₁ : ℝ) : timeOrderedExp H t₁ t₁ = 1 := by
  rw [timeOrderedExp, tsum_eq_single (0 : ℕ)]
  · simp [dysonTerm]
  · intro n hn
    cases n with
    | zero => contradiction
    | succ n => simp [dysonTerm]

/-! ### Continuity of the solution -/

/-- For continuous nonnegative `g`, the "distance travelled" `|∫_t₁^x g|` is bounded on any
interval `[a, b]` by the sum of its endpoint values: monotonicity of the oriented integral. -/
lemma abs_integral_le_abs_integral_of_mem_Icc {g : ℝ → ℝ} (hg : Continuous g)
    (hgnn : ∀ t, 0 ≤ g t) (t₁ a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    |(∫ u in t₁..x, g u)| ≤ |(∫ u in t₁..a, g u)| + |(∫ u in t₁..b, g u)| := by
  have hmono : Monotone (fun t : ℝ => ∫ u in t₁..t, g u) := by
    intro s t hst
    have hnonneg : 0 ≤ ∫ u in s..t, g u :=
      intervalIntegral.integral_nonneg hst (fun u _ => hgnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := g)
      (μ := MeasureTheory.volume) (a := t₁) (b := s) (c := t) (hg.intervalIntegrable t₁ s)
      (hg.intervalIntegrable s t)
    linarith [hadd, hnonneg]
  have hlo : (∫ u in t₁..a, g u) ≤ ∫ u in t₁..x, g u := hmono hx.1
  have hhi : (∫ u in t₁..x, g u) ≤ ∫ u in t₁..b, g u := hmono hx.2
  have hneg_abs : -|∫ u in t₁..a, g u| ≤ ∫ u in t₁..a, g u := by
    simpa using (neg_le_neg (neg_le_abs (∫ u in t₁..a, g u)))
  exact abs_le.mpr ⟨
    le_trans (le_trans (neg_le_neg (le_add_of_nonneg_right (abs_nonneg (∫ u in t₁..b, g u))))
      hneg_abs) hlo,
    le_trans (le_trans hhi (le_abs_self (∫ u in t₁..b, g u)))
      (le_add_of_nonneg_left (abs_nonneg (∫ u in t₁..a, g u)))⟩

/-- For continuous `H`, the solution `t ↦ exp_T H t₁ t` is continuous. The Dyson series
converges locally uniformly (its sup norm on any compact interval is summable), so its sum
is continuous. -/
lemma continuous_timeOrderedExp (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) :
    Continuous (fun t => timeOrderedExp H t₁ t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let a : ℝ := t₀ - 1
  let b : ℝ := t₀ + 1
  let M : ℝ := |(∫ u in t₁..a, ‖H u‖)| + |(∫ u in t₁..b, ‖H u‖)|
  let u : ℕ → ℝ := fun n => ‖(1 : 𝔸)‖ * M ^ n / Nat.factorial n
  have hM_le : ∀ t, t ∈ Set.Icc a b → |(∫ u in t₁..t, ‖H u‖)| ≤ M := by
    intro t ht
    exact abs_integral_le_abs_integral_of_mem_Icc hH.norm (fun _ => norm_nonneg _) t₁ a b t ht
  have hOn_sum : ContinuousOn (fun t => ∑' n : ℕ, dysonTerm H t₁ n t) (Set.Icc a b) := by
    refine continuousOn_tsum (u := u) (f := fun n => dysonTerm H t₁ n) (s := Set.Icc a b) ?_ ?_ ?_
    · intro n
      exact (continuous_dysonTerm H hH t₁ n).continuousOn
    · simpa [u, mul_div_assoc'] using (Real.summable_pow_div_factorial M).mul_left ‖(1 : 𝔸)‖
    · intro n t ht
      refine (norm_dysonTerm_le_abs H hH t₁ n t).trans ?_
      have hle : |(∫ u in t₁..t, ‖H u‖)| ^ n / Nat.factorial n ≤ M ^ n / Nat.factorial n :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM_le t ht) n) (by positivity)
      simpa [mul_div_assoc'] using mul_le_mul_of_nonneg_left hle (norm_nonneg (1 : 𝔸))
  have hOn : ContinuousOn (fun t => timeOrderedExp H t₁ t) (Set.Icc a b) := by
    simpa [timeOrderedExp] using hOn_sum
  exact hOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-! ### The integral equation -/

/-- `eq:int_eq` (prelim.tex:58): the integral equation
`exp_T H t₁ t₂ = 1 + ∫ τ in t₁..t₂, H τ * exp_T H t₁ τ`.
The proof commutes the `tsum` with the interval integral via the dominated convergence
theorem for series, using the two-sided termwise bound `norm_dysonTerm_le_abs`. -/
lemma timeOrderedExp_eq_integral (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₁ t₂ = 1 + ∫ τ in t₁..t₂, H τ * timeOrderedExp H t₁ τ := by
  let bound : ℕ → ℝ → ℝ := fun n τ =>
    (‖H τ‖ * ‖(1 : 𝔸)‖) * (|∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n)
  have hDCT : HasSum (fun n : ℕ => ∫ τ in t₁..t₂, H τ * dysonTerm H t₁ n τ)
      (∫ τ in t₁..t₂, H τ * timeOrderedExp H t₁ τ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (a := t₁) (b := t₂) (bound := bound)
      (f := fun τ => H τ * timeOrderedExp H t₁ τ) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (hH.mul (continuous_dysonTerm H hH t₁ n)).aestronglyMeasurable.mono_measure
        MeasureTheory.Measure.restrict_le_self
    · intro n
      filter_upwards with τ hτ
      calc
        ‖H τ * dysonTerm H t₁ n τ‖ ≤ ‖H τ‖ * ‖dysonTerm H t₁ n τ‖ := norm_mul_le _ _
        _ ≤ ‖H τ‖ * (‖(1 : 𝔸)‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n) :=
            mul_le_mul_of_nonneg_left (norm_dysonTerm_le_abs H hH t₁ n τ) (norm_nonneg (H τ))
        _ = bound n τ := by ring
    · filter_upwards with τ hτ
      simpa [bound] using
        (Real.summable_pow_div_factorial |(∫ u in t₁..τ, ‖H u‖)|).mul_left (‖H τ‖ * ‖(1 : 𝔸)‖)
    · -- `∑' n, bound n τ = ‖H τ‖ * ‖1‖ * Real.exp |∫ ‖H‖|`, which is continuous in τ.
      have hbound_tsum : ∀ τ, (∑' n, bound n τ) =
          ‖H τ‖ * ‖(1 : 𝔸)‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
        intro τ
        have hhasSum : HasSum (fun n =>
            (‖H τ‖ * ‖(1 : 𝔸)‖) * (|∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n))
            ((‖H τ‖ * ‖(1 : 𝔸)‖) * Real.exp |∫ u in t₁..τ, ‖H u‖|) :=
          (Real.hasSum_pow_div_factorial |(∫ u in t₁..τ, ‖H u‖)|).mul_left (‖H τ‖ * ‖(1 : 𝔸)‖)
        simpa [bound] using hhasSum.tsum_eq
      have hcont : Continuous (fun τ => ‖H τ‖ * ‖(1 : 𝔸)‖ * Real.exp |∫ u in t₁..τ, ‖H u‖|) := by
        fun_prop
      have hfeq : (fun τ => ∑' n, bound n τ) =
          fun τ => ‖H τ‖ * ‖(1 : 𝔸)‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
        funext τ
        exact hbound_tsum τ
      simpa [hfeq] using hcont.intervalIntegrable t₁ t₂
    · filter_upwards with τ hτ
      simpa [timeOrderedExp] using (summable_dysonTerm_abs H hH t₁ τ).hasSum.mul_left (H τ)
  have hsplit : (∑' n : ℕ, dysonTerm H t₁ n t₂) =
      dysonTerm H t₁ 0 t₂ + ∑' n : ℕ, dysonTerm H t₁ (n + 1) t₂ :=
    (summable_dysonTerm_abs H hH t₁ t₂).tsum_eq_zero_add
  rw [timeOrderedExp, hsplit]
  have hd0 : dysonTerm H t₁ 0 t₂ = 1 := by simp [dysonTerm]
  rw [hd0]; congr 1
  have hsum1 : (∑' n : ℕ, dysonTerm H t₁ (n + 1) t₂) =
      ∑' n : ℕ, ∫ τ in t₁..t₂, H τ * dysonTerm H t₁ n τ := by
    apply tsum_congr
    intro n
    rw [dysonTerm]
  rw [hsum1]
  exact hDCT.tsum_eq

/-! ### Derivative with respect to the upper limit -/

/-- `prelim.tex:44-49` (first rule): derivative with respect to the upper limit
`∂/∂t₂ exp_T(∫_{t₁}^{t₂} H) = H(t₂) · exp_T(∫_{t₁}^{t₂} H)`.
Follows from the integral equation and `intervalIntegral.integral_hasDerivAt_right`. -/
lemma timeOrderedExp_hasDerivAt (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => timeOrderedExp H t₁ s) (H t₂ * timeOrderedExp H t₁ t₂) t₂ := by
  have hfcont : Continuous (fun τ => H τ * timeOrderedExp H t₁ τ) :=
    hH.mul (continuous_timeOrderedExp H hH t₁)
  have hderiv_integral : HasDerivAt (fun s => ∫ τ in t₁..s, H τ * timeOrderedExp H t₁ τ)
      (H t₂ * timeOrderedExp H t₁ t₂) t₂ :=
    intervalIntegral.integral_hasDerivAt_right (hfcont.intervalIntegrable t₁ t₂)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter hfcont.continuousAt
  have heq : (fun s => timeOrderedExp H t₁ s) =
      fun s => 1 + ∫ τ in t₁..s, H τ * timeOrderedExp H t₁ τ := by
    funext s
    rw [timeOrderedExp_eq_integral H hH t₁ s]
  rw [heq]
  exact hderiv_integral.const_add 1

/-! ### Uniqueness of solutions to the ODE -/

omit [CompleteSpace 𝔸] in
/-- Uniqueness of solutions to the ODE `U' = H·U`: two functions solving `U' = H·U` pointwise and
agreeing at one time `t₀` agree everywhere. The continuity of `H` is used only to obtain a uniform
Lipschitz constant on the compact interval between `t₀` and each target point. -/
lemma ode_solution_unique (H : ℝ → 𝔸) (hH : Continuous H) {f g : ℝ → 𝔸}
    (hf : ∀ t, HasDerivAt f (H t * f t) t) (hg : ∀ t, HasDerivAt g (H t * g t) t)
    (t₀ : ℝ) (heq : f t₀ = g t₀) : f = g := by
  funext t
  let a : ℝ := min t t₀ - 1
  let b : ℝ := max t t₀ + 1
  have ht₀ : t₀ ∈ Set.Ioo a b := by
    constructor <;> linarith [min_le_right t t₀, le_max_right t t₀]
  have ht : t ∈ Set.Ioo a b := by
    constructor <;> linarith [min_le_left t t₀, le_max_left t t₀]
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨t₀, ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩⟩ (hH.norm.continuousOn)
  let M : NNReal := ⟨‖H x‖, norm_nonneg (H x)⟩
  have hM : ∀ s ∈ Set.Icc a b, ‖H s‖ ≤ (M : ℝ) := fun s hs => (isMaxOn_iff.mp hmax) s hs
  have hv : ∀ s ∈ Set.Ioo a b, LipschitzOnWith M (fun y : 𝔸 => H s * y) Set.univ := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    calc
      dist (H s * x) (H s * y) = ‖H s * (x - y)‖ := by
          rw [dist_eq_norm, mul_sub]
      _ ≤ ‖H s‖ * ‖x - y‖ := norm_mul_le _ _
      _ ≤ (M : ℝ) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (hM s (Set.Ioo_subset_Icc_self hs)) (norm_nonneg (x - y))
      _ = M * dist x y := by simp [dist_eq_norm]
  have hres := ODE_solution_unique_of_mem_Ioo
    (v := fun s y => H s * y) (s := fun _ => Set.univ) (K := M)
    (f := f) (g := g) (a := a) (b := b) (t₀ := t₀) hv ht₀
    (fun s hs => ⟨hf s, trivial⟩) (fun s hs => ⟨hg s, trivial⟩) heq
  exact hres ht

/-! ### The multiplicative property -/

/-- `prelim.tex:52`: the multiplicative property
`exp_T H t₁ t₃ = exp_T H t₂ t₃ · exp_T H t₁ t₂`. Both sides solve the ODE `U' = H·U` and agree
at `t₂`, so they are equal by `ode_solution_unique`. -/
lemma timeOrderedExp_mul (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ t₃ : ℝ) :
    timeOrderedExp H t₁ t₃ = timeOrderedExp H t₂ t₃ * timeOrderedExp H t₁ t₂ := by
  have hf : ∀ t, HasDerivAt (fun s => timeOrderedExp H t₁ s) (H t * timeOrderedExp H t₁ t) t :=
    fun t => timeOrderedExp_hasDerivAt H hH t₁ t
  have hg : ∀ t, HasDerivAt (fun s => timeOrderedExp H t₂ s * timeOrderedExp H t₁ t₂)
      (H t * (timeOrderedExp H t₂ t * timeOrderedExp H t₁ t₂)) t := by
    intro t
    simpa [mul_assoc] using
      (timeOrderedExp_hasDerivAt H hH t₂ t).mul_const (timeOrderedExp H t₁ t₂)
  have heq : timeOrderedExp H t₁ t₂ =
      timeOrderedExp H t₂ t₂ * timeOrderedExp H t₁ t₂ := by
    rw [timeOrderedExp_initial H t₂, one_mul]
  exact congr_fun (ode_solution_unique H hH hf hg t₂ heq) t₃

/-! ### Invertibility -/

/-- The inverse evolution: `exp_T H t₁ t₂ · exp_T H t₂ t₁ = 1`. -/
lemma timeOrderedExp_mul_inv_self (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₁ t₂ * timeOrderedExp H t₂ t₁ = 1 := by
  have h := timeOrderedExp_mul H hH t₂ t₁ t₂
  rw [timeOrderedExp_initial H t₂] at h
  exact h.symm

/-- The inverse evolution, other side: `exp_T H t₂ t₁ · exp_T H t₁ t₂ = 1`. -/
lemma timeOrderedExp_inv_mul_self (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₂ t₁ * timeOrderedExp H t₁ t₂ = 1 := by
  have h := timeOrderedExp_mul H hH t₁ t₂ t₁
  rw [timeOrderedExp_initial H t₁] at h
  exact h.symm

/-- Every time-ordered exponential is a unit. -/
lemma isUnit_timeOrderedExp (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    IsUnit (timeOrderedExp H t₁ t₂) := isUnit_iff_exists.mpr ⟨timeOrderedExp H t₂ t₁,
  timeOrderedExp_mul_inv_self H hH t₁ t₂, timeOrderedExp_inv_mul_self H hH t₁ t₂⟩

/-! ### Constant generator -/

/-- `∫ τ in a..b, (τ - a)^n = (b - a)^(n+1) / (n+1)`. -/
lemma integral_sub_pow (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, (τ - a) ^ n) = (b - a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  have hfun : (fun τ : ℝ => (τ - a) ^ n) = fun τ => (τ + (-a)) ^ n := by
    funext τ
    rw [sub_eq_add_neg]
  rw [hfun, intervalIntegral.integral_comp_add_right (f := fun σ : ℝ => σ ^ n) (d := -a),
    integral_pow]
  simp [sub_eq_add_neg]

/-- For the constant generator, the `n`-th Dyson term is `(n!⁻¹ : ℝ) • ((t - t₁) • H)^n`. -/
lemma dysonTerm_const (H : 𝔸) (t₁ : ℝ) (n : ℕ) (t : ℝ) :
    dysonTerm (fun _ : ℝ => H) t₁ n t = (Nat.factorial n : ℝ)⁻¹ • ((t - t₁) • H) ^ n := by
  induction n generalizing t with
  | zero => simp [dysonTerm]
  | succ n ih =>
      simp_rw [dysonTerm, ih, mul_smul_comm]
      rw [intervalIntegral.integral_smul]
      have hkey : (∫ τ in t₁..t, H * ((τ - t₁) • H) ^ n) =
          ((n + 1 : ℕ) : ℝ)⁻¹ • ((t - t₁) • H) ^ (n + 1) := by
        calc
          (∫ τ in t₁..t, H * ((τ - t₁) • H) ^ n)
              = ∫ τ in t₁..t, (τ - t₁) ^ n • H ^ (n + 1) := by
                  apply intervalIntegral.integral_congr_uIoo
                  intro τ hτ
                  dsimp
                  rw [smul_pow, mul_smul_comm, ← pow_succ']
          _ = (∫ τ in t₁..t, (τ - t₁) ^ n) • H ^ (n + 1) :=
                  intervalIntegral.integral_smul_const (f := fun τ => (τ - t₁) ^ n)
                    (c := H ^ (n + 1))
          _ = (((t - t₁) ^ (n + 1)) / ((n + 1 : ℕ) : ℝ)) • H ^ (n + 1) := by
                  rw [integral_sub_pow t₁ t n]
          _ = ((n + 1 : ℕ) : ℝ)⁻¹ • ((t - t₁) • H) ^ (n + 1) := by
                  rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← smul_pow]
      rw [hkey, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]

/-- `prelim.tex:41` (the paper states the `0 → t` case `e^{tH}`; this is its arbitrary-interval
form): for the constant generator, the time-ordered exponential is the ordinary matrix
exponential `exp ((t₂ - t₁) • H)`. Proved directly from the Dyson series. -/
lemma timeOrderedExp_const (H : 𝔸) (t₁ t₂ : ℝ) :
    timeOrderedExp (fun _ => H) t₁ t₂ = exp ((t₂ - t₁) • H) := by
  rw [timeOrderedExp, NormedSpace.exp_eq_tsum ℝ]
  apply tsum_congr
  intro n
  rw [dysonTerm_const H t₁ n t₂]

/-! ### Derivative with respect to the lower limit -/

/-- `prelim.tex:44-49` (second rule): derivative with respect to the lower limit
`∂/∂t₁ exp_T(∫_{t₁}^{t₂} H) = -exp_T(∫_{t₁}^{t₂} H) · H(t₁)`.

By the inverse relation, `exp_T H s t₂ = (exp_T H t₂ s)⁻¹`, so the result follows from the
derivative of the (ring) inversion `hasFDerivAt_ringInverse` composed with the upper-limit
derivative `timeOrderedExp_hasDerivAt`. -/
lemma timeOrderedExp_hasDerivAt_lower (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => timeOrderedExp H s t₂) (-(timeOrderedExp H t₁ t₂ * H t₁)) t₁ := by
  let u : ℝ → 𝔸ˣ := fun s =>
    ⟨timeOrderedExp H t₂ s, timeOrderedExp H s t₂,
      timeOrderedExp_mul_inv_self H hH t₂ s, timeOrderedExp_inv_mul_self H hH t₂ s⟩
  have hderiv : HasDerivAt (Ring.inverse ∘ fun s => timeOrderedExp H t₂ s)
      (-(timeOrderedExp H t₁ t₂ * H t₁)) t₁ := by
    have H₁ : HasFDerivAt Ring.inverse _ (u t₁ : 𝔸) := hasFDerivAt_ringInverse (𝕜 := ℝ) (u t₁)
    have H₂ : HasDerivAt (fun s => timeOrderedExp H t₂ s) (H t₁ * timeOrderedExp H t₂ t₁) t₁ :=
      timeOrderedExp_hasDerivAt H hH t₂ t₁
    have hu_inv : (((u t₁)⁻¹ : 𝔸ˣ) : 𝔸) = timeOrderedExp H t₁ t₂ := rfl
    simpa [hu_inv, mul_assoc, timeOrderedExp_inv_mul_self H hH t₁ t₂] using
      (H₁.comp_hasDerivAt t₁ H₂)
  have hfun : (fun s => timeOrderedExp H s t₂) = Ring.inverse ∘ fun s => timeOrderedExp H t₂ s := by
    funext s
    have h := Ring.inverse_unit (u s)
    simpa [u] using h.symm
  rwa [hfun]

/-! ### Continuity in the lower limit -/

/-- For continuous `H`, the time-ordered exponential `t ↦ exp_T H t t₂` is continuous in its lower
limit. -/
lemma continuous_timeOrderedExp_lower (H : ℝ → 𝔸) (hH : Continuous H) (t₂ : ℝ) :
    Continuous (fun t => timeOrderedExp H t t₂) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (timeOrderedExp_hasDerivAt_lower H hH t t₂).continuousAt

/-! ### Duhamel / variation of parameters -/

/-- Left multiplication by a constant commutes with the interval integral (for a general normed
ℝ-algebra). -/
lemma integral_mul_left (c : 𝔸) (f : ℝ → 𝔸) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, c * f x) = c * ∫ x in a..b, f x := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul ℝ 𝔸 c).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

/-- The Duhamel (variation-of-parameters) particular integral factors through the forward evolution:
`∫ τ in t₀..t, exp_T H τ t · R τ = exp_T H t₀ t · ∫ τ in t₀..t, exp_T H τ t₀ · R τ`, using the
multiplicative property `exp_T H τ t = exp_T H t₀ t · exp_T H τ t₀`. -/
lemma duhamelParticular_factor (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    (t₀ t : ℝ) :
    (∫ τ in t₀..t, timeOrderedExp H τ t * R τ) =
      timeOrderedExp H t₀ t * ∫ τ in t₀..t, timeOrderedExp H τ t₀ * R τ := by
  calc
    (∫ τ in t₀..t, timeOrderedExp H τ t * R τ)
        = ∫ τ in t₀..t, (timeOrderedExp H t₀ t * timeOrderedExp H τ t₀) * R τ := by
            apply intervalIntegral.integral_congr_uIoo
            intro τ hτ
            simp [timeOrderedExp_mul H hH τ t₀ t]
    _ = ∫ τ in t₀..t, timeOrderedExp H t₀ t * (timeOrderedExp H τ t₀ * R τ) := by
            apply intervalIntegral.integral_congr_uIoo
            intro τ hτ
            simp [mul_assoc]
    _ = timeOrderedExp H t₀ t * ∫ τ in t₀..t, timeOrderedExp H τ t₀ * R τ := integral_mul_left
            (timeOrderedExp H t₀ t) (fun τ => timeOrderedExp H τ t₀ * R τ)
              ((continuous_timeOrderedExp_lower H hH t₀).mul hR) t₀ t

/-- The Duhamel particular solution `t ↦ ∫ τ in t₀..t, exp_T H τ t · R τ` solves the inhomogeneous
ODE with zero initial value: its derivative is `R t + H t · (that integral)`. -/
lemma duhamelParticular_hasDerivAt (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    (t₀ t : ℝ) :
    HasDerivAt (fun s => ∫ τ in t₀..s, timeOrderedExp H τ s * R τ)
      (R t + H t * ∫ τ in t₀..t, timeOrderedExp H τ t * R τ) t := by
  let Ψ : ℝ → 𝔸 := fun s => ∫ τ in t₀..s, timeOrderedExp H τ t₀ * R τ
  have hfeq : (fun s => ∫ τ in t₀..s, timeOrderedExp H τ s * R τ) =
      fun s => timeOrderedExp H t₀ s * Ψ s := by
    funext s
    exact duhamelParticular_factor H R hH hR t₀ s
  have hΨderiv : HasDerivAt Ψ (timeOrderedExp H t t₀ * R t) t := by
    have hcont : Continuous (fun τ => timeOrderedExp H τ t₀ * R τ) :=
      (continuous_timeOrderedExp_lower H hH t₀).mul hR
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable t₀ t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hderiv : HasDerivAt (fun s => timeOrderedExp H t₀ s * Ψ s)
      (H t * (timeOrderedExp H t₀ t * Ψ t) + R t) t := by
    have h1 := (timeOrderedExp_hasDerivAt H hH t₀ t).mul hΨderiv
    have hderiv_eq : (H t * timeOrderedExp H t₀ t) * Ψ t +
          timeOrderedExp H t₀ t * (timeOrderedExp H t t₀ * R t)
        = H t * (timeOrderedExp H t₀ t * Ψ t) + R t := by
      rw [mul_assoc, ← mul_assoc (timeOrderedExp H t₀ t) (timeOrderedExp H t t₀) (R t),
        timeOrderedExp_mul_inv_self H hH t₀ t, one_mul]
    exact hderiv_eq ▸ h1
  rw [hfeq]
  simpa [duhamelParticular_factor H R hH hR t₀ t, add_comm] using hderiv

/-- The closed-form solution of `U' = H · U + R`, `U 0 = U₀`, satisfies the ODE: its derivative is
`H t · (that expression) + R t`. -/
lemma timeOrderedExp_duhamel_hasDerivAt (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    (U₀ : 𝔸) (t : ℝ) :
    HasDerivAt (fun s => timeOrderedExp H 0 s * U₀ + ∫ τ in 0..s, timeOrderedExp H τ s * R τ)
      (H t * (timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ) + R t) t := by
  have hhom := (timeOrderedExp_hasDerivAt H hH 0 t).mul_const U₀
  have hpart := duhamelParticular_hasDerivAt H R hH hR 0 t
  have hsum := hhom.add hpart
  have hderiv_eq : (H t * timeOrderedExp H 0 t) * U₀ +
        (R t + H t * ∫ τ in 0..t, timeOrderedExp H τ t * R τ)
      = H t * (timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ) + R t := by
    rw [mul_add, ← mul_assoc]
    abel
  exact hderiv_eq ▸ hsum

omit [CompleteSpace 𝔸] in
/-- The closed-form solution of `U' = H · U + R` has initial value `U₀`. -/
lemma timeOrderedExp_duhamel_initial (H R : ℝ → 𝔸) (U₀ : 𝔸) :
    timeOrderedExp H 0 0 * U₀ + ∫ τ in 0..0, timeOrderedExp H τ 0 * R τ = U₀ := by
  rw [timeOrderedExp_initial H 0, one_mul, intervalIntegral.integral_same, add_zero]

/-- `lem:td_Duhamel` (variation of parameters): the unique solution of `U' = H · U + R`,
`U 0 = U₀`, is `exp_T(∫₀ᵗ H) · U₀ + ∫ τ in 0..t, exp_T(∫_τ^t H) · R τ`. -/
lemma timeOrderedExp_duhamel (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    {U : ℝ → 𝔸} (U₀ : 𝔸) (hU : ∀ t, HasDerivAt U (H t * U t + R t) t) (hU0 : U 0 = U₀) (t : ℝ) :
    U t = timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ := by
  let F : ℝ → 𝔸 := fun s => timeOrderedExp H 0 s * U₀ + ∫ τ in 0..s, timeOrderedExp H τ s * R τ
  have hF : ∀ s, HasDerivAt F (H s * F s + R s) s := by
    intro s
    simpa [F] using timeOrderedExp_duhamel_hasDerivAt H R hH hR U₀ s
  have hF0 : F 0 = U₀ := by
    simpa [F] using timeOrderedExp_duhamel_initial H R U₀
  let d : ℝ → 𝔸 := fun s => U s - F s
  have hd : ∀ s, HasDerivAt d (H s * d s) s := by
    intro s
    have hsub := (hU s).sub (hF s)
    have hderiv_eq : (H s * U s + R s) - (H s * F s + R s) = H s * (U s - F s) := by
      rw [mul_sub]
      abel
    simpa [d] using (hderiv_eq ▸ hsub)
  have hd0 : d 0 = 0 := by
    dsimp [d]
    rw [hU0, hF0, sub_self]
  have hzero : ∀ s, HasDerivAt (fun _ : ℝ => (0 : 𝔸)) (H s * (0 : 𝔸)) s := by
    intro s
    simpa using (hasDerivAt_const (x := s) (c := (0 : 𝔸)))
  have hd_eq_zero : d = fun _ : ℝ => (0 : 𝔸) := ode_solution_unique H hH hd hzero 0 hd0
  have hU_eq_F : U = F := by
    funext s
    have hds : d s = 0 := congr_fun hd_eq_zero s
    dsimp [d] at hds
    exact sub_eq_zero.mp hds
  simpa [F] using congr_fun hU_eq_F t

/-! ### Interaction picture -/

/-- `lem:interaction_picture` (time-ordered evolution in the interaction picture):
`exp_T(∫₀ᵗ (A + B)) = exp_T(∫₀ᵗ A) · exp_T(∫₀ᵗ (exp_T A τ 0 · B τ · exp_T A 0 τ))`. -/
lemma timeOrderedExp_interaction_picture (A B : ℝ → 𝔸) (hA : Continuous A) (hB : Continuous B)
    (t : ℝ) :
    timeOrderedExp (fun τ => A τ + B τ) 0 t =
      timeOrderedExp A 0 t * timeOrderedExp (fun τ =>
        timeOrderedExp A τ 0 * B τ * timeOrderedExp A 0 τ) 0 t := by
  let H : ℝ → 𝔸 := fun τ => A τ + B τ
  let Bt : ℝ → 𝔸 := fun τ => timeOrderedExp A τ 0 * B τ * timeOrderedExp A 0 τ
  have hH : Continuous H := hA.add hB
  have hBt : Continuous Bt :=
    ((continuous_timeOrderedExp_lower A hA 0).mul hB).mul (continuous_timeOrderedExp A hA 0)
  have hUderiv : ∀ s, HasDerivAt (fun r => timeOrderedExp A 0 r * timeOrderedExp Bt 0 r)
      (H s * (timeOrderedExp A 0 s * timeOrderedExp Bt 0 s)) s := by
    intro s
    have h1 := (timeOrderedExp_hasDerivAt A hA 0 s).mul (timeOrderedExp_hasDerivAt Bt hBt 0 s)
    have hkey : (A s * timeOrderedExp A 0 s) * timeOrderedExp Bt 0 s
        + timeOrderedExp A 0 s * (Bt s * timeOrderedExp Bt 0 s)
        = (A s + B s) * (timeOrderedExp A 0 s * timeOrderedExp Bt 0 s) := by
      rw [add_mul]
      congr 1
      · rw [mul_assoc]
      · let E : 𝔸 := timeOrderedExp A 0 s
        let Ei : 𝔸 := timeOrderedExp A s 0
        let F : 𝔸 := timeOrderedExp Bt 0 s
        have hBts : Bt s = Ei * B s * E := rfl
        have hEi : E * Ei = 1 := by
          simpa [E, Ei] using timeOrderedExp_mul_inv_self A hA 0 s
        change E * (Bt s * F) = B s * (E * F)
        rw [hBts]
        calc
          E * ((Ei * B s * E) * F)
              = E * ((Ei * B s) * (E * F)) :=
                  congrArg (fun x => E * x) (mul_assoc (Ei * B s) E F)
          _ = (E * (Ei * B s)) * (E * F) := (mul_assoc E (Ei * B s) (E * F)).symm
          _ = ((E * Ei) * B s) * (E * F) :=
                  congrArg (fun x => x * (E * F)) ((mul_assoc E Ei (B s)).symm)
          _ = B s * (E * F) := by rw [hEi, one_mul]
    simpa [H] using (hkey ▸ h1)
  have hLHSderiv : ∀ s, HasDerivAt (fun r => timeOrderedExp H 0 r) (H s * timeOrderedExp H 0 s) s :=
    fun s => timeOrderedExp_hasDerivAt H hH 0 s
  have hU0 : timeOrderedExp A 0 0 * timeOrderedExp Bt 0 0 = 1 := by
    rw [timeOrderedExp_initial A 0, timeOrderedExp_initial Bt 0, mul_one]
  have huniq := ode_solution_unique H hH hLHSderiv hUderiv 0
    (by rw [timeOrderedExp_initial H 0, hU0])
  simpa [H, Bt] using congr_fun huniq t

/-! ### Fundamental theorem of time-ordered evolution -/

/-- For continuous `H`, the solution `t ↦ exp_T H t₁ t` is `C¹`. -/
lemma contDiff_timeOrderedExp (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) :
    ContDiff ℝ 1 (fun t => timeOrderedExp H t₁ t) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro t
    exact (timeOrderedExp_hasDerivAt H hH t₁ t).differentiableAt
  · have hderiv :
        deriv (fun t => timeOrderedExp H t₁ t) = fun t => H t * timeOrderedExp H t₁ t := by
      funext t
      exact (timeOrderedExp_hasDerivAt H hH t₁ t).deriv
    rw [hderiv]
    exact hH.mul (continuous_timeOrderedExp H hH t₁)

/-- (⇒) of `lem:fte`: a `C¹` function that is pointwise a unit is generated by the continuous
generator `H t = deriv U t * Ring.inverse (U t)`. -/
lemma fundamentalTheorem_timeOrderedExp_of_isUnit (U : ℝ → 𝔸) (hU : ContDiff ℝ 1 U)
    (hunit : ∀ t, IsUnit (U t)) :
    IsUnit (U 0) ∧ ∃ H : ℝ → 𝔸, Continuous H ∧ ∀ t, U t = timeOrderedExp H 0 t * U 0 := by
  refine ⟨hunit 0, ?_⟩
  let H : ℝ → 𝔸 := fun t => deriv U t * Ring.inverse (U t)
  have hUdiff : Differentiable ℝ U := (contDiff_one_iff_deriv.mp hU).1
  have hUderivcont : Continuous (deriv U) := (contDiff_one_iff_deriv.mp hU).2
  have hUcont : Continuous U := hU.continuous
  have hInvCont : Continuous (fun t => Ring.inverse (U t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (differentiableAt_inverse (𝕜 := ℝ) (hunit t)).continuousAt.comp hUcont.continuousAt
  have hH : Continuous H := hUderivcont.mul hInvCont
  have hHasDeriv : ∀ t, HasDerivAt U (H t * U t) t := by
    intro t
    have hd : HasDerivAt U (deriv U t) t := (hUdiff t).hasDerivAt
    have hkey : (deriv U t * Ring.inverse (U t)) * U t = deriv U t := by
      rw [mul_assoc, Ring.inverse_mul_cancel (U t) (hunit t), mul_one]
    simpa [H, hkey] using hd
  have hTODeriv : ∀ t, HasDerivAt (fun s => timeOrderedExp H 0 s * U 0)
      (H t * (timeOrderedExp H 0 t * U 0)) t := by
    intro t
    simpa [mul_assoc] using (timeOrderedExp_hasDerivAt H hH 0 t).mul_const (U 0)
  have heq0 : U 0 = timeOrderedExp H 0 0 * U 0 := by
    rw [timeOrderedExp_initial H 0, one_mul]
  refine ⟨H, hH, ?_⟩
  intro t
  exact congr_fun (ode_solution_unique H hH hHasDeriv hTODeriv 0 heq0) t

/-- (⇐) of `lem:fte`: `t ↦ exp_T H 0 t · U 0` is `C¹` and pointwise a unit when `U 0` is a unit. -/
lemma fundamentalTheorem_timeOrderedExp_of_timeOrderedExp (U : ℝ → 𝔸) (hU0 : IsUnit (U 0))
    (H : ℝ → 𝔸) (hH : Continuous H) (hEq : ∀ t, U t = timeOrderedExp H 0 t * U 0) :
    ContDiff ℝ 1 U ∧ ∀ t, IsUnit (U t) := by
  refine ⟨?_, ?_⟩
  · have hUfun : U = fun t => timeOrderedExp H 0 t * U 0 := by
      funext t
      exact hEq t
    rw [hUfun]
    exact (contDiff_timeOrderedExp H hH 0).mul contDiff_const
  · intro t
    rw [hEq t]
    exact (isUnit_timeOrderedExp H hH 0 t).mul hU0

/-- `lem:fte` (fundamental theorem of time-ordered evolution): `U` is `C¹` and pointwise a unit iff
it is `exp_T(∫₀ᵗ H) · U 0` for some continuous `H` and `U 0` is a unit. -/
lemma fundamentalTheorem_timeOrderedExp (U : ℝ → 𝔸) :
    (ContDiff ℝ 1 U ∧ ∀ t, IsUnit (U t)) ↔
      IsUnit (U 0) ∧ ∃ H : ℝ → 𝔸, Continuous H ∧ ∀ t, U t = timeOrderedExp H 0 t * U 0 := by
  constructor
  · rintro ⟨hU, hunit⟩
    exact fundamentalTheorem_timeOrderedExp_of_isUnit U hU hunit
  · rintro ⟨hU0, H, hH, hEq⟩
    exact fundamentalTheorem_timeOrderedExp_of_timeOrderedExp U hU0 H hH hEq

/-- The generator in the fundamental theorem is unique: any two continuous generators `H₁, H₂`
with `U t = exp_T Hᵢ 0 t · U 0` coincide (they both equal `deriv U · Ring.inverse (U ·)`). -/
lemma fundamentalTheorem_timeOrderedExp_unique (U : ℝ → 𝔸) (hU0 : IsUnit (U 0))
    (H₁ H₂ : ℝ → 𝔸) (hH₁ : Continuous H₁) (hH₂ : Continuous H₂)
    (hEq₁ : ∀ t, U t = timeOrderedExp H₁ 0 t * U 0)
    (hEq₂ : ∀ t, U t = timeOrderedExp H₂ 0 t * U 0) :
    H₁ = H₂ := by
  funext t
  have hUt : IsUnit (U t) := by
    rw [hEq₁ t]
    exact (isUnit_timeOrderedExp H₁ hH₁ 0 t).mul hU0
  have hderiv₁ : deriv U t = (H₁ t * timeOrderedExp H₁ 0 t) * U 0 := by
    have hUfun₁ : U = fun s => timeOrderedExp H₁ 0 s * U 0 := by
      funext s; exact hEq₁ s
    have h := (timeOrderedExp_hasDerivAt H₁ hH₁ 0 t).mul_const (U 0)
    conv_lhs => rw [hUfun₁]
    exact h.deriv
  have hderiv₂ : deriv U t = (H₂ t * timeOrderedExp H₂ 0 t) * U 0 := by
    have hUfun₂ : U = fun s => timeOrderedExp H₂ 0 s * U 0 := by
      funext s; exact hEq₂ s
    have h := (timeOrderedExp_hasDerivAt H₂ hH₂ 0 t).mul_const (U 0)
    conv_lhs => rw [hUfun₂]
    exact h.deriv
  have hEqU : H₁ t * U t = H₂ t * U t := by
    calc
      H₁ t * U t = (H₁ t * timeOrderedExp H₁ 0 t) * U 0 := by
          rw [hEq₁ t, ← mul_assoc]
      _ = (H₂ t * timeOrderedExp H₂ 0 t) * U 0 := by rw [← hderiv₁, hderiv₂]
      _ = H₂ t * U t := by rw [mul_assoc, ← hEq₂ t]
  have hcancel := congrArg (fun x => x * Ring.inverse (U t)) hEqU
  calc
    H₁ t = H₁ t * U t * Ring.inverse (U t) := by
        rw [mul_assoc, Ring.mul_inverse_cancel (U t) hUt, mul_one]
    _ = H₂ t * U t * Ring.inverse (U t) := hcancel
    _ = H₂ t := by
        rw [mul_assoc, Ring.mul_inverse_cancel (U t) hUt, mul_one]

/-! ### The norm-equals-one branch for skew generators -/

/-- `lem:time_ordered_norm_bound` (item 2): when the generator `H` is pointwise skew-adjoint
(`star (H τ) = -H τ`), the time-ordered exponential is unitary, hence `‖exp_T H t₁ t₂‖ = 1`.
The proof shows `W t := star (U t) * U t` (with `U t := exp_T H t₁ t`) has derivative `0`, so `W`
is constant and `W t₂ = W t₁ = 1`; thus `U t₂` is unitary and the norm follows from the
C*-identity. -/
lemma timeOrderedExp_norm_eq_one_of_skewAdjoint
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : ℝ → 𝔸) (hH : Continuous H) (hskew : ∀ τ, star (H τ) = -H τ) (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂‖ = 1 := by
  let U : ℝ → 𝔸 := fun t => timeOrderedExp H t₁ t
  let W : ℝ → 𝔸 := fun t => star (U t) * U t
  have hUderiv : ∀ t, HasDerivAt U (H t * U t) t := fun t =>
    timeOrderedExp_hasDerivAt H hH t₁ t
  have hstarUderiv : ∀ t, HasDerivAt (fun s => star (U s)) (star (H t * U t)) t := by
    intro t
    have hcomp : HasDerivAt (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) ∘ U)
        (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (H t * U t)) t :=
      (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸).hasFDerivAt.comp_hasDerivAt t (hUderiv t))
    have hfun : (⇑(starL' ℝ : 𝔸 ≃L[ℝ] 𝔸)) ∘ U = fun s => star (U s) := by
      funext s
      simp
    simpa [hfun] using hcomp
  have hWderiv : ∀ t, HasDerivAt W 0 t := by
    intro t
    have hmul : HasDerivAt (fun s => star (U s) * U s)
        (star (H t * U t) * U t + star (U t) * (H t * U t)) t :=
      (hstarUderiv t).mul (hUderiv t)
    have hkey : star (H t * U t) * U t + star (U t) * (H t * U t) = 0 := by
      rw [star_mul, hskew t, mul_assoc, ← mul_add, ← add_mul]
      simp
    simpa [W] using (hkey ▸ hmul)
  have hWdiff : Differentiable ℝ W := fun t => (hWderiv t).differentiableAt
  have hWderiv_eq : ∀ t, deriv W t = 0 := fun t => (hWderiv t).deriv
  have hWconst : W t₂ = W t₁ := is_const_of_deriv_eq_zero hWdiff hWderiv_eq t₂ t₁
  have hWt₁ : W t₁ = 1 := by
    simp [W, U, timeOrderedExp_initial H t₁]
  have hstar_mul_self : star (timeOrderedExp H t₁ t₂) * timeOrderedExp H t₁ t₂ = 1 := by
    simpa [W, U] using hWconst.trans hWt₁
  have hmem : timeOrderedExp H t₁ t₂ ∈ unitary 𝔸 :=
    IsUnit.mem_unitary_of_star_mul_self (isUnit_timeOrderedExp H hH t₁ t₂) hstar_mul_self
  exact CStarRing.norm_of_mem_unitary hmem

/-! ### Distance bound: monotonicity "last mile" -/

/-- For nonnegative continuous `f, g` and `x` in the unordered interval between `a` and `b`, the
sum of the two partial oriented-absolute integrals `|∫_x^b f| + |∫_a^x g|` is at most
`|∫_a^b (f + g)|`. This is the monotonicity "last mile" for the distance bound: both partial
integrals carry the sign of the orientation, so their absolute values telescope into the single
oriented integral of `f + g`. -/
lemma abs_integral_add_le_abs_integral_of_mem_uIcc {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfnn : ∀ t, 0 ≤ f t) (hgnn : ∀ t, 0 ≤ g t) (a b x : ℝ)
    (hx : x ∈ Set.uIcc a b) :
    |∫ u in x..b, f u| + |∫ u in a..x, g u| ≤ |∫ u in a..b, f u + g u| := by
  by_cases hab : a ≤ b
  · -- forward: `a ≤ x ≤ b`, all partial integrals are nonnegative.
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    have hfx : 0 ≤ ∫ u in x..b, f u :=
      intervalIntegral.integral_nonneg hx'.2 (fun u _ => hfnn u)
    have hgx : 0 ≤ ∫ u in a..x, g u :=
      intervalIntegral.integral_nonneg hx'.1 (fun u _ => hgnn u)
    have hfg : 0 ≤ ∫ u in a..b, f u + g u :=
      intervalIntegral.integral_nonneg hab (fun u _ => add_nonneg (hfnn u) (hgnn u))
    rw [abs_of_nonneg hfx, abs_of_nonneg hgx, abs_of_nonneg hfg]
    have hfx_le : ∫ u in x..b, f u ≤ ∫ u in x..b, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := x) (b := b) hx'.2
        (hf.intervalIntegrable x b) ((hf.add hg).intervalIntegrable x b) ?_
      intro u _
      exact le_add_of_nonneg_right (hgnn u)
    have hgx_le : ∫ u in a..x, g u ≤ ∫ u in a..x, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := a) (b := x) hx'.1
        (hg.intervalIntegrable a x) ((hf.add hg).intervalIntegrable a x) ?_
      intro u _
      exact le_add_of_nonneg_left (hfnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := fun u => f u + g u)
      (μ := MeasureTheory.volume) (a := a) (b := x) (c := b)
      ((hf.add hg).intervalIntegrable a x) ((hf.add hg).intervalIntegrable x b)
    calc
      (∫ u in x..b, f u) + ∫ u in a..x, g u
          ≤ (∫ u in a..x, f u + g u) + ∫ u in x..b, f u + g u :=
              (add_le_add hfx_le hgx_le).trans_eq (add_comm _ _)
      _ = ∫ u in a..b, f u + g u := hadd
  · -- backward: `b ≤ x ≤ a`, the partial integrals are nonpositive, so their absolute values are
    -- the integrals over the reversed (nonnegative) subintervals.
    have hba : b ≤ a := le_of_not_ge hab
    have hx' : x ∈ Set.Icc b a := by
      simpa [Set.uIcc_of_ge hba] using hx
    have hfx : 0 ≤ ∫ u in b..x, f u :=
      intervalIntegral.integral_nonneg hx'.1 (fun u _ => hfnn u)
    have hgx : 0 ≤ ∫ u in x..a, g u :=
      intervalIntegral.integral_nonneg hx'.2 (fun u _ => hgnn u)
    have hfg : 0 ≤ ∫ u in b..a, f u + g u :=
      intervalIntegral.integral_nonneg hba (fun u _ => add_nonneg (hfnn u) (hgnn u))
    have hfx_le : ∫ u in b..x, f u ≤ ∫ u in b..x, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := b) (b := x) hx'.1
        (hf.intervalIntegrable b x) ((hf.add hg).intervalIntegrable b x) ?_
      intro u _
      exact le_add_of_nonneg_right (hgnn u)
    have hgx_le : ∫ u in x..a, g u ≤ ∫ u in x..a, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := x) (b := a) hx'.2
        (hg.intervalIntegrable x a) ((hf.add hg).intervalIntegrable x a) ?_
      intro u _
      exact le_add_of_nonneg_left (hfnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := fun u => f u + g u)
      (μ := MeasureTheory.volume) (a := b) (b := x) (c := a)
      ((hf.add hg).intervalIntegrable b x) ((hf.add hg).intervalIntegrable x a)
    have hsum : (∫ u in b..x, f u) + ∫ u in x..a, g u ≤ ∫ u in b..a, f u + g u := by
      calc
        (∫ u in b..x, f u) + ∫ u in x..a, g u
            ≤ (∫ u in b..x, f u + g u) + ∫ u in x..a, f u + g u := add_le_add hfx_le hgx_le
        _ = ∫ u in b..a, f u + g u := hadd
    have habs_f : |∫ u in x..b, f u| = ∫ u in b..x, f u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hfx]
    have habs_g : |∫ u in a..x, g u| = ∫ u in x..a, g u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hgx]
    have habs_fg : |∫ u in a..b, f u + g u| = ∫ u in b..a, f u + g u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hfg]
    rwa [habs_f, habs_g, habs_fg]

/-! ### Difference of two time-ordered exponentials -/

/-- `cor:time_ordered_distance_bound` (difference representation): the difference of two
time-ordered exponentials equals the Duhamel integral
`∫ τ in t₁..t₂, exp_T(G,τ,t₂) · (H τ − G τ) · exp_T(H,t₁,τ)`.
The proof runs the `ode_solution_unique` argument on `D − X`, where
`D t = exp_T H t₁ t − exp_T G t₁ t` and
`X t = ∫ τ in t₁..t, exp_T G τ t · (H τ − G τ) · exp_T H t₁ τ`
solve the same inhomogeneous ODE `Y' = G·Y + (H−G)·exp_T H t₁` with the same initial value `0`. -/
lemma timeOrderedExp_sub (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂ =
      ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ := by
  let R : ℝ → 𝔸 := fun τ => (H τ - G τ) * timeOrderedExp H t₁ τ
  let D : ℝ → 𝔸 := fun t => timeOrderedExp H t₁ t - timeOrderedExp G t₁ t
  let X : ℝ → 𝔸 := fun t => ∫ τ in t₁..t, timeOrderedExp G τ t * R τ
  have hR : Continuous R := (hH.sub hG).mul (continuous_timeOrderedExp H hH t₁)
  have hD : ∀ t, HasDerivAt D (G t * D t + R t) t := by
    intro t
    have hsub := (timeOrderedExp_hasDerivAt H hH t₁ t).sub (timeOrderedExp_hasDerivAt G hG t₁ t)
    have hderiv_eq : (H t * timeOrderedExp H t₁ t) - (G t * timeOrderedExp G t₁ t)
        = G t * D t + R t := by
      dsimp [D, R]
      noncomm_ring
    simpa [D] using (hderiv_eq ▸ hsub)
  have hX : ∀ t, HasDerivAt X (G t * X t + R t) t := by
    intro t
    simpa [X, add_comm] using duhamelParticular_hasDerivAt G R hG hR t₁ t
  have hD0 : D t₁ = 0 := by
    dsimp [D]
    rw [timeOrderedExp_initial H t₁, timeOrderedExp_initial G t₁, sub_self]
  have hX0 : X t₁ = 0 := by
    dsimp [X]
    rw [intervalIntegral.integral_same]
  let d : ℝ → 𝔸 := fun s => D s - X s
  have hd : ∀ s, HasDerivAt d (G s * d s) s := by
    intro s
    have hsub := (hD s).sub (hX s)
    have hderiv_eq : (G s * D s + R s) - (G s * X s + R s) = G s * (D s - X s) := by
      noncomm_ring
    simpa [d] using (hderiv_eq ▸ hsub)
  have hd0 : d t₁ = 0 := by
    dsimp [d]
    rw [hD0, hX0, sub_self]
  have hzero : ∀ s, HasDerivAt (fun _ : ℝ => (0 : 𝔸)) (G s * (0 : 𝔸)) s := by
    intro s
    simpa using (hasDerivAt_const (x := s) (c := (0 : 𝔸)))
  have hd_eq_zero : d = fun _ : ℝ => (0 : 𝔸) := ode_solution_unique G hG hd hzero t₁ hd0
  have hDt : D t₂ = X t₂ := by
    have hds : d t₂ = 0 := congr_fun hd_eq_zero t₂
    dsimp [d] at hds
    exact sub_eq_zero.mp hds
  calc
    timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂
        = ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * R τ := by
            simpa [D, X] using hDt
    _ = ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ := by
            apply intervalIntegral.integral_congr
            intro τ _
            dsimp [R]
            rw [← mul_assoc]

/-! ### Distance bounds -/

omit [CompleteSpace 𝔸] in
/-- Pointwise bound for the integrand of the general distance bound: for `τ` in the unordered
interval between `t₁` and `t₂`,
`‖exp_T(G,τ,t₂) · (H τ − G τ) · exp_T(H,t₁,τ)‖ ≤ Real.exp |∫ ‖H‖+‖G‖| · ‖H τ − G τ‖`. -/
lemma norm_timeOrderedExp_sub_integrand_le [NormOneClass 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H)
    (hG : Continuous G) (t₁ t₂ τ : ℝ) (hτ : τ ∈ Set.uIcc t₁ t₂) :
    ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ ≤
      Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| * ‖H τ - G τ‖ := by
  calc
    ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖
        ≤ ‖timeOrderedExp G τ t₂ * (H τ - G τ)‖ * ‖timeOrderedExp H t₁ τ‖ := norm_mul_le _ _
    _ ≤ ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
        have hG_le := timeOrderedExp_norm_le G hG τ t₂
        have hH_le := timeOrderedExp_norm_le H hH t₁ τ
        have h1 : ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖
            ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖ := by
          have hleft : ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖
              ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ :=
            mul_le_mul_of_nonneg_right hG_le (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right hleft (norm_nonneg _)
        have h2 : Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖
            ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
          have hnonneg : 0 ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ :=
            mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hH_le hnonneg
        exact h1.trans h2
    _ ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| * ‖H τ - G τ‖ := by
        have hsum : |∫ u in τ..t₂, ‖G u‖| + |∫ u in t₁..τ, ‖H u‖|
            ≤ |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| := by
          have hle : |∫ u in τ..t₂, ‖G u‖| + |∫ u in t₁..τ, ‖H u‖|
              ≤ |∫ u in t₁..t₂, ‖G u‖ + ‖H u‖| :=
            abs_integral_add_le_abs_integral_of_mem_uIcc (f := fun u => ‖G u‖)
              (g := fun u => ‖H u‖) (hf := hG.norm) (hg := hH.norm)
              (hfnn := fun _ => norm_nonneg _) (hgnn := fun _ => norm_nonneg _)
              (a := t₁) (b := t₂) (x := τ) hτ
          have hcomm : (∫ u in t₁..t₂, ‖G u‖ + ‖H u‖) = ∫ u in t₁..t₂, ‖H u‖ + ‖G u‖ := by
            apply intervalIntegral.integral_congr
            intro u _
            simp [add_comm]
          simpa [hcomm] using hle
        have hcoef : Real.exp |∫ u in τ..t₂, ‖G u‖| * Real.exp |∫ u in t₁..τ, ‖H u‖|
            ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| := by
          calc
            Real.exp |∫ u in τ..t₂, ‖G u‖| * Real.exp |∫ u in t₁..τ, ‖H u‖|
                = Real.exp (|∫ u in τ..t₂, ‖G u‖| + |∫ u in t₁..τ, ‖H u‖|) :=
                    (Real.exp_add _ _).symm
            _ ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| := Real.exp_le_exp_of_le hsum
        calc
          Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * Real.exp |∫ u in t₁..τ, ‖H u‖|
              = (Real.exp |∫ u in τ..t₂, ‖G u‖| * Real.exp |∫ u in t₁..τ, ‖H u‖|) *
                  ‖H τ - G τ‖ := by
                  ring
          _ ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| * ‖H τ - G τ‖ :=
                  mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

/-- `cor:time_ordered_distance_bound` (item 1, general):
`‖exp_T(∫ H) − exp_T(∫ G)‖ ≤ |∫ ‖H−G‖| · Real.exp |∫ (‖H‖+‖G‖)|`. -/
lemma timeOrderedExp_dist_le [NormOneClass 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G)
    (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖ ≤
      |∫ τ in t₁..t₂, ‖H τ - G τ‖| * Real.exp (|∫ τ in t₁..t₂, ‖H τ‖ + ‖G τ‖|) := by
  let K : ℝ := Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖|
  calc
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖
        = ‖∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ := by
            rw [timeOrderedExp_sub H G hH hG t₁ t₂]
    _ ≤ |∫ τ in t₁..t₂, K * ‖H τ - G τ‖| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun τ => timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ)
              (g := fun τ => K * ‖H τ - G τ‖) ?_ ?_
            · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with τ hτ
              simpa [K] using
                (norm_timeOrderedExp_sub_integrand_le H G hH hG t₁ t₂ τ
                  (Set.uIoc_subset_uIcc hτ))
            · have hcont : Continuous fun τ => K * ‖H τ - G τ‖ := by
                dsimp [K]
                fun_prop
              exact hcont.intervalIntegrable t₁ t₂
    _ = |∫ τ in t₁..t₂, ‖H τ - G τ‖| * Real.exp (|∫ τ in t₁..t₂, ‖H τ‖ + ‖G τ‖|) := by
            dsimp [K]
            rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
              mul_comm]

/-- `cor:time_ordered_distance_bound` (item 2, skew): when `H` and `G` are pointwise
anti-Hermitian, `‖exp_T(∫ H) − exp_T(∫ G)‖ ≤ |∫ ‖H−G‖|`. -/
lemma timeOrderedExp_dist_le_of_skewAdjoint
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G)
    (hHskew : ∀ τ, star (H τ) = -H τ) (hGskew : ∀ τ, star (G τ) = -G τ) (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖ ≤ |∫ τ in t₁..t₂, ‖H τ - G τ‖| := by
  calc
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖
        = ‖∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ := by
            rw [timeOrderedExp_sub H G hH hG t₁ t₂]
    _ ≤ |∫ τ in t₁..t₂, ‖H τ - G τ‖| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun τ => timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ)
              (g := fun τ => ‖H τ - G τ‖) ?_ ?_
            · filter_upwards with τ
              calc
                ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖
                    ≤ ‖timeOrderedExp G τ t₂ * (H τ - G τ)‖ * ‖timeOrderedExp H t₁ τ‖ :=
                        norm_mul_le _ _
                _ ≤ ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖ :=
                        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
                _ = ‖H τ - G τ‖ := by
                        rw [timeOrderedExp_norm_eq_one_of_skewAdjoint G hG hGskew τ t₂,
                          timeOrderedExp_norm_eq_one_of_skewAdjoint H hH hHskew t₁ τ]
                        simp
            · exact (by fun_prop : Continuous fun τ => ‖H τ - G τ‖).intervalIntegrable t₁ t₂

end TrotterError
