/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CQM1.TrotterError.Calculus

/-!
# Interval integrals used in the Trotter error bounds

Generic interval-integral identities over `ℝ` used across the Trotter error theory
(arXiv:1912.08854): beta-type integrals, the substituted Taylor remainder integral, and the
FTC identity `∫₀¹ (1-u)^p = 1/(p+1)`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace MeasureTheory
open scoped algebraMap

/-- The beta-type integral `∫ u in uIoc 0 τ, |τ - u|^(q-1) du = |τ|^q / q`, for `1 ≤ q`. -/
lemma integral_abs_sub_pow_uIoc (q : ℕ) (τ : ℝ) (hq : 1 ≤ q) :
    (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1)) = |τ| ^ q / (q : ℝ) := by
  have h := integral_pow_abs_sub_uIoc (a := τ) (b := (0 : ℝ)) (n := q - 1)
  calc
    (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1))
        = (∫ u in Set.uIoc (τ : ℝ) 0, |u - τ| ^ (q - 1)) := by
            rw [Set.uIoc_comm (a := (0 : ℝ)) (b := τ)]
            exact setIntegral_congr_fun measurableSet_uIoc
              (fun u _ => congrArg (fun t : ℝ => t ^ (q - 1)) (abs_sub_comm τ u))
    _ = |τ| ^ q / (q : ℝ) := by
            rw [h]
            have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
              norm_cast
              rw [Nat.sub_add_cancel hq]
            rw [Nat.sub_add_cancel hq, hcast, abs_sub_comm (0 : ℝ) τ, sub_zero]

/-- `∫₀^τ |s|^(p-1)/(p-1)! ds = |τ|^p/p!` over the unordered interval, for `1 ≤ p`. -/
lemma integral_abs_pow_sub_div_factorial_uIoc (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) =
      |τ| ^ p / (Nat.factorial p : ℝ) := by
  have hfac : Nat.factorial p = p * Nat.factorial (p - 1) := by
    simpa [Nat.sub_add_cancel hp] using Nat.factorial_succ (p - 1)
  calc
    (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))
        = (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1)) / (Nat.factorial (p - 1) : ℝ) := by
            rw [integral_div]
    _ = (|τ| ^ p / (p : ℝ)) / (Nat.factorial (p - 1) : ℝ) := by
            have hp' : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
              rw [Nat.cast_sub hp]
              ring
            have hpow : (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1)) = |τ| ^ p / (p : ℝ) := by
              have h := integral_pow_abs_sub_uIoc (a := 0) (b := τ) (n := p - 1)
              rw [Nat.sub_add_cancel hp, hp'] at h
              simpa using h
            rw [hpow]
    _ = |τ| ^ p / (Nat.factorial p : ℝ) := by
            rw [hfac, Nat.cast_mul]
            field_simp

/-- `|∫₀^τ |s|^(p-1)/(p-1)! ds| = |τ|^p/p!` for `1 ≤ p`. -/
lemma abs_integral_abs_pow_div_factorial (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    |∫ s in 0..τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)|
      = |τ| ^ p / (Nat.factorial p : ℝ) := by
  rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
  have hnonneg : 0 ≤ (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) :=
    setIntegral_nonneg measurableSet_uIoc (fun s _ => by positivity)
  rw [abs_of_nonneg hnonneg, integral_abs_pow_sub_div_factorial_uIoc p τ hp]

/-- The standard Taylor remainder integral equals the paper's substituted form:
`∫₀^τ (τ-s)^n/n! • F s = ∫₀^τ F (τ-s) * (s^n/n!)`. -/
lemma integral_smul_eq_integral_mul_sub {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (F : ℝ → 𝔸) (n : ℕ) (τ : ℝ) :
    (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s) =
      ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
  calc
    (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s)
        = ∫ s in 0..τ, F s * (((τ - s) ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
            apply intervalIntegral.integral_congr_uIoo
            intro s hs
            exact smul_eq_mul_right (((τ - s) ^ n / (Nat.factorial n : ℝ))) (F s)
    _ = ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
            simpa using (intervalIntegral.integral_comp_sub_left (a := 0) (b := τ) (d := τ)
              (f := fun u => F (τ - u) * ((u ^ n / (Nat.factorial n : ℝ)) : 𝔸)))

/-- `∫₀¹ (1-u)^p du = 1/(p+1)`. -/
lemma intervalIntegral_one_sub_pow (p : ℕ) :
    (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p) = (1 : ℝ) / ((p + 1 : ℕ) : ℝ) := by
  calc
    (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p)
        = ∫ u in (0 : ℝ)..(1 : ℝ), u ^ p := by
            simpa using (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ p)
              (a := 0) (b := 1) (d := 1))
    _ = (1 : ℝ) / ((p + 1 : ℕ) : ℝ) := by
        have hp : (p + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero p
        rw [integral_pow, one_pow, zero_pow hp,
          show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 by norm_num]
        ring

end TrotterError
