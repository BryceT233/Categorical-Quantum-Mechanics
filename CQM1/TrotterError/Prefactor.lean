/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.ExpSMulConj
public import CQM1.TrotterError.ProductFormula
public import CQM1.TrotterError.Suzuki

import CQM1.TrotterError.TimeOrderedExp

/-!
# Error bounds with small prefactors (§5.1)

Tight-constant Trotter error bounds for the first-order Lie-Trotter and second-order Suzuki
formulas, following `papers/prefactor.tex` `sec:prefactor_pf12`.

The paper states these in terms of a Hermitian `H = Σ_γ H_γ` and the real-time evolution
`e^{-itH}`. Here, following the anti-Hermitian-generator convention of the surrounding theory,
we work with anti-Hermitian generators `K_γ` (`star (K γ) = -(K γ)`) and the evolution
`exp (t • Σ_γ K γ)`; the paper's `H_γ ↔ K_γ = -i H_γ`, `e^{-itH_γ} ↔ exp (t • K_γ)`, and
`[H_γ, H_γ'] ↔ ⁅K_γ, K_γ'⁆` (equal norm), so the constants `t²/2`, `t³/12`, `t³/24` are unchanged.

## Main results

* `firstOrder_twoTerm`, `secondOrder_twoTerm`: the two-summand (Γ = 2) tight bounds.
* `firstOrder_bound`, `secondOrder_bound`: the general-Γ bounds via triangle-inequality
  telescoping (prefactor.tex:45–50 and 105–114).

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace Finset LieAlgebra MeasureTheory
open scoped BigOperators algebraMap

/- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A`, matching `Commutator.lean`. -/
attribute [local instance] LieRing.ofAssociativeRing

/-! ### Two-summand Duhamel identity -/

/-- The two-summand additive error identity (`prefactor.tex:16`, in anti-Hermitian-generator
form): for `S₁(t) = e^{tB} e^{tA}` and `H = A + B`,
`S₁(t) - e^{tH} = ∫₀ᵗ e^{(t-τ)H} (e^{τB} A e^{-τB} - A) e^{τB} e^{τA} dτ`. -/
lemma exp_mul_exp_sub_exp_add_eq_integral {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (t : ℝ) :
    exp (t • B) * exp (t • A) - exp (t • (A + B)) =
      ∫ τ in 0..t,
        exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A) := by
  have hH : Continuous (fun _ : ℝ => A + B) := continuous_const
  have hR : Continuous (fun τ : ℝ => (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A)) := by
    unfold expSMulConj
    fun_prop
  have hU : ∀ s : ℝ, HasDerivAt (fun r : ℝ => exp (r • B) * exp (r • A))
      ((A + B) * (exp (s • B) * exp (s • A)) +
        (expSMulConj B A s - A) * exp (s • B) * exp (s • A)) s := by
    intro s
    have hderiv : HasDerivAt (fun r : ℝ => exp (r • B) * exp (r • A))
        ((B * exp (s • B)) * exp (s • A) + exp (s • B) * (A * exp (s • A))) s :=
      (hasDerivAt_exp_smul_const' B s).mul (hasDerivAt_exp_smul_const' A s)
    have hexp : exp ((-s) • B) * exp (s • B) = 1 := by
      simpa [neg_smul] using (exp_neg_mul_self (s • B) : exp (-(s • B)) * exp (s • B) = 1)
    have hkey : (B * exp (s • B)) * exp (s • A) + exp (s • B) * (A * exp (s • A)) =
        (A + B) * (exp (s • B) * exp (s • A)) +
          (expSMulConj B A s - A) * exp (s • B) * exp (s • A) := by
      unfold expSMulConj
      have hmid : exp (s • B) * A * exp ((-s) • B) * exp (s • B) * exp (s • A) =
          exp (s • B) * A * exp (s • A) := by
        calc
          exp (s • B) * A * exp ((-s) • B) * exp (s • B) * exp (s • A)
              = exp (s • B) * A * (exp ((-s) • B) * exp (s • B)) * exp (s • A) := by noncomm_ring
          _ = exp (s • B) * A * exp (s • A) := by rw [hexp, mul_one]
      calc
        (B * exp (s • B)) * exp (s • A) + exp (s • B) * (A * exp (s • A))
            = (A + B) * (exp (s • B) * exp (s • A)) +
                exp (s • B) * A * exp (s • A) - A * exp (s • B) * exp (s • A) := by noncomm_ring
        _ = (A + B) * (exp (s • B) * exp (s • A)) +
              exp (s • B) * A * exp ((-s) • B) * exp (s • B) * exp (s • A)
                - A * exp (s • B) * exp (s • A) := by rw [← hmid]
        _ = (A + B) * (exp (s • B) * exp (s • A)) +
              (exp (s • B) * A * exp ((-s) • B) - A) *
                exp (s • B) * exp (s • A) := by noncomm_ring
    simpa [hkey] using hderiv
  have hU0 : exp ((0 : ℝ) • B) * exp ((0 : ℝ) • A) = 1 := by simp
  have hduhamel := timeOrderedExp_duhamel (fun _ : ℝ => A + B)
    (fun τ : ℝ => (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A)) hH hR
    (U := fun τ => exp (τ • B) * exp (τ • A)) 1 hU hU0 t
  calc
    exp (t • B) * exp (t • A) - exp (t • (A + B))
        = (timeOrderedExp (fun _ : ℝ => A + B) 0 t * 1 +
            ∫ τ in 0..t, timeOrderedExp (fun _ : ℝ => A + B) τ t *
              ((expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A))) - exp (t • (A + B)) := by
            rw [hduhamel]
    _ = ∫ τ in 0..t,
          exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A) := by
        rw [timeOrderedExp_const (A + B) 0 t]
        simp only [sub_zero, mul_one]
        abel_nf
        refine intervalIntegral.integral_congr_uIoo ?_
        intro τ hτ
        simp only [mul_assoc]
        rw [timeOrderedExp_const (A + B) τ t]
        simp only [smul_add, Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]

/-! ### First-order two-summand bound -/

/-- The two-summand first-order Lie-Trotter bound (`prefactor.tex:29`, anti-Hermitian-generator
form): for anti-Hermitian `A, B`, `‖e^{tB} e^{tA} - e^{t(A+B)}‖ ≤ (t²/2) · ‖⁅B, A⁆‖`. -/
theorem firstOrder_twoTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) :
    ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • B) * exp (t • A) - exp (t • (A + B))‖ ≤ (t ^ 2 / 2) * ‖⁅B, A⁆‖ := by
  have hAB : star (A + B) = -(A + B) := by
    rw [star_add, hA, hB]
    abel
  intro t ht
  calc
    ‖exp (t • B) * exp (t • A) - exp (t • (A + B))‖
        = ‖∫ τ in 0..t,
            exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A)‖ := by
            rw [exp_mul_exp_sub_exp_add_eq_integral A B t]
    _ ≤ ∫ τ in 0..t, ‖⁅B, A⁆‖ * τ := by
        have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
            ‖exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A)‖ ≤
              ‖⁅B, A⁆‖ * τ := by
          intro τ hτ
          have hτpos : 0 ≤ τ := le_of_lt hτ.1
          have hunitAB : ‖exp ((t - τ) • (A + B))‖ = 1 :=
            norm_exp_smul_of_skewAdjoint hAB (t - τ)
          have hunitB : ‖exp (τ • B)‖ = 1 := norm_exp_smul_of_skewAdjoint hB τ
          have hunitA : ‖exp (τ • A)‖ = 1 := norm_exp_smul_of_skewAdjoint hA τ
          have hconj : ‖expSMulConj B A τ - A‖ ≤ ‖⁅B, A⁆‖ * τ := by
            have hFTC := expSMulConj_sub_eq_integral B A τ
            rw [hFTC]
            have hpoint' : ∀ s ∈ Set.Ioc (0 : ℝ) τ, ‖expSMulConj B ⁅B, A⁆ s‖ ≤ ‖⁅B, A⁆‖ := by
              intro s hs
              exact norm_expSMulConj_le_of_skewAdjoint B ⁅B, A⁆ hB s
            calc
              ‖∫ s in 0..τ, expSMulConj B ⁅B, A⁆ s‖
                  ≤ ∫ s in 0..τ, ‖⁅B, A⁆‖ := by
                      exact intervalIntegral.norm_integral_le_of_norm_le hτpos
                        (by filter_upwards with s hs; exact hpoint' s hs)
                        (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 τ)
              _ = ‖⁅B, A⁆‖ * τ := by
                  rw [intervalIntegral.integral_const]
                  ring
          calc
            ‖exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A)‖
                ≤ ‖exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B)‖ *
                    ‖exp (τ • A)‖ := norm_mul_le _ _
            _ ≤ ‖exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A)‖ * ‖exp (τ • B)‖ *
                  ‖exp (τ • A)‖ :=
                  mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
            _ ≤ ‖exp ((t - τ) • (A + B))‖ * ‖expSMulConj B A τ - A‖ * ‖exp (τ • B)‖ *
                  ‖exp (τ • A)‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
            _ = ‖expSMulConj B A τ - A‖ := by
                rw [hunitAB, hunitB, hunitA]
                ring
            _ ≤ ‖⁅B, A⁆‖ * τ := hconj
        have hcont_g : Continuous (fun τ : ℝ => ‖⁅B, A⁆‖ * τ) :=
          continuous_const.mul continuous_id
        exact intervalIntegral.norm_integral_le_of_norm_le ht
          (by filter_upwards with τ hτ; exact hpoint τ hτ)
          (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    _ = ‖⁅B, A⁆‖ * (t ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul]
        have hpow : (∫ τ in 0..t, τ) = t ^ 2 / 2 := by
          calc
            ∫ τ in 0..t, τ = ∫ τ in 0..t, τ ^ 1 := by
              apply intervalIntegral.integral_congr_uIoo
              intro x hx
              simp
            _ = t ^ 2 / 2 := by
              rw [integral_pow]
              ring
        rw [hpow]
    _ = (t ^ 2 / 2) * ‖⁅B, A⁆‖ := by ring

/-! ### General-Γ first-order bound -/

/-- `upperSum K j` is the sum of `K γ` over `γ > j` (the paper's `Σ_{γ₂ = γ₁+1}^Γ H_{γ₂}`). -/
abbrev upperSum {𝔸 : Type*} [AddCommMonoid 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (j : Fin Γ) :
    𝔸 :=
  Finset.sum ((Finset.univ : Finset (Fin Γ)).filter (fun γ => j < γ)) (fun γ => K γ)

/-- The `0`-upper sum is the whole tail: `upperSum K 0 = Σ_{i} K i.succ`. -/
lemma upperSum_zero_eq {𝔸 : Type*} [AddCommMonoid 𝔸] {n : ℕ} (K : Fin (n + 1) → 𝔸) :
    upperSum K 0 = ∑ i : Fin n, K i.succ := by
  unfold upperSum
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp

/-- `upperSum (K ∘ Fin.succ) i = upperSum K i.succ`. -/
lemma upperSum_succ {𝔸 : Type*} [AddCommMonoid 𝔸] {n : ℕ} (K : Fin (n + 1) → 𝔸) (i : Fin n) :
    upperSum (fun j : Fin n => K j.succ) i = upperSum K i.succ := by
  unfold upperSum
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

/-- The Lie-Trotter product of anti-Hermitian factors has norm at most `1` (each factor is
unitary). -/
lemma norm_lieTrotter_le_one_of_skew {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) (t : ℝ) :
    ‖lieTrotter K t‖ ≤ 1 := by
  induction Γ with
  | zero => simp [lieTrotter]
  | succ n ih =>
      rw [lieTrotter]
      calc
        ‖lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0)‖
            ≤ ‖lieTrotter (fun i : Fin n => K i.succ) t‖ * ‖exp (t • K 0)‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (ih (fun i : Fin n => K i.succ) (fun i => h i.succ))
            (le_of_eq (norm_exp_smul_of_skewAdjoint (h 0) t)) (norm_nonneg _) (by positivity)
        _ = 1 := by ring

/-- `prop:pf1_bound` (prefactor.tex:45–50, anti-Hermitian-generator form): the tight first-order
Lie-Trotter bound for general `Γ`. -/
theorem firstOrder_bound {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] (Γ : ℕ) (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) :
    ∀ t : ℝ, 0 ≤ t →
      ‖lieTrotter K t - exp (t • ∑ γ, K γ)‖ ≤
        (t ^ 2 / 2) * ∑ γ₁ : Fin Γ, ‖⁅upperSum K γ₁, K γ₁⁆‖ := by
  induction Γ with
  | zero =>
      intro t ht
      simp [lieTrotter, upperSum]
  | succ n ih =>
      intro t ht
      have hSkew : star (∑ i : Fin n, K i.succ) = -(∑ i : Fin n, K i.succ) :=
        sum_skewAdjoint (fun i : Fin n => K i.succ) (fun i => h i.succ)
      have htwo := firstOrder_twoTerm (K 0) (∑ i : Fin n, K i.succ) (h 0) hSkew t ht
      have hih := ih (fun i : Fin n => K i.succ) (fun i => h i.succ) t ht
      have hstep : ‖lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0) -
          exp (t • (K 0 + ∑ i : Fin n, K i.succ))‖ ≤
          ‖lieTrotter (fun i : Fin n => K i.succ) t - exp (t • ∑ i : Fin n, K i.succ)‖ +
            (t ^ 2 / 2) * ‖⁅∑ i : Fin n, K i.succ, K 0⁆‖ := by
        let D : 𝔸 := lieTrotter (fun i : Fin n => K i.succ) t - exp (t • ∑ i : Fin n, K i.succ)
        have hdecomp : lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0) -
            exp (t • (K 0 + ∑ i : Fin n, K i.succ)) =
          D * exp (t • K 0) +
            (exp (t • ∑ i : Fin n, K i.succ) * exp (t • K 0) -
              exp (t • (K 0 + ∑ i : Fin n, K i.succ))) := by
          dsimp [D]
          noncomm_ring
        rw [hdecomp]
        calc
          ‖D * exp (t • K 0) +
            (exp (t • ∑ i : Fin n, K i.succ) * exp (t • K 0) -
              exp (t • (K 0 + ∑ i : Fin n, K i.succ)))‖
              ≤ ‖D * exp (t • K 0)‖
                + ‖exp (t • ∑ i : Fin n, K i.succ) * exp (t • K 0) -
                    exp (t • (K 0 + ∑ i : Fin n, K i.succ))‖ := norm_add_le _ _
          _ ≤ ‖D‖ + (t ^ 2 / 2) * ‖⁅∑ i : Fin n, K i.succ, K 0⁆‖ := by
              have hfirst : ‖D * exp (t • K 0)‖ ≤ ‖D‖ := by
                calc
                  ‖D * exp (t • K 0)‖ ≤ ‖D‖ * ‖exp (t • K 0)‖ := norm_mul_le _ _
                  _ = ‖D‖ := by rw [norm_exp_smul_of_skewAdjoint (h 0) t, mul_one]
              exact add_le_add hfirst htwo
      calc
        ‖lieTrotter K t - exp (t • ∑ γ : Fin (n + 1), K γ)‖
            = ‖lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0) -
                exp (t • (K 0 + ∑ i : Fin n, K i.succ))‖ := by
                rw [lieTrotter, Fin.sum_univ_succ]
        _ ≤ ‖lieTrotter (fun i : Fin n => K i.succ) t - exp (t • ∑ i : Fin n, K i.succ)‖ +
              (t ^ 2 / 2) * ‖⁅∑ i : Fin n, K i.succ, K 0⁆‖ := hstep
        _ ≤ (t ^ 2 / 2) * (∑ i : Fin n, ‖⁅upperSum (fun i : Fin n => K i.succ) i, K i.succ⁆‖) +
              (t ^ 2 / 2) * ‖⁅∑ i : Fin n, K i.succ, K 0⁆‖ :=
              add_le_add hih (le_of_eq (by ring))
        _ = (t ^ 2 / 2) * ∑ γ₁ : Fin (n + 1), ‖⁅upperSum K γ₁, K γ₁⁆‖ := by
              rw [Fin.sum_univ_succ, upperSum_zero_eq K, mul_add, add_comm]
              congr 1
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              rw [upperSum_succ K i]

/-! ### Second-order two-summand bound -/

/-- The second-order kernel `𝒯₂(τ)` of prefactor.tex:60, anti-Hermitian-generator form:
`e^{τB} (A/2) e^{-τB} - A/2 - e^{-(τ/2)A} B e^{(τ/2)A} + B`. -/
noncomputable def secondOrderKernel {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A B : 𝔸) (τ : ℝ) : 𝔸 :=
  expSMulConj B ((1 / 2 : ℝ) • A) τ - (1 / 2 : ℝ) • A -
    expSMulConj A B (-(τ / 2)) + B

/-- The second-order Duhamel identity (prefactor.tex:52–57, anti-Hermitian-generator form). -/
lemma secondOrder_sub_eq_integral {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (t : ℝ) :
    exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B)) =
      ∫ τ in 0..t, exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ *
        exp (τ • B) * exp ((τ / 2) • A) := by
  let Aₕ : 𝔸 := (1 / 2 : ℝ) • A
  have hhalf : ∀ τ : ℝ, exp ((τ / 2) • A) = exp (τ • Aₕ) := by
    intro τ
    apply congrArg exp
    dsimp [Aₕ]
    rw [← mul_smul]
    congr 1
    ring
  have hH : Continuous (fun _ : ℝ => A + B) := continuous_const
  have hR : Continuous (fun τ : ℝ =>
      exp (τ • Aₕ) * secondOrderKernel A B τ * exp (τ • B) * exp (τ • Aₕ)) := by
    unfold secondOrderKernel expSMulConj
    fun_prop
  have hU : ∀ s : ℝ, HasDerivAt (fun r : ℝ => exp (r • Aₕ) * exp (r • B) * exp (r • Aₕ))
      ((A + B) * (exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)) +
        exp (s • Aₕ) * secondOrderKernel A B s * exp (s • B) * exp (s • Aₕ)) s := by
    intro s
    have hderiv : HasDerivAt (fun r : ℝ => exp (r • Aₕ) * exp (r • B) * exp (r • Aₕ))
        (((Aₕ * exp (s • Aₕ)) * exp (s • B) + exp (s • Aₕ) * (B * exp (s • B))) * exp (s • Aₕ) +
          (exp (s • Aₕ) * exp (s • B)) * (Aₕ * exp (s • Aₕ))) s :=
      (hasDerivAt_exp_smul_const' Aₕ s).mul (hasDerivAt_exp_smul_const' B s) |>.mul
        (hasDerivAt_exp_smul_const' Aₕ s)
    have hcA : Commute (exp (s • Aₕ)) Aₕ := (exp_smul_comm Aₕ s).symm
    have hBneg : exp ((-s) • B) * exp (s • B) = 1 := by
      simpa [neg_smul] using (exp_neg_mul_self (s • B) : exp (-(s • B)) * exp (s • B) = 1)
    have hApos : exp (s • Aₕ) * exp ((-s) • Aₕ) = 1 := by
      simpa [neg_smul] using (exp_mul_neg_self (s • Aₕ) : exp (s • Aₕ) * exp (-(s • Aₕ)) = 1)
    have hT₂ : exp (s • Aₕ) * secondOrderKernel A B s * exp (s • B) * exp (s • Aₕ) =
        exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ) * Aₕ
          - Aₕ * exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)
          - B * exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)
          + exp (s • Aₕ) * B * exp (s • B) * exp (s • Aₕ) := by
      dsimp [secondOrderKernel, expSMulConj]
      have hAₕ : (1 / 2 : ℝ) • A = Aₕ := rfl
      have hpos : (s / 2) • A = s • Aₕ := by
        dsimp [Aₕ]
        rw [← mul_smul]
        congr 1
        ring
      have hneg : (-(s / 2)) • A = (-s) • Aₕ := by
        dsimp [Aₕ]
        rw [← mul_smul]
        congr 1
        ring
      rw [neg_neg, hAₕ, hpos, hneg]
      calc
        exp (s • Aₕ) * (exp (s • B) * Aₕ * exp ((-s) • B) - Aₕ -
            exp ((-s) • Aₕ) * B * exp (s • Aₕ) + B) * exp (s • B) * exp (s • Aₕ)
            = exp (s • Aₕ) * exp (s • B) * Aₕ * (exp ((-s) • B) * exp (s • B)) * exp (s • Aₕ)
              - exp (s • Aₕ) * Aₕ * exp (s • B) * exp (s • Aₕ)
              - (exp (s • Aₕ) * exp ((-s) • Aₕ)) * B * exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)
              + exp (s • Aₕ) * B * exp (s • B) * exp (s • Aₕ) := by noncomm_ring
        _ = exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ) * Aₕ
              - Aₕ * exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)
              - B * exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)
              + exp (s • Aₕ) * B * exp (s • B) * exp (s • Aₕ) := by
            rw [hBneg, hApos]
            noncomm_ring [hcA.eq]
    have hkey : ((Aₕ * exp (s • Aₕ)) * exp (s • B) + exp (s • Aₕ) * (B * exp (s • B))) *
          exp (s • Aₕ) + (exp (s • Aₕ) * exp (s • B)) * (Aₕ * exp (s • Aₕ)) =
        (A + B) * (exp (s • Aₕ) * exp (s • B) * exp (s • Aₕ)) +
          exp (s • Aₕ) * secondOrderKernel A B s * exp (s • B) * exp (s • Aₕ) := by
      rw [hT₂]
      have hAeq : A = (2 : ℝ) • Aₕ := by
        apply Eq.symm
        rw [show Aₕ = (1 / 2 : ℝ) • A by rfl, smul_smul]
        norm_num
      noncomm_ring [hcA.eq, hAeq]
      rw [two_smul]
      abel
    simpa [hkey] using hderiv
  have hU0 : exp ((0 : ℝ) • Aₕ) * exp ((0 : ℝ) • B) * exp ((0 : ℝ) • Aₕ) = 1 := by simp
  have hduhamel := timeOrderedExp_duhamel (fun _ : ℝ => A + B)
    (fun τ : ℝ => exp (τ • Aₕ) * secondOrderKernel A B τ * exp (τ • B) * exp (τ • Aₕ)) hH hR
    (U := fun τ => exp (τ • Aₕ) * exp (τ • B) * exp (τ • Aₕ)) 1 hU hU0 t
  calc
    exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))
        = exp (t • Aₕ) * exp (t • B) * exp (t • Aₕ) - exp (t • (A + B)) := by
            rw [hhalf t]
    _ = (timeOrderedExp (fun _ : ℝ => A + B) 0 t * 1 +
            ∫ τ in 0..t, timeOrderedExp (fun _ : ℝ => A + B) τ t *
              (exp (τ • Aₕ) * secondOrderKernel A B τ * exp (τ • B) * exp (τ • Aₕ))) -
          exp (t • (A + B)) := by rw [hduhamel]
    _ = ∫ τ in 0..t, exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ *
          exp (τ • B) * exp ((τ / 2) • A) := by
        rw [timeOrderedExp_const (A + B) 0 t]
        simp only [sub_zero, mul_one]
        abel_nf
        refine intervalIntegral.integral_congr_uIoo ?_
        intro τ hτ
        simp only [mul_assoc]
        rw [timeOrderedExp_const (A + B) τ t, hhalf τ]
        simp only [smul_add, Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]

/-! ### Taylor expansion of the second-order kernel -/

/-- The linear term of the first conjugation: `⁅B, (1/2)•A⁆ * τ = (τ/2) • ⁅B, A⁆`. -/
private lemma lie_smul_half_mul_coe {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A B : 𝔸) (τ : ℝ) :
    ⁅B, (1 / 2 : ℝ) • A⁆ * (τ : 𝔸) = (τ / 2) • ⁅B, A⁆ := by
  rw [lie_smul, smul_mul_cast (1 / 2 : ℝ) τ ⁅B, A⁆]
  congr 1
  ring

/-- The linear term of the second conjugation: `⁅A, B⁆ * (-(τ/2)) = (τ/2) • ⁅B, A⁆`. -/
private lemma lie_mul_neg_half_coe {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A B : 𝔸) (τ : ℝ) :
    ⁅A, B⁆ * ((-(τ / 2) : ℝ) : 𝔸) = (τ / 2) • ⁅B, A⁆ := by
  calc
    ⁅A, B⁆ * ((-(τ / 2) : ℝ) : 𝔸) = (-(τ / 2)) • ⁅A, B⁆ :=
      (smul_eq_mul_right (-(τ / 2)) ⁅A, B⁆).symm
    _ = (-(τ / 2)) • (-⁅B, A⁆) := by
        rw [(lie_skew A B).symm]
    _ = (τ / 2) • ⁅B, A⁆ := by
        rw [smul_neg, neg_smul, neg_neg]

/-- The `p = 2` specialization of the single-layer Taylor expansion:
`expSMulConj A X τ = X + ⁅A, X⁆ * τ + ∫₀^τ expSMulConj A (adPow A 2 X) (τ-s) * s`. -/
lemma expSMulConj_taylor_two {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A X : 𝔸) (τ : ℝ) :
    expSMulConj A X τ = X + ⁅A, X⁆ * (τ : 𝔸) +
      ∫ s in 0..τ, expSMulConj A (adPow A 2 X) (τ - s) * (s : 𝔸) := by
  rw [expSMulConj_taylor A X 2 τ (by norm_num)]
  congr 1
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [adPow, Nat.factorial, pow_succ, pow_zero]
  · apply intervalIntegral.integral_congr_uIoo
    intro s _
    norm_num

/-- The second-order kernel is the difference of two `p = 2` Taylor remainders
(prefactor.tex:63–68, anti-Hermitian-generator form). -/
lemma secondOrderKernel_eq_remainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A B : 𝔸) (τ : ℝ) :
    secondOrderKernel A B τ =
      (∫ s in 0..τ, expSMulConj B ((1 / 2 : ℝ) • adPow B 2 A) (τ - s) * (s : 𝔸))
      - (∫ s in 0..-(τ / 2), expSMulConj A (adPow A 2 B) ((-(τ / 2)) - s) * (s : 𝔸)) := by
  dsimp [secondOrderKernel]
  rw [expSMulConj_taylor_two B ((1 / 2 : ℝ) • A) τ, expSMulConj_taylor_two A B (-(τ / 2)),
    lie_smul_half_mul_coe A B τ, lie_mul_neg_half_coe A B τ, (adPow B 2).map_smul (1 / 2 : ℝ) A]
  noncomm_ring

/-! ### Norm bound of the second-order kernel -/

/-- Norm bound for a single-layer `p = 2` Taylor remainder under an anti-Hermitian generator:
`‖∫₀^τ expSMulConj A Y (τ-s) * s‖ ≤ ‖Y‖ · |τ|²/2`. -/
lemma norm_expSMulConj_taylor_remainder_le_of_skew {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A Y : 𝔸) (hA : star A = -A) (τ : ℝ) :
    ‖∫ s in 0..τ, expSMulConj A Y (τ - s) * (s : 𝔸)‖ ≤ ‖Y‖ * (|τ| ^ 2 / 2) := by
  have hpoint : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
      ‖expSMulConj A Y (τ - s) * (s : 𝔸)‖ ≤ ‖Y‖ * |s| := by
    intro s hs
    calc
      ‖expSMulConj A Y (τ - s) * (s : 𝔸)‖ = ‖s • expSMulConj A Y (τ - s)‖ := by
          rw [smul_eq_mul_right s (expSMulConj A Y (τ - s))]
      _ = |s| * ‖expSMulConj A Y (τ - s)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * ‖Y‖ := mul_le_mul_of_nonneg_left
          (norm_expSMulConj_le_of_skewAdjoint A Y hA (τ - s)) (abs_nonneg s)
      _ = ‖Y‖ * |s| := by ring
  have hcont_g : Continuous (fun s : ℝ => ‖Y‖ * |s|) := by fun_prop
  calc
    ‖∫ s in 0..τ, expSMulConj A Y (τ - s) * (s : 𝔸)‖
        ≤ |∫ s in 0..τ, (‖Y‖ * |s|)| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun s => expSMulConj A Y (τ - s) * (s : 𝔸))
              (g := fun s => ‖Y‖ * |s|) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with s hs
              exact hpoint s hs
            · exact hcont_g.intervalIntegrable 0 τ
    _ = ‖Y‖ * (|τ| ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (norm_nonneg Y)]
        have hbeta : |∫ s in 0..τ, (|s|)| = |τ| ^ 2 / 2 := by
          have h := abs_integral_abs_pow_div_factorial 2 τ (by norm_num : 1 ≤ 2)
          norm_num at h ⊢
          exact h
        rw [hbeta]

/-- The second-order kernel bound (prefactor.tex:82–85, anti-Hermitian-generator form):
`‖𝒯₂(τ)‖ ≤ (τ²/4) ‖adPow B 2 A‖ + (τ²/8) ‖adPow A 2 B‖`. -/
lemma norm_secondOrderKernel_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) (τ : ℝ) :
    ‖secondOrderKernel A B τ‖ ≤ (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖ := by
  rw [secondOrderKernel_eq_remainder A B τ]
  calc
    ‖(∫ s in 0..τ, expSMulConj B ((1 / 2 : ℝ) • adPow B 2 A) (τ - s) * (s : 𝔸))
      - (∫ s in 0..-(τ / 2), expSMulConj A (adPow A 2 B) ((-(τ / 2)) - s) * (s : 𝔸))‖
        ≤ ‖∫ s in 0..τ, expSMulConj B ((1 / 2 : ℝ) • adPow B 2 A) (τ - s) * (s : 𝔸)‖
          + ‖∫ s in 0..-(τ / 2), expSMulConj A (adPow A 2 B) ((-(τ / 2)) - s) * (s : 𝔸)‖ :=
            norm_sub_le _ _
    _ ≤ ‖(1 / 2 : ℝ) • adPow B 2 A‖ * (|τ| ^ 2 / 2) + ‖adPow A 2 B‖ * (|-(τ / 2)| ^ 2 / 2) :=
            add_le_add
              (norm_expSMulConj_taylor_remainder_le_of_skew B ((1 / 2 : ℝ) • adPow B 2 A) hB τ)
              (norm_expSMulConj_taylor_remainder_le_of_skew A (adPow A 2 B) hA (-(τ / 2)))
    _ = (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num)]
        have hneg : |-(τ / 2)| ^ 2 = τ ^ 2 / 4 := by
          rw [abs_neg, abs_div, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num), div_pow, sq_abs]
          norm_num
        rw [hneg, sq_abs]
        ring

/-! ### Second-order two-summand bound -/

/-- The two-summand second-order Suzuki bound (prefactor.tex:82–85, anti-Hermitian-generator
form): `‖e^{(t/2)A} e^{tB} e^{(t/2)A} - e^{t(A+B)}‖ ≤ (t³/12)‖⁅B,⁅B,A⁆⁆‖ + (t³/24)‖⁅A,⁅A,B⁆⁆‖`. -/
theorem secondOrder_twoTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) :
    ∀ t : ℝ, 0 ≤ t →
      ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖ ≤
        (t ^ 3 / 12) * ‖adPow B 2 A‖ + (t ^ 3 / 24) * ‖adPow A 2 B‖ := by
  have hAB : star (A + B) = -(A + B) := by
    rw [star_add, hA, hB]
    abel
  intro t ht
  have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      ‖exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ *
          exp (τ • B) * exp ((τ / 2) • A)‖
        ≤ (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖ := by
    intro τ hτ
    have hunitAB : ‖exp ((t - τ) • (A + B))‖ = 1 := norm_exp_smul_of_skewAdjoint hAB (t - τ)
    have hunitA : ‖exp ((τ / 2) • A)‖ = 1 := norm_exp_smul_of_skewAdjoint hA (τ / 2)
    have hunitB : ‖exp (τ • B)‖ = 1 := norm_exp_smul_of_skewAdjoint hB τ
    calc
      ‖exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ *
          exp (τ • B) * exp ((τ / 2) • A)‖
          ≤ ‖exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ * exp (τ • B)‖ *
              ‖exp ((τ / 2) • A)‖ := norm_mul_le _ _
      _ ≤ ‖exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ‖ * ‖exp (τ • B)‖ *
              ‖exp ((τ / 2) • A)‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖exp ((t - τ) • (A + B)) * exp ((τ / 2) • A)‖ *
            ‖secondOrderKernel A B τ‖ * ‖exp (τ • B)‖ * ‖exp ((τ / 2) • A)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖exp ((t - τ) • (A + B))‖ * ‖exp ((τ / 2) • A)‖ *
            ‖secondOrderKernel A B τ‖ * ‖exp (τ • B)‖ * ‖exp ((τ / 2) • A)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _))
                (norm_nonneg _)
      _ = ‖secondOrderKernel A B τ‖ := by
              simp only [hunitAB, hunitA, hunitB, mul_one, one_mul]
      _ ≤ (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖ :=
              norm_secondOrderKernel_le A B hA hB τ
  have hcont_g : Continuous
      (fun τ : ℝ => (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖) := by
    fun_prop
  calc
    ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖
        = ‖∫ τ in 0..t, exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ *
            exp (τ • B) * exp ((τ / 2) • A)‖ := by
            rw [secondOrder_sub_eq_integral A B t]
    _ ≤ ∫ τ in 0..t, (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖ := by
        exact intervalIntegral.norm_integral_le_of_norm_le ht
          (by filter_upwards with τ hτ; exact hpoint τ hτ)
          (hcont_g.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    _ = (t ^ 3 / 12) * ‖adPow B 2 A‖ + (t ^ 3 / 24) * ‖adPow A 2 B‖ := by
        have hf : IntervalIntegrable (fun τ : ℝ => τ ^ 2 / 4 * ‖adPow B 2 A‖)
            MeasureTheory.volume 0 t :=
          (by fun_prop : Continuous (fun τ : ℝ => τ ^ 2 / 4 * ‖adPow B 2 A‖)).intervalIntegrable
            0 t
        have hg : IntervalIntegrable (fun τ : ℝ => τ ^ 2 / 8 * ‖adPow A 2 B‖)
            MeasureTheory.volume 0 t :=
          (by fun_prop : Continuous (fun τ : ℝ => τ ^ 2 / 8 * ‖adPow A 2 B‖)).intervalIntegrable
            0 t
        rw [intervalIntegral.integral_add hf hg,
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        have hpow2 : (∫ τ in 0..t, τ ^ 2) = t ^ 3 / 3 := by
          rw [integral_pow]
          ring
        have hpow4 : (∫ τ in 0..t, τ ^ 2 / 4) = t ^ 3 / 12 := by
          calc
            (∫ τ in 0..t, τ ^ 2 / 4) = (∫ τ in 0..t, (1 / 4 : ℝ) * τ ^ 2) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ
                ring
            _ = (1 / 4 : ℝ) * (∫ τ in 0..t, τ ^ 2) := by rw [intervalIntegral.integral_const_mul]
            _ = (1 / 4 : ℝ) * (t ^ 3 / 3) := by rw [hpow2]
            _ = t ^ 3 / 12 := by ring
        have hpow8 : (∫ τ in 0..t, τ ^ 2 / 8) = t ^ 3 / 24 := by
          calc
            (∫ τ in 0..t, τ ^ 2 / 8) = (∫ τ in 0..t, (1 / 8 : ℝ) * τ ^ 2) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ
                ring
            _ = (1 / 8 : ℝ) * (∫ τ in 0..t, τ ^ 2) := by rw [intervalIntegral.integral_const_mul]
            _ = (1 / 8 : ℝ) * (t ^ 3 / 3) := by rw [hpow2]
            _ = t ^ 3 / 24 := by ring
        rw [hpow4, hpow8]

/-! ### General-Γ second-order bound -/

/-- The second-order Suzuki product of anti-Hermitian factors has norm at most `1`. -/
lemma norm_suzuki2_le_one_of_skew {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) (t : ℝ) :
    ‖suzuki2 K t‖ ≤ 1 := by
  induction Γ with
  | zero => simp [suzuki2]
  | succ n ih =>
      rw [suzuki2]
      calc
        ‖exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0)‖
            ≤ ‖exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t‖ *
                ‖exp ((t / 2) • K 0)‖ :=
                norm_mul_le _ _
        _ ≤ ‖exp ((t / 2) • K 0)‖ * ‖suzuki2 (fun i : Fin n => K i.succ) t‖ *
              ‖exp ((t / 2) • K 0)‖ :=
                mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul
              (le_of_eq (norm_exp_smul_of_skewAdjoint (h 0) (t / 2)))
              (ih (fun i : Fin n => K i.succ) (fun i => h i.succ)) (norm_nonneg _) (by positivity))
            (le_of_eq (norm_exp_smul_of_skewAdjoint (h 0) (t / 2))) (norm_nonneg _) (by positivity)
        _ = 1 := by ring

/-- `prop:pf2_bound` (prefactor.tex:105–114, anti-Hermitian-generator form): the tight second-order
Suzuki bound for general `Γ`. -/
theorem secondOrder_bound {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (Γ : ℕ) (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) :
    ∀ t : ℝ, 0 ≤ t →
      ‖suzuki2 K t - exp (t • ∑ γ, K γ)‖ ≤
        (t ^ 3 / 12) * ∑ γ₁ : Fin Γ, ‖adPow (upperSum K γ₁) 2 (K γ₁)‖
        + (t ^ 3 / 24) * ∑ γ₁ : Fin Γ, ‖adPow (K γ₁) 2 (upperSum K γ₁)‖ := by
  induction Γ with
  | zero =>
      intro t ht
      simp [suzuki2, upperSum]
  | succ n ih =>
      intro t ht
      have hT : star (∑ i : Fin n, K i.succ) = -(∑ i : Fin n, K i.succ) :=
        sum_skewAdjoint (fun i : Fin n => K i.succ) (fun i => h i.succ)
      have htwo := secondOrder_twoTerm (K 0) (∑ i : Fin n, K i.succ) (h 0) hT t ht
      have hih := ih (fun i : Fin n => K i.succ) (fun i => h i.succ) t ht
      have hstep :
          ‖exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0) -
              exp (t • (K 0 + ∑ i : Fin n, K i.succ))‖ ≤
          ‖suzuki2 (fun i : Fin n => K i.succ) t - exp (t • ∑ i : Fin n, K i.succ)‖ +
            (t ^ 3 / 12) * ‖adPow (∑ i : Fin n, K i.succ) 2 (K 0)‖
            + (t ^ 3 / 24) * ‖adPow (K 0) 2 (∑ i : Fin n, K i.succ)‖ := by
        let D : 𝔸 := suzuki2 (fun i : Fin n => K i.succ) t - exp (t • ∑ i : Fin n, K i.succ)
        have hdecomp :
            exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0) -
              exp (t • (K 0 + ∑ i : Fin n, K i.succ)) =
          exp ((t / 2) • K 0) * D * exp ((t / 2) • K 0) +
            (exp ((t / 2) • K 0) * exp (t • ∑ i : Fin n, K i.succ) * exp ((t / 2) • K 0)
              - exp (t • (K 0 + ∑ i : Fin n, K i.succ))) := by
          dsimp [D]
          noncomm_ring
        rw [hdecomp]
        calc
          ‖exp ((t / 2) • K 0) * D * exp ((t / 2) • K 0) +
            (exp ((t / 2) • K 0) * exp (t • ∑ i : Fin n, K i.succ) * exp ((t / 2) • K 0)
              - exp (t • (K 0 + ∑ i : Fin n, K i.succ)))‖
              ≤ ‖exp ((t / 2) • K 0) * D * exp ((t / 2) • K 0)‖
                + ‖exp ((t / 2) • K 0) * exp (t • ∑ i : Fin n, K i.succ) * exp ((t / 2) • K 0)
                    - exp (t • (K 0 + ∑ i : Fin n, K i.succ))‖ := norm_add_le _ _
          _ ≤ ‖D‖ + (t ^ 3 / 12) * ‖adPow (∑ i : Fin n, K i.succ) 2 (K 0)‖
              + (t ^ 3 / 24) * ‖adPow (K 0) 2 (∑ i : Fin n, K i.succ)‖ := by
              have hfirst : ‖exp ((t / 2) • K 0) * D * exp ((t / 2) • K 0)‖ ≤ ‖D‖ := by
                calc
                  ‖exp ((t / 2) • K 0) * D * exp ((t / 2) • K 0)‖
                      ≤ ‖exp ((t / 2) • K 0) * D‖ * ‖exp ((t / 2) • K 0)‖ := norm_mul_le _ _
                  _ ≤ ‖exp ((t / 2) • K 0)‖ * ‖D‖ * ‖exp ((t / 2) • K 0)‖ :=
                      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
                  _ = ‖D‖ := by rw [norm_exp_smul_of_skewAdjoint (h 0) (t / 2), one_mul, mul_one]
              linarith [hfirst, htwo]
      calc
        ‖suzuki2 K t - exp (t • ∑ γ : Fin (n + 1), K γ)‖
            = ‖exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0) -
                exp (t • (K 0 + ∑ i : Fin n, K i.succ))‖ := by
                rw [suzuki2, Fin.sum_univ_succ]
        _ ≤ ‖suzuki2 (fun i : Fin n => K i.succ) t - exp (t • ∑ i : Fin n, K i.succ)‖ +
              (t ^ 3 / 12) * ‖adPow (∑ i : Fin n, K i.succ) 2 (K 0)‖
              + (t ^ 3 / 24) * ‖adPow (K 0) 2 (∑ i : Fin n, K i.succ)‖ := hstep
        _ ≤ (t ^ 3 / 12) *
              (∑ i : Fin n, ‖adPow (upperSum (fun i : Fin n => K i.succ) i) 2 (K i.succ)‖)
              + (t ^ 3 / 24) *
              (∑ i : Fin n, ‖adPow (K i.succ) 2 (upperSum (fun i : Fin n => K i.succ) i)‖)
              + (t ^ 3 / 12) * ‖adPow (∑ i : Fin n, K i.succ) 2 (K 0)‖
              + (t ^ 3 / 24) * ‖adPow (K 0) 2 (∑ i : Fin n, K i.succ)‖ := by
              linarith [hih]
        _ = (t ^ 3 / 12) * ∑ γ₁ : Fin (n + 1), ‖adPow (upperSum K γ₁) 2 (K γ₁)‖
              + (t ^ 3 / 24) * ∑ γ₁ : Fin (n + 1), ‖adPow (K γ₁) 2 (upperSum K γ₁)‖ := by
              rw [Fin.sum_univ_succ, Fin.sum_univ_succ, upperSum_zero_eq K]
              simp_rw [upperSum_succ K]
              ring

end TrotterError
