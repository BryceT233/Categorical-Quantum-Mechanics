/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.ExpSMulConj

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Multi-layer conjugation: commutator expansion and remainder norm bounds

The multi-layer conjugation results for the Trotter error theory (arXiv:1912.08854): the
commutator expansion of `e^{τA_s} ⋯ e^{τA_1} B e^{-τA_1} ⋯ e^{-τA_s}` and the norm bounds
of its remainder (theory.tex:184-249).

## Main definitions

* `multiConj`: the multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`.
* `commutatorRemainderTerm`, `commutatorRemainder`: the operator-valued remainder `𝒞(τ)`.
* `conjCoeff`: the multinomial-weighted `τ^j` coefficient of the multi-layer expansion.

## Main results

* `norm_commutatorRemainder_le`: the spectral-norm bound of the commutator remainder for
  general operators (theory.tex:238-241).
* `norm_commutatorRemainder_le_of_skewAdjoint`: the bound for anti-Hermitian operators
  (theory.tex:242-244).

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace MeasureTheory Finset
open scoped ContDiff algebraMap

/-! ### Multi-layer conjugation `thm:comm_exp_conj` -/

/-- The multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`, where
`A ⟨0⟩` is innermost (the paper's `A₁`, applied first) and `A ⟨s-1⟩` is outermost (the paper's
`A_s`). -/
noncomputable def multiConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) : 𝔸 :=
  (List.ofFn (fun i : Fin s => exp (τ • A i))).reverse.prod * B *
    (List.ofFn (fun i : Fin s => exp (-τ • A i))).prod

/-- `A : Fin s → 𝔸` restricted to its first `m` entries, as `Fin m → 𝔸`. -/
def prefixRestrict {𝔸 : Type*} {s : ℕ} (A : Fin s → 𝔸) (m : ℕ) (hm : m ≤ s) : Fin m → 𝔸 :=
  fun i => A (Fin.castLE hm i)

/-- The single `(j, q)` summand of `commutatorRemainder`. -/
@[irreducible]
noncomputable def commutatorRemainderTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : 𝔸 :=
  ((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod *
    (∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
      expSMulConj (A j) (adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B) u) *
    ((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod

/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (prefixRestrict A (j + 1) …) q B = ad_{A_k}^{q_k} ⋯ ad_{A₁}^{q₁}(B)`. -/
noncomputable def commutatorRemainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸 :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    commutatorRemainderTerm A B τ j q

/-- The `τ^j` coefficient of the multi-layer conjugation, as the multinomial-weighted sum
`Σ_{q ∈ finAntidiagonal s j} (∏ i, q_i!⁻¹) • adSequence A q B`. -/
noncomputable def conjCoeff {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (j : ℕ) : 𝔸 :=
  ∑ q ∈ finAntidiagonal s j,
    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B

/-! ### Norm bounds for `thm:comm_exp_conj` -/

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

/-- The integral-norm estimation shared by the general and skew-adjoint remainder bounds: given a
nonnegative `C` and a pointwise bound for the smul'd conjugation, the beta integral yields
`C * |τ|^m / D * |τ|^q / q`. -/
lemma norm_integral_smul_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
  have hcont_g : Continuous (fun u : ℝ => C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) := by
    fun_prop
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖
        ≤ |∫ u in 0..τ, C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun u => (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
                (expSMulConj A X u))
              (g := fun u => C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with u hu
              exact hpoint u hu
            · exact hcont_g.intervalIntegrable 0 τ
    _ = C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
            rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
            have hnonneg : 0 ≤ (∫ u in Set.uIoc (0 : ℝ) τ,
                C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :=
              setIntegral_nonneg measurableSet_uIoc (fun u _ => by positivity)
            rw [abs_of_nonneg hnonneg]
            have hint : (∫ u in Set.uIoc (0 : ℝ) τ, (|τ - u| ^ (q - 1) * |τ| ^ m / D)) =
                (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
              calc
                (∫ u in Set.uIoc (0 : ℝ) τ, (|τ - u| ^ (q - 1) * |τ| ^ m / D))
                    = (∫ u in Set.uIoc (0 : ℝ) τ, (|τ| ^ m / D) * |τ - u| ^ (q - 1)) := by
                        apply setIntegral_congr_fun measurableSet_uIoc
                        intro u _
                        ring
                _ = (|τ| ^ m / D) * (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1)) := by
                        rw [integral_const_mul]
                _ = (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
                        rw [integral_abs_sub_pow_uIoc q τ hq]
            rw [integral_const_mul, hint]
            ring

/-- The norm of the integral in one remainder summand is bounded by `‖X‖ · |τ|^(q+m) / (q · D) ·
e^{2|τ|‖A‖}`. Here the integrand is `((τ-u)^(q-1) · τ^m / D) • (e^{uA} X e^{-uA})`. -/
lemma norm_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
  let C : ℝ := ‖X‖ * Real.exp (2 * |τ| * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg X) (Real.exp_nonneg _)
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by
    intro u hu
    have habs : |(τ - u) ^ (q - 1) * τ ^ m / D| = |τ - u| ^ (q - 1) * |τ| ^ m / D := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_nonneg (le_of_lt hD)]
    have hsmul : ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ =
        (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs]
    have hconj : ‖expSMulConj A X u‖ ≤ ‖X‖ * Real.exp (2 * |τ| * ‖A‖) := by
      refine (norm_expSMulConj_le A X u).trans ?_
      have harg : 2 * |u| * ‖A‖ ≤ 2 * |τ| * ‖A‖ := by
        have habs_u : |u| ≤ |τ| := by
          simpa using Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hu)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs_u (by norm_num))
          (norm_nonneg A)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg X)
    calc
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
          = (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := hsmul
      _ ≤ (|τ - u| ^ (q - 1) * |τ| ^ m / D) *
            (‖X‖ * Real.exp (2 * |τ| * ‖A‖)) := by gcongr
      _ = C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by dsimp [C]; ring
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖
        ≤ C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) :=
            norm_integral_smul_conj_le A X q m D hq hD τ C hC hpoint
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
            dsimp [C]
            have hq_ne : (q : ℝ) ≠ 0 := by positivity
            have hDne : D ≠ 0 := ne_of_gt hD
            field_simp [hq_ne, hDne]
            ring

/-- The product of the norms of exponentials `∏ᵢ ‖exp (tᵢ • Aᵢ)‖` is bounded by
`exp (Σᵢ |tᵢ| · ‖Aᵢ‖)`. -/
lemma norm_prod_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {ι : Type*} (l : List ι)
    (A : ι → 𝔸) (t : ι → ℝ) :
    (l.map (fun i => ‖exp (t i • A i)‖)).prod ≤
      Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
  calc
    (l.map (fun i => ‖exp (t i • A i)‖)).prod
        ≤ (l.map (fun i => Real.exp (|t i| * ‖A i‖))).prod := by
            have hle : ∀ i ∈ l, ‖exp (t i • A i)‖ ≤ Real.exp (|t i| * ‖A i‖) := by
              intro i _
              simpa [norm_smul] using norm_exp_le (t i • A i)
            have hnonneg : ∀ i ∈ l, 0 ≤ ‖exp (t i • A i)‖ := by
              intro i _
              exact norm_nonneg (exp (t i • A i))
            exact List.prod_map_le_prod_map₀
              (f := fun i => ‖exp (t i • A i)‖)
              (g := fun i => Real.exp (|t i| * ‖A i‖))
              (s := l) hnonneg hle
    _ = Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
            rw [Real.exp_list_sum, List.map_map]
            rfl

/-- The norm of the outer (left) exponential product of a remainder summand is bounded by
`exp (Σ_{i ≥ k} |τ| · ‖A i‖)`, expressed as a `List` sum over the dropped suffix. -/
lemma norm_ofFn_drop_reverse_prod_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  have h := norm_prod_exp_smul_le (l := (List.ofFn (fun i : Fin s => i)).drop k)
    (A := A) (t := fun _ : Fin s => τ)
  have hmap : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => ‖exp (τ • A i)‖) =
      (List.ofFn (fun i : Fin s => ‖exp (τ • A i)‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  have hmap' : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => |τ| * ‖A i‖) =
      (List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  rw [hmap, hmap'] at h
  calc
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖
        ≤ (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.map
            (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
    _ = (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map
            (fun x : 𝔸 => ‖x‖)).prod := by
            rw [List.map_reverse, List.prod_reverse]
    _ = ((List.ofFn (fun i : Fin s => ‖exp (τ • A i)‖)).drop k).prod := by
            rw [List.map_drop, ← List.ofFn_comp']
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := h

/-- The sum of the norms of `A j` and the strictly-larger layers is at most the total norm sum. -/
lemma norm_point_add_drop_sum_le {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) :
    ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤ ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hlen : (j : ℕ) < l.length := by simp [l]
  have hsplit : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := hlen)
    rw [← hcons, List.sum_cons]
    simp [l]
  calc
    ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum = (l.drop (j : ℕ)).sum := hsplit.symm
    _ ≤ l.sum := by
        have hnonneg : ∀ a ∈ l, (0 : ℝ) ≤ a := by
          intro a ha
          rcases (List.mem_ofFn' (fun i : Fin s => ‖A i‖) a).mp (by simpa [l] using ha) with ⟨i, hi⟩
          rw [← hi]
          exact norm_nonneg (A i)
        exact (List.drop_sublist (j : ℕ) l).sum_le_sum hnonneg
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-! ### Completion: layering the remainder sum into `alphaCommConj` -/

/-- The antidiagonal of `Fin (m + 1)` fibers over that of `Fin m` by the value at the last index,
via `Fin.snoc`. -/
lemma sum_finAntidiagonal_snoc {𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ)
    (G : (Fin (m + 1) → ℕ) → 𝔸) :
    (∑ q' ∈ finAntidiagonal (m + 1) n, G q') =
      ∑ k ∈ range (n + 1), ∑ q ∈ finAntidiagonal m (n - k), G (Fin.snoc q k) := by
  rw [sum_sigma']
  refine (sum_bij (fun x _ => Fin.snoc x.2 x.1) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [mem_finAntidiagonal, Fin.sum_snoc]
    have hx' : x.1 ∈ range (n + 1) ∧ x.2 ∈ finAntidiagonal m (n - x.1) :=
      mem_sigma.mp hx
    have hle : x.1 ≤ n := by simpa using mem_range.mp hx'.1
    have hsum : (∑ i : Fin m, x.2 i) = n - x.1 := by
      simpa using mem_finAntidiagonal.mp hx'.2
    rw [hsum, Nat.sub_add_cancel hle]
  · intro x₁ _ x₂ _ h
    obtain ⟨hq, hk⟩ := Fin.snoc_inj.mp h
    exact Sigma.ext hk (heq_of_eq hq)
  · intro q' hq'
    have hsum : (∑ i : Fin (m + 1), q' i) = n := mem_finAntidiagonal.mp hq'
    have hsplit : (∑ i : Fin m, q' i.castSucc) + q' (Fin.last m) = n := by
      simpa [Fin.sum_univ_castSucc] using hsum
    refine ⟨⟨q' (Fin.last m), Fin.init q'⟩, ?_, Fin.snoc_init_self q'⟩
    rw [mem_sigma]; constructor
    · rw [mem_range]
      have hle : q' (Fin.last m) ≤ n := by
        rw [← hsplit]
        exact Nat.le_add_left _ _
      exact Nat.lt_succ_of_le hle
    · rw [mem_finAntidiagonal]
      have hinit : (∑ i : Fin m, q' i.castSucc) = n - q' (Fin.last m) := by
        rw [← hsplit, Nat.add_sub_cancel_right]
      simpa [Fin.init] using hinit
  · tauto

/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖

/-- Appending a zero multiplicity does not change the multinomial coefficient. -/
lemma multinomial_snoc_zero {m : ℕ} (q : Fin m → ℕ) :
    Nat.multinomial (univ : Finset (Fin (m + 1))) (Fin.snoc q 0) =
      Nat.multinomial (univ : Finset (Fin m)) q := by
  simp only [Nat.multinomial]
  rw [Fin.sum_snoc, Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Reindexing `range (n+1)` minus `0` to `range n` by `k ↦ k + 1`. -/
lemma sum_range_filter_ne_zero {𝔸 : Type*} [AddCommMonoid 𝔸] (n : ℕ) (f : ℕ → 𝔸) :
    (∑ k ∈ (range (n + 1)).filter (fun k => k ≠ 0), f k) =
      ∑ k ∈ range n, f (k + 1) := by
  refine (sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [mem_filter, mem_range]
    exact ⟨Nat.add_lt_add_right (mem_range.mp hk) 1, Nat.succ_ne_zero k⟩
  · intro a _ b _ h
    exact Nat.succ.inj h
  · intro b hb
    rw [mem_filter, mem_range] at hb
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb.2
    refine ⟨b - 1, ?_, ?_⟩
    · rw [mem_range]; lia
    · lia
  · tauto

/-- The sum over `finAntidiagonal (s + 1) p` filtered by nonzero last entry equals the sum over the
`k ≥ 1` slices of the `Fin.snoc` fibration. -/
lemma sum_finAntidiagonal_filter_last_ne_zero {𝔸 : Type*} [AddCommMonoid 𝔸] (s p : ℕ)
    (G : (Fin (s + 1) → ℕ) → 𝔸) :
    (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), G q) =
      ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
        G (Fin.snoc q (k + 1)) := by
  rw [sum_filter, sum_finAntidiagonal_snoc]
  simp only [Fin.snoc_last]
  trans (∑ x ∈ (range (p + 1)).filter (fun x => x ≠ 0),
      ∑ q ∈ finAntidiagonal s (p - x), G (Fin.snoc q x))
  · rw [sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases h : x = 0 <;> simp [h]
  · rw [sum_range_filter_ne_zero]

/-- Splitting `alphaCommConj` over `Fin (s + 1)` into the inner `Fin s` part (zero on the last
layer) and the part with nonzero outermost multiplicity. -/
lemma alphaCommConj_snoc_split {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    alphaCommConj A B p = alphaCommConj (fun i : Fin s => A i.castSucc) B p +
      ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
        (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖ := by
  calc
    alphaCommConj A B p
        = ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              rfl
    _ = ∑ k ∈ range (p + 1), ∑ q ∈ finAntidiagonal s (p - k),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q k) : ℝ) *
              ‖adSequence A (Fin.snoc q k) B‖ := by
              rw [sum_finAntidiagonal_snoc]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          (∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
              ‖adSequence A (Fin.snoc q 0) B‖) := by
              rw [sum_range_succ', Nat.sub_zero]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          alphaCommConj (fun i : Fin s => A i.castSucc) B p := by
              rw [show (∑ q ∈ finAntidiagonal s p,
                (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
                  ‖adSequence A (Fin.snoc q 0) B‖) =
                alphaCommConj (fun i : Fin s => A i.castSucc) B p from by
                simp [alphaCommConj, adSequence_snoc_zero, multinomial_snoc_zero]]
    _ = alphaCommConj (fun i : Fin s => A i.castSucc) B p +
          (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) := by
              rw [add_comm]
    _ = alphaCommConj (fun i : Fin s => A i.castSucc) B p +
          (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖) := by
              rw [sum_finAntidiagonal_filter_last_ne_zero]

/-- The layer sum is bounded by `alphaCommConj`: collapsing each `(j, q)` into the antidiagonal of
`Fin s` by padding with zeros (theory.tex:198-214, the `Σ_k Σ_q → Σ_{q₁+⋯+q_s=p}` step). -/
lemma layerSum_le_alphaCommConj {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    layerSum A B p ≤ alphaCommConj A B p := by
  induction s with
  | zero =>
      simp only [layerSum, alphaCommConj]
      exact sum_nonneg (fun q _ => mul_nonneg (by positivity) (norm_nonneg _))
  | succ s ih =>
      rw [layerSum, Fin.sum_univ_castSucc]
      have hsplit : (∑ j : Fin s,
          (fun j : Fin (s + 1) =>
            ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
              (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
                ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖) j.castSucc)
          = layerSum (fun i : Fin s => A i.castSucc) B p := rfl
      rw [hsplit, alphaCommConj_snoc_split A B p]
      exact add_le_add (ih (fun i : Fin s => A i.castSucc)) (le_refl _)

/-- The scalar coefficient in one remainder summand equals `multinomial(q) · |τ|^p / p!`. -/
lemma coeff_eq_multinomial_div_factorial {j p : ℕ} (q : Fin (j + 1) → ℕ) (τ : ℝ)
    (hsum : (∑ i : Fin (j + 1), q i) = p) (hlast : 1 ≤ q (Fin.last j)) :
    |τ| ^ p / ((q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
  have hfac : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) =
      (Nat.factorial (q (Fin.last j)) : ℝ) := by
    rw [← Nat.cast_mul]
    congr 1
    have h := Nat.factorial_succ (q (Fin.last j) - 1)
    rw [Nat.sub_add_cancel hlast] at h
    exact h.symm
  have hden : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        (∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      ∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ) := by
    rw [hfac, Fin.prod_univ_castSucc, mul_comm]
  have hms : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) *
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) = (Nat.factorial p : ℝ) := by
    have h' := Nat.multinomial_spec (s := (univ : Finset (Fin (j + 1)))) (f := q)
    rw [hsum] at h'
    exact_mod_cast h'
  rw [hden]
  have hfac_p : (Nat.factorial p : ℝ) ≠ 0 := by positivity
  have hprod : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => by positivity)
  field_simp [hfac_p, hprod]
  rw [← hms]
  ring

/-- Combining the exponential factors of one remainder summand into the global exponential. -/
lemma exp_bound_combine {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
      Real.exp (2 * |τ| * ‖A j‖) *
        Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) ≤
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  have hS : ((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum =
      |τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum := by
    rw [List.ofFn_comp' (f := fun i : Fin s => ‖A i‖) (g := fun x : ℝ => |τ| * x),
      ← List.map_drop, List.sum_map_mul_left, List.map_id']
  calc
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
        Real.exp (2 * |τ| * ‖A j‖) *
          Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)
        = Real.exp (2 * (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum +
              |τ| * ‖A j‖)) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
    _ ≤ Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              apply Real.exp_le_exp.mpr
              rw [hS]
              have hle : ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤
                  ∑ i : Fin s, ‖A i‖ := norm_point_add_drop_sum_le A j
              have h1 : 2 * (|τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum +
                    |τ| * ‖A j‖) = 2 * |τ| * (‖A j‖ +
                      ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum) := by ring
              rw [h1]
              simpa [mul_assoc] using (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hle (abs_nonneg τ)) (by norm_num : 0 ≤ (2 : ℝ)))

/-- The norm of the outer (right) exponential product is bounded by the same suffix exponential. -/
lemma norm_ofFn_drop_prod_exp_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  have h := norm_prod_exp_smul_le (l := (List.ofFn (fun i : Fin s => i)).drop k)
    (A := A) (t := fun _ : Fin s => -τ)
  have hmap : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => ‖exp (-τ • A i)‖) =
      (List.ofFn (fun i : Fin s => ‖exp (-τ • A i)‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  have hmap' : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => |-τ| * ‖A i‖) =
      (List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
    simp [abs_neg]
  rw [hmap, hmap'] at h
  calc
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖
        ≤ (((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).map
            (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
    _ = ((List.ofFn (fun i : Fin s => ‖exp (-τ • A i)‖)).drop k).prod := by
            rw [List.map_drop, ← List.ofFn_comp']
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := h

/-- The norm bound of a single remainder summand. -/
lemma norm_commutatorRemainderTerm_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (j : Fin s) (q : Fin (j + 1) → ℕ) (hq : q ∈ finAntidiagonal (j + 1) p)
    (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  let X : 𝔸 := adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hD : 0 < D := by dsimp [D]; positivity
  have houterL : ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_reverse_prod_exp_le A (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_prod_exp_le A (j + 1) τ
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (2 * |τ| * ‖A j‖) := by
        simpa [D] using norm_conj_smul_integral_le (A j) X (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D (by lia) hD τ
  have hcoeff : |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      calc
        q (Fin.last j) + (∑ i : Fin j, q i.castSucc)
            = (∑ i : Fin j, q i.castSucc) + q (Fin.last j) := by rw [add_comm]
        _ = ∑ i : Fin (j + 1), q i := (Fin.sum_univ_castSucc (f := q)).symm
        _ = p := hsum
    rw [hqsum]
    dsimp [D]
    rw [← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q τ hsum (by lia)
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
              ((q (Fin.last j) : ℝ) * D) *
              Real.exp (2 * |τ| * ‖A j‖)) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
          (Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            Real.exp (2 * |τ| * ‖A j‖) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)) := by ring
    _ ≤ ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ)) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              rw [hcoeff]; gcongr
              exact exp_bound_combine A j τ
    _ = ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              dsimp [X]; ring

/-- The spectral-norm bound of the commutator remainder (theory.tex:238-241, general operators). -/
theorem norm_commutatorRemainder_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    ‖commutatorRemainder A B p τ‖ ≤ alphaCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  rw [commutatorRemainder]
  have h1 : ‖∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖commutatorRemainderTerm A B τ j q‖ := by
    apply norm_sum_le_of_le
    intros; exact norm_sum_le ..
  have h2 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
    exact sum_le_sum (fun j _ => sum_le_sum (fun q hq =>
      norm_commutatorRemainderTerm_le A B p τ j q (mem_filter.mp hq).1 (mem_filter.mp hq).2))
  have h3 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) ≤
      alphaCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
        Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
    have hlayer : layerSum A B p ≤ alphaCommConj A B p := layerSum_le_alphaCommConj A B p
    have hnonneg : 0 ≤ |τ| ^ p / (Nat.factorial p : ℝ) *
        Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by positivity
    have hmain : (∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
        (fun q => q (Fin.last j) ≠ 0),
          (‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ)) *
            (|τ| ^ p / (Nat.factorial p : ℝ) *
              Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖))) ≤
        alphaCommConj A B p * (|τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖)) := by
      simp_rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [layerSum, mul_comm] using hlayer) hnonneg
    simpa [div_eq_mul_inv, mul_assoc] using hmain
  exact h1.trans (h2.trans h3)

/-- The product of the norms of skew-exponentials `exp (τ • A i)` is at most `1`. -/
lemma norm_ofFn_drop_prod_le_one_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (hskew : ∀ i, star (A i) = -A i)
    (k : ℕ) (τ : ℝ) :
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod ≤ 1 := by
  have hle : ∀ i ∈ (List.ofFn (fun i : Fin s => i)).drop k, ‖exp (τ • A i)‖ ≤ 1 := by
    intro i _
    exact (norm_exp_smul_of_skewAdjoint (hskew i) τ).le
  have hnonneg : ∀ i ∈ (List.ofFn (fun i : Fin s => i)).drop k, 0 ≤ ‖exp (τ • A i)‖ := by
    intro i _
    exact norm_nonneg (exp (τ • A i))
  have h := List.prod_map_le_prod_map₀
    (f := fun i : Fin s => ‖exp (τ • A i)‖)
    (g := fun _ : Fin s => (1 : ℝ))
    (s := (List.ofFn (fun i : Fin s => i)).drop k) hnonneg hle
  calc
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod
        = (((List.ofFn (fun i : Fin s => i)).drop k).map
            (fun i : Fin s => ‖exp (τ • A i)‖)).prod := by
              rw [List.map_drop, List.map_ofFn, List.map_drop, List.map_ofFn]
              rfl
    _ ≤ (((List.ofFn (fun i : Fin s => i)).drop k).map (fun _ : Fin s => (1 : ℝ))).prod := h
    _ = 1 := by
      rw [List.map_drop, List.map_ofFn]
      apply List.prod_eq_one
      intro x hx
      have hx' : x ∈ List.ofFn (fun _ : Fin s => (1 : ℝ)) :=
        (List.drop_sublist k (List.ofFn (fun _ : Fin s => (1 : ℝ)))).subset hx
      rcases (List.mem_ofFn' (fun _ : Fin s => (1 : ℝ)) x).mp hx' with ⟨i, hi⟩
      rw [← hi]

/-- The norm of the integral in one skew-adjoint remainder summand is bounded by
`‖X‖ · |τ|^(q+m) / (q · D)` (no exponential factor). -/
lemma norm_conj_smul_integral_le_of_skew {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (hskew : star A = -A) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  let C : ℝ := ‖X‖
  have hC : 0 ≤ C := norm_nonneg X
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by
    intro u hu
    have habs : |(τ - u) ^ (q - 1) * τ ^ m / D| = |τ - u| ^ (q - 1) * |τ| ^ m / D := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_nonneg (le_of_lt hD)]
    have hsmul : ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ =
        (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs]
    have hconj : ‖expSMulConj A X u‖ ≤ ‖X‖ := by
      unfold expSMulConj
      have h1 : ‖exp (u • A) * X‖ ≤ ‖X‖ := by
        simpa [norm_exp_smul_of_skewAdjoint hskew u] using norm_mul_le (exp (u • A)) X
      have h2 : ‖exp (-u • A)‖ ≤ 1 := (norm_exp_smul_of_skewAdjoint hskew (-u)).le
      calc
        ‖exp (u • A) * X * exp (-u • A)‖
            ≤ ‖exp (u • A) * X‖ * ‖exp (-u • A)‖ := norm_mul_le _ _
        _ ≤ ‖X‖ * 1 := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg X)
        _ = ‖X‖ := by rw [mul_one]
    calc
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
          = (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := hsmul
      _ ≤ (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖X‖ := by gcongr
      _ = C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by dsimp [C]; ring
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) :=
            norm_integral_smul_conj_le A X q m D hq hD τ C hC hpoint
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) := by
            dsimp [C]
            have hq_ne : (q : ℝ) ≠ 0 := by positivity
            have hDne : D ≠ 0 := ne_of_gt hD
            field_simp [hq_ne, hDne]
            ring

/-- The norm bound of a single remainder summand in the skew-adjoint case. -/
lemma norm_commutatorRemainderTerm_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ)
    (τ : ℝ) (hskew : ∀ i, star (A i) = -A i) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) := by
  let X : 𝔸 := adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hlast_le : 1 ≤ q (Fin.last j) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have houterL :
      ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤ 1 := by
    calc
      ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖
          ≤ (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.map
              (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
      _ = (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).map
              (fun x : 𝔸 => ‖x‖)).prod := by rw [List.map_reverse, List.prod_reverse]
      _ ≤ 1 := norm_ofFn_drop_prod_le_one_of_skewAdjoint A hskew (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤ 1 := by
    calc
      ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖
          ≤ (((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).map
              (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
      _ ≤ 1 := by simpa using norm_ofFn_drop_prod_le_one_of_skewAdjoint A hskew (j + 1) (-τ)
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) := by
        simpa [D] using norm_conj_smul_integral_le_of_skew (A j) X (hskew j) (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D hlast_le hD τ
  have hcoeff : |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      calc
        q (Fin.last j) + (∑ i : Fin j, q i.castSucc)
            = (∑ i : Fin j, q i.castSucc) + q (Fin.last j) := by rw [add_comm]
        _ = ∑ i : Fin (j + 1), q i := (Fin.sum_univ_castSucc (f := q)).symm
        _ = p := hsum
    rw [hqsum]
    dsimp [D]
    rw [← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q τ hsum hlast_le
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
          ((q (Fin.last j) : ℝ) * D)) * 1 := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D)) := by ring
    _ = ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) := by
              rw [hcoeff]; dsimp [X]
              ring

/-- The spectral-norm bound of the commutator remainder for anti-Hermitian operators
(theory.tex:242-244). -/
theorem norm_commutatorRemainder_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (hskew : ∀ i, star (A i) = -A i) :
    ‖commutatorRemainder A B p τ‖ ≤ alphaCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) := by
  rw [commutatorRemainder]
  have h1 : ‖∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖commutatorRemainderTerm A B τ j q‖ := by
    apply norm_sum_le_of_le
    intros; exact norm_sum_le ..
  have h2 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) := by
    exact sum_le_sum (fun j _ => sum_le_sum (fun q hq =>
      norm_commutatorRemainderTerm_le_of_skewAdjoint A B p τ hskew j q
        (mem_filter.mp hq).1 (mem_filter.mp hq).2))
  have h3 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) ≤
      alphaCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) := by
    have hlayer : layerSum A B p ≤ alphaCommConj A B p := layerSum_le_alphaCommConj A B p
    have hnonneg : 0 ≤ |τ| ^ p / (Nat.factorial p : ℝ) := by positivity
    have hmain : (∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
        (fun q => q (Fin.last j) ≠ 0),
          (‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ)) *
            (|τ| ^ p / (Nat.factorial p : ℝ))) ≤
        alphaCommConj A B p * (|τ| ^ p / (Nat.factorial p : ℝ)) := by
      simp_rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [layerSum, mul_comm] using hlayer) hnonneg
    simpa [div_eq_mul_inv, mul_assoc] using hmain
  exact h1.trans (h2.trans h3)

/-! ### The expansion theorem `commutatorExpansion_conj` -/

/-- Peeling the outermost layer off `multiConj`:
`multiConj A B τ = e^{τA⟨s⟩} (multiConj (A∘castSucc) B τ) e^{-τA⟨s⟩}`. -/
lemma multiConj_succ {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) :
    multiConj A B τ =
      expSMulConj (A (Fin.last s)) (multiConj (fun i : Fin s => A i.castSucc) B τ) τ := by
  unfold multiConj expSMulConj
  have hleft : (List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).reverse.prod =
      exp (τ • A (Fin.last s)) *
        (List.ofFn (fun i : Fin s => exp (τ • A i.castSucc))).reverse.prod := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.reverse_concat', List.prod_cons]
  have hright : (List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).prod =
      (List.ofFn (fun i : Fin s => exp (-τ • A i.castSucc))).prod *
        exp (-τ • A (Fin.last s)) := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.prod_append, List.prod_singleton]
  rw [hleft, hright]
  noncomm_ring

/-- The product of factorials of a snoc'd multiplicity factors into the outer `j!` and the inner
product. -/
lemma factorial_prod_snoc {s : ℕ} (q : Fin s → ℕ) (j : ℕ) :
    (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ)) =
      (∏ i : Fin s, (Nat.factorial (q i) : ℝ)) * (Nat.factorial j : ℝ) := by
  rw [Fin.prod_univ_castSucc (fun i : Fin (s + 1) =>
    (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The inverse factorial coefficient of a snoc'd multiplicity factors as `j!⁻¹ · ∏qᵢ!⁻¹`. -/
lemma factorial_inv_snoc {s : ℕ} (q : Fin s → ℕ) (j : ℕ) :
    (Nat.factorial j : ℝ)⁻¹ * (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ =
      (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ := by
  rw [← mul_inv,
    mul_comm (Nat.factorial j : ℝ) (∏ i : Fin s, (Nat.factorial (q i) : ℝ)),
    factorial_prod_snoc]

/-- One summand of the `(s+1)`-layer coefficient, rewritten through the outermost `ad` layer. -/
lemma conjCoeff_snoc_summand {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (q : Fin s → ℕ) (j : ℕ) :
    (Nat.factorial j : ℝ)⁻¹ •
        adPow (A (Fin.last s)) j
          ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
            adSequence (fun i : Fin s => A i.castSucc) q B) =
      ((∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ : ℝ) •
        adSequence A (Fin.snoc q j) B := by
  rw [adPow_smul, ← mul_smul, adSequence_snoc, factorial_inv_snoc]

/-- The `m`-th coefficient of the `(s+1)`-layer expansion is obtained from the inner `s`-layer
coefficients by one further `ad` layer. -/
lemma conjCoeff_succ {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (m : ℕ) :
    conjCoeff A B m = ∑ j ∈ range (m + 1),
      ((Nat.factorial j : ℝ)⁻¹ : ℝ) •
        adPow (A (Fin.last s)) j (conjCoeff (fun i : Fin s => A i.castSucc) B (m - j)) := by
  rw [conjCoeff, sum_finAntidiagonal_snoc s m
    (fun q' => ((∏ i : Fin (s + 1), (Nat.factorial (q' i) : ℝ))⁻¹ : ℝ) • adSequence A q' B)]
  apply sum_congr rfl
  intro j _
  rw [conjCoeff]
  symm
  have hsum : adPow (A (Fin.last s)) j (∑ q ∈ finAntidiagonal s (m - j),
      (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
        adSequence (fun i : Fin s => A i.castSucc) q B) =
      ∑ q ∈ finAntidiagonal s (m - j),
        adPow (A (Fin.last s)) j
          ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
            adSequence (fun i : Fin s => A i.castSucc) q B) :=
    map_sum (adPowLin (A (Fin.last s)) j).toAddMonoidHom
      (fun q => (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
        adSequence (fun i : Fin s => A i.castSucc) q B)
      (finAntidiagonal s (m - j))
  rw [hsum, smul_sum]
  apply sum_congr rfl
  intro q _
  exact conjCoeff_snoc_summand A B q j

/-- Restricting to the full length is the identity. -/
lemma prefixRestrict_self {𝔸 : Type*} {s : ℕ} (A : Fin s → 𝔸) (hm : s ≤ s) :
    prefixRestrict A s hm = A := by
  funext i; simp [prefixRestrict]

end TrotterError
