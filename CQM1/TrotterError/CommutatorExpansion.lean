/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.ExpSMulConj
import CQM1.TrotterError.ListProd
import CQM1.TrotterError.Integrals

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
lemma norm_point_add_drop_sum_le {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) :
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

/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.2)) q B‖

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
              ‖adSequence A q' B‖ := rfl
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
          (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖) := by
              rw [add_comm, sum_finAntidiagonal_filter_last_ne_zero]

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
  rw [← hms]; ring

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
              congr 1; ring
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
    rw [hqsum, ← mul_assoc]
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
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) :=
    sum_le_sum (fun j _ => sum_le_sum (fun q hq =>
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
  have hC : 0 ≤ ‖X‖ := norm_nonneg X
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ ‖X‖ * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by
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
      _ = ‖X‖ * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by ring
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ ‖X‖ * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) :=
            norm_integral_smul_conj_le A X q m D hq hD τ ‖X‖ hC hpoint
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) := by
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
    rw [hqsum, ← mul_assoc]
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
            (Nat.factorial p : ℝ) := by rw [hcoeff]; dsimp [X]; ring

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
  intro j _; rw [conjCoeff]; symm
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

/-! ### Auxiliary algebra and reindexing lemmas for `commutatorExpansion_conj` -/

/-- Conjugation commutes with right multiplication by a central scalar:
`expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸)`. -/
lemma expSMulConj_mul_cast {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (r : ℝ) (τ : ℝ) :
    expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸) := by
  rw [← smul_eq_mul_right r X]
  calc
    expSMulConj A (r • X) τ = r • expSMulConj A X τ := (expSMulConjLin A τ).map_smul' r X
    _ = expSMulConj A X τ * (r : 𝔸) := smul_eq_mul_right r (expSMulConj A X τ)

/-- `expSMulConj A · τ` distributes over a finite sum. -/
lemma expSMulConj_map_sum {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : 𝔸) (τ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) :
    expSMulConj A (∑ x ∈ s, f x) τ = ∑ x ∈ s, expSMulConj A (f x) τ := by
  change (expSMulConjLin A τ).toAddMonoidHom (∑ x ∈ s, f x) =
    ∑ x ∈ s, (expSMulConjLin A τ).toAddMonoidHom (f x)
  exact map_sum (expSMulConjLin A τ).toAddMonoidHom f s

/-- Right multiplication by a central scalar `(c : 𝔸)` commutes with the interval integral. -/
lemma integral_mul_cast {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (F : ℝ → 𝔸) (c : ℝ)
    (τ : ℝ) :
    (∫ u in 0..τ, F u) * (c : 𝔸) = ∫ u in 0..τ, F u * (c : 𝔸) := by
  rw [← smul_eq_mul_right c (∫ u in 0..τ, F u)]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_uIoo
  intro u _
  exact smul_eq_mul_right c (F u)

/-- The single-layer Taylor remainder term, weighted by `d⁻¹` and `τ^j`, rewritten as the
`commutatorRemainderTerm` integrand `((τ-u)^k * τ^j / (k! * d)) • expSMulConj A X u`. -/
lemma expSMulConj_taylor_remainder_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (k j : ℕ) (d : ℝ) (τ : ℝ) (hd : d ≠ 0) :
    (d⁻¹ • (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸)))
        * (τ ^ j : 𝔸)
      = ∫ u in 0..τ, ((τ - u) ^ k * τ ^ j / ((Nat.factorial k : ℝ) * d)) •
          expSMulConj A X u := by
  have hsub : (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸)) =
        ∫ u in 0..τ, ((τ - u) ^ k / (Nat.factorial k : ℝ)) • expSMulConj A X u :=
    (integral_smul_eq_integral_mul_sub (fun u => expSMulConj A X u) k τ).symm
  rw [hsub]
  rw [← intervalIntegral.integral_smul]
  rw [← map_pow (algebraMap ℝ 𝔸) τ j]
  rw [integral_mul_cast (fun u => d⁻¹ • (((τ - u) ^ k / (Nat.factorial k : ℝ)) •
    expSMulConj A X u)) (τ ^ j) τ]
  apply intervalIntegral.integral_congr_uIoo
  intro u _
  dsimp
  rw [← mul_smul]
  rw [smul_mul_cast]
  congr 1
  exact scalar_combine k j d τ u hd

/-! ### Structural lemmas for the induction step of `commutatorExpansion_conj` -/

/-- Restricting `A : Fin (s+1) → 𝔸` (via `prefixRestrict`) to the first `j+1` layers coincides
whether one first drops to the inner `Fin s` sequence or works directly on `Fin (s+1)`. -/
lemma prefixRestrict_castSucc {s} {𝔸 : Type*} (A : Fin (s + 1) → 𝔸) (j : Fin s) :
    prefixRestrict (fun i : Fin s => A i.castSucc) (j + 1) (Nat.succ_le_of_lt j.2)
      = prefixRestrict A (j + 1) (Nat.succ_le_of_lt j.castSucc.2) := by
  funext i
  simp [prefixRestrict]

/-- Conjugating an inner-layer remainder term by the outermost layer yields the corresponding
outer-layer remainder term at the same (inner) layer index. -/
lemma expSMulConj_commutatorRemainderTerm {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) :
    expSMulConj (A (Fin.last s)) (commutatorRemainderTerm (fun i : Fin s => A i.castSucc) B τ j q) τ
      = commutatorRemainderTerm A B τ j.castSucc q := by
  unfold commutatorRemainderTerm expSMulConj
  let L_inner : 𝔸 :=
    ((List.ofFn (fun i : Fin s => exp (τ • A i.castSucc))).drop (j + 1)).reverse.prod
  let I_inner : 𝔸 := ∫ u in 0..τ,
    (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
    expSMulConj (A j.castSucc)
      (adSequence (prefixRestrict (fun i : Fin s => A i.castSucc) (j + 1)
        (Nat.succ_le_of_lt j.2)) q B) u
  let R_inner : 𝔸 := ((List.ofFn (fun i : Fin s => exp (-τ • A i.castSucc))).drop (j + 1)).prod
  let L_outer : 𝔸 :=
    ((List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).drop (j.castSucc + 1)).reverse.prod
  let I_outer : 𝔸 := ∫ u in 0..τ,
    (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
    expSMulConj (A j.castSucc)
      (adSequence (prefixRestrict A (j.castSucc + 1) (Nat.succ_le_of_lt j.castSucc.2)) q B) u
  let R_outer : 𝔸 :=
    ((List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).drop (j.castSucc + 1)).prod
  change exp (τ • A (Fin.last s)) * ((L_inner * I_inner) * R_inner) * exp (-τ • A (Fin.last s))
      = (L_outer * I_outer) * R_outer
  have hL : exp (τ • A (Fin.last s)) * L_inner = L_outer := by
    have hk : j + 1 ≤ s := Nat.succ_le_of_lt j.2
    dsimp [L_inner, L_outer]
    simpa using (ofFn_castSucc_drop_reverse_prod
      (f := fun i : Fin (s + 1) => exp (τ • A i)) (k := j + 1) hk)
  have hR : R_inner * exp (-τ • A (Fin.last s)) = R_outer := by
    have hk : j + 1 ≤ s := Nat.succ_le_of_lt j.2
    dsimp [R_inner, R_outer]
    simpa using (ofFn_castSucc_drop_prod (f := fun i : Fin (s + 1) => exp (-τ • A i))
      (k := j + 1) hk)
  have hI : I_inner = I_outer := by
    dsimp [I_inner, I_outer]
    apply intervalIntegral.integral_congr_uIoo
    intro u _
    simp only [prefixRestrict_castSucc A j]
  calc
    exp (τ • A (Fin.last s)) * ((L_inner * I_inner) * R_inner) * exp (-τ • A (Fin.last s))
        = (exp (τ • A (Fin.last s)) * L_inner) * I_inner *
            (R_inner * exp (-τ • A (Fin.last s))) := by
            noncomm_ring
    _ = (L_outer * I_outer) * R_outer := by rw [hL, hI, hR]

/-- Decomposing `commutatorRemainder` over `s + 1` layers into the inner remainder conjugated by the
outermost layer plus the outermost-layer remainder. -/
lemma commutatorRemainder_succ {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    commutatorRemainder A B p τ =
      expSMulConj (A (Fin.last s)) (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
  rw [commutatorRemainder, Fin.sum_univ_castSucc]
  congr 1
  · symm
    rw [commutatorRemainder]
    rw [expSMulConj_map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [expSMulConj_map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact expSMulConj_commutatorRemainderTerm A B τ j q

/-! ### Reassembly lemmas for the polynomial and remainder parts -/

/-- The polynomial part of the single-layer Taylor expansion reassembles, after reindexing by the
total degree, into `Σ_{m < p} conjCoeff A B m · τ^m`. -/
lemma conjCoeff_sum_of_taylor {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    (∑ j ∈ range p,
        (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
          (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸))
          * (τ ^ j : 𝔸))
      = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸) := by
  calc
    (∑ j ∈ range p, (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
        (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸))
          * (τ ^ j : 𝔸))
        = ∑ j ∈ range p, ∑ i ∈ range (p - j),
            ((Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j))) *
              (τ ^ (i + j) : 𝔸) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              rw [mul_assoc]
              rw [show (τ ^ i : 𝔸) * (τ ^ j : 𝔸) = (τ ^ (i + j) : 𝔸) by rw [← pow_add]]
    _ = ∑ m ∈ range p, ∑ i ∈ range (m + 1),
            ((Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B (m - i)))) *
              (τ ^ m : 𝔸) := by
              rw [sum_range_add_antidiagonal p
                (fun i j => ((Nat.factorial i : ℝ)⁻¹ •
                  (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j))) *
                    (τ ^ (i + j) : 𝔸))]
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : i ≤ m := Nat.le_of_lt_succ (mem_range.mp hi)
              congr 1
              rw [show i + (m - i) = m by lia]
    _ = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸) := by
              apply Finset.sum_congr rfl
              intro m _
              rw [← Finset.sum_mul]
              congr 1
              rw [conjCoeff_succ A B m]

/-- The outermost-layer (`j = Fin.last s`) remainder term, written as the smul-integral of the
conjugated `adPow A' (k + 1)` applied to the inner `adSequence`. -/
lemma commutatorRemainderTerm_last {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (q : Fin s → ℕ) (m : ℕ) :
    commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q m) =
      ∫ u in 0..τ, (((τ - u) ^ (m - 1) * τ ^ (∑ i : Fin s, q i) /
          ((Nat.factorial (m - 1) : ℝ) * ∏ i : Fin s, (Nat.factorial (q i) : ℝ)))) •
        expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) m (adSequence (fun i : Fin s => A i.castSucc) q B)) u := by
  unfold commutatorRemainderTerm
  have hL : ((List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).drop
      ((Fin.last s : ℕ) + 1)) = [] := by
    rw [Fin.val_last]
    exact List.drop_eq_nil_of_le (by simp)
  have hR : ((List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).drop
      ((Fin.last s : ℕ) + 1)) = [] := by
    rw [Fin.val_last]
    exact List.drop_eq_nil_of_le (by simp)
  rw [hL, hR]
  simp [Fin.snoc_last, Fin.snoc_castSucc, prefixRestrict_self, adSequence_snoc]

/-- The single `j`-th Taylor remainder of the outermost conjugation, expanded over the
`finAntidiagonal s j` fibers and matched against the outermost-layer `commutatorRemainderTerm`s. -/
lemma expSMulConj_taylor_remainder_conjCoeff {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p j : ℕ) (τ : ℝ) :
    (∫ u in 0..τ, expSMulConj (A (Fin.last s))
        (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)
      = ∑ q ∈ finAntidiagonal s j,
          commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
  let A' : 𝔸 := A (Fin.last s)
  let A_inner : Fin s → 𝔸 := fun i => A i.castSucc
  calc
    (∫ u in 0..τ, expSMulConj A' (adPow A' (p - j) (conjCoeff A_inner B j)) (τ - u) *
        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)
        = (∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
            (∫ u in 0..τ, expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
              ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) * (τ ^ j : 𝔸) := by
              congr 1
              have had : adPow A' (p - j) (conjCoeff A_inner B j) =
                  ∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B) := by
                rw [conjCoeff]
                have h : adPow A' (p - j) (∑ q ∈ finAntidiagonal s j,
                    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B) =
                    ∑ q ∈ finAntidiagonal s j, adPow A' (p - j)
                      (((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B) :=
                  map_sum (adPowLin A' (p - j)).toAddMonoidHom
                    (fun q =>
                      ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B)
                    (finAntidiagonal s j)
                rw [h]
                apply Finset.sum_congr rfl
                intro q _
                exact (adPowLin A' (p - j)).map_smul' ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹)
                  (adSequence A_inner q B)
              rw [had]
              have hpoint : ∀ u : ℝ, expSMulConj A' (∑ q ∈ finAntidiagonal s j,
                  ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                  ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)
                  = ∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) := by
                intro u
                rw [expSMulConj_map_sum (A := A') (τ := τ - u) (s := finAntidiagonal s j)
                  (f := fun q => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B))]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro q _
                have hsmul : expSMulConj A' (((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (adPow A' (p - j) (adSequence A_inner q B))) (τ - u)
                    = ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                      expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) :=
                  (expSMulConjLin A' (τ - u)).map_smul' ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹)
                    (adPow A' (p - j) (adSequence A_inner q B))
                rw [hsmul]
                rw [smul_mul_assoc]
              rw [intervalIntegral.integral_congr_uIoo (fun u _ => hpoint u)]
              have hint : ∀ q ∈ finAntidiagonal s j, IntervalIntegrable
                  (fun u : ℝ => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) volume 0 τ := by
                intro q _
                have hc : Continuous
                  (fun u : ℝ => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) := by
                  refine Continuous.smul continuous_const ?_
                  rw [show (fun u : ℝ =>
                      expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))
                        = fun u : ℝ => (u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) •
                          expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) by
                    funext u
                    rw [← smul_eq_mul_right]]
                  refine Continuous.smul (by fun_prop) ?_
                  exact (continuous_expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B))).comp
                    (continuous_const.sub continuous_id)
                exact hc.intervalIntegrable 0 τ
              rw [intervalIntegral.integral_finsetSum hint]
              apply Finset.sum_congr rfl
              intro q _
              rw [intervalIntegral.integral_smul]
    _ = ∑ q ∈ finAntidiagonal s j,
          commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro q hq
              have hd : (∏ i : Fin s, (Nat.factorial (q i) : ℝ)) ≠ 0 := by positivity
              have hsum : (∑ i : Fin s, q i) = j := mem_finAntidiagonal.mp hq
              rw [expSMulConj_taylor_remainder_smul (A := A')
                (X := adPow A' (p - j) (adSequence A_inner q B))
                (k := p - j - 1) (j := j) (d := ∏ i : Fin s, (Nat.factorial (q i) : ℝ)) (τ := τ) hd]
              rw [commutatorRemainderTerm_last A B τ q (p - j)]
              rw [hsum]

/-- Summing the single-layer Taylor remainders over `j < p` and reindexing by the antidiagonal
fiber gives the outermost-layer part of `commutatorRemainder`. -/
lemma taylor_remainder_sum {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    (∑ j ∈ range p,
        (∫ u in 0..τ, expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
          ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸))
      = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
          commutatorRemainderTerm A B τ (Fin.last s) q := by
  calc
    (∑ j ∈ range p,
        (∫ u in 0..τ, expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
          ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸))
        = ∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j,
            commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact expSMulConj_taylor_remainder_conjCoeff A B p j τ
    _ = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (k + 1)) := by
              exact sum_range_finAntidiagonal_reflect
                (fun q' => commutatorRemainderTerm A B τ (Fin.last s) q')
    _ = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
          commutatorRemainderTerm A B τ (Fin.last s) q := by
              exact (sum_finAntidiagonal_filter_last_ne_zero s p
                (fun q => commutatorRemainderTerm A B τ (Fin.last s) q)).symm

/-- The single-layer Taylor expansion of `expSMulConj A' (Σ_{j<p} C_j · τ^j) τ`, split into the
reassembled polynomial `Σ_{m<p} conjCoeff A B m · τ^m` plus the outermost-layer remainder. -/
lemma expSMulConj_taylor_poly {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    expSMulConj (A (Fin.last s))
        (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ
      = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸))
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
  calc
    expSMulConj (A (Fin.last s))
      (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ
        = ∑ j ∈ range p, expSMulConj (A (Fin.last s))
            (conjCoeff (fun i : Fin s => A i.castSucc) B j) τ * (τ ^ j : 𝔸) := by
              rw [expSMulConj_map_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [← map_pow (algebraMap ℝ 𝔸) τ j]
              exact expSMulConj_mul_cast (A (Fin.last s))
                (conjCoeff (fun i : Fin s => A i.castSucc) B j) (τ ^ j) τ
    _ = ∑ j ∈ range p, ((∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) *
              (τ ^ i : 𝔸))
            + ∫ u in 0..τ, expSMulConj (A (Fin.last s))
                (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j))
                  (τ - u) *
                ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hpj : 1 ≤ p - j := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (mem_range.mp hj))
              rw [expSMulConj_taylor (A (Fin.last s))
                (conjCoeff (fun i : Fin s => A i.castSucc) B j) (p - j) τ hpj]
    _ = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸))
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
              simp_rw [add_mul, Finset.sum_add_distrib]
              congr 1
              · exact conjCoeff_sum_of_taylor A B p τ
              · exact taylor_remainder_sum A B p τ

/-- `thm:comm_exp_conj` (theory.tex:222-236): the multi-layer conjugation expands as
`multiConj A B τ = Σ_{j < p} conjCoeff A B j · τ^j + commutatorRemainder A B p τ`,
where the `conjCoeff A B j` are the operators `C_j` independent of `τ`. -/
theorem commutatorExpansion_conj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    multiConj A B τ =
      (∑ j ∈ Finset.range p, conjCoeff A B j * (τ ^ j : 𝔸)) + commutatorRemainder A B p τ := by
  induction s with
  | zero =>
      have hmulti : multiConj A B τ = B := by simp [multiConj]
      have hc0 : conjCoeff A B 0 = B := by
        rw [conjCoeff]
        rw [Finset.sum_eq_single_of_mem (s := finAntidiagonal 0 0) (a := 0)
          (f := fun q => ((∏ i : Fin 0, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B)]
        · simp [adSequence]
        · rw [mem_finAntidiagonal]
          simp
        · intro b _ hb
          exfalso
          apply hb
          exact Subsingleton.elim _ _
      have hcj : ∀ j, 0 < j → conjCoeff A B j = 0 := by
        intro j hj
        rw [conjCoeff]
        have hempty : finAntidiagonal 0 j = ∅ := by
          ext q
          rw [mem_finAntidiagonal]
          rw [show (∑ i : Fin 0, q i) = 0 by simp]
          constructor
          · intro h
            exact False.elim ((ne_of_gt hj) h.symm)
          · intro h
            simp at h
        rw [hempty]
        simp
      have hrem : commutatorRemainder A B p τ = 0 := by simp [commutatorRemainder]
      rw [hmulti, hrem, add_zero]
      rw [Finset.sum_eq_single_of_mem (a := 0) (s := Finset.range p)
        (f := fun j => conjCoeff A B j * (τ ^ j : 𝔸))]
      · simp [hc0]
      · rw [Finset.mem_range]
        exact lt_of_lt_of_le zero_lt_one hp
      · intro j _ hj0
        rw [hcj j (Nat.pos_of_ne_zero hj0), zero_mul]
  | succ s ih =>
      rw [multiConj_succ A B τ]
      rw [ih (fun i : Fin s => A i.castSucc)]
      have hlin : expSMulConj (A (Fin.last s))
          ((∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) +
            commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ
          = expSMulConj (A (Fin.last s))
              (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ +
            expSMulConj (A (Fin.last s))
              (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ :=
        (expSMulConjLin (A (Fin.last s)) τ).map_add' _ _
      rw [hlin]
      rw [expSMulConj_taylor_poly A B p τ]
      rw [commutatorRemainder_succ A B p τ]
      abel

end TrotterError
