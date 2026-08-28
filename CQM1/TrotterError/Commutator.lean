/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

import Mathlib.Tactic.NoncommRing

/-!
# Commutators and nested commutators

Commutator foundations for the Trotter error theory (arXiv:1912.08854). We define the
commutator `[A, B] = A * B - B * A`, the iterated commutator `ad_A^q(B)` of a single
operator, the iterated `ad` over a sequence of (possibly different) operators with
multiplicities, and the nested commutator `[H_p, ⋯ [H_1, H_0] ⋯]`. We also define the
`α`-norm quantities `α~_comm` and `α_comm` of the paper, together with their basic
norm bounds.

## Main definitions

* `commutator`: the commutator `[A, B] = A * B - B * A`.
* `adPow`: the `q`-fold iterated commutator `ad_A^q(B)`.
* `adSequence`: the iterated `ad` over `A ⟨0⟩, …, A ⟨s-1⟩` with multiplicities
  `q ⟨0⟩, …, q ⟨s-1⟩`; `A ⟨0⟩` is innermost and `A ⟨s-1⟩` is outermost.
* `nestedComm`: the nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with
  exactly `p` brackets, `H ⟨0⟩` innermost and `H ⟨p⟩` outermost.
* `alphaComm`: `α~_comm = Σ_{γ : Fin (p+1) → Fin Γ} ‖[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]‖`.
* `alphaCommConj`: the multinomial-weighted sum `Σ_{q₁+⋯+q_s = p}
  (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`.

## Main results

* `norm_commutator_le`: `‖[A, B]‖ ≤ 2 * ‖A‖ * ‖B‖`.
* `norm_adPow_le`: `‖ad_A^k(B)‖ ≤ (2 * ‖A‖)^k * ‖B‖`.
* `norm_adSequence_le`: the product bound for an iterated `ad` over a sequence.
* `alphaComm_nonneg`: `0 ≤ alphaComm p H`.
* `commutator_add`, `commutator_smul`, `adPow_add`, `adPow_smul`, `adPowLin`: the
  ℝ-linearity and algebraic properties of `commutator` and `adPow A k`.
* `adPow_mul_central`: `adPow A k` commutes with right multiplication by elements
  commuting with `A`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open scoped algebraMap

/-! ### Basic commutator objects -/

/-- The commutator `[A, B] = A * B - B * A` in an associative ring. -/
def commutator {𝔸 : Type*} [Ring 𝔸] (A B : 𝔸) : 𝔸 :=
  A * B - B * A

/-- The `q`-fold iterated commutator `ad_A^q(B)`, defined by recursion on `q`:
`adPow A 0 B = B` and `adPow A (q + 1) B = commutator A (adPow A q B)`. -/
def adPow {𝔸 : Type*} [Ring 𝔸] (A : 𝔸) (q : ℕ) (B : 𝔸) : 𝔸 :=
  match q with
  | 0 => B
  | q + 1 => commutator A (adPow A q B)

/-- The iterated `ad` over a sequence of operators with multiplicities,
`ad_{A ⟨s-1⟩}^{q ⟨s-1⟩} ⋯ ad_{A ⟨0⟩}^{q ⟨0⟩}(B)`, where `A ⟨0⟩` is applied first
(innermost) and `A ⟨s-1⟩` is applied last (outermost). -/
def adSequence {𝔸 : Type*} [Ring 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) : 𝔸 :=
  match s with
  | 0 => B
  | s + 1 =>
      adPow (A (Fin.last s)) (q (Fin.last s))
        (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) B)

/-- The nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with exactly `p`
brackets: `H ⟨0⟩` is innermost and `H ⟨p⟩` is outermost. -/
def nestedComm {𝔸 : Type*} [Ring 𝔸] {p : ℕ} (H : Fin (p + 1) → 𝔸) : 𝔸 :=
  match p with
  | 0 => H ⟨0, by simp⟩
  | p + 1 =>
      commutator (H ⟨p + 1, by simp⟩) (nestedComm (fun i : Fin (p + 1) => H i.castSucc))

/-- The paper's `α~_comm`: the sum of the norms of all nested commutators
`[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]` over all tuples `γ : Fin (p + 1) → Fin Γ`
(repeated indices allowed). -/
noncomputable def alphaComm {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ)
    (H : Fin Γ → 𝔸) : ℝ :=
  ∑ γ : Fin (p + 1) → Fin Γ, ‖nestedComm (H ∘ γ)‖

/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
noncomputable def alphaCommConj {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ q ∈ Finset.finAntidiagonal s p,
    (Nat.multinomial (Finset.univ : Finset (Fin s)) q : ℝ) * ‖adSequence A q B‖

/-! ### Norm bounds -/

/-- The norm of a commutator is bounded by `2 * ‖A‖ * ‖B‖`. -/
theorem norm_commutator_le {𝔸 : Type*} [NormedRing 𝔸] (A B : 𝔸) :
    ‖commutator A B‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  rw [commutator]
  calc
    ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le (A * B) (B * A)
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le A B) (norm_mul_le B A)
    _ = 2 * ‖A‖ * ‖B‖ := by ring

/-- The norm of the `k`-fold iterated commutator is bounded by `(2 * ‖A‖)^k * ‖B‖`. -/
theorem norm_adPow_le {𝔸 : Type*} [NormedRing 𝔸] (A : 𝔸) (k : ℕ) (B : 𝔸) :
    ‖adPow A k B‖ ≤ (2 * ‖A‖) ^ k * ‖B‖ := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      calc
        ‖adPow A (k + 1) B‖ = ‖commutator A (adPow A k B)‖ := by rw [adPow]
        _ ≤ 2 * ‖A‖ * ‖adPow A k B‖ := norm_commutator_le A (adPow A k B)
        _ ≤ 2 * ‖A‖ * ((2 * ‖A‖) ^ k * ‖B‖) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * ‖A‖) ^ (k + 1) * ‖B‖ := by rw [pow_succ]; ring

/-- The norm of an iterated `ad` over a sequence is bounded by the product of the
per-step bounds `(2 * ‖A i‖) ^ (q i)`. -/
theorem norm_adSequence_le {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    ‖adSequence A q B‖ ≤ (∏ i : Fin s, (2 * ‖A i‖) ^ (q i)) * ‖B‖ := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      calc
        ‖adSequence A q B‖
            = ‖adPow (A (Fin.last s)) (q (Fin.last s))
                (adSequence (fun i : Fin s => A i.castSucc)
                  (fun i : Fin s => q i.castSucc) B)‖ := by
                rw [adSequence]
        _ ≤ (2 * ‖A (Fin.last s)‖) ^ (q (Fin.last s)) *
              ‖adSequence (fun i : Fin s => A i.castSucc)
                (fun i : Fin s => q i.castSucc) B‖ :=
              norm_adPow_le (A (Fin.last s)) (q (Fin.last s))
                (adSequence (fun i : Fin s => A i.castSucc)
                  (fun i : Fin s => q i.castSucc) B)
        _ ≤ (2 * ‖A (Fin.last s)‖) ^ (q (Fin.last s)) *
              ((∏ i : Fin s, (2 * ‖A i.castSucc‖) ^ (q i.castSucc)) * ‖B‖) :=
              mul_le_mul_of_nonneg_left
                (ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc))
                (by positivity)
        _ = (∏ i : Fin (s + 1), (2 * ‖A i‖) ^ (q i)) * ‖B‖ := by
              rw [Fin.prod_univ_castSucc]
              ring

/-- `alphaComm p H` is a sum of norms, hence nonnegative. -/
theorem alphaComm_nonneg {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ) (H : Fin Γ → 𝔸) :
    0 ≤ alphaComm p H := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-! ### Linear and algebraic properties of `commutator` and `adPow` -/

/-- In an ℝ-algebra, the scalar action `r • a` equals right multiplication `a * (r : 𝔸)`. -/
lemma smul_eq_mul_right {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r : ℝ) (a : 𝔸) :
    r • a = a * (r : 𝔸) := by
  rw [Algebra.smul_def, Algebra.commutes]

/-- Appending a zero multiplicity on the outermost layer does not change `adSequence`. -/
lemma adSequence_snoc_zero {𝔸 : Type*} [Ring 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q 0) B = adSequence (fun i : Fin m => A i.castSucc) q B := by
  rw [adSequence]
  simp [adPow, Fin.snoc_last]

/-- Appending a multiplicity on the outermost layer of `adSequence`: the `k`-fold commutator of
`A ⟨m⟩` applied to the inner sequence. -/
lemma adSequence_snoc {𝔸 : Type*} [Ring 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (k : ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q k) B =
      adPow (A (Fin.last m)) k (adSequence (fun i : Fin m => A i.castSucc) q B) := by
  rw [adSequence]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-- The commutator `[A, ·]` is additive in its second argument. -/
lemma commutator_add {𝔸 : Type*} [Ring 𝔸] (A X Y : 𝔸) :
    commutator A (X + Y) = commutator A X + commutator A Y := by
  unfold commutator
  noncomm_ring

/-- The commutator `[A, ·]` commutes with ℝ-scalar multiplication in its second argument. -/
lemma commutator_smul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (r : ℝ) (X : 𝔸) :
    commutator A (r • X) = r • commutator A X := by
  unfold commutator
  rw [smul_eq_mul_right r X, smul_eq_mul_right r (A * X - X * A)]
  noncomm_ring [Algebra.commutes (r : ℝ) A]

/-- The `k`-fold iterated commutator `adPow A k` is additive in its last argument. -/
lemma adPow_add {𝔸 : Type*} [Ring 𝔸] (A : 𝔸) (k : ℕ) (X Y : 𝔸) :
    adPow A k (X + Y) = adPow A k X + adPow A k Y := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [adPow, adPow, adPow, ih]
      exact commutator_add A (adPow A k X) (adPow A k Y)

/-- The `k`-fold iterated commutator `adPow A k` commutes with ℝ-scalar multiplication. -/
lemma adPow_smul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) (r : ℝ) (X : 𝔸) :
    adPow A k (r • X) = r • adPow A k X := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [adPow, adPow, ih]
      exact commutator_smul A r (adPow A k X)

/-- `adPow A k` as an ℝ-linear endomorphism of `𝔸`. -/
def adPowLin {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) : 𝔸 →ₗ[ℝ] 𝔸 where
  toFun := fun X => adPow A k X
  map_add' := fun X Y => adPow_add A k X Y
  map_smul' := fun r X => adPow_smul A k r X

/-- `adPow A k` commutes with right multiplication by an element `t` commuting with `A`. -/
lemma adPow_mul_central {𝔸 : Type*} [Ring 𝔸] (A X t : 𝔸) (k : ℕ) (ht : Commute A t) :
    adPow A k (X * t) = adPow A k X * t := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      calc
        adPow A (k + 1) (X * t) = commutator A (adPow A k (X * t)) := by rw [adPow]
        _ = commutator A (adPow A k X * t) := by rw [ih]
        _ = (commutator A (adPow A k X)) * t := by
              unfold commutator
              rw [← mul_assoc A (adPow A k X) t]
              rw [show (adPow A k X * t) * A = (adPow A k X * A) * t by
                rw [mul_assoc, ← ht.eq, ← mul_assoc]]
              rw [← sub_mul]
        _ = adPow A (k + 1) X * t := by rw [adPow]

end TrotterError
