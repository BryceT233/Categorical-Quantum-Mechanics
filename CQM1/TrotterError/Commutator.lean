/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Commutators and nested commutators

Commutator foundations for the Trotter error theory (arXiv:1912.08854). We use the
associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A`, the adjoint map `ad A = [A, ·]`, and
its `q`-fold iteration `(ad A)^[q]` for the iterated commutator `ad_A^q(B)` of a single
operator, the iterated `ad` over a sequence of (possibly different) operators with
multiplicities, and the nested commutator `[H_p, ⋯ [H_1, H_0] ⋯]`. We also define the
`α`-norm quantities `α~_comm` and `α_comm` of the paper, together with their basic
norm bounds.

## Main definitions

* `ad`: the adjoint map `ad A = ⁅A, ·⁆`.
* `adPow`: the `q`-fold iterated commutator `ad_A^q(B) = (ad A)^[q] B`.
* `adSequence`: the iterated `ad` over `A ⟨0⟩, …, A ⟨s-1⟩` with multiplicities
  `q ⟨0⟩, …, q ⟨s-1⟩`; `A ⟨0⟩` is innermost and `A ⟨s-1⟩` is outermost.
* `nestedComm`: the nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with
  exactly `p` brackets, `H ⟨0⟩` innermost and `H ⟨p⟩` outermost.
* `alphaComm`: `α~_comm = Σ_{γ : Fin (p+1) → Fin Γ} ‖[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]‖`.
* `alphaCommConj`: the multinomial-weighted sum `Σ_{q₁+⋯+q_s = p}
  (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`.

## Main results

* `norm_commutator_le`: `‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖`.
* `norm_adPow_le`: `‖ad_A^k(B)‖ ≤ (2 * ‖A‖)^k * ‖B‖`.
* `norm_adSequence_le`: the product bound for an iterated `ad` over a sequence.
* `alphaComm_nonneg`: `0 ≤ alphaComm p H`.
* `adPow_add`, `adPow_smul`, `adPowLin`: the ℝ-linearity and algebraic properties of
  `adPow A k` (derived from the Lie bracket axioms).
* `adPow_mul_central`: `adPow A k` commutes with right multiplication by elements
  commuting with `A`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open scoped algebraMap

/- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A` on any ring, so that the
standard Lie-bracket lemmas (`lie_add`, `lie_smul`, Jacobi `leibniz_lie`, …) are available. -/
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Basic commutator objects -/

/-- The adjoint map `ad A = [A, ·]`, as the bare function underlying Mathlib's
`LieAlgebra.ad` over `ℤ` (the scalar-free instantiation for a plain ring). -/
def ad {𝔸 : Type*} [Ring 𝔸] (A : 𝔸) : 𝔸 → 𝔸 := (LieAlgebra.ad ℤ 𝔸 A : 𝔸 → 𝔸)

/-- The `q`-fold iterated commutator `ad_A^q(B)`, i.e. the `q`-th iterate of `ad A` applied
to `B`: `adPow A 0 B = B` and `adPow A (q + 1) B = ⁅A, adPow A q B⁆`. -/
def adPow {𝔸 : Type*} [Ring 𝔸] (A : 𝔸) (q : ℕ) (B : 𝔸) : 𝔸 :=
  (ad A)^[q] B

/-- `adPow A 0 B = B`. -/
@[simp] lemma adPow_zero {𝔸 : Type*} [Ring 𝔸] (A B : 𝔸) : adPow A 0 B = B := rfl

/-- `adPow A (q + 1) B = ⁅A, adPow A q B⁆`. -/
@[simp] lemma adPow_succ {𝔸 : Type*} [Ring 𝔸] (A : 𝔸) (q : ℕ) (B : 𝔸) :
    adPow A (q + 1) B = ⁅A, adPow A q B⁆ := by
  rw [adPow, Function.iterate_succ_apply']
  rfl

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
  | p + 1 => ⁅H ⟨p + 1, by simp⟩, nestedComm (fun i : Fin (p + 1) => H i.castSucc)⁆

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
    ‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  rw [Ring.lie_def]
  calc
    ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le (A * B) (B * A)
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le A B) (norm_mul_le B A)
    _ = 2 * ‖A‖ * ‖B‖ := by ring

/-- The norm of the `k`-fold iterated commutator is bounded by `(2 * ‖A‖)^k * ‖B‖`. -/
theorem norm_adPow_le {𝔸 : Type*} [NormedRing 𝔸] (A : 𝔸) (k : ℕ) (B : 𝔸) :
    ‖adPow A k B‖ ≤ (2 * ‖A‖) ^ k * ‖B‖ := by
  induction k with
  | zero => simp [adPow_zero]
  | succ k ih =>
      calc
        ‖adPow A (k + 1) B‖ = ‖⁅A, adPow A k B⁆‖ := by rw [adPow_succ]
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

/-! ### Linear and algebraic properties of `adPow` -/

/-- Appending a zero multiplicity on the outermost layer does not change `adSequence`. -/
lemma adSequence_snoc_zero {𝔸 : Type*} [Ring 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q 0) B = adSequence (fun i : Fin m => A i.castSucc) q B := by
  rw [adSequence]
  simp [Fin.snoc_last]

/-- Appending a multiplicity on the outermost layer of `adSequence`: the `k`-fold commutator of
`A ⟨m⟩` applied to the inner sequence. -/
lemma adSequence_snoc {𝔸 : Type*} [Ring 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (k : ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q k) B =
      adPow (A (Fin.last m)) k (adSequence (fun i : Fin m => A i.castSucc) q B) := by
  rw [adSequence]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-- The `k`-fold iterated commutator `adPow A k` is additive in its last argument. -/
lemma adPow_add {𝔸 : Type*} [Ring 𝔸] (A : 𝔸) (k : ℕ) (X Y : 𝔸) :
    adPow A k (X + Y) = adPow A k X + adPow A k Y := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [adPow_succ, adPow_succ, adPow_succ, ih]
      exact LieRing.lie_add A (adPow A k X) (adPow A k Y)

/-- The `k`-fold iterated commutator `adPow A k` commutes with ℝ-scalar multiplication. -/
lemma adPow_smul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) (r : ℝ) (X : 𝔸) :
    adPow A k (r • X) = r • adPow A k X := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [adPow_succ, adPow_succ, ih]
      exact lie_smul r A (adPow A k X)

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
        adPow A (k + 1) (X * t) = ⁅A, adPow A k (X * t)⁆ := by rw [adPow_succ]
        _ = ⁅A, adPow A k X * t⁆ := by rw [ih]
        _ = ⁅A, adPow A k X⁆ * t := by
              rw [Ring.lie_def, Ring.lie_def]
              rw [← mul_assoc A (adPow A k X) t]
              rw [show (adPow A k X * t) * A = (adPow A k X * A) * t by
                rw [mul_assoc, ← ht.eq, ← mul_assoc]]
              rw [← sub_mul]
        _ = adPow A (k + 1) X * t := by rw [adPow_succ]

/-! ### The nested commutator of a list -/

/-- `nestedComm` commutes with reindexing a tuple by a `Fin.cast`. -/
lemma nestedComm_cast {𝔸 : Type*} [Ring 𝔸] {n m : ℕ} (h : n = m) (H : Fin (m + 1) → 𝔸) :
    nestedComm (H ∘ Fin.cast (congrArg (· + 1) h)) = nestedComm H := by
  subst h
  rfl

/-- The nested commutator of a list with an innermost seed: `nestedCommOfList b [x₁, …, xₙ] =
⁅xₙ, ⋯ ⁅x₁, b⁆ ⋯⁆` (the head `x₁` is innermost and the last element `xₙ` is outermost). -/
def nestedCommOfList {𝔸 : Type*} [Ring 𝔸] (b : 𝔸) : List 𝔸 → 𝔸 :=
  List.foldl (fun acc X => ⁅X, acc⁆) b

@[simp] lemma nestedCommOfList_nil {𝔸 : Type*} [Ring 𝔸] (b : 𝔸) :
    nestedCommOfList b [] = b := rfl

@[simp] lemma nestedCommOfList_append {𝔸 : Type*} [Ring 𝔸] (b X : 𝔸) (L : List 𝔸) :
    nestedCommOfList b (L ++ [X]) = ⁅X, nestedCommOfList b L⁆ := by
  rw [nestedCommOfList, List.foldl_append]
  rfl

/-- `nestedCommOfList b (L ++ replicate k X) = adPow X k (nestedCommOfList b L)`: the `k`
outermost copies of `X` contribute the `k`-fold iterated commutator. -/
lemma nestedCommOfList_append_replicate {𝔸 : Type*} [Ring 𝔸] (b X : 𝔸) (L : List 𝔸)
    (k : ℕ) :
    nestedCommOfList b (L ++ List.replicate k X) = adPow X k (nestedCommOfList b L) := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [List.replicate_succ', ← List.append_assoc, nestedCommOfList_append, adPow_succ, ih]

/-- The tuple `Fin (L.length + 1) → 𝔸` with `0 ↦ b` and `t + 1 ↦ f (L[t])`. -/
def listIndexed {ι 𝔸 : Type*} (b : 𝔸) (L : List ι) (f : ι → 𝔸) : Fin (L.length + 1) → 𝔸 :=
  Fin.cons b (fun t : Fin L.length => f (L[t.val]'t.2))

/-- `nestedComm` peels the outermost element of a `Fin.cons`-built tuple. -/
lemma nestedComm_cons_succ {𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin (n + 1) → 𝔸) :
    nestedComm (Fin.cons b tail) =
      ⁅tail (Fin.last n), nestedComm (Fin.cons b (fun i : Fin n => tail i.castSucc))⁆ := by
  rw [nestedComm]
  apply congrArg₂ (fun x y : 𝔸 => ⁅x, y⁆)
  · rw [show ((⟨n + 1, by simp⟩ : Fin (n + 2)) = Fin.succ (Fin.last n)) by rfl]
    rw [Fin.cons_succ]
  · congr 1
    funext i
    refine Fin.cases ?zero ?succ i
    · simp [Fin.cons_zero]
    · intro j
      rw [Fin.castSucc_succ, Fin.cons_succ, Fin.cons_succ]

/-- `nestedComm` of a `Fin.cons`-built tuple equals the list nested commutator of the
`List.ofFn` image of the tail. -/
lemma nestedComm_ofFn_cons {𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin n → 𝔸) :
    nestedComm (Fin.cons b tail) = nestedCommOfList b (List.ofFn tail) := by
  induction n with
  | zero => simp [Fin.cons, List.ofFn, nestedComm]
  | succ n ih =>
      rw [nestedComm_cons_succ]
      rw [List.ofFn_succ_last]
      rw [nestedCommOfList_append]
      rw [ih (fun i : Fin n => tail i.castSucc)]

/-- `nestedComm` of `listIndexed` is the list nested commutator. -/
lemma nestedComm_listIndexed {𝔸 : Type*} [Ring 𝔸] {ι : Type*} (b : 𝔸) (L : List ι)
    (f : ι → 𝔸) :
    nestedComm (listIndexed b L f) = nestedCommOfList b (L.map f) := by
  rw [listIndexed]
  rw [nestedComm_ofFn_cons]
  congr 1
  rw [List.ofFn_eq_map]
  rw [show (List.finRange L.length).map (fun t => f (L[t.val]'t.2)) =
      ((List.finRange L.length).map (fun t => L[t.val]'t.2)).map f by
    rw [List.map_map]
    rfl]
  rw [List.map_getElem_finRange]

end TrotterError
