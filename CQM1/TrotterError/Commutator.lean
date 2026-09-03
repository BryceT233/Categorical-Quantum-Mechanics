/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

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

* `adPow`: the `q`-fold iterated adjoint `(ad A)^q`, as an ℝ-linear endomorphism of `𝔸`.
* `adSequence`: the iterated `ad` over `A ⟨0⟩, …, A ⟨s-1⟩` with multiplicities
  `q ⟨0⟩, …, q ⟨s-1⟩`; `A ⟨0⟩` is innermost and `A ⟨s-1⟩` is outermost.
* `nestedComm`: the nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with
  exactly `p` brackets, `H ⟨0⟩` innermost and `H ⟨p⟩` outermost.
* `nestedCommOfList`, `listIndexed`: the list-based nested commutator and its `Fin`-indexed
  realization.
* `αComm`: `α~_comm = Σ_{γ : Fin (p+1) → Fin Γ} ‖[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]‖`.
* `αCommConj`: the multinomial-weighted sum `Σ_{q₁+⋯+q_s = p}
  (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`.

## Main results

* `norm_commutator_le`: `‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖`.
* `norm_adPow_le`: `‖ad_A^k(B)‖ ≤ (2 * ‖A‖)^k * ‖B‖`.
* `norm_adSequence_le`: the product bound for an iterated `ad` over a sequence.
* `αComm_nonneg`: `0 ≤ αComm p H`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open Finset LieAlgebra
open scoped algebraMap

/- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A` on any ring, so that the
standard Lie-bracket lemmas (`lie_add`, `lie_smul`, …) are available. -/
attribute [local instance] LieRing.ofAssociativeRing

/-! ### Basic commutator objects -/

@[simp] lemma ad_pow_succ {R 𝔸 : Type*} [CommRing R] [Ring 𝔸] [LieAlgebra R 𝔸] (A : 𝔸) (q : ℕ)
    (B : 𝔸) : ((ad R 𝔸 A) ^ (q + 1)) B = ⁅A, ((ad R 𝔸 A) ^ q) B⁆ := by simp [pow_succ']

/-- The `q`-fold iterated adjoint `ad_A^q = (ad A)^q`, as an ℝ-linear endomorphism of `𝔸`. -/
abbrev adPow {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (q : ℕ) : Module.End ℝ 𝔸 :=
  (ad ℝ 𝔸 A) ^ q

/-- The iterated `ad` over a sequence of operators with multiplicities,
`ad_{A ⟨s-1⟩}^{q ⟨s-1⟩} ⋯ ad_{A ⟨0⟩}^{q ⟨0⟩}(B)`, where `A ⟨0⟩` is applied first
(innermost) and `A ⟨s-1⟩` is applied last (outermost). -/
def adSequence {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
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
noncomputable def αComm {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ)
    (H : Fin Γ → 𝔸) : ℝ :=
  ∑ γ : Fin (p + 1) → Fin Γ, ‖nestedComm (H ∘ γ)‖

/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
noncomputable def αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
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
theorem norm_adPow_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) (B : 𝔸) :
    ‖adPow A k B‖ ≤ (2 * ‖A‖) ^ k * ‖B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        ‖adPow A (k + 1) B‖ = ‖⁅A, adPow A k B⁆‖ := by rw [ad_pow_succ]
        _ ≤ 2 * ‖A‖ * ‖adPow A k B‖ := norm_commutator_le A (adPow A k B)
        _ ≤ 2 * ‖A‖ * ((2 * ‖A‖) ^ k * ‖B‖) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * ‖A‖) ^ (k + 1) * ‖B‖ := by rw [pow_succ]; ring

/-- The norm of an iterated `ad` over a sequence is bounded by the product of the
per-step bounds `(2 * ‖A i‖) ^ (q i)`. -/
theorem norm_adSequence_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
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

/-- `αComm p H` is a sum of norms, hence nonnegative. -/
theorem αComm_nonneg {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ) (H : Fin Γ → 𝔸) :
    0 ≤ αComm p H := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-! ### Linear and algebraic properties of `adPow` -/

/-- Appending a zero multiplicity on the outermost layer does not change `adSequence`. -/
lemma adSequence_snoc_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q 0) B = adSequence (fun i : Fin m => A i.castSucc) q B := by
  rw [adSequence]
  simp [Fin.snoc_last]

/-- Appending a multiplicity on the outermost layer of `adSequence`: the `k`-fold commutator of
`A ⟨m⟩` applied to the inner sequence. -/
lemma adSequence_snoc {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (k : ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q k) B =
      adPow (A (Fin.last m)) k (adSequence (fun i : Fin m => A i.castSucc) q B) := by
  rw [adSequence]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-- `adSequence A q` commutes with ℝ-scalar multiplication in its last argument `B`. -/
lemma adSequence_smul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (r : ℝ) (X : 𝔸) :
    adSequence A q (r • X) = r • adSequence A q X := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      rw [adSequence, ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)]
      exact (adPow (A (Fin.last s)) (q (Fin.last s))).map_smul r
        (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) X)

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
lemma nestedCommOfList_append_replicate {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (b X : 𝔸) (L : List 𝔸)
    (k : ℕ) :
    nestedCommOfList b (L ++ List.replicate k X) = adPow X k (nestedCommOfList b L) := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [List.replicate_succ', ← List.append_assoc, nestedCommOfList_append, ad_pow_succ, ih]

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
      rw [nestedComm_cons_succ, List.ofFn_succ_last, nestedCommOfList_append,
        ih (fun i : Fin n => tail i.castSucc)]

/-- `nestedComm` of `listIndexed` is the list nested commutator. -/
lemma nestedComm_listIndexed {𝔸 : Type*} [Ring 𝔸] {ι : Type*} (b : 𝔸) (L : List ι)
    (f : ι → 𝔸) :
    nestedComm (listIndexed b L f) = nestedCommOfList b (L.map f) := by
  rw [listIndexed, nestedComm_ofFn_cons]
  congr 1
  rw [List.ofFn_eq_map]
  rw [show (List.finRange L.length).map (fun t => f (L[t.val]'t.2)) =
      ((List.finRange L.length).map (fun t => L[t.val]'t.2)).map f by
    rw [List.map_map]
    rfl]
  rw [List.map_getElem_finRange]

/-! ### Multinomial coefficients are bounded by `p!` -/

/-- Every multinomial coefficient is at most the factorial of the total degree: the multinomial
`Nat.multinomial s f` divides `(∑ f)!` (via `Nat.multinomial_spec`), and the complementary product
of factorials is `≥ 1`. -/
lemma multinomial_le_factorial {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.multinomial s f ≤ Nat.factorial (∑ i ∈ s, f i) := by
  have hspec := Nat.multinomial_spec s f
  have hprod : 1 ≤ ∏ i ∈ s, (f i).factorial := one_le_prod (fun i _ => Nat.factorial_pos _)
  calc
    Nat.multinomial s f = Nat.multinomial s f * 1 := by rw [mul_one]
    _ ≤ Nat.multinomial s f * (∏ i ∈ s, (f i).factorial) := Nat.mul_le_mul_left _ hprod
    _ = (∏ i ∈ s, (f i).factorial) * Nat.multinomial s f := by rw [mul_comm]
    _ = (∑ i ∈ s, f i).factorial := hspec

/-! ### The list of layer indices -/

/-- The list of the non-innermost operators of `expandTuple f q b`, each `f i` repeated `q i`
times, in increasing order of `i`. -/
def layersOf {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) : List α :=
  (List.finRange s).flatMap fun i => List.replicate (q i) (f i)

/-- `layersOf f q` has length `∑ q`. -/
lemma layersOf_length {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) :
    (layersOf f q).length = ∑ i : Fin s, q i := by
  induction s with
  | zero => simp [layersOf]
  | succ s ih =>
      rw [layersOf, List.finRange_succ]
      simp only [List.flatMap_cons, List.flatMap_map, List.length_append, List.length_replicate]
      change q 0 + (layersOf (f ∘ Fin.succ) (q ∘ Fin.succ)).length = ∑ i : Fin (s + 1), q i
      rw [ih (f ∘ Fin.succ) (q ∘ Fin.succ)]
      simp [Fin.sum_univ_succ]

/-- `layersOf` commutes with post-composition. -/
lemma layersOf_map {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) :
    layersOf (g ∘ f) q = (layersOf f q).map g := by
  rw [layersOf, layersOf, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  simp [List.map_replicate]

/-- The list of indices, each `i : Fin s` repeated `q i` times. -/
def layerIndices {s : ℕ} (q : Fin s → ℕ) : List (Fin s) := layersOf (fun i : Fin s => i) q

/-- The index `i` occurs exactly `q i` times in `layerIndices q`. -/
lemma layersOf_count {s : ℕ} (q : Fin s → ℕ) (i : Fin s) :
    (layersOf (fun i : Fin s => i) q).count i = q i := by
  induction s with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      rw [layersOf, List.finRange_succ_last]
      simp only [List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
      rw [List.count_append]
      refine Fin.lastCases ?_ ?_ i
      · change List.count (Fin.last s)
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count (Fin.last s) (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q (Fin.last s)
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc)]
        have hmem : Fin.last s ∉
            (layersOf (fun i : Fin s => i) (q ∘ Fin.castSucc)).map Fin.castSucc := by
          intro h
          rw [List.mem_map] at h
          rcases h with ⟨x, -, hx⟩
          exact (Fin.castSucc_lt_last x).ne hx
        rw [List.count_eq_zero_of_not_mem hmem, List.count_replicate]
        simp
      · intro j
        change List.count j.castSucc
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count j.castSucc (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q j.castSucc
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc),
          List.count_map_of_injective _ Fin.castSucc (Fin.castSucc_injective s) j,
          ih (q ∘ Fin.castSucc) j]
        have hne : Fin.last s ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
        rw [List.count_replicate]
        simp [hne]

/-! ### Expanding a multiplicity vector into a tuple -/

/-- Expand a multiplicity vector `q : Fin s → ℕ` into a tuple of length `∑ q + 1`: the entry at
position `0` is `b`, and the entries at positions `1` through `∑ q` are the layer operators
`f i`, each repeated `q i` times. -/
def expandTuple {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    Fin (∑ i : Fin s, q i + 1) → α :=
  Fin.cons b (fun t : Fin (∑ i : Fin s, q i) =>
    f ((layerIndices q)[t.val]'(by simp [layerIndices, layersOf_length])))

/-- The entry at position `0` of `expandTuple` is the innermost `b`. -/
lemma expandTuple_zero {α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    expandTuple f q b 0 = b := by
  simp [expandTuple]

/-- The entry at position `t + 1` of `expandTuple f q b` is `f` applied to the `t`-th layer
index. -/
lemma expandTuple_succ {α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) (t : ℕ)
    (ht : t < ∑ i : Fin s, q i) :
    expandTuple f q b ⟨t + 1, Nat.succ_lt_succ ht⟩ =
      f ((layersOf (fun i : Fin s => i) q)[t]'(by simpa [layersOf_length] using ht)) := by
  rw [expandTuple]
  rw [show (⟨t + 1, Nat.succ_lt_succ ht⟩ : Fin ((∑ i : Fin s, q i) + 1)) =
      Fin.succ (⟨t, ht⟩ : Fin (∑ i : Fin s, q i)) by simp]
  rw [Fin.cons_succ]
  congr

/-- `expandTuple` is natural in the target:
`expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b`. -/
lemma expandTuple_nat {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b := by
  funext j
  refine Fin.cases ?zero ?succ j
  · simp [Function.comp_apply, expandTuple_zero]
  · intro t
    change expandTuple (g ∘ f) q (g b) ⟨t.val + 1, by exact Nat.succ_lt_succ t.isLt⟩ =
      g (expandTuple f q b ⟨t.val + 1, by exact Nat.succ_lt_succ t.isLt⟩)
    rw [expandTuple_succ (g ∘ f) q (g b) t.val t.isLt]
    simp [expandTuple_succ f q b t.val t.isLt]

/-- `adSequence A q B` equals the list nested commutator of the layers. -/
lemma adSequence_eq_nestedCommOfList {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedCommOfList B (layersOf A q) := by
  induction s with
  | zero => simp [adSequence, layersOf]
  | succ s ih =>
      rw [adSequence, ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)]
      have hlayers : layersOf A q = layersOf (fun i : Fin s => A i.castSucc)
          (fun i : Fin s => q i.castSucc) ++
          List.replicate (q (Fin.last s)) (A (Fin.last s)) := by
        simp [layersOf, List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      rw [hlayers, nestedCommOfList_append_replicate]

/-- `adSequence A q B` is exactly the nested commutator of the expanded tuple. -/
lemma adSequence_eq_nestedComm_expandTuple {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedComm (expandTuple A q B) := by
  rw [adSequence_eq_nestedCommOfList A q B]
  rw [show layersOf A q = (layerIndices q).map A by
    rw [layerIndices]
    exact layersOf_map A (fun i : Fin s => i) q]
  rw [← nestedComm_listIndexed B (layerIndices q) A]
  rw [show expandTuple A q B =
      listIndexed B (layerIndices q) A ∘ Fin.cast (congrArg (· + 1)
        (show (∑ i : Fin s, q i) = (layerIndices q).length by
          rw [layerIndices, layersOf_length])) by
    ext j
    refine Fin.cases ?zero ?succ j
    · simp [expandTuple, listIndexed, Fin.cons_zero]
    · intro t
      simp [expandTuple, listIndexed, Fin.cons_succ, Fin.cast_succ_eq, Fin.val_cast]]
  rw [nestedComm_cast (show (∑ i : Fin s, q i) = (layerIndices q).length by
    rw [layerIndices, layersOf_length]) (listIndexed B (layerIndices q) A)]

/-! ### Coefficient-dropping for `αCommConj` -/

/-- `adPow (c • A) k X = c ^ k • adPow A k X`. -/
lemma adPow_smul_left {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (c : ℝ) (A : 𝔸) (k : ℕ) (X : 𝔸) :
    adPow (c • A) k X = c ^ k • adPow A k X := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [ad_pow_succ, ad_pow_succ, ih, smul_lie, lie_smul, smul_smul, pow_succ, mul_comm]

/-- `adSequence (fun i => c i • A i) q B = (∏ i, c i ^ q i) • adSequence A q B`. -/
lemma adSequence_smul_fun {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (c : Fin s → ℝ)
    (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) :
    adSequence (fun i => c i • A i) q B = (∏ i : Fin s, (c i) ^ q i) • adSequence A q B := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      rw [adSequence, adSequence, ih (fun i => c i.castSucc) (fun i => A i.castSucc)
          (fun i => q i.castSucc), adPow_smul_left, (adPow (A (Fin.last s))
          (q (Fin.last s))).map_smul, smul_smul, Fin.prod_univ_castSucc, mul_comm]

/-- `αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p` for `|c i| ≤ 1`. -/
lemma αCommConj_smul_fun_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (c : Fin s → ℝ) (A : Fin s → 𝔸) (hc : ∀ i, |c i| ≤ 1) (B : 𝔸) (p : ℕ) :
    αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  apply sum_le_sum
  intro q hq
  rw [adSequence_smul_fun c A q B, norm_smul, Real.norm_eq_abs]
  have hprod : |∏ i : Fin s, (c i) ^ q i| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one (fun i _ => abs_nonneg _) (fun i _ => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hc i))
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hprod) (Nat.cast_nonneg _)

/-- `αCommConj A (c • B) p ≤ αCommConj A B p` for `|c| ≤ 1`. -/
lemma αCommConj_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸) (c : ℝ) (hc : |c| ≤ 1) (B : 𝔸) (p : ℕ) :
    αCommConj A (c • B) p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  apply sum_le_sum
  intro q hq
  rw [adSequence_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hc) (Nat.cast_nonneg _)

/-- `αCommConj` is invariant under `Fin.cast` reindexing. -/
lemma αCommConj_cast {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s t : ℕ} (h : s = t) (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (fun i : Fin t => A (Fin.cast h.symm i)) B p = αCommConj A B p := by
  subst h
  simp [αCommConj]

/-! ### Sum-splitting and reindexing -/

/-- `adSequence A q (∑ γ, H γ) = ∑ γ, adSequence A q (H γ)`. -/
lemma adSequence_sum {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ)
    {ι : Type*} [Fintype ι] (H : ι → 𝔸) :
    adSequence A q (∑ γ : ι, H γ) = ∑ γ : ι, adSequence A q (H γ) := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      unfold adSequence
      rw [ih (fun i => A i.castSucc) (fun i => q i.castSucc)]
      change (adPow (A (Fin.last s)) (q (Fin.last s))).toAddMonoidHom
          (∑ γ : ι, adSequence (fun i => A i.castSucc) (fun i => q i.castSucc) (H γ)) =
        ∑ γ : ι, (adPow (A (Fin.last s)) (q (Fin.last s))).toAddMonoidHom
          (adSequence (fun i => A i.castSucc) (fun i => q i.castSucc) (H γ))
      exact map_sum (adPow (A (Fin.last s)) (q (Fin.last s))).toAddMonoidHom
        (fun γ : ι => adSequence (fun i => A i.castSucc) (fun i => q i.castSucc) (H γ))
        (univ : Finset ι)

/-- `αCommConj A (∑ γ, H γ) p ≤ ∑ γ, αCommConj A (H γ) p`. -/
lemma αCommConj_sum_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸) {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) :
    αCommConj A (∑ γ : ι, H γ) p ≤ ∑ γ : ι, αCommConj A (H γ) p := by
  rw [αCommConj]
  calc
    (∑ q ∈ finAntidiagonal s p,
        (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
          ‖adSequence A q (∑ γ : ι, H γ)‖)
        = ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              ‖∑ γ : ι, adSequence A q (H γ)‖ := by
              apply sum_congr rfl
              intro q hq
              rw [adSequence_sum A q H]
    _ ≤ ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              (∑ γ : ι, ‖adSequence A q (H γ)‖) := by
              apply sum_le_sum
              intro q hq
              exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ = ∑ γ : ι, ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              ‖adSequence A q (H γ)‖ := by
              simp_rw [mul_sum]
              rw [sum_comm]
    _ = ∑ γ : ι, αCommConj A (H γ) p := by rfl

/-! ### Suffix extension (peel innermost zeros) -/

/-- Prepending a zero multiplicity shifts the layers: the innermost `f 0` contributes nothing and
each `f (i.succ)` becomes the `i`-th layer. -/
lemma layersOf_cons_zero {α : Type*} {s : ℕ} (f : Fin (s + 1) → α) (q : Fin s → ℕ) :
    layersOf f (Fin.cons 0 q) = layersOf (fun i : Fin s => f i.succ) q := by
  rw [layersOf, layersOf, List.finRange_succ]
  simp only [List.flatMap_cons, List.flatMap_map, Fin.cons_zero, List.replicate_zero,
    List.nil_append]
  apply List.flatMap_congr
  intro j _
  simp

/-- `adSequence A (Fin.cons 0 q) B = adSequence (fun i => A i.succ) q B`: a zero innermost
multiplicity lets the innermost `A ⟨0⟩` drop out. -/
lemma adSequence_cons_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A (Fin.cons 0 q) B = adSequence (fun i : Fin s => A i.succ) q B := by
  rw [adSequence_eq_nestedCommOfList A (Fin.cons 0 q) B,
    adSequence_eq_nestedCommOfList (fun i : Fin s => A i.succ) q B]
  rw [layersOf_cons_zero A q]

/-- `Nat.multinomial (Fin.cons 0 q) = Nat.multinomial q`: prepending a zero multiplicity does not
change the multinomial coefficient. -/
lemma multinomial_cons_zero {s : ℕ} (q : Fin s → ℕ) :
    Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) =
      Nat.multinomial (univ : Finset (Fin s)) q := by
  unfold Nat.multinomial
  rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp [Nat.factorial_zero]

/-- Dropping the innermost summand does not increase `αCommConj`. -/
lemma αCommConj_succ_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (fun i : Fin s => A i.succ) B p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  calc
    (∑ q ∈ finAntidiagonal s p,
        (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
          ‖adSequence (fun i => A i.succ) q B‖)
        = ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) : ℝ) *
              ‖adSequence A (Fin.cons 0 q) B‖ := by
              apply sum_congr rfl
              intro q hq
              rw [adSequence_cons_zero A q B, multinomial_cons_zero q]
    _ = ∑ q' ∈ (finAntidiagonal s p).image (Fin.cons 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              rw [sum_image]
              intro q₁ hq₁ q₂ hq₂ h
              funext i
              simpa using (congrFun h (i.succ))
    _ ≤ ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro q hq
                rw [mem_image] at hq
                rcases hq with ⟨q₀, hq₀, rfl⟩
                rw [mem_finAntidiagonal]
                rw [mem_finAntidiagonal] at hq₀
                rw [Fin.sum_univ_succ]
                simpa using hq₀
              · intro q _ _
                exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- `αCommConj` of the last `n` entries of `A : Fin (m + n) → 𝔸` (indexed by `Fin.natAdd m`)
is bounded by the full `αCommConj`. -/
lemma αCommConj_natAdd_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {m n : ℕ} (A : Fin (m + n) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (A ∘ Fin.natAdd m) B p ≤ αCommConj A B p := by
  induction m with
  | zero =>
      rw [show A ∘ Fin.natAdd 0 = (fun i : Fin n => A (Fin.cast (Nat.zero_add n).symm i)) by
        funext i
        apply congrArg A
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast]
        exact Nat.zero_add i.val]
      exact (αCommConj_cast (Nat.zero_add n) A B p).le
  | succ m ih =>
      let e : (m + 1) + n = (m + n) + 1 := Nat.succ_add m n
      rw [show A ∘ Fin.natAdd (m + 1) =
          (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) ∘ Fin.natAdd m by
        funext i
        apply congrArg A
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
        exact Nat.succ_add m i.val]
      calc
        αCommConj ((fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) ∘ Fin.natAdd m) B p
            ≤ αCommConj (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) B p :=
                ih (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ))
        _ ≤ αCommConj (A ∘ Fin.cast e.symm) B p :=
                αCommConj_succ_le (A ∘ Fin.cast e.symm) B p
        _ = αCommConj A B p := αCommConj_cast e A B p

/-- `αCommConj A B p` is a sum of nonnegative terms, hence nonnegative. -/
lemma αCommConj_nonneg {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (p : ℕ) : 0 ≤ αCommConj A B p :=
  sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

end TrotterError
