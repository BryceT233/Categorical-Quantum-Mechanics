/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.Commutator
public import CQM1.TrotterError.ProductFormula

/-!
# Main theorem: ordering-removal lemma

This file proves the "ordering removal" step of the main theorem of *A Theory of Trotter
Error* (arXiv:1912.08854), `papers/rep.tex` lines 129–139.

The paper's `α_comm` quantity is the multinomial-weighted sum over all multiplicities
`q : Fin (Υ·Γ) → ℕ` with `Σ q = p` of the norms of the iterated `ad` operators
`ad_{H_{π_1(1)}}^{q_(1,1)} ⋯ ad_{H_{π_Υ(Γ)}}^{q_(Υ,Γ)}(H_γ)`. The main lemma bounds the sum
over the innermost summand `H_γ` of this quantity by `p! · Υ^p · α~_comm`, where `α~_comm`
is the sum over all nested commutators `‖[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_γ]]‖`.

The two ingredients are: (1) each multinomial coefficient `(p choose q)` is at most `p!`;
(2) each nested commutator `[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_γ]]` arises from at most `Υ^p`
different multiplicity vectors `q` (each of the `p` outer operators can sit in any of the `Υ`
stages, and the stage then determines the position and multiplicity).

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

/-! ### The ordered list of permuted summands -/

/-- The product formula's permuted summands `H_{π_υ(γ)}`, as a `Fin (Υ * Γ)`-indexed list in
`evalIndexList` order (the paper's `\overrightarrow{\{H_{π_υ(γ)}\}}`). The index
`i = υ * Γ + γ` carries the summand `H_{π_υ(γ)}`; `i.divNat` is the stage and `i.modNat` the
summand index within the stage. -/
noncomputable def orderedSummands (P : ProductFormulaData) {𝔸 : Type*} (H : Fin P.Γ → 𝔸) :
    Fin (P.Υ * P.Γ) → 𝔸 :=
  fun i => H (P.perm (i.divNat) (i.modNat))

/-! ### Multinomial coefficients are bounded by `p!` -/

/-- Every multinomial coefficient is at most the factorial of the total degree: the multinomial
`Nat.multinomial s f` divides `(∑ f)!` (via `Nat.multinomial_spec`), and the complementary product
of factorials is `≥ 1`. -/
lemma multinomial_le_factorial {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.multinomial s f ≤ Nat.factorial (∑ i ∈ s, f i) := by
  have hspec := Nat.multinomial_spec s f
  have hprod : 1 ≤ ∏ i ∈ s, (f i).factorial := Finset.one_le_prod (fun i _ => Nat.factorial_pos _)
  calc
    Nat.multinomial s f = Nat.multinomial s f * 1 := by rw [mul_one]
    _ ≤ Nat.multinomial s f * (∏ i ∈ s, (f i).factorial) := Nat.mul_le_mul_left _ hprod
    _ = (∏ i ∈ s, (f i).factorial) * Nat.multinomial s f := by rw [mul_comm]
    _ = (∑ i ∈ s, f i).factorial := hspec

/-! ### The list of layer indices -/

/-- The list of the non-innermost operators of `expandTuple f q b`, each `f i` repeated `q i`
times, in increasing order of `i`. -/
def layersOf {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) : List α :=
  (List.finRange s).flatMap fun i => List.replicate (q i) (f i)

/-- `layersOf f q` has length `∑ q`. -/
lemma layersOf_length {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) :
    (layersOf f q).length = ∑ i : Fin s, q i := by
  induction s with
  | zero => simp [layersOf]
  | succ s ih =>
      rw [layersOf, List.finRange_succ]
      simp only [List.flatMap_cons, List.flatMap_map, List.length_append, List.length_replicate]
      change q 0 + (layersOf (f ∘ Fin.succ) (q ∘ Fin.succ)).length = ∑ i : Fin (s + 1), q i
      rw [ih (f ∘ Fin.succ) (q ∘ Fin.succ)]
      rw [Fin.sum_univ_succ]
      rfl

/-- `layersOf` commutes with post-composition. -/
lemma layersOf_map {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) :
    layersOf (g ∘ f) q = (layersOf f q).map g := by
  rw [layersOf, layersOf]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  rw [List.map_replicate]
  rfl

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
        rw [List.count_eq_zero_of_not_mem hmem]
        rw [List.count_replicate]
        simp
      · intro j
        change List.count j.castSucc
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count j.castSucc (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q j.castSucc
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc)]
        rw [List.count_map_of_injective _ Fin.castSucc (Fin.castSucc_injective s) j]
        rw [ih (q ∘ Fin.castSucc) j]
        have hne : Fin.last s ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
        rw [List.count_replicate]
        simp [hne]

/-! ### Expanding a multiplicity vector into a tuple -/

/-- Expand a multiplicity vector `q : Fin s → ℕ` into a tuple of length `∑ q + 1`: the entry at
position `0` is `b`, and the entries at positions `1` through `∑ q` are the layer operators
`f i`, each repeated `q i` times. -/
def expandTuple {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
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
      Fin.succ (⟨t, ht⟩ : Fin (∑ i : Fin s, q i)) by rfl]
  rw [Fin.cons_succ]
  rfl

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
    rw [expandTuple_succ f q b t.val t.isLt]
    rfl

/-- `adSequence A q B` equals the list nested commutator of the layers. -/
lemma adSequence_eq_nestedCommOfList {𝔸 : Type*} [Ring 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedCommOfList B (layersOf A q) := by
  induction s with
  | zero => simp [adSequence, layersOf]
  | succ s ih =>
      rw [adSequence]
      rw [ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)]
      have hlayers : layersOf A q = layersOf (fun i : Fin s => A i.castSucc)
          (fun i : Fin s => q i.castSucc) ++
          List.replicate (q (Fin.last s)) (A (Fin.last s)) := by
        simp [layersOf, List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      rw [hlayers, nestedCommOfList_append_replicate]

/-- `adSequence A q B` is exactly the nested commutator of the expanded tuple. -/
lemma adSequence_eq_nestedComm_expandTuple {𝔸 : Type*} [Ring 𝔸] {s : ℕ} (A : Fin s → 𝔸)
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

/-! ### The tuple of summand indices of the product formula -/

/-- The antidiagonal of multiplicity vectors with total degree `p`. -/
abbrev Antidiag (s p : ℕ) : Type := {q : Fin s → ℕ // q ∈ Finset.finAntidiagonal s p}

/-- The `j`-th non-innermost layer index of a multiplicity vector on the antidiagonal. -/
noncomputable def layerAt (P : ProductFormulaData) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) (j : Fin p) : Fin (P.Υ * P.Γ) :=
  (layerIndices q.1)[j.val]'(by
    simp [layerIndices, layersOf_length, Finset.mem_finAntidiagonal.mp q.2])

/-- The stage of the `j`-th non-innermost layer. -/
noncomputable def stageOf (P : ProductFormulaData) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) (j : Fin p) : Fin P.Υ :=
  (layerAt P p q j).divNat

/-- The tuple `Fin (p + 1) → Fin Γ` realizing `adSequence (orderedSummands P H) q (H γ)` as
`nestedComm (H ∘ ·)`: entry `0` is `γ` (the innermost `H_γ`), and entry `j + 1` is
`π_υ(γ')` where `(υ, γ')` is the stage/summand of the `j`-th layer. -/
noncomputable def orderedLayers (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) : Fin (p + 1) → Fin P.Γ :=
  (expandTuple (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) ∘
    Fin.cast (congrArg (· + 1) (Finset.mem_finAntidiagonal.mp q.2).symm)

/-- The `(j + 1)`-st entry of `orderedLayers` is the permuted summand of the `j`-th layer. -/
lemma orderedLayers_succ (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) (j : Fin p) :
    orderedLayers P γ p q j.succ =
      P.perm (stageOf P p q j) ((layerAt P p q j).modNat) := by
  rw [orderedLayers]
  simp only [Function.comp_apply]
  have hq : (∑ i : Fin (P.Υ * P.Γ), q.1 i) = p := Finset.mem_finAntidiagonal.mp q.2
  have ht : j.val < ∑ i : Fin (P.Υ * P.Γ), q.1 i := by
    simp [hq]
  rw [show Fin.cast (congrArg (· + 1) hq.symm) j.succ = ⟨j.val + 1, Nat.succ_lt_succ ht⟩ from by
    apply Fin.ext
    simp [Fin.val_cast, Fin.val_succ]]
  rw [expandTuple_succ (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ j.val ht]
  simp [layerAt, stageOf, layerIndices]

/-- The entry at position `0` of `orderedLayers` is the innermost summand `γ`. -/
lemma orderedLayers_zero (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) :
    orderedLayers P γ p q 0 = γ := by
  rw [orderedLayers]
  simp only [Function.comp_apply]
  rw [show Fin.cast (congrArg (· + 1) (Finset.mem_finAntidiagonal.mp q.2).symm)
      (0 : Fin (p + 1)) = (0 : Fin (∑ i : Fin (P.Υ * P.Γ), q.1 i + 1)) by
    apply Fin.ext
    simp]
  rw [expandTuple_zero]

/-- `adSequence (orderedSummands P H) q (H γ)` equals the nested commutator of `H` along the
tuple `orderedLayers`. -/
lemma adSequence_orderedSummands_eq_nestedComm (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    (H : Fin P.Γ → 𝔸) (γ : Fin P.Γ) (p : ℕ) (q : Antidiag (P.Υ * P.Γ) p) :
    adSequence (orderedSummands P H) q.1 (H γ) = nestedComm (H ∘ orderedLayers P γ p q) := by
  calc
    adSequence (orderedSummands P H) q.1 (H γ)
        = nestedComm (expandTuple (orderedSummands P H) q.1 (H γ)) :=
            adSequence_eq_nestedComm_expandTuple (orderedSummands P H) q.1 (H γ)
    _ = nestedComm (expandTuple
        (H ∘ fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 (H γ)) := by
            rfl
    _ = nestedComm (H ∘ expandTuple
        (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) := by
            rw [expandTuple_nat H (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ]
    _ = nestedComm (H ∘ orderedLayers P γ p q) := by
            rw [orderedLayers]
            change nestedComm
              (H ∘ expandTuple (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) =
              nestedComm ((H ∘ expandTuple
                (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) ∘
                Fin.cast (congrArg (· + 1) (Finset.mem_finAntidiagonal.mp q.2).symm))
            rw [← nestedComm_cast (Finset.mem_finAntidiagonal.mp q.2).symm]

/-- The layer index is determined by the tuple and the stage assignment. -/
lemma layerAt_eq_of_orderedLayers_stageOf (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) (j : Fin p) :
    layerAt P p q j =
      finProdFinEquiv
        (stageOf P p q j, (P.perm (stageOf P p q j)).symm (orderedLayers P γ p q j.succ)) := by
  rw [orderedLayers_succ P γ p q j]
  have hs : (P.perm (stageOf P p q j)).symm (P.perm (stageOf P p q j) ((layerAt P p q j).modNat)) =
      (layerAt P p q j).modNat :=
    Equiv.symm_apply_apply (P.perm (stageOf P p q j)) ((layerAt P p q j).modNat)
  rw [hs]
  rw [stageOf]
  rw [show finProdFinEquiv ((layerAt P p q j).divNat, (layerAt P p q j).modNat) =
      layerAt P p q j from by
    simpa [finProdFinEquiv_symm_apply] using (finProdFinEquiv.apply_symm_apply (layerAt P p q j))]

/-- On the antidiagonal, `q ↦ (orderedLayers q, stageOf q)` is injective. -/
lemma orderedLayers_stageOf_injective (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ) :
    Function.Injective
      (fun q : Antidiag (P.Υ * P.Γ) p => (orderedLayers P γ p q, stageOf P p q)) := by
  intro q₁ q₂ h
  have hOL : orderedLayers P γ p q₁ = orderedLayers P γ p q₂ := congrArg Prod.fst h
  have hS : stageOf P p q₁ = stageOf P p q₂ := congrArg Prod.snd h
  apply Subtype.ext
  funext i
  rw [← layersOf_count q₁.1 i, ← layersOf_count q₂.1 i]
  congr 1
  apply List.ext_getElem
  · rw [layersOf_length, layersOf_length]
    simp [Finset.mem_finAntidiagonal.mp q₁.2, Finset.mem_finAntidiagonal.mp q₂.2]
  · intro n hn₁ hn₂
    have h₁n : n < p := by simpa [layersOf_length, Finset.mem_finAntidiagonal.mp q₁.2] using hn₁
    let j : Fin p := ⟨n, h₁n⟩
    have hl₁ := layerAt_eq_of_orderedLayers_stageOf P γ p q₁ j
    have hl₂ := layerAt_eq_of_orderedLayers_stageOf P γ p q₂ j
    have hl : layerAt P p q₁ j = layerAt P p q₂ j := by
      rw [hl₁, hl₂]
      apply congrArg finProdFinEquiv
      apply Prod.ext
      · exact congr_fun hS j
      · rw [congr_fun hS j, congr_fun hOL j.succ]
    simpa [layerAt, layerIndices] using hl

/-- For a fixed target tuple `γ'`, at most `Υ^p` multiplicity vectors `q` have
`orderedLayers q = γ'`. -/
lemma fiber_card_le (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ)
    (γ' : Fin (p + 1) → Fin P.Γ) :
    (Finset.univ.filter (fun q : Antidiag (P.Υ * P.Γ) p => orderedLayers P γ p q = γ')).card ≤
      (P.Υ : ℕ) ^ p := by
  let s : Finset (Antidiag (P.Υ * P.Γ) p) :=
    Finset.univ.filter (fun q => orderedLayers P γ p q = γ')
  have hinj : Set.InjOn (fun q : Antidiag (P.Υ * P.Γ) p => stageOf P p q)
      (↑s : Set (Antidiag (P.Υ * P.Γ) p)) := by
    intro q₁ hq₁ q₂ hq₂ hstage
    have hOL₁ : orderedLayers P γ p q₁ = γ' := (Finset.mem_filter.mp hq₁).2
    have hOL₂ : orderedLayers P γ p q₂ = γ' := (Finset.mem_filter.mp hq₂).2
    apply orderedLayers_stageOf_injective P γ p
    change (orderedLayers P γ p q₁, stageOf P p q₁) = (orderedLayers P γ p q₂, stageOf P p q₂)
    exact Prod.ext (hOL₁.trans hOL₂.symm) hstage
  have hcard : s.card ≤ (Finset.univ : Finset (Fin p → Fin P.Υ)).card := by
    refine Finset.card_le_card_of_injOn (fun q => stageOf P p q) ?_ hinj
    intro q hq
    simp
  calc
    s.card ≤ (Finset.univ : Finset (Fin p → Fin P.Υ)).card := hcard
    _ = (P.Υ : ℕ) ^ p := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ### The ordering-removal bound -/

/-- The multinomial-weighted `α_comm` is bounded by `p!` times the unweighted sum of the norms. -/
lemma alphaCommConj_le_mul_sum {𝔸 : Type*} [NormedRing 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (p : ℕ) :
    alphaCommConj A B p ≤
      (Nat.factorial p : ℝ) * ∑ q ∈ Finset.finAntidiagonal s p, ‖adSequence A q B‖ := by
  rw [alphaCommConj]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun q hq => ?_)
  have hsum : (∑ i : Fin s, q i) = p := Finset.mem_finAntidiagonal.mp hq
  have hle : (Nat.multinomial (Finset.univ : Finset (Fin s)) q : ℝ) ≤ (Nat.factorial p : ℝ) := by
    have hnat : Nat.multinomial (Finset.univ : Finset (Fin s)) q ≤ Nat.factorial p := by
      simpa [hsum] using multinomial_le_factorial (Finset.univ : Finset (Fin s)) q
    exact_mod_cast hnat
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- For each `γ`, the sum over all `q` of the nested-commutator norms is bounded by
`Υ^p · Σ_{γ' : γ'⟨0⟩=γ} ‖nestedComm (H ∘ γ')‖` (the paper's rep.tex:135–137). -/
lemma sum_adSequence_norm_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    (H : Fin P.Γ → 𝔸) (γ : Fin P.Γ) (p : ℕ) :
    (∑ q ∈ Finset.finAntidiagonal (P.Υ * P.Γ) p, ‖adSequence (orderedSummands P H) q (H γ)‖) ≤
      (P.Υ : ℝ) ^ p *
        (∑ γ' ∈ Finset.univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
          ‖nestedComm (H ∘ γ')‖) := by
  let g : Antidiag (P.Υ * P.Γ) p → Fin (p + 1) → Fin P.Γ := orderedLayers P γ p
  let A : Finset (Antidiag (P.Υ * P.Γ) p) := (Finset.finAntidiagonal (P.Υ * P.Γ) p).attach
  let t : Finset (Fin (p + 1) → Fin P.Γ) := Finset.univ.filter (fun γ' => γ' 0 = γ)
  calc
    (∑ q ∈ Finset.finAntidiagonal (P.Υ * P.Γ) p, ‖adSequence (orderedSummands P H) q (H γ)‖)
        = ∑ q ∈ A, ‖nestedComm (H ∘ g q)‖ := by
            rw [← Finset.sum_attach]
            refine Finset.sum_congr rfl (fun q hq => ?_)
            rw [adSequence_orderedSummands_eq_nestedComm]
    _ = ∑ γ' ∈ t, ∑ q ∈ A with g q = γ', ‖nestedComm (H ∘ g q)‖ := by
            rw [Finset.sum_fiberwise_of_maps_to (fun q hq => by simp [g, t, orderedLayers_zero])]
    _ = ∑ γ' ∈ t, ∑ q ∈ A with g q = γ', ‖nestedComm (H ∘ γ')‖ := by
            refine Finset.sum_congr rfl (fun γ' hγ' => ?_)
            refine Finset.sum_congr rfl (fun q hq => ?_)
            rw [(Finset.mem_filter.mp hq).2]
    _ ≤ ∑ γ' ∈ t, (P.Υ : ℝ) ^ p * ‖nestedComm (H ∘ γ')‖ := by
            refine Finset.sum_le_sum (fun γ' hγ' => ?_)
            have hcard : (A.filter (fun q => g q = γ')).card ≤ (P.Υ : ℕ) ^ p := by
              simpa [A, g] using fiber_card_le P γ p γ'
            rw [Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)
    _ = (P.Υ : ℝ) ^ p * (∑ γ' ∈ t, ‖nestedComm (H ∘ γ')‖) := by
            rw [Finset.mul_sum]

/-- rep.tex:129-139 (ordering removal): the sum over innermost summands of the conjugation
`α_comm` is bounded by `p! · Υ^p · α~_comm` — each multinomial coefficient is ≤ `p!`, and each
nested-commutator pattern recurs in at most `Υ^p` stage placements. -/
theorem alphaCommConj_sum_le_alphaComm (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) :
    (∑ γ : Fin P.Γ, alphaCommConj (orderedSummands P H) (H γ) p) ≤
      (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p * alphaComm p H := by
  have hfiber :
      (∑ γ : Fin P.Γ, ∑ γ' ∈ Finset.univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
          ‖nestedComm (H ∘ γ')‖) = ∑ γ' : Fin (p + 1) → Fin P.Γ, ‖nestedComm (H ∘ γ')‖ := by
    simpa using (Finset.sum_fiberwise (Finset.univ : Finset (Fin (p + 1) → Fin P.Γ))
      (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0)
      (fun γ' : Fin (p + 1) → Fin P.Γ => ‖nestedComm (H ∘ γ')‖))
  calc
    (∑ γ : Fin P.Γ, alphaCommConj (orderedSummands P H) (H γ) p)
        ≤ ∑ γ : Fin P.Γ, (Nat.factorial p : ℝ) *
            (∑ q ∈ Finset.finAntidiagonal (P.Υ * P.Γ) p,
              ‖adSequence (orderedSummands P H) q (H γ)‖) := by
            refine Finset.sum_le_sum
              (fun γ hγ => alphaCommConj_le_mul_sum (orderedSummands P H) (H γ) p)
    _ = (Nat.factorial p : ℝ) * ∑ γ : Fin P.Γ,
            (∑ q ∈ Finset.finAntidiagonal (P.Υ * P.Γ) p,
              ‖adSequence (orderedSummands P H) q (H γ)‖) := by
            rw [Finset.mul_sum]
    _ ≤ (Nat.factorial p : ℝ) * ∑ γ : Fin P.Γ,
            ((P.Υ : ℝ) ^ p *
              (∑ γ' ∈ Finset.univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
                ‖nestedComm (H ∘ γ')‖)) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun γ hγ => sum_adSequence_norm_le P H γ p))
              (Nat.cast_nonneg _)
    _ = (Nat.factorial p : ℝ) * ((P.Υ : ℝ) ^ p *
          (∑ γ : Fin P.Γ,
            (∑ γ' ∈ Finset.univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
              ‖nestedComm (H ∘ γ')‖))) := by
            rw [← Finset.mul_sum]
    _ = (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p *
          (∑ γ : Fin P.Γ,
            (∑ γ' ∈ Finset.univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
              ‖nestedComm (H ∘ γ')‖)) := by
            ring
    _ = (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p *
          (∑ γ' : Fin (p + 1) → Fin P.Γ, ‖nestedComm (H ∘ γ')‖) := by
            rw [hfiber]
    _ = (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p * alphaComm p H := by
            rw [alphaComm]

end TrotterError
