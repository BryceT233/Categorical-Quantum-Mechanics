/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import CQM1.TrotterError.Commutator
public import CQM1.TrotterError.ProductFormula

/-!
# Ordering removal (`α_comm ≲ p!·Υ^p·α~_comm`)

The ordering-removal step of the main theorem (arXiv:1912.08854, `papers/rep.tex`
lines 129-139): the sum over innermost summands `H_γ` of the conjugation quantity
`α_comm` is bounded by `p! · Υ^p · α~_comm`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace Finset
open scoped BigOperators

/-! ### The tuple of summand indices of the product formula -/

/-- The antidiagonal of multiplicity vectors with total degree `p`. -/
abbrev Antidiag (s p : ℕ) : Type := {q : Fin s → ℕ // q ∈ finAntidiagonal s p}

/-- The `j`-th non-innermost layer index of a multiplicity vector on the antidiagonal. -/
noncomputable def layerAt (P : ProductFormulaData) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) (j : Fin p) : Fin (P.Υ * P.Γ) :=
  (layerIndices q.1)[j.val]'(by
    simp [layerIndices, layersOf_length, mem_finAntidiagonal.mp q.2])

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
    Fin.cast (congrArg (· + 1) (mem_finAntidiagonal.mp q.2).symm)

/-- The `(j + 1)`-st entry of `orderedLayers` is the permuted summand of the `j`-th layer. -/
lemma orderedLayers_succ (P : ProductFormulaData) (γ : Fin P.Γ) (p : ℕ)
    (q : Antidiag (P.Υ * P.Γ) p) (j : Fin p) :
    orderedLayers P γ p q j.succ =
      P.perm (stageOf P p q j) ((layerAt P p q j).modNat) := by
  rw [orderedLayers]
  simp only [Function.comp_apply]
  have hq : (∑ i : Fin (P.Υ * P.Γ), q.1 i) = p := mem_finAntidiagonal.mp q.2
  have ht : j.val < ∑ i : Fin (P.Υ * P.Γ), q.1 i := by
    simp [hq]
  rw [show Fin.cast (congrArg (· + 1) hq.symm) j.succ = ⟨j.val + 1, Nat.succ_lt_succ ht⟩ by
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
  rw [show Fin.cast (congrArg (· + 1) (mem_finAntidiagonal.mp q.2).symm)
      (0 : Fin (p + 1)) = (0 : Fin (∑ i : Fin (P.Υ * P.Γ), q.1 i + 1)) by
    apply Fin.ext
    simp]
  rw [expandTuple_zero]

/-- `adSequence (orderedSummands P H) q (H γ)` equals the nested commutator of `H` along the
tuple `orderedLayers`. -/
lemma adSequence_orderedSummands_eq_nestedComm (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸]
    [Algebra ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (γ : Fin P.Γ) (p : ℕ) (q : Antidiag (P.Υ * P.Γ) p) :
    adSequence (orderedSummands P H) q.1 (H γ) = nestedComm (H ∘ orderedLayers P γ p q) := by
  calc
    adSequence (orderedSummands P H) q.1 (H γ)
        = nestedComm (expandTuple (orderedSummands P H) q.1 (H γ)) :=
            adSequence_eq_nestedComm_expandTuple (orderedSummands P H) q.1 (H γ)
    _ = nestedComm (expandTuple
        (H ∘ fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 (H γ)) := rfl
    _ = nestedComm (H ∘ expandTuple
        (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) := by
            rw [expandTuple_nat H (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ]
    _ = nestedComm (H ∘ orderedLayers P γ p q) := by
            rw [orderedLayers]
            change nestedComm
              (H ∘ expandTuple (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) =
              nestedComm ((H ∘ expandTuple
                (fun i : Fin (P.Υ * P.Γ) => P.perm (i.divNat) (i.modNat)) q.1 γ) ∘
                Fin.cast (congrArg (· + 1) (mem_finAntidiagonal.mp q.2).symm))
            rw [← nestedComm_cast (mem_finAntidiagonal.mp q.2).symm]

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
  rw [hs, stageOf, show finProdFinEquiv ((layerAt P p q j).divNat, (layerAt P p q j).modNat) =
      layerAt P p q j by
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
    simp [mem_finAntidiagonal.mp q₁.2, mem_finAntidiagonal.mp q₂.2]
  · intro n hn₁ hn₂
    have h₁n : n < p := by simpa [layersOf_length, mem_finAntidiagonal.mp q₁.2] using hn₁
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
    (univ.filter (fun q : Antidiag (P.Υ * P.Γ) p => orderedLayers P γ p q = γ')).card ≤
      (P.Υ : ℕ) ^ p := by
  let s : Finset (Antidiag (P.Υ * P.Γ) p) :=
    univ.filter (fun q => orderedLayers P γ p q = γ')
  have hinj : Set.InjOn (fun q : Antidiag (P.Υ * P.Γ) p => stageOf P p q)
      (↑s : Set (Antidiag (P.Υ * P.Γ) p)) := by
    intro q₁ hq₁ q₂ hq₂ hstage
    have hOL₁ : orderedLayers P γ p q₁ = γ' := (mem_filter.mp hq₁).2
    have hOL₂ : orderedLayers P γ p q₂ = γ' := (mem_filter.mp hq₂).2
    exact orderedLayers_stageOf_injective P γ p (Prod.ext (hOL₁.trans hOL₂.symm) hstage)
  have hcard : s.card ≤ (univ : Finset (Fin p → Fin P.Υ)).card := by
    refine card_le_card_of_injOn (fun q => stageOf P p q) ?_ hinj
    intro q hq
    simp
  calc
    s.card ≤ (univ : Finset (Fin p → Fin P.Υ)).card := hcard
    _ = (P.Υ : ℕ) ^ p := by
        rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ### The ordering-removal bound -/

/-- The multinomial-weighted `α_comm` is bounded by `p!` times the unweighted sum of the norms. -/
lemma αCommConj_le_mul_sum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (p : ℕ) :
    αCommConj A B p ≤
      (Nat.factorial p : ℝ) * ∑ q ∈ finAntidiagonal s p, ‖adSequence A q B‖ := by
  rw [αCommConj, mul_sum]
  refine sum_le_sum (fun q hq => ?_)
  have hsum : (∑ i : Fin s, q i) = p := mem_finAntidiagonal.mp hq
  have hle : (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) ≤ (Nat.factorial p : ℝ) := by
    have hnat : Nat.multinomial (univ : Finset (Fin s)) q ≤ Nat.factorial p := by
      simpa [hsum] using multinomial_le_factorial (univ : Finset (Fin s)) q
    exact_mod_cast hnat
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- For each `γ`, the sum over all `q` of the nested-commutator norms is bounded by
`Υ^p · Σ_{γ' : γ'⟨0⟩=γ} ‖nestedComm (H ∘ γ')‖` (the paper's rep.tex:135–137). -/
lemma sum_adSequence_norm_le (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (γ : Fin P.Γ) (p : ℕ) :
    (∑ q ∈ finAntidiagonal (P.Υ * P.Γ) p, ‖adSequence (orderedSummands P H) q (H γ)‖) ≤
      (P.Υ : ℝ) ^ p *
        (∑ γ' ∈ univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
          ‖nestedComm (H ∘ γ')‖) := by
  let g : Antidiag (P.Υ * P.Γ) p → Fin (p + 1) → Fin P.Γ := orderedLayers P γ p
  let A : Finset (Antidiag (P.Υ * P.Γ) p) := (finAntidiagonal (P.Υ * P.Γ) p).attach
  let t : Finset (Fin (p + 1) → Fin P.Γ) := univ.filter (fun γ' => γ' 0 = γ)
  calc
    (∑ q ∈ finAntidiagonal (P.Υ * P.Γ) p, ‖adSequence (orderedSummands P H) q (H γ)‖)
        = ∑ q ∈ A, ‖nestedComm (H ∘ g q)‖ := by
            rw [← sum_attach]
            refine sum_congr rfl (fun q hq => ?_)
            rw [adSequence_orderedSummands_eq_nestedComm]
    _ = ∑ γ' ∈ t, ∑ q ∈ A with g q = γ', ‖nestedComm (H ∘ g q)‖ := by
            rw [sum_fiberwise_of_maps_to (fun q hq => by simp [g, t, orderedLayers_zero])]
    _ = ∑ γ' ∈ t, ∑ q ∈ A with g q = γ', ‖nestedComm (H ∘ γ')‖ := by
            refine sum_congr rfl (fun γ' hγ' => ?_)
            refine sum_congr rfl (fun q hq => ?_)
            rw [(mem_filter.mp hq).2]
    _ ≤ ∑ γ' ∈ t, (P.Υ : ℝ) ^ p * ‖nestedComm (H ∘ γ')‖ := by
            refine sum_le_sum (fun γ' hγ' => ?_)
            have hcard : (A.filter (fun q => g q = γ')).card ≤ (P.Υ : ℕ) ^ p := by
              simpa [A, g] using fiber_card_le P γ p γ'
            rw [sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)
    _ = (P.Υ : ℝ) ^ p * (∑ γ' ∈ t, ‖nestedComm (H ∘ γ')‖) := by
            rw [mul_sum]

/-- rep.tex:129-139 (ordering removal): the sum over innermost summands of the conjugation
`α_comm` is bounded by `p! · Υ^p · α~_comm` — each multinomial coefficient is ≤ `p!`, and each
nested-commutator pattern recurs in at most `Υ^p` stage placements. -/
theorem αCommConj_sum_le_αComm (P : ProductFormulaData) {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (H : Fin P.Γ → 𝔸) (p : ℕ) :
    (∑ γ : Fin P.Γ, αCommConj (orderedSummands P H) (H γ) p) ≤
      (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p * αComm p H := by
  have hfiber :
      (∑ γ : Fin P.Γ, ∑ γ' ∈ univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
          ‖nestedComm (H ∘ γ')‖) = ∑ γ' : Fin (p + 1) → Fin P.Γ, ‖nestedComm (H ∘ γ')‖ := by
    simpa using (sum_fiberwise (univ : Finset (Fin (p + 1) → Fin P.Γ))
      (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0)
      (fun γ' : Fin (p + 1) → Fin P.Γ => ‖nestedComm (H ∘ γ')‖))
  calc
    (∑ γ : Fin P.Γ, αCommConj (orderedSummands P H) (H γ) p)
        ≤ ∑ γ : Fin P.Γ, (Nat.factorial p : ℝ) *
            (∑ q ∈ finAntidiagonal (P.Υ * P.Γ) p,
              ‖adSequence (orderedSummands P H) q (H γ)‖) := sum_le_sum
              (fun γ hγ => αCommConj_le_mul_sum (orderedSummands P H) (H γ) p)
    _ = (Nat.factorial p : ℝ) * ∑ γ : Fin P.Γ,
            (∑ q ∈ finAntidiagonal (P.Υ * P.Γ) p,
              ‖adSequence (orderedSummands P H) q (H γ)‖) := by rw [mul_sum]
    _ ≤ (Nat.factorial p : ℝ) * ∑ γ : Fin P.Γ,
            ((P.Υ : ℝ) ^ p *
              (∑ γ' ∈ univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
                ‖nestedComm (H ∘ γ')‖)) := mul_le_mul_of_nonneg_left
              (sum_le_sum (fun γ hγ => sum_adSequence_norm_le P H γ p))
              (Nat.cast_nonneg _)
    _ = (Nat.factorial p : ℝ) * ((P.Υ : ℝ) ^ p *
          (∑ γ : Fin P.Γ,
            (∑ γ' ∈ univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
              ‖nestedComm (H ∘ γ')‖))) := by rw [← mul_sum]
    _ = (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p *
          (∑ γ : Fin P.Γ,
            (∑ γ' ∈ univ.filter (fun γ' : Fin (p + 1) → Fin P.Γ => γ' 0 = γ),
              ‖nestedComm (H ∘ γ')‖)) := by ring
    _ = (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p *
          (∑ γ' : Fin (p + 1) → Fin P.Γ, ‖nestedComm (H ∘ γ')‖) := by rw [hfiber]
    _ = (Nat.factorial p : ℝ) * (P.Υ : ℝ) ^ p * αComm p H := by rw [αComm]

end TrotterError
