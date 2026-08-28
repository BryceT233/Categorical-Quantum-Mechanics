/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Multinomial

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Calculus for normed algebra exponentials

Generic calculus lemmas for the exponential `NormedSpace.exp` in a normed algebra,
used in the Trotter error theory (arXiv:1912.08854).

## Main results

* `iteratedDeriv_exp_smul_const`: the `q`-th iterated derivative of `u ↦ exp (u • A)`.
* `iteratedDeriv_ofFn_prod`, `iteratedDeriv_list_prod_general`:
  the multinomial Leibniz expansion of the `n`-th iterated derivative of a finite product.
* `sum_piAntidiag_univ_equiv`, `multinomial_univ_equiv`: reindexing `piAntidiag` sums and
  multinomial coefficients by an equivalence of the index type.
* `contDiffAt_exp_smul_const`: `u ↦ exp (u • A)` is `C^m` at every point.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

open NormedSpace
open Asymptotics
open scoped Topology BigOperators ContDiff

/-- The `q`-th iterated derivative of `u ↦ exp (u • A)` is `u ↦ A^q * exp (u • A)`. -/
theorem iteratedDeriv_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (q : ℕ) :
    iteratedDeriv q (fun u : ℝ => exp (u • A)) = fun u : ℝ => A ^ q * exp (u • A) := by
  induction q with
  | zero =>
      simp [iteratedDeriv_zero]
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((hasDerivAt_exp_smul_const' A t).const_mul (A ^ q)).deriv]
      simp [pow_succ, mul_assoc]

/-! ### Multinomial Leibniz expansion for finite products -/

/-- `ContDiffAt` for the pointwise product of a finite list of functions. -/
lemma contDiffAt_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    ContDiffAt ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (1 : 𝔸)) t)
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ContDiffAt.mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

/-- A natural-number cast factors through the real scalar action:
`(a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y)`. -/
lemma natCast_mul_smul_eq {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (a b : ℕ) (x y : 𝔸) :
    (a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y) := by
  rw [(algebraMap.coe_natCast (R := ℝ) (A := 𝔸) a).symm, ← Algebra.smul_def (a : ℝ) x,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← Nat.cast_mul]

/-- The multinomial coefficient is invariant under renaming the index type by an injective map. -/
lemma multinomial_image {α β : Type*} [DecidableEq β] (s : Finset α) (e : α → β)
    (he : Set.InjOn e s) (f : β → ℕ) :
    Nat.multinomial (s.image e) f = Nat.multinomial s (f ∘ e) := by
  simp [Nat.multinomial, Finset.sum_image he, Finset.prod_image he, Function.comp_apply]

/-- The multinomial recursion for `Fin (m + 1)`, splitting off the index `0`. -/
lemma multinomial_fin_succ {m : ℕ} (k : ℕ) (q : Fin m → ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) =
      (k + ∑ i : Fin m, q i).choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q := by
  have huniv : (Finset.univ : Finset (Fin (m + 1))) =
      insert (0 : Fin (m + 1)) (Finset.univ.image (Fin.succ : Fin m → Fin (m + 1))) := by
    ext i
    simp [Fin.image_succ_univ]
  rw [huniv, Nat.multinomial_insert (show (0 : Fin (m + 1)) ∉
      Finset.univ.image (Fin.succ : Fin m → Fin (m + 1)) by
    simp [Fin.image_succ_univ])]
  simp only [Fin.cons_zero]
  have hinj : Set.InjOn (Fin.succ : Fin m → Fin (m + 1))
      (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro a _ b _ h
    exact Fin.succ_injective m h
  rw [Finset.sum_image hinj, multinomial_image (Finset.univ : Finset (Fin m))
    (Fin.succ : Fin m → Fin (m + 1)) hinj (Fin.cons k q)]
  have hsum :
      (∑ x : Fin m, ((Fin.cons k q : Fin (m + 1) → ℕ) (Fin.succ x))) = ∑ x : Fin m, q x := rfl
  have hcomp : ((Fin.cons k q : Fin (m + 1) → ℕ) ∘ Fin.succ) = q := rfl
  rw [hsum, hcomp]

/-- The antidiagonal of `Fin (m + 1)` fibers over that of `Fin m` by the value at `0`. -/
lemma sum_finAntidiagonal_succ {𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ)
    (G : (Fin (m + 1) → ℕ) → 𝔸) :
    (∑ q' ∈ Finset.finAntidiagonal (m + 1) n, G q') =
      ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k), G (Fin.cons k q) := by
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij (fun x _ => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_finAntidiagonal, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hx' : x.1 ∈ Finset.range (n + 1) ∧ x.2 ∈ Finset.finAntidiagonal m (n - x.1) :=
      Finset.mem_sigma.mp hx
    have hle : x.1 ≤ n := by simpa using Finset.mem_range.mp hx'.1
    have hsum : (∑ i : Fin m, x.2 i) = n - x.1 := by
      simpa using Finset.mem_finAntidiagonal.mp hx'.2
    rw [hsum, Nat.add_sub_of_le hle]
  · intro x₁ _ x₂ _ h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.mp h
    exact Sigma.ext h1 (heq_of_eq h2)
  · intro q' hq'
    have hsum : (∑ i : Fin (m + 1), q' i) = n := Finset.mem_finAntidiagonal.mp hq'
    have hsplit : q' 0 + (∑ i : Fin m, q' (Fin.succ i)) = n := by
      simpa [Fin.sum_univ_succ] using hsum
    refine ⟨⟨q' 0, Fin.tail q'⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_range]
        have hle : q' 0 ≤ n := by
          rw [← hsplit]
          exact Nat.le_add_right _ _
        exact Nat.lt_succ_of_le hle
      · rw [Finset.mem_finAntidiagonal]
        have htail : (∑ i : Fin m, q' (Fin.succ i)) = n - q' 0 := by
          rw [← hsplit, Nat.add_sub_cancel_left]
        simpa [Fin.tail] using htail
    · exact Fin.cons_self_tail q'
  · intro x _
    rfl

/-- The `Fin m` antidiagonal coincides with `piAntidiag` on `univ`. -/
lemma finAntidiagonal_eq_piAntidiag_univ (m n : ℕ) :
    Finset.finAntidiagonal m n = Finset.piAntidiag (Finset.univ : Finset (Fin m)) n := by
  ext f
  simp [Finset.mem_finAntidiagonal, Finset.mem_piAntidiag]

/-- The antidiagonal over the empty index type. -/
lemma finAntidiagonal_zero (n : ℕ) : Finset.finAntidiagonal 0 n = if n = 0 then {0} else ∅ := by
  ext f
  rw [Finset.mem_finAntidiagonal]
  by_cases h : n = 0
  · subst n
    simp [funext_iff]
  · simp only [if_neg h, Finset.notMem_empty, iff_false, Fin.sum_univ_zero]
    intro hsum
    exact h hsum.symm

/-- The `n`-th iterated derivative of a finite product of functions is the multinomial Leibniz
expansion, indexed by `Finset.finAntidiagonal`. -/
theorem iteratedDeriv_ofFn_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {m : ℕ} (f : Fin m → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i, ContDiffAt ℝ n (f i) t) :
    iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin m => f i t)).prod) t =
      ∑ q ∈ Finset.finAntidiagonal m n,
        (Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) •
          (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (f i) t)).prod := by
  induction m generalizing n t with
  | zero =>
      cases n with
      | zero => simp [iteratedDeriv_zero, finAntidiagonal_zero]
      | succ n => simp [iteratedDeriv_const, finAntidiagonal_zero]
  | succ m ih =>
      let g : Fin m → ℝ → 𝔸 := fun i => f i.succ
      calc
        iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin (m + 1) => f i t)).prod) t
            = iteratedDeriv n
                ((f 0) * (fun t : ℝ => (List.ofFn (fun i : Fin m => g i t)).prod)) t := by
                congr 1
                funext t
                rw [List.ofFn_succ]
                rfl
        _ = ∑ k ∈ Finset.range (n + 1), n.choose k * iteratedDeriv k (f 0) t *
              iteratedDeriv (n - k) (fun t : ℝ => (List.ofFn (fun i : Fin m => g i t)).prod) t := by
                rw [iteratedDeriv_mul (hf 0) (by
                  simpa [List.ofFn_eq_map] using
                    contDiffAt_list_prod (List.finRange m) g n t (fun i _ => hf i.succ))]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k),
              n.choose k * iteratedDeriv k (f 0) t *
                ((Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) •
                  (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (g i) t)).prod) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [ih g (n - k) t (fun i => (hf i.succ).of_le (mod_cast Nat.sub_le n k)),
                  Finset.mul_sum]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k),
              (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) : ℝ) •
                (List.ofFn (fun i : Fin (m + 1) =>
                  iteratedDeriv (((Fin.cons k q : Fin (m + 1) → ℕ) i)) (f i) t)).prod := by
                apply Finset.sum_congr rfl
                intro k hk
                apply Finset.sum_congr rfl
                intro q hq
                have hle : k ≤ n := by simpa using Finset.mem_range.mp hk
                have hqsum : (∑ i : Fin m, q i) = n - k := by
                  simpa using Finset.mem_finAntidiagonal.mp hq
                rw [natCast_mul_smul_eq (n.choose k)
                  (Nat.multinomial (Finset.univ : Finset (Fin m)) q)
                  (iteratedDeriv k (f 0) t)
                  ((List.ofFn (fun i : Fin m => iteratedDeriv (q i) (g i) t)).prod)]
                have hrec : Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) =
                    n.choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q := by
                  rw [multinomial_fin_succ, hqsum, Nat.add_sub_of_le hle]
                rw [hrec]
                congr 1
                rw [List.ofFn_succ]
                simp [g, Fin.cons_zero, Fin.cons_succ]
        _ = ∑ q' ∈ Finset.finAntidiagonal (m + 1) n,
              (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) q' : ℝ) •
                (List.ofFn (fun i : Fin (m + 1) => iteratedDeriv (q' i) (f i) t)).prod := by
                rw [sum_finAntidiagonal_succ m n (fun q' =>
                  (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) q' : ℝ) •
                    (List.ofFn (fun i : Fin (m + 1) => iteratedDeriv (q' i) (f i) t)).prod)]

/-- The `n`-th iterated derivative of the product of a family indexed by an arbitrary list `l`
is the multinomial Leibniz expansion, with multi-indices indexed by the positions `Fin l.length`. -/
theorem iteratedDeriv_list_prod_general {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    iteratedDeriv n (fun t : ℝ => (l.map (fun i => f i t)).prod) t =
      ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin l.length)) n,
        (Nat.multinomial (Finset.univ : Finset (Fin l.length)) q : ℝ) •
          (List.ofFn (fun j : Fin l.length => iteratedDeriv (q j) (f (l.get j)) t)).prod := by
  have hprod : (fun t : ℝ => (List.ofFn (fun j : Fin l.length => f (l.get j) t)).prod) =
      fun t : ℝ => (l.map (fun i => f i t)).prod := by
    funext t
    congr 1
    simpa using (List.ofFn_getElem_eq_map l (fun i : ι => f i t))
  rw [← hprod]
  simpa [finAntidiagonal_eq_piAntidiag_univ] using
    iteratedDeriv_ofFn_prod (fun j : Fin l.length => f (l.get j)) n t
      (fun j => hf (l.get j) (List.get_mem l j))

/-- Reindexing a sum over `Finset.piAntidiag univ` by an equivalence of the index type. -/
lemma sum_piAntidiag_univ_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (e : α ≃ β) (n : ℕ) {𝕄 : Type*} [AddCommMonoid 𝕄] (G : (α → ℕ) → 𝕄) :
    (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset α) n, G q) =
      ∑ q' ∈ Finset.piAntidiag (Finset.univ : Finset β) n, G (q' ∘ e) := by
  refine Finset.sum_bij (fun q _ => q ∘ e.symm) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_piAntidiag] at hq ⊢
    constructor
    · exact (Equiv.sum_comp e.symm q).trans hq.1
    · intro b hb
      simp
  · intro q₁ hq₁ q₂ hq₂ h
    funext x
    have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [hx]
    exact congr_fun h (e x)
  · intro q' hq'
    refine ⟨q' ∘ e, ?_, ?_⟩
    · rw [Finset.mem_piAntidiag] at hq' ⊢
      constructor
      · exact (Equiv.sum_comp e q').trans hq'.1
      · intro a ha; simp
    · ext b; simp
  · intro q hq
    apply congrArg G
    funext x
    simp

/-- The multinomial coefficient over `univ` is invariant under reindexing by an equivalence. -/
lemma multinomial_univ_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (q : β → ℕ) :
    Nat.multinomial (Finset.univ : Finset β) q =
      Nat.multinomial (Finset.univ : Finset α) (q ∘ e) := by
  classical
  rw [← Finset.image_univ_equiv e]
  exact multinomial_image (Finset.univ : Finset α) e (fun a _ b _ h ↦ e.injective h) q

/-- `u ↦ exp (u • A)` is `C^m` at every point. -/
lemma contDiffAt_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (m : ℕ) (t : ℝ) :
    ContDiffAt ℝ m (fun u : ℝ => exp (u • A)) t :=
  (NormedSpace.exp_analytic (t • A)).contDiffAt.comp t
    (ContDiffAt.smul (f := fun u : ℝ => u) (g := fun _ : ℝ => A) contDiffAt_id contDiffAt_const)

/-! ### CS19 Supplementary Lemma 1: big-O scaling iff derivatives vanish at 0 -/

/-- If the first `n` iterated derivatives of `F` at `x₀` vanish, then the `n`-th Taylor
polynomial of `F` at `x₀` is just the leading term `(x - x₀)^n • ((n! : ℝ)⁻¹ • F⁽ⁿ⁾(x₀))`. -/
lemma taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (n : ℕ) {x₀ x : ℝ}
    (h0 : ∀ k < n, iteratedDeriv k F x₀ = 0) :
    taylorWithinEval F n Set.univ x₀ x =
      (x - x₀) ^ n • ((Nat.factorial n : ℝ)⁻¹ • iteratedDeriv n F x₀) := by
  rw [taylor_within_apply, Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range n, ((Nat.factorial k : ℝ)⁻¹ * (x - x₀) ^ k) •
      iteratedDerivWithin k F Set.univ x₀) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    rw [iteratedDerivWithin_univ, h0 k hkn, smul_zero]
  rw [hsum, zero_add]
  simp only [iteratedDerivWithin_univ]
  rw [mul_smul, smul_comm]

/-- A smooth function `F` satisfies `‖F t‖ = O(t^(p + 1))` as `t → 0` if and only if its
first `p` iterated derivatives vanish at `0` (CS19, Supplementary Lemma 1). -/
theorem isBigO_norm_iff_iteratedDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun t : ℝ => ‖F t‖) =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) ↔
      ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0 := by
  classical
  constructor
  · intro hbig; by_contra hnot
    have hex : ∃ j : ℕ, j ≤ p ∧ iteratedDeriv j F 0 ≠ 0 := by
      by_contra h; apply hnot
      intro j hj; by_contra hjz
      exact h ⟨j, hj, hjz⟩
    rcases hex with ⟨j₀, hj₀_le, hj₀_nz⟩
    have hex' : ∃ j : ℕ, iteratedDeriv j F 0 ≠ 0 := ⟨j₀, hj₀_nz⟩
    let j := Nat.find hex'
    have hj_nz : iteratedDeriv j F 0 ≠ 0 := Nat.find_spec hex'
    have hj_min : ∀ k < j, iteratedDeriv k F 0 = 0 := by
      intro k hk
      by_contra hk'
      exact (Nat.find_min hex' hk) hk'
    have hj_le : j ≤ p := le_trans (Nat.find_min' hex' hj₀_nz) hj₀_le
    have hbigF : F =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) := isBigO_norm_left.mp hbig
    rw [isBigO_iff] at hbigF
    rcases hbigF with ⟨C₁, hbigF⟩
    have hbigF' : ∀ᶠ t in 𝓝 (0 : ℝ), ‖F t‖ ≤ C₁ * |t| ^ (p + 1) := by
      filter_upwards [hbigF] with t ht
      simpa [norm_pow] using ht
    have hFj : ContDiff ℝ j F := hF.of_le (mod_cast le_top)
    have htaylor : (fun x : ℝ => F x - taylorWithinEval F j Set.univ 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ j) := by
      simpa using (taylor_isLittleO_univ (f := F) (x₀ := 0) (n := j) hFj)
    let c : E := ((Nat.factorial j : ℝ)⁻¹) • iteratedDeriv j F 0
    have htaylor' : (fun x : ℝ => F x - x ^ j • c) =o[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ j) := by
      refine htaylor.congr_left (fun x => ?_)
      rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F j (x₀ := 0) (x := x) hj_min]
      simp [c]
    have hc_nz : c ≠ 0 := smul_ne_zero (inv_ne_zero (by positivity)) hj_nz
    have hrem : ∀ᶠ x in 𝓝 (0 : ℝ), ‖F x - x ^ j • c‖ ≤ (‖c‖ / 2) * |x| ^ j := by
      filter_upwards [htaylor'.def (show 0 < ‖c‖ / 2 by positivity)] with x hx
      simpa [norm_pow] using hx
    have hlower : ∀ᶠ x in 𝓝 (0 : ℝ), (‖c‖ / 2) * |x| ^ j ≤ ‖F x‖ := by
      filter_upwards [hrem] with x hx
      have hnorm : ‖x ^ j • c‖ = ‖c‖ * |x| ^ j := by
        rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm]
      have htri : ‖x ^ j • c‖ - ‖F x‖ ≤ ‖F x - x ^ j • c‖ := by
        have h := norm_sub_norm_le (x ^ j • c) (F x)
        simpa [norm_sub_rev] using h
      linarith [hnorm, htri, hx]
    have hcombine : ∀ᶠ x in 𝓝 (0 : ℝ), (‖c‖ / 2) * |x| ^ j ≤ C₁ * |x| ^ (p + 1) := by
      filter_upwards [hlower, hbigF'] with x hlow hbig
      exact hlow.trans hbig
    have hO_scaled : (fun x : ℝ => (‖c‖ / 2) * |x| ^ j) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => |x| ^ (p + 1)) := by
      refine IsBigO.of_bound C₁ ?_
      filter_upwards [hcombine] with x hx
      rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hO : (fun x : ℝ => |x| ^ j) =O[𝓝 (0 : ℝ)] (fun x : ℝ => |x| ^ (p + 1)) :=
      (isBigO_const_mul_left_iff (f := fun x : ℝ => |x| ^ j) (g := fun x : ℝ => |x| ^ (p + 1))
        (c := ‖c‖ / 2) (l := 𝓝 (0 : ℝ)) (by positivity)).1 hO_scaled
    have ho : (fun x : ℝ => |x| ^ (p + 1)) =o[𝓝 (0 : ℝ)] (fun x : ℝ => |x| ^ j) := by
      simpa [Real.norm_eq_abs] using
        (isLittleO_norm_pow_norm_pow (E' := ℝ) (m := j) (n := p + 1) (by lia))
    have hfreq0 : ∃ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hU⟩
      refine ⟨ε / 2, hU ?_, ne_of_gt (div_pos hε (by norm_num))⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg (by positivity)]
      linarith
    have hfreq : ∃ᶠ x in 𝓝 (0 : ℝ), |x| ^ j ≠ 0 :=
      hfreq0.mono fun x hx => pow_ne_zero j (abs_ne_zero.mpr hx)
    exact (isLittleO_irrefl hfreq) (hO.trans_isLittleO ho)
  · intro h0
    have hFp1 : ContDiff ℝ (p + 1) F := hF.of_le (mod_cast le_top)
    have htaylor : (fun x : ℝ => F x - taylorWithinEval F (p + 1) Set.univ 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      simpa using (taylor_isLittleO_univ (f := F) (x₀ := 0) (n := p + 1) hFp1)
    let a : E := ((Nat.factorial (p + 1) : ℝ)⁻¹) • iteratedDeriv (p + 1) F 0
    have htaylor' : (fun x : ℝ => F x - x ^ (p + 1) • a) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      refine htaylor.congr_left (fun x => ?_)
      rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F (p + 1) (x₀ := 0) (x := x)
        (fun k hk => h0 k (Nat.lt_succ_iff.mp hk))]
      simp [a]
    have hbig_smul : (fun x : ℝ => x ^ (p + 1) • a) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ (p + 1)) := by
      refine IsBigO.of_bound ‖a‖ ?_
      filter_upwards with x
      simp [norm_smul, mul_comm]
    have hbig_F : (fun x : ℝ => F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ (p + 1)) :=
      (hbig_smul.add htaylor'.isBigO).congr_left (fun x => by abel)
    exact isBigO_norm_left.mpr hbig_F

/-! ### Taylor's theorem with integral remainder (vanishing derivatives at 0) -/

/-- If the first `p` iterated derivatives of `f` vanish at `0`, then the `p`-th Taylor polynomial
of `f` on `uIcc 0 t` (with base point `0`) vanishes, provided `t ≠ 0`. -/
lemma taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0)
    (ht : t ≠ 0) :
    taylorWithinEval f p (Set.uIcc 0 t) 0 t = 0 := by
  rw [taylor_within_apply]
  have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc (Ne.symm ht)
  apply Finset.sum_eq_zero
  intro k hk
  have hk_le_p : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk_le : k ≤ p + 1 := le_trans hk_le_p (Nat.le_succ p)
  rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (mod_cast hk_le))
    (by simp)]
  simp [h0 k hk_le_p]

/-- The scalar identity used to pass from the standard integral remainder to the paper's
substituted form: `t * (t - u * t)^p / p! = (p + 1) * (1 - u)^p * t^(p + 1) / (p + 1)!`. -/
lemma taylor_paper_scalar_eq (p : ℕ) (t u : ℝ) :
    t * ((t - u * t) ^ p / (Nat.factorial p : ℝ)) =
      (p + 1 : ℝ) * ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  rw [mul_pow]
  push_cast
  ring

/-- Taylor's theorem with the integral remainder for a function whose first `p` iterated
derivatives vanish at `0`: `f t = ∫₀ᵗ ((t - s)^p / p!) • f⁽ᵖ⁺¹⁾(s) ds`. -/
theorem taylor_integral_remainder_iteratedDeriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) :
    f t = ∫ s in (0 : ℝ)..t,
      ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s := by
  by_cases ht : t = 0
  · subst t
    simpa using (h0 0 (Nat.zero_le p))
  · have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc (Ne.symm ht)
    have hpoly : taylorWithinEval f p (Set.uIcc (0 : ℝ) t) 0 t = 0 :=
      taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero hf h0 ht
    have hmain := taylor_integral_remainder (f := f) (x₀ := 0) (x := t) (n := p) hf.contDiffOn
    have hf_t : f t = ∫ s in (0 : ℝ)..t,
        ((t - s) ^ p / (Nat.factorial p : ℝ)) •
          iteratedDerivWithin (p + 1) f (Set.uIcc (0 : ℝ) t) s := by
      simpa [hpoly] using hmain
    rw [hf_t]
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    exact congrArg (fun y => ((t - s) ^ p / (Nat.factorial p : ℝ)) • y)
      (iteratedDerivWithin_eq_iteratedDeriv hud hf.contDiffAt (Set.uIoo_subset_uIcc_self hs))

/-- Taylor's theorem with the integral remainder in the paper's substituted form
(`s = u * t`): `f t = (p + 1) • ∫₀¹ (1 - u)^p * t^(p + 1) / (p + 1)! • f⁽ᵖ⁺¹⁾(u * t) du`. -/
theorem taylor_integral_remainder_iteratedDeriv_zero_paper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) :
    f t = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
      ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) •
        iteratedDeriv (p + 1) f (u * t) := by
  rw [taylor_integral_remainder_iteratedDeriv_zero hf h0]
  calc
    ∫ s in (0 : ℝ)..t, ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s
        = t • ∫ u in (0 : ℝ)..(1 : ℝ),
            ((t - u * t) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f (u * t) := by
            simpa [mul_zero, one_mul] using
              (intervalIntegral.smul_integral_comp_mul_right
                (f := fun s => ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s)
                (a := 0) (b := 1) (c := t)).symm
    _ = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
          ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) •
            iteratedDeriv (p + 1) f (u * t) := by
          simp only [← intervalIntegral.integral_smul]
          apply intervalIntegral.integral_congr_uIoo
          intro u _
          simp only [smul_smul]
          exact congrArg₂ (fun r y => r • y) (taylor_paper_scalar_eq p t u) rfl

/-! ### Norm bounds for the exponential -/

section NormExpBounds

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- Each term of the exponential series is bounded by `‖a‖^n / n!`. -/
lemma norm_exp_term_le [NormOneClass 𝔸] (a : 𝔸) (n : ℕ) :
    ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ ≤ ‖a‖ ^ n / Nat.factorial n := by
  rw [norm_smul, norm_inv, ← Rat.norm_cast_real, Real.norm_eq_abs, inv_mul_eq_div]
  norm_cast; gcongr
  exact norm_pow_le ..

/-- The norm of the exponential is bounded by the exponential of the norm:
`‖exp a‖ ≤ Real.exp ‖a‖` for a general normed algebra. -/
lemma norm_exp_le [NormOneClass 𝔸] (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [NormedSpace.exp_eq_tsum ℚ, Real.exp_eq_exp_ℝ,
    ← (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq]
  have hnsumm : Summable fun n ↦ ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ :=
    (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_exp_term_le a)
  calc
    _ ≤ ∑' n, ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ := norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ‖a‖ ^ n / Nat.factorial n :=
      hnsumm.tsum_le_tsum (norm_exp_term_le a) (Real.summable_pow_div_factorial ‖a‖)

end NormExpBounds

/-- In a C*-algebra, the exponential of an anti-Hermitian (`star a = -a`) multiple is unitary,
hence has norm `1`: `‖exp (t • a)‖ = 1`. -/
lemma norm_exp_smul_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] {a : 𝔸} (ha : star a = -a) (t : ℝ) :
    ‖exp (t • a)‖ = 1 := by
  have hta : star (t • a) = -(t • a) := by
    rw [StarModule.star_smul, ha, smul_neg, star_trivial]
  exact CStarRing.norm_of_mem_unitary
    (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr hta))

/-- For a single element, the norm of `H^k * exp (s • H)` is bounded by
`‖H‖^k * Real.exp (s * ‖H‖)` whenever `s ≥ 0` (the paper's single-element bound,
prelim.tex:186–187). -/
theorem norm_pow_mul_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : 𝔸) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ‖H ^ k * exp (s • H)‖ ≤ ‖H‖ ^ k * Real.exp (s * ‖H‖) := by
  calc
    ‖H ^ k * exp (s • H)‖ ≤ ‖H ^ k‖ * ‖exp (s • H)‖ := norm_mul_le _ _
    _ ≤ ‖H‖ ^ k * Real.exp ‖s • H‖ := mul_le_mul (norm_pow_le H k) (norm_exp_le (s • H))
          (norm_nonneg _) (pow_nonneg (norm_nonneg H) k)
    _ = ‖H‖ ^ k * Real.exp (s * ‖H‖) := by
        congr 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

end TrotterError
