/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# General `List.prod` lemmas

General results about ordered (`List.prod`) products and sums, at the `Monoid` / `AddCommMonoid` /
`NormedAlgebra` level, used by the Trotter error theory (arXiv:1912.08854).

These are the `List`-level facts that the product-formula lemmas in `ErrorTypes.lean`
(`factorProdOver`, `prefixFactorProd`, `strictSuffixFactorProd`, …) specialize.

## Main results

* `prod_drop_eq_get_mul`: `((l.drop k).map f).prod = f (l.get k) * ((l.drop (k + 1)).map f).prod`.
* `prod_map_eq_take_mul_get_mul_drop`: splitting `(l.map f).prod` at an element `i ∈ l` into
  prefix `· f i ·` suffix.
* `sum_get_eq_sum_idxOf`: reindexing a sum over positions `Fin l.length` to a sum over the
  (nodup) elements of `l`.
* `hasDerivAt_list_prod`: the product rule for the ordered product `t ↦ (l.map (f · t)).prod`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace TrotterError

/-! ### Products over sublists -/

/-- The product over `l.drop k` splits as `f (l.get k)` times the product over `l.drop (k + 1)`. -/
lemma prod_drop_eq_get_mul {ι M : Type*} [Monoid M] (l : List ι) (f : ι → M) (k : Fin l.length) :
    ((l.drop (k : ℕ)).map f).prod = f (l.get k) * ((l.drop ((k : ℕ) + 1)).map f).prod := by
  rw [← List.cons_get_drop_succ (l := l) (n := k)]
  simp only [List.map_cons, List.prod_cons]

/-- Splitting the product `(l.map f).prod` at the occurrence of `i`: it is the product over the
prefix strictly before `i`, times `f i`, times the product over the suffix strictly after `i`. -/
lemma prod_map_eq_take_mul_get_mul_drop {ι M : Type*} [BEq ι] [LawfulBEq ι] [Monoid M]
    (l : List ι) (f : ι → M) (i : ι) (hi : i ∈ l) :
    (l.map f).prod = ((l.take (l.idxOf i)).map f).prod * f i *
      ((l.drop (l.idxOf i + 1)).map f).prod := by
  have hidx : l.idxOf i < l.length := List.idxOf_lt_length_iff.mpr hi
  have hcons : i :: l.drop (l.idxOf i + 1) = l.drop (l.idxOf i) := by
    calc
      i :: l.drop (l.idxOf i + 1) = l[l.idxOf i] :: l.drop (l.idxOf i + 1) := by
          rw [List.getElem_idxOf hidx]
      _ = l.drop (l.idxOf i) := List.cons_getElem_drop_succ (l := l) (n := l.idxOf i) (h := hidx)
  calc
    (l.map f).prod = ((l.take (l.idxOf i) ++ l.drop (l.idxOf i)).map f).prod := by
        rw [List.take_append_drop (l.idxOf i) l]
    _ = ((l.take (l.idxOf i)).map f).prod * ((l.drop (l.idxOf i)).map f).prod := by
        rw [List.map_append, List.prod_append]
    _ = ((l.take (l.idxOf i)).map f).prod * ((i :: l.drop (l.idxOf i + 1)).map f).prod := by
        rw [← hcons]
    _ = ((l.take (l.idxOf i)).map f).prod * (f i * ((l.drop (l.idxOf i + 1)).map f).prod) := by
        rw [List.map_cons, List.prod_cons]
    _ = ((l.take (l.idxOf i)).map f).prod * f i * ((l.drop (l.idxOf i + 1)).map f).prod := by
        rw [mul_assoc]

/-- If `g i` is a right inverse of `f i` for every `i`, then the product of `f` over `l` times the
product of `g` over `l.reverse` is `1`. -/
lemma prod_mul_rev_eq_one_of_mul_eq_one {ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M)
    (hfg : ∀ i, f i * g i = 1) :
    (l.map f).prod * (l.reverse.map g).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one]
      calc
        (f a * (l.map f).prod) * ((l.reverse.map g).prod * g a)
            = f a * ((l.map f).prod * (l.reverse.map g).prod) * g a := by
                simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hfg a]

/-- If `g i` is a left inverse of `f i` for every `i`, then the product of `g` over `l.reverse`
times the product of `f` over `l` is `1`. -/
lemma rev_mul_prod_eq_one_of_mul_eq_one {ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M)
    (hgf : ∀ i, g i * f i = 1) :
    (l.reverse.map g).prod * (l.map f).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one]
      calc
        ((l.reverse.map g).prod * g a) * (f a * (l.map f).prod)
            = (l.reverse.map g).prod * (g a * f a) * (l.map f).prod := by
                simp only [mul_assoc]
        _ = 1 := by rw [hgf a, mul_one, ih]

/-! ### Reindexing a sum by a nodup list -/

/-- A sum over positions `Fin l.length` reindexes to a sum over the (pairwise distinct) elements
of `l`, using `l.idxOf i` as the inverse of `l.get`. -/
lemma sum_get_eq_sum_idxOf {ι A : Type*} [Fintype ι] [BEq ι] [LawfulBEq ι] [AddCommMonoid A]
    {l : List ι} (hnodup : l.Nodup) (hmem : ∀ i : ι, i ∈ l) (G : ι → ℕ → A) :
    (∑ k : Fin l.length, G (l.get k) (k : ℕ)) = ∑ i : ι, G i (l.idxOf i) := by
  refine (Finset.sum_bij (fun i _ => ⟨l.idxOf i, List.idxOf_lt_length_iff.mpr (hmem i)⟩)
    (fun i _ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro a₁ ha₁ a₂ ha₂ h
    have h₁ := List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a₁))
    have h₂ := List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a₂))
    exact h₁.symm.trans ((congrArg l.get h).trans h₂)
  · intro b hb
    refine ⟨l.get b, Finset.mem_univ _, ?_⟩
    ext; exact List.get_idxOf hnodup b
  · intro a ha
    rw [List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a))]

/-! ### Derivative of an ordered product -/

/-- The product rule for an ordered `List.prod`: the derivative of `t ↦ (l.map (f · t)).prod` is
the sum over positions `k` of the `k`-th factor differentiated, surrounded by the earlier and later
factors. -/
lemma hasDerivAt_list_prod {ι 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (l : List ι) (f : ι → ℝ → 𝔸) (Df : ι → ℝ → 𝔸)
    (hf : ∀ i ∈ l, ∀ t : ℝ, HasDerivAt (f i) (Df i t) t) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
      (∑ k : Fin l.length,
        ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
          ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (hasDerivAt_const t (1 : 𝔸))
  | cons a l ih =>
      have hf' : ∀ i ∈ l, ∀ t : ℝ, HasDerivAt (f i) (Df i t) t := by
        intro i hi s
        exact hf i (List.mem_cons_of_mem a hi) s
      have ih' : HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
          (∑ k : Fin l.length,
            ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
              ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := ih hf'
      have hfa : HasDerivAt (f a) (Df a t) t := hf a (show a ∈ a :: l from List.mem_cons_self) t
      have hprod : HasDerivAt (fun s : ℝ => f a s * (l.map (fun i => f i s)).prod)
          (Df a t * (l.map (fun i => f i t)).prod + f a t *
            (∑ k : Fin l.length,
              ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
                ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod)) t := hfa.mul ih'
      have hsum :
          (∑ k : Fin (l.length + 1),
            (((a :: l).take (k : ℕ)).map (fun i => f i t)).prod * Df ((a :: l).get k) t *
              (((a :: l).drop ((k : ℕ) + 1)).map (fun i => f i t)).prod)
            = Df a t * (l.map (fun i => f i t)).prod + f a t *
                (∑ k : Fin l.length,
                  ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
                    ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) := by
        rw [Fin.sum_univ_succ]
        congr 1; · simp
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp [mul_assoc]
      change HasDerivAt (fun s : ℝ => f a s * (l.map (fun i => f i s)).prod)
        (∑ k : Fin (l.length + 1),
          (((a :: l).take (k : ℕ)).map (fun i => f i t)).prod * Df ((a :: l).get k) t *
            (((a :: l).drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t
      rwa [hsum]

end TrotterError
