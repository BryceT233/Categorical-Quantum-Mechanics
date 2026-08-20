/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Dagger categories

This file defines the categorical abstraction of the dagger (adjoint) operation: a
contravariant, involutive involution on morphisms that fixes identities and reverses
composition. It also introduces the standard classes of morphisms used in categorical
quantum mechanics — projections, isometries, unitaries, and positive maps — together
with monoidal dagger categories, where the dagger is compatible with the monoidal
structure.

## Main definitions

* `DaggerCategory`: a category equipped with a dagger.
* `DaggerCategory.IsProj`: an idempotent self-adjoint endomorphism, i.e. a projection.
* `DaggerCategory.IsIsometry`: a morphism `f` satisfying `f ≫ f† = 𝟙`.
* `DaggerCategory.IsUnitary`: an isometry `f` that also satisfies `f† ≫ f = 𝟙`.
* `DaggerCategory.IsPositive`: an endomorphism of the form `g ≫ g†`.
* `MonoidalDaggerCategory`: a dagger category that is also monoidal, with the dagger
  compatible with the tensor product and the structural isomorphisms.

## Notation

* `f†` is notation for `DaggerCategory.dagger f`.

## Main results

* `dagger_zero`: the dagger of a zero morphism is zero.
* `isZero_of_isInitial` and `isZero_of_isTerminal`: in a dagger category, initial and
  terminal objects are zero objects.
-/

@[expose] public section

@[expose] public section

open CategoryTheory

section DaggerCategory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A category equipped with a contravariant dagger that fixes identities, reverses
composition, and is involutive. -/
class CategoryTheory.DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The contravariant dagger of a morphism, reversing its direction. -/
  dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : c₂ ⟶ c₁
  dagger_comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : dagger (f ≫ g) = dagger g ≫ dagger f
  dagger_id (c : C) : dagger (𝟙 c) = 𝟙 c
  involutive_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : dagger (dagger f) = f

/-- Notation `f†` for the dagger of a morphism `f`. -/
notation:max f "†" => DaggerCategory.dagger f

namespace CategoryTheory.DaggerCategory

attribute [simp] dagger_comp dagger_id involutive_dagger

variable [DaggerCategory C]

/-- Dagger induces an equivalence on arrows. -/
@[simps]
def daggerEquiv (c c' : C) : (c ⟶ c') ≃ (c' ⟶ c) where
  toFun := dagger
  invFun := dagger
  left_inv _ := by simp
  right_inv _ := by simp

/-- An idempotent self-adjoint endomorphism, i.e. a projection. -/
class IsProj [DaggerCategory C] {c : C} (f : End c) where
  idem (f) : IsIdempotentElem f
  selfAdjoint (f) : f† = f

attribute [simp] IsProj.selfAdjoint

@[simp]
lemma IsProj.comp_self {c : C} (f : End c) [IsProj f] : f ≫ f = f := IsProj.idem f

theorem IsProj.id (c : C) : IsProj (𝟙 c) := ⟨by simp [isIdempotentElem_iff], by simp⟩

instance IsProj.dagger {c : C} (f : End c) [IsProj f] : IsProj f† := by simpa

/-- A morphism satisfying `f ≫ f† = 𝟙`, i.e. an isometry. -/
class IsIsometry [DaggerCategory C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) where
  comp_dagger_eq_id (f) : f ≫ f† = 𝟙 c₁

attribute [simp] IsIsometry.comp_dagger_eq_id

instance (c : C) : IsIsometry (𝟙 c) := ⟨by simp⟩

instance IsIsometry.comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) [IsIsometry f]
    [IsIsometry g] : IsIsometry (f ≫ g) where
  comp_dagger_eq_id := by
    rw [dagger_comp, Category.assoc]
    nth_rw 2 [Category.assoc']; simp

/-- An isometry that also satisfies `f† ≫ f = 𝟙`, i.e. a unitary morphism. -/
class IsUnitary [DaggerCategory C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) extends IsIsometry f where
  dagger_comp_eq_id (f) : f† ≫ f = 𝟙 c₂

attribute [simp] IsUnitary.dagger_comp_eq_id

instance (c : C) : IsUnitary (𝟙 c) := ⟨by simp⟩

instance IsUnitary.comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) [IsUnitary f]
    [IsUnitary g] : IsUnitary (f ≫ g) where
  dagger_comp_eq_id := by
    rw [dagger_comp, Category.assoc]
    nth_rw 2 [Category.assoc']; simp

instance IsUnitary.dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : IsUnitary f† where
  comp_dagger_eq_id := by simp
  dagger_comp_eq_id := by simp

instance IsUnitary.isIso {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : IsIso f :=
  ⟨f†, by simp, by simp⟩

lemma IsUnitary.inv_self_eq_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : inv f = f† := by
  rw [← Category.comp_id (inv f), ← IsIsometry.comp_dagger_eq_id f, Category.assoc']
  simp

lemma IsUnitary.inv_dagger_eq_self {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : inv f† = f := by
  simp [inv_self_eq_dagger f†]

/-- An isomorphism whose dagger is its inverse has a unitary forward map. -/
theorem isUnitary_of_dagger_eq_inv {c₁ c₂ : C} (e : c₁ ≅ c₂) (hdag : e.hom† = e.inv) :
    DaggerCategory.IsUnitary e.hom where
  comp_dagger_eq_id := hdag ▸ e.hom_inv_id
  dagger_comp_eq_id := hdag ▸ e.inv_hom_id

/-- An endomorphism of the form `g ≫ g†` for some morphism `g`, i.e. a positive morphism. -/
class IsPositive {c : C} (f : End c) where
  out (f) : ∃ (c' : C) (g : c ⟶ c'), f = g ≫ g†

instance IsPositive.id (c : C) : IsPositive (𝟙 c) := ⟨c, 𝟙 c, by simp⟩

instance IsPositive.comp_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : IsPositive (f ≫ f†) :=
  ⟨c₂, f, rfl⟩

instance IsPositive.dagger_comp {c₁ c₂ : C} (f : c₁ ⟶ c₂) : IsPositive (f† ≫ f) :=
  ⟨c₁, f†, by simp⟩

instance IsPositive.dagger {c : C} (f : End c) [IsPositive f] : IsPositive f† := by
  rcases IsPositive.out f with ⟨c', g, rfl⟩
  simpa

/-- A positive endomorphism is self-adjoint. -/
@[simp]
lemma selfAdjoint_of_isPositive {c : C} (f : End c) [IsPositive f] : f† = f := by
  rcases IsPositive.out f with ⟨c', g, rfl⟩
  simp

open Limits

attribute [local instance] HasZeroObject.zero' in
/-- Lemma 2.35 in `Categorical Quantum Mechanics: An Introduction`. -/
@[simp]
lemma dagger_zero [HasZeroObject C] [HasZeroMorphisms C] {c c' : C} : (0 : c ⟶ c')† = 0 := by
  have := HasZeroObject.uniqueTo c
  rw [← zero_comp (X := c) (Y := 0) (Z := c') (f := 0), dagger_comp,
    Subsingleton.elim (0† : 0 ⟶ c) 0, comp_zero]

/-- Lemma 2.36 in `Categorical Quantum Mechanics: An Introduction`. -/
lemma isZero_of_isInitial {c : C} (init : IsInitial c) : IsZero c where
  unique_to c' := ⟨isInitialEquivUnique _ _ init c'⟩
  unique_from c' := ⟨have := isInitialEquivUnique _ _ init c'; Equiv.unique (daggerEquiv ..)⟩

/-- Lemma 2.36 in `Categorical Quantum Mechanics: An Introduction`. -/
lemma isZero_of_isTerminal {c : C} (term : IsTerminal c) : IsZero c where
  unique_to c' := ⟨have := isTerminalEquivUnique _ _ term c'; Equiv.unique (daggerEquiv ..)⟩
  unique_from c' := ⟨isTerminalEquivUnique _ _ term c'⟩

end CategoryTheory.DaggerCategory

open MonoidalCategory

/-- A dagger category that is also monoidal, with the dagger compatible with the tensor product
and the structural isomorphisms. -/
class CategoryTheory.MonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    DaggerCategory C, MonoidalCategory C where
  dagger_tensor {H₁ H₂ K₁ K₂ : C} (f₁ : H₁ ⟶ K₁) (f₂ : H₂ ⟶ K₂) : (f₁ ⊗ₘ f₂)† = f₁† ⊗ₘ f₂†
  isUnitary_associator (H₁ H₂ H₃ : C) : DaggerCategory.IsUnitary (α_ H₁ H₂ H₃).hom
  isUnitary_leftUnitor (H : C) : DaggerCategory.IsUnitary (λ_ H).hom
  isUnitary_rightUnitor (H : C) : DaggerCategory.IsUnitary (ρ_ H).hom

attribute [instance] CategoryTheory.MonoidalDaggerCategory.isUnitary_associator
attribute [instance] CategoryTheory.MonoidalDaggerCategory.isUnitary_leftUnitor
attribute [instance] CategoryTheory.MonoidalDaggerCategory.isUnitary_rightUnitor

end DaggerCategory
