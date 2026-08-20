/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import CQM1.Category.DaggerCategory
public import Mathlib

/-!
# The category of Hilbert spaces

This file defines `HilbCat`, the category of complex Hilbert spaces: objects are Hilbert
spaces over `ℂ` (complete inner product spaces) and morphisms are continuous linear maps
between them. The category is equipped with a dagger structure given by the adjoint of a
continuous linear map.

## Main definitions

* `HilbCat`: the category of complex Hilbert spaces.
* `HilbCat.Hom`: a morphism between two Hilbert spaces, i.e. a continuous linear map of the
  underlying spaces.

## Main results

* `HilbCat` is a dagger category.

## Implementation notes

The universe level of the underlying spaces is fixed to `Type` for simplicity.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory

/-- The category of Hilbert spaces, where the universe level of the underlying spaces is
fixed to be 0 for simplicity. Objects in this category represent complex Hilbert spaces. -/
structure HilbCat where
  /-- Construct an object in `HilbCat` from a Hilbert space. -/
  of ::
  /-- The underlying Hilbert space of an object of `HilbCat`. -/
  carrier : Type
  [isNormedAddCommGroup : NormedAddCommGroup carrier]
  [isInnerProductSpace : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]

initialize_simps_projections HilbCat (-isNormedAddCommGroup, -isInnerProductSpace, -complete)
attribute [instance] HilbCat.isNormedAddCommGroup HilbCat.isInnerProductSpace HilbCat.complete

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `HilbCat.of X` being printed as
`{ HilbCat := X, isNormedAddCommGroup := ... }` by `delabStructureInstance`. -/
@[app_delab HilbCat.of]
meta def HilbCat.delabOf : Delab := delabApp

end Notation

namespace HilbCat

instance : CoeSort HilbCat Type := ⟨HilbCat.carrier⟩

attribute [coe] HilbCat.carrier

lemma of_carrier {H : HilbCat} : of H.carrier = H := rfl

lemma carrier_of (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] : (of X).carrier = X := rfl

section Hom

/-- The type of morphisms in `HilbCat`. -/
@[ext]
structure Hom (H₁ H₂ : HilbCat) where
  private mk ::
  /-- The underlying continuous linear map between the Hilbert spaces. -/
  hom' : H₁ →L[ℂ] H₂

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance largeCategory : LargeCategory HilbCat where
  Hom H₁ H₂ := Hom H₁ H₂
  id _ := ⟨ContinuousLinearMap.id ..⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance concreteCategory : ConcreteCategory HilbCat (fun H₁ H₂ ↦ H₁ →L[ℂ] H₂) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `HilbCat` back into a `ContinuousLinearMap`. -/
abbrev Hom.hom {H₁ H₂ : HilbCat} (f : Hom H₁ H₂) :=
  ConcreteCategory.hom (C := HilbCat) f

/-- Typecheck a `ContinuousLinearMap` as a morphism in `HilbCat`. -/
abbrev ofHom {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (f : X →L[ℂ] Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := HilbCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (H₁ H₂ : HilbCat) (f : Hom H₁ H₂) := f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_id {H : HilbCat} : (𝟙 H : H ⟶ H).hom = ContinuousLinearMap.id .. := rfl

lemma id_apply (H : HilbCat) (x : H) : 𝟙 H x = x := by simp

@[simp]
lemma hom_comp {H₁ H₂ H₃ : HilbCat} (f : H₁ ⟶ H₂) (g : H₂ ⟶ H₃) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma comp_apply {H₁ H₂ H₃ : HilbCat} (f : H₁ ⟶ H₂) (g : H₂ ⟶ H₃) (x : H₁) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {H₁ H₂ : HilbCat} {f g : H₁ ⟶ H₂} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_bijective {H₁ H₂ : HilbCat} :
    Function.Bijective (Hom.hom : (H₁ ⟶ H₂) → (H₁ →L[ℂ] H₂)) where
  left f g h := by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩

/-- Convenience shortcut for `HilbCat.hom_bijective.injective`. -/
lemma hom_injective {H₁ H₂ : HilbCat} :
    Function.Injective (Hom.hom : (H₁ ⟶ H₂) → (H₁ →L[ℂ] H₂)) :=
  hom_bijective.injective

/-- Convenience shortcut for `HilbCat.hom_bijective.surjective`. -/
lemma hom_surjective {H₁ H₂ : HilbCat} :
    Function.Surjective (Hom.hom : (H₁ ⟶ H₂) → (H₁ →L[ℂ] H₂)) :=
  hom_bijective.surjective

@[simp]
lemma hom_ofHom {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (f : X →L[ℂ] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {H₁ H₂ : HilbCat} (f : H₁ ⟶ H₂) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] : ofHom (ContinuousLinearMap.id ℂ X) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    [CompleteSpace Z] (f : X →L[ℂ] Y) (g : Y →L[ℂ] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] (f : X →L[ℂ] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply {H₁ H₂ : HilbCat} (e : H₁ ≅ H₂) (x : H₁) :
    e.inv (e.hom x) = x := by simp

lemma hom_inv_apply {H₁ H₂ : HilbCat} (e : H₁ ≅ H₂) (x : H₂) :
    e.hom (e.inv x) = x := by simp

/-- `HilbCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {H₁ H₂ : HilbCat} : (H₁ ⟶ H₂) ≃ (H₁ →L[ℂ] H₂) where
  toFun := Hom.hom
  invFun := ofHom

/-- Build an isomorphism in the category `HilbCat` from a `ContinuousLinearEquiv` between
Hilbert spaces. -/
def isoMk {X Y : Type} {_ : NormedAddCommGroup X} {_ : InnerProductSpace ℂ X}
    {_ : CompleteSpace X} {_ : NormedAddCommGroup Y} {_ : InnerProductSpace ℂ Y}
    {_ : CompleteSpace Y} (e : X ≃L[ℂ] Y) : of X ≅ of Y where
  hom := ofHom (e : X →L[ℂ] Y)
  inv := ofHom (e.symm : Y →L[ℂ] X)

/-- Build a `LinearEquiv` from an isomorphism in the category `HilbCat`. -/
def linearEquivOfIso {H₁ H₂ : HilbCat} (i : H₁ ≅ H₂) : H₁ ≃ₗ[ℂ] H₂ where
  __ := (i.hom.hom : H₁ →ₗ[ℂ] H₂)
  toFun := i.hom
  invFun := i.inv
  left_inv _ := by simp
  right_inv _ := by simp

/-- Build a `ContinuousLinearEquiv` from an isomorphism in the category `HilbCat`. -/
def continuousLinearEquivOfIso {H₁ H₂ : HilbCat} (i : H₁ ≅ H₂) : H₁ ≃L[ℂ] H₂ where
  toLinearEquiv := linearEquivOfIso i
  continuous_toFun := (i.hom.hom).continuous
  continuous_invFun := (i.inv.hom).continuous

end Hom

noncomputable instance daggerCategory : DaggerCategory HilbCat where
  dagger f := ofHom (f.hom.adjoint)
  dagger_comp f g := by simp
  dagger_id f := by simp [ContinuousLinearMap.adjoint_id]
  involutive_dagger f := by simp

open DaggerCategory

@[simp]
lemma hom_dagger {H₁ H₂ : HilbCat} (f : H₁ ⟶ H₂) : f†.hom = f.hom.adjoint := rfl

end HilbCat
