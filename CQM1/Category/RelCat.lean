/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import CQM1.Category.DaggerCategory
public import Mathlib

/-!
# The monoidal dagger structure on the category of relations

This file equips `RelCat`, the category of types with binary relations as morphisms,
with its monoidal category structure: the tensor product is the cartesian product of types
and the tensor unit is `PUnit`.

## Main definitions

* the monoidal category structure on `RelCat`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonoidalCategory

namespace CategoryTheory.RelCat

/-- The monoidal category structure on `RelCat`: the tensor product is the cartesian
product of types, and the tensor unit is `PUnit`. -/
instance : MonoidalCategoryStruct RelCat.{u} where
  tensorObj X Y := X × Y
  whiskerLeft _ _ _ f := .ofRel {((x, y₁), (x', y₂)) | x = x' ∧ (y₁, y₂) ∈ f.rel}
  whiskerRight f _ := .ofRel {((x, y), (x', y')) | (x, x') ∈ f.rel ∧ y = y'}
  tensorUnit := PUnit
  associator X Y Z := graphFunctor.mapIso (Equiv.prodAssoc X Y Z).toIso
  leftUnitor X := graphFunctor.mapIso (Equiv.punitProd X).toIso
  rightUnitor X := graphFunctor.mapIso (Equiv.prodPUnit X).toIso

lemma tensorObj_ext_iff {X Y : RelCat.{u}} (u v : X ⊗ Y) : u = v ↔ u.1 = v.1 ∧ u.2 = v.2 :=
  Prod.ext_iff

lemma mem_id {X : RelCat.{u}} (u : X ⊗ X) : u ∈ SetRel.id ↔ u.1 = u.2 := Iff.rfl

lemma mem_comp {X Y Z : RelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (x, z) ∈ f.rel.comp g.rel ↔ ∃ y : Y, (x, y) ∈ f.rel ∧ (y, z) ∈ g.rel := SetRel.mem_comp

lemma mem_whiskerLeft {X Y Z : RelCat.{u}} (f : Y ⟶ Z) (x x' : X) (y : Y) (z : Z) :
    ((x, y), (x', z)) ∈ (X ◁ f).rel ↔ x = x' ∧ (y, z) ∈ f.rel := Iff.rfl

lemma mem_whiskerRight {X Y Z : RelCat.{u}} (f : X ⟶ Y) (x : X) (y : Y) (z z' : Z) :
    ((x, z), (y, z')) ∈ (f ▷ Z).rel ↔ (x, y) ∈ f.rel ∧ z = z' := Iff.rfl

lemma mem_tensorHom {X₁ Y₁ X₂ Y₂ : RelCat.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (x₁ : X₁) (x₂ : X₂) (y₁ : Y₁) (y₂ : Y₂) :
    ((x₁, x₂), (y₁, y₂)) ∈ (f ⊗ₘ g).rel ↔ (x₁, y₁) ∈ f.rel ∧ (x₂, y₂) ∈ g.rel := by
  constructor
  · rintro ⟨⟨z₁, z₂⟩, hf, hg⟩; grind only [usr Set.mem_ofPred_eq]
  · rintro ⟨h₁, h₂⟩
    exact ⟨(y₁, x₂), (mem_whiskerRight f x₁ y₁ x₂ x₂).2 ⟨h₁, rfl⟩,
      (mem_whiskerLeft g y₁ y₁ x₂ y₂).2 ⟨rfl, h₂⟩⟩

lemma mem_associator_hom {X Y Z : RelCat.{u}} (x : X) (y : Y) (z : Z) (p : X × (Y × Z)) :
    (((x, y), z), p) ∈ (α_ X Y Z).hom.rel ↔ (x, y, z) = p := Iff.rfl

lemma mem_leftUnitor_hom {X : RelCat.{u}} (u : PUnit) (x : X) (y : X) :
    ((u, x), y) ∈ (λ_ X).hom.rel ↔ x = y := Iff.rfl

lemma mem_rightUnitor_hom {X : RelCat.{u}} (x : X) (u : PUnit) (y : X) :
    ((x, u), y) ∈ (ρ_ X).hom.rel ↔ x = y := Iff.rfl

/-- `RelCat` is a monoidal category. -/
instance : MonoidalCategory RelCat.{u} where
  id_tensorHom_id X₁ X₂ := by
    ext ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
    rw [mem_tensorHom, Hom.rel_id, mem_id, Hom.rel_id, mem_id, Hom.rel_id, mem_id,
      tensorObj_ext_iff]
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext ⟨⟨x₁, x₂⟩, ⟨z₁, z₂⟩⟩; constructor
    · rintro ⟨⟨y₁, y₂⟩, hf, hg⟩
      rw [mem_tensorHom] at hf hg
      rw [mem_tensorHom, Hom.rel_comp, Hom.rel_comp, mem_comp, mem_comp]
      grind only
    · intro h
      rw [mem_tensorHom, Hom.rel_comp, Hom.rel_comp, mem_comp, mem_comp] at h
      rcases h with ⟨⟨y₁, hf, hg⟩, ⟨y₂, hf', hg'⟩⟩
      refine ⟨(y₁, y₂), ?_, ?_⟩
      all_goals rw [mem_tensorHom]; grind only
  whiskerLeft_id X Y := by
    ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    rw [mem_whiskerLeft, Hom.rel_id, mem_id, Hom.rel_id, mem_id, tensorObj_ext_iff]
  id_whiskerRight X Y := by
    ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    rw [mem_whiskerRight, Hom.rel_id, mem_id, Hom.rel_id, mem_id, tensorObj_ext_iff]
  associator_naturality f₁ f₂ f₃ := by
    ext ⟨⟨⟨x₁, x₂⟩, x₃⟩, ⟨y₁, ⟨y₂, y₃⟩⟩⟩; constructor
    · rintro ⟨⟨⟨a₁, a₂⟩, a₃⟩, hf, hα⟩
      rw [mem_tensorHom] at hf
      rcases hf with ⟨hf₁₂, hf₃⟩
      rw [mem_tensorHom] at hf₁₂
      rw [mem_associator_hom] at hα
      have ha₁ : a₁ = y₁ := congrArg (fun p => p.1) hα
      have ha₂ : a₂ = y₂ := congrArg (fun p => p.2.1) hα
      have ha₃ : a₃ = y₃ := congrArg (fun p => p.2.2) hα
      refine ⟨(x₁, (x₂, x₃)), ?_, ?_⟩
      · rw [mem_associator_hom]
      · rw [mem_tensorHom, mem_tensorHom]
        grind only
    · rintro ⟨⟨r₁, ⟨r₂, r₃⟩⟩, hα, hf⟩
      rw [mem_associator_hom] at hα
      rw [mem_tensorHom,mem_tensorHom] at hf
      refine ⟨((y₁, y₂), y₃), ?_, ?_⟩
      · rw [mem_tensorHom, mem_tensorHom]
        grind only
      · rw [mem_associator_hom]
  leftUnitor_naturality f := by
    ext ⟨⟨u, x⟩, y⟩; constructor
    · rintro ⟨⟨u₁, y₁⟩, hf, hl⟩
      rw [mem_whiskerLeft] at hf
      rw [mem_leftUnitor_hom] at hl
      refine ⟨x, ?_, ?_⟩
      · rw [mem_leftUnitor_hom]
      · simpa [hl] using hf.2
    · rintro ⟨r, hl, hf⟩
      rw [mem_leftUnitor_hom] at hl
      refine ⟨(u, y), ?_, ?_⟩
      · rw [mem_whiskerLeft]
        grind only
      · rw [mem_leftUnitor_hom]
  rightUnitor_naturality f := by
    ext ⟨⟨x, u⟩, y⟩; constructor
    · rintro ⟨⟨y₁, u₁⟩, hf, hr⟩
      rw [mem_whiskerRight] at hf
      rw [mem_rightUnitor_hom] at hr
      refine ⟨x, ?_, ?_⟩
      · rw [mem_rightUnitor_hom]
      · simpa [hr] using hf.1
    · rintro ⟨r, hr, hf⟩
      rw [mem_rightUnitor_hom] at hr
      refine ⟨(y, u), ?_, ?_⟩
      · rw [mem_whiskerRight]
        exact ⟨by simpa [← hr] using hf, rfl⟩
      · rw [mem_rightUnitor_hom]
  pentagon W X Y Z := by
    ext ⟨⟨⟨⟨w, x⟩, y⟩, z⟩, ⟨w', ⟨x', ⟨y', z'⟩⟩⟩⟩; constructor
    · rintro ⟨⟨⟨m₁, ⟨m₂₁, m₂₂⟩⟩, m₃⟩, hA, hBC⟩
      rw [mem_whiskerRight, mem_associator_hom] at hA
      rcases hBC with ⟨⟨n₁, ⟨⟨n₂₁, n₂₂⟩, n₃⟩⟩, hB, hC⟩
      rw [mem_associator_hom] at hB
      rw [mem_whiskerLeft, mem_associator_hom] at hC
      refine ⟨((w, x), y, z), ?_, ?_⟩
      · rw [mem_associator_hom]
      · rw [mem_associator_hom]
        ext <;> grind only
    · rintro ⟨⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩, hR, hS⟩
      rw [mem_associator_hom] at hR hS
      refine ⟨((w, x, y), z), ?_, ?_⟩
      · rw [mem_whiskerRight, mem_associator_hom]
        exact ⟨rfl, rfl⟩
      · refine ⟨(w, (x, y), z), ?_, ?_⟩
        · rw [mem_associator_hom]
        · rw [mem_whiskerLeft, mem_associator_hom]
          constructor; · grind only
          ext <;> grind only
  triangle X Y := by
    ext ⟨⟨⟨x, u⟩, y⟩, ⟨x', y'⟩⟩; constructor
    · rintro ⟨⟨q₁, q₂, q₃⟩, hα, hf⟩
      rw [mem_associator_hom] at hα
      rw [mem_whiskerLeft, mem_leftUnitor_hom] at hf
      rw [mem_whiskerRight, mem_rightUnitor_hom]
      grind only
    · intro h
      rw [mem_whiskerRight, mem_rightUnitor_hom] at h
      refine ⟨(x, u, y), ?_, ?_⟩
      · rw [mem_associator_hom]
      · rwa [mem_whiskerLeft, mem_leftUnitor_hom]

instance : DaggerCategory RelCat.{u} where
  dagger f := .ofRel (SetRel.inv f.rel)
  dagger_comp f g := RelCat.Hom.ext _ _ (SetRel.inv_comp f.rel g.rel)
  dagger_id _ := RelCat.Hom.ext _ _ SetRel.inv_id
  involutive_dagger _ := RelCat.Hom.ext _ _ SetRel.inv_inv

end CategoryTheory.RelCat
