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
with its monoidal dagger category structure: the tensor product is the cartesian product of types,
the tensor unit is `PUnit` and the dagger is `SetRel.inv`.

It also characterizes the dagger-derived morphism classes (`IsUnitary`, `IsIsometry`, `IsProj`,
`IsPositive`) in terms of the underlying relations.

## Main definitions

* the monoidal dagger category structure on `RelCat`.

## Main results

* `isUnitary_iff_isIso`: unitary morphisms are exactly the isomorphisms.
* `isIsometry_iff_leftTotal_leftUnique`: isometries are exactly total and injective relations.
* `isProj_iff_symm_trans`: projections are exactly partial equivalence relations.
* `isPositive_iff_symm_reflOnDom`: positive morphisms are exactly symmetric relations that are
  reflexive on their domain.
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
    ((x, z), y, z') ∈ (f ▷ Z).rel ↔ (x, y) ∈ f.rel ∧ z = z' := Iff.rfl

lemma mem_tensorHom {X₁ Y₁ X₂ Y₂ : RelCat.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (x₁ : X₁) (x₂ : X₂) (y₁ : Y₁) (y₂ : Y₂) :
    ((x₁, x₂), y₁, y₂) ∈ (f ⊗ₘ g).rel ↔ (x₁, y₁) ∈ f.rel ∧ (x₂, y₂) ∈ g.rel := by
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
      refine ⟨(x₁, x₂, x₃), ?_, ?_⟩
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
  dagger_comp f g := Hom.ext _ _ (SetRel.inv_comp f.rel g.rel)
  dagger_id _ := Hom.ext _ _ SetRel.inv_id
  involutive_dagger _ := Hom.ext _ _ SetRel.inv_inv

lemma rel_dagger {X Y : RelCat.{u}} (f : X ⟶ Y) : f†.rel = f.rel.inv := rfl

lemma mem_dagger {X Y : RelCat.{u}} (f : X ⟶ Y) (x : X) (y : Y) :
    (y, x) ∈ f†.rel ↔ (x, y) ∈ f.rel := Iff.rfl

instance monoidalDaggerCategory : MonoidalDaggerCategory RelCat.{u} where
  dagger_tensor f g := by
    ext ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
    rw [mem_dagger, mem_tensorHom, mem_tensorHom, mem_dagger, mem_dagger]
  isUnitary_associator _ _ _ := DaggerCategory.isUnitary_of_dagger_eq_inv _ <|
    Hom.ext _ _ (Equiv.graph_inv (Equiv.prodAssoc ..)).symm
  isUnitary_leftUnitor _ := DaggerCategory.isUnitary_of_dagger_eq_inv _ <|
    Hom.ext _ _ (Equiv.graph_inv (Equiv.punitProd ..)).symm
  isUnitary_rightUnitor _ := DaggerCategory.isUnitary_of_dagger_eq_inv _ <|
    Hom.ext _ _ (Equiv.graph_inv (Equiv.prodPUnit ..)).symm

/-! ### Dagger morphisms in `RelCat` -/

variable {X Y : RelCat.{u}}

/-- The graph of a bijection is a unitary morphism in `RelCat`. -/
theorem isUnitary_graphFunctor_mapIso {X Y : Type u} (e : X ≅ Y) :
    DaggerCategory.IsUnitary (graphFunctor.mapIso e).hom :=
  DaggerCategory.isUnitary_of_dagger_eq_inv (graphFunctor.mapIso e) <| by
    apply Hom.ext
    exact (Equiv.graph_inv e.toEquiv).symm

/-- In `RelCat`, a morphism is unitary exactly when it is an isomorphism. -/
theorem isUnitary_iff_isIso (f : X ⟶ Y) :
    DaggerCategory.IsUnitary f ↔ IsIso f := by
  refine ⟨fun h ↦ h.isIso, fun h ↦ ?_⟩
  rcases (rel_iso_iff f).1 h with ⟨e, he⟩
  rw [← he]
  exact DaggerCategory.isUnitary_of_dagger_eq_inv (graphFunctor.mapIso e) <| by
    apply Hom.ext
    exact (Equiv.graph_inv e.toEquiv).symm

/-- In `RelCat`, an isometry is exactly a total and injective relation. -/
theorem isIsometry_iff_leftTotal_leftUnique (f : X ⟶ Y) :
    DaggerCategory.IsIsometry f ↔
      Relator.LeftTotal (fun x : X ↦ fun y : Y ↦ (x, y) ∈ f.rel) ∧
        Relator.LeftUnique (fun x : X ↦ fun y : Y ↦ (x, y) ∈ f.rel) := by
  constructor
  · intro h; constructor
    · intro x
      have hmem : (x, x) ∈ (f ≫ f†).rel := by
        rw [h.comp_dagger_eq_id, Hom.rel_id, mem_id]
      rw [Hom.rel_comp, mem_comp] at hmem
      rcases hmem with ⟨y, hy, _⟩
      exact ⟨y, hy⟩
    · intro x x' y hxy hx'y
      have hmem : (x, x') ∈ (f ≫ f†).rel := by
        rw [Hom.rel_comp, mem_comp]
        exact ⟨y, hxy, (mem_dagger f x' y).2 hx'y⟩
      rw [h.comp_dagger_eq_id, Hom.rel_id, mem_id] at hmem
      exact hmem
  · intro h; refine ⟨?_⟩
    apply Hom.ext; ext ⟨x, x'⟩
    rw [Hom.rel_comp, mem_comp, Hom.rel_id, mem_id]
    simp only; constructor
    · rintro ⟨y, hxy, hyx'⟩
      exact h.2 hxy ((mem_dagger f x' y).1 hyx')
    · intro hxx'; subst hxx'
      rcases h.1 x with ⟨y, hy⟩
      refine ⟨y, hy, ?_⟩
      exact (mem_dagger f x y).2 hy

/-- In `RelCat`, a projection is exactly a symmetric and transitive relation, i.e. a partial
equivalence relation. -/
theorem isProj_iff_symm_trans (f : End X) :
    DaggerCategory.IsProj f ↔ f.rel.IsSymm ∧ f.rel.IsTrans := by
  constructor
  · intro h; constructor
    · have hself : f†.rel = f.rel := congrArg Hom.rel h.selfAdjoint
      rw [rel_dagger] at hself
      exact (SetRel.inv_eq_self_iff).1 hself
    · have hrel : (f ≫ f).rel = f.rel := congrArg Hom.rel h.idem
      rw [Hom.rel_comp] at hrel
      exact SetRel.isTrans_iff_comp_subset_self.2 (by simp [hrel])
  · rintro ⟨hsymm, htrans⟩; constructor
    · rw [isIdempotentElem_iff, End.mul_def]
      apply Hom.ext; ext ⟨x, x'⟩
      rw [Hom.rel_comp, mem_comp]
      constructor
      · rintro ⟨y, hxy, hyx'⟩
        exact htrans.trans x y x' hxy hyx'
      · intro hxx'; refine ⟨x, ?_, hxx'⟩
        exact htrans.trans x x' x hxx' (hsymm.symm x x' hxx')
    · apply Hom.ext; ext ⟨x, x'⟩
      rw [mem_dagger]
      exact ⟨hsymm.symm x' x, hsymm.symm x x'⟩

/-- In `RelCat`, a positive morphism is exactly a symmetric relation that is reflexive on its
domain. -/
theorem isPositive_iff_isSymm_reflOnDom (f : End X) : DaggerCategory.IsPositive f ↔
    f.rel.IsSymm ∧ ∀ x : X, (∃ x' : X, (x, x') ∈ f.rel) → (x, x) ∈ f.rel := by
  constructor
  · intro h; rcases h.out with ⟨Y, g, hfg⟩
    constructor
    · constructor; intro a b hab
      rw [hfg, Hom.rel_comp, mem_comp] at hab ⊢
      rcases hab with ⟨y, hay, hyb⟩
      exact ⟨y, (mem_dagger g b y).1 hyb, (mem_dagger g a y).2 hay⟩
    · rintro x ⟨x', hxx'⟩
      rw [hfg, Hom.rel_comp, mem_comp] at hxx' ⊢
      rcases hxx' with ⟨y, hxy, _⟩
      exact ⟨y, hxy, (mem_dagger g x y).2 hxy⟩
  · rintro ⟨hsymm, hrefl⟩
    let E : RelCat.{u} := {p : X × X // p ∈ f.rel}
    let g : X ⟶ E := .ofRel {q : X × E | q.1 = q.2.1.1 ∨ q.1 = q.2.1.2}
    have hg : ∀ a e, (a, e) ∈ g.rel ↔ a = e.1.1 ∨ a = e.1.2 := by intros; rfl
    refine ⟨E, g, ?_⟩; apply Hom.ext
    ext ⟨a, b⟩; constructor
    · intro hab; rw [Hom.rel_comp, mem_comp]
      refine ⟨⟨(a, b), hab⟩, ?_, ?_⟩
      · exact (hg a ⟨(a, b), hab⟩).2 (Or.inl rfl)
      · exact (hg b ⟨(a, b), hab⟩).2 (Or.inr rfl)
    · intro hab
      rw [Hom.rel_comp, mem_comp] at hab
      rcases hab with ⟨e, hae, hbe⟩
      rcases (hg a e).1 hae with (rfl | rfl) <;> rcases (hg b e).1 hbe with (rfl | rfl)
      · exact hrefl e.1.1 ⟨e.1.2, e.2⟩
      · exact e.2
      · exact hsymm.symm e.1.1 e.1.2 e.2
      · exact hrefl e.1.2 ⟨e.1.1, hsymm.symm e.1.1 e.1.2 e.2⟩

end CategoryTheory.RelCat
