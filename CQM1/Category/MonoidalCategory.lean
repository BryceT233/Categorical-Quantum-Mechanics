/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib
public import CQM1.Category.DaggerCategory

/-! xxxxx **Assisted by Deepseek Harness** -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C]

section

variable [MonoidalCategory.{v} C]

/-- scalar -/
abbrev Scalar (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] : Type _ := End (𝟙_ C)

@[reassoc]
private lemma whiskerRight_leftUnitor (s : Scalar C) :
    (s ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ s :=
  unitors_equal (C := C) ▸ rightUnitor_naturality s

private lemma scalar_tensor_eq_comp (s t : Scalar C) :
    (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom = s ≫ t := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality, whiskerRight_leftUnitor_assoc]
  simp

private lemma scalar_tensor_eq_comp_rev (s t : Scalar C) :
    (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom = t ≫ s := by
  have : s ⊗ₘ t = (𝟙_ C ◁ t) ≫ (s ▷ 𝟙_ C) := by
    rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
  rw [this, Category.assoc, whiskerRight_leftUnitor, leftUnitor_naturality_assoc]
  simp

@[reassoc]
lemma comp_comm {s t : End (𝟙_ C)} : s ≫ t = t ≫ s := by
  rw [← scalar_tensor_eq_comp, scalar_tensor_eq_comp_rev]

/-- Scalar endomorphisms of the monoidal unit commute. -/
instance Scalar.commMonoid : CommMonoid (Scalar C) where
  mul_comm _ _ := by rw [End.mul_def, End.mul_def, comp_comm]

instance {c₁ c₂ : C} : SMul (Scalar C) (c₁ ⟶ c₂) where
  smul s f := (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom

lemma smul_def {c₁ c₂ : C} {s : Scalar C} {f : c₁ ⟶ c₂} :
    s • f = (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom := rfl

/-- Scalar multiplication is associative: acting on a morphism by `s` then `t` agrees with
acting by the scalar product `t * s`. -/
lemma smul_assoc {c₁ c₂ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} : s • t • f = (t * s) • f := by
  rw [smul_def, smul_def, smul_def, End.mul_def, ← scalar_tensor_eq_comp]
  simp [tensorHom_def]

lemma smul_comp_smul {c₁ c₂ c₃ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
    (s • f) ≫ (t • g) = (s * t) • (f ≫ g) := by
  simp [comp_comm, smul_def]

/-- state -/
abbrev State (c : C) : Type _ := 𝟙_ C ⟶ c

/-- joint state -/
abbrev JointState (c₁ c₂ : C) : Type _ := 𝟙_ C ⟶ c₁ ⊗ c₂

/-- A joint state is entangled -/
def JointState.Entangled {c₁ c₂ : C} (f : JointState c₁ c₂) : Prop :=
  ∀ (g : State c₁) (h : State c₂), f ≠ (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)

lemma JointState.not_entangled_iff {c₁ c₂ : C} (f : JointState c₁ c₂) :
    ¬ f.Entangled ↔ ∃ (g : State c₁) (h : State c₂), f = (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h) := by
  simp [JointState.Entangled]

/-- effect -/
abbrev Effect (c : C) : Type _ := c ⟶ 𝟙_ C

end

/-- probability -/
abbrev probability [MonoidalDaggerCategory C] {c : C} (a : 𝟙_ C ⟶ c) (x : c ⟶ 𝟙_ C) :
    Scalar C := a ≫ x ≫ x† ≫ a†

end CategoryTheory.MonoidalCategory
