/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib

/-! xxxxx **Assisted by Deepseek Harness** -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

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

end CategoryTheory.MonoidalCategory
