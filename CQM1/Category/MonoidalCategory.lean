/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import CQM1.Category.DaggerCategory
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Scalars, states and effects in a monoidal category

This file develops the basic ingredients of categorical quantum mechanics in an arbitrary
monoidal category `C`. The scalars of `C` are the endomorphisms of its monoidal unit `𝟙_ C`;
they form a commutative monoid (by the Eckmann-Hilton argument) and act on every hom-set by
scalar multiplication. We also define states, joint states and entanglement, effects, and the
Born-rule probability of an effect in a state (for a monoidal dagger category).

## Main definitions

* `Scalar`: the scalars of a monoidal category, i.e. `End (𝟙_ C)`.
* `State` and `JointState`: morphisms from the monoidal unit into an object, resp. a tensor
  product of two objects.
* `JointState.Entangled`: the property that a joint state is not a product state.
* `Effect`: morphisms into the monoidal unit.
* `probability`: the Born-rule probability of an effect in a state.

## Main results

* `Scalar.commMonoid`: the scalars of a monoidal category form a commutative monoid.
* `comp_comm`: endomorphisms of the monoidal unit commute under composition.
* `smul_assoc` and `smul_comp_smul`: the scalar action is associative and satisfies the
  interchange law with composition.
* `JointState.not_entangled_iff`: a joint state is not entangled iff it is a product state.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C]

section

variable [MonoidalCategory.{v} C]

/-- The scalars of a monoidal category `C`, i.e. the endomorphisms of its monoidal unit
`𝟙_ C`. They form a commutative monoid (see `Scalar.commMonoid`) and act on every hom-set by
scalar multiplication (see the `SMul` instance below). -/
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

/-- Endomorphisms of the monoidal unit commute under composition. -/
@[reassoc]
lemma comp_comm {s t : End (𝟙_ C)} : s ≫ t = t ≫ s := by
  rw [← scalar_tensor_eq_comp, scalar_tensor_eq_comp_rev]

/-- Scalar endomorphisms of the monoidal unit commute. -/
instance Scalar.commMonoid : CommMonoid (Scalar C) where
  mul_comm _ _ := by rw [End.mul_def, End.mul_def, comp_comm]

instance {c₁ c₂ : C} : SMul (Scalar C) (c₁ ⟶ c₂) where
  smul s f := (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom

/-- The scalar action of `s : Scalar C` on a morphism `f : c₁ ⟶ c₂` is given by tensoring
with `s` and transporting across the left unitors. -/
lemma smul_def {c₁ c₂ : C} {s : Scalar C} {f : c₁ ⟶ c₂} :
    s • f = (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom := rfl

/-- Scalar multiplication is associative: acting on a morphism by `s` then `t` agrees with
acting by the scalar product `t * s`. -/
lemma smul_assoc {c₁ c₂ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} : s • t • f = (t * s) • f := by
  rw [smul_def, smul_def, smul_def, End.mul_def, ← scalar_tensor_eq_comp]
  simp [tensorHom_def]

/-- Scalar multiplication satisfies the interchange law with composition:
`(s • f) ≫ (t • g) = (s * t) • (f ≫ g)`. -/
lemma smul_comp_smul {c₁ c₂ c₃ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
    (s • f) ≫ (t • g) = (s * t) • (f ≫ g) := by
  simp [comp_comm, smul_def]

/-- A state of an object `c` is a morphism from the monoidal unit `𝟙_ C` into `c`. -/
abbrev State (c : C) : Type _ := 𝟙_ C ⟶ c

/-- A joint state of two objects `c₁` and `c₂` is a morphism from the monoidal unit `𝟙_ C`
into their tensor product `c₁ ⊗ c₂`. -/
abbrev JointState (c₁ c₂ : C) : Type _ := 𝟙_ C ⟶ c₁ ⊗ c₂

/-- A joint state `f : JointState c₁ c₂` is entangled if it is not a product state, i.e. if
it cannot be written as `(λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)` for states `g : State c₁` and
`h : State c₂`. -/
def JointState.Entangled {c₁ c₂ : C} (f : JointState c₁ c₂) : Prop :=
  ∀ (g : State c₁) (h : State c₂), f ≠ (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)

/-- A joint state is not entangled iff it is a product state, i.e. of the form
`(λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)` for states `g` and `h`. -/
lemma JointState.not_entangled_iff {c₁ c₂ : C} (f : JointState c₁ c₂) :
    ¬ f.Entangled ↔ ∃ (g : State c₁) (h : State c₂), f = (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h) := by
  simp [JointState.Entangled]

/-- An effect on an object `c` is a morphism from `c` into the monoidal unit `𝟙_ C`. -/
abbrev Effect (c : C) : Type _ := c ⟶ 𝟙_ C

end

/-- The probability associated to a state and an effect of an object in a monoidal dagger category,
given by the scalar `a ≫ x ≫ x† ≫ a†`. -/
abbrev probability [MonoidalDaggerCategory C] {c : C} (a : State c) (x : Effect c) :
    Scalar C := a ≫ x ≫ x† ≫ a†

end CategoryTheory.MonoidalCategory
