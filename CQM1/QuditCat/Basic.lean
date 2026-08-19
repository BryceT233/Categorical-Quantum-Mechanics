/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import CQM1.Category.DaggerCategory
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.RingTheory.PicardGroup

/-!
# The category of qudits

This file defines `QuditCat`, the category of qudits: objects are finite-dimensional
complex Hilbert spaces (the state spaces of qudits) and morphisms are linear maps between
them. The category is equipped with a dagger structure given by the adjoint, a monoidal
structure given by the tensor product, and it is shown that these interact to form a
braided, symmetric monoidal dagger category. The file also sets up Dirac bra-ket notation,
the standard `n`-dimensional Hilbert space `ℂⁿ` with its computational basis, and the
usual single-qubit gates.

## Main definitions

* `QuditCat`: the category of finite-dimensional complex Hilbert spaces.
* `QuditCat.Hom`: a morphism between two qudits, i.e. a linear map of the underlying
  state spaces.
* `QuditCat.bra` and `QuditCat.ket`: the bra and ket maps of a state.
* `QuditCat.std` and `QuditCat.ZBasis`: the standard `n`-dimensional Hilbert space and
  its computational basis.
* `QuditCat.matrixToEnd`: a matrix, interpreted as an endomorphism of the standard space.
* `QuditCat.Qubit`: the 2-dimensional qubit space.

## Notation

* `⟨a|` is notation for the bra functional of a state `a`.
* `|b⟩` is notation for the ket map of a state `b`.
* `⟨v|u⟩` is notation for the inner product of `v` and `u`.

## Main results

* `QuditCat` is a dagger category, a braided monoidal category, a symmetric monoidal
  category, and a monoidal dagger category.
* `isUnitary_matrixToEnd_iff` characterizes unitary matrices by `M * star M = 1`.

## Implementation notes

The universe level of state spaces is fixed to `Type` for simplicity.
-/

@[expose] public section

open CategoryTheory

/-- The category of qudits, where the universe level of state spaces is fixed to be 0
for simplicity. Objects in this category represent finite-dimensional quantum state spaces. -/
structure QuditCat where
  /-- Construct an object in `QuditCat` from a state space. -/
  of ::
  /-- The underlying finite-dimensional Hilbert space of a qudit. -/
  State : Type
  [isNormedAddCommGroup : NormedAddCommGroup State]
  [isInnerProductSpace : InnerProductSpace ℂ State]
  [finiteDim : FiniteDimensional ℂ State]

initialize_simps_projections QuditCat (-isNormedAddCommGroup, -isInnerProductSpace, -finiteDim)
attribute [instance] QuditCat.isNormedAddCommGroup QuditCat.isInnerProductSpace QuditCat.finiteDim

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `QuditCat.of X` being printed as
`{ Qudit := X, isNormedAddCommGroup := ... }` by `delabStructureInstance`. -/
@[app_delab QuditCat.of]
meta def QuditCat.delabOf : Delab := delabApp

end Notation

namespace QuditCat

lemma of_state {H : QuditCat} : of H.State = H := rfl

lemma state_of (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] : (of X).State = X := rfl

section Hom

/-- The type of morphisms in `QuditCat`. -/
@[ext]
structure Hom (H₁ H₂ : QuditCat) where
  private mk ::
  /-- The underlying linear map between the state spaces. -/
  hom' : H₁.State →ₗ[ℂ] H₂.State

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance largeCategory : LargeCategory QuditCat where
  Hom H₁ H₂ := Hom H₁ H₂
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance concreteCategory : ConcreteCategory QuditCat (fun H₁ H₂ ↦ H₁.State →ₗ[ℂ] H₂.State) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `QuditCat` back into a `LinearMap`. -/
abbrev Hom.hom {H₁ H₂ : QuditCat} (f : Hom H₁ H₂) :=
  ConcreteCategory.hom (C := QuditCat) f

/-- Typecheck a `LinearMap` as a morphism in `QuditCat`. -/
abbrev ofHom {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [FiniteDimensional ℂ Y] (f : X →ₗ[ℂ] Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := QuditCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (H₁ H₂ : QuditCat) (f : Hom H₁ H₂) := f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_id {H : QuditCat} : (𝟙 H : H ⟶ H).hom = LinearMap.id := rfl

lemma id_apply (H : QuditCat) (x : H.State) : 𝟙 H x = x := by simp

@[simp]
lemma hom_comp {H₁ H₂ H₃ : QuditCat} (f : H₁ ⟶ H₂) (g : H₂ ⟶ H₃) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma comp_apply {H₁ H₂ H₃ : QuditCat} (f : H₁ ⟶ H₂) (g : H₂ ⟶ H₃) (x : H₁.State) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {H₁ H₂ : QuditCat} {f g : H₁ ⟶ H₂} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_bijective {H₁ H₂ : QuditCat} :
    Function.Bijective (Hom.hom : (H₁ ⟶ H₂) → (H₁.State →ₗ[ℂ] H₂.State)) where
  left f g h := by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩

/-- Convenience shortcut for `ModuleCat.hom_bijective.injective`. -/
lemma hom_injective {H₁ H₂ : QuditCat} :
    Function.Injective (Hom.hom : (H₁ ⟶ H₂) → (H₁.State →ₗ[ℂ] H₂.State)) :=
  hom_bijective.injective

/-- Convenience shortcut for `ModuleCat.hom_bijective.surjective`. -/
lemma hom_surjective {H₁ H₂ : QuditCat} :
    Function.Surjective (Hom.hom : (H₁ ⟶ H₂) → (H₁.State →ₗ[ℂ] H₂.State)) :=
  hom_bijective.surjective

@[simp]
lemma hom_ofHom {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [FiniteDimensional ℂ Y] (f : X →ₗ[ℂ] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {H₁ H₂ : QuditCat} (f : H₁ ⟶ H₂) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] : ofHom LinearMap.id = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [FiniteDimensional ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    [FiniteDimensional ℂ Z] (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [FiniteDimensional ℂ Y] (f : X →ₗ[ℂ] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply {H₁ H₂ : QuditCat} (e : H₁ ≅ H₂) (x : H₁.State) :
    e.inv (e.hom x) = x := by simp

lemma hom_inv_apply {H₁ H₂ : QuditCat} (e : H₁ ≅ H₂) (x : H₂.State) :
    e.hom (e.inv x) = x := by simp

/-- `QuditCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {H₁ H₂ : QuditCat} : (H₁ ⟶ H₂) ≃ (H₁.State →ₗ[ℂ] H₂.State) where
  toFun := Hom.hom
  invFun := ofHom

/-- Build an isomorphism in the category `QuditCat` from an `LinearEquiv` between
finite dimensional Hilbert spaces. -/
def isoMk {X Y : Type} {_ : NormedAddCommGroup X} {_ : InnerProductSpace ℂ X}
    {_ : FiniteDimensional ℂ X} {_ : NormedAddCommGroup Y} {_ : InnerProductSpace ℂ Y}
    {_ : FiniteDimensional ℂ Y} (e : X ≃ₗ[ℂ] Y) : of X ≅ of Y where
  hom := ofHom (e : X →ₗ[ℂ] Y)
  inv := ofHom (e.symm : Y →ₗ[ℂ] X)

/-- Build an `LinearEquiv` from an isomorphism in the category `QuditCat`. -/
def linearEquivOfIso {H₁ H₂ : QuditCat} (i : H₁ ≅ H₂) : H₁.State ≃ₗ[ℂ] H₂.State where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv _ := by simp
  right_inv _ := by simp

end Hom

noncomputable instance daggerCategory : DaggerCategory QuditCat where
  dagger f := ofHom (f.hom.adjoint)
  dagger_comp f g := by simp
  dagger_id f := by simp
  involutive_dagger f := by simp

open DaggerCategory

@[simp]
lemma hom_dagger {H₁ H₂ : QuditCat} (f : H₁ ⟶ H₂) : f†.hom = f.hom.adjoint := rfl

noncomputable section

open TensorProduct MonoidalCategory

instance : MonoidalCategoryStruct QuditCat where
  tensorObj H₁ H₂ := of (H₁.State ⊗[ℂ] H₂.State)
  whiskerLeft _ _ _ f := ofHom (TensorProduct.map LinearMap.id f.hom)
  whiskerRight f _ := ofHom (TensorProduct.map f.hom LinearMap.id)
  tensorUnit := of ℂ
  associator X Y Z := isoMk (TensorProduct.assoc ℂ X.State Y.State Z.State)
  leftUnitor X := isoMk (TensorProduct.lid ℂ X.State)
  rightUnitor X := isoMk (TensorProduct.rid ℂ X.State)

instance : MonoidalCategory QuditCat where
  id_tensorHom_id X₁ X₂ := by
    apply hom_ext; apply TensorProduct.ext'
    intros; rfl
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    apply hom_ext; apply TensorProduct.ext'
    intros; rfl
  whiskerLeft_id X Y := by
    apply hom_ext; apply TensorProduct.ext'
    intros; rfl
  id_whiskerRight X Y := by
    apply hom_ext; apply TensorProduct.ext'
    intros; rfl
  associator_naturality f₁ f₂ f₃ := by
    apply hom_ext; apply TensorProduct.ext_threefold
    intros; rfl
  leftUnitor_naturality := by
    intro X Y f
    apply hom_ext; apply TensorProduct.ext'
    intro c x
    change TensorProduct.lid ℂ Y.State (TensorProduct.map LinearMap.id f.hom (c ⊗ₜ x)) =
      f.hom (TensorProduct.lid ℂ X.State (c ⊗ₜ x))
    simp
  rightUnitor_naturality := by
    intro X Y f
    apply hom_ext; apply TensorProduct.ext'
    intro x c
    change TensorProduct.rid ℂ Y.State (TensorProduct.map f.hom LinearMap.id (x ⊗ₜ c)) =
      f.hom (TensorProduct.rid ℂ X.State (x ⊗ₜ c))
    simp
  pentagon W X Y Z := by
    apply hom_ext; apply TensorProduct.ext_fourfold
    intros; rfl
  triangle X Y := by
    apply hom_ext; apply TensorProduct.ext_threefold
    intros; exact TensorProduct.tmul_smul ..

lemma hom_tensorHom {X₁ Y₁ X₂ Y₂ : QuditCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := by
  change ((f ▷ X₂) ≫ (Y₁ ◁ g)).hom = _
  simp only [hom_comp]
  apply TensorProduct.ext'
  intros; rfl

lemma isUnitary_isoMk_coe_linearIsometry {H₁ H₂ : QuditCat} (e : H₁.State ≃ₗᵢ[ℂ] H₂.State) :
    IsUnitary (c₁ := H₁) (c₂ := H₂) (isoMk e.toLinearEquiv).hom := by
  apply isUnitary_of_dagger_eq_inv
  apply hom_ext
  exact e.adjoint_toLinearMap_eq_symm

instance monoidalDaggerCategory : MonoidalDaggerCategory QuditCat where
  dagger_tensor f₁ f₂ := by
    apply hom_ext
    rw [hom_dagger, hom_tensorHom f₁ f₂, hom_tensorHom f₁† f₂†]
    exact adjoint_map f₁.hom f₂.hom
  isUnitary_associator H₁ H₂ H₃ := by
    dsimp [associator]
    rw [← toLinearEquiv_assocIsometry]
    exact isUnitary_isoMk_coe_linearIsometry ..
  isUnitary_leftUnitor H := by
    dsimp [leftUnitor]
    rw [← toLinearEquiv_lidIsometry]
    exact isUnitary_isoMk_coe_linearIsometry ..
  isUnitary_rightUnitor H := by
    dsimp [rightUnitor]
    rw [← toLinearEquiv_ridIsometry]
    exact isUnitary_isoMk_coe_linearIsometry ..

instance : BraidedCategory QuditCat where
  braiding H₁ H₂ := isoMk (TensorProduct.comm ..)
  braiding_naturality_left f H := by
    apply hom_ext; apply TensorProduct.ext'
    intros; rfl
  braiding_naturality_right H f K g := by
    apply hom_ext; apply TensorProduct.ext'
    intros; rfl
  hexagon_forward H K L := by
    apply hom_ext; apply TensorProduct.ext_threefold
    intros; rfl
  hexagon_reverse H K L := by
    apply hom_ext; apply TensorProduct.ext_threefold'
    intros; rfl

instance symmetricCategory : SymmetricCategory QuditCat where
  symmetry H₁ H₂ := by
    apply hom_ext
    rw [hom_comp, hom_id]
    exact TensorProduct.comm_comp_comm ..

end

section braket

/-- Converts a quantum state `a : H.State` into its corresponding bra functional `⟨a|`. -/
noncomputable def bra {H : QuditCat} (a : H.State) : H.State →ₗ[ℂ] ℂ := innerₛₗ ℂ a

/-- Notation `⟨a|` for the bra functional of a state `a`. -/
notation "⟨" u "|" => bra u

@[simp]
lemma bra_apply {H : QuditCat} (a b : H.State) : ⟨a| b = inner ℂ a b := rfl

/-- Converts a quantum state `b : H.State` into its corresponding ket map |b⟩. -/
def ket {H : QuditCat} (b : H.State) : ℂ →ₗ[ℂ] H.State := .toSpanSingleton ℂ H.State b

/-- Notation `|b⟩` for the ket map of a state `b`. -/
notation "|" u "⟩" => ket u

@[simp]
lemma hom_ket_apply {H : QuditCat} (b : H.State) (x : ℂ) : |b⟩ x = x • b := rfl

/-- Notation `⟨v|u⟩` for the inner product of states `v` and `u`. -/
notation "⟨" v "|" u "⟩" => inner ℂ v u

@[simp]
lemma ket_comp_bra {H : QuditCat} (a b : H.State) : ⟨b| ∘ₗ |a⟩ = .lsmul ℂ _ ⟨b|a⟩ := by
  ext; simp

/-- Morphism in `QuditCat` corresponding to the bra functional `⟨a|`. -/
noncomputable def braArrow {H : QuditCat} (a : H.State) : H ⟶ of ℂ := ofHom (bra a)

/-- Morphism in `QuditCat` corresponding to the ket map `|b⟩`. -/
noncomputable def ketArrow {H : QuditCat} (b : H.State) : of ℂ ⟶ H := ofHom (ket b)

lemma ketArrow_comp_braArrow {H : QuditCat} (a b : H.State) :
    ketArrow a ≫ braArrow b = ofHom (.lsmul ℂ ℂ ⟨b|a⟩) := by
  ext1; rw [hom_comp]; exact ket_comp_bra a b

lemma hom_ketArrow_comp_braArrow_apply {H : QuditCat} (a b : H.State) (x : ℂ) :
    (ketArrow a ≫ braArrow b).hom x = ⟨b|a⟩ • x := by simp [ketArrow_comp_braArrow]

end braket

/-- A state is normalized if its norm is 1. -/
def State.Normalized {H : QuditCat} (v : H.State) : Prop := ⟨v|v⟩ = 1

noncomputable section standard

/-- The standard `n`-dimensional Hilbert space `ℂⁿ`, treated as an object in `QuditCat`. -/
def std (n : ℕ) : QuditCat := of (EuclideanSpace ℂ (Fin n))

lemma state_std (n : ℕ) : (std n).State = EuclideanSpace ℂ (Fin n) := rfl

/-- The computational basis for the standard `n`-dimensional Hilbert space `ℂⁿ`. -/
def ZBasis (n : ℕ) : OrthonormalBasis (Fin n) ℂ (std n).State :=
  EuclideanSpace.basisFun (Fin n) ℂ

lemma ZBasis_apply {n : ℕ} (i : Fin n) : ZBasis n i = EuclideanSpace.single i 1 :=
  EuclideanSpace.basisFun_apply ..

/-- The `i`-th computational basis vector representing `|i⟩`. -/
abbrev ithKet {n : ℕ} (i : Fin n) : (std n).State := ZBasis n i

lemma ithKet_eq_ket_ZBasis {n : ℕ} (i : Fin n) : ithKet i = |ZBasis n i⟩ 1 := by simp

/-- Converts an `n × n` complex matrix into an endomorphism on the standard `n`-dimensional
Hilbert space. The transformation is defined with respect to the computational basis. -/
abbrev matrixToEnd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : End (std n) :=
  ofHom (M.toLin (ZBasis n).toBasis (ZBasis n).toBasis)

lemma hom_matrixToEnd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (matrixToEnd M).hom = M.toLin (ZBasis n).toBasis (ZBasis n).toBasis := rfl

theorem isUnitary_matrixToEnd_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    DaggerCategory.IsUnitary (matrixToEnd M) ↔ M * star M = 1 := by
  constructor
  · intro hU
    apply (Matrix.toLin (ZBasis n).toBasis (ZBasis n).toBasis).injective
    rw [Matrix.toLin_mul (ZBasis n).toBasis (ZBasis n).toBasis (ZBasis n).toBasis M (star M),
      Matrix.toLin_one, Matrix.star_eq_conjTranspose,
      Matrix.toLin_conjTranspose (ZBasis n) (ZBasis n) M]
    exact congrArg Hom.hom hU.dagger_comp_eq_id
  · intro h
    refine { comp_dagger_eq_id := ?_, dagger_comp_eq_id := ?_ }
    · apply hom_ext
      rw [hom_comp, hom_dagger, hom_matrixToEnd, hom_id,
        ← Matrix.toLin_conjTranspose (ZBasis n) (ZBasis n) M,
        ← Matrix.toLin_mul (ZBasis n).toBasis (ZBasis n).toBasis (ZBasis n).toBasis
        M.conjTranspose M, ← Matrix.toLin_one (ZBasis n).toBasis]
      exact congrArg (Matrix.toLin (ZBasis n).toBasis (ZBasis n).toBasis) (mul_eq_one_comm.mp h)
    · apply hom_ext
      rw [hom_id, hom_comp, hom_dagger, hom_matrixToEnd,
        ← Matrix.toLin_conjTranspose (ZBasis n) (ZBasis n) M,
        ← Matrix.toLin_mul (ZBasis n).toBasis (ZBasis n).toBasis (ZBasis n).toBasis
        M M.conjTranspose, ← Matrix.toLin_one (ZBasis n).toBasis]
      exact congrArg (Matrix.toLin (ZBasis n).toBasis (ZBasis n).toBasis) h

open ComplexConjugate Complex

theorem isUnitary_matrixToEnd_of_iff_fin_two {a b c d : ℂ} :
    DaggerCategory.IsUnitary (matrixToEnd !![a, b; c, d]) ↔
      ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 ∧ ‖c‖ ^ 2 + ‖d‖ ^ 2 = 1 ∧ conj a * c + conj b * d = 0 := by
  trans ((‖a‖ : ℂ) ^ 2 + ‖b‖ ^ 2 = 1 ∧ a * conj c + b * conj d = 0) ∧
    c * conj a + d * conj b = 0 ∧ (‖c‖ : ℂ) ^ 2 + ‖d‖ ^ 2 = 1
  · simp [isUnitary_matrixToEnd_iff, ← Matrix.ext_iff, Fin.forall_fin_succ,
      Matrix.vecMul_apply_eq_sum, Complex.mul_conj']
  norm_cast
  refine ⟨fun h ↦ ⟨h.1.1, h.2.2, by rw [← h.2.1]; ring⟩, fun h ↦ ⟨⟨h.1, ?_⟩, ?_, h.2.1⟩⟩
  · rw [← star_inj, star_zero, ← h.2.2]; simp
  · rw [← h.2.2]; ring

theorem isUnitary_matrixToEnd_iff_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    DaggerCategory.IsUnitary (matrixToEnd M) ↔
      ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 = 1 ∧ ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2 = 1 ∧
        conj (M 0 0) * (M 1 0) + conj (M 0 1) * (M 1 1) = 0 := by
  rw [← Matrix.etaExpand_eq M]
  exact isUnitary_matrixToEnd_of_iff_fin_two

/-- The Qubit space, defined as the 2-dimensional standard Hilbert space `ℂ²`. -/
abbrev Qubit : QuditCat := std 2

namespace Qubit

/-- Pauli-X gate as an endomorphism of `Qubit`. -/
def pauliX : End Qubit := matrixToEnd !![0, 1; 1, 0]

/-- Pauli-Y gate as an endomorphism of `Qubit`. -/
def pauliY : End Qubit := matrixToEnd !![0, -I; I, 0]

/-- Pauli-Z gate as an endomorphism of `Qubit`. -/
def pauliZ : End Qubit := matrixToEnd !![1, 0; 0, -1]

/-- Phase shift gate as an endomorphism of `Qubit`. -/
def phaseShift (ϕ : ℝ) : End Qubit := matrixToEnd !![1, 0; 0, exp (ϕ * I)]

/-- Hadamard gate as an endomorphism of `Qubit`. -/
def H : End Qubit := matrixToEnd (((√2)⁻¹ : ℂ) • !![1, 1; 1, -1])

instance isUnitary_H : IsUnitary H := by
  rw [H, isUnitary_matrixToEnd_iff_fin_two]
  suffices (2⁻¹ : ℝ) + 2⁻¹ = 1 by simpa
  linarith

end Qubit

end standard

end QuditCat
