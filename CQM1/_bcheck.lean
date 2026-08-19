import CQM1.RelCat

open CategoryTheory
open scoped MonoidalCategory

namespace CategoryTheory.RelCat

universe u

variable {X Y Z : RelCat.{u}}

-- naturality_right : X ◁ f ≫ (β_ X Z).hom = (β_ X Y).hom ≫ f ▷ X
example (X : RelCat.{u}) (f : Y ⟶ Z) :
    X ◁ f ≫ (β_ X Z).hom = (β_ X Y).hom ≫ f ▷ X := by
  apply Hom.ext; ext ⟨⟨x, y⟩, ⟨z'', x'⟩⟩
  rw [Hom.rel_comp, mem_comp, Hom.rel_comp, mem_comp]
  constructor
  · rintro ⟨⟨x'', z'⟩, hxf, hβ⟩
    rw [mem_whiskerLeft] at hxf
    change (z', x'') = (z'', x') at hβ
    refine ⟨(y, x), by tauto, ?_⟩
    rw [mem_whiskerRight]; grind only
  · rintro ⟨⟨y', x''⟩, hβ, hfx⟩
    change (y, x) = (y', x'') at hβ
    rw [mem_whiskerRight] at hfx
    refine ⟨(x, z''), ?_, ?_⟩
    · rw [mem_whiskerLeft]; grind only
    · change (z'', x) = (z'', x'); grind only

-- hexagon_forward
example (X Y Z : RelCat.{u}) :
    (α_ X Y Z).hom ≫ (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((β_ X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (β_ X Z).hom) := by
  apply Hom.ext; ext ⟨⟨⟨x, y⟩, z⟩, ⟨y', ⟨z', x'⟩⟩⟩; constructor
  · rintro ⟨p, hα₁, hrest⟩
    rw [mem_associator_hom] at hα₁
    subst p
    rcases hrest with ⟨⟨⟨m₁, m₂⟩, m₃⟩, hβ, hα₂⟩
    change ((y, z), x) = ((m₁, m₂), m₃) at hβ
    rw [mem_associator_hom] at hα₂
    refine ⟨((y, x), z), ?_, ?_⟩
    · rw [mem_whiskerRight]
      change (y, x) = (y, x) ∧ z = z
      tauto
    · refine ⟨(y, (x, z)), ?_, ?_⟩
      · rw [mem_associator_hom]
      · rw [mem_whiskerLeft]
        change y = y' ∧ (z, x) = (z', x')
        grind only
  · rintro ⟨⟨⟨y'', x''⟩, z''⟩, hβ₁, hrest⟩
    rw [mem_whiskerRight] at hβ₁
    change (y, x) = (y'', x'') ∧ z = z'' at hβ₁
    rcases hrest with ⟨q, hα₁, hrest'⟩
    rw [mem_associator_hom] at hα₁
    subst q
    rw [mem_whiskerLeft] at hrest'
    change y'' = y' ∧ (z'', x'') = (z', x') at hrest'
    refine ⟨(x, (y, z)), ?_, ?_⟩
    · rw [mem_associator_hom]
    · refine ⟨((y, z), x), ?_, ?_⟩
      · change ((y, z), x) = ((y, z), x); rfl
      · rw [mem_associator_hom]
        ext <;> grind only

-- hexagon_reverse
example (X Y Z : RelCat.{u}) :
    (α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((β_ X Z).hom ▷ Y) := by
  apply Hom.ext; ext ⟨⟨x, ⟨y, z⟩⟩, ⟨⟨z', x'⟩, y'⟩⟩; constructor
  · rintro ⟨p, hα₁, hrest⟩
    change ((x, y), z) = p at hα₁
    subst p
    rcases hrest with ⟨q, hβ, hα₂⟩
    change (z, (x, y)) = q at hβ
    subst q
    change ((z, x), y) = ((z', x'), y') at hα₂
    refine ⟨(x, (z, y)), ?_, ?_⟩
    · rw [mem_whiskerLeft]
      change x = x ∧ (z, y) = (z, y)
      tauto
    · refine ⟨((x, z), y), ?_, ?_⟩
      · change ((x, z), y) = ((x, z), y); rfl
      · rw [mem_whiskerRight]
        change (z, x) = (z', x') ∧ y = y'
        grind only
  · rintro ⟨⟨x'', ⟨z'', y''⟩⟩, hw, hrest⟩
    rw [mem_whiskerLeft] at hw
    change x = x'' ∧ (z, y) = (z'', y'') at hw
    rcases hrest with ⟨q, hα₁, hrest'⟩
    change ((x'', z''), y'') = q at hα₁
    subst q
    rw [mem_whiskerRight] at hrest'
    change (z'', x'') = (z', x') ∧ y'' = y' at hrest'
    refine ⟨((x, y), z), ?_, ?_⟩
    · change ((x, y), z) = ((x, y), z); rfl
    · refine ⟨(z, (x, y)), ?_, ?_⟩
      · change (z, (x, y)) = (z, (x, y)); rfl
      · change ((z, x), y) = ((z', x'), y')
        grind only

end CategoryTheory.RelCat
