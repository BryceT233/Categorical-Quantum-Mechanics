import CQM1.RelCat

open CategoryTheory
open scoped MonoidalCategory

namespace CategoryTheory.RelCat

universe u

variable {X Y : RelCat.{u}}

example (X Y : RelCat.{u}) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by
  apply Hom.ext; ext ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  rw [Hom.rel_comp, mem_comp, Hom.rel_id, mem_id]
  constructor
  · rintro ⟨⟨y'', x''⟩, hβ₁, hβ₂⟩
    change (y, x) = (y'', x'') at hβ₁
    change (x'', y'') = (x', y') at hβ₂
    grind only
  · intro h
    refine ⟨(y, x), by tauto, ?_⟩
    change (x, y) = (x', y')
    exact h

end CategoryTheory.RelCat
