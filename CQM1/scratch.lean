import CQM1.Category.DaggerCategory
import Mathlib.CategoryTheory.Category.RelCat

open CategoryTheory
open SetRel

namespace CategoryTheory.RelCat

universe u

instance : DaggerCategory RelCat.{u} where
  dagger f := .ofRel (SetRel.inv f.rel)
  dagger_comp f g := RelCat.Hom.ext _ _ (SetRel.inv_comp f.rel g.rel)
  dagger_id X := by
    apply RelCat.Hom.ext
    exact SetRel.inv_id
  involutive_dagger f := by
    apply RelCat.Hom.ext
    change SetRel.inv (SetRel.inv f.rel) = f.rel
    exact SetRel.inv_inv

end CategoryTheory.RelCat
