import TwistedYetter.Kirby.PresentationIsotopy

namespace TwistedYetter.Mutations.MissingSphericalCutCyclicity

open CategoryTheory
open TwistedYetter.Kirby.PresentationIsotopy

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

variable
  (close : (X : C) → (X ⟶ X) → (𝟙_ C ⟶ 𝟙_ C))

/-- This must fail: a closure operation without cyclicity is not admitted. -/
def missingCyclicity : SphericalCutTrace (C := C) where
  close := close
  source_ref := "ref:mutation"
  source_locator := "deliberately incomplete"

end TwistedYetter.Mutations.MissingSphericalCutCyclicity
