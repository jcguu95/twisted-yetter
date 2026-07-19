import TwistedYetter.Kirby.PresentationIsotopy

namespace TwistedYetter.Mutations.MissingSphericalCutCyclicity

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.PresentationIsotopy

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/-- This must fail: spherical metadata without trace cyclicity is not admitted. -/
def missingCyclicity
    (spherical : SphericalStructure (C := C)) :
    SphericalTraceLaws spherical where
  source_ref := "ref:mutation"
  source_locator := "deliberately incomplete"

end TwistedYetter.Mutations.MissingSphericalCutCyclicity
