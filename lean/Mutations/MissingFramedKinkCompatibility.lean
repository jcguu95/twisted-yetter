import TwistedYetter.Kirby.PresentationIsotopy

namespace TwistedYetter.Mutations.MissingFramedKinkCompatibility

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.PresentationIsotopy

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

variable
  (twist : NaturalTwist C)
  (positiveSound : (X : C) →
    eval C (positiveKink X) = twist.iso.hom.app X)

/-- This must fail: inverse-kink compatibility cannot be omitted. -/
def missingNegativeSound : FramedKinkCompatibility (C := C) where
  twist := twist
  positive_sound := positiveSound
  source_ref := "ref:mutation"
  source_locator := "deliberately incomplete"

end TwistedYetter.Mutations.MissingFramedKinkCompatibility
