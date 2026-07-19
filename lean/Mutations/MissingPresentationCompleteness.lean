import TwistedYetter.Kirby.PresentationIsotopy

namespace TwistedYetter.Mutations.MissingPresentationCompleteness

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.PresentationIsotopy

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]
variable {Link : Type w}
variable
  (represents : Diagram C .unit .unit → Link → Prop)

/-- This must fail: source metadata cannot replace the connectedness witness. -/
def missingConnected :
    FramedLinkPresentationCompleteness (C := C) Link where
  represents := represents
  source_ref := "ref:mutation"
  source_locator := "deliberately incomplete"
  source_scope_caveat := "deliberately incomplete"

end TwistedYetter.Mutations.MissingPresentationCompleteness
