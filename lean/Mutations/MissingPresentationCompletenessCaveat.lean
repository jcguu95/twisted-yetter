import TwistedYetter.Kirby.PresentationIsotopy

namespace TwistedYetter.Mutations.MissingPresentationCompletenessCaveat

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.PresentationIsotopy

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]
variable {Link : Type w}
variable
  (represents : Diagram C .unit .unit → Link → Prop)
  (connected :
    {left right : Diagram C .unit .unit} → {link : Link} →
    represents left link → represents right link →
    GeneratedIsotopy left right)

/-- This must fail: the cited coherence theorem's scope caveat is mandatory. -/
def missingSourceCaveat :
    FramedLinkPresentationCompleteness (C := C) Link where
  represents := represents
  connected := connected
  source_ref := "ref:mutation"
  source_locator := "deliberately incomplete"

end TwistedYetter.Mutations.MissingPresentationCompletenessCaveat
