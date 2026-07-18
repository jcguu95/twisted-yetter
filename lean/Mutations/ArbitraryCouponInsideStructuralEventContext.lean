import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.ArbitraryCouponInsideStructuralEventContext

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/--
This must fail: coherence-only event contexts have no arbitrary coupon
constructor.
-/
def hiddenCoupon
    {source target : Boundary C}
    (morphism : source.denote ⟶ target.denote) :
    StructuralDiagram C source target :=
  StructuralDiagram.coupon "hidden-event-context-morphism" morphism

end TwistedYetter.Mutations.ArbitraryCouponInsideStructuralEventContext
