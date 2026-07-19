import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.UnboundFramingStrandInWindow

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.Presentation

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/--
This must fail: a one-strand framing window cannot omit the proof that the
retained strand is the exact strand named by the serialized event.
-/
def unsafeWindow
    (objectOf : StrandState → C)
    (requestedStrandId : String)
    (leading suffix : List StrandState)
    (strand : StrandState) :
    WindowedFramingTwistEvent objectOf requestedStrandId
      (leading ++ ([strand] ++ suffix))
      (leading ++ ([strand] ++ suffix)) where
  leading := leading
  strand := strand
  suffix := suffix
  before_sound := rfl
  after_sound := rfl

end TwistedYetter.Mutations.UnboundFramingStrandInWindow
