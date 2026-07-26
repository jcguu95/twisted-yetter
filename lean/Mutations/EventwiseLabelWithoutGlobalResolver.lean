import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant

namespace TwistedYetter.Mutations.EventwiseLabelWithoutGlobalResolver

open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe uH

variable {S : Type}

def rejected
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation H2)
    (labeling : GlobalLabeling (S := S) topology)
    (eventwiseLabel : String → S) :
    LabelledComponentResolver topology labeling where
  labelOf := eventwiseLabel

end TwistedYetter.Mutations.EventwiseLabelWithoutGlobalResolver
