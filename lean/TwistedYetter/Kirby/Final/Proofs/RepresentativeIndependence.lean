import TwistedYetter.Kirby.Final.Proofs.DottedRepresentativeIndependence

/-!
# Representative independence

The former projector-site proof in this module conflated physical strand
orientation with dotted-disk incidence when forming character powers.  That
route has been removed.  The public theorem below is a thin exported name for
the dotted-collar incidence proof.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open TwistedYetter.Semantics.Independent
open CategoryTheory

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The frozen evaluator depends only on the THAM-side second-homology class.
This theorem is proved through dotted-collar incidence morphisms; dotted direction never
chooses `X` versus `X*` and never supplies a character exponent.
-/
theorem frozenFrontendRepresentativeIndependence
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram) :
    RepresentativeIndependenceStatement
      𝒞η diagram presentation :=
  dottedFrozenFrontendRepresentativeIndependence
    𝒞η diagram presentation

end

end TwistedYetter.Kirby.Final.Proofs
