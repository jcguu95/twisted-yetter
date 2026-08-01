import TwistedYetter.Kirby.Final.Proofs.IntrinsicRepresentativeIndependence

/-!
# Representative independence

The former projector-site proof in this module conflated physical strand
orientation with dotted-disk incidence when forming character powers.  That
route has been removed.  The public theorem below is now only a compatibility
name for the intrinsic dotted-cut proof.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The frozen evaluator depends only on the THAM-side second-homology class.
This theorem is proved through intrinsic dotted cuts; dotted direction never
chooses `X` versus `X*` and never supplies a character exponent.
-/
theorem frozenFrontendRepresentativeIndependence
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram) :
    RepresentativeIndependenceStatement 𝒞η diagram primal :=
  intrinsicFrozenFrontendRepresentativeIndependence 𝒞η diagram primal

end

end TwistedYetter.Kirby.Final.Proofs
