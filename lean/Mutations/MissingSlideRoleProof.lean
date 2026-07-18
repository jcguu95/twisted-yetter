import TwistedYetter.Kirby.KirbyHandleMoves

namespace TwistedYetter.Mutations.MissingSlideRoleProof

open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation

/--
This must fail: serialized component roles cannot be admitted without the
kind-indexed role proof.
-/
def unsafeMetadata
    (distinct : "moving" ≠ "stationary") :
    SlideMetadata where
  moveId := "unsafe"
  kind := .oneOverOne
  orientation := .positive
  sourcePresentationHash :=
    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  targetPresentationHash :=
    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
  slidingComponentId := "moving"
  stationaryComponentId := "stationary"
  slidingRole := .ordinary
  stationaryRole := .ordinary
  framing := .oneOverOne
  component_ids_distinct := distinct

end TwistedYetter.Mutations.MissingSlideRoleProof
