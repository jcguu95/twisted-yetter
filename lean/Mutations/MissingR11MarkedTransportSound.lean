import TwistedYetter.Kirby.HomologicallyTwistedInvariant

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe uH

example
    (H2 : Type uH)
    [AddCommGroup H2]
    (completeness : TableTwoLinkCompleteness H2)
    (represents :
      (presentation : SpecialKirbyPresentation H2) →
        H2 → H2 → Prop)
    (chosenPresentation :
      H2 → SpecialKirbyPresentation H2)
    (chosenCoordinate : H2 → H2)
    (chosen_represents :
      (alpha : H2) →
        represents (chosenPresentation alpha) (chosenCoordinate alpha) alpha)
    (markingCertificateHash : String)
    (marking_hash_shape :
      RawPresentation.sha256Shape markingCertificateHash = true)
    (sourceRefs : List String)
    (exactMarkedScope sourceScopeCaveat : String) :
    MarkedPairPresentationSystem H2 where
  completeness := completeness
  represents := represents
  chosenPresentation := chosenPresentation
  chosenCoordinate := chosenCoordinate
  chosen_represents := chosen_represents
  markingCertificateHash := markingCertificateHash
  marking_certificate_hash_shape := marking_hash_shape
  sourceRefs := sourceRefs
  exactMarkedScope := exactMarkedScope
  sourceScopeCaveat := sourceScopeCaveat

end TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations
