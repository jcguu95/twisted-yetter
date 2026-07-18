import TwistedYetter.Kirby.HomologicallyTwistedInvariant

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe uH

example
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target)
    (graphicalCertificateHash : String)
    (graphical_hash_shape :
      RawPresentation.sha256Shape graphicalCertificateHash = true) :
    LocalEvaluationBinding move where
  graphicalCertificateHash := graphicalCertificateHash
  graphical_certificate_hash_shape := graphical_hash_shape

end TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations
