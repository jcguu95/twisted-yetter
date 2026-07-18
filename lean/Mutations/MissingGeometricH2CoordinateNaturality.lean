import TwistedYetter.Kirby.SourceBoundGeometricH2Compiler

namespace TwistedYetter.Mutations.MissingGeometricH2CoordinateNaturality

open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation

universe uH

/--
This must fail: a chain equivalence and matching recipe ID do not by
themselves identify the source and target geometric H2 coordinates.
-/
def unsafeCertificate
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH}
    [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TopologicalTableTwoMove source target)
    (recipeId : String)
    (recipeIdSound : recipeId = topologicalMoveRecipeId move)
    (chainEquivalence :
      HandleChainEquivalence source.handleChain target.handleChain)
    (chainCertificateHash : String)
    (chainHashShape :
      RawPresentation.sha256Shape chainCertificateHash = true) :
    SourceBoundChainMoveCertificate move where
  recipeId := recipeId
  recipe_id_sound := recipeIdSound
  chainEquivalence := chainEquivalence
  chainCertificateHash := chainCertificateHash
  chain_certificate_hash_shape := chainHashShape

end TwistedYetter.Mutations.MissingGeometricH2CoordinateNaturality
