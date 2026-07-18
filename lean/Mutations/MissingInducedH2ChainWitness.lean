import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingInducedH2ChainWitness

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.Presentation

universe u

/--
This must fail: a handwritten equivalence is no longer a field at all.
The only admitted input is a chain homotopy equivalence, from which the map on
second homology is derived.
-/
def unsafeTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (chainEquivalence :
      HandleChainEquivalence source.handleChain target.handleChain)
    (equiv : H2 ≃ H2) :
    MarkedH2Transport source target where
  chainEquivalence := chainEquivalence
  homologyEquiv := equiv

end TwistedYetter.Mutations.MissingInducedH2ChainWitness
