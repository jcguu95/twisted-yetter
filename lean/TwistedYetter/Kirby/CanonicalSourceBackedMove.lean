import TwistedYetter.Kirby.LiteratureBackedFourManifoldInputs

/-!
# Canonical chain enrichment of topology-only Kirby moves

The special-Kirby topology relation deliberately contains no category and no
homology map.  This module enriches one such move by the unique chain
homotopy equivalence supplied at the separately audited handle-chain
naturality boundary.

No caller can provide a replacement `MarkedH2Transport`.
-/

namespace TwistedYetter.Kirby.CanonicalSourceBackedMove

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uH

/--
Enrich a category-neutral topology move by the source-backed handle-chain
transport.
-/
noncomputable def enrichedMove
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target) :
    TableTwoMove source target :=
  SourceBackedKirbyCompleteness.enrichMove
    (sourceBackedGeometricH2Compiler H2).localCompiler
    move

end TwistedYetter.Kirby.CanonicalSourceBackedMove
