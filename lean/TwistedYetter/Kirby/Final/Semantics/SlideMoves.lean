import TwistedYetter.Kirby.Final.Semantics.BandSlide

/-!
# The three semantic handle-slide moves

Exact H₂ transport and the 1/1, 2/1, and 2/2 clean band moves.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

open TwistedYetter.Kirby.Final.SemanticHandleChain

universe uH

/-! ## Chain-level marking semantics -/

/--
The chain-level transport of one move.

The map on displayed `H₂` is not independently supplied.  It is computed by
passing from displayed `H₂` to source handle homology, applying the induced
map of the chain homotopy equivalence, and returning through the target
identification.  A move of two presentations of the same marked manifold
must make this composite the identity.
-/
structure MarkingTransport
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  chainEquivalence :
    HandleChainEquivalence source.handleChain target.handleChain
  displayed_square :
    source.handleH₂Equiv.symm.trans
        (chainEquivalence.secondHomologyAddEquiv.trans
          target.handleH₂Equiv) =
      AddEquiv.refl H₂


structure OneOverOne
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  lineage : SameComponentLineage source target
  count_exact : target.counts = source.counts
  orientation : BandOrientation
  movingSource : DottedOneHandle source
  stationarySource : DottedOneHandle source
  distinct :
    movingSource.index ≠ stationarySource.index
  movingComponentId : String
  stationaryComponentId : String
  moving_id_exact :
    (componentAt source movingSource.index).componentId = movingComponentId
  stationary_id_exact :
    (componentAt source stationarySource.index).componentId =
      stationaryComponentId
  band :
    CleanBandSlide source target replacement orientation
      movingComponentId stationaryComponentId

/-- A clean ordinary two-handle sliding through a dotted one-handle. -/
structure TwoOverOne
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  lineage : SameComponentLineage source target
  count_exact : target.counts = source.counts
  orientation : BandOrientation
  movingSource : TwoHandle source
  stationarySource : DottedOneHandle source
  distinct :
    movingSource.index ≠ stationarySource.index
  movingComponentId : String
  stationaryComponentId : String
  moving_id_exact :
    (componentAt source movingSource.index).componentId = movingComponentId
  stationary_id_exact :
    (componentAt source stationarySource.index).componentId =
      stationaryComponentId
  band :
    CleanBandSlide source target replacement orientation
      movingComponentId stationaryComponentId

/-- A clean ordinary two-handle band-summed with another two-handle. -/
structure TwoOverTwo
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  lineage : SameComponentLineage source target
  count_exact : target.counts = source.counts
  orientation : BandOrientation
  movingSource : TwoHandle source
  stationarySource : TwoHandle source
  distinct :
    movingSource.index ≠ stationarySource.index
  movingComponentId : String
  stationaryComponentId : String
  moving_id_exact :
    (componentAt source movingSource.index).componentId = movingComponentId
  stationary_id_exact :
    (componentAt source stationarySource.index).componentId =
      stationaryComponentId
  band :
    CleanBandSlide source target replacement orientation
      movingComponentId stationaryComponentId


end TwistedYetter.Kirby.Final.SemanticEightMoves

