import TwistedYetter.Kirby.Final.Semantics.Presentation

/-!
# Semantic clean band-slide geometry

Category-neutral attach, finite band transport, and detach data.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

open TwistedYetter.Kirby.Presentation

universe uH

/-! ## Independent clean band geometry -/

/-- Orientation of an oriented band sum. -/
inductive BandOrientation
  | positive
  | negative
  deriving Repr, BEq, DecidableEq

/--
The combinatorial candidate for one clean end of a band movie.

The moving and stationary strands are literally adjacent in the selected
slice.  The complete left and right strand lists remain visible, so a third
strand cannot be hidden by presenting only the two desired strands.  The
actual clean-collar topology is certified by `IsCleanOrientedBandSum`; this
record alone does not pretend that one horizontal slice proves it.
-/
structure AdjacentBandEndpoint
    (movingComponentId stationaryComponentId : String) where
  slice : DeclaredSlice
  left : List StrandState
  moving : StrandState
  stationary : StrandState
  right : List StrandState
  order_exact :
    slice.activeStrands = left ++ [moving, stationary] ++ right
  moving_component_exact :
    moving.componentId = movingComponentId
  stationary_component_exact :
    stationary.componentId = stationaryComponentId
  strands_distinct : moving.strandId ≠ stationary.strandId

/--
The finitely many kinds of topological features met by the core of a band.

These are geometric events of the *band*, not movements of a character
coupon.  Character coupons belong to the later evaluator proof and cannot be
used as a substitute for the Kirby move itself.
-/
inductive BandPassageEvent
  | crossing (eventId overStrand underStrand : String) (sign : CrossingSign)
  | cup (eventId component positive negative : String)
  | cap (eventId component first second : String)
  | twist (eventId strand : String) (sign : CrossingSign)
  | planar (eventId : String) (activeOrder : List String)
  deriving Repr, BEq, DecidableEq

/--
Trusted classical-topology relation: `target` presents the oriented framed
band sum of `source` specified by the clean endpoints and finite band path.

This is a relation rather than a function because a geometric band surgery
has many serialized planar representatives.  It is intentionally the one
visible semantic boundary in the independent slide language.  It says
nothing about categories, characters, evaluations, or scalar equalities.
-/
axiom IsCleanOrientedBandSum
    (source : FormalPresentation)
    (movingComponentId stationaryComponentId : String)
    (orientation : BandOrientation)
    (sourceAttach sourceDetach :
      AdjacentBandEndpoint movingComponentId stationaryComponentId)
    (targetAttach targetDetach :
      AdjacentBandEndpoint movingComponentId stationaryComponentId)
    (path : List BandPassageEvent)
    (target : FormalPresentation) :
    Prop

/--
An independent clean attach--finite band transport--detach surgery.

Both endpoint slices must occur in the admitted source/target ledgers.  The
target presentation must satisfy `IsCleanOrientedBandSum` for these exact
source and target endpoints.  The common-exterior replacement separately
verifies that nothing outside the declared window changed.
-/
structure CleanBandSlide
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂)
    (replacement : LocalReplacement source target)
    (orientation : BandOrientation)
    (movingComponentId stationaryComponentId : String) where
  sourceAttach :
    AdjacentBandEndpoint movingComponentId stationaryComponentId
  sourceDetach :
    AdjacentBandEndpoint movingComponentId stationaryComponentId
  targetAttach :
    AdjacentBandEndpoint movingComponentId stationaryComponentId
  targetDetach :
    AdjacentBandEndpoint movingComponentId stationaryComponentId
  source_attach_declared :
    sourceAttach.slice ∈ source.formal.raw.declaredSlices
  source_detach_declared :
    sourceDetach.slice ∈ source.formal.raw.declaredSlices
  target_attach_declared :
    targetAttach.slice ∈ target.formal.raw.declaredSlices
  target_detach_declared :
    targetDetach.slice ∈ target.formal.raw.declaredSlices
  source_attach_before_detach :
    sourceAttach.slice.index < sourceDetach.slice.index
  target_attach_before_detach :
    targetAttach.slice.index < targetDetach.slice.index
  source_attach_is_window_start :
    sourceAttach.slice.index = replacement.commonEventPrefix.length
  target_attach_is_window_start :
    targetAttach.slice.index = replacement.commonEventPrefix.length
  source_detach_is_window_end :
    sourceDetach.slice.index =
      (replacement.commonEventPrefix ++
        replacement.sourceEventWindow).length
  target_detach_is_window_end :
    targetDetach.slice.index =
      (replacement.commonEventPrefix ++
        replacement.targetEventWindow).length
  path : List BandPassageEvent
  target_is_band_sum :
    IsCleanOrientedBandSum source.formal movingComponentId
      stationaryComponentId orientation sourceAttach sourceDetach
      targetAttach targetDetach path target.formal


end TwistedYetter.Kirby.Final.SemanticEightMoves

