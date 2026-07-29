import TwistedYetter.Kirby.Final.Semantics.Presentation

/-!
# Semantic framed-isotopy grammar

A finite, explicit grammar of primitive framed-isotopy rewrites.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

open TwistedYetter.Kirby.Presentation

universe uH

/-! ## The eight exact moves -/

/-- Strand IDs mentioned by one primitive sliced event. -/
def eventStrands : SliceEvent → List String
  | .birth _ _ positive negative _ => [positive, negative]
  | .death _ _ first second => [first, second]
  | .crossing _ over under _ => [over, under]
  | .coupon _ _ _ inputs outputs _ =>
      inputs ++ outputs.map StrandState.strandId
  | .framingTwist _ strand _ => [strand]
  | .planarIsotopy _ order => order

/--
Independent primitive framed-isotopy rewrites.

Every constructor gives literal before and after event lists.  The grammar is
deliberately finite and closed: a caller cannot submit an arbitrary pair of
windows and call it an isotopy.
-/
inductive FramedIsotopyStep :
    List SliceEvent → List SliceEvent → Type
  | planar
      (beforeEventId afterEventId : String)
      (activeOrder : List String) :
      FramedIsotopyStep
        [.planarIsotopy beforeEventId activeOrder]
        [.planarIsotopy afterEventId activeOrder]
  | commute
      (first second : SliceEvent)
      (disjoint : (eventStrands first).Disjoint (eventStrands second)) :
      FramedIsotopyStep [first, second] [second, first]
  | reidemeisterII
      (positiveId negativeId identityId over under : String) :
      FramedIsotopyStep
        [
          .crossing positiveId over under .positive,
          .crossing negativeId under over .negative
        ]
        [.planarIsotopy identityId [over, under]]
  | reidemeisterIII
      (firstId secondId thirdId
        firstId' secondId' thirdId' : String)
      (left middle right : String)
      (sign : CrossingSign) :
      FramedIsotopyStep
        [
          .crossing firstId left middle sign,
          .crossing secondId left right sign,
          .crossing thirdId middle right sign
        ]
        [
          .crossing firstId' middle right sign,
          .crossing secondId' left right sign,
          .crossing thirdId' left middle sign
        ]
  | snake
      (birthId deathId identityId component positive negative : String)
      (insertAt : Nat) :
      FramedIsotopyStep
        [
          .birth birthId component positive negative insertAt,
          .death deathId component positive negative
        ]
        [.planarIsotopy identityId []]

/-- Finite closure of the independent primitive framed-isotopy grammar. -/
inductive FramedIsotopyScript :
    List SliceEvent → List SliceEvent → Type
  | refl (events : List SliceEvent) :
      FramedIsotopyScript events events
  | inside
      {before after : List SliceEvent}
      (commonPrefix commonSuffix : List SliceEvent)
      (step : FramedIsotopyStep before after) :
      FramedIsotopyScript
        (commonPrefix ++ before ++ commonSuffix)
        (commonPrefix ++ after ++ commonSuffix)
  | symm
      {before after : List SliceEvent}
      (script : FramedIsotopyScript before after) :
      FramedIsotopyScript after before
  | trans
      {before middle after : List SliceEvent}
      (first : FramedIsotopyScript before middle)
      (second : FramedIsotopyScript middle after) :
      FramedIsotopyScript before after

/--
Independent generated framed isotopy witness.

Its exact endpoints and every primitive rewrite are data.  Geometric
completeness of this finite grammar is a separate topology theorem; it is not
smuggled into the move constructor.
-/
structure FramedIsotopy
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  lineage : SameComponentLineage source target
  count_exact : target.counts = source.counts
  component_spec_exact :
    (targetIndex : ComponentIndex target) →
      componentAt target targetIndex =
        componentAt source (lineage.targetToSource targetIndex)
  script :
    FramedIsotopyScript replacement.sourceEventWindow
      replacement.targetEventWindow
end TwistedYetter.Kirby.Final.SemanticEightMoves
