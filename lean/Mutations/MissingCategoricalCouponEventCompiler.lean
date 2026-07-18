import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.MissingCategoricalCouponEventCompiler

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.Presentation

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/-- This must fail: coupon events may not silently disappear. -/
def unsafeCompiler
    (raw : RawPresentation)
    (boundary : List StrandState → Boundary C)
    (emptyBoundarySound : boundary [] = .unit)
    (framingTwistData : NaturalTwist C)
    (birth :
      (eventId componentId positiveStrand negativeStrand : String) →
      (insertAt : Nat) →
      {before after : List StrandState} →
      (step_sound :
        raw.applyEvent before
            (.birth
              eventId componentId positiveStrand negativeStrand insertAt) =
          Except.ok after) →
        CompiledCategoricalEvent C .birth
          (boundary before) (boundary after))
    (death :
      (eventId componentId firstStrand secondStrand : String) →
      {before after : List StrandState} →
      (step_sound :
        raw.applyEvent before
            (.death eventId componentId firstStrand secondStrand) =
          Except.ok after) →
        CompiledCategoricalEvent C .death
          (boundary before) (boundary after))
    (crossing :
      (eventId overStrand underStrand : String) →
      (sign : TwistedYetter.Kirby.Presentation.CrossingSign) →
      {before after : List StrandState} →
      (step_sound :
        raw.applyEvent before
            (.crossing eventId overStrand underStrand sign) =
          Except.ok after) →
        CompiledCategoricalEvent C (crossingPrimitiveKind sign)
          (boundary before) (boundary after))
    (framingTwist :
      (eventId strandId : String) →
      (sign : TwistedYetter.Kirby.Presentation.CrossingSign) →
      {before after : List StrandState} →
      (step_sound :
        raw.applyEvent before
            (.framingTwist eventId strandId sign) =
          Except.ok after) →
        CompiledFramingTwistEvent C framingTwistData sign
          (boundary before) (boundary after))
    (planarIsotopy :
      (eventId : String) →
      (activeOrder : List String) →
      {before after : List StrandState} →
      (step_sound :
        raw.applyEvent before
            (.planarIsotopy eventId activeOrder) =
          Except.ok after) →
        CompiledCategoricalEvent C .planarIdentity
          (boundary before) (boundary after))
    (compilerSnapshotHash : String)
    (compilerHashShape :
      RawPresentation.sha256Shape compilerSnapshotHash = true) :
    CategoricalEventCompiler C raw where
  framingTwistData := framingTwistData
  boundary := boundary
  empty_boundary_sound := emptyBoundarySound
  birth := birth
  death := death
  crossing := crossing
  framingTwist := framingTwist
  planarIsotopy := planarIsotopy
  compilerSchema := "mutation"
  compilerSnapshotHash := compilerSnapshotHash
  compiler_snapshot_hash_shape := compilerHashShape
  sourceRefs := []
  exactScope := "mutation"
  sourceScopeCaveat := "mutation"

end TwistedYetter.Mutations.MissingCategoricalCouponEventCompiler
