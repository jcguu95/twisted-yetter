import TwistedYetter.Kirby.Presentation

/-!
# Kernel regressions for the shared presentation schema

These small closed calculations pin the semantics that previously differed
between the Python artifact validator and Lean. They use reduction only:
there is no `sorry`, native decision oracle, or project axiom.
-/

namespace TwistedYetter.Kirby.PresentationSchemaRegression

open Lean
open TwistedYetter.Kirby.Presentation

theorem formal_identity_is_content_hash
    (formal : FormalPresentation) :
    formal.pinnedSourceHash = formal.raw.contentHash := by
  rfl

theorem provenance_projection_is_source_snapshot_hash
    (formal : FormalPresentation) :
    formal.provenanceSourceHash = formal.raw.sourceSnapshotHash := by
  rfl

def aPositive : StrandState :=
  { strandId := "A+", componentId := "K0", orientation := .positive }

def aNegative : StrandState :=
  { strandId := "A-", componentId := "K0", orientation := .negative }

def bPositive : StrandState :=
  { strandId := "B+", componentId := "K0", orientation := .positive }

def bNegative : StrandState :=
  { strandId := "B-", componentId := "K0", orientation := .negative }

theorem adjacent_crossing_swaps_boundary_order :
    roundTripFixture.applyEvent [aPositive, aNegative]
      (.crossing "cross" "A+" "A-" .positive) =
        Except.ok [aNegative, aPositive] := by
  rfl

theorem nonadjacent_crossing_rejected :
    roundTripFixture.applyEvent
      [aPositive, aNegative, bPositive, bNegative]
      (.crossing "cross" "A+" "B+" .positive) =
        Except.error
          "crossing strands are not adjacent in the Morse slice" := by
  rfl

theorem same_orientation_death_rejected :
    roundTripFixture.applyEvent [aPositive, bPositive]
      (.death "death" "K0" "A+" "B+") =
        Except.error "death requires opposite strand orientations" := by
  rfl

theorem planar_reordering_rejected :
    roundTripFixture.applyEvent [aPositive, aNegative]
      (.planarIsotopy "isotopy" ["A-", "A+"]) =
        Except.error "planar isotopy has the wrong active boundary" := by
  rfl

def unknownFieldJson : Json :=
  (RawPresentation.toJson roundTripFixture).setObjVal!
    "alias" "current"

theorem unknown_json_field_rejected :
    RawPresentation.fromJson unknownFieldJson =
      Except.error "presentation keys mismatch" := by
  rfl

end TwistedYetter.Kirby.PresentationSchemaRegression
