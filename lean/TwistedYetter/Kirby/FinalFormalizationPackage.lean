import TwistedYetter.Kirby.ComputationArtifactImporter

/-!
# Terminal package for the Lean Kirby formalization route

R13 adds no mathematical axiom. It forwards the conditional R11 invariant and
the exact/structural separation proved in R12, while making the remaining
claim boundaries proof-relevant.

`formalizationRouteTerminal = true` means that R0--R12 have been assembled
into one audited route relative to their listed inputs. It does not mean that
the invariant has been identified with a Crane--Yetter state sum, nor that the
Figure 21 structural batch has become an exact invariant computation.
-/

namespace TwistedYetter.Kirby.FinalFormalizationPackage

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.ComputationArtifactImporter
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness

/-- The four distinct kinds of evidence assembled by R13. -/
inductive EvidenceLayer where
  | categoryAndGraphicalAlgebra
  | presentationAndLocalKirbyMoves
  | topologyAndMarkedInvariant
  | computationImport
  deriving Repr, DecidableEq

/-- The complete R13 evidence-layer denominator. -/
def requiredEvidenceLayers : List EvidenceLayer :=
  [
    .categoryAndGraphicalAlgebra,
    .presentationAndLocalKirbyMoves,
    .topologyAndMarkedInvariant,
    .computationImport
  ]

theorem evidence_layer_count :
    requiredEvidenceLayers.length = 4 := by
  rfl

/-- The unchanged R12 blockers for exact Figure 21 admission. -/
def requiredFigure21Blockers : List BlockerReason :=
  [
    .dirtyProvenance,
    .draftDiagram,
    .roundedOutput,
    .missingR11Binding,
    .unsealedEvaluatorClosure,
    .missingMarkedH2Comparison
  ]

/--
The final claim boundary. Every negative field is an equality to `false`, so a
consumer cannot replace a non-claim with a positive status string.
-/
structure TerminalBoundary where
  evidenceLayers : List EvidenceLayer
  figure21Blockers : List BlockerReason
  formalizationRouteTerminal : Bool
  craneYetterIdentificationEstablished : Bool
  figure21ExactValueAdmitted : Bool
  figure21MarkedComparisonAdmitted : Bool
  allImportedCategoryIdentitiesReproved : Bool
  sourceByteCompleteArchive : Bool
  ctlClaimAdmitted : Bool
  evidence_layers_exact :
    evidenceLayers = requiredEvidenceLayers
  figure21_blockers_exact :
    figure21Blockers = requiredFigure21Blockers
  route_terminal :
    formalizationRouteTerminal = true
  crane_yetter_not_identified :
    craneYetterIdentificationEstablished = false
  figure21_exact_not_admitted :
    figure21ExactValueAdmitted = false
  figure21_comparison_not_admitted :
    figure21MarkedComparisonAdmitted = false
  category_inputs_not_all_reproved :
    allImportedCategoryIdentitiesReproved = false
  source_archive_not_byte_complete :
    sourceByteCompleteArchive = false
  ctl_not_admitted :
    ctlClaimAdmitted = false

/-- The unique R13 terminal boundary used by the generated certificate. -/
def currentBoundary : TerminalBoundary where
  evidenceLayers := requiredEvidenceLayers
  figure21Blockers := requiredFigure21Blockers
  formalizationRouteTerminal := true
  craneYetterIdentificationEstablished := false
  figure21ExactValueAdmitted := false
  figure21MarkedComparisonAdmitted := false
  allImportedCategoryIdentitiesReproved := false
  sourceByteCompleteArchive := false
  ctlClaimAdmitted := false
  evidence_layers_exact := rfl
  figure21_blockers_exact := rfl
  route_terminal := rfl
  crane_yetter_not_identified := rfl
  figure21_exact_not_admitted := rfl
  figure21_comparison_not_admitted := rfl
  category_inputs_not_all_reproved := rfl
  source_archive_not_byte_complete := rfl
  ctl_not_admitted := rfl

theorem formalization_route_is_terminal :
    currentBoundary.formalizationRouteTerminal = true :=
  currentBoundary.route_terminal

theorem crane_yetter_identification_not_established :
    currentBoundary.craneYetterIdentificationEstablished = false :=
  currentBoundary.crane_yetter_not_identified

theorem figure21_exact_value_not_admitted :
    currentBoundary.figure21ExactValueAdmitted = false :=
  currentBoundary.figure21_exact_not_admitted

theorem figure21_marked_comparison_not_admitted :
    currentBoundary.figure21MarkedComparisonAdmitted = false :=
  currentBoundary.figure21_comparison_not_admitted

theorem all_imported_category_identities_not_reproved :
    currentBoundary.allImportedCategoryIdentitiesReproved = false :=
  currentBoundary.category_inputs_not_all_reproved

theorem source_archive_not_byte_complete :
    currentBoundary.sourceByteCompleteArchive = false :=
  currentBoundary.source_archive_not_byte_complete

theorem ctl_claim_not_admitted :
    currentBoundary.ctlClaimAdmitted = false :=
  currentBoundary.ctl_not_admitted

theorem figure21_blocker_count :
    currentBoundary.figure21Blockers.length = 6 := by
  rw [currentBoundary.figure21_blockers_exact]
  rfl

theorem toy_exact_control_remains_admitted :
    toyExactControl.outputValue =
      toyExactControl.target.invariantValue :=
  toy_exact_control_admitted

theorem figure21_structural_row_count :
    figure21PointedBatch.rows.length = 15 :=
  figure21_pointed_row_count

theorem figure21_structural_not_exact :
    figure21PointedBatch.disposition ≠ .admittedExactValue :=
  figure21_not_promoted_to_invariant_values

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
The exact terminal R11 theorem, forwarded without hiding any of its category,
diagram, local-move, topology, or marking inputs.
-/
theorem r11_conditional_invariant
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    (system : MarkedPairPresentationSystem manifold H2)
    {presentation : SpecialKirbyPresentation manifold H2}
    {coordinate alpha : H2}
    (represents : system.represents presentation coordinate alpha) :
    prescription.presentationValue presentation coordinate =
      system.invariant prescription alpha :=
  MarkedPairPresentationSystem.homologically_twisted_kirby_invariant_established
    prescription system represents

end TwistedYetter.Kirby.FinalFormalizationPackage
