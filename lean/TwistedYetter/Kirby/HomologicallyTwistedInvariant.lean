import TwistedYetter.Kirby.KirbyCompleteness
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# A homologically twisted Kirby invariant under explicit inputs

This module assembles R7--R10.  It does not identify the resulting invariant
with a Crane--Yetter state sum.

The key boundary is `EvaluatedTableTwoStep`.  Its eight constructors mirror
the eight directed constructors of `TableTwoMove`.  A framed isotopy must
carry an R7 `GeneratedIsotopy`; the three slides must carry the corresponding
R8 graphical proof object; and the four cancellation directions must carry an
R9 local calculation.  There is no constructor from a bare equality of final
or normalized values.

`HomologicallyTwistedKirbyPrescription.movie_invariant` is then a genuine
induction over a topology movie.  `MarkedPairPresentationSystem` is a separate
topology/marking input saying which presentation coordinate represents a
geometric class and that the R10 movie transports that coordinate correctly.
Only after exposing that input do we define a value of the pair `(X, alpha)`.
-/

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationIsotopy

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
All category-level data used by the R11 Kirby route.

The two proof-relevant coherence fields prevent a dimension profile,
generalized-sliding package, and closed-diagram scalarization from being
silently assembled from unrelated category snapshots.  R12 will be
responsible for importing concrete snapshots into this abstract interface.
-/
structure AdmissibleKirbyCategory where
  categorySnapshotHash : String
  category_snapshot_hash_shape :
    RawPresentation.sha256Shape categorySnapshotHash = true
  dimensionProfile : GlobalDimensionProfile (K := K)
  slidingData :
    SlidingCategoryData (R := K) (D := C) (S := S) (I := I)
  closedScalar : (𝟙_ C ⟶ 𝟙_ C) → K
  scalarizationMatchesGroundField : Prop
  scalarization_witness : scalarizationMatchesGroundField
  singleSnapshotCoherent : Prop
  single_snapshot_witness : singleSnapshotCoherent
  coherenceCertificateHash : String
  coherence_certificate_hash_shape :
    RawPresentation.sha256Shape coherenceCertificateHash = true
  sourceRefs : List String
  sourceScopeCaveat : String

/--
A typed evaluator realization of one special Kirby presentation for every
marked class.

The raw numerator is not a free field: it must be the chosen scalarization of
the categorical evaluation of the recorded closed diagram.  Category,
presentation, and marked-homology certificate identities are pinned by
equalities rather than by arbitrary semantic propositions that could be
instantiated with `True`.
-/
structure DecoratedKirbyPresentation
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2) where
  diagram : H2 → Diagram C .unit .unit
  evaluationState : H2 → EvaluationState (K := K)
  counts_sound :
    (alpha : H2) → (evaluationState alpha).counts = topology.counts
  raw_numerator_sound :
    (alpha : H2) →
      (evaluationState alpha).rawNumerator =
        categoryData.closedScalar (Diagram.eval C (diagram alpha))
  compiledCategorySnapshotHash : String
  category_snapshot_hash_sound :
    compiledCategorySnapshotHash = categoryData.categorySnapshotHash
  compiledPresentationSnapshotHash : String
  presentation_snapshot_hash_sound :
    compiledPresentationSnapshotHash = topology.formal.pinnedSourceHash
  compiledH2ModelCertificateHash : String
  h2_model_certificate_hash_sound :
    compiledH2ModelCertificateHash = topology.h2ModelCertificateHash
  diagramCertificateHash : String
  diagram_certificate_hash_shape :
    RawPresentation.sha256Shape diagramCertificateHash = true
  decorationCertificateHash : String
  decoration_certificate_hash_shape :
    RawPresentation.sha256Shape decorationCertificateHash = true

namespace DecoratedKirbyPresentation

/-- The normalized R9 value attached to one presentation and marked class. -/
def normalizedValue
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (presentation :
      DecoratedKirbyPresentation categoryData topology)
    (alpha : H2) : K :=
  (presentation.evaluationState alpha).normalized
    categoryData.dimensionProfile

end DecoratedKirbyPresentation

/-- Extract the R8 metadata without weakening the closed slide whitelist. -/
def ordinarySlideMetadata
    {source target : Boundary C}
    {before after : Diagram C source target}
    (slide : OrdinaryHandleSlide before after) : SlideMetadata :=
  match slide with
  | .oneOverOne metadata _ _ _ _ _ => metadata
  | .twoOverOne metadata _ _ _ _ _ => metadata

/-- Extract the unique R8 two-over-two metadata. -/
def twoOverTwoSlideMetadata
    {source target : Boundary C}
    {before after : Diagram C source target}
    {data :
      SlidingCategoryData (R := K) (D := C) (S := S) (I := I)}
    (slide : TwoHandleOverTwoSlide (data := data) before after) :
    SlideMetadata :=
  match slide with
  | .twoOverTwo metadata _ _ _ _ _ => metadata

/-- Extract the R10 metadata from every exact Table 2 constructor. -/
def tableTwoMoveMetadata
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target) :
    TableTwoMoveMetadata source target :=
  match move with
  | .framedIsotopy metadata _ _ => metadata
  | .oneOverOne _ metadata _ _ => metadata
  | .twoOverOne _ metadata _ _ => metadata
  | .twoOverTwo _ metadata _ _ => metadata
  | .oneTwoBirth metadata _ _ => metadata
  | .oneTwoDeath metadata _ _ => metadata
  | .twoThreeBirth metadata _ _ => metadata
  | .twoThreeDeath metadata _ _ => metadata

/--
Hash-bound assertion that one R7/R8/R9 proof object realizes the exact R10
topology step.  This does not contain an evaluator equality.
-/
structure LocalEvaluationBinding
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target) where
  moveId : String
  move_id_sound : moveId = (tableTwoMoveMetadata move).moveId
  sourcePresentationHash : String
  source_hash_sound :
    sourcePresentationHash = source.formal.pinnedSourceHash
  targetPresentationHash : String
  target_hash_sound :
    targetPresentationHash = target.formal.pinnedSourceHash
  graphicalCertificateHash : String
  graphical_certificate_hash_shape :
    RawPresentation.sha256Shape graphicalCertificateHash = true

/--
The only admitted bridge from an R10 topology step to evaluator data.

Every constructor is indexed by the exact corresponding `TableTwoMove`.
There is no constructor accepting a normalized equality.
-/
inductive EvaluatedTableTwoStep
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (sourceEvaluation :
      DecoratedKirbyPresentation categoryData source)
    (targetEvaluation :
      DecoratedKirbyPresentation categoryData target) :
    (move : TableTwoMove source target) → H2 →
      Type (max (max (max uK uC) vC) (max (max uS uI) uH))
  | framedIsotopy
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.framedIsotopy metadata counts_sound transport))
      (isotopy :
        GeneratedIsotopy
          (sourceEvaluation.diagram alpha)
          (targetEvaluation.diagram (transport.targetClass alpha))) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.framedIsotopy metadata counts_sound transport) alpha
  | oneOverOne
      (orientation : BandOrientation)
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.oneOverOne
            orientation metadata counts_sound transport))
      (slide :
        OrdinaryHandleSlide
          (sourceEvaluation.diagram alpha)
          (targetEvaluation.diagram (transport.targetClass alpha)))
      (graphical_kind_sound :
        (ordinarySlideMetadata slide).kind = .oneOverOne)
      (graphical_orientation_sound :
        (ordinarySlideMetadata slide).orientation = orientation)
      (graphical_move_id_sound :
        (ordinarySlideMetadata slide).moveId = metadata.moveId)
      (graphical_source_hash_sound :
        (ordinarySlideMetadata slide).sourcePresentationHash =
          metadata.sourcePresentationHash)
      (graphical_target_hash_sound :
        (ordinarySlideMetadata slide).targetPresentationHash =
          metadata.targetPresentationHash) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.oneOverOne
          orientation metadata counts_sound transport) alpha
  | twoOverOne
      (orientation : BandOrientation)
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.twoOverOne
            orientation metadata counts_sound transport))
      (slide :
        OrdinaryHandleSlide
          (sourceEvaluation.diagram alpha)
          (targetEvaluation.diagram (transport.targetClass alpha)))
      (graphical_kind_sound :
        (ordinarySlideMetadata slide).kind = .twoOverOne)
      (graphical_orientation_sound :
        (ordinarySlideMetadata slide).orientation = orientation)
      (graphical_move_id_sound :
        (ordinarySlideMetadata slide).moveId = metadata.moveId)
      (graphical_source_hash_sound :
        (ordinarySlideMetadata slide).sourcePresentationHash =
          metadata.sourcePresentationHash)
      (graphical_target_hash_sound :
        (ordinarySlideMetadata slide).targetPresentationHash =
          metadata.targetPresentationHash) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.twoOverOne
          orientation metadata counts_sound transport) alpha
  | twoOverTwo
      (orientation : BandOrientation)
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.twoOverTwo
            orientation metadata counts_sound transport))
      (slide :
        TwoHandleOverTwoSlide
          (data := categoryData.slidingData)
          (sourceEvaluation.diagram alpha)
          (targetEvaluation.diagram (transport.targetClass alpha)))
      (graphical_orientation_sound :
        (twoOverTwoSlideMetadata slide).orientation = orientation)
      (graphical_move_id_sound :
        (twoOverTwoSlideMetadata slide).moveId = metadata.moveId)
      (graphical_source_hash_sound :
        (twoOverTwoSlideMetadata slide).sourcePresentationHash =
          metadata.sourcePresentationHash)
      (graphical_target_hash_sound :
        (twoOverTwoSlideMetadata slide).targetPresentationHash =
          metadata.targetPresentationHash) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.twoOverTwo
          orientation metadata counts_sound transport) alpha
  | oneTwoBirth
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : target.counts = source.counts.addOneTwo)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.oneTwoBirth metadata counts_sound transport))
      (calculation :
        OneTwoLocalCalculation categoryData.dimensionProfile)
      (before_is_target :
        calculation.before =
          targetEvaluation.evaluationState (transport.targetClass alpha))
      (after_is_source :
        calculation.after = sourceEvaluation.evaluationState alpha) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.oneTwoBirth metadata counts_sound transport) alpha
  | oneTwoDeath
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts.addOneTwo)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.oneTwoDeath metadata counts_sound transport))
      (calculation :
        OneTwoLocalCalculation categoryData.dimensionProfile)
      (before_is_source :
        calculation.before = sourceEvaluation.evaluationState alpha)
      (after_is_target :
        calculation.after =
          targetEvaluation.evaluationState (transport.targetClass alpha)) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.oneTwoDeath metadata counts_sound transport) alpha
  | twoThreeBirth
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : target.counts = source.counts.addTwoThree)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.twoThreeBirth metadata counts_sound transport))
      (calculation :
        TwoThreeLocalCalculation categoryData.dimensionProfile)
      (before_is_target :
        calculation.before =
          targetEvaluation.evaluationState (transport.targetClass alpha))
      (after_is_source :
        calculation.after = sourceEvaluation.evaluationState alpha) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.twoThreeBirth metadata counts_sound transport) alpha
  | twoThreeDeath
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts.addTwoThree)
      (transport : MarkedH2Transport source target)
      (alpha : H2)
      (binding :
        LocalEvaluationBinding
          (TableTwoMove.twoThreeDeath metadata counts_sound transport))
      (calculation :
        TwoThreeLocalCalculation categoryData.dimensionProfile)
      (before_is_source :
        calculation.before = sourceEvaluation.evaluationState alpha)
      (after_is_target :
        calculation.after =
          targetEvaluation.evaluationState (transport.targetClass alpha)) :
      EvaluatedTableTwoStep categoryData sourceEvaluation targetEvaluation
        (TableTwoMove.twoThreeDeath metadata counts_sound transport) alpha

namespace EvaluatedTableTwoStep

/-- Equal raw numerators and handle counts give equal normalized values. -/
theorem normalized_eq_of_counts_and_raw
    {profile : GlobalDimensionProfile (K := K)}
    {left right : EvaluationState (K := K)}
    (counts_eq : left.counts = right.counts)
    (raw_eq : left.rawNumerator = right.rawNumerator) :
    left.normalized profile = right.normalized profile := by
  simp only [EvaluationState.normalized]
  rw [counts_eq, raw_eq]

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Turn an equality of closed categorical evaluations into normalized equality. -/
lemma normalized_eq_of_diagram_eval
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (sourceEvaluation :
      DecoratedKirbyPresentation categoryData source)
    (targetEvaluation :
      DecoratedKirbyPresentation categoryData target)
    (alpha beta : H2)
    (counts_eq : source.counts = target.counts)
    (diagram_eval_eq :
      Diagram.eval C (sourceEvaluation.diagram alpha) =
        Diagram.eval C (targetEvaluation.diagram beta)) :
    sourceEvaluation.normalizedValue alpha =
      targetEvaluation.normalizedValue beta := by
  apply normalized_eq_of_counts_and_raw
  · calc
      (sourceEvaluation.evaluationState alpha).counts = source.counts :=
        sourceEvaluation.counts_sound alpha
      _ = target.counts := counts_eq
      _ = (targetEvaluation.evaluationState beta).counts :=
        (targetEvaluation.counts_sound beta).symm
  · rw [sourceEvaluation.raw_numerator_sound,
      targetEvaluation.raw_numerator_sound, diagram_eval_eq]

/-- Every constructor in the closed R11 bridge preserves normalized value. -/
theorem normalized_sound
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    {sourceEvaluation :
      DecoratedKirbyPresentation categoryData source}
    {targetEvaluation :
      DecoratedKirbyPresentation categoryData target}
    {move : TableTwoMove source target}
    {alpha : H2}
    (step :
      EvaluatedTableTwoStep
        categoryData sourceEvaluation targetEvaluation move alpha) :
    sourceEvaluation.normalizedValue alpha =
      targetEvaluation.normalizedValue
        (move.homologyTransport.targetClass alpha) := by
  cases step with
  | framedIsotopy metadata counts transport alpha binding isotopy =>
      exact normalized_eq_of_diagram_eval
        sourceEvaluation targetEvaluation alpha
          (transport.targetClass alpha) counts isotopy.eval_eq
  | oneOverOne orientation metadata counts transport alpha binding slide
      graphical_kind_sound graphical_orientation_sound
      graphical_move_id_sound graphical_source_hash_sound
      graphical_target_hash_sound =>
      exact normalized_eq_of_diagram_eval
        sourceEvaluation targetEvaluation alpha
          (transport.targetClass alpha) counts slide.sound
  | twoOverOne orientation metadata counts transport alpha binding slide
      graphical_kind_sound graphical_orientation_sound
      graphical_move_id_sound graphical_source_hash_sound
      graphical_target_hash_sound =>
      exact normalized_eq_of_diagram_eval
        sourceEvaluation targetEvaluation alpha
          (transport.targetClass alpha) counts slide.sound
  | twoOverTwo orientation metadata counts transport alpha binding slide
      graphical_orientation_sound graphical_move_id_sound
      graphical_source_hash_sound graphical_target_hash_sound =>
      exact normalized_eq_of_diagram_eval
        sourceEvaluation targetEvaluation alpha
          (transport.targetClass alpha) counts slide.sound
  | oneTwoBirth metadata counts transport alpha binding calculation
      before_is_target after_is_source =>
      simpa [after_is_source, before_is_target] using
        calculation.normalized_sound.symm
  | oneTwoDeath metadata counts transport alpha binding calculation
      before_is_source after_is_target =>
      simpa [before_is_source, after_is_target] using
        calculation.normalized_sound
  | twoThreeBirth metadata counts transport alpha binding calculation
      before_is_target after_is_source =>
      simpa [after_is_source, before_is_target] using
        calculation.normalized_sound.symm
  | twoThreeDeath metadata counts transport alpha binding calculation
      before_is_source after_is_target =>
      simpa [before_is_source, after_is_target] using
        calculation.normalized_sound

end EvaluatedTableTwoStep

/--
A complete local evaluator prescription for one fixed manifold and H2 model.

The `localStep` field returns a closed R7/R8/R9 proof object.  It cannot return
an equality directly.
-/
structure HomologicallyTwistedKirbyPrescription
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  evaluation :
    (presentation : SpecialKirbyPresentation manifold H2) →
      DecoratedKirbyPresentation categoryData presentation
  localStep :
    {source target : SpecialKirbyPresentation manifold H2} →
    (move : TableTwoMove source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target) move alpha
  prescriptionCertificateHash : String
  prescription_certificate_hash_shape :
    RawPresentation.sha256Shape prescriptionCertificateHash = true
  sourceRefs : List String
  exactFormulaScope : String
  sourceScopeCaveat : String

namespace HomologicallyTwistedKirbyPrescription

/-- The normalized value on one marked presentation. -/
def presentationValue
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    (presentation : SpecialKirbyPresentation manifold H2)
    (alpha : H2) : K :=
  (prescription.evaluation presentation).normalizedValue alpha

/-- One admitted topology move preserves the normalized marked value. -/
theorem move_invariant
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target)
    (alpha : H2) :
    prescription.presentationValue source alpha =
      prescription.presentationValue target
        (move.homologyTransport.targetClass alpha) :=
  (prescription.localStep move alpha).normalized_sound

/-- Target-class transport along a composite movie is literal composition. -/
theorem targetClass_trans
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source middle target : SpecialKirbyPresentation manifold H2}
    (first : TableTwoMovie source middle)
    (second : TableTwoMovie middle target)
    (alpha : H2) :
    (TableTwoMovie.trans first second).targetClass alpha =
      second.targetClass (first.targetClass alpha) :=
  rfl

/-- Induction over an arbitrary R10 movie. -/
theorem movie_invariant
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target)
    (alpha : H2) :
    prescription.presentationValue source alpha =
      prescription.presentationValue target (movie.targetClass alpha) := by
  induction movie generalizing alpha with
  | refl presentation =>
      rfl
  | step move =>
      exact prescription.move_invariant move alpha
  | trans first second firstIH secondIH =>
      rw [targetClass_trans]
      exact (firstIH alpha).trans
        (secondIH (first.targetClass alpha))

end HomologicallyTwistedKirbyPrescription

/--
The marked topology input needed to interpret presentation coordinates as one
geometric class.

`marked_transport_sound` is deliberately visible.  R10 supplies the movie and
its chain-induced H2 equivalence, but a theorem that two independently
certified coordinates represent the same geometric class still has to say
that this exact movie carries one coordinate to the other.
-/
structure MarkedPairPresentationSystem
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  completeness : TableTwoLinkCompleteness manifold H2
  represents :
    (presentation : SpecialKirbyPresentation manifold H2) →
      H2 → H2 → Prop
  chosenPresentation :
    H2 → SpecialKirbyPresentation manifold H2
  chosenCoordinate : H2 → H2
  chosen_represents :
    (alpha : H2) →
      represents (chosenPresentation alpha) (chosenCoordinate alpha) alpha
  marked_transport_sound :
    {source target : SpecialKirbyPresentation manifold H2} →
    {sourceCoordinate targetCoordinate geometricClass : H2} →
    represents source sourceCoordinate geometricClass →
    represents target targetCoordinate geometricClass →
      (completeness.tableTwoConnected source target).targetClass
          sourceCoordinate =
        targetCoordinate
  markingCertificateHash : String
  marking_certificate_hash_shape :
    RawPresentation.sha256Shape markingCertificateHash = true
  sourceRefs : List String
  exactMarkedScope : String
  sourceScopeCaveat : String

namespace MarkedPairPresentationSystem

/--
The homologically twisted Kirby invariant of the fixed manifold and geometric
class, defined using the system's chosen marked presentation.
-/
noncomputable def invariant
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    (system : MarkedPairPresentationSystem manifold H2)
    (alpha : H2) : K :=
  prescription.presentationValue
    (system.chosenPresentation alpha) (system.chosenCoordinate alpha)

/-- Every certified presentation of `(X, alpha)` computes the chosen value. -/
theorem presentation_independent
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
      system.invariant prescription alpha := by
  let movie :=
    system.completeness.tableTwoConnected
      (system.chosenPresentation alpha) presentation
  have movieEquality :=
    prescription.movie_invariant movie (system.chosenCoordinate alpha)
  have coordinateEquality :
      movie.targetClass (system.chosenCoordinate alpha) = coordinate :=
    system.marked_transport_sound (system.chosen_represents alpha) represents
  rw [coordinateEquality] at movieEquality
  exact movieEquality.symm

/-- Any two certified realizations of the same pair have the same value. -/
theorem same_pair_value
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    (system : MarkedPairPresentationSystem manifold H2)
    {left right : SpecialKirbyPresentation manifold H2}
    {leftCoordinate rightCoordinate alpha : H2}
    (leftRepresents :
      system.represents left leftCoordinate alpha)
    (rightRepresents :
      system.represents right rightCoordinate alpha) :
    prescription.presentationValue left leftCoordinate =
      prescription.presentationValue right rightCoordinate := by
  rw [system.presentation_independent prescription leftRepresents,
    system.presentation_independent prescription rightRepresents]

/--
Terminal R11 theorem: the normalized Kirby prescription is an invariant of
the marked pair, relative exactly to the category, local-move, topology, and
marking inputs visible above.
-/
theorem homologically_twisted_kirby_invariant_established
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
  system.presentation_independent prescription represents

end MarkedPairPresentationSystem

end TwistedYetter.Kirby.HomologicallyTwistedInvariant
