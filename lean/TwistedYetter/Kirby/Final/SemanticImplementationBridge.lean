import TwistedYetter.Kirby.Final.SemanticSpecification
import TwistedYetter.Kirby.Final.TwistedYetter
import TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo

/-!
# Implementation bridge for the short semantic specification

This file is intentionally the pressure point between the short human
specification and the existing implementation.  It must not use casts,
arbitrary equalities, or a global auxiliary `H₂`.
-/

namespace TwistedYetter.Kirby.Final.SemanticImplementationBridge

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Kirby.Final
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwareRepresentativeIndependence
open TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance
open TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo
open TwistedYetter.Fusion.EGNO

universe uK uC vC uX

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-! ## Algebraic bridge -/

/-- The existing EGNO category data supplies every field of the human spec. -/
noncomputable def currentPremodularCategory_meets_spec
    (𝒞 : PremodularFusionCategory (K := K) (C := C) (S := S)) :
    SemanticSpecification.PremodularCategory
      (K := K) (C := C) (S := S) where
  simple := 𝒞.simple
  simple_isSimple := 𝒞.simple_isSimple
  simple_pairwise := 𝒞.simple_pairwise
  simple_complete := 𝒞.simple_complete
  hom_finite := 𝒞.hom_finite
  multiplicity := 𝒞.multiplicity
  decomposition := 𝒞.decomposition
  unitIndex := 𝒞.unitIndex
  unitIso := 𝒞.unitIso
  dualIndex := 𝒞.dualIndex
  dualIso := 𝒞.dualIso
  twist := 𝒞.ribbon.iso
  twist_tensor := 𝒞.ribbon.tensor
  twist_dual := 𝒞.ribbon.dual

/-- The existing monoidal natural automorphism supplies the exact `η` laws. -/
def currentCharacter_meets_spec
    (η : TensorIdentityAutomorphism C) :
    SemanticSpecification.TensorIdentityCharacter (C := C) where
  iso := η.iso
  tensor := η.tensor_hom
  unit := η.unit_hom

/-! ## Topological family and realization bridge -/

/-- The existing manifold declarations, viewed through the short specification. -/
noncomputable def currentTopology :
    SemanticSpecification.ClosedFourManifoldSemantics.{uX, uX, uX} where
  Manifold := ClosedOrientedSmoothFourManifold.{uX}
  H₂ := fun X => H₂.{uX, uX} X
  h₂AddCommGroup := fun _ => inferInstance
  OrientedDiffeomorphism := fun X Y => orientedDiffeomorphism.Hom X Y
  inducedH₂ := inducedH₂

/--
Change only the external homology coordinate group of a special Kirby
presentation.  The serialized link, handle chain, and all certificates remain
literally unchanged.
-/
private noncomputable def reindexSpecialKirbyPresentation
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.KirbyCompleteness.SpecialKirbyPresentation H2) :
    TwistedYetter.Kirby.KirbyCompleteness.SpecialKirbyPresentation H2' :=
  { presentation with
    h2ModelEquiv := presentation.h2ModelEquiv.trans change }

/-- Reindex the canonical evaluator presentation without changing its link. -/
private noncomputable def reindexCanonicalPresentation
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
        H2) :
    TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
      H2' :=
  { presentation with
    topology := reindexSpecialKirbyPresentation change presentation.topology }

private noncomputable def reindexGeneratorGeometry
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
        H2)
    (generator :
      Fin presentation.topology.counts.turnedOver.h3)
    (geometry :
      TwistedYetter.Kirby.DottedBoundaryGeometry.GeneratorGeometry
        presentation generator) :
    TwistedYetter.Kirby.DottedBoundaryGeometry.GeneratorGeometry
      (reindexCanonicalPresentation change presentation) generator where
  dottedComponentIndex := geometry.dottedComponentIndex
  dottedComponent := geometry.dottedComponent
  dotted_component_def := geometry.dotted_component_def
  dotted_role := geometry.dotted_role
  punctureBoundary := geometry.punctureBoundary
  dotted_absent_from_punctures := geometry.dotted_absent_from_punctures
  puncture_ids_indexed_in_component_registry :=
    geometry.puncture_ids_indexed_in_component_registry
  puncture_ids_are_two_handles := geometry.puncture_ids_are_two_handles
  exteriorContext := geometry.exteriorContext
  dotted_absent_from_exterior := geometry.dotted_absent_from_exterior
  factorization := geometry.factorization
  incidence_sound := geometry.incidence_sound
  geometryCertificateHash := geometry.geometryCertificateHash
  geometry_certificate_hash_shape :=
    geometry.geometry_certificate_hash_shape
  sourceRefs := geometry.sourceRefs
  sourceLocator := geometry.sourceLocator

private noncomputable def reindexGeometrySystem
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
        H2)
    (system :
      TwistedYetter.Kirby.DottedBoundaryGeometry.GeometrySystem presentation) :
    TwistedYetter.Kirby.DottedBoundaryGeometry.GeometrySystem
      (reindexCanonicalPresentation change presentation) where
  geometry := fun generator =>
    reindexGeneratorGeometry change presentation generator
      (system.geometry generator)
  generator_component_injective := system.generator_component_injective
  every_raw_dotted_component_covered :=
    system.every_raw_dotted_component_covered

private noncomputable def reindexSimultaneousGeometry
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
        H2)
    (geometry :
      TwistedYetter.Kirby.SimultaneousDottedCutGeometry.Geometry presentation) :
    TwistedYetter.Kirby.SimultaneousDottedCutGeometry.Geometry
      (reindexCanonicalPresentation change presentation) where
  cutDiagram := geometry.cutDiagram
  erase_isotopy := geometry.erase_isotopy
  every_dotted_cut_exactly_once := geometry.every_dotted_cut_exactly_once
  every_special_cut_is_dotted := geometry.every_special_cut_is_dotted
  dotted_absent_from_ordinary_nodes :=
    geometry.dotted_absent_from_ordinary_nodes
  punctures_are_two_handles := geometry.punctures_are_two_handles

private noncomputable def reindexGeneratorCutWindow
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
        H2)
    (dottedGeometry :
      TwistedYetter.Kirby.DottedBoundaryGeometry.GeometrySystem presentation)
    (simultaneousGeometry :
      TwistedYetter.Kirby.SimultaneousDottedCutGeometry.Geometry presentation)
    (generator :
      Fin presentation.topology.counts.turnedOver.h3)
    (window :
      TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation.GeneratorCutWindow
        presentation dottedGeometry simultaneousGeometry generator) :
    TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation.GeneratorCutWindow
      (reindexCanonicalPresentation change presentation)
      (reindexGeometrySystem change presentation dottedGeometry)
      (reindexSimultaneousGeometry change presentation simultaneousGeometry)
      generator where
  context := window.context
  factorization := window.factorization

/--
Reindex the complete role-aware presentation.  Dependent geometry fields are
transported only because every structural projection of the canonical
presentation is unchanged.
-/
private noncomputable def reindexRoleAwarePresentation
    {H2 H2' : Type uX} [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation.Presentation H2) :
    TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation.Presentation H2' :=
  { canonicalPresentation :=
      reindexCanonicalPresentation change presentation.canonicalPresentation
    dottedGeometry :=
      reindexGeometrySystem change presentation.canonicalPresentation
        presentation.dottedGeometry
    simultaneousGeometry :=
      reindexSimultaneousGeometry change presentation.canonicalPresentation
        presentation.simultaneousGeometry
    generatorCutWindow := fun generator => by
      exact reindexGeneratorCutWindow change
        presentation.canonicalPresentation presentation.dottedGeometry
        presentation.simultaneousGeometry generator
        (presentation.generatorCutWindow generator) }

/--
The missing category-neutral topology certification, isolated as data rather
than hidden in the presentation type.
-/
structure DependentPresentationCertification where
  Realizes :
    (X : ClosedOrientedSmoothFourManifold.{uX}) →
      Presentation.{uX} (H₂.{uX, uX} X) → Prop
  presentationExists :
    (X : ClosedOrientedSmoothFourManifold.{uX}) →
      Nonempty {presentation : Presentation.{uX} (H₂.{uX, uX} X) //
        Realizes X presentation}
  reindex_realizes :
    {X Y : ClosedOrientedSmoothFourManifold.{uX}} →
    (f : orientedDiffeomorphism.Hom X Y) →
    (presentation : Presentation.{uX} (H₂.{uX, uX} X)) →
      Realizes X presentation →
        Realizes Y
          (reindexRoleAwarePresentation (inducedH₂ f) presentation)

/-- Presentations are indexed by the actual group `H₂ X`, never by `ℤ`. -/
abbrev CurrentPresentation
    (certification : DependentPresentationCertification.{uX})
    (X : ClosedOrientedSmoothFourManifold.{uX}) :=
  {presentation : Presentation.{uX} (H₂.{uX, uX} X) //
    certification.Realizes X presentation}

/-- The exact dependent presentation family required by the specification. -/
abbrev currentPresentationFamily
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.PresentationFamily currentTopology :=
  CurrentPresentation certification

/--
The handle-chain homology of a certified presentation is identified with the
actual `H₂ X` by its checked `h2ModelEquiv`.
-/
noncomputable def currentPresentationRealization
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.PresentationRealization
      currentTopology (currentPresentationFamily certification) where
  Realizes := fun {X} presentation Y =>
    Y = X ∧ certification.Realizes X presentation.1
  realizedManifold := fun {X} _ => X
  realizationDiffeomorphism := fun {X} _ =>
    orientedDiffeomorphism.identity X
  realizes_realizedManifold := fun presentation =>
    ⟨rfl, presentation.2⟩
  HandleH₂ := fun presentation =>
    presentation.1.canonicalPresentation.topology.handleChain.SecondHomology
  handleH₂AddCommGroup := fun _ => inferInstance
  handleH₂EquivRealized := fun presentation =>
    presentation.1.canonicalPresentation.topology.h2ModelEquiv

/-! ## Exact role-aware evaluator bridge -/

abbrev CurrentAlgebraicInput :=
  TwistedPremodularCategory (K := K) (C := C) (S := S)

/-- The concrete role-aware evaluator, field for field. -/
noncomputable def currentRoleAwareEvaluator
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.RoleAwareEvaluator
      (K := K) (S := S)
      (CurrentAlgebraicInput (K := K) (C := C) (S := S))
      (currentPresentationFamily certification)
      (currentPresentationRealization certification) where
  OrdinaryComponent := fun presentation =>
    RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryComponentIndex
      presentation.1.canonicalPresentation
  ordinaryComponentFintype := fun _ => inferInstance
  DottedComponent := fun presentation =>
    RoleAwarePremodularEvaluator.CanonicalPresentation.DottedComponentIndex
      presentation.1.canonicalPresentation
  dottedComponentFintype := fun _ => inferInstance
  ordinaryLabelingFintype := fun _ => inferInstance
  HandleCycle := fun presentation =>
    presentation.1.canonicalPresentation.DegreeTwoCycle
  cycleClass := fun {_} {presentation} cycle =>
    presentation.1.canonicalPresentation.topology.handleChain.complex.homologyπ
      2 cycle
  cycleRepresentative := fun presentation homologyClass =>
    presentation.1.canonicalPresentation.chosenCycle homologyClass
  cycleRepresentative_class := fun presentation homologyClass =>
    presentation.1.canonicalPresentation.chosenCycle_class homologyClass
  ordinaryExponent := fun {_} {presentation} cycle component =>
    presentation.1.canonicalPresentation.cycleComponentExponent cycle
      (presentation.1.canonicalPresentation.topology.formal.raw.components.get
        component.1)
  ordinaryCoefficient := fun algebra {_} presentation cycle labeling =>
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
      algebra.1 algebra.2 presentation.1.canonicalPresentation cycle labeling
  specialCutDiagramEvaluation := fun algebra {_} presentation labeling =>
    algebra.1.toFusionCategoryData.closedScalar
      (TwistedYetter.Kirby.CategoricalTangle.Diagram.eval C
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
          algebra.1 algebra.2 presentation.1.canonicalPresentation
          presentation.1.simultaneousGeometry labeling))
  globalDimension := fun algebra => algebra.1.globalDimension
  globalDimension_ne_zero := fun algebra => algebra.1.globalDimension_ne_zero
  oneHandleCount := fun {_} presentation =>
    presentation.1.canonicalPresentation.topology.counts.h1
  twoHandleCount := fun {_} presentation =>
    presentation.1.canonicalPresentation.topology.counts.h2

/-- The short finite-sum numerator is definitionally the implemented sum. -/
theorem currentRawNumerator_eq
    (certification : DependentPresentationCertification.{uX})
    (algebra : CurrentAlgebraicInput (K := K) (C := C) (S := S))
    {X : ClosedOrientedSmoothFourManifold.{uX}}
    (presentation : CurrentPresentation certification X)
    (cycle : presentation.1.canonicalPresentation.DegreeTwoCycle) :
    SemanticSpecification.RoleAwareEvaluator.rawNumerator
        (currentRoleAwareEvaluator certification)
        algebra presentation cycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareRawNumerator
        algebra.1 algebra.2 presentation.1.canonicalPresentation
        presentation.1.simultaneousGeometry cycle := by
  symm
  simpa [
    SemanticSpecification.RoleAwareEvaluator.rawNumerator,
    currentRoleAwareEvaluator
  ] using
    SourceBoundRoleAwareOneTwo.roleAwareRawNumerator_eq_sum
      algebra.1 algebra.2 presentation.1.canonicalPresentation
      presentation.1.simultaneousGeometry cycle

/-- Representative independence is inherited from the source-bound proof. -/
theorem currentRepresentativeIndependent
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.RepresentativeIndependent
      (currentPresentationRealization certification)
      (currentRoleAwareEvaluator
        (K := K) (C := C) (S := S) certification) := by
  intro algebra X presentation left right sameClass
  rw [currentRawNumerator_eq, currentRawNumerator_eq]
  have normalizedEquality :=
    Presentation.roleAwareCycleEval_respects_homology_class
        algebra.1 algebra.2 presentation.1 left right sameClass
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareEvaluationState
    TwistedYetter.Kirby.KirbyCancellation.EvaluationState.normalized
      at normalizedEquality
  exact
    (div_left_inj'
      ((CanonicalPresentation.roleAwareNormalizationProfile
        algebra.1).denominator_ne_zero
          presentation.1.canonicalPresentation.topology.counts)).mp
      normalizedEquality

/-- The semantic evaluator value is exactly the implemented `roleAwareEvalH2`. -/
theorem currentValue_eq_roleAwareEvalH2
    (certification : DependentPresentationCertification.{uX})
    (algebra : CurrentAlgebraicInput (K := K) (C := C) (S := S))
    {X : ClosedOrientedSmoothFourManifold.{uX}}
    (presentation : CurrentPresentation certification X)
    (α : H₂ X) :
    SemanticSpecification.RoleAwareEvaluator.value
        (currentRoleAwareEvaluator certification)
        algebra presentation α =
      roleAwareEvalH2 algebra.1 algebra.2 presentation.1
        (presentation.1.canonicalPresentation.topology.h2ModelEquiv.symm α) := by
  have hTrans :
      presentation.1.canonicalPresentation.topology.h2ModelEquiv.trans
          (AddEquiv.refl (H₂ X)) =
        presentation.1.canonicalPresentation.topology.h2ModelEquiv := by
    ext x
    rfl
  have hSymm := congrArg AddEquiv.symm hTrans
  have hApply := DFunLike.congr_fun hSymm α
  rw [SemanticSpecification.RoleAwareEvaluator.value]
  rw [currentRawNumerator_eq]
  simp [
    SemanticSpecification.PresentationRealization.handleH₂Equiv,
    currentPresentationRealization,
    currentTopology,
    inducedH₂_identity,
    currentRoleAwareEvaluator,
    SemanticSpecification.RoleAwareEvaluator.denominator,
    roleAwareEvalH2,
    CanonicalPresentation.roleAwareCycleEval,
    CanonicalPresentation.roleAwareEvaluationState,
    TwistedYetter.Kirby.KirbyCancellation.EvaluationState.normalized,
    CanonicalPresentation.roleAwareNormalizationProfile,
    TwistedYetter.Kirby.KirbyCancellation.GlobalDimensionProfile.denominator,
    TwistedYetter.Kirby.KirbyCancellation.GlobalDimensionProfile.oneTwoFactor
  ]
  exact congrArg
    (fun β =>
      CanonicalPresentation.roleAwareRawNumerator algebra.1 algebra.2
          presentation.1.canonicalPresentation
          presentation.1.simultaneousGeometry
          (presentation.1.canonicalPresentation.chosenCycle β) /
        (PremodularCategory.globalDimension algebra.1 ^
            (Int.ofNat presentation.1.canonicalPresentation.topology.counts.h2 -
              Int.ofNat presentation.1.canonicalPresentation.topology.counts.h1) *
          PremodularCategory.globalDimension algebra.1 ^
            presentation.1.canonicalPresentation.topology.counts.h1))
    hApply

/-! ## Exact eight-move bridge -/

private def semanticSlideOrientation :
    _root_.TwistedYetter.Kirby.KirbyHandleMoves.BandOrientation →
      SemanticSpecification.SlideOrientation
  | .positive => .positive
  | .negative => .negative

/-- The exact event tag exposed by one concrete role-aware move. -/
private inductive CurrentMoveTag
  | framedIsotopy
  | oneOverOne (orientation : SemanticSpecification.SlideOrientation)
  | twoOverOne (orientation : SemanticSpecification.SlideOrientation)
  | twoOverTwo (orientation : SemanticSpecification.SlideOrientation)
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath

private def currentMoveTag
    {H2 : Type uX} [AddCommGroup H2]
    {source target :
      _root_.TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation.Presentation H2}
    (move :
      _root_.TwistedYetter.Kirby.RoleAwareTableTwoMove.ElementaryMove
        source target) :
    CurrentMoveTag :=
  match move with
  | .framedIsotopy .. => .framedIsotopy
  | .oneOverOne metadata .. =>
      .oneOverOne
        (semanticSlideOrientation
          metadata.recipe.handleEdit.oneOverOneOrientation)
  | .twoOverOne metadata .. =>
      .twoOverOne
        (semanticSlideOrientation
          metadata.recipe.handleEdit.twoOverOneOrientation)
  | .twoOverTwo metadata .. =>
      .twoOverTwo
        (semanticSlideOrientation
          metadata.recipe.handleEdit.twoOverTwoOrientation)
  | .oneTwoBirth .. => .oneTwoBirth
  | .oneTwoDeath .. => .oneTwoDeath
  | .twoThreeBirth .. => .twoThreeBirth
  | .twoThreeDeath .. => .twoThreeDeath

/--
One concrete move together with the category-neutral statement that its
handle-chain transport preserves the displayed class in the actual `H₂ X`.
-/
structure CurrentMoveCertificate
    (certification : DependentPresentationCertification.{uX})
    {X : ClosedOrientedSmoothFourManifold.{uX}}
    (source target : CurrentPresentation certification X) where
  move :
    _root_.TwistedYetter.Kirby.RoleAwareTableTwoMove.ElementaryMove
      source.1 target.1
  displayedClass_sound :
    ∀ α : H₂ X,
      _root_.TwistedYetter.Kirby.RoleAwareTableTwoMove.ElementaryMove.transport
          move
          (source.1.canonicalPresentation.topology.h2ModelEquiv.symm α) =
        target.1.canonicalPresentation.topology.h2ModelEquiv.symm α

private def currentMoveRelation
    (certification : DependentPresentationCertification.{uX})
    (tag : CurrentMoveTag)
    {X : ClosedOrientedSmoothFourManifold.{uX}}
    (source target : CurrentPresentation certification X) : Prop :=
  ∃ certificate : CurrentMoveCertificate certification source target,
    currentMoveTag certificate.move = tag

/-- The semantic eight-event language is the exact tagging of concrete moves. -/
def currentMoveRelations
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.ElementaryMoveRelations
      (currentPresentationFamily certification) where
  framedIsotopy := currentMoveRelation certification .framedIsotopy
  oneOverOne := fun orientation =>
    currentMoveRelation certification (.oneOverOne orientation)
  twoOverOne := fun orientation =>
    currentMoveRelation certification (.twoOverOne orientation)
  twoOverTwo := fun orientation =>
    currentMoveRelation certification (.twoOverTwo orientation)
  oneTwoBirth := currentMoveRelation certification .oneTwoBirth
  oneTwoDeath := currentMoveRelation certification .oneTwoDeath
  twoThreeBirth := currentMoveRelation certification .twoThreeBirth
  twoThreeDeath := currentMoveRelation certification .twoThreeDeath

/--
All eight semantic move cases are discharged by the concrete role-aware local
invariance theorem plus the category-neutral marking soundness certificate.
-/
theorem currentPreservesElementaryMoves
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.PreservesElementaryMoves
      (currentPresentationRealization certification)
      (currentMoveRelations certification)
      (currentRoleAwareEvaluator
        (K := K) (C := C) (S := S) certification) := by
  intro algebra X source target semanticMove α
  cases semanticMove with
  | framedIsotopy witness
  | oneOverOne _ witness
  | twoOverOne _ witness
  | twoOverTwo _ witness
  | oneTwoBirth witness
  | oneTwoDeath witness
  | twoThreeBirth witness
  | twoThreeDeath witness =>
      rcases witness with ⟨certificate, _⟩
      rw [currentValue_eq_roleAwareEvalH2]
      rw [currentValue_eq_roleAwareEvalH2]
      rw [← certificate.displayedClass_sound α]
      exact
        PremodularRoleAwareLocalInvariance.elementaryMove_invariant
          algebra.1 algebra.2 certificate.move
          (source.1.canonicalPresentation.topology.h2ModelEquiv.symm α)

/-!
## Remaining dependent reindex bridge

This definition is intentionally left red until the concrete presentation
language supplies an honest change-of-`H₂` constructor.  Filling it by
choosing a fresh unrelated presentation would not prove reindexing
invariance; filling it with the old global `AuxiliaryH₂ := ℤ` would restore
the semantic bug that this bridge is designed to expose.
-/

noncomputable def currentPresentationReindexing
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.PresentationReindexing
      (currentPresentationFamily certification) where
  reindex := by
    intro X Y f presentation
    exact
      ⟨reindexRoleAwarePresentation (inducedH₂ f) presentation.1,
        certification.reindex_realizes f presentation.1 presentation.2⟩

set_option maxHeartbeats 800000 in
-- The proof unfolds and compares two complete finite role-aware sums.
/--
Reindexing changes only the external `H₂` marking, so the role-aware
evaluation of the transported class is unchanged.
-/
theorem currentPreservesReindexing
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.PreservesReindexing
      (currentPresentationRealization certification)
      (currentPresentationReindexing certification)
      (currentRoleAwareEvaluator
        (K := K) (C := C) (S := S) certification) := by
  intro algebra X Y f presentation α
  have hClass :
      ((presentation.1.canonicalPresentation.topology.h2ModelEquiv.trans
          (inducedH₂ f)).symm (inducedH₂ f α)) =
        presentation.1.canonicalPresentation.topology.h2ModelEquiv.symm α := by
    simp
  let β :=
    presentation.1.canonicalPresentation.topology.h2ModelEquiv.symm α
  let reindexed :=
    reindexRoleAwarePresentation (inducedH₂ f) presentation.1
  let sourceCycle :=
    presentation.1.canonicalPresentation.chosenCycle β
  let targetCycle :=
    reindexed.canonicalPresentation.chosenCycle β
  have hLabel
      (labeling :
        CanonicalPresentation.OrdinaryLabeling
          (S := S) presentation.1.canonicalPresentation) :
      CanonicalPresentation.roleAwareLabelOf algebra.1
          presentation.1.canonicalPresentation labeling =
        CanonicalPresentation.roleAwareLabelOf algebra.1
          reindexed.canonicalPresentation labeling := by
    funext componentId
    unfold CanonicalPresentation.roleAwareLabelOf
      CanonicalPresentation.roleAwareLabelOfWithUnit
    simp [reindexed, reindexRoleAwarePresentation,
      reindexCanonicalPresentation, reindexSpecialKirbyPresentation]
    split <;> rfl
  have hExponent
      (component : TwistedYetter.Kirby.Presentation.ComponentSpec) :
      presentation.1.canonicalPresentation.cycleComponentExponent
          sourceCycle component =
        reindexed.canonicalPresentation.cycleComponentExponent
          sourceCycle component := by
    unfold
      CanonicalModularKirbyEvaluator.CanonicalPresentation.cycleComponentExponent
      KirbyCompleteness.SpecialKirbyPresentation.cycleComponentExponent
      KirbyCompleteness.SpecialKirbyPresentation.cycleHandleCoefficients
    simp [reindexed, reindexRoleAwarePresentation,
      reindexCanonicalPresentation, reindexSpecialKirbyPresentation]
    split <;> rfl
  have hWeight
      (labeling :
        CanonicalPresentation.OrdinaryLabeling
          (S := S) presentation.1.canonicalPresentation) :
      CanonicalPresentation.roleAwareGlobalWeight algebra.1 algebra.2
          presentation.1.canonicalPresentation sourceCycle labeling =
        CanonicalPresentation.roleAwareGlobalWeight algebra.1 algebra.2
          reindexed.canonicalPresentation sourceCycle labeling := by
    unfold CanonicalPresentation.roleAwareGlobalWeight
    apply Finset.prod_congr rfl
    intro index _
    unfold
      CanonicalModularKirbyEvaluator.CanonicalPresentation.cycleComponentWeight
    rw [hExponent]
    congr 2
  have hTerm
      (labeling :
        CanonicalPresentation.OrdinaryLabeling
          (S := S) presentation.1.canonicalPresentation) :
      CanonicalPresentation.roleAwareTermDiagram algebra.1 algebra.2
          presentation.1.canonicalPresentation
          presentation.1.simultaneousGeometry labeling =
        CanonicalPresentation.roleAwareTermDiagram algebra.1 algebra.2
          reindexed.canonicalPresentation
          reindexed.simultaneousGeometry labeling := by
    unfold CanonicalPresentation.roleAwareTermDiagram
    rw [hLabel]
    rfl
  have hStructural :
      CanonicalPresentation.roleAwareCycleEval algebra.1 algebra.2
          presentation.1.canonicalPresentation
          presentation.1.simultaneousGeometry sourceCycle =
        CanonicalPresentation.roleAwareCycleEval algebra.1 algebra.2
          reindexed.canonicalPresentation
          reindexed.simultaneousGeometry sourceCycle := by
    unfold
      CanonicalPresentation.roleAwareCycleEval
      CanonicalPresentation.roleAwareEvaluationState
      TwistedYetter.Kirby.KirbyCancellation.EvaluationState.normalized
    congr 1
    unfold
      CanonicalPresentation.roleAwareRawNumerator
      CanonicalPresentation.roleAwareLinearDiagram
    apply congrArg algebra.1.toFusionCategoryData.closedScalar
    simp only [LinearDiagram.eval_weightedSum]
    apply Finset.sum_congr rfl
    intro labeling _
    rw [hWeight labeling, hTerm labeling]
  have hSameClass :
      reindexed.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 sourceCycle =
        reindexed.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 targetCycle := by
    change
      presentation.1.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 sourceCycle =
        reindexed.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 targetCycle
    rw [presentation.1.canonicalPresentation.chosenCycle_class]
    rw [reindexed.canonicalPresentation.chosenCycle_class]
  have hEval :
      roleAwareEvalH2 algebra.1 algebra.2 presentation.1
          β =
        roleAwareEvalH2 algebra.1 algebra.2 reindexed β := by
    calc
      roleAwareEvalH2 algebra.1 algebra.2 presentation.1 β =
          CanonicalPresentation.roleAwareCycleEval algebra.1 algebra.2
            presentation.1.canonicalPresentation
            presentation.1.simultaneousGeometry sourceCycle := rfl
      _ =
          CanonicalPresentation.roleAwareCycleEval algebra.1 algebra.2
            reindexed.canonicalPresentation
            reindexed.simultaneousGeometry sourceCycle := hStructural
      _ =
          CanonicalPresentation.roleAwareCycleEval algebra.1 algebra.2
            reindexed.canonicalPresentation
            reindexed.simultaneousGeometry targetCycle :=
        _root_.TwistedYetter.Kirby.RoleAwareRepresentativeIndependence.Presentation.roleAwareCycleEval_respects_homology_class
            algebra.1 algebra.2 reindexed sourceCycle targetCycle hSameClass
      _ = roleAwareEvalH2 algebra.1 algebra.2 reindexed β := rfl
  rw [currentValue_eq_roleAwareEvalH2]
  rw [currentValue_eq_roleAwareEvalH2]
  change
    roleAwareEvalH2 algebra.1 algebra.2 presentation.1
        β =
      roleAwareEvalH2 algebra.1 algebra.2 reindexed
        (((presentation.1.canonicalPresentation.topology.h2ModelEquiv.trans
          (inducedH₂ f)).symm (inducedH₂ f α)))
  rw [hClass]
  exact hEval

/-! ## Marked Kirby--Cerf descent bridge -/

/--
The remaining global topology boundary.  It is an explicit theorem parameter,
not a result constructed below and not a hidden global axiom.  It says only
that the exact role-aware move language is complete for certified
presentations of the same marked manifold pair.
-/
structure DependentKirbyCerfCertification extends
    DependentPresentationCertification.{uX} where
  kirbyCerfComplete :
    SemanticSpecification.KirbyCerfComplete
      (currentMoveRelations toDependentPresentationCertification)
      (currentPresentationReindexing toDependentPresentationCertification)

/-- T1 is exactly the existence field of the dependent certification. -/
theorem currentPresentationExistence
    (certification : DependentPresentationCertification.{uX}) :
    SemanticSpecification.PresentationExistence
      (currentPresentationFamily certification) :=
  certification.presentationExists

/-- The intrinsic value obtained from the fully dependent presentation route. -/
noncomputable def dependentTwistedYetter
    (topology : DependentKirbyCerfCertification.{uX})
    (algebra : CurrentAlgebraicInput (K := K) (C := C) (S := S))
    (Xα : SemanticSpecification.HomologicalFourManifold currentTopology) :
    K :=
  SemanticSpecification.descendedValue
    (currentPresentationExistence
      topology.toDependentPresentationCertification)
    (currentPresentationRealization
      topology.toDependentPresentationCertification)
    (currentRoleAwareEvaluator
      (K := K) (C := C) (S := S)
      topology.toDependentPresentationCertification)
    algebra Xα

/--
The fully bridged role-aware premodular evaluator is invariant under oriented
diffeomorphism for arbitrary integral `H₂ X`.
-/
theorem dependentTwistedYetter_diffeomorphism_invariant
    (topology : DependentKirbyCerfCertification.{uX}) :
    SemanticSpecification.DiffeomorphismInvariant
      currentTopology
      (CurrentAlgebraicInput (K := K) (C := C) (S := S))
      K
      (dependentTwistedYetter
        (K := K) (C := C) (S := S) topology) := by
  exact
    SemanticSpecification.descendedValue_diffeomorphism_invariant
      (currentPresentationExistence
        topology.toDependentPresentationCertification)
      (currentPresentationRealization
        topology.toDependentPresentationCertification)
      (currentMoveRelations
        topology.toDependentPresentationCertification)
      (currentPresentationReindexing
        topology.toDependentPresentationCertification)
      topology.kirbyCerfComplete
      (currentRoleAwareEvaluator
        (K := K) (C := C) (S := S)
        topology.toDependentPresentationCertification)
      (currentPreservesReindexing
        (K := K) (C := C) (S := S)
        topology.toDependentPresentationCertification)
      (currentPreservesElementaryMoves
        (K := K) (C := C) (S := S)
        topology.toDependentPresentationCertification)

end TwistedYetter.Kirby.Final.SemanticImplementationBridge
