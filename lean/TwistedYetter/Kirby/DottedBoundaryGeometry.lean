import TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
import TwistedYetter.Kirby.ComponentBoundarySignedProduct
import TwistedYetter.Kirby.ComponentDottedEncircling
import TwistedYetter.Kirby.ComponentRibbonIsotopy
import TwistedYetter.Kirby.LinearContext
import TwistedYetter.Kirby.SelectedCoordinateFiniteSum

/-!
# Geometry certificates for dual degree-three boundary generators

The evaluator's degree-three basis is the basis dual to the primal
one-handles.  This module states exactly what must be checked in the raw
serialized Kirby diagram for one such generator:

* select an actual raw component and prove that it is dotted;
* expose its spanning-disk punctures as a free component boundary;
* factor the complete canonical trace through one free open-encircling window;
* identify every signed puncture multiplicity with the corresponding
  coordinate of the evaluator's actual degree-three boundary.

The certificate is category-neutral.  It contains no category object,
morphism, scalar, linear diagram, evaluator value, or equality of evaluator
values.  Its factorization witness is a term of the closed free-isotopy
grammar, not an arbitrary graphical equality.
-/

namespace TwistedYetter.Kirby.DottedBoundaryGeometry

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.ComponentBoundarySignedProduct
open TwistedYetter.Kirby.ComponentDottedEncircling
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.HandleChainGeneratorReduction
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.ModularDottedEncircling
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum

universe uK uC vC uH

/--
Coordinate row of one integral evaluator-side degree-three generator.

This is read from the same `HandleChainModel` consumed by `EvalC`: add the
unit generator boundary to the zero cycle and then read the stored
degree-two basis coordinate.  It is not an independently supplied matrix.
-/
noncomputable def integralGeneratorBoundaryRow
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (generator : Fin presentation.topology.counts.turnedOver.h3)
    (twoHandle : Fin presentation.topology.counts.h2) : ℤ :=
  presentation.cycleHandleCoefficients
    (addBoundary presentation.topology.handleChain 0
      (coordinateChain presentation.topology.handleChain generator 1))
    twoHandle

/--
The coefficient shift used by a dotted-disk movie is forced by the actual
handle chain complex: adding coefficient `n` of generator `i` adds `n` times
the unit-generator row to every two-handle coordinate.
-/
theorem cycleHandleCoefficients_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (cycle : presentation.DegreeTwoCycle)
    (generator : Fin presentation.topology.counts.turnedOver.h3)
    (coefficient : ℤ)
    (twoHandle : Fin presentation.topology.counts.h2) :
    presentation.cycleHandleCoefficients
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            generator coefficient)) twoHandle =
      presentation.cycleHandleCoefficients cycle twoHandle +
        integralGeneratorBoundaryRow presentation generator twoHandle *
          coefficient := by
  let coordinateMap :=
    presentation.topology.handleChain.degreeTwoBasis.hom.hom
  change coordinateMap
      (presentation.topology.handleChain.complex.iCycles 2
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            generator coefficient))) twoHandle = _
  rw [iCycles_addBoundary_coordinateChain]
  rw [coordinateMap.map_add]
  rw [map_zsmul coordinateMap]
  change
    presentation.cycleHandleCoefficients cycle twoHandle +
        coefficient *
          integralGeneratorBoundaryRow presentation generator twoHandle =
      presentation.cycleHandleCoefficients cycle twoHandle +
        integralGeneratorBoundaryRow presentation generator twoHandle *
          coefficient
  rw [mul_comm]

/--
One exact topology-side dotted-disk factorization for one dual generator.
-/
structure GeneratorGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (generator : Fin presentation.topology.counts.turnedOver.h3) where
  dottedComponentIndex :
    Fin presentation.topology.formal.raw.components.length
  dottedComponent : ComponentSpec :=
    presentation.topology.formal.raw.components.get dottedComponentIndex
  dotted_component_def :
    dottedComponent =
      presentation.topology.formal.raw.components.get dottedComponentIndex
  dotted_role : dottedComponent.role = .dotted
  punctureBoundary : ComponentBoundary
  dotted_absent_from_punctures :
    dottedComponent.componentId ∉ punctureBoundary.componentIds
  puncture_ids_indexed_in_component_registry :
    (componentId : String) →
      componentId ∈ punctureBoundary.componentIds →
        ∃ componentIndex,
          presentation.componentIndexing.indexOf componentId =
            some componentIndex
  puncture_ids_are_two_handles :
    (componentId : String) →
      componentId ∈ punctureBoundary.componentIds →
        ∃ twoHandle,
          presentation.topology.twoHandleIndex? componentId =
            some twoHandle
  exteriorContext :
    ComponentDiagram.Context
      punctureBoundary punctureBoundary .unit .unit
  dotted_absent_from_exterior :
    dottedComponent.componentId ∉ exteriorContext.componentIds
  factorization :
    GeneratedIsotopy presentation.componentTermDiagram
      (exteriorContext.plug
        (ComponentDiagram.openDottedEncircling
          dottedComponent.componentId punctureBoundary))
  incidence_sound :
    (twoHandle : Fin presentation.topology.counts.h2) →
      signedMultiplicity
          (presentation.topology.twoHandleComponent twoHandle).componentId
          punctureBoundary =
        integralGeneratorBoundaryRow presentation generator twoHandle
  geometryCertificateHash : String
  geometry_certificate_hash_shape :
    RawPresentation.sha256Shape geometryCertificateHash = true
  sourceRefs : List String
  sourceLocator : String

namespace GeneratorGeometry

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Reconstruct a complete labeling after isolating the dotted coordinate. -/
def labelingWithDotted
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (dottedLabel : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    presentation.GlobalLabeling (S := S) :=
  combineAt geometry.dottedComponentIndex dottedLabel remaining

@[simp] theorem labelingWithDotted_selected
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (dottedLabel : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    geometry.labelingWithDotted dottedLabel remaining
        geometry.dottedComponentIndex = dottedLabel := by
  simp [labelingWithDotted]

/-- The isolated coordinate really labels the selected dotted component. -/
theorem labelOf_dotted
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (dottedLabel : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    presentation.labelOf 𝒞.premodular
        (geometry.labelingWithDotted dottedLabel remaining)
        geometry.dottedComponent.componentId = dottedLabel := by
  rw [geometry.dotted_component_def]
  rw [presentation.labelOf_component]
  exact geometry.labelingWithDotted_selected dottedLabel remaining

/-- Changing the dotted coordinate leaves every different component ID fixed. -/
theorem labelOf_labelingWithDotted_eq_of_ne
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (leftDotted rightDotted : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (componentId : String)
    (different : componentId ≠ geometry.dottedComponent.componentId) :
    presentation.labelOf 𝒞.premodular
        (geometry.labelingWithDotted leftDotted remaining) componentId =
      presentation.labelOf 𝒞.premodular
        (geometry.labelingWithDotted rightDotted remaining) componentId := by
  unfold CanonicalPresentation.labelOf
  cases lookup : presentation.componentIndexing.indexOf componentId with
  | none => rfl
  | some componentIndex =>
      have index_ne : componentIndex ≠ geometry.dottedComponentIndex := by
        intro equal
        have component_id :=
          presentation.componentIndexing.index_sound
            componentId componentIndex lookup
        apply different
        rw [geometry.dotted_component_def]
        rw [component_id, equal]
      simp only
      simp [labelingWithDotted, combineAt, splitAt, index_ne]

/-- Puncture labels are independent of the isolated dotted coordinate. -/
theorem labelOf_eq_on_punctures
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (leftDotted rightDotted : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    ∀ componentId ∈ geometry.punctureBoundary.componentIds,
      presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted leftDotted remaining) componentId =
        presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted rightDotted remaining) componentId := by
  intro componentId membership
  apply geometry.labelOf_labelingWithDotted_eq_of_ne
  intro equal
  apply geometry.dotted_absent_from_punctures
  rw [← equal]
  exact membership

/-- Exterior labels are independent of the isolated dotted coordinate. -/
theorem labelOf_eq_on_exterior
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (leftDotted rightDotted : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    ∀ componentId ∈ geometry.exteriorContext.componentIds,
      presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted leftDotted remaining) componentId =
        presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted rightDotted remaining) componentId := by
  intro componentId membership
  apply geometry.labelOf_labelingWithDotted_eq_of_ne
  intro equal
  apply geometry.dotted_absent_from_exterior
  rw [← equal]
  exact membership

/-- The interpreted puncture object is fixed while the dotted label varies. -/
theorem punctureBoundary_interpret_eq
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (leftDotted rightDotted : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    geometry.punctureBoundary.interpret 𝒞.premodular
        (presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted leftDotted remaining)) =
      geometry.punctureBoundary.interpret 𝒞.premodular
        (presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted rightDotted remaining)) := by
  exact geometry.punctureBoundary.interpret_eq_of_eq_on_componentIds
    𝒞.premodular _ _
    (geometry.labelOf_eq_on_punctures 𝒞 presentation
      leftDotted rightDotted remaining)

/-- The interpreted exterior context is fixed while the dotted label varies. -/
theorem exteriorContext_interpret_heq
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (leftDotted rightDotted : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    HEq
      (geometry.exteriorContext.interpret 𝒞.premodular
        (presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted leftDotted remaining)))
      (geometry.exteriorContext.interpret 𝒞.premodular
        (presentation.labelOf 𝒞.premodular
          (geometry.labelingWithDotted rightDotted remaining))) := by
  exact geometry.exteriorContext.interpret_heq_of_eq_on_hole_and_componentIds
    𝒞.premodular _ _
    (geometry.labelOf_eq_on_punctures 𝒞 presentation
      leftDotted rightDotted remaining)
    (geometry.labelOf_eq_on_punctures 𝒞 presentation
      leftDotted rightDotted remaining)
    (geometry.labelOf_eq_on_exterior 𝒞 presentation
      leftDotted rightDotted remaining)

/-- A fixed complete labeling used to type the common exterior context. -/
def referenceLabeling
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    presentation.GlobalLabeling (S := S) :=
  geometry.labelingWithDotted
    category.premodular.toFusionCategoryData.unitIndex remaining

/-- Component-label lookup associated to the fixed reference labeling. -/
def referenceLabelOf
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    String → S :=
  presentation.labelOf category.premodular
    (geometry.referenceLabeling category remaining)

/-- The common exterior context after all labels except the dotted one are fixed. -/
def referenceExteriorContext
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    CategoricalTangle.Context C
      (geometry.punctureBoundary.interpret category.premodular
        (geometry.referenceLabelOf category presentation remaining))
      (geometry.punctureBoundary.interpret category.premodular
        (geometry.referenceLabelOf category presentation remaining))
      .unit .unit :=
  geometry.exteriorContext.interpret category.premodular
    (geometry.referenceLabelOf category presentation remaining)

/-- Evaluation of a plugged piece is the linear action of its context. -/
theorem evalContextLinearMap_piece
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context : CategoricalTangle.Context C
      holeSource holeTarget wholeSource wholeTarget)
    (piece : Diagram C holeSource holeTarget) :
    evalContextLinearMap (R := K) context (Diagram.eval C piece) =
      Diagram.eval C (CategoricalTangle.Context.plug C context piece) := by
  calc
    evalContextLinearMap (R := K) context (Diagram.eval C piece) =
        Diagram.eval C
          (CategoricalTangle.Context.plug C context
            (Diagram.coupon "context-linearized-piece"
              (Diagram.eval C piece))) :=
      evalContextLinearMap_apply context _ _
    _ = Diagram.eval C
        (CategoricalTangle.Context.plug C context piece) :=
      CategoricalTangle.Context.eval_plug_congr C context rfl

private theorem openEncircling_eval_heq_of_boundary_eq
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S)
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      (Diagram.eval C (source := .atom left.denote) (target := .atom left.denote)
        (openEncirclingDiagram data simple left.denote))
      (Diagram.eval C (source := .atom right.denote) (target := .atom right.denote)
        (openEncirclingDiagram data simple right.denote)) := by
  subst right
  rfl

private theorem eval_plug_eq_evalContextLinearMap_of_heq
    {leftHole rightHole : Boundary C}
    {leftContext : CategoricalTangle.Context C
      leftHole leftHole .unit .unit}
    {rightContext : CategoricalTangle.Context C
      rightHole rightHole .unit .unit}
    {piece : Diagram C leftHole leftHole}
    {rightMorphism : rightHole.denote ⟶ rightHole.denote}
    (holeEq : leftHole = rightHole)
    (contextHeq : HEq leftContext rightContext)
    (morphismHeq : HEq (Diagram.eval C piece) rightMorphism) :
    Diagram.eval C
        (CategoricalTangle.Context.plug C leftContext piece) =
      evalContextLinearMap (R := K) rightContext rightMorphism := by
  subst rightHole
  have contextEq : leftContext = rightContext := eq_of_heq contextHeq
  have morphismEq : Diagram.eval C piece = rightMorphism :=
    eq_of_heq morphismHeq
  rw [← contextEq]
  rw [← evalContextLinearMap_piece (K := K) leftContext piece]
  exact congrArg (evalContextLinearMap (R := K) leftContext) morphismEq

/--
With every other label fixed, a summand is one common linear exterior
context applied to a simple-labelled open meridian.
-/
theorem factorizedTerm_eval_eq_contextOpen
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (dottedLabel : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    Diagram.eval C
        ((geometry.exteriorContext.plug
          (ComponentDiagram.openDottedEncircling
            geometry.dottedComponent.componentId
            geometry.punctureBoundary)).interpret
          category.premodular
          (presentation.labelOf category.premodular
            (geometry.labelingWithDotted dottedLabel remaining))) =
      evalContextLinearMap (R := K)
        (geometry.referenceExteriorContext category presentation remaining)
        (Diagram.eval C
          (source := .atom
            (geometry.punctureBoundary.interpret category.premodular
              (geometry.referenceLabelOf category presentation remaining)).denote)
          (target := .atom
            (geometry.punctureBoundary.interpret category.premodular
              (geometry.referenceLabelOf category presentation remaining)).denote)
          (openEncirclingDiagram category.premodular dottedLabel
            (geometry.punctureBoundary.interpret category.premodular
              (geometry.referenceLabelOf category presentation remaining)).denote)) := by
  let reference :=
    category.premodular.toFusionCategoryData.unitIndex
  have boundaryEq := geometry.punctureBoundary_interpret_eq
    category presentation dottedLabel reference remaining
  have contextHeq := geometry.exteriorContext_interpret_heq
    category presentation dottedLabel reference remaining
  rw [ComponentDiagram.Context.interpret_plug]
  apply eval_plug_eq_evalContextLinearMap_of_heq
    (holeEq := boundaryEq) (contextHeq := contextHeq)
  have localEq :=
    ComponentDiagram.openDottedEncircling_interpret_eval
      category.premodular
      (presentation.labelOf category.premodular
        (geometry.labelingWithDotted dottedLabel remaining))
      geometry.dottedComponent.componentId geometry.punctureBoundary
  rw [geometry.labelOf_dotted category presentation dottedLabel remaining]
    at localEq
  exact (heq_of_eq localEq).trans
    (openEncircling_eval_heq_of_boundary_eq
      category.premodular dottedLabel boundaryEq)

/--
The stored free factorization is sound after interpretation in every modular
category and under every complete component labeling.
-/
theorem termDiagram_eval_eq_factorized
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (labeling : presentation.GlobalLabeling (S := S)) :
    Diagram.eval C (presentation.termDiagram 𝒞.premodular labeling) =
      Diagram.eval C
        ((geometry.exteriorContext.plug
          (ComponentDiagram.openDottedEncircling
            geometry.dottedComponent.componentId
            geometry.punctureBoundary)).interpret
          𝒞.premodular (presentation.labelOf 𝒞.premodular labeling)) := by
  simpa only [CanonicalPresentation.termDiagram,
    CanonicalPresentation.componentTermDiagram] using
    geometry.factorization.eval_eq
      𝒞.premodular (presentation.labelOf 𝒞.premodular labeling)

/--
For every serialized component, the exponent shift is exactly the signed
puncture multiplicity times the integral boundary-generator coefficient.
Unindexed components are handled by proving that they do not occur among the
punctures; they are not silently dropped.
-/
theorem cycleComponentExponent_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (coefficient : ℤ)
    (component : ComponentSpec) :
    presentation.cycleComponentExponent
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            generator coefficient)) component =
      presentation.cycleComponentExponent cycle component +
        signedMultiplicity component.componentId
          geometry.punctureBoundary * coefficient := by
  unfold CanonicalPresentation.cycleComponentExponent
  cases handleIndexEq :
      presentation.topology.twoHandleIndex? component.componentId with
  | none =>
    simp only [SpecialKirbyPresentation.cycleComponentExponent, handleIndexEq]
    have absent :
        component.componentId ∉ geometry.punctureBoundary.componentIds := by
      intro present
      obtain ⟨twoHandle, indexed⟩ :=
        geometry.puncture_ids_are_two_handles component.componentId present
      rw [handleIndexEq] at indexed
      contradiction
    rw [signedMultiplicity_eq_zero_of_not_mem
      component.componentId geometry.punctureBoundary absent]
    simp
  | some handleIndex =>
    simp only [SpecialKirbyPresentation.cycleComponentExponent, handleIndexEq]
    change
      presentation.cycleHandleCoefficients
          (addBoundary presentation.topology.handleChain cycle
            (coordinateChain presentation.topology.handleChain
              generator coefficient)) handleIndex =
        presentation.cycleHandleCoefficients cycle handleIndex +
          signedMultiplicity component.componentId
            geometry.punctureBoundary * coefficient
    rw [cycleHandleCoefficients_add_integralGenerator]
    have component_id :=
      presentation.topology.two_handle_index_sound
        component.componentId _ handleIndexEq
    rw [component_id, geometry.incidence_sound]

/-- Product of all component weights except the isolated dotted coordinate. -/
noncomputable def remainingGlobalWeight
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) : K :=
  ∏ index : RemainingIndex geometry.dottedComponentIndex,
    presentation.cycleComponentWeight category automorphism cycle
      (presentation.topology.formal.raw.components.get index.1)
      (remaining index)

/-- A dotted component contributes quantum dimension and no cycle character. -/
theorem cycleComponentWeight_dotted
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (dottedLabel : S) :
    presentation.cycleComponentWeight category automorphism cycle
        geometry.dottedComponent dottedLabel =
      category.premodular.quantumDimension dottedLabel := by
  have unindexed := presentation.topology.dotted_component_unindexed
    geometry.dottedComponent geometry.dotted_role
  unfold CanonicalPresentation.cycleComponentWeight
  unfold CanonicalPresentation.cycleComponentExponent
  unfold SpecialKirbyPresentation.cycleComponentExponent
  rw [unindexed]
  simp

/-- The complete global weight splits at the selected dotted coordinate. -/
theorem cycleGlobalWeight_split_dotted
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (dottedLabel : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S) :
    presentation.cycleGlobalWeight category automorphism cycle
        (geometry.labelingWithDotted dottedLabel remaining) =
      category.premodular.quantumDimension dottedLabel *
        geometry.remainingGlobalWeight category automorphism
          presentation cycle remaining := by
  classical
  unfold CanonicalPresentation.cycleGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne]
  rw [← geometry.dotted_component_def]
  rw [geometry.labelingWithDotted_selected]
  rw [geometry.cycleComponentWeight_dotted
    category automorphism presentation cycle dottedLabel]
  congr 1
  unfold remainingGlobalWeight
  apply Finset.prod_congr rfl
  intro index _
  congr 2
  exact combineAt_remaining geometry.dottedComponentIndex
    dottedLabel remaining index

/-- Internal reindexing lemma used before the public named corollary below. -/
private theorem boundaryCharacterPower_eq_rawRegistryProduct_aux
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (labeling : presentation.GlobalLabeling (S := S))
    (coefficient : ℤ) :
    boundaryCharacterPower
        category.premodular.toFusionCategoryData automorphism
        (presentation.labelOf category.premodular labeling)
        geometry.punctureBoundary coefficient =
      ↑(∏ componentIndex,
        (category.premodular.toFusionCategoryData.automorphismSimpleUnit
          automorphism (labeling componentIndex)) ^
          (signedMultiplicity
              (presentation.topology.formal.raw.components.get
                componentIndex).componentId
              geometry.punctureBoundary * coefficient) : Kˣ) := by
  rw [boundaryCharacterPower_eq_signedProduct]
  rw [signedProduct_eq_indexedProduct
    (value := fun componentId =>
      category.premodular.toFusionCategoryData.automorphismSimpleUnit
        automorphism (presentation.labelOf category.premodular labeling componentId))
    (coefficient := coefficient)
    (indexOf := presentation.componentIndexing.indexOf)
    (idOf := fun componentIndex =>
      (presentation.topology.formal.raw.components.get
        componentIndex).componentId)
    (roundtrip := presentation.componentIndexing.index_roundtrip)
    (sound := presentation.componentIndexing.index_sound)
    (boundary := geometry.punctureBoundary)
    (allIndexed := geometry.puncture_ids_indexed_in_component_registry)]
  congr 1
  apply Finset.prod_congr rfl
  intro componentIndex _
  rw [presentation.labelOf_component
    category.premodular labeling componentIndex]

/--
The complete global-label coefficient acquires exactly one boundary-character
factor under an integral generator boundary.  This is a finite product over
the exact raw component registry, so no component or exponent is implicit.
-/
theorem cycleGlobalWeight_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (coefficient : ℤ)
    (labeling : presentation.GlobalLabeling (S := S)) :
    presentation.cycleGlobalWeight 𝒞 automorphism
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            generator coefficient)) labeling =
      boundaryCharacterPower
          𝒞.premodular.toFusionCategoryData automorphism
          (presentation.labelOf 𝒞.premodular labeling)
          geometry.punctureBoundary coefficient *
        presentation.cycleGlobalWeight 𝒞 automorphism cycle labeling := by
  classical
  rw [geometry.boundaryCharacterPower_eq_rawRegistryProduct_aux
    𝒞 automorphism presentation labeling coefficient]
  unfold CanonicalPresentation.cycleGlobalWeight
  rw [show
      (∏ index,
        presentation.cycleComponentWeight 𝒞 automorphism
          (addBoundary presentation.topology.handleChain cycle
            (coordinateChain presentation.topology.handleChain
              generator coefficient))
          (presentation.topology.formal.raw.components.get index)
          (labeling index)) =
        ∏ index,
          𝒞.premodular.toFusionCategoryData.automorphismScalarPower
              automorphism (labeling index)
              (signedMultiplicity
                (presentation.topology.formal.raw.components.get index).componentId
                geometry.punctureBoundary * coefficient) *
            presentation.cycleComponentWeight 𝒞 automorphism cycle
              (presentation.topology.formal.raw.components.get index)
              (labeling index) by
    apply Finset.prod_congr rfl
    intro index _
    unfold CanonicalPresentation.cycleComponentWeight
    rw [geometry.cycleComponentExponent_add_integralGenerator]
    rw [FusionCategoryData.automorphismScalarPower_add]
    ring]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [FusionCategoryData.automorphismScalarPower]
  simp

/--
The puncture character can be reindexed over the exact raw component
registry.  This proves that no puncture occurrence is lost or duplicated
before the dotted-label sum is isolated.
-/
theorem boundaryCharacterPower_eq_rawRegistryProduct
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (labeling : presentation.GlobalLabeling (S := S))
    (coefficient : ℤ) :
    boundaryCharacterPower
        𝒞.premodular.toFusionCategoryData automorphism
        (presentation.labelOf 𝒞.premodular labeling)
        geometry.punctureBoundary coefficient =
      ↑(∏ componentIndex,
        (𝒞.premodular.toFusionCategoryData.automorphismSimpleUnit
          automorphism (labeling componentIndex)) ^
          (signedMultiplicity
              (presentation.topology.formal.raw.components.get
                componentIndex).componentId
              geometry.punctureBoundary * coefficient) : Kˣ) := by
  rw [boundaryCharacterPower_eq_signedProduct]
  rw [signedProduct_eq_indexedProduct
    (value := fun componentId =>
      𝒞.premodular.toFusionCategoryData.automorphismSimpleUnit
        automorphism (presentation.labelOf 𝒞.premodular labeling componentId))
    (coefficient := coefficient)
    (indexOf := presentation.componentIndexing.indexOf)
    (idOf := fun componentIndex =>
      (presentation.topology.formal.raw.components.get
        componentIndex).componentId)
    (roundtrip := presentation.componentIndexing.index_roundtrip)
    (sound := presentation.componentIndexing.index_sound)
    (boundary := geometry.punctureBoundary)
    (allIndexed := geometry.puncture_ids_indexed_in_component_registry)]
  congr 1
  apply Finset.prod_congr rfl
  intro componentIndex _
  rw [presentation.labelOf_component
    𝒞.premodular labeling componentIndex]

end GeneratorGeometry

/--
Complete finite geometry denominator: one certificate for every evaluator
degree-three generator, with no two generators silently sharing one dotted
component and no raw dotted component silently omitted.
-/
structure GeometrySystem
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) where
  geometry :
    (generator : Fin presentation.topology.counts.turnedOver.h3) →
      GeneratorGeometry presentation generator
  generator_component_injective :
    Function.Injective
      (fun generator => (geometry generator).dottedComponentIndex)
  every_raw_dotted_component_covered :
    (componentIndex :
      Fin presentation.topology.formal.raw.components.length) →
    (presentation.topology.formal.raw.components.get componentIndex).role =
        .dotted →
      ∃ generator,
        (geometry generator).dottedComponentIndex = componentIndex

/-- Machine-visible result: exact certificate language, not its population. -/
def currentStatus : String :=
  "PASS_FAIL_CLOSED_DOTTED_GENERATOR_GEOMETRY_CERTIFICATE_LANGUAGE"

/-- Honest remaining obligation after defining the topology-side language. -/
def remainingScope : String :=
  "This module defines the category-neutral certificate language. The "
    ++ "finite-label evaluation compiler is proved in "
    ++ "DottedBoundaryFiniteSum and DottedBoundaryGeneratorInvariance; "
    ++ "automatic population from raw planar coordinates is not implemented. "
    ++ "The final modular theorem instead restricts its presentation domain "
    ++ "to StandardDottedCanonicalPresentation, where this certificate is "
    ++ "part of the accepted topology input."

end TwistedYetter.Kirby.DottedBoundaryGeometry
