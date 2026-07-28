import TwistedYetter.Kirby.Final.Semantics.IndependentGraphicalCalculusSpecification
import TwistedYetter.Kirby.Final.Semantics.IndependentHomologyMarkingSpecification
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators

/-!
# Independent human specification of the role-aware evaluator

This file is normative.  It was written from the human formula and Tham,
Definition 5.11, without importing or inspecting this repository's evaluator,
Sage implementation, compatibility bridge, or numerical artifacts.

Reference:

* Ying Hong Tham, *On the Category of Boundary Values in the extended
  Crane-Yetter TQFT* (2021), Definition 5.11, thesis page 52 (PDF page 58).

Tham writes

`D = ∑ i : Irr(𝒞), dᵢ²`.

For the dual reading of a primal special Kirby diagram:

* each ordinary primal 2-handle receives the regular colour;
* each dotted primal 1-handle is cut and only the tensor-unit summand is
  retained;
* primal 3-handles contribute `D⁻¹`;
* the unique primal 4-handle contributes `D`;
* the resulting closed typed ribbon diagram is evaluated in `S³`.

This file does not contain a second handle complex or a second presentation
type.  Its topological input is exactly `SpecialKirbyDiagram`; its marking is
exactly an element of `KirbyH₂ = ker(∂₂)/im(∂₃)`.
-/

namespace TwistedYetter.Kirby.Final.IndependentEvaluatorSpecification

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open IndependentAlgebraicInput
open IndependentPresentationSpecification
open IndependentHomologyMarkingSpecification
open IndependentGraphicalCalculusSpecification

universe
  uK uC vC
  uKnot uFramed uDisk uPoint uBunching uThreeManifold

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

variable
  {geometry : KirbyGeometrySemantics}

/--
The categorical graphical data needed to interpret the formula.

All scalar evaluation factors through a typed closed ribbon diagram and an
endomorphism of the tensor unit.  There is no arbitrary
`expanded term → K` evaluator.
-/
structure EvaluatorGraphicalData
    (𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)) where
  interpretation :
    RibbonDiagramInterpretation 𝒞.ribbon
  graphicalRelations :
    GraphicalRelationSoundness interpretation
  fusionResolution :
    FusionResolutionSemantics 𝒞.fusion
  closedScalar :
    ClosedRibbonScalarSemantics 𝒞.fusion interpretation

/-- The standard closed pivotal loop used to define quantum dimension. -/
def simpleClosedLoop (X : C) :
    RibbonDiagram ([] : TensorWord (C := C)) [] :=
  .compose (.leftCoevaluation X) (.rightEvaluation X)

/--
The quantum dimension is not an independent scalar table.  It is the scalar
of the standard closed simple loop in the fixed ribbon graphical semantics.
-/
noncomputable def quantumDimension
    {𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)}
    (graphical : EvaluatorGraphicalData 𝒞)
    (s : S) : K :=
  graphical.closedScalar.scalar
    (simpleClosedLoop (𝒞.fusion.simple s))

/--
Tham's `D`: the sum of squared quantum dimensions, not its square root.
-/
noncomputable def categoryDimension
    {𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)}
    (graphical : EvaluatorGraphicalData 𝒞) : K :=
  ∑ s, quantumDimension graphical s * quantumDimension graphical s

/--
The one scalar nondegeneracy input needed by the normalization.

It is stated separately so that no reciprocal of `D` is silently formed when
`D = 0`.
-/
structure NormalizationData
    {𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)}
    (graphical : EvaluatorGraphicalData 𝒞) where
  categoryDimension_ne_zero :
    categoryDimension graphical ≠ 0

/-- The natural-number power of an endomorphism, using categorical composition. -/
def endomorphismNatPower
    {X : C}
    (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => endomorphismNatPower f n ≫ f

/--
The integer power of the character coupon.

Positive powers use the forward natural isomorphism; negative powers use its
inverse.  Exponent zero is the identity endomorphism.
-/
def characterPower
    (η : TensorIdentityCharacterSemantics (C := C))
    (X : C) : ℤ → (X ⟶ X)
  | .ofNat n => endomorphismNatPower (η.iso.hom.app X) n
  | .negSucc n => endomorphismNatPower (η.iso.inv.app X) (n + 1)

/--
An auxiliary coordinate extraction associated with one handle coordinate
chart.

`coordinates` means the coefficients of a 2-chain in the individually
chosen generators of the ordinary 2-handle orientation lines.  It is not an
arbitrary `GL(h₂, ℤ)` coordinate system.
-/
structure TwoHandleCoordinateExtraction
    (diagram : SpecialKirbyDiagram geometry)
    (chart : HandleCoordinateChart diagram) where
  coordinates :
    diagram.handleBoundary.twoChains.carrier →
      (Fin diagram.geometric.hTwo → ℤ)
  additive :
    ∀ a b,
      coordinates (a + b) = coordinates a + coordinates b
  zero :
    coordinates 0 = 0

/--
The narrow coordinate-free meaning of the extraction.

It says that `coordinates` is obtained by:

1. decomposing `C₂` into the individually indexed handle lines;
2. applying exactly the generator selected by `chart` on each line.

This contains no category or evaluator equality.
-/
axiom CoordinatesRealizeHandleChart
    {diagram : SpecialKirbyDiagram geometry}
    (chart : HandleCoordinateChart diagram)
    (extraction : TwoHandleCoordinateExtraction diagram chart) :
    Prop

/--
Local strand directions at every recorded puncture of every dotted disk.

The direction is auxiliary because the public Kirby diagram has no component
orientations.
-/
structure DottedPunctureDirections
    (diagram : SpecialKirbyDiagram geometry) where
  direction :
    (i : Fin diagram.geometric.hOne) →
      DottedPuncture geometry diagram.geometric.hTwo →
      StrandDirection

/--
The puncture directions agree with the temporary handle orientations.

Equivalently, after choosing the chart generators, the signed count of the
punctures of ordinary component `j` through dotted disk `i` is the `(i,j)`
coefficient of `∂₂`.

This is a topology/coordinate statement.  It contains no category or
evaluation equality.
-/
axiom PunctureDirectionsAgreeWithHandleChart
    {diagram : SpecialKirbyDiagram geometry}
    (chart : HandleCoordinateChart diagram)
    (directions : DottedPunctureDirections diagram) :
    Prop

/-- Convert one recorded puncture to the directed simple object it carries. -/
def directedPunctureObject
    {diagram : SpecialKirbyDiagram geometry}
    {𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)}
    (directions : DottedPunctureDirections diagram)
    (label : Fin diagram.geometric.hTwo → S)
    (i : Fin diagram.geometric.hOne)
    (puncture : DottedPuncture geometry diagram.geometric.hTwo) :
    DirectedObject (C := C) :=
  { object := 𝒞.fusion.simple (label puncture.ordinaryComponent)
    direction := directions.direction i puncture }

/-- The exact directed tensor word exposed by one dotted spanning disk. -/
def dottedTensorWord
    {diagram : SpecialKirbyDiagram geometry}
    {𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)}
    (directions : DottedPunctureDirections diagram)
    (label : Fin diagram.geometric.hTwo → S)
    (i : Fin diagram.geometric.hOne) :
    TensorWord (C := C) :=
  (diagram.geometric.dottedDisk i).punctures.map
    (directedPunctureObject
      (𝒞 := 𝒞)
      directions
      label
      i)

/--
All auxiliary choices required to turn a marked diagram into one expanded
cycle-level formula.

The public marking remains `α`.  `representative`, `chart`, coordinate
extraction, and puncture directions are temporary witnesses whose
independence must later be proved.
-/
structure EvaluationAuxiliaryChoice
    (diagram : SpecialKirbyDiagram geometry)
    (α : KirbyH₂ diagram) where
  representative :
    CycleRepresentative α
  chart :
    HandleCoordinateChart diagram
  coordinateExtraction :
    TwoHandleCoordinateExtraction diagram chart
  coordinateExtraction_is_chart :
    CoordinatesRealizeHandleChart chart coordinateExtraction
  punctureDirections :
    DottedPunctureDirections diagram
  punctureDirections_are_chart :
    PunctureDirectionsAgreeWithHandleChart chart punctureDirections

/-- The integer character exponent on ordinary component `j`. -/
def EvaluationAuxiliaryChoice.exponent
    {diagram : SpecialKirbyDiagram geometry}
    {α : KirbyH₂ diagram}
    (choice : EvaluationAuxiliaryChoice diagram α)
    (j : Fin diagram.geometric.hTwo) : ℤ :=
  choice.coordinateExtraction.coordinates
    choice.representative.cycle.chain
    j

/--
The complete algebraic instructions for one ordinary-label assignment.

Every ordinary component carries its simple object and the character coupon
with the exponent extracted from the chosen representative.  Every dotted
component carries the exact directed puncture word and its tensor-unit
projector.
-/
structure RoleAwareExpansion
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (α : KirbyH₂ diagram)
    (choice : EvaluationAuxiliaryChoice diagram α)
    (label : Fin diagram.geometric.hTwo → S) where
  ordinaryObject :
    Fin diagram.geometric.hTwo → C :=
      fun j => 𝒞η.1.fusion.simple (label j)
  ordinaryCharacterCoupon :
    (j : Fin diagram.geometric.hTwo) →
      ordinaryObject j ⟶ ordinaryObject j :=
        fun j =>
          characterPower 𝒞η.2 (ordinaryObject j) (choice.exponent j)
  dottedWord :
    Fin diagram.geometric.hOne → TensorWord (C := C) :=
      dottedTensorWord
        (𝒞 := 𝒞η.1)
        choice.punctureDirections
        label
  dottedUnitProjector :
    (i : Fin diagram.geometric.hOne) →
      (dottedWord i).value ⟶ (dottedWord i).value :=
        fun i =>
          tensorUnitProjector
            graphical.fusionResolution
            (dottedWord i).value

/--
Literal topology-to-syntax obligations for an assembly function.

These six predicates are deliberately separate audit points.  None returns a
scalar or states an equality of evaluations.
-/
axiom OrdinaryComponentsRenderedExactly
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assemble :
      {α : KirbyH₂ diagram} →
        (choice : EvaluationAuxiliaryChoice diagram α) →
        (label : Fin diagram.geometric.hTwo → S) →
        RoleAwareExpansion 𝒞η graphical diagram α choice label →
        RibbonDiagram ([] : TensorWord (C := C)) []) :
    Prop

axiom CharacterCouponsRenderedExactly
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assemble :
      {α : KirbyH₂ diagram} →
        (choice : EvaluationAuxiliaryChoice diagram α) →
        (label : Fin diagram.geometric.hTwo → S) →
        RoleAwareExpansion 𝒞η graphical diagram α choice label →
        RibbonDiagram ([] : TensorWord (C := C)) []) :
    Prop

axiom DottedComponentsRemovedAsOrdinaryCircles
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assemble :
      {α : KirbyH₂ diagram} →
        (choice : EvaluationAuxiliaryChoice diagram α) →
        (label : Fin diagram.geometric.hTwo → S) →
        RoleAwareExpansion 𝒞η graphical diagram α choice label →
        RibbonDiagram ([] : TensorWord (C := C)) []) :
    Prop

axiom TensorUnitCutsRenderedExactly
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assemble :
      {α : KirbyH₂ diagram} →
        (choice : EvaluationAuxiliaryChoice diagram α) →
        (label : Fin diagram.geometric.hTwo → S) →
        RoleAwareExpansion 𝒞η graphical diagram α choice label →
        RibbonDiagram ([] : TensorWord (C := C)) []) :
    Prop

axiom ExteriorRibbonDataPreserved
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assemble :
      {α : KirbyH₂ diagram} →
        (choice : EvaluationAuxiliaryChoice diagram α) →
        (label : Fin diagram.geometric.hTwo → S) →
        RoleAwareExpansion 𝒞η graphical diagram α choice label →
        RibbonDiagram ([] : TensorWord (C := C)) []) :
    Prop

axiom NoExtraProjectorOrModularKilling
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assemble :
      {α : KirbyH₂ diagram} →
        (choice : EvaluationAuxiliaryChoice diagram α) →
        (label : Fin diagram.geometric.hTwo → S) →
        RoleAwareExpansion 𝒞η graphical diagram α choice label →
        RibbonDiagram ([] : TensorWord (C := C)) []) :
    Prop

/--
The topology-to-typed-graph translation for the fully expanded summand.

It must use the ordinary framed link and its framings, insert exactly the
listed character coupons, cut every chosen dotted disk simultaneously, and
insert exactly the listed tensor-unit projectors.  It may insert only the
associators, unitors, braidings, cups, caps, twists, and general coupons of
the independent graphical language.

This is a diagram-construction boundary, not an evaluator and not an
equality of scalars.
-/
structure RoleAwareClosedDiagramAssembly
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry) where
  assemble :
    {α : KirbyH₂ diagram} →
      (choice : EvaluationAuxiliaryChoice diagram α) →
      (label : Fin diagram.geometric.hTwo → S) →
      RoleAwareExpansion 𝒞η graphical diagram α choice label →
      RibbonDiagram ([] : TensorWord (C := C)) []

  ordinaryComponents :
    OrdinaryComponentsRenderedExactly
      𝒞η graphical diagram assemble
  characterCoupons :
    CharacterCouponsRenderedExactly
      𝒞η graphical diagram assemble
  dottedComponentsAreNotOrdinaryCircles :
    DottedComponentsRemovedAsOrdinaryCircles
      𝒞η graphical diagram assemble
  tensorUnitCuts :
    TensorUnitCutsRenderedExactly
      𝒞η graphical diagram assemble
  exteriorPreserved :
    ExteriorRibbonDataPreserved
      𝒞η graphical diagram assemble
  noExtraProjectorOrKilling :
    NoExtraProjectorOrModularKilling
      𝒞η graphical diagram assemble

/-- Construct the expansion data for one ordinary-label assignment. -/
noncomputable def roleAwareExpansion
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (α : KirbyH₂ diagram)
    (choice : EvaluationAuxiliaryChoice diagram α)
    (label : Fin diagram.geometric.hTwo → S) :
    RoleAwareExpansion 𝒞η graphical diagram α choice label :=
  {}

/--
The raw finite sum.

Only ordinary 2-handles are summed over simple labels and weighted by their
quantum dimensions.  Dotted 1-handles never enter this denominator.
-/
noncomputable def rawCycleEvaluation
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assembly : RoleAwareClosedDiagramAssembly 𝒞η graphical diagram)
    (α : KirbyH₂ diagram)
    (choice : EvaluationAuxiliaryChoice diagram α) : K :=
  ∑ label : Fin diagram.geometric.hTwo → S,
    (∏ j, quantumDimension graphical (label j)) *
      graphical.closedScalar.scalar
        (assembly.assemble
          choice
          label
          (roleAwareExpansion
            𝒞η graphical diagram α choice label))

/--
Tham Definition 5.11 read on the dual handle decomposition.

The unique primal 4-handle contributes `D`; every primal 3-handle contributes
`D⁻¹`.  Therefore the factor is exactly `D^(1-h₃)`.
-/
noncomputable def dualHandleNormalization
    {𝒞 : PremodularCategorySemantics (K := K) (C := C) (S := S)}
    (graphical : EvaluatorGraphicalData 𝒞)
    (diagram : SpecialKirbyDiagram geometry) : K :=
  categoryDimension graphical /
    categoryDimension graphical ^ diagram.geometric.hThree

/-- The fully specified cycle-level expression for one auxiliary choice. -/
noncomputable def cycleEvaluation
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assembly : RoleAwareClosedDiagramAssembly 𝒞η graphical diagram)
    (α : KirbyH₂ diagram)
    (choice : EvaluationAuxiliaryChoice diagram α) : K :=
  dualHandleNormalization graphical diagram *
    rawCycleEvaluation 𝒞η graphical diagram assembly α choice

/--
The exact descent obligation before the formula defines a function of
`(diagram, α)`.

It simultaneously includes:

* independence of the cycle representative of `α`;
* independence of each temporary handle-line generator;
* independence of compatible puncture directions;
* independence of the concrete coordinate extraction realizing the chart.
-/
def AuxiliaryChoiceIndependent
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assembly : RoleAwareClosedDiagramAssembly 𝒞η graphical diagram) :
    Prop :=
  ∀ (α : KirbyH₂ diagram)
    (first second : EvaluationAuxiliaryChoice diagram α),
    cycleEvaluation 𝒞η graphical diagram assembly α first =
      cycleEvaluation 𝒞η graphical diagram assembly α second

/--
The diagram-level function exists only after the auxiliary-choice
independence theorem is supplied.

This structure is a specification target, not an axiom asserting that the
proof has already been completed.
-/
structure DiagramLevelTwistedYetter
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (diagram : SpecialKirbyDiagram geometry)
    (assembly : RoleAwareClosedDiagramAssembly 𝒞η graphical diagram) where
  auxiliaryChoiceIndependent :
    AuxiliaryChoiceIndependent 𝒞η graphical diagram assembly
  evaluate :
    KirbyH₂ diagram → K
  evaluate_agrees_with_formula :
    ∀ (α : KirbyH₂ diagram)
      (choice : EvaluationAuxiliaryChoice diagram α),
      evaluate α =
        cycleEvaluation 𝒞η graphical diagram assembly α choice

end TwistedYetter.Kirby.Final.IndependentEvaluatorSpecification
