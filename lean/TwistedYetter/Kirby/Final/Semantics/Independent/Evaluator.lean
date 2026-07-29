import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

/-!
# Independent semantics: role-aware THAM-side evaluator

The definition below starts from a finite combinatorial special Kirby
diagram.  It does not start from a knot in `S³`, and it does not reuse an
existing evaluator.

Ordinary and specially-dotted two-handle components are summed over the
simple labels.  Literal dotted one-handle components are never assigned an
ordinary Kirby-colour label: every dotted puncture is compiled using the
normalized tensor-unit projector.

The displayed diagram keeps ordinary Kirby-calculus names.  Before evaluating,
the handle decomposition is read upside down as in Tham, Definition 5.11:
primal one-handles are THAM three-handles, primal two-handles remain
two-handles, and primal three-handles are THAM one-handles.  Character
exponents therefore come only from `ThamTwoCycles`, never directly from a
primal representative.
-/

namespace TwistedYetter.Semantics.Independent

universe uK uC uS v

abbrev TwoHandleLabeling
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram) :=
  Fin diagram.handles.hTwo → 𝒞.simples.Simple

instance
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram) :
    Fintype (TwoHandleLabeling 𝒞 diagram) :=
  inferInstance

def ordinaryKirbyWeight
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {diagram : CombinatorialSpecialKirbyDiagram}
    (labeling : TwoHandleLabeling 𝒞 diagram) : K :=
  ∏ handle, 𝒞.simples.quantumDimension (labeling handle)

def characterWeight
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles turnedOver) : K :=
  ((∏ handle,
      (𝒞η.character.value (labeling handle)) ^ (cycle.1 handle)) : Kˣ)

/-!
The displayed formula stores the homological character exactly once, in
`characterWeight`.  A character coupon may be introduced later as a
graphical proof device when this scalar action is rewritten using Schur's
lemma and monoidal naturality; it is not inserted a second time by the
presentation compiler.
-/

/-- Convert the stored strand orientation to the graphical direction. -/
def ribbonDirectionOfStrandOrientation : StrandOrientation → RibbonDirection
  | .positive => .forward
  | .negative => .dual

/-- Convert the orientation of a dotted-disk puncture. -/
def ribbonDirectionOfPunctureDirection : PunctureDirection → RibbonDirection
  | .withDiskOrientation => .forward
  | .againstDiskOrientation => .dual

def ribbonCrossingSign : CrossingSign → RibbonCrossingSign
  | .positive => .positive
  | .negative => .negative

/--
Read the simple label carried by one strand of the cut-open exterior.

The fallback to the tensor unit is definitionally total but unreachable on
every active exterior word by
`CutOpenExteriorTrace.activeStrandsAreTwoHandles`.
-/
def exteriorStrandLabel
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strand : diagram.trace.StrandId) :
    𝒞.simples.Simple :=
  let component := (diagram.trace.strands strand).component
  if role : (diagram.trace.components component).role ≠ .dotted then
    labeling (diagram.handles.twoHandleIndex.symm ⟨component, role⟩)
  else
    𝒞.simples.tensorUnit

def orientedExteriorStrand
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strand : diagram.trace.StrandId) :
    OrientedSimple 𝒞 where
  label := exteriorStrandLabel 𝒞 diagram labeling strand
  direction :=
    ribbonDirectionOfStrandOrientation
      (diagram.trace.strands strand).orientation

def orientedPuncture
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    OrientedSimple 𝒞 where
  label :=
    labeling
      (diagram.handles.twoHandleIndex.symm
        ⟨puncture.twoHandleComponent, puncture.two_handle_role⟩)
  direction := ribbonDirectionOfPunctureDirection puncture.direction

def exteriorWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strands : List diagram.trace.StrandId) :
    RibbonWord 𝒞 :=
  strands.map (orientedExteriorStrand 𝒞 diagram labeling)

def punctureWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    RibbonWord 𝒞 :=
  punctures.map (orientedPuncture 𝒞 diagram labeling)

/-- Compile one exact cut-open event, before adding its exterior contexts. -/
def compileCutOpenEvent
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    CutOpenEvent diagram.trace → RibbonExpression 𝒞
  | .birth left right =>
      .generator (.cup
        (orientedExteriorStrand 𝒞 diagram labeling left)
        (orientedExteriorStrand 𝒞 diagram labeling right))
  | .death left right =>
      .generator (.cap
        (orientedExteriorStrand 𝒞 diagram labeling left)
        (orientedExteriorStrand 𝒞 diagram labeling right))
  | .crossing overStrand underStrand sign =>
      .generator (.crossing
        (orientedExteriorStrand 𝒞 diagram labeling overStrand)
        (orientedExteriorStrand 𝒞 diagram labeling underStrand)
        (ribbonCrossingSign sign))
  | .framingTwist strand sign =>
      .generator (.twist
        (orientedExteriorStrand 𝒞 diagram labeling strand)
        (ribbonCrossingSign sign))
  | .planarIsotopy word =>
      .generator (.identity
        (exteriorWord 𝒞 diagram labeling word))
  | .projectorHole _ punctures =>
      .generator (.tensorUnitProjector
        (punctureWord 𝒞 diagram labeling punctures))

/-- The chosen left exterior context of one certified event transition. -/
noncomputable def eventLeftContext
    (diagram : CombinatorialSpecialKirbyDiagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    List diagram.trace.StrandId :=
  Classical.choose
    (diagram.dottedCuts.exterior.transitionValid i)

/-- The chosen right exterior context of one certified event transition. -/
noncomputable def eventRightContext
    (diagram : CombinatorialSpecialKirbyDiagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    List diagram.trace.StrandId :=
  Classical.choose
    (Classical.choose_spec
      (diagram.dottedCuts.exterior.transitionValid i))

/-- Compile one event together with the exact common exterior context. -/
noncomputable def compileContextualCutOpenEvent
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    RibbonExpression 𝒞 :=
  .tensor
    (.generator (.identity
      (exteriorWord 𝒞 diagram labeling (eventLeftContext diagram i))))
    (.tensor
      (compileCutOpenEvent 𝒞 diagram labeling
        (diagram.dottedCuts.exterior.events i))
      (.generator (.identity
        (exteriorWord 𝒞 diagram labeling (eventRightContext diagram i)))))

/-- Compile the complete finite cut-open exterior trace in sweep order. -/
noncomputable def compileCutOpenExterior
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    RibbonExpression 𝒞 :=
  (List.ofFn fun i =>
      compileContextualCutOpenEvent 𝒞 diagram labeling i).foldl
    RibbonExpression.compose
    (.generator (.identity []))

/--
Fusion-channel resolutions belong to local graphical proofs, not to the
definition of the original closed link.  Therefore the canonical compiled
term is exactly one closed graph, with no auxiliary channel denominator.
-/
structure RoleAwareCompiledTerm
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (_primal : PrimalDegreeThreeBoundaryData diagram)
    (_turnedOver : TurnedOverBoundaryCertificate _primal)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (_cycle : ThamTwoCycles _turnedOver) where
  graph : RibbonExpression 𝒞η.category :=
    compileCutOpenExterior 𝒞η.category diagram labeling

noncomputable def canonicalRoleAwareGraphCompiler
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles turnedOver) :
    RoleAwareCompiledTerm 𝒞η diagram primal turnedOver labeling cycle :=
  {}

/--
Tham Definition 5.11 normalization on the turned-over handle decomposition.

The arguments use THAM indices.  Thus `hOne` is the number of primal
three-handles, and the unique primal four-handle contributes the numerator
`globalDimension`.  The value is exactly

`globalDimension / globalDimension ^ hOne`.

There is no caller-supplied normalization datum or opaque conformance
predicate.
-/
def thamDefinition511Normalization
    {K : Type uK} [Field K]
    (globalDimension : K)
    (hOne _hTwo _hThree : ℕ) : K :=
  globalDimension / globalDimension ^ hOne

noncomputable def evaluateCycle
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (cycle : ThamTwoCycles turnedOver) : K :=
  thamDefinition511Normalization
      𝒞η.category.simples.globalDimension
      diagram.handles.hThree
      diagram.handles.hTwo
      diagram.handles.hOne *
    ∑ labeling : TwoHandleLabeling 𝒞η.category diagram,
      ordinaryKirbyWeight 𝒞η.category labeling *
      characterWeight 𝒞η turnedOver labeling cycle *
      let term :=
        canonicalRoleAwareGraphCompiler
          𝒞η diagram primal turnedOver labeling cycle
      graphical.evaluate term.graph

/--
Representative independence is not baked into the definition.  It is the
precise obligation required before `evaluateCycle` descends to `ThamKirbyH₂`.
-/
def RepresentativeIndependenceStatement
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (turnedOver : TurnedOverBoundaryCertificate primal) : Prop :=
  ∀ left right : ThamTwoCycles turnedOver,
    thamCycleClass turnedOver left = thamCycleClass turnedOver right →
    evaluateCycle 𝒞η graphical
        diagram primal turnedOver left =
      evaluateCycle 𝒞η graphical
        diagram primal turnedOver right

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 3253
