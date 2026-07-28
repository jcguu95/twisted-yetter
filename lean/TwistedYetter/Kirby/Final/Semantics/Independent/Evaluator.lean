import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

/-!
# Independent semantics: role-aware evaluator

The definition below starts from a finite combinatorial special Kirby
diagram.  It does not start from a knot in `S³`, and it does not reuse an
existing evaluator.

Ordinary and specially-dotted two-handle components are summed over the
simple labels.  Literal dotted one-handle components are never assigned an
ordinary Kirby-colour label: every dotted puncture is compiled using the
normalized tensor-unit projector.
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
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : TwoCycles diagram) : K :=
  ((∏ handle,
      (𝒞η.character.value (labeling handle)) ^ (cycle.1 handle)) : Kˣ)

/--
A compiled term retains all finite auxiliary fusion-channel choices.  This
prevents an evaluator from silently replacing a multiplicity sum by one
preferred channel.
-/
structure RoleAwareCompiledTerm
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : TwoCycles diagram) where
  ChannelChoice : Type
  channelChoiceFintype : Fintype ChannelChoice
  graph : ChannelChoice → RibbonExpression 𝒞η.category
  coefficient : ChannelChoice → K
  ordinaryComponentsUseAssignedSimpleLabels : Prop
  dottedComponentsUseNormalizedTensorUnitProjector : Prop
  characterCouponsUseCycleCoordinates : Prop
  punctureDirectionsDetermineExponentSigns : Prop
  everyFusionMultiplicityIsSummed : Prop
  ordinaryComponentsUseAssignedSimpleLabels_holds :
    ordinaryComponentsUseAssignedSimpleLabels
  dottedComponentsUseNormalizedTensorUnitProjector_holds :
    dottedComponentsUseNormalizedTensorUnitProjector
  characterCouponsUseCycleCoordinates_holds :
    characterCouponsUseCycleCoordinates
  punctureDirectionsDetermineExponentSigns_holds :
    punctureDirectionsDetermineExponentSigns
  everyFusionMultiplicityIsSummed_holds :
    everyFusionMultiplicityIsSummed

attribute [instance] RoleAwareCompiledTerm.channelChoiceFintype

/--
The independent compiler contract.  It is intentionally a theorem obligation
for later implementation comparison; no existing compiler is imported here.
-/
structure RoleAwareGraphCompiler
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K) where
  compile :
    (diagram : CombinatorialSpecialKirbyDiagram) →
    (labeling : TwoHandleLabeling 𝒞η.category diagram) →
    (cycle : TwoCycles diagram) →
      RoleAwareCompiledTerm 𝒞η diagram labeling cycle

/--
The handle normalization is isolated because its exact power is a convention
from Tham, Definition 5.11.  It is a function of the special handle counts
only and cannot inspect labels, characters, or the compiled graph.
-/
structure ThamDefinition511Normalization
    (K : Type uK) [Field K] where
  value :
    (globalDimension : K) →
    (hOne hTwo hThree : ℕ) →
    K
  dependsOnlyOnDisplayedArguments : Prop
  followsDefinition511DualHandleConvention : Prop
  dependsOnlyOnDisplayedArguments_holds :
    dependsOnlyOnDisplayedArguments
  followsDefinition511DualHandleConvention_holds :
    followsDefinition511DualHandleConvention

def evaluateCycle
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (cycle : TwoCycles diagram) : K :=
  normalization.value
      𝒞η.category.simples.globalDimension
      diagram.handles.hOne
      diagram.handles.hTwo
      diagram.handles.hThree *
    ∑ labeling : TwoHandleLabeling 𝒞η.category diagram,
      ordinaryKirbyWeight 𝒞η.category labeling *
      characterWeight 𝒞η labeling cycle *
      let term := compiler.compile diagram labeling cycle
      ∑ channel : term.ChannelChoice,
        term.coefficient channel * graphical.evaluate (term.graph channel)

/--
Representative independence is not baked into the definition.  It is the
precise obligation required before `evaluateCycle` descends to `KirbyH₂`.
-/
def RepresentativeIndependenceStatement
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (degreeThree : DegreeThreeBoundaryData diagram) : Prop :=
  ∀ left right : TwoCycles diagram,
    cycleClass degreeThree left = cycleClass degreeThree right →
    evaluateCycle 𝒞η graphical compiler normalization diagram left =
      evaluateCycle 𝒞η graphical compiler normalization diagram right

end TwistedYetter.Semantics.Independent
