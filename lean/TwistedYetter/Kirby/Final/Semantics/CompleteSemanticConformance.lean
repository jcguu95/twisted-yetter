import TwistedYetter.Kirby.Final.Semantics.Independent.Entry
import TwistedYetter.Kirby.Final.Semantics.ClosingHandleImplementationBridge
import TwistedYetter.Kirby.RoleAwarePresentationEvaluation

/-!
# Complete frozen-semantics conformance gate

This file is the one-way gate from the current implementation to the frozen
normative semantics.  The frozen files are not modified.

The gate deliberately does not accept the final evaluator equality as a
field.  It accepts only:

* an exact source binding;
* a comparison of the two algebraic inputs;
* an exact reindexing of the finite label denominator;
* equality of the scalar normalization;
* primitive data forcing each label-sector weight; and
* equality of each label-sector graphical term.

The complete evaluator equality is then proved by finite-sum reindexing.
-/

namespace TwistedYetter.Kirby.Final.CompleteSemanticConformance

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.Final.ClosingHandleImplementationBridge
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Semantics.Independent

universe uK uC vC uH uD uIso uSlide uP

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {H2 : Type uH} [AddCommGroup H2]

/--
One proof-bearing source shared by the frozen diagram and the current
evaluator.

The equality is intentionally about the complete formal presentation, not an
alias, hash, family name, or component count.
-/
structure ExactSourceBinding
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (current : Presentation H2) where
  certifiedClosed :
    CertifiedClosedDottedPresentation semantics
  formal_eq :
    certifiedClosed.dotted.formal =
      current.canonicalPresentation.topology.formal
  primalBoundary :
    PrimalDegreeThreeBoundaryData certifiedClosed.toCombinatorialSpecialKirbyDiagram
  turnedOver :
    TurnedOverBoundaryCertificate primalBoundary
  turnover :
    TurnoverH₂Identification turnedOver
  /--
  The frozen THAM-side quotient and the current certified dual handle complex
  compute the same turned-over second homology.  This is topology data, not an
  evaluator equality.
  -/
  thamToCurrentH₂ :
    ThamKirbyH₂ turnedOver ≃+
      current.canonicalPresentation.topology.handleChain.SecondHomology

namespace ExactSourceBinding

noncomputable def frozenDiagram
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    (source : ExactSourceBinding semantics current) :
    CombinatorialSpecialKirbyDiagram :=
  source.certifiedClosed.toCombinatorialSpecialKirbyDiagram

end ExactSourceBinding

/--
The only freely chosen marking is the primal frozen class.  Its evaluator-side
class is forced through the source's turnover identification and the exact
comparison with the current certified dual complex.
-/
structure MarkingBinding
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    (source : ExactSourceBinding semantics current) where
  frozenAlpha : PrimalKirbyH₂ source.primalBoundary

namespace MarkingBinding

noncomputable def currentAlpha
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    (marking : MarkingBinding source) :
    current.canonicalPresentation.topology.handleChain.SecondHomology :=
  source.thamToCurrentH₂
    (source.turnover.equiv marking.frozenAlpha)

noncomputable def frozenThamCycle
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    (marking : MarkingBinding source) :
    ThamTwoCycles source.turnedOver :=
  Quotient.out (source.turnover.equiv marking.frozenAlpha)

noncomputable def currentCycle
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    (marking : MarkingBinding source) :
    current.canonicalPresentation.DegreeTwoCycle :=
  current.canonicalPresentation.chosenCycle marking.currentAlpha

theorem currentAlpha_is_exact_turnedOver_marking
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    (marking : MarkingBinding source) :
    marking.currentAlpha =
      source.thamToCurrentH₂
        (source.turnover.equiv marking.frozenAlpha) :=
  rfl

end MarkingBinding

/--
Primitive algebraic agreement between a frozen category/character and the
current categorical implementation.

These fields compare the finite simple skeleton.  They do not mention a Kirby
diagram or an evaluator value.
-/
structure AlgebraBinding
    (frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K)
    (currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S))
    (currentCharacter : TensorIdentityAutomorphism C) where
  simpleEquiv : frozen.category.simples.Simple ≃ S
  tensorUnit_sound :
    simpleEquiv frozen.category.simples.tensorUnit =
      currentCategory.toFusionCategoryData.unitIndex
  dual_sound :
    ∀ simple,
      simpleEquiv (frozen.category.simples.dual simple) =
        currentCategory.toFusionCategoryData.dualIndex (simpleEquiv simple)
  fusionMultiplicity_sound :
    ∀ left right output,
      frozen.category.simples.fusionMultiplicity left right output =
        currentCategory.toFusionCategoryData.fusionMultiplicity
          (simpleEquiv left) (simpleEquiv right) (simpleEquiv output)
  quantumDimension_sound :
    ∀ simple,
      frozen.category.simples.quantumDimension simple =
        currentCategory.quantumDimension (simpleEquiv simple)
  globalDimension_sound :
    frozen.category.simples.globalDimension =
      currentCategory.globalDimension
  character_sound :
    ∀ simple,
      frozen.character.value simple =
        currentCategory.toFusionCategoryData.automorphismSimpleUnit
          currentCharacter (simpleEquiv simple)

/-- One frozen outer summand before normalization. -/
def frozenSummand
    (frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation frozen.category)
    (compiler : RoleAwareGraphCompiler frozen)
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (cycle : ThamTwoCycles turnedOver)
    (labeling : TwoHandleLabeling frozen.category diagram) : K :=
  ordinaryKirbyWeight frozen.category labeling *
    characterWeight frozen turnedOver labeling cycle *
    let term := compiler.compile diagram primal turnedOver labeling cycle
    ∑ channel : term.ChannelChoice,
      term.coefficient channel * graphical.evaluate (term.graph channel)

/--
The exact finite comparison data required from an implementation.

There is deliberately no field whose type is the final evaluator equality.
The two local equalities expose separately:

* the Kirby/character coefficient; and
* the graphical/fusion-channel value.
-/
structure EvaluatorBinding
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    (source : ExactSourceBinding semantics current)
    (marking : MarkingBinding source)
    (frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation frozen.category)
    (compiler : RoleAwareGraphCompiler frozen)
    (normalization : ThamDefinition511Normalization K)
    (currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S))
    (currentCharacter : TensorIdentityAutomorphism C) where
  algebra :
    AlgebraBinding frozen currentCategory currentCharacter
  handleEquiv :
    Fin source.frozenDiagram.handles.hTwo ≃
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryComponentIndex
        current.canonicalPresentation
  handle_component_sound :
    ∀ handle,
      source.certifiedClosed.dotted.indexing.componentName
          (source.frozenDiagram.handles.twoHandleIndex handle).1 =
        (current.canonicalPresentation.topology.formal.raw.components.get
          (handleEquiv handle).1).componentId
  cycle_coordinate_sound :
    ∀ handle,
      marking.frozenThamCycle.1 handle =
        current.canonicalPresentation.cycleComponentExponent
          marking.currentCycle
          (current.canonicalPresentation.topology.formal.raw.components.get
            (handleEquiv handle).1)
  normalization_sound :
    normalization.value
        frozen.category.simples.globalDimension
        source.frozenDiagram.handles.hThree
        source.frozenDiagram.handles.hTwo
        source.frozenDiagram.handles.hOne =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareNormalizationFactor
        currentCategory current.canonicalPresentation
  graphicalTerm_sound :
    ∀ labeling : TwoHandleLabeling frozen.category source.frozenDiagram,
      let currentLabeling :
          RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
            (S := S) current.canonicalPresentation :=
        fun currentHandle =>
          algebra.simpleEquiv (labeling (handleEquiv.symm currentHandle))
      let term :=
        compiler.compile source.frozenDiagram source.primalBoundary
          source.turnedOver labeling marking.frozenThamCycle
      (∑ channel : term.ChannelChoice,
          term.coefficient channel *
            graphical.evaluate (term.graph channel)) =
        currentCategory.toFusionCategoryData.closedScalar
          (TwistedYetter.Kirby.CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
              currentCategory currentCharacter current.canonicalPresentation
              current.simultaneousGeometry currentLabeling))

namespace EvaluatorBinding

/-- Reindex the complete frozen labeling denominator into the current one. -/
def labelingEquiv
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    {marking : MarkingBinding source}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (binding :
      EvaluatorBinding source marking frozen graphical compiler normalization
        currentCategory currentCharacter) :
    TwoHandleLabeling frozen.category source.frozenDiagram ≃
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) current.canonicalPresentation where
  toFun := fun labeling currentHandle =>
    binding.algebra.simpleEquiv
      (labeling (binding.handleEquiv.symm currentHandle))
  invFun := fun labeling frozenHandle =>
    binding.algebra.simpleEquiv.symm
      (labeling (binding.handleEquiv frozenHandle))
  left_inv := by
    intro labeling
    funext handle
    simp
  right_inv := by
    intro labeling
    funext handle
    simp

/--
The visible coefficient comparison required before the final finite sum may
be reindexed.

This is intentionally a named theorem obligation rather than a field in
`EvaluatorBinding`: it must be proved from the simple, handle, and cycle
coordinate equations above.
-/
def WeightConformance
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    {marking : MarkingBinding source}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (binding :
      EvaluatorBinding source marking frozen graphical compiler normalization
        currentCategory currentCharacter) : Prop :=
  ∀ labeling : TwoHandleLabeling frozen.category source.frozenDiagram,
    ordinaryKirbyWeight frozen.category labeling *
        characterWeight frozen source.turnedOver labeling
          marking.frozenThamCycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
        currentCategory currentCharacter current.canonicalPresentation
        marking.currentCycle (binding.labelingEquiv labeling)

/--
The finite coefficient obligation is forced by the primitive algebra, handle,
and cycle-coordinate bindings; it is not an additional assumption.
-/
theorem weightConformance_of_primitive_bindings
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    {marking : MarkingBinding source}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (binding :
      EvaluatorBinding source marking frozen graphical compiler normalization
        currentCategory currentCharacter) :
    binding.WeightConformance := by
  classical
  intro labeling
  unfold ordinaryKirbyWeight characterWeight
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
  rw [Units.coe_prod]
  change
    (∏ handle,
        frozen.category.simples.quantumDimension (labeling handle)) *
        (∏ handle,
          (((frozen.character.value (labeling handle)) ^
            (marking.frozenThamCycle.1 handle) : Kˣ) : K)) =
      ∏ currentHandle,
        current.canonicalPresentation.cycleComponentWeight
          currentCategory currentCharacter marking.currentCycle
          (current.canonicalPresentation.topology.formal.raw.components.get
            currentHandle.1)
          (binding.labelingEquiv labeling currentHandle)
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_equiv binding.handleEquiv
  intro handle
  dsimp [EvaluatorBinding.labelingEquiv]
  rw [Equiv.symm_apply_apply]
  unfold
    CanonicalModularKirbyEvaluator.CanonicalPresentation.cycleComponentWeight
    FusionCategoryData.automorphismScalarPower
  change
    frozen.category.simples.quantumDimension (labeling handle) *
        (((frozen.character.value (labeling handle)) ^
          (marking.frozenThamCycle.1 handle) : Kˣ) : K) =
      currentCategory.quantumDimension
          (binding.algebra.simpleEquiv (labeling handle)) *
        (((currentCategory.toFusionCategoryData.automorphismSimpleUnit
            currentCharacter
            (binding.algebra.simpleEquiv (labeling handle))) ^
          (current.canonicalPresentation.cycleComponentExponent
            marking.currentCycle
            (current.canonicalPresentation.topology.formal.raw.components.get
              (binding.handleEquiv handle).1)) : Kˣ) : K)
  rw [
    binding.algebra.quantumDimension_sound,
    binding.algebra.character_sound,
    binding.cycle_coordinate_sound
  ]

/--
If every primitive binding is proved, the current evaluator is forced to
equal the frozen evaluator.  The conclusion is not an input field.
-/
theorem roleAwareCycleEval_eq_frozenEvaluateCycle
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {source : ExactSourceBinding semantics current}
    {marking : MarkingBinding source}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (binding :
      EvaluatorBinding source marking frozen graphical compiler normalization
        currentCategory currentCharacter) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        currentCategory currentCharacter current.canonicalPresentation
        current.simultaneousGeometry marking.currentCycle =
      evaluateCycle frozen graphical compiler normalization
        source.frozenDiagram source.primalBoundary source.turnedOver
          marking.frozenThamCycle := by
  classical
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
    evaluateCycle
  rw [
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareRawNumerator_eq_sum_roleAwareSummand
  ]
  rw [binding.normalization_sound]
  congr 1
  symm
  apply Fintype.sum_equiv binding.labelingEquiv
  intro labeling
  conv_lhs =>
    congr
    · exact binding.weightConformance_of_primitive_bindings labeling
  rw [binding.graphicalTerm_sound labeling]
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareSummand
  rfl

end EvaluatorBinding

/--
A proof-bearing admission certificate for one current evaluator case.

The certificate contains only primitive source, marking, algebra, coordinate,
normalization, and graphical-term bindings.  It cannot store the final
evaluator equality: that equality is derived by
`FrozenConformanceCertificate.sound`.
-/
structure FrozenConformanceCertificate
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (current : Presentation H2)
    (frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation frozen.category)
    (compiler : RoleAwareGraphCompiler frozen)
    (normalization : ThamDefinition511Normalization K)
    (currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S))
    (currentCharacter : TensorIdentityAutomorphism C) where
  source : ExactSourceBinding semantics current
  marking : MarkingBinding source
  binding :
    EvaluatorBinding source marking frozen graphical compiler normalization
      currentCategory currentCharacter

namespace FrozenConformanceCertificate

/--
The only formal-admission token for one current evaluator case is the
complete primitive certificate itself.  There is no second wrapper containing
a Boolean, status string, hash, or pre-written evaluator equality.
-/
abbrev FormalAdmission
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    :=
  FrozenConformanceCertificate semantics current frozen graphical compiler
    normalization currentCategory currentCharacter

/--
Every complete primitive certificate is definitionally a formal-admission
token.
-/
def formalAdmission
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (certificate :
      FrozenConformanceCertificate semantics current frozen graphical compiler
        normalization currentCategory currentCharacter) :
    FormalAdmission (semantics := semantics) (current := current)
      (frozen := frozen) (graphical := graphical) (compiler := compiler)
      (normalization := normalization) (currentCategory := currentCategory)
      (currentCharacter := currentCharacter) :=
  certificate

/--
The admitted current value is definitionally the current role-aware
evaluator, not a separately supplied scalar.
-/
noncomputable def currentValue
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (certificate :
      FrozenConformanceCertificate semantics current frozen graphical compiler
        normalization currentCategory currentCharacter) : K :=
  RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
    currentCategory currentCharacter current.canonicalPresentation
    current.simultaneousGeometry certificate.marking.currentCycle

/--
The normative value is definitionally the frozen evaluator applied to the
same proof-bound source and marking.
-/
noncomputable def frozenValue
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (certificate :
      FrozenConformanceCertificate semantics current frozen graphical compiler
        normalization currentCategory currentCharacter) : K :=
  evaluateCycle frozen graphical compiler normalization
    certificate.source.frozenDiagram certificate.source.primalBoundary
      certificate.source.turnedOver certificate.marking.frozenThamCycle

/--
Kernel-checked semantic soundness of every admitted evaluator case.
-/
theorem sound
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {current : Presentation H2}
    {frozen : TwistedYetter.Semantics.Independent.TwistedPremodularCategory K}
    {graphical : RibbonGraphicalEvaluation frozen.category}
    {compiler : RoleAwareGraphCompiler frozen}
    {normalization : ThamDefinition511Normalization K}
    {currentCategory :
      TwistedYetter.Fusion.EGNO.PremodularFusionCategory
        (K := K) (C := C) (S := S)}
    {currentCharacter : TensorIdentityAutomorphism C}
    (admission :
      FormalAdmission (semantics := semantics) (current := current)
        (frozen := frozen) (graphical := graphical) (compiler := compiler)
        (normalization := normalization)
        (currentCategory := currentCategory)
        (currentCharacter := currentCharacter)) :
    admission.currentValue = admission.frozenValue := by
  exact admission.binding.roleAwareCycleEval_eq_frozenEvaluateCycle

end FrozenConformanceCertificate

end TwistedYetter.Kirby.Final.CompleteSemanticConformance
