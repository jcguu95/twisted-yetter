import TwistedYetter.Kirby.FinalFormalizationPackage
import TwistedYetter.Kirby.ConcreteMarkedPairAssembly
import TwistedYetter.Kirby.SourceBackedKirbyCompleteness
import TwistedYetter.Kirby.SourceBackedHandleChainNaturality
import TwistedYetter.Kirby.SourceBoundGeometricH2Compiler
import TwistedYetter.Kirby.SourceBoundTableTwoEvaluatorCompiler

/-!
# Target theorem for a marked four-manifold invariant

This module states the next formalization target without identifying the
construction with a Crane--Yetter state sum.

The existing R11 theorem proves presentation independence after receiving a
complete evaluator prescription and a marked-presentation system.  The target
below keeps that valid implication while making the remaining construction
obligations impossible to confuse with an established concrete invariant.

No current value of `FourManifoldInvariantInputs` is defined here. Producing
one from concrete Kirby syntax and the remaining source-bound evaluator
compiler is the construction goal. Special Kirby completeness and handle-chain
naturality are separate, visible topology and homology domain axioms.
-/

namespace TwistedYetter.Kirby.FourManifoldInvariantTarget

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.ConcreteMarkedPairAssembly
open TwistedYetter.Kirby.EvaluatorCompiler
open TwistedYetter.Kirby.SourceBoundEvaluatorCompilation
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality

/-- Exact denominator of conditions for the intended four-manifold theorem. -/
inductive TargetCondition where
  | categoryAndGraphicalAlgebra
  | explicitThreeHandleNormalization
  | closedTypedPresentationExecution
  | primitiveCategoricalEventCompilerMechanism
  | chainDerivedMarkedH2Transport
  | sourceBoundGeometricH2CompilerMechanism
  | specialKirbyCalculusCompleteness
  | exhaustiveEvaluatorCompilerMechanism
  | markedPairAssemblyMechanism
  | sourceBoundLocalMoveRecipes
  | sourceBoundEvaluatorCompilerInstance
  | sourceBoundGeometricH2CompilerInstance
  deriving Repr, BEq, DecidableEq

/-- Every condition that must be closed before the target can be promoted. -/
def requiredTargetConditions : List TargetCondition :=
  [
    .categoryAndGraphicalAlgebra,
    .explicitThreeHandleNormalization,
    .closedTypedPresentationExecution,
    .primitiveCategoricalEventCompilerMechanism,
    .chainDerivedMarkedH2Transport,
    .sourceBoundGeometricH2CompilerMechanism,
    .specialKirbyCalculusCompleteness,
    .exhaustiveEvaluatorCompilerMechanism,
    .markedPairAssemblyMechanism,
    .sourceBoundLocalMoveRecipes,
    .sourceBoundGeometricH2CompilerInstance,
    .sourceBoundEvaluatorCompilerInstance
  ]

/--
Conditions already discharged by kernel-checked constructions.

The chain-derived item establishes the generic mechanism: a move supplies a
chain homotopy equivalence and Lean derives the additive map on `H2`. The
special-Kirby item is established relative to one separately audited,
source-backed topology domain axiom, which returns only an unmarked topology
movie. The handle-chain compiler instance is established relative to a second
separately audited standard homology-domain axiom. Every move carries one
typed local recipe shared by graphical and chain compilation. Constructing
the concrete categorical evaluator remains open.
-/
def establishedFoundationConditions : List TargetCondition :=
  [
    .categoryAndGraphicalAlgebra,
    .explicitThreeHandleNormalization,
    .closedTypedPresentationExecution,
    .primitiveCategoricalEventCompilerMechanism,
    .chainDerivedMarkedH2Transport,
    .sourceBoundGeometricH2CompilerMechanism,
    .specialKirbyCalculusCompleteness,
    .exhaustiveEvaluatorCompilerMechanism,
    .markedPairAssemblyMechanism,
    .sourceBoundLocalMoveRecipes,
    .sourceBoundGeometricH2CompilerInstance
  ]

/-- Conditions deliberately left open for the concrete invariant construction. -/
def openConstructionConditions : List TargetCondition :=
  [
    .sourceBoundEvaluatorCompilerInstance
  ]

theorem target_condition_count :
    requiredTargetConditions.length = 12 := by
  rfl

theorem established_foundation_condition_count :
    establishedFoundationConditions.length = 11 := by
  rfl

theorem open_construction_condition_count :
    openConstructionConditions.length = 1 := by
  rfl

/--
Every special presentation now carries a kernel-checked event-by-event trace
from the empty boundary back to the empty boundary, bound to its declared
Morse slices.
-/
theorem closed_typed_presentation_execution_established :
    TargetCondition.closedTypedPresentationExecution ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- Raw presentation execution is no longer an untracked construction gap. -/
theorem closed_typed_presentation_execution_not_open :
    TargetCondition.closedTypedPresentationExecution ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

/--
Every raw event must compile to a sign-correct primitive inside a
coherence-only structural context; whole diagrams and raw numerators are
derived from the typed execution trace.
-/
theorem primitive_categorical_event_compiler_mechanism_established :
    TargetCondition.primitiveCategoricalEventCompilerMechanism ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The primitive event compiler mechanism is no longer an untracked gap. -/
theorem primitive_categorical_event_compiler_mechanism_not_open :
    TargetCondition.primitiveCategoricalEventCompilerMechanism ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

/-- Chain-derived marked `H2` transport is explicitly on the established side. -/
theorem chain_derived_marked_h2_transport_established :
    TargetCondition.chainDerivedMarkedH2Transport ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The same condition cannot simultaneously remain in the open ledger. -/
theorem chain_derived_marked_h2_transport_not_open :
    TargetCondition.chainDerivedMarkedH2Transport ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

/--
Each local H2 identity is now derived from an exact chain equivalence, the
shared recipe identity, and a geometric-coordinate naturality square.
-/
theorem source_bound_geometric_h2_compiler_mechanism_established :
    TargetCondition.sourceBoundGeometricH2CompilerMechanism ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The source-bound H2 mechanism is no longer an untracked gap. -/
theorem source_bound_geometric_h2_compiler_mechanism_not_open :
    TargetCondition.sourceBoundGeometricH2CompilerMechanism ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

/--
Special Kirby completeness is established only as the explicitly audited
topology domain axiom in `SourceBackedKirbyCompleteness`.
-/
theorem special_kirby_calculus_completeness_established :
    TargetCondition.specialKirbyCalculusCompleteness ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The source-backed topology condition is no longer in the open ledger. -/
theorem special_kirby_calculus_completeness_not_open :
    TargetCondition.specialKirbyCalculusCompleteness ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

/-- Exhaustive dispatch is established as a mechanism, not as an instance. -/
theorem exhaustive_evaluator_compiler_mechanism_established :
    TargetCondition.exhaustiveEvaluatorCompilerMechanism ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The marked-pair transport theorem is now derived by movie induction. -/
theorem marked_pair_assembly_mechanism_established :
    TargetCondition.markedPairAssemblyMechanism ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/--
Each topology move now carries a kind-indexed literal presentation-window
recipe with one shared identity for graphical and chain compilation.
-/
theorem source_bound_local_move_recipes_established :
    TargetCondition.sourceBoundLocalMoveRecipes ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The typed-recipe mechanism cannot simultaneously remain open. -/
theorem source_bound_local_move_recipes_not_open :
    TargetCondition.sourceBoundLocalMoveRecipes ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

/-- No concrete eight-case evaluator compiler value is defined yet. -/
theorem source_bound_evaluator_compiler_instance_open :
    TargetCondition.sourceBoundEvaluatorCompilerInstance ∈
      openConstructionConditions := by
  simp [openConstructionConditions]

/--
The marked H2 compiler instance is constructed relative to one visible,
standard handle-chain naturality domain axiom.
-/
theorem source_bound_geometric_h2_compiler_instance_established :
    TargetCondition.sourceBoundGeometricH2CompilerInstance ∈
      establishedFoundationConditions := by
  simp [establishedFoundationConditions]

/-- The source-backed H2 compiler instance is no longer an open constructor. -/
theorem source_bound_geometric_h2_compiler_instance_not_open :
    TargetCondition.sourceBoundGeometricH2CompilerInstance ∉
      openConstructionConditions := by
  simp [openConstructionConditions]

theorem target_condition_partition :
    establishedFoundationConditions ++ openConstructionConditions =
      requiredTargetConditions := by
  rfl

/--
The partition contains exactly the required conditions, up to list order.
Using `Perm` prevents a bookkeeping reorder from being mistaken for a changed
mathematical denominator.
-/
theorem target_condition_partition_complete :
    (establishedFoundationConditions ++ openConstructionConditions).Perm
      requiredTargetConditions := by
  decide

/-- Machine-checked guard against silently calling the current target complete. -/
theorem current_target_has_open_conditions :
    openConstructionConditions ≠ [] := by
  decide

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
The exact mathematical inputs whose concrete construction will establish the
marked four-manifold invariant.

This structure does not accept an arbitrary compact evaluator prescription,
an arbitrary decorated-presentation function, or an already-complete marked
presentation system. Its evaluator field is the source-bound exhaustive
eight-case compiler: every closed diagram is compiled event-by-event from the
typed raw execution trace. Its marked system is derived from local chain
transport by movie induction.

An arbitrary inhabitant is still only a conditional theorem input, not
admissible construction evidence. The evaluator must be generated from
source-bound local move recipes and must compile the exact graphical R7/R8/R9
proof objects. Handle-chain equivalences come only from the separately named
standard homology-domain axiom; the final identity is derived in Lean.
`generalCerf` is also a visible standard topology-domain input, not a theorem
proved in this module.
-/
structure FourManifoldInvariantInputs
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  evaluatorCompiler :
    SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2
  generalCerf : GeneralCerfCompleteness manifold
  basePresentation : SpecialKirbyPresentation manifold H2

namespace FourManifoldInvariantInputs

/-- The compact R11 prescription derived from the exhaustive compiler. -/
noncomputable def prescription
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : FourManifoldInvariantInputs categoryData manifold H2) :
    HomologicallyTwistedKirbyPrescription categoryData manifold H2 :=
  inputs.evaluatorCompiler.toTableTwo.toPrescription

/-- Marked presentation system derived from local chain functoriality. -/
noncomputable def markedSystem
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : FourManifoldInvariantInputs categoryData manifold H2) :
    MarkedPairPresentationSystem manifold H2 :=
  (sourceBackedGeometricH2Compiler manifold H2).toGeometricMarkedH2Compiler
    |>.markedPairSystem inputs.generalCerf inputs.basePresentation

/-- The value assigned to the marked pair by the chosen certified presentation. -/
noncomputable def value
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : FourManifoldInvariantInputs categoryData manifold H2)
    (alpha : H2) : K :=
  inputs.markedSystem.invariant inputs.prescription alpha

/--
Target theorem, presentation form.

Once concrete target inputs have been constructed, every certified Kirby
presentation of `(X, alpha)` computes the same value.
-/
theorem presentation_independent
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : FourManifoldInvariantInputs categoryData manifold H2)
    {presentation : SpecialKirbyPresentation manifold H2}
    {coordinate alpha : H2}
    (represents :
      inputs.markedSystem.represents presentation coordinate alpha) :
    inputs.prescription.presentationValue presentation coordinate =
      inputs.value alpha :=
  inputs.markedSystem.homologically_twisted_kirby_invariant_established
    inputs.prescription represents

/--
Target theorem, two-presentation form.

Any two certified realizations of the same marked pair have equal normalized
Kirby evaluations.  This is the exact presentation-independence statement
needed before the construction may be called a four-manifold invariant.
-/
theorem four_manifold_invariant_target
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : FourManifoldInvariantInputs categoryData manifold H2)
    {left right : SpecialKirbyPresentation manifold H2}
    {leftCoordinate rightCoordinate alpha : H2}
    (leftRepresents :
      inputs.markedSystem.represents left leftCoordinate alpha)
    (rightRepresents :
      inputs.markedSystem.represents right rightCoordinate alpha) :
    inputs.prescription.presentationValue left leftCoordinate =
      inputs.prescription.presentationValue right rightCoordinate :=
  inputs.markedSystem.same_pair_value inputs.prescription
    leftRepresents rightRepresents

end FourManifoldInvariantInputs

end TwistedYetter.Kirby.FourManifoldInvariantTarget
