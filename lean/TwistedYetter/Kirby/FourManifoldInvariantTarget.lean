import TwistedYetter.Kirby.FinalFormalizationPackage
import TwistedYetter.Kirby.SourceBackedKirbyCompleteness

/-!
# Target theorem for a marked four-manifold invariant

This module states the next formalization target without identifying the
construction with a Crane--Yetter state sum.

The existing R11 theorem proves presentation independence after receiving a
complete evaluator prescription and a marked-presentation system.  The target
below keeps that valid implication while making the remaining construction
obligations impossible to confuse with an established concrete invariant.

No current value of `FourManifoldInvariantInputs` is defined here.  Producing
one from concrete Kirby syntax, a concrete evaluator compiler, the
source-backed special Kirby calculus theorem, and chain-derived `H2` transport
is the remaining goal.
-/

namespace TwistedYetter.Kirby.FourManifoldInvariantTarget

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness

/-- Exact denominator of conditions for the intended four-manifold theorem. -/
inductive TargetCondition where
  | categoryAndGraphicalAlgebra
  | explicitThreeHandleNormalization
  | concreteEvaluatorCompiler
  | specialKirbyCalculusCompleteness
  | chainDerivedMarkedH2Transport
  | concreteMarkedPairAssembly
  deriving Repr, BEq, DecidableEq

/-- Every condition that must be closed before the target can be promoted. -/
def requiredTargetConditions : List TargetCondition :=
  [
    .categoryAndGraphicalAlgebra,
    .explicitThreeHandleNormalization,
    .chainDerivedMarkedH2Transport,
    .specialKirbyCalculusCompleteness,
    .concreteEvaluatorCompiler,
    .concreteMarkedPairAssembly
  ]

/--
Conditions already discharged by kernel-checked constructions.

The chain-derived item establishes the generic mechanism: a move supplies a
chain homotopy equivalence and Lean derives the additive map on `H2`. The
special-Kirby item is established relative to one separately audited,
source-backed topology domain axiom, which returns only an unmarked topology
movie. Binding concrete Kirby syntax to chain matrices and enriching that
movie remains part of `concreteMarkedPairAssembly`.
-/
def establishedFoundationConditions : List TargetCondition :=
  [
    .categoryAndGraphicalAlgebra,
    .explicitThreeHandleNormalization,
    .chainDerivedMarkedH2Transport,
    .specialKirbyCalculusCompleteness
  ]

/-- Conditions deliberately left open for the concrete invariant construction. -/
def openConstructionConditions : List TargetCondition :=
  [
    .concreteEvaluatorCompiler,
    .concreteMarkedPairAssembly
  ]

theorem target_condition_count :
    requiredTargetConditions.length = 6 := by
  rfl

theorem established_foundation_condition_count :
    establishedFoundationConditions.length = 4 := by
  rfl

theorem open_construction_condition_count :
    openConstructionConditions.length = 2 := by
  rfl

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

This structure adds no proposition that can be filled by an arbitrary
`True` witness.  Its fields are the closed evaluator prescription and marked
presentation system already required by the kernel-checked R11 theorem.

The nested R11 structures still expose semantic propositions at the external
topology boundary.  Consequently, an arbitrary inhabitant of this structure
is not by itself admissible evidence.  The eventual concrete value must be
generated by the evaluator compiler, exact special-Kirby source binding, and
chain-derived marked-homology construction listed above.
-/
structure FourManifoldInvariantInputs
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  prescription :
    HomologicallyTwistedKirbyPrescription categoryData manifold H2
  markedSystem : MarkedPairPresentationSystem manifold H2

namespace FourManifoldInvariantInputs

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
