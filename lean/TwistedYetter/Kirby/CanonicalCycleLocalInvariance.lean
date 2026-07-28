import TwistedYetter.Kirby.CanonicalCycleSlideGeometry

/-!
# Eight cycle-safe local calculations

This module proves the category-side consequence of each directed special
Kirby move.  Every calculation starts from an explicit degree-two cycle.
The target representative is supplied by exact move geometry, and
representative independence is invoked only after the local graphical
calculation has finished.

The eight constructors below cannot contain a final equality of evaluator
values.  They contain only:

* generated framed-isotopy geometry;
* whole-linear-sum ordinary or label-indexed slide programs; or
* exact isolated 1--2 or 2--3 factorization geometry.

Lean proves the finite sums, scalarization, normalization, reverse-move
bookkeeping, and passage from explicit cycles to homology classes.
-/

namespace TwistedYetter.Kirby.CanonicalCycleLocalInvariance

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalCycleSlideGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Equal counts and equal explicit-cycle linear evaluations give equal values. -/
theorem cycleEvalC_eq_of_counts_and_linear_eval
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle)
    (countsEq : source.topology.counts = target.topology.counts)
    (linearEvalEq :
      LinearDiagram.eval
          (source.cycleLinearDiagram
            𝒞.premodular automorphism sourceCycle) =
        LinearDiagram.eval
          (target.cycleLinearDiagram
            𝒞.premodular automorphism targetCycle)) :
    source.cycleEvalC 𝒞 automorphism sourceCycle =
      target.cycleEvalC 𝒞 automorphism targetCycle := by
  apply EvaluatedTableTwoStep.normalized_eq_of_counts_and_raw
  · exact countsEq
  · exact congrArg
      𝒞.premodular.toFusionCategoryData.closedScalar linearEvalEq

/-- Exact 1--2 birth geometry gives equality of normalized cycle values. -/
theorem oneTwoBirth_cycleEvalC
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo)
    (geometry :
      OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    source.cycleEvalC 𝒞 automorphism sourceCycle =
      target.cycleEvalC 𝒞 automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle) := by
  let calculation :
      OneTwoLocalCalculation
        (CanonicalPresentation.normalizationProfile 𝒞) := {
    pairValue := globalDimension 𝒞.premodular
    cutValue := 1
    before :=
      target.cycleEvaluationState 𝒞.premodular automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle)
    after :=
      source.cycleEvaluationState
        𝒞.premodular automorphism sourceCycle
    counts_sound := countsSound
    isolated_from_rest := True
    isolated_from_rest_witness := True.intro
    disjoint_union_sound := fun _ =>
      geometry.cycleRawNumerator_factor
        𝒞 automorphism sourceCycle
    transparent_twist_trivial := True
    transparent_twist_witness := True.intro
    cutting_identity := fun _ => by
      simp [CanonicalPresentation.normalizationProfile]
    killing_identity := by
      simp [CanonicalPresentation.normalizationProfile]
  }
  simpa only [CanonicalPresentation.cycleEvalC] using
    calculation.normalized_sound.symm

/-- Exact 2--3 birth geometry gives equality of normalized cycle values. -/
theorem twoThreeBirth_cycleEvalC
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree)
    (geometry :
      TwoThreeBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    source.cycleEvalC 𝒞 automorphism sourceCycle =
      target.cycleEvalC 𝒞 automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle) := by
  let calculation :
      TwoThreeLocalCalculation
        (CanonicalPresentation.normalizationProfile 𝒞) := {
    unknotValue := globalDimension 𝒞.premodular
    before :=
      target.cycleEvaluationState 𝒞.premodular automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle)
    after :=
      source.cycleEvaluationState
        𝒞.premodular automorphism sourceCycle
    counts_sound := countsSound
    unlinked_unknotted_zero_framed := True
    unlink_witness := True.intro
    disjoint_union_sound := fun _ =>
      geometry.cycleRawNumerator_factor
        𝒞.premodular automorphism sourceCycle
    pivotal_dimension_preserved := rfl
  }
  simpa only [CanonicalPresentation.cycleEvalC] using
    calculation.normalized_sound.symm

/--
The eight directed, source-bound local calculations.

The move's chain-level `MarkedH2Transport` remains part of the index.  A
calculation cannot substitute a separately selected homology map.
-/
inductive LocalCycleCalculation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    TableTwoMove source.topology target.topology →
      Type (max (max uK uC) (max vC (uH + 1)))
  | framedIsotopy
      (metadata :
        TableTwoMoveMetadata .framedIsotopy
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        FramedIsotopyCycleGeometry
          source target transport.targetClass) :
      LocalCycleCalculation 𝒞 automorphism
        (.framedIsotopy metadata countsSound transport)
  | oneOverOne
      (metadata :
        TableTwoMoveMetadata .oneOverOne
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        OrdinaryCycleSlideGeometry 𝒞.premodular automorphism
          source target transport
          .oneOverOne
          (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
          metadata.moveId
          metadata.sourcePresentationHash metadata.targetPresentationHash
          (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
          (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit)) :
      LocalCycleCalculation 𝒞 automorphism
        (.oneOverOne metadata countsSound transport)
  | twoOverOne
      (metadata :
        TableTwoMoveMetadata .twoOverOne
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        OrdinaryCycleSlideGeometry 𝒞.premodular automorphism
          source target transport
          .twoOverOne
          (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
          metadata.moveId
          metadata.sourcePresentationHash metadata.targetPresentationHash
          (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
          (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit)) :
      LocalCycleCalculation 𝒞 automorphism
        (.twoOverOne metadata countsSound transport)
  | twoOverTwo
      (metadata :
        TableTwoMoveMetadata .twoOverTwo
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (transport : MarkedH2Transport source.topology target.topology)
      (evaluationSound :
        (sourceCycle : source.DegreeTwoCycle) →
          LinearDiagram.eval
              (source.cycleLinearDiagram
                𝒞.premodular automorphism sourceCycle) =
            LinearDiagram.eval
              (target.cycleLinearDiagram 𝒞.premodular automorphism
                ((CycleTransport.ofMarkedH2Transport
                  source target transport).targetCycle sourceCycle))) :
      LocalCycleCalculation 𝒞 automorphism
        (.twoOverTwo metadata countsSound transport)
  | oneTwoBirth
      (metadata :
        TableTwoMoveMetadata .oneTwoBirth
          source.topology target.topology)
      (countsSound :
        target.topology.counts = source.topology.counts.addOneTwo)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        OneTwoBirthCycleGeometry
          source target transport.targetClass) :
      LocalCycleCalculation 𝒞 automorphism
        (.oneTwoBirth metadata countsSound transport)
  | oneTwoDeath
      (metadata :
        TableTwoMoveMetadata .oneTwoDeath
          source.topology target.topology)
      (countsSound :
        source.topology.counts = target.topology.counts.addOneTwo)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        OneTwoDeathCycleGeometry source target transport) :
      LocalCycleCalculation 𝒞 automorphism
        (.oneTwoDeath metadata countsSound transport)
  | twoThreeBirth
      (metadata :
        TableTwoMoveMetadata .twoThreeBirth
          source.topology target.topology)
      (countsSound :
        target.topology.counts = source.topology.counts.addTwoThree)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        TwoThreeBirthCycleGeometry
          source target transport.targetClass) :
      LocalCycleCalculation 𝒞 automorphism
        (.twoThreeBirth metadata countsSound transport)
  | twoThreeDeath
      (metadata :
        TableTwoMoveMetadata .twoThreeDeath
          source.topology target.topology)
      (countsSound :
        source.topology.counts = target.topology.counts.addTwoThree)
      (transport : MarkedH2Transport source.topology target.topology)
      (geometry :
        TwoThreeDeathCycleGeometry source target transport) :
      LocalCycleCalculation 𝒞 automorphism
        (.twoThreeDeath metadata countsSound transport)

namespace LocalCycleCalculation

/-- The cycle selected by the public evaluator represents its input class. -/
private theorem chosenCycleClass
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.topology.handleChain.complex.homologyπ 2
        (presentation.chosenCycle alpha) =
      alpha :=
  presentation.chosenCycle_class alpha

/--
A direct cycle transport sends the selected source cycle to the actual
target handle-chain homology class induced by the chain equivalence.
-/
private theorem transportedChosenCycleClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (markedTransport :
      MarkedH2Transport source.topology target.topology)
    (cycleTransport :
      CycleTransport source target markedTransport.targetClass)
    (alpha : source.topology.handleChain.SecondHomology) :
    target.topology.handleChain.complex.homologyπ 2
        (cycleTransport.targetCycle (source.chosenCycle alpha)) =
      markedTransport.chainEquivalence.secondHomologyAddEquiv alpha := by
  apply target.topology.h2ModelEquiv.injective
  rw [cycleTransport.class_sound]
  rw [chosenCycleClass source alpha]
  simp [MarkedH2Transport.targetClass,
    MarkedH2Transport.homologyEquiv,
    MarkedH2Transport.homologyAddEquiv]

/-- Reverse transport after forward transport returns to the original class. -/
private theorem reverseTransportedCycleClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (transport : MarkedH2Transport source.topology target.topology)
    (forward : CycleTransport source target transport.targetClass)
    (reverse :
      CycleTransport target source transport.homologyEquiv.symm)
    (alpha : source.topology.handleChain.SecondHomology) :
    source.topology.handleChain.complex.homologyπ 2
        (reverse.targetCycle
          (forward.targetCycle (source.chosenCycle alpha))) =
      alpha := by
  apply source.topology.h2ModelEquiv.injective
  rw [reverse.class_sound]
  rw [forward.class_sound]
  rw [chosenCycleClass source alpha]
  simp [MarkedH2Transport.targetClass,
    MarkedH2Transport.homologyEquiv,
    MarkedH2Transport.homologyAddEquiv]

/--
Every restricted local calculation preserves the public homology-level value
once representative independence is known at its two endpoints.
-/
theorem soundOfEndpoints
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (sourceRepresentativeIndependence :
      CanonicalPresentation.CycleRepresentativeIndependence
        𝒞 automorphism source)
    (targetRepresentativeIndependence :
      CanonicalPresentation.CycleRepresentativeIndependence
        𝒞 automorphism target)
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (alpha : source.topology.handleChain.SecondHomology) :
    source.EvalC 𝒞 automorphism alpha =
      target.EvalC 𝒞 automorphism
        (move.homologyTransport.chainEquivalence
          |>.secondHomologyAddEquiv alpha) := by
  cases calculation with
  | framedIsotopy metadata counts transport geometry =>
      let sourceCycle := source.chosenCycle alpha
      let targetCycle :=
        geometry.cycleTransport.targetCycle sourceCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism sourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha sourceCycle (chosenCycleClass source alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle := by
              exact cycleEvalC_eq_of_counts_and_linear_eval
                𝒞 automorphism sourceCycle targetCycle counts
                (geometry.cycleLinearDiagram_eval_transport
                  𝒞.premodular automorphism sourceCycle)
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass
                  transport geometry.cycleTransport alpha)
  | oneOverOne metadata counts transport geometry =>
      let cycleTransport :=
        CycleTransport.ofMarkedH2Transport source target transport
      let sourceCycle := source.chosenCycle alpha
      let targetCycle := cycleTransport.targetCycle sourceCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism sourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha sourceCycle (chosenCycleClass source alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle := by
              exact cycleEvalC_eq_of_counts_and_linear_eval
                𝒞 automorphism sourceCycle targetCycle counts
                (geometry.cycleLinearDiagram_eval_transport
                  𝒞.premodular automorphism sourceCycle)
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass
                  transport cycleTransport alpha)
  | twoOverOne metadata counts transport geometry =>
      let cycleTransport :=
        CycleTransport.ofMarkedH2Transport source target transport
      let sourceCycle := source.chosenCycle alpha
      let targetCycle := cycleTransport.targetCycle sourceCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism sourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha sourceCycle (chosenCycleClass source alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle := by
              exact cycleEvalC_eq_of_counts_and_linear_eval
                𝒞 automorphism sourceCycle targetCycle counts
                (geometry.cycleLinearDiagram_eval_transport
                  𝒞.premodular automorphism sourceCycle)
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass
                  transport cycleTransport alpha)
  | twoOverTwo metadata counts transport evaluationSound =>
      let cycleTransport :=
        CycleTransport.ofMarkedH2Transport source target transport
      let sourceCycle := source.chosenCycle alpha
      let targetCycle := cycleTransport.targetCycle sourceCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism sourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha sourceCycle (chosenCycleClass source alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle := by
              exact cycleEvalC_eq_of_counts_and_linear_eval
                𝒞 automorphism sourceCycle targetCycle counts
                (evaluationSound sourceCycle)
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass
                  transport cycleTransport alpha)
  | oneTwoBirth metadata counts transport geometry =>
      let sourceCycle := source.chosenCycle alpha
      let targetCycle :=
        geometry.added.cycleTransport.targetCycle sourceCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism sourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha sourceCycle (chosenCycleClass source alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle :=
              oneTwoBirth_cycleEvalC
                𝒞 automorphism counts geometry sourceCycle
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass
                  transport geometry.added.cycleTransport alpha)
  | oneTwoDeath metadata counts transport geometry =>
      let forward :=
        CycleTransport.ofMarkedH2Transport source target transport
      let sourceCycle := source.chosenCycle alpha
      let targetCycle := forward.targetCycle sourceCycle
      let reverse := geometry.reverseBirth.added.cycleTransport
      let returnedSourceCycle := reverse.targetCycle targetCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism returnedSourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha returnedSourceCycle
                (reverseTransportedCycleClass
                  transport forward reverse alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle := by
              symm
              exact oneTwoBirth_cycleEvalC
                𝒞 automorphism counts geometry.reverseBirth targetCycle
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass transport forward alpha)
  | twoThreeBirth metadata counts transport geometry =>
      let sourceCycle := source.chosenCycle alpha
      let targetCycle :=
        geometry.added.cycleTransport.targetCycle sourceCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism sourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha sourceCycle (chosenCycleClass source alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle :=
              twoThreeBirth_cycleEvalC
                𝒞 automorphism counts geometry sourceCycle
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass
                  transport geometry.added.cycleTransport alpha)
  | twoThreeDeath metadata counts transport geometry =>
      let forward :=
        CycleTransport.ofMarkedH2Transport source target transport
      let sourceCycle := source.chosenCycle alpha
      let targetCycle := forward.targetCycle sourceCycle
      let reverse := geometry.reverseBirth.added.cycleTransport
      let returnedSourceCycle := reverse.targetCycle targetCycle
      calc
        source.EvalC 𝒞 automorphism alpha =
            source.cycleEvalC 𝒞 automorphism returnedSourceCycle := by
              exact source.EvalC_eq_cycleEvalC
                𝒞 automorphism
                sourceRepresentativeIndependence
                alpha returnedSourceCycle
                (reverseTransportedCycleClass
                  transport forward reverse alpha)
        _ = target.cycleEvalC 𝒞 automorphism targetCycle := by
              symm
              exact twoThreeBirth_cycleEvalC
                𝒞 automorphism counts geometry.reverseBirth targetCycle
        _ = target.EvalC 𝒞 automorphism
              (transport.chainEquivalence
                |>.secondHomologyAddEquiv alpha) := by
              symm
              exact target.EvalC_eq_cycleEvalC
                𝒞 automorphism
                targetRepresentativeIndependence
                (transport.chainEquivalence
                  |>.secondHomologyAddEquiv alpha) targetCycle
                (transportedChosenCycleClass transport forward alpha)

/-- Backward-compatible global-system wrapper around `soundOfEndpoints`. -/
theorem sound
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (representativeIndependence :
      CanonicalPresentation.CycleRepresentativeIndependenceSystem
        𝒞 automorphism H2)
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (alpha : source.topology.handleChain.SecondHomology) :
    source.EvalC 𝒞 automorphism alpha =
      target.EvalC 𝒞 automorphism
        (move.homologyTransport.chainEquivalence
          |>.secondHomologyAddEquiv alpha) :=
  soundOfEndpoints
    (representativeIndependence source)
    (representativeIndependence target)
    calculation alpha

end LocalCycleCalculation

end TwistedYetter.Kirby.CanonicalCycleLocalInvariance
