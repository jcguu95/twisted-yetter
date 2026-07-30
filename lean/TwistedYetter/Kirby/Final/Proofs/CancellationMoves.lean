import TwistedYetter.Kirby.Final.Proofs.CleanBandSlides
import TwistedYetter.Kirby.Final.Proofs.RepresentativeIndependence

/-!
# Frozen-frontend cancellation moves

The topology entrance supplies only fixed-label local graphical normal forms.
This file proves the character, finite-sum, and THAM-normalization calculations.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

theorem addedTwoHandle_ordinaryKirbyWeight
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    ordinaryKirbyWeight 𝒞
        (coordinates.mergeLabeling sourceLabeling newLabel) =
      ordinaryKirbyWeight 𝒞 sourceLabeling *
        𝒞.simples.quantumDimension newLabel := by
  classical
  unfold ordinaryKirbyWeight
  calc
    (∏ i,
      𝒞.simples.quantumDimension
        (coordinates.mergeLabeling sourceLabeling newLabel i)) =
      ∏ i : Fin source.diagram.handles.hTwo ⊕ Unit,
        𝒞.simples.quantumDimension
          (match i with
          | .inl old => sourceLabeling old
          | .inr _ => newLabel) := by
      symm
      apply Fintype.prod_equiv coordinates.indexEquiv
        (fun i =>
          𝒞.simples.quantumDimension
            (match i with
            | .inl old => sourceLabeling old
            | .inr _ => newLabel))
        (fun i =>
          𝒞.simples.quantumDimension
            (coordinates.mergeLabeling sourceLabeling newLabel i))
      intro i
      cases i with
      | inl old =>
          simp [AddedTwoHandleCoordinates.mergeLabeling]
      | inr new =>
          obtain rfl : new = () := Subsingleton.elim _ _
          simp [AddedTwoHandleCoordinates.mergeLabeling]
    _ =
      (∏ i,
        𝒞.simples.quantumDimension (sourceLabeling i)) *
        𝒞.simples.quantumDimension newLabel := by
      simp

theorem addedTwoHandle_characterWeight
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    characterWeight 𝒞η target.turnedOver
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (transport.mapCycle sourceCycle) =
      characterWeight 𝒞η source.turnedOver
        sourceLabeling sourceCycle := by
  classical
  unfold characterWeight
  have unitEquality :
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling sourceLabeling newLabel i)) ^
            ((transport.mapCycle sourceCycle).1 i)) =
        ∏ i,
          (𝒞η.character.value (sourceLabeling i)) ^
            (sourceCycle.1 i) := by
    calc
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling sourceLabeling newLabel i)) ^
            ((transport.mapCycle sourceCycle).1 i)) =
        ∏ i : Fin source.diagram.handles.hTwo ⊕ Unit,
          match i with
          | .inl old =>
              (𝒞η.character.value (sourceLabeling old)) ^
                (sourceCycle.1 old)
          | .inr _ => 1 := by
            symm
            apply Fintype.prod_equiv coordinates.indexEquiv
            intro i
            cases i with
            | inl old =>
                simp [AddedTwoHandleCoordinates.mergeLabeling,
                  coordinates.oldCoefficient]
            | inr new =>
                obtain rfl : new = () := Subsingleton.elim _ _
                simp [AddedTwoHandleCoordinates.mergeLabeling,
                  coordinates.newCoefficientZero]
      _ =
        ∏ i,
          (𝒞η.character.value (sourceLabeling i)) ^
            (sourceCycle.1 i) := by
          simp
  exact congrArg (fun unit : Kˣ => (unit : K)) unitEquality

theorem oneTwoBirth_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η target.diagram target.primalBoundary target.turnedOver
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (transport.mapCycle sourceCycle)).graph =
      specialCutMeridianClosedValue 𝒞η.category newLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.primalBoundary source.turnedOver
            sourceLabeling sourceCycle).graph := by
  have interpreted :=
    shum_framedRibbonCoherence
      (oneTwoBirth_hasTypedGraphicalNormalForm
        𝒞η coordinates sourceCycle sourceLabeling newLabel)
  unfold canonicalRibbonGraphicalEvaluation
  rw [interpreted]
  exact closedComposeExpression_scalar _ _

theorem twoThreeBirth_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η target.diagram target.primalBoundary target.turnedOver
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (transport.mapCycle sourceCycle)).graph =
      𝒞η.category.simples.quantumDimension newLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.primalBoundary source.turnedOver
            sourceLabeling sourceCycle).graph := by
  have interpreted :=
    shum_framedRibbonCoherence
      (twoThreeBirth_hasTypedGraphicalNormalForm
        𝒞η coordinates sourceCycle sourceLabeling newLabel)
  unfold canonicalRibbonGraphicalEvaluation
  rw [interpreted, closedComposeExpression_scalar]
  have localValue :
      𝒞η.category.closedScalar
          (ordinaryKirbyLoopExpression
            𝒞η.category newLabel).interpret =
        𝒞η.category.simples.quantumDimension newLabel := by
    unfold ordinaryKirbyLoopExpression
    simp only [RibbonExpression.interpret]
    rw [ribbonTraceMorphism_identity,
      𝒞η.category.closedScalar_smul_identity]
  rw [localValue]

theorem oneTwoBirth_rawCycleSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    rawCycleSum 𝒞η target.diagram target.primalBoundary target.turnedOver
        (transport.mapCycle sourceCycle) =
      rawCycleSum 𝒞η source.diagram source.primalBoundary source.turnedOver
        sourceCycle := by
  classical
  unfold rawCycleSum
  calc
    (∑ targetLabeling,
      ordinaryKirbyWeight 𝒞η.category targetLabeling *
        characterWeight 𝒞η target.turnedOver targetLabeling
          (transport.mapCycle sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.primalBoundary target.turnedOver
            targetLabeling (transport.mapCycle sourceCycle)).graph) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category source.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η target.turnedOver
            (coordinates.mergeLabeling pair.1 pair.2)
            (transport.mapCycle sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η target.diagram target.primalBoundary target.turnedOver
              (coordinates.mergeLabeling pair.1 pair.2)
              (transport.mapCycle sourceCycle)).graph := by
        symm
        apply Fintype.sum_equiv
          (coordinates.labelingEquiv 𝒞η.category.simples.Simple)
        intro pair
        rfl
    _ =
      ∑ sourceLabeling,
        ∑ newLabel,
          (𝒞η.category.simples.quantumDimension newLabel *
            specialCutMeridianClosedValue 𝒞η.category newLabel) *
          (ordinaryKirbyWeight 𝒞η.category sourceLabeling *
            characterWeight 𝒞η source.turnedOver sourceLabeling sourceCycle *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.primalBoundary source.turnedOver
                sourceLabeling sourceCycle).graph) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        apply Finset.sum_congr rfl
        intro newLabel _
        rw [addedTwoHandle_ordinaryKirbyWeight,
          addedTwoHandle_characterWeight,
          oneTwoBirth_graphicalFactor]
        ring
    _ =
      ∑ sourceLabeling,
        ordinaryKirbyWeight 𝒞η.category sourceLabeling *
          characterWeight 𝒞η source.turnedOver sourceLabeling sourceCycle *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.primalBoundary source.turnedOver
                sourceLabeling sourceCycle).graph := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        rw [← Finset.sum_mul]
        rw [specialCutMeridianSum_eq_one
          𝒞η.category (egno_tensorUnitQuantumDimension 𝒞η.category)]
        simp

theorem twoThreeBirth_rawCycleSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    rawCycleSum 𝒞η target.diagram target.primalBoundary target.turnedOver
        (transport.mapCycle sourceCycle) =
      𝒞η.category.globalDimension *
        rawCycleSum 𝒞η source.diagram source.primalBoundary source.turnedOver
          sourceCycle := by
  classical
  unfold rawCycleSum
  calc
    (∑ targetLabeling,
      ordinaryKirbyWeight 𝒞η.category targetLabeling *
        characterWeight 𝒞η target.turnedOver targetLabeling
          (transport.mapCycle sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.primalBoundary target.turnedOver
            targetLabeling (transport.mapCycle sourceCycle)).graph) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category source.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η target.turnedOver
            (coordinates.mergeLabeling pair.1 pair.2)
            (transport.mapCycle sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η target.diagram target.primalBoundary target.turnedOver
              (coordinates.mergeLabeling pair.1 pair.2)
              (transport.mapCycle sourceCycle)).graph := by
        symm
        apply Fintype.sum_equiv
          (coordinates.labelingEquiv 𝒞η.category.simples.Simple)
        intro pair
        rfl
    _ =
      ∑ sourceLabeling,
        ∑ newLabel,
          (𝒞η.category.simples.quantumDimension newLabel *
            𝒞η.category.simples.quantumDimension newLabel) *
          (ordinaryKirbyWeight 𝒞η.category sourceLabeling *
            characterWeight 𝒞η source.turnedOver sourceLabeling sourceCycle *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.primalBoundary source.turnedOver
                sourceLabeling sourceCycle).graph) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        apply Finset.sum_congr rfl
        intro newLabel _
        rw [addedTwoHandle_ordinaryKirbyWeight,
          addedTwoHandle_characterWeight,
          twoThreeBirth_graphicalFactor]
        ring
    _ =
      𝒞η.category.globalDimension *
        ∑ sourceLabeling,
          ordinaryKirbyWeight 𝒞η.category sourceLabeling *
            characterWeight 𝒞η source.turnedOver sourceLabeling sourceCycle *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.primalBoundary source.turnedOver
                sourceLabeling sourceCycle).graph := by
        apply Eq.trans ?_ (Finset.mul_sum ..).symm
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        rw [← Finset.sum_mul]
        change
          𝒞η.category.globalDimension *
              (ordinaryKirbyWeight 𝒞η.category sourceLabeling *
                characterWeight 𝒞η source.turnedOver
                  sourceLabeling sourceCycle *
                canonicalRibbonGraphicalEvaluation 𝒞η.category
                  (canonicalRoleAwareGraphCompiler
                    𝒞η source.diagram source.primalBoundary
                    source.turnedOver sourceLabeling sourceCycle).graph) =
            _
        rfl

theorem oneTwoBirth_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoBirth)
    (homology : MoveHomologyTransport source target)
    (coordinates :
      AddedTwoHandleCoordinates source target homology.tham)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    evaluateCycle 𝒞η
        source.diagram source.primalBoundary source.turnedOver sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.primalBoundary target.turnedOver
          (homology.tham.mapCycle sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  unfold evaluateCycle
  rw [oneTwoBirth_rawCycleSum 𝒞η coordinates sourceCycle]
  unfold thamDefinition511Normalization
  rw [counts.2.2]

theorem twoThree_normalization_cancels
    (D : K) (D_ne_zero : D ≠ 0)
    (hOne hTwo hThree : ℕ)
    (raw : K) :
    thamDefinition511Normalization D (hOne + 1) hTwo hThree *
        (D * raw) =
      thamDefinition511Normalization D hOne hTwo hThree * raw := by
  unfold thamDefinition511Normalization
  rw [pow_succ]
  field_simp

theorem twoThreeBirth_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeBirth)
    (homology : MoveHomologyTransport source target)
    (coordinates :
      AddedTwoHandleCoordinates source target homology.tham)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    evaluateCycle 𝒞η
        source.diagram source.primalBoundary source.turnedOver sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.primalBoundary target.turnedOver
          (homology.tham.mapCycle sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  unfold evaluateCycle
  rw [twoThreeBirth_rawCycleSum 𝒞η coordinates sourceCycle]
  rw [counts.1, counts.2.1, counts.2.2]
  exact
    (twoThree_normalization_cancels
      𝒞η.category.globalDimension
      (egno_globalDimension_ne_zero 𝒞η.category)
      source.diagram.handles.hThree
      source.diagram.handles.hTwo
      source.diagram.handles.hOne
      (rawCycleSum 𝒞η source.diagram source.primalBoundary
        source.turnedOver sourceCycle)).symm

theorem removedTwoHandle_ordinaryKirbyWeight
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (targetLabeling : TwoHandleLabeling 𝒞 target.diagram)
    (removedLabel : 𝒞.simples.Simple) :
    ordinaryKirbyWeight 𝒞
        (coordinates.mergeLabeling targetLabeling removedLabel) =
      ordinaryKirbyWeight 𝒞 targetLabeling *
        𝒞.simples.quantumDimension removedLabel := by
  classical
  unfold ordinaryKirbyWeight
  calc
    (∏ i,
      𝒞.simples.quantumDimension
        (coordinates.mergeLabeling targetLabeling removedLabel i)) =
      ∏ i : Fin target.diagram.handles.hTwo ⊕ Unit,
        𝒞.simples.quantumDimension
          (match i with
          | .inl old => targetLabeling old
          | .inr _ => removedLabel) := by
      symm
      apply Fintype.prod_equiv coordinates.indexEquiv
      intro i
      cases i with
      | inl old =>
          simp [RemovedTwoHandleCoordinates.mergeLabeling]
      | inr new =>
          obtain rfl : new = () := Subsingleton.elim _ _
          simp [RemovedTwoHandleCoordinates.mergeLabeling]
    _ =
      (∏ i,
        𝒞.simples.quantumDimension (targetLabeling i)) *
        𝒞.simples.quantumDimension removedLabel := by
      simp

theorem removedTwoHandle_characterWeight
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    characterWeight 𝒞η source.turnedOver
        (coordinates.mergeLabeling targetLabeling removedLabel)
        (coordinates.safeCycle sourceCycle) =
      characterWeight 𝒞η target.turnedOver targetLabeling
        (transport.mapCycle (coordinates.safeCycle sourceCycle)) := by
  classical
  unfold characterWeight
  have unitEquality :
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling targetLabeling removedLabel i)) ^
            ((coordinates.safeCycle sourceCycle).1 i)) =
        ∏ i,
          (𝒞η.character.value (targetLabeling i)) ^
            ((transport.mapCycle
              (coordinates.safeCycle sourceCycle)).1 i) := by
    calc
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling targetLabeling removedLabel i)) ^
            ((coordinates.safeCycle sourceCycle).1 i)) =
        ∏ i : Fin target.diagram.handles.hTwo ⊕ Unit,
          match i with
          | .inl old =>
              (𝒞η.character.value (targetLabeling old)) ^
                ((transport.mapCycle
                  (coordinates.safeCycle sourceCycle)).1 old)
          | .inr _ => 1 := by
            symm
            apply Fintype.prod_equiv coordinates.indexEquiv
            intro i
            cases i with
            | inl old =>
                simp [RemovedTwoHandleCoordinates.mergeLabeling,
                  coordinates.transportedOldCoefficient]
            | inr new =>
                obtain rfl : new = () := Subsingleton.elim _ _
                simp [RemovedTwoHandleCoordinates.mergeLabeling,
                  coordinates.safe_newCoefficientZero]
      _ =
        ∏ i,
          (𝒞η.character.value (targetLabeling i)) ^
            ((transport.mapCycle
              (coordinates.safeCycle sourceCycle)).1 i) := by
          simp
  exact congrArg (fun unit : Kˣ => (unit : K)) unitEquality

theorem oneTwoDeath_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η source.diagram source.primalBoundary source.turnedOver
          (coordinates.mergeLabeling targetLabeling removedLabel)
          (coordinates.safeCycle sourceCycle)).graph =
      specialCutMeridianClosedValue 𝒞η.category removedLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.primalBoundary target.turnedOver
            targetLabeling
            (transport.mapCycle (coordinates.safeCycle sourceCycle))).graph := by
  have interpreted :=
    shum_framedRibbonCoherence
      (oneTwoDeath_hasTypedGraphicalNormalForm
        𝒞η coordinates sourceCycle targetLabeling removedLabel)
  unfold canonicalRibbonGraphicalEvaluation
  rw [interpreted]
  exact closedComposeExpression_scalar _ _

theorem twoThreeDeath_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η source.diagram source.primalBoundary source.turnedOver
          (coordinates.mergeLabeling targetLabeling removedLabel)
          (coordinates.safeCycle sourceCycle)).graph =
      𝒞η.category.simples.quantumDimension removedLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.primalBoundary target.turnedOver
            targetLabeling
            (transport.mapCycle (coordinates.safeCycle sourceCycle))).graph := by
  have interpreted :=
    shum_framedRibbonCoherence
      (twoThreeDeath_hasTypedGraphicalNormalForm
        𝒞η coordinates sourceCycle targetLabeling removedLabel)
  unfold canonicalRibbonGraphicalEvaluation
  rw [interpreted, closedComposeExpression_scalar]
  have localValue :
      𝒞η.category.closedScalar
          (ordinaryKirbyLoopExpression
            𝒞η.category removedLabel).interpret =
        𝒞η.category.simples.quantumDimension removedLabel := by
    unfold ordinaryKirbyLoopExpression
    simp only [RibbonExpression.interpret]
    rw [ribbonTraceMorphism_identity,
      𝒞η.category.closedScalar_smul_identity]
  rw [localValue]

theorem oneTwoDeath_rawCycleSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    rawCycleSum 𝒞η source.diagram source.primalBoundary source.turnedOver
        (coordinates.safeCycle sourceCycle) =
      rawCycleSum 𝒞η target.diagram target.primalBoundary target.turnedOver
        (transport.mapCycle (coordinates.safeCycle sourceCycle)) := by
  classical
  unfold rawCycleSum
  calc
    (∑ sourceLabeling,
      ordinaryKirbyWeight 𝒞η.category sourceLabeling *
        characterWeight 𝒞η source.turnedOver sourceLabeling
          (coordinates.safeCycle sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.primalBoundary source.turnedOver
            sourceLabeling (coordinates.safeCycle sourceCycle)).graph) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category target.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η source.turnedOver
            (coordinates.mergeLabeling pair.1 pair.2)
            (coordinates.safeCycle sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η source.diagram source.primalBoundary source.turnedOver
              (coordinates.mergeLabeling pair.1 pair.2)
              (coordinates.safeCycle sourceCycle)).graph := by
        symm
        apply Fintype.sum_equiv
          (coordinates.labelingEquiv 𝒞η.category.simples.Simple)
        intro pair
        rfl
    _ =
      ∑ targetLabeling,
        ∑ removedLabel,
          (𝒞η.category.simples.quantumDimension removedLabel *
            specialCutMeridianClosedValue 𝒞η.category removedLabel) *
          (ordinaryKirbyWeight 𝒞η.category targetLabeling *
            characterWeight 𝒞η target.turnedOver targetLabeling
              (transport.mapCycle (coordinates.safeCycle sourceCycle)) *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η target.diagram target.primalBoundary target.turnedOver
                targetLabeling
                (transport.mapCycle
                  (coordinates.safeCycle sourceCycle))).graph) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro targetLabeling _
        apply Finset.sum_congr rfl
        intro removedLabel _
        rw [removedTwoHandle_ordinaryKirbyWeight,
          removedTwoHandle_characterWeight,
          oneTwoDeath_graphicalFactor]
        ring
    _ =
      ∑ targetLabeling,
        ordinaryKirbyWeight 𝒞η.category targetLabeling *
          characterWeight 𝒞η target.turnedOver targetLabeling
            (transport.mapCycle (coordinates.safeCycle sourceCycle)) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η target.diagram target.primalBoundary target.turnedOver
              targetLabeling
              (transport.mapCycle
                (coordinates.safeCycle sourceCycle))).graph := by
        apply Finset.sum_congr rfl
        intro targetLabeling _
        rw [← Finset.sum_mul]
        rw [specialCutMeridianSum_eq_one
          𝒞η.category (egno_tensorUnitQuantumDimension 𝒞η.category)]
        simp

theorem twoThreeDeath_rawCycleSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    rawCycleSum 𝒞η source.diagram source.primalBoundary source.turnedOver
        (coordinates.safeCycle sourceCycle) =
      𝒞η.category.globalDimension *
        rawCycleSum 𝒞η target.diagram target.primalBoundary target.turnedOver
          (transport.mapCycle (coordinates.safeCycle sourceCycle)) := by
  classical
  unfold rawCycleSum
  calc
    (∑ sourceLabeling,
      ordinaryKirbyWeight 𝒞η.category sourceLabeling *
        characterWeight 𝒞η source.turnedOver sourceLabeling
          (coordinates.safeCycle sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.primalBoundary source.turnedOver
            sourceLabeling (coordinates.safeCycle sourceCycle)).graph) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category target.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η source.turnedOver
            (coordinates.mergeLabeling pair.1 pair.2)
            (coordinates.safeCycle sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η source.diagram source.primalBoundary source.turnedOver
              (coordinates.mergeLabeling pair.1 pair.2)
              (coordinates.safeCycle sourceCycle)).graph := by
        symm
        apply Fintype.sum_equiv
          (coordinates.labelingEquiv 𝒞η.category.simples.Simple)
        intro pair
        rfl
    _ =
      ∑ targetLabeling,
        ∑ removedLabel,
          (𝒞η.category.simples.quantumDimension removedLabel *
            𝒞η.category.simples.quantumDimension removedLabel) *
          (ordinaryKirbyWeight 𝒞η.category targetLabeling *
            characterWeight 𝒞η target.turnedOver targetLabeling
              (transport.mapCycle (coordinates.safeCycle sourceCycle)) *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η target.diagram target.primalBoundary target.turnedOver
                targetLabeling
                (transport.mapCycle
                  (coordinates.safeCycle sourceCycle))).graph) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro targetLabeling _
        apply Finset.sum_congr rfl
        intro removedLabel _
        rw [removedTwoHandle_ordinaryKirbyWeight,
          removedTwoHandle_characterWeight,
          twoThreeDeath_graphicalFactor]
        ring
    _ =
      𝒞η.category.globalDimension *
        ∑ targetLabeling,
          ordinaryKirbyWeight 𝒞η.category targetLabeling *
            characterWeight 𝒞η target.turnedOver targetLabeling
              (transport.mapCycle (coordinates.safeCycle sourceCycle)) *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η target.diagram target.primalBoundary target.turnedOver
                targetLabeling
                (transport.mapCycle
                  (coordinates.safeCycle sourceCycle))).graph := by
        apply Eq.trans ?_ (Finset.mul_sum ..).symm
        apply Finset.sum_congr rfl
        intro targetLabeling _
        rw [← Finset.sum_mul]
        change
          𝒞η.category.globalDimension *
              (ordinaryKirbyWeight 𝒞η.category targetLabeling *
                characterWeight 𝒞η target.turnedOver targetLabeling
                  (transport.mapCycle
                    (coordinates.safeCycle sourceCycle)) *
                canonicalRibbonGraphicalEvaluation 𝒞η.category
                  (canonicalRoleAwareGraphCompiler
                    𝒞η target.diagram target.primalBoundary
                    target.turnedOver targetLabeling
                    (transport.mapCycle
                      (coordinates.safeCycle sourceCycle))).graph) =
            _
        rfl

theorem removedTwoHandle_mappedSafe_sameClass
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    thamCycleClass target.turnedOver
        (transport.mapCycle (coordinates.safeCycle sourceCycle)) =
      thamCycleClass target.turnedOver
        (transport.mapCycle sourceCycle) := by
  have mapped :=
    congrArg transport.inducedH₂
      (coordinates.safeCycle_sameClass sourceCycle)
  exact mapped

theorem oneTwoDeath_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoDeath)
    (homology : MoveHomologyTransport source target)
    (coordinates :
      RemovedTwoHandleCoordinates source target homology.tham)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    evaluateCycle 𝒞η
        source.diagram source.primalBoundary source.turnedOver sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.primalBoundary target.turnedOver
          (homology.tham.mapCycle sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  calc
    evaluateCycle 𝒞η source.diagram source.primalBoundary
        source.turnedOver sourceCycle =
      evaluateCycle 𝒞η source.diagram source.primalBoundary
        source.turnedOver (coordinates.safeCycle sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η source.diagram source.primalBoundary source.turnedOver
        sourceCycle (coordinates.safeCycle sourceCycle)
        (coordinates.safeCycle_sameClass sourceCycle).symm
    _ =
      evaluateCycle 𝒞η target.diagram target.primalBoundary
        target.turnedOver
        (homology.tham.mapCycle (coordinates.safeCycle sourceCycle)) := by
      unfold evaluateCycle thamDefinition511Normalization
      rw [oneTwoDeath_rawCycleSum 𝒞η coordinates sourceCycle]
      rw [counts.2.2]
    _ =
      evaluateCycle 𝒞η target.diagram target.primalBoundary
        target.turnedOver (homology.tham.mapCycle sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η target.diagram target.primalBoundary target.turnedOver
        (homology.tham.mapCycle (coordinates.safeCycle sourceCycle))
        (homology.tham.mapCycle sourceCycle)
        (removedTwoHandle_mappedSafe_sameClass coordinates sourceCycle)

theorem twoThreeDeath_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeDeath)
    (homology : MoveHomologyTransport source target)
    (coordinates :
      RemovedTwoHandleCoordinates source target homology.tham)
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    evaluateCycle 𝒞η
        source.diagram source.primalBoundary source.turnedOver sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.primalBoundary target.turnedOver
          (homology.tham.mapCycle sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  calc
    evaluateCycle 𝒞η source.diagram source.primalBoundary
        source.turnedOver sourceCycle =
      evaluateCycle 𝒞η source.diagram source.primalBoundary
        source.turnedOver (coordinates.safeCycle sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η source.diagram source.primalBoundary source.turnedOver
        sourceCycle (coordinates.safeCycle sourceCycle)
        (coordinates.safeCycle_sameClass sourceCycle).symm
    _ =
      evaluateCycle 𝒞η target.diagram target.primalBoundary
        target.turnedOver
        (homology.tham.mapCycle (coordinates.safeCycle sourceCycle)) := by
      unfold evaluateCycle
      rw [twoThreeDeath_rawCycleSum 𝒞η coordinates sourceCycle]
      unfold thamDefinition511Normalization
      rw [counts.2.2, pow_succ]
      field_simp
    _ =
      evaluateCycle 𝒞η target.diagram target.primalBoundary
        target.turnedOver (homology.tham.mapCycle sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η target.diagram target.primalBoundary target.turnedOver
        (homology.tham.mapCycle (coordinates.safeCycle sourceCycle))
        (homology.tham.mapCycle sourceCycle)
        (removedTwoHandle_mappedSafe_sameClass coordinates sourceCycle)

end

end TwistedYetter.Kirby.Final.Proofs
