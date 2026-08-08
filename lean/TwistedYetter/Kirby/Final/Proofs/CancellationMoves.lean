import TwistedYetter.Kirby.Final.Proofs.CleanBandSlides
import TwistedYetter.Kirby.Final.Proofs.RepresentativeIndependence
import TwistedYetter.Kirby.Final.Proofs.CancellationTraceFactorization
import TwistedYetter.Kirby.Final.Proofs.TwoThreeTraceFactorization

/-!
# Frozen-frontend cancellation moves

The topology entrance supplies only fixed-label local graphical normal forms.
This file proves the character, finite-sum, and THAM-normalization calculations.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

theorem addedTwoHandle_ordinaryKirbyWeight
    (𝒞 : BundledPremodularCategory K)
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
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    characterWeight 𝒞η
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (transport.mapCoefficients sourceCycle) =
      characterWeight 𝒞η
        sourceLabeling sourceCycle := by
  classical
  unfold characterWeight
  have unitEquality :
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling sourceLabeling newLabel i)) ^
            (transport.mapCoefficients sourceCycle i)) =
        ∏ i,
          (𝒞η.character.value (sourceLabeling i)) ^
            (sourceCycle i) := by
    calc
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling sourceLabeling newLabel i)) ^
            (transport.mapCoefficients sourceCycle i)) =
        ∏ i : Fin source.diagram.handles.hTwo ⊕ Unit,
          match i with
          | .inl old =>
              (𝒞η.character.value (sourceLabeling old)) ^
                (sourceCycle old)
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
            (sourceCycle i) := by
          simp
  exact congrArg (fun unit : Kˣ => (unit : K)) unitEquality

/--
Compiler-locality obligation for a standard one--two birth.

The topology hypothesis is now obtained from the exact category-neutral
serialized normal form.  What remains to prove is that the finite-event
compiler sends its three-event prefix to the special-cut meridian and sends
the unchanged suffix to the source expression.
-/
theorem oneTwoBirth_hasTypedGraphicalNormalForm
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoBirth)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesOneTwoBirthMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    (canonicalRoleAwareGraphCompiler
        𝒞η target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (transport.mapCoefficients sourceCycle)).interpret =
      (closedComposeExpression
        (specialCutMeridianExpression 𝒞η.category newLabel)
        (canonicalRoleAwareGraphCompiler
          𝒞η source.diagram source.cut
          sourceLabeling sourceCycle)).interpret := by
  exact standardOneTwoBirth_compiledExteriorMorphism
    𝒞η.category
    (OneTwoGraphCoordinates.ofAdded coordinates)
    (OneTwoGraphCoordinates.ofAdded_matchesCanonicalMeridian
      coordinates coordinateBinding)
    normalForm
    sourceLabeling newLabel

theorem oneTwoBirth_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoBirth)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesOneTwoBirthMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η target.diagram target.cut
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (transport.mapCoefficients sourceCycle)) =
      specialCutMeridianClosedValue 𝒞η.category newLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.cut
            sourceLabeling sourceCycle) := by
  have interpreted :=
    oneTwoBirth_hasTypedGraphicalNormalForm
      𝒞η script kind coordinates coordinateBinding normalForm
        sourceCycle sourceLabeling newLabel
  unfold canonicalRibbonGraphicalEvaluation
  rw [interpreted]
  exact closedComposeExpression_scalar _ _

theorem twoThreeBirth_hasTypedGraphicalNormalForm
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeBirth)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesTwoThreeBirthComponent)
    (normalForm : IsStandardTwoThreeBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    (canonicalRoleAwareGraphCompiler
        𝒞η target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (transport.mapCoefficients sourceCycle)).interpret =
      (closedComposeExpression
        (ordinaryKirbyLoopExpression 𝒞η.category newLabel)
        (canonicalRoleAwareGraphCompiler
          𝒞η source.diagram source.cut
          sourceLabeling sourceCycle)).interpret := by
  exact standardTwoThreeBirth_compiledExteriorMorphism
    𝒞η.category
    (TwoThreeGraphCoordinates.ofAdded coordinates)
    (TwoThreeGraphCoordinates.ofAdded_matches
      coordinates coordinateBinding)
    normalForm
    sourceLabeling newLabel

theorem twoThreeBirth_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeBirth)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesTwoThreeBirthComponent)
    (normalForm : IsStandardTwoThreeBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (sourceLabeling :
      TwoHandleLabeling 𝒞η.category source.diagram)
    (newLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η target.diagram target.cut
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (transport.mapCoefficients sourceCycle)) =
      𝒞η.category.simples.quantumDimension newLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.cut
            sourceLabeling sourceCycle) := by
  have interpreted :=
    twoThreeBirth_hasTypedGraphicalNormalForm
      𝒞η script kind coordinates coordinateBinding normalForm
      sourceCycle sourceLabeling newLabel
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

theorem oneTwoBirth_rawCoefficientSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoBirth)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesOneTwoBirthMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    rawCoefficientSum 𝒞η target.diagram target.cut
        (transport.mapCoefficients sourceCycle) =
      rawCoefficientSum 𝒞η source.diagram source.cut
        sourceCycle := by
  classical
  unfold rawCoefficientSum
  calc
    (∑ targetLabeling,
      ordinaryKirbyWeight 𝒞η.category targetLabeling *
        characterWeight 𝒞η targetLabeling
          (transport.mapCoefficients sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.cut
            targetLabeling (transport.mapCoefficients sourceCycle))) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category source.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η
            (coordinates.mergeLabeling pair.1 pair.2)
            (transport.mapCoefficients sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η target.diagram target.cut
              (coordinates.mergeLabeling pair.1 pair.2)
              (transport.mapCoefficients sourceCycle)) := by
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
            characterWeight 𝒞η sourceLabeling sourceCycle *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.cut
                sourceLabeling sourceCycle)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        apply Finset.sum_congr rfl
        intro newLabel _
        rw [addedTwoHandle_ordinaryKirbyWeight,
          addedTwoHandle_characterWeight,
          oneTwoBirth_graphicalFactor
            𝒞η script kind coordinates coordinateBinding normalForm]
        ring
    _ =
      ∑ sourceLabeling,
        ordinaryKirbyWeight 𝒞η.category sourceLabeling *
          characterWeight 𝒞η sourceLabeling sourceCycle *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.cut
                sourceLabeling sourceCycle) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        rw [← Finset.sum_mul]
        rw [specialCutMeridianSum_eq_one
          𝒞η.category (standard_tensorUnitQuantumDimension 𝒞η.category)]
        simp

theorem twoThreeBirth_rawCoefficientSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeBirth)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesTwoThreeBirthComponent)
    (normalForm : IsStandardTwoThreeBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    rawCoefficientSum 𝒞η target.diagram target.cut
        (transport.mapCoefficients sourceCycle) =
      𝒞η.category.globalDimension *
        rawCoefficientSum 𝒞η source.diagram source.cut
          sourceCycle := by
  classical
  unfold rawCoefficientSum
  calc
    (∑ targetLabeling,
      ordinaryKirbyWeight 𝒞η.category targetLabeling *
        characterWeight 𝒞η targetLabeling
          (transport.mapCoefficients sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.cut
            targetLabeling (transport.mapCoefficients sourceCycle))) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category source.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η
            (coordinates.mergeLabeling pair.1 pair.2)
            (transport.mapCoefficients sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η target.diagram target.cut
              (coordinates.mergeLabeling pair.1 pair.2)
              (transport.mapCoefficients sourceCycle)) := by
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
            characterWeight 𝒞η sourceLabeling sourceCycle *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.cut
                sourceLabeling sourceCycle)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        apply Finset.sum_congr rfl
        intro newLabel _
        rw [addedTwoHandle_ordinaryKirbyWeight,
          addedTwoHandle_characterWeight,
          twoThreeBirth_graphicalFactor
            𝒞η script kind coordinates coordinateBinding normalForm
            sourceCycle sourceLabeling newLabel]
        ring
    _ =
      𝒞η.category.globalDimension *
        ∑ sourceLabeling,
          ordinaryKirbyWeight 𝒞η.category sourceLabeling *
            characterWeight 𝒞η sourceLabeling sourceCycle *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η source.diagram source.cut
                sourceLabeling sourceCycle) := by
        apply Eq.trans ?_ (Finset.mul_sum ..).symm
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        rw [← Finset.sum_mul]
        change
          𝒞η.category.globalDimension *
              (ordinaryKirbyWeight 𝒞η.category sourceLabeling *
                characterWeight 𝒞η
                  sourceLabeling sourceCycle *
                canonicalRibbonGraphicalEvaluation 𝒞η.category
                  (canonicalRoleAwareGraphCompiler
                    𝒞η source.diagram source.cut sourceLabeling sourceCycle)) =
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
    (coordinateBinding :
      coordinates.MatchesOneTwoBirthMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    evaluateCoefficients 𝒞η
        source.diagram source.cut sourceCycle =
      evaluateCoefficients 𝒞η
        target.diagram target.cut
          (homology.tham.mapCoefficients sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  unfold evaluateCoefficients
  rw [oneTwoBirth_rawCoefficientSum
    𝒞η script kind coordinates coordinateBinding normalForm sourceCycle]
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
    (coordinateBinding :
      coordinates.MatchesTwoThreeBirthComponent)
    (normalForm : IsStandardTwoThreeBirth source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    evaluateCoefficients 𝒞η
        source.diagram source.cut sourceCycle =
      evaluateCoefficients 𝒞η
        target.diagram target.cut
          (homology.tham.mapCoefficients sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  unfold evaluateCoefficients
  rw [twoThreeBirth_rawCoefficientSum
    𝒞η script kind coordinates coordinateBinding normalForm sourceCycle]
  rw [counts.1, counts.2.1, counts.2.2]
  exact
    (twoThree_normalization_cancels
      𝒞η.category.globalDimension
      (eno_globalDimension_ne_zero 𝒞η.category)
      source.diagram.handles.hThree
      source.diagram.handles.hTwo
      source.diagram.handles.hOne
      (rawCoefficientSum 𝒞η source.diagram source.cut sourceCycle)).symm

theorem removedTwoHandle_ordinaryKirbyWeight
    (𝒞 : BundledPremodularCategory K)
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
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    characterWeight 𝒞η
        (coordinates.mergeLabeling targetLabeling removedLabel)
        (coordinates.safeCoefficients sourceCycle) =
      characterWeight 𝒞η targetLabeling
        (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) := by
  classical
  unfold characterWeight
  have unitEquality :
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling targetLabeling removedLabel i)) ^
            (coordinates.safeCoefficients sourceCycle i)) =
        ∏ i,
          (𝒞η.character.value (targetLabeling i)) ^
            (transport.mapCoefficients
              (coordinates.safeCoefficients sourceCycle) i) := by
    calc
      (∏ i,
        (𝒞η.character.value
          (coordinates.mergeLabeling targetLabeling removedLabel i)) ^
            (coordinates.safeCoefficients sourceCycle i)) =
        ∏ i : Fin target.diagram.handles.hTwo ⊕ Unit,
          match i with
          | .inl old =>
              (𝒞η.character.value (targetLabeling old)) ^
                (transport.mapCoefficients
                  (coordinates.safeCoefficients sourceCycle) old)
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
            (transport.mapCoefficients
              (coordinates.safeCoefficients sourceCycle) i) := by
          simp
  exact congrArg (fun unit : Kˣ => (unit : K)) unitEquality

/--
The reverse compiler-locality obligation.  Its topology input is definitionally
the birth normal form with source and target exchanged.
-/
theorem oneTwoDeath_hasTypedGraphicalNormalForm
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoDeath)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesOneTwoDeathMeridian)
    (normalForm : IsStandardOneTwoDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    (canonicalRoleAwareGraphCompiler
        𝒞η source.diagram source.cut
        (coordinates.mergeLabeling targetLabeling removedLabel)
        (coordinates.safeCoefficients sourceCycle)).interpret =
      (closedComposeExpression
        (specialCutMeridianExpression 𝒞η.category removedLabel)
        (canonicalRoleAwareGraphCompiler
          𝒞η target.diagram target.cut
          targetLabeling
          (transport.mapCoefficients
            (coordinates.safeCoefficients sourceCycle)))).interpret := by
  exact standardOneTwoBirth_compiledExteriorMorphism
    𝒞η.category
    (OneTwoGraphCoordinates.ofRemoved coordinates)
    (OneTwoGraphCoordinates.ofRemoved_matchesCanonicalMeridian
      coordinates coordinateBinding)
    normalForm
    targetLabeling removedLabel

theorem oneTwoDeath_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoDeath)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesOneTwoDeathMeridian)
    (normalForm : IsStandardOneTwoDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η source.diagram source.cut
          (coordinates.mergeLabeling targetLabeling removedLabel)
          (coordinates.safeCoefficients sourceCycle)) =
      specialCutMeridianClosedValue 𝒞η.category removedLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.cut
            targetLabeling
            (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle))) := by
  have interpreted :=
    oneTwoDeath_hasTypedGraphicalNormalForm
      𝒞η script kind coordinates coordinateBinding normalForm
        sourceCycle targetLabeling removedLabel
  unfold canonicalRibbonGraphicalEvaluation
  rw [interpreted]
  exact closedComposeExpression_scalar _ _

theorem twoThreeDeath_hasTypedGraphicalNormalForm
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeDeath)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesTwoThreeDeathComponent)
    (normalForm : IsStandardTwoThreeDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    (canonicalRoleAwareGraphCompiler
        𝒞η source.diagram source.cut
        (coordinates.mergeLabeling targetLabeling removedLabel)
        (coordinates.safeCoefficients sourceCycle)).interpret =
      (closedComposeExpression
        (ordinaryKirbyLoopExpression 𝒞η.category removedLabel)
        (canonicalRoleAwareGraphCompiler
          𝒞η target.diagram target.cut
          targetLabeling
          (transport.mapCoefficients
            (coordinates.safeCoefficients sourceCycle)))).interpret := by
  exact standardTwoThreeBirth_compiledExteriorMorphism
    𝒞η.category
    (TwoThreeGraphCoordinates.ofRemoved coordinates)
    (TwoThreeGraphCoordinates.ofRemoved_matches
      coordinates coordinateBinding)
    normalForm
    targetLabeling removedLabel

theorem twoThreeDeath_graphicalFactor
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeDeath)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesTwoThreeDeathComponent)
    (normalForm : IsStandardTwoThreeDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram)
    (targetLabeling :
      TwoHandleLabeling 𝒞η.category target.diagram)
    (removedLabel : 𝒞η.category.simples.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler
          𝒞η source.diagram source.cut
          (coordinates.mergeLabeling targetLabeling removedLabel)
          (coordinates.safeCoefficients sourceCycle)) =
      𝒞η.category.simples.quantumDimension removedLabel *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η target.diagram target.cut
          targetLabeling
          (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle))) := by
  have interpreted :=
    twoThreeDeath_hasTypedGraphicalNormalForm
      𝒞η script kind coordinates coordinateBinding normalForm
      sourceCycle targetLabeling removedLabel
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

theorem oneTwoDeath_rawCoefficientSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoDeath)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesOneTwoDeathMeridian)
    (normalForm : IsStandardOneTwoDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    rawCoefficientSum 𝒞η source.diagram source.cut
        (coordinates.safeCoefficients sourceCycle) =
      rawCoefficientSum 𝒞η target.diagram target.cut
        (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) := by
  classical
  unfold rawCoefficientSum
  calc
    (∑ sourceLabeling,
      ordinaryKirbyWeight 𝒞η.category sourceLabeling *
        characterWeight 𝒞η sourceLabeling
          (coordinates.safeCoefficients sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.cut
            sourceLabeling (coordinates.safeCoefficients sourceCycle))) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category target.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η
            (coordinates.mergeLabeling pair.1 pair.2)
            (coordinates.safeCoefficients sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η source.diagram source.cut
              (coordinates.mergeLabeling pair.1 pair.2)
              (coordinates.safeCoefficients sourceCycle)) := by
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
            characterWeight 𝒞η targetLabeling
              (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η target.diagram target.cut
                targetLabeling
                (transport.mapCoefficients
                  (coordinates.safeCoefficients sourceCycle)))) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro targetLabeling _
        apply Finset.sum_congr rfl
        intro removedLabel _
        rw [removedTwoHandle_ordinaryKirbyWeight,
          removedTwoHandle_characterWeight,
          oneTwoDeath_graphicalFactor
            𝒞η script kind coordinates coordinateBinding normalForm]
        ring
    _ =
      ∑ targetLabeling,
        ordinaryKirbyWeight 𝒞η.category targetLabeling *
          characterWeight 𝒞η targetLabeling
            (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η target.diagram target.cut
              targetLabeling
              (transport.mapCoefficients
                (coordinates.safeCoefficients sourceCycle))) := by
        apply Finset.sum_congr rfl
        intro targetLabeling _
        rw [← Finset.sum_mul]
        rw [specialCutMeridianSum_eq_one
          𝒞η.category (standard_tensorUnitQuantumDimension 𝒞η.category)]
        simp

theorem twoThreeDeath_rawCoefficientSum
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeDeath)
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (coordinateBinding :
      coordinates.MatchesTwoThreeDeathComponent)
    (normalForm : IsStandardTwoThreeDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    rawCoefficientSum 𝒞η source.diagram source.cut
        (coordinates.safeCoefficients sourceCycle) =
      𝒞η.category.globalDimension *
        rawCoefficientSum 𝒞η target.diagram target.cut
          (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) := by
  classical
  unfold rawCoefficientSum
  calc
    (∑ sourceLabeling,
      ordinaryKirbyWeight 𝒞η.category sourceLabeling *
        characterWeight 𝒞η sourceLabeling
          (coordinates.safeCoefficients sourceCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler
            𝒞η source.diagram source.cut
            sourceLabeling (coordinates.safeCoefficients sourceCycle))) =
      ∑ pair :
          TwoHandleLabeling 𝒞η.category target.diagram ×
            𝒞η.category.simples.Simple,
        ordinaryKirbyWeight 𝒞η.category
            (coordinates.mergeLabeling pair.1 pair.2) *
          characterWeight 𝒞η
            (coordinates.mergeLabeling pair.1 pair.2)
            (coordinates.safeCoefficients sourceCycle) *
          canonicalRibbonGraphicalEvaluation 𝒞η.category
            (canonicalRoleAwareGraphCompiler
              𝒞η source.diagram source.cut
              (coordinates.mergeLabeling pair.1 pair.2)
              (coordinates.safeCoefficients sourceCycle)) := by
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
            characterWeight 𝒞η targetLabeling
              (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η target.diagram target.cut
                targetLabeling
                (transport.mapCoefficients
                  (coordinates.safeCoefficients sourceCycle)))) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro targetLabeling _
        apply Finset.sum_congr rfl
        intro removedLabel _
        rw [removedTwoHandle_ordinaryKirbyWeight,
          removedTwoHandle_characterWeight,
          twoThreeDeath_graphicalFactor
            𝒞η script kind coordinates coordinateBinding normalForm
            sourceCycle targetLabeling removedLabel]
        ring
    _ =
      𝒞η.category.globalDimension *
        ∑ targetLabeling,
          ordinaryKirbyWeight 𝒞η.category targetLabeling *
            characterWeight 𝒞η targetLabeling
              (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) *
            canonicalRibbonGraphicalEvaluation 𝒞η.category
              (canonicalRoleAwareGraphCompiler
                𝒞η target.diagram target.cut
                targetLabeling
                (transport.mapCoefficients
                  (coordinates.safeCoefficients sourceCycle))) := by
        apply Eq.trans ?_ (Finset.mul_sum ..).symm
        apply Finset.sum_congr rfl
        intro targetLabeling _
        rw [← Finset.sum_mul]
        change
          𝒞η.category.globalDimension *
              (ordinaryKirbyWeight 𝒞η.category targetLabeling *
                characterWeight 𝒞η targetLabeling
                  (transport.mapCoefficients
                    (coordinates.safeCoefficients sourceCycle)) *
                canonicalRibbonGraphicalEvaluation 𝒞η.category
                  (canonicalRoleAwareGraphCompiler
                    𝒞η target.diagram target.cut targetLabeling
                    (transport.mapCoefficients
                      (coordinates.safeCoefficients sourceCycle)))) =
            _
        rfl

theorem removedTwoHandle_mappedSafe_sameClass
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    thamMarkingClass
        (transport.mapCoefficients (coordinates.safeCoefficients sourceCycle)) =
      thamMarkingClass (transport.mapCoefficients sourceCycle) := by
  have mapped :=
    congrArg transport.inducedMarking
      (coordinates.safeCoefficients_sameClass sourceCycle)
  exact mapped

theorem oneTwoDeath_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .oneTwoDeath)
    (homology : MoveHomologyTransport source target)
    (coordinates :
      RemovedTwoHandleCoordinates source target homology.tham)
    (coordinateBinding :
      coordinates.MatchesOneTwoDeathMeridian)
    (normalForm : IsStandardOneTwoDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    evaluateCoefficients 𝒞η
        source.diagram source.cut sourceCycle =
      evaluateCoefficients 𝒞η
        target.diagram target.cut
          (homology.tham.mapCoefficients sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  calc
    evaluateCoefficients 𝒞η source.diagram source.cut sourceCycle =
      evaluateCoefficients 𝒞η source.diagram source.cut (coordinates.safeCoefficients sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η source.diagram source.cut
        sourceCycle (coordinates.safeCoefficients sourceCycle)
        (coordinates.safeCoefficients_sameClass sourceCycle).symm
    _ =
      evaluateCoefficients 𝒞η target.diagram target.cut
        (homology.tham.mapCoefficients (coordinates.safeCoefficients sourceCycle)) := by
      unfold evaluateCoefficients thamDefinition511Normalization
      rw [oneTwoDeath_rawCoefficientSum
        𝒞η script kind coordinates coordinateBinding normalForm sourceCycle]
      rw [counts.2.2]
    _ =
      evaluateCoefficients 𝒞η target.diagram target.cut (homology.tham.mapCoefficients sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η target.diagram target.cut
        (homology.tham.mapCoefficients (coordinates.safeCoefficients sourceCycle))
        (homology.tham.mapCoefficients sourceCycle)
        (removedTwoHandle_mappedSafe_sameClass coordinates sourceCycle)

theorem twoThreeDeath_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (kind : script.kind = .twoThreeDeath)
    (homology : MoveHomologyTransport source target)
    (coordinates :
      RemovedTwoHandleCoordinates source target homology.tham)
    (coordinateBinding :
      coordinates.MatchesTwoThreeDeathComponent)
    (normalForm : IsStandardTwoThreeDeath source.diagram target.diagram source.cut target.cut)
    (sourceCycle : ThamTwoHandleCoefficients source.diagram) :
    evaluateCoefficients 𝒞η
        source.diagram source.cut sourceCycle =
      evaluateCoefficients 𝒞η
        target.diagram target.cut
          (homology.tham.mapCoefficients sourceCycle) := by
  have counts := script.handleCountChangeIsStandard
  simp [CancellationHandleCountChangeIsStandard, kind] at counts
  calc
    evaluateCoefficients 𝒞η source.diagram source.cut sourceCycle =
      evaluateCoefficients 𝒞η source.diagram source.cut (coordinates.safeCoefficients sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η source.diagram source.cut
        sourceCycle (coordinates.safeCoefficients sourceCycle)
        (coordinates.safeCoefficients_sameClass sourceCycle).symm
    _ =
      evaluateCoefficients 𝒞η target.diagram target.cut
        (homology.tham.mapCoefficients (coordinates.safeCoefficients sourceCycle)) := by
      unfold evaluateCoefficients
      rw [twoThreeDeath_rawCoefficientSum
        𝒞η script kind coordinates coordinateBinding normalForm sourceCycle]
      unfold thamDefinition511Normalization
      rw [counts.2.2, pow_succ]
      field_simp
    _ =
      evaluateCoefficients 𝒞η target.diagram target.cut (homology.tham.mapCoefficients sourceCycle) :=
      frozenFrontendRepresentativeIndependence
        𝒞η target.diagram target.cut
        (homology.tham.mapCoefficients (coordinates.safeCoefficients sourceCycle))
        (homology.tham.mapCoefficients sourceCycle)
        (removedTwoHandle_mappedSafe_sameClass coordinates sourceCycle)

end

end TwistedYetter.Kirby.Final.Proofs
