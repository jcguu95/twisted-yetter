import TwistedYetter.Kirby.Final.Proofs.IntrinsicDottedBoundaryFactor
import TwistedYetter.Kirby.Final.Semantics.Independent.EntranceAxioms

/-!
# Representative independence through intrinsic dotted cuts

This is the corrected route.  Component colours, internal graphical
forward/dual polarity, and dotted-cut input/output incidence are never
identified.  The THAM degree-three-chain coefficient supplies the character
exponent once; dotted direction supplies only the boundary partition used to
form an output-to-input ratio.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
One topologically realized intrinsic cut exhibits the actual compiled closed
graph as a linear exterior context applied to the interpreted cut morphism.
-/
theorem canonicalEvaluation_factorizes_through_intrinsicDottedCut
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (cut : IntrinsicDottedCutTangle diagram
      (presentation.cut.punctureWord dotted role))
    (regluing :
      IntrinsicDottedCutRegluesToDiagram
        diagram presentation dotted role cut) :
    ∃ exterior :
        (simpleLabelWordObject 𝒞
              (dottedInboundLabelWord 𝒞 diagram labeling
                (presentation.cut.punctureWord dotted role)) ⟶
          simpleLabelWordObject 𝒞
              (dottedOutboundLabelWord 𝒞 diagram labeling
                (presentation.cut.punctureWord dotted role))) →ₗ[K] K,
      canonicalRibbonGraphicalEvaluation 𝒞
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞 diagram presentation labeling)) =
        exterior (intrinsicDottedCutMorphism 𝒞 diagram labeling cut) := by
  obtain ⟨context, isotopy⟩ :=
    intrinsicDottedCutRegluing_hasTypedGraphicalInterpretation
      𝒞 diagram presentation labeling dotted role cut regluing
  let exterior :
      (simpleLabelWordObject 𝒞
            (dottedInboundLabelWord 𝒞 diagram labeling
              (presentation.cut.punctureWord dotted role)) ⟶
        simpleLabelWordObject 𝒞
            (dottedOutboundLabelWord 𝒞 diagram labeling
              (presentation.cut.punctureWord dotted role))) →ₗ[K] K :=
    𝒞.unitEndLinearEquiv.symm.toLinearMap.comp
      context.interpretLinearMap
  refine ⟨exterior, ?_⟩
  have interpreted := shum_framedRibbonCoherence isotopy
  have plugged := context.plug_interpret
    (intrinsicDottedCutMorphism 𝒞 diagram labeling cut)
  have graph_eq_context :
      compileCutOpenExteriorMorphism 𝒞 diagram presentation labeling =
        context.interpretLinearMap
          (intrinsicDottedCutMorphism 𝒞 diagram labeling cut) :=
    interpreted.symm.trans plugged
  change
    𝒞.closedScalar
        (compileCutOpenExteriorMorphism 𝒞 diagram presentation labeling) =
      𝒞.closedScalar
        (context.interpretLinearMap
          (intrinsicDottedCutMorphism 𝒞 diagram labeling cut))
  exact congrArg 𝒞.closedScalar graph_eq_context

/--
For one dotted one-handle, its THAM boundary-row character factor acts
trivially on the actual canonical closed evaluation.
-/
theorem twoOneBoundaryCharacterFactor_absorbs_canonicalEvaluation
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (one : Fin diagram.handles.hOne)
    (exponent : ℤ) :
    (((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * exponent) : Kˣ) : K) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram presentation labeling))) =
      canonicalRibbonGraphicalEvaluation 𝒞η.category
        (.morphism
          (compileCutOpenExteriorMorphism
            𝒞η.category diagram presentation labeling)) := by
  let dotted := diagram.handles.oneHandleIndex one
  obtain ⟨cut, regluing⟩ :=
    standardIntrinsicDottedCutRealization
      diagram presentation dotted.1 dotted.2
  obtain ⟨exterior, factorization⟩ :=
    canonicalEvaluation_factorizes_through_intrinsicDottedCut
      𝒞η.category diagram presentation labeling
        dotted.1 dotted.2 cut regluing
  rw [factorization]
  exact twoOneBoundaryCharacterFactor_absorbs_in_linearContext
    𝒞η diagram presentation labeling one exponent cut exterior

/-- The THAM boundary coordinate is the incidence pairing with a one-chain. -/
theorem intrinsic_thamBoundaryThree_apply_eq_sum_incidence
    (diagram : SpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) :
    primal.thamBoundaryThree oneChain two =
      ∑ one : Fin diagram.handles.hOne,
        twoOneIncidence diagram one two * oneChain one := by
  classical
  unfold PrimalDegreeThreeBoundaryData.thamBoundaryThree
    transposeAddHom coordinatePairing primalBoundaryTwo
  change
    (∑ one : Fin diagram.handles.hOne,
      diagram.handles.boundaryTwo
          (coordinateUnit diagram.handles.hTwo two) one * oneChain one) =
      ∑ one : Fin diagram.handles.hOne,
        twoOneIncidence diagram one two * oneChain one
  apply Finset.sum_congr rfl
  intro one _
  rfl

/-- Adding one THAM boundary multiplies the character weight by its factor. -/
theorem intrinsic_characterWeight_add_thamBoundaryAsCycle
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    characterWeight 𝒞η labeling
        (cycle + thamBoundaryAsCycle primal oneChain) =
      characterWeight 𝒞η labeling cycle *
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (primal.thamBoundaryThree oneChain two) : Kˣ) : K) := by
  unfold characterWeight
  change
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (cycle.1 two + primal.thamBoundaryThree oneChain two) : Kˣ) : K) =
      ((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^ cycle.1 two : Kˣ) : K) *
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            primal.thamBoundaryThree oneChain two : Kˣ) : K)
  simp only [zpow_add, Finset.prod_mul_distrib, Units.val_mul]

private theorem intrinsic_finset_prod_zpow_eq_zpow_sum
    {G : Type*} [CommGroup G]
    {ι : Type*}
    (items : Finset ι)
    (base : G)
    (exponent : ι → ℤ) :
    (∏ item ∈ items, base ^ exponent item) =
      base ^ (∑ item ∈ items, exponent item) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items not_mem ih =>
      simp [not_mem, ih, zpow_add]

/--
The complete THAM boundary factor is the product of the individual dotted
one-handle boundary-row factors.  No puncture-level exponent occurs here.
-/
theorem thamBoundaryCharacterProduct_eq_twoOneProduct
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (primal.thamBoundaryThree oneChain two) : Kˣ) : K) =
      ∏ one : Fin diagram.handles.hOne,
        (((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K)) := by
  classical
  have boundary_expansion :
      (∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (primal.thamBoundaryThree oneChain two)) =
        ∏ two : Fin diagram.handles.hTwo,
          ∏ one : Fin diagram.handles.hOne,
            𝒞η.character.value (labeling two) ^
              (twoOneIncidence diagram one two * oneChain one) := by
    apply Finset.prod_congr rfl
    intro two _
    rw [intrinsic_thamBoundaryThree_apply_eq_sum_incidence
      diagram primal oneChain two]
    exact
      (intrinsic_finset_prod_zpow_eq_zpow_sum
        (Finset.univ : Finset (Fin diagram.handles.hOne))
        (𝒞η.character.value (labeling two))
        (fun one =>
          twoOneIncidence diagram one two * oneChain one)).symm
  rw [boundary_expansion]
  rw [Finset.prod_comm]
  simpa using
    Units.coe_prod
      (fun one : Fin diagram.handles.hOne =>
        ∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (twoOneIncidence diagram one two * oneChain one))
      Finset.univ

private theorem intrinsic_finset_prod_mul_eq_of_each_mul_eq
    {ι M : Type*} [CommMonoid M]
    (items : Finset ι)
    (factor : ι → M)
    (value : M)
    (absorbs : ∀ item ∈ items, factor item * value = value) :
    (∏ item ∈ items, factor item) * value = value := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items not_mem ih =>
      rw [Finset.prod_insert not_mem]
      rw [mul_assoc, ih]
      · exact absorbs item (Finset.mem_insert_self item items)
      · intro other other_mem
        exact absorbs other (Finset.mem_insert_of_mem other_mem)

/-- The product of every dotted boundary-row factor is invisible. -/
theorem twoOneBoundaryCharacterProduct_absorbs_canonicalEvaluation
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    (∏ one : Fin diagram.handles.hOne,
      (((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K))) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram presentation labeling)) =
      canonicalRibbonGraphicalEvaluation 𝒞η.category
        (.morphism
          (compileCutOpenExteriorMorphism
            𝒞η.category diagram presentation labeling)) := by
  apply intrinsic_finset_prod_mul_eq_of_each_mul_eq
    (Finset.univ : Finset (Fin diagram.handles.hOne))
  intro one _
  exact twoOneBoundaryCharacterFactor_absorbs_canonicalEvaluation
    𝒞η diagram presentation labeling one (oneChain one)

/-- Fixed-label evaluation is unchanged after adding a THAM boundary. -/
theorem intrinsic_characterWeight_mul_canonicalEvaluation_add_boundary
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    characterWeight 𝒞η labeling
          (cycle + thamBoundaryAsCycle primal oneChain) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram presentation labeling)) =
      characterWeight 𝒞η labeling cycle *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram presentation labeling)) := by
  let graphicalValue :=
    canonicalRibbonGraphicalEvaluation 𝒞η.category
      (.morphism
        (compileCutOpenExteriorMorphism
          𝒞η.category diagram presentation labeling))
  let boundaryFactor :=
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (primal.thamBoundaryThree oneChain two) : Kˣ) : K)
  calc
    _ =
        (characterWeight 𝒞η labeling cycle *
          boundaryFactor) * graphicalValue := by
      rw [intrinsic_characterWeight_add_thamBoundaryAsCycle
        𝒞η diagram primal labeling cycle oneChain]
    _ =
        characterWeight 𝒞η labeling cycle *
          (boundaryFactor * graphicalValue) := by
      rw [mul_assoc]
    _ =
        characterWeight 𝒞η labeling cycle *
          ((∏ one : Fin diagram.handles.hOne,
            (((∏ two : Fin diagram.handles.hTwo,
              𝒞η.character.value (labeling two) ^
                (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K))) *
            graphicalValue) := by
      dsimp only [boundaryFactor]
      rw [thamBoundaryCharacterProduct_eq_twoOneProduct
        𝒞η diagram primal labeling oneChain]
    _ = _ := by
      dsimp only [graphicalValue]
      rw [twoOneBoundaryCharacterProduct_absorbs_canonicalEvaluation
        𝒞η diagram presentation labeling oneChain]

/-- The complete frozen cycle evaluator is unchanged by one boundary. -/
theorem intrinsic_evaluateCycle_add_thamBoundaryAsCycle
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (cycle : ThamTwoCycles primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    evaluateCycle 𝒞η diagram presentation primal
        (cycle + thamBoundaryAsCycle primal oneChain) =
      evaluateCycle 𝒞η diagram presentation primal cycle := by
  unfold evaluateCycle
  apply congrArg
  apply Finset.sum_congr rfl
  intro labeling _
  dsimp only [canonicalRoleAwareGraphCompiler]
  let graphicalValue :=
    canonicalRibbonGraphicalEvaluation 𝒞η.category
      (.morphism
          (compileCutOpenExteriorMorphism
          𝒞η.category diagram presentation labeling))
  calc
    ordinaryKirbyWeight 𝒞η.category labeling *
          characterWeight 𝒞η labeling
            (cycle + thamBoundaryAsCycle primal oneChain) *
        graphicalValue =
      ordinaryKirbyWeight 𝒞η.category labeling *
        (characterWeight 𝒞η labeling
            (cycle + thamBoundaryAsCycle primal oneChain) *
          graphicalValue) := by
      rw [mul_assoc]
    _ =
      ordinaryKirbyWeight 𝒞η.category labeling *
        (characterWeight 𝒞η labeling cycle * graphicalValue) := by
      rw [intrinsic_characterWeight_mul_canonicalEvaluation_add_boundary
        𝒞η diagram presentation primal labeling cycle oneChain]
    _ =
      ordinaryKirbyWeight 𝒞η.category labeling *
          characterWeight 𝒞η labeling cycle * graphicalValue := by
      rw [mul_assoc]

/--
The corrected frozen role-aware evaluator depends only on the THAM-side
second-homology class.
-/
theorem intrinsicFrozenFrontendRepresentativeIndependence
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (primal : PrimalDegreeThreeBoundaryData diagram) :
    RepresentativeIndependenceStatement
      𝒞η diagram presentation primal := by
  intro left right same_class
  change
    (QuotientAddGroup.mk'
      (thamBoundaryAsCycle primal).range) left =
      (QuotientAddGroup.mk'
        (thamBoundaryAsCycle primal).range) right at same_class
  obtain ⟨boundary, boundary_mem, left_add_boundary_eq⟩ :=
    (QuotientAddGroup.mk'_eq_mk'
      (thamBoundaryAsCycle primal).range).mp same_class
  obtain ⟨oneChain, oneChain_eq⟩ := boundary_mem
  subst boundary
  rw [← left_add_boundary_eq]
  exact (intrinsic_evaluateCycle_add_thamBoundaryAsCycle
    𝒞η diagram presentation primal left oneChain).symm

end

end TwistedYetter.Kirby.Final.Proofs
