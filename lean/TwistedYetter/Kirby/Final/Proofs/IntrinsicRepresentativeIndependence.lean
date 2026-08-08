import TwistedYetter.Kirby.Final.Proofs.IntrinsicDottedBoundaryFactor
import TwistedYetter.Kirby.Final.Semantics.Independent.EntranceAxioms

/-!
# Representative independence through intrinsic dotted cuts

This is the corrected route.  Component colours, internal graphical
forward/dual polarity, and dotted-cut input/output incidence are never
identified.  A visible primal one-handle cochain supplies one integer
coefficient; dotted direction supplies only the boundary partition used to
prove that the corresponding `∂₂ᵀ` coboundary factor is invisible.
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

/-- The visible THAM coboundary is the incidence pairing with a one-cochain. -/
theorem intrinsic_thamVisibleCoboundary_apply_eq_sum_incidence
    (diagram : SpecialKirbyDiagram)
    (oneChain : HandleChainGroup diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) :
    thamVisibleCoboundary diagram oneChain two =
      ∑ one : Fin diagram.handles.hOne,
        twoOneIncidence diagram one two * oneChain one := by
  classical
  unfold thamVisibleCoboundary transposeAddHom coordinatePairing
    primalBoundaryTwo
  change
    (∑ one : Fin diagram.handles.hOne,
      diagram.handles.boundaryTwo
          (coordinateUnit diagram.handles.hTwo two) one * oneChain one) =
      ∑ one : Fin diagram.handles.hOne,
        twoOneIncidence diagram one two * oneChain one
  apply Finset.sum_congr rfl
  intro one _
  rfl

/-- Adding one visible THAM coboundary multiplies the character weight by its factor. -/
theorem intrinsic_characterWeight_add_thamVisibleCoboundary
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (coefficients : ThamTwoHandleCoefficients diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    characterWeight 𝒞η labeling
        (coefficients + thamVisibleCoboundary diagram oneChain) =
      characterWeight 𝒞η labeling coefficients *
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (thamVisibleCoboundary diagram oneChain two) : Kˣ) : K) := by
  unfold characterWeight
  change
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (coefficients two + thamVisibleCoboundary diagram oneChain two) : Kˣ) : K) =
      ((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^ coefficients two : Kˣ) : K) *
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            thamVisibleCoboundary diagram oneChain two : Kˣ) : K)
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
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (thamVisibleCoboundary diagram oneChain two) : Kˣ) : K) =
      ∏ one : Fin diagram.handles.hOne,
        (((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K)) := by
  classical
  have boundary_expansion :
      (∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (thamVisibleCoboundary diagram oneChain two)) =
        ∏ two : Fin diagram.handles.hTwo,
          ∏ one : Fin diagram.handles.hOne,
            𝒞η.character.value (labeling two) ^
              (twoOneIncidence diagram one two * oneChain one) := by
    apply Finset.prod_congr rfl
    intro two _
    rw [intrinsic_thamVisibleCoboundary_apply_eq_sum_incidence
      diagram oneChain two]
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

/-- Fixed-label evaluation is unchanged after adding a visible coboundary. -/
theorem intrinsic_characterWeight_mul_canonicalEvaluation_add_boundary
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (coefficients : ThamTwoHandleCoefficients diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    characterWeight 𝒞η labeling
          (coefficients + thamVisibleCoboundary diagram oneChain) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram presentation labeling)) =
      characterWeight 𝒞η labeling coefficients *
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
        (thamVisibleCoboundary diagram oneChain two) : Kˣ) : K)
  calc
    _ =
        (characterWeight 𝒞η labeling coefficients *
          boundaryFactor) * graphicalValue := by
      rw [intrinsic_characterWeight_add_thamVisibleCoboundary
        𝒞η diagram labeling coefficients oneChain]
    _ =
        characterWeight 𝒞η labeling coefficients *
          (boundaryFactor * graphicalValue) := by
      rw [mul_assoc]
    _ =
        characterWeight 𝒞η labeling coefficients *
          ((∏ one : Fin diagram.handles.hOne,
            (((∏ two : Fin diagram.handles.hTwo,
              𝒞η.character.value (labeling two) ^
                (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K))) *
            graphicalValue) := by
      dsimp only [boundaryFactor]
      rw [thamBoundaryCharacterProduct_eq_twoOneProduct
        𝒞η diagram labeling oneChain]
    _ = _ := by
      dsimp only [graphicalValue]
      rw [twoOneBoundaryCharacterProduct_absorbs_canonicalEvaluation
        𝒞η diagram presentation labeling oneChain]

/-- The complete evaluator is unchanged by one visible coboundary. -/
theorem intrinsic_evaluateCoefficients_add_thamVisibleCoboundary
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (coefficients : ThamTwoHandleCoefficients diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    evaluateCoefficients 𝒞η diagram presentation
        (coefficients + thamVisibleCoboundary diagram oneChain) =
      evaluateCoefficients 𝒞η diagram presentation coefficients := by
  unfold evaluateCoefficients
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
            (coefficients + thamVisibleCoboundary diagram oneChain) *
        graphicalValue =
      ordinaryKirbyWeight 𝒞η.category labeling *
        (characterWeight 𝒞η labeling
            (coefficients + thamVisibleCoboundary diagram oneChain) *
          graphicalValue) := by
      rw [mul_assoc]
    _ =
      ordinaryKirbyWeight 𝒞η.category labeling *
        (characterWeight 𝒞η labeling coefficients * graphicalValue) := by
      rw [intrinsic_characterWeight_mul_canonicalEvaluation_add_boundary
        𝒞η diagram presentation labeling coefficients oneChain]
    _ =
      ordinaryKirbyWeight 𝒞η.category labeling *
          characterWeight 𝒞η labeling coefficients * graphicalValue := by
      rw [mul_assoc]

/--
The corrected frozen role-aware evaluator depends only on the visible ambient
THAM marking class.
-/
theorem intrinsicFrozenFrontendRepresentativeIndependence
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram) :
    RepresentativeIndependenceStatement
      𝒞η diagram presentation := by
  intro left right same_class
  change
    (QuotientAddGroup.mk'
      (thamVisibleCoboundary diagram).range) left =
      (QuotientAddGroup.mk'
        (thamVisibleCoboundary diagram).range) right at same_class
  obtain ⟨boundary, boundary_mem, left_add_boundary_eq⟩ :=
    (QuotientAddGroup.mk'_eq_mk'
      (thamVisibleCoboundary diagram).range).mp same_class
  obtain ⟨oneChain, oneChain_eq⟩ := boundary_mem
  subst boundary
  rw [← left_add_boundary_eq]
  exact (intrinsic_evaluateCoefficients_add_thamVisibleCoboundary
    𝒞η diagram presentation left oneChain).symm

end

end TwistedYetter.Kirby.Final.Proofs
