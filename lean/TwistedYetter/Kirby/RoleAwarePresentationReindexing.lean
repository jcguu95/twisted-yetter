import TwistedYetter.Kirby.RoleAwarePresentationEvaluation

/-!
# Reindexing the external second-homology coordinate group

A role-aware presentation contains an equivalence from its intrinsic
handle-chain homology to an external coordinate group.  Reindexing composes
that equivalence with a new additive equivalence.  It changes no link,
handle-chain, trace, dotted-cut geometry, or evaluator term.
-/

namespace TwistedYetter.Kirby.RoleAwarePresentationReindexing

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwareRepresentativeIndependence
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation

universe uK uC vC uH uH'

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Change only the external homology coordinate group. -/
noncomputable def reindexSpecialKirbyPresentation
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation :
      KirbyCompleteness.SpecialKirbyPresentation H2) :
    KirbyCompleteness.SpecialKirbyPresentation H2' :=
  { presentation with
    h2ModelEquiv := presentation.h2ModelEquiv.trans change }

/-- Reindex a canonical presentation without changing its diagram. -/
noncomputable def reindexCanonicalPresentation
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation : CanonicalPresentation H2) :
    CanonicalPresentation H2' :=
  { presentation with
    topology :=
      reindexSpecialKirbyPresentation change presentation.topology }

private noncomputable def reindexGeneratorGeometry
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation : CanonicalPresentation H2)
    (generator :
      Fin presentation.topology.counts.turnedOver.h3)
    (geometry :
      DottedBoundaryGeometry.GeneratorGeometry presentation generator) :
    DottedBoundaryGeometry.GeneratorGeometry
      (reindexCanonicalPresentation change presentation) generator where
  dottedComponentIndex := geometry.dottedComponentIndex
  dottedComponent := geometry.dottedComponent
  dotted_component_def := geometry.dotted_component_def
  dotted_role := geometry.dotted_role
  punctureBoundary := geometry.punctureBoundary
  dotted_absent_from_punctures := geometry.dotted_absent_from_punctures
  puncture_ids_indexed_in_component_registry :=
    geometry.puncture_ids_indexed_in_component_registry
  puncture_ids_are_two_handles := geometry.puncture_ids_are_two_handles
  exteriorContext := geometry.exteriorContext
  dotted_absent_from_exterior := geometry.dotted_absent_from_exterior
  factorization := geometry.factorization
  incidence_sound := geometry.incidence_sound
  geometryCertificateHash := geometry.geometryCertificateHash
  geometry_certificate_hash_shape :=
    geometry.geometry_certificate_hash_shape
  sourceRefs := geometry.sourceRefs
  sourceLocator := geometry.sourceLocator

private noncomputable def reindexGeometrySystem
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation : CanonicalPresentation H2)
    (system : DottedBoundaryGeometry.GeometrySystem presentation) :
    DottedBoundaryGeometry.GeometrySystem
      (reindexCanonicalPresentation change presentation) where
  geometry := fun generator =>
    reindexGeneratorGeometry change presentation generator
      (system.geometry generator)
  generator_component_injective := system.generator_component_injective
  every_raw_dotted_component_covered :=
    system.every_raw_dotted_component_covered

private noncomputable def reindexSimultaneousGeometry
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation : CanonicalPresentation H2)
    (geometry :
      SimultaneousDottedCutGeometry.Geometry presentation) :
    SimultaneousDottedCutGeometry.Geometry
      (reindexCanonicalPresentation change presentation) where
  cutDiagram := geometry.cutDiagram
  erase_isotopy := geometry.erase_isotopy
  every_dotted_cut_exactly_once := geometry.every_dotted_cut_exactly_once
  every_special_cut_is_dotted := geometry.every_special_cut_is_dotted
  dotted_absent_from_ordinary_nodes :=
    geometry.dotted_absent_from_ordinary_nodes
  punctures_are_two_handles := geometry.punctures_are_two_handles

private noncomputable def reindexGeneratorCutWindow
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation : CanonicalPresentation H2)
    (dottedGeometry :
      DottedBoundaryGeometry.GeometrySystem presentation)
    (simultaneousGeometry :
      SimultaneousDottedCutGeometry.Geometry presentation)
    (generator :
      Fin presentation.topology.counts.turnedOver.h3)
    (window :
      GeneratorCutWindow presentation dottedGeometry
        simultaneousGeometry generator) :
    GeneratorCutWindow
      (reindexCanonicalPresentation change presentation)
      (reindexGeometrySystem change presentation dottedGeometry)
      (reindexSimultaneousGeometry change presentation simultaneousGeometry)
      generator where
  context := window.context
  factorization := window.factorization

/--
Reindex the complete role-aware presentation.

Every proof-relevant geometry field is transported because all structural
diagram projections remain definitionally unchanged.
-/
noncomputable def reindex
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (change : H2 ≃+ H2')
    (presentation : Presentation H2) :
    Presentation H2' :=
  { canonicalPresentation :=
      reindexCanonicalPresentation change presentation.canonicalPresentation
    dottedGeometry :=
      reindexGeometrySystem change presentation.canonicalPresentation
        presentation.dottedGeometry
    simultaneousGeometry :=
      reindexSimultaneousGeometry change presentation.canonicalPresentation
        presentation.simultaneousGeometry
    generatorCutWindow := fun generator =>
      reindexGeneratorCutWindow change
        presentation.canonicalPresentation presentation.dottedGeometry
        presentation.simultaneousGeometry generator
        (presentation.generatorCutWindow generator) }

/--
Reindexing does not change the role-aware evaluation.

The class lies in the intrinsic handle-chain homology, which is literally
unchanged.  Only its external coordinate equivalence is replaced.
-/
theorem roleAwareEvalH2_reindex
    {H2 : Type uH} {H2' : Type uH'}
    [AddCommGroup H2] [AddCommGroup H2']
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (change : H2 ≃+ H2')
    (presentation : Presentation H2)
    (alpha :
      presentation.canonicalPresentation.topology.handleChain.SecondHomology) :
    roleAwareEvalH2 𝒞 η presentation alpha =
      roleAwareEvalH2 𝒞 η (reindex change presentation) alpha := by
  let reindexed := reindex change presentation
  let sourceCycle :=
    presentation.canonicalPresentation.chosenCycle alpha
  let targetCycle :=
    reindexed.canonicalPresentation.chosenCycle alpha
  have hLabel
      (labeling :
        CanonicalPresentation.OrdinaryLabeling
          (S := S) presentation.canonicalPresentation) :
      CanonicalPresentation.roleAwareLabelOf 𝒞
          presentation.canonicalPresentation labeling =
        CanonicalPresentation.roleAwareLabelOf 𝒞
          reindexed.canonicalPresentation labeling := by
    funext componentId
    unfold
      CanonicalPresentation.roleAwareLabelOf
      CanonicalPresentation.roleAwareLabelOfWithUnit
    simp [reindexed, reindex, reindexCanonicalPresentation,
      reindexSpecialKirbyPresentation]
    split <;> rfl
  have hExponent
      (component : TwistedYetter.Kirby.Presentation.ComponentSpec) :
      presentation.canonicalPresentation.cycleComponentExponent
          sourceCycle component =
        reindexed.canonicalPresentation.cycleComponentExponent
          sourceCycle component := by
    unfold
      CanonicalPresentation.cycleComponentExponent
      KirbyCompleteness.SpecialKirbyPresentation.cycleComponentExponent
      KirbyCompleteness.SpecialKirbyPresentation.cycleHandleCoefficients
    simp [reindexed, reindex, reindexCanonicalPresentation,
      reindexSpecialKirbyPresentation]
    split <;> rfl
  have hWeight
      (labeling :
        CanonicalPresentation.OrdinaryLabeling
          (S := S) presentation.canonicalPresentation) :
      CanonicalPresentation.roleAwareGlobalWeight
          𝒞 η presentation.canonicalPresentation sourceCycle labeling =
        CanonicalPresentation.roleAwareGlobalWeight
          𝒞 η reindexed.canonicalPresentation sourceCycle labeling := by
    unfold CanonicalPresentation.roleAwareGlobalWeight
    apply Finset.prod_congr rfl
    intro index _
    unfold CanonicalPresentation.cycleComponentWeight
    rw [hExponent]
    congr 2
  have hTerm
      (labeling :
        CanonicalPresentation.OrdinaryLabeling
          (S := S) presentation.canonicalPresentation) :
      CanonicalPresentation.roleAwareTermDiagram
          𝒞 η presentation.canonicalPresentation
            presentation.simultaneousGeometry labeling =
        CanonicalPresentation.roleAwareTermDiagram
          𝒞 η reindexed.canonicalPresentation
            reindexed.simultaneousGeometry labeling := by
    unfold CanonicalPresentation.roleAwareTermDiagram
    rw [hLabel]
    rfl
  have hStructural :
      CanonicalPresentation.roleAwareCycleEval
          𝒞 η presentation.canonicalPresentation
            presentation.simultaneousGeometry sourceCycle =
        CanonicalPresentation.roleAwareCycleEval
          𝒞 η reindexed.canonicalPresentation
            reindexed.simultaneousGeometry sourceCycle := by
    unfold
      CanonicalPresentation.roleAwareCycleEval
      CanonicalPresentation.roleAwareNormalizationFactor
    congr 1
    unfold
      CanonicalPresentation.roleAwareRawNumerator
      CanonicalPresentation.roleAwareLinearDiagram
    apply congrArg 𝒞.toFusionCategoryData.closedScalar
    simp only [LinearDiagram.eval_weightedSum]
    apply Finset.sum_congr rfl
    intro labeling _
    rw [hWeight labeling, hTerm labeling]
  have hSameClass :
      reindexed.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 sourceCycle =
        reindexed.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 targetCycle := by
    change
      presentation.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 sourceCycle =
        reindexed.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 targetCycle
    rw [presentation.canonicalPresentation.chosenCycle_class]
    rw [reindexed.canonicalPresentation.chosenCycle_class]
  calc
    roleAwareEvalH2 𝒞 η presentation alpha =
        CanonicalPresentation.roleAwareCycleEval
          𝒞 η presentation.canonicalPresentation
            presentation.simultaneousGeometry sourceCycle := rfl
    _ =
        CanonicalPresentation.roleAwareCycleEval
          𝒞 η reindexed.canonicalPresentation
            reindexed.simultaneousGeometry sourceCycle := hStructural
    _ =
        CanonicalPresentation.roleAwareCycleEval
          𝒞 η reindexed.canonicalPresentation
            reindexed.simultaneousGeometry targetCycle :=
      TwistedYetter.Kirby.RoleAwareRepresentativeIndependence.Presentation.roleAwareCycleEval_respects_homology_class
        𝒞 η reindexed sourceCycle targetCycle hSameClass
    _ = roleAwareEvalH2 𝒞 η reindexed alpha := rfl

end TwistedYetter.Kirby.RoleAwarePresentationReindexing
