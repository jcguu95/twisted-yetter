import TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler

/-!
# Cycle-section integral-character Kirby colours

The category-bound compiler fixes the simple labels, ordinary weights,
strand objects, duals, and framing twist.  Its remaining coefficient field is
still too broad: an arbitrary function of a presentation, marked class,
component, and simple object could be supplied.

This module records the older cycle-section implementation.  The marked class
is lifted noncomputably to one degree-two cycle, and its raw coefficients are
used as component exponents.
A monoidal natural automorphism of the identity supplies one invertible
scalar on every recorded simple object.  The coefficient on an ordinary
two-handle component is then forced to be

`ordinaryWeight * simpleScalar ^ integralCoordinate`.

This file alone does not prove an `H₂`-level invariant: one still needs the
dual-chain representative-independence theorem.  The former primal
cancelling 2--3 calculation is not a counterexample to that theorem.
-/

namespace TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RightRigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
One source-backed integral two-cycle model inside one Kirby presentation.

`cycleRepresentative` lands in the actual degree-two cycles of the pinned
handle-chain complex. `cycle_class_sound` then forces its homology class to be
the requested geometric class. The representative is intentionally only a
normalized choice function, not an additive section: an additive section of
cycles onto integral homology need not exist when `H₂` has torsion.

The component index is no longer duplicated here. It is mandatory data of
`SpecialKirbyPresentation`, so the handle chain and framed-link component
coordinates cannot drift apart between evaluator instances.
-/
structure IntegralTwoHandleCycleModel
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation H2) where
  cycleRepresentative :
    H2 → topology.handleChain.complex.cycles 2
  cycle_zero_sound :
    cycleRepresentative 0 = 0
  cycle_class_sound :
    (alpha : H2) →
      topology.h2ModelEquiv
          (topology.handleChain.complex.homologyπ 2
            (cycleRepresentative alpha)) =
        alpha
  cycleCertificateHash : String
  cycle_certificate_hash_shape :
    RawPresentation.sha256Shape cycleCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace IntegralTwoHandleCycleModel

/--
Choose a representative of one homology class using the epimorphic homology
quotient.  The zero class is normalized to the zero cycle.

No additive splitting is asserted or used.
-/
noncomputable def normalizedCycleRepresentative
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    topology.handleChain.complex.cycles 2 := by
  classical
  by_cases zeroClass : alpha = 0
  · exact 0
  · exact Function.surjInv
      ((ModuleCat.epi_iff_surjective
        (topology.handleChain.complex.homologyπ 2)).mp inferInstance)
      (topology.h2ModelEquiv.symm alpha)

@[simp]
theorem normalizedCycleRepresentative_zero
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation H2) :
    normalizedCycleRepresentative topology 0 = 0 := by
  simp [normalizedCycleRepresentative]

theorem normalizedCycleRepresentative_class
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    topology.h2ModelEquiv
        (topology.handleChain.complex.homologyπ 2
          (normalizedCycleRepresentative topology alpha)) =
      alpha := by
  classical
  by_cases zeroClass : alpha = 0
  · subst alpha
    simp
  · rw [normalizedCycleRepresentative]
    simp only [zeroClass, ↓reduceDIte]
    rw [Function.rightInverse_surjInv
      ((ModuleCat.epi_iff_surjective
        (topology.handleChain.complex.homologyπ 2)).mp inferInstance)]
    exact topology.h2ModelEquiv.apply_symm_apply alpha

/--
A normalized choice of cycle representative derived from one presentation.

This construction is canonical only as a Lean choice term.  It is not by
itself evidence that the cycle-colour evaluation descends to homology; that
requires the dual-boundary graphical realization.
-/
noncomputable def canonical
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation H2) :
    IntegralTwoHandleCycleModel topology where
  cycleRepresentative := normalizedCycleRepresentative topology
  cycle_zero_sound := normalizedCycleRepresentative_zero topology
  cycle_class_sound := normalizedCycleRepresentative_class topology
  cycleCertificateHash := topology.h2ModelCertificateHash
  cycle_certificate_hash_shape := topology.h2_model_certificate_hash_shape
  sourceRefs := [
    "mathlib:HomologicalComplex.homologyPi-epi",
    "presentation:" ++ topology.formal.pinnedSourceHash
  ]
  exactScope :=
    "Normalized integral cycle representative selected from the pinned "
      ++ "handle-chain homology quotient; two-handle coordinates use the "
      ++ "presentation's mandatory component index."
  sourceScopeCaveat :=
    "This is a normalized choice term, not by itself a homology-level "
      ++ "evaluator. Representative descent must be proved in the dual "
      ++ "handle complex using the primal dotted one-handle / Tham k=3 "
      ++ "vacuum projector."

/--
The degree-two handle coefficients of the certified cycle representative.
-/
noncomputable def handleCoefficients
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2) :
    Fin topology.counts.h2 → ℤ :=
  topology.handleChain.degreeTwoBasis.hom
    (topology.handleChain.complex.iCycles 2
      (model.cycleRepresentative alpha))

/--
The exponent attached to one raw component.

Every two-handle-bearing framed component, ordinary or specially dotted,
receives the coefficient of its corresponding handle in the certified cycle
representative. Dotted one-handle components receive zero.
-/
noncomputable def componentExponent
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2)
    (component : ComponentSpec) : ℤ :=
  match topology.twoHandleIndex? component.componentId with
  | none => 0
  | some index => model.handleCoefficients alpha index

/-- The zero marked class gives exponent zero on every component. -/
theorem componentExponent_zero
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation H2}
    (model : IntegralTwoHandleCycleModel topology)
    (component : ComponentSpec) :
    model.componentExponent 0 component = 0 := by
  have coefficients_zero : model.handleCoefficients 0 = 0 := by
    simp only [handleCoefficients, model.cycle_zero_sound]
    rw [map_zero, map_zero]
    rfl
  unfold componentExponent
  split
  · rfl
  · simpa using congrFun coefficients_zero _

/-- A recorded two-handle component reads the matching cycle coefficient. -/
theorem two_handle_component_exponent
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2)
    (index : Fin topology.counts.h2) :
    model.componentExponent alpha (topology.twoHandleComponent index) =
      model.handleCoefficients alpha index := by
  simp [componentExponent, topology.two_handle_index_roundtrip index]

/-- Dotted one-handle components carry no degree-two cycle coefficient. -/
theorem dotted_component_exponent
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2)
    (component : ComponentSpec)
    (dotted : component.role = .dotted) :
    model.componentExponent alpha component = 0 := by
  simp [componentExponent,
    topology.dotted_component_unindexed component dotted]

end IntegralTwoHandleCycleModel

/--
A certified integral cycle representative for every admitted presentation of
one manifold. Each presentation may have different handle coordinates; the
separately compiled handle-chain move controls their transport.
-/
structure IntegralCycleRepresentativeSystem
    (H2 : Type uH) [AddCommGroup H2] where
  model :
    (topology : SpecialKirbyPresentation H2) →
      IntegralTwoHandleCycleModel topology
  systemCertificateHash : String
  system_certificate_hash_shape :
    RawPresentation.sha256Shape systemCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace IntegralCycleRepresentativeSystem

/--
A normalized choice system for every admitted presentation.

All representatives map to the requested quotient class, but the choices
are neither natural under Kirby moves nor safe inputs for the naive
cycle-colour evaluator.  This object is bookkeeping only.
-/
noncomputable def canonical
    (systemCertificateHash : String)
    (system_certificate_hash_shape :
      RawPresentation.sha256Shape systemCertificateHash = true)
    (H2 : Type uH) [AddCommGroup H2] :
    IntegralCycleRepresentativeSystem H2 where
  model := IntegralTwoHandleCycleModel.canonical
  systemCertificateHash := systemCertificateHash
  system_certificate_hash_shape := system_certificate_hash_shape
  sourceRefs := [
    "mathlib:HomologicalComplex.homologyPi-epi",
    "presentation:mandatory-two-handle-component-index"
  ]
  exactScope :=
    "All admitted presentations use their pinned two-handle component index "
      ++ "and a normalized representative of the requested integral H2 class."
  sourceScopeCaveat :=
    "Representative selection is noncomputable, not additive, and not "
      ++ "evaluation-independent. It must not authorize a homology-level "
      ++ "claim; use cancellation-safe geometric basis data instead."

end IntegralCycleRepresentativeSystem

/--
A monoidal natural automorphism generator with its exact scalar action on
the admitted simple-object representatives.

Naturality is carried by `automorphism`.  The two displayed equations are
the tensor and unit laws.  `simple_scalar_sound` prevents a free character
table from being substituted for the categorical automorphism.
-/
structure TensorAutomorphismGenerator
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)) where
  automorphism : (𝟭 C) ≅ (𝟭 C)
  tensor_hom :
    (left right : C) →
      automorphism.hom.app (left ⊗ right) =
        automorphism.hom.app left ⊗ₘ automorphism.hom.app right
  unit_hom :
    automorphism.hom.app (𝟙_ C) = 𝟙 (𝟙_ C)
  simpleScalar : S → Kˣ
  simple_scalar_sound :
    (simple : S) →
      automorphism.hom.app (categoryData.slidingData.simple simple) =
        (simpleScalar simple : K) •
          𝟙 (categoryData.slidingData.simple simple)
  categorySnapshotHash : String
  category_snapshot_hash_sound :
    categorySnapshotHash = categoryData.categorySnapshotHash
  automorphismCertificateHash : String
  automorphism_certificate_hash_shape :
    RawPresentation.sha256Shape automorphismCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

/--
A selected genuinely nontrivial tensor automorphism.

Nontriviality is not asserted for every admissible category. It is explicit
category-domain data: the caller supplies one simple object on which the
verified categorical automorphism acts by a scalar different from one.
-/
structure NontrivialTensorAutomorphismGenerator
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)) where
  generator : TensorAutomorphismGenerator categoryData
  witnessSimple : S
  witness_nontrivial :
    generator.simpleScalar witnessSimple ≠ 1

namespace NontrivialTensorAutomorphismGenerator

/-- The selected character cannot definitionally collapse to the identity control. -/
theorem not_all_scalars_one
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (selected : NontrivialTensorAutomorphismGenerator categoryData) :
    ¬ ∀ simple, selected.generator.simpleScalar simple = 1 := by
  intro allTrivial
  exact selected.witness_nontrivial (allTrivial selected.witnessSimple)

end NontrivialTensorAutomorphismGenerator

namespace TensorAutomorphismGenerator

/--
The identity tensor automorphism, derived without a caller-supplied scalar
table or certificate.

This is the formal untwisted control. Its certificate provenance is the
category's already pinned coherence certificate, while all mathematical
laws below are kernel-checked consequences of identity morphisms.
-/
noncomputable def trivial
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)) :
    TensorAutomorphismGenerator categoryData where
  automorphism := Iso.refl (𝟭 C)
  tensor_hom := by
    intro left right
    simp
  unit_hom := by
    simp
  simpleScalar := fun _ => 1
  simple_scalar_sound := by
    intro simple
    simp
  categorySnapshotHash := categoryData.categorySnapshotHash
  category_snapshot_hash_sound := rfl
  automorphismCertificateHash := categoryData.coherenceCertificateHash
  automorphism_certificate_hash_shape :=
    categoryData.coherence_certificate_hash_shape
  sourceRefs := categoryData.sourceRefs
  exactScope :=
    "Identity monoidal natural automorphism control; every simple scalar is 1."
  sourceScopeCaveat :=
    "This control is alpha-insensitive and does not witness a nontrivial "
      ++ "universal-grading character or nontrivial tensor automorphism."

/-- Scalar by which the integral power of the generator acts on one simple. -/
def scalarPower
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (generator : TensorAutomorphismGenerator categoryData)
    (simple : S)
    (exponent : ℤ) : K :=
  ↑((generator.simpleScalar simple) ^ exponent : Kˣ)

theorem scalarPower_zero
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (generator : TensorAutomorphismGenerator categoryData)
    (simple : S) :
    generator.scalarPower simple 0 = 1 := by
  simp [scalarPower]

theorem scalarPower_add
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (generator : TensorAutomorphismGenerator categoryData)
    (simple : S)
    (left right : ℤ) :
    generator.scalarPower simple (left + right) =
      generator.scalarPower simple left *
        generator.scalarPower simple right := by
  simp [scalarPower, zpow_add₀]

/-- Every simple scalar in the identity control is definitionally one. -/
theorem trivial_simpleScalar
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (simple : S) :
    (trivial categoryData).simpleScalar simple = 1 := by
  rfl

/-- Every integral power of the identity control acts by the scalar one. -/
theorem trivial_scalarPower
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (simple : S)
    (exponent : ℤ) :
    (trivial categoryData).scalarPower simple exponent = 1 := by
  simp [scalarPower, trivial]

end TensorAutomorphismGenerator

/--
The only integral-character coefficient formula admitted by this module.

The ordinary category weight and automorphism scalar are both selected from
the same `categoryData`.  The exponent is derived from the exact
presentation-specific integral cycle representative.
-/
noncomputable def integralCharacterWeights
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (cycleSystem : IntegralCycleRepresentativeSystem H2)
    (generator : TensorAutomorphismGenerator categoryData) :
    HomologicalKirbyColorWeights categoryData H2 where
  coefficient := fun topology alpha component simple =>
    categoryData.slidingData.weight simple *
      generator.scalarPower simple
        ((cycleSystem.model topology).componentExponent alpha component)
  zero_class_sound := by
    intro topology component simple
    rw [(cycleSystem.model topology).componentExponent_zero]
    simp [TensorAutomorphismGenerator.scalarPower]
  categorySnapshotHash := generator.categorySnapshotHash
  category_snapshot_hash_sound :=
    generator.category_snapshot_hash_sound
  coefficientCertificateHash := cycleSystem.systemCertificateHash
  coefficient_certificate_hash_shape :=
    cycleSystem.system_certificate_hash_shape
  markingCertificateHash := cycleSystem.systemCertificateHash
  marking_certificate_hash_shape :=
    cycleSystem.system_certificate_hash_shape
  sourceRefs := cycleSystem.sourceRefs ++ generator.sourceRefs
  exactScope :=
    cycleSystem.exactScope ++ " " ++ generator.exactScope
  sourceScopeCaveat :=
    cycleSystem.sourceScopeCaveat ++ " " ++
      generator.sourceScopeCaveat

theorem integral_character_coefficient_formula
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (cycleSystem : IntegralCycleRepresentativeSystem H2)
    (generator : TensorAutomorphismGenerator categoryData)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (component : ComponentSpec)
    (simple : S) :
    (integralCharacterWeights cycleSystem generator).coefficient
        topology alpha component simple =
          categoryData.slidingData.weight simple *
        generator.scalarPower simple
          ((cycleSystem.model topology).componentExponent alpha component) := by
  rfl

/--
The identity-generator control is untwisted for every marked class, not only
at `alpha = 0`.

This theorem is a reusable oracle against accidental dependence on cycle
coordinates in the ordinary control path.
-/
theorem trivial_generator_coefficient_is_ordinary
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (cycleSystem : IntegralCycleRepresentativeSystem H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (component : ComponentSpec)
    (simple : S) :
    (integralCharacterWeights cycleSystem
        (TensorAutomorphismGenerator.trivial categoryData)).coefficient
          topology alpha component simple =
      categoryData.slidingData.weight simple := by
  simp [integralCharacterWeights,
    TensorAutomorphismGenerator.trivial_scalarPower]

/--
Presentation compiler for the not-yet-certified cycle-section route.

Its category-bound predecessor is derived below.  Callers cannot supply a
different `HomologicalKirbyColorWeights` value after the cycle model and
tensor automorphism have been fixed.  This restriction does not prove
descent to `H₂`, so this compiler cannot support a final invariant claim
until the dual-boundary bridge is integrated.
-/
structure IntegralCharacterBoundPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2]
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData) where
  cycleSystemCertificateHash : String
  cycle_system_certificate_hash_shape :
    RawPresentation.sha256Shape cycleSystemCertificateHash = true
  selectedGenerator : NontrivialTensorAutomorphismGenerator categoryData
  resolver :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        (integralCharacterWeights
          (IntegralCycleRepresentativeSystem.canonical
            cycleSystemCertificateHash
            cycle_system_certificate_hash_shape H2)
          selectedGenerator.generator).toComponentExpansion
          topology) →
      LabelledComponentResolver
        (integralCharacterWeights
          (IntegralCycleRepresentativeSystem.canonical
            cycleSystemCertificateHash
            cycle_system_certificate_hash_shape H2)
          selectedGenerator.generator)
        topology labeling
  eventSemantics :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        (integralCharacterWeights
          (IntegralCycleRepresentativeSystem.canonical
            cycleSystemCertificateHash
            cycle_system_certificate_hash_shape H2)
          selectedGenerator.generator).toComponentExpansion
          topology) →
      WindowedCategoricalEventSemantics
        topology.formal.raw
        (strandObject (resolver topology alpha labeling))
        algebra.framedKink.twist
  diagramCertificateHash :
    SpecialKirbyPresentation H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (decorationCertificateHash topology) = true
  sourceRefs : List String
  exactEventScope : String
  sourceScopeCaveat : String

namespace IntegralCharacterBoundPresentationCompiler

/-- Derive the category-bound compiler without a free coefficient function. -/
noncomputable def toCategoryBound
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      IntegralCharacterBoundPresentationCompiler
        categoryData H2 algebra) :
    CategoryBoundPresentationCompiler
      categoryData H2 algebra where
  weights :=
    integralCharacterWeights
      (IntegralCycleRepresentativeSystem.canonical
        compiler.cycleSystemCertificateHash
        compiler.cycle_system_certificate_hash_shape H2)
      compiler.selectedGenerator.generator
  resolver := compiler.resolver
  eventSemantics := compiler.eventSemantics
  diagramCertificateHash := compiler.diagramCertificateHash
  diagram_certificate_hash_shape :=
    compiler.diagram_certificate_hash_shape
  decorationCertificateHash := compiler.decorationCertificateHash
  decoration_certificate_hash_shape :=
    compiler.decoration_certificate_hash_shape
  sourceRefs :=
    compiler.sourceRefs ++
      (IntegralCycleRepresentativeSystem.canonical
        compiler.cycleSystemCertificateHash
        compiler.cycle_system_certificate_hash_shape H2).sourceRefs ++
      compiler.selectedGenerator.generator.sourceRefs
  exactEventScope := compiler.exactEventScope
  sourceScopeCaveat :=
    compiler.sourceScopeCaveat ++ " " ++
      (IntegralCycleRepresentativeSystem.canonical
        compiler.cycleSystemCertificateHash
        compiler.cycle_system_certificate_hash_shape H2).sourceScopeCaveat
        ++ " " ++
      compiler.selectedGenerator.generator.sourceScopeCaveat

/-- The derived coefficients are definitionally the integral-character formula. -/
theorem weights_are_integral_character_weights
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      IntegralCharacterBoundPresentationCompiler
      categoryData H2 algebra) :
    compiler.toCategoryBound.weights =
      integralCharacterWeights
        (IntegralCycleRepresentativeSystem.canonical
          compiler.cycleSystemCertificateHash
          compiler.cycle_system_certificate_hash_shape H2)
        compiler.selectedGenerator.generator := by
  rfl

/-- Every admitted final presentation compiler carries a witnessed nontrivial character. -/
theorem selected_generator_is_nontrivial
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      IntegralCharacterBoundPresentationCompiler
        categoryData H2 algebra) :
    ¬ ∀ simple,
      compiler.selectedGenerator.generator.simpleScalar simple = 1 :=
  compiler.selectedGenerator.not_all_scalars_one

end IntegralCharacterBoundPresentationCompiler

end TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
