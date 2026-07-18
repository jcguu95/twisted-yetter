import TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler

/-!
# Integral-character-bound Kirby colours

The category-bound compiler fixes the simple labels, ordinary weights,
strand objects, duals, and framing twist.  Its remaining coefficient field is
still too broad: an arbitrary function of a presentation, marked class,
component, and simple object could be supplied.

This module narrows that field for one precise scope.  The marked class is an
integral class in the `H2` model already carried by a special Kirby
presentation.  Every presentation supplies a source-backed additive choice
of integral two-cycle representative, together with a complete indexing of
ordinary framed components by the two-handle basis of the handle chain.
A monoidal natural automorphism of the identity supplies one invertible
scalar on every recorded simple object.  The coefficient on an ordinary
two-handle component is then forced to be

`ordinaryWeight * simpleScalar ^ integralCoordinate`.

This is an integral-character construction mechanism.  It is not a model of
arbitrary `H2(X; A)`, and it does not construct the presentation bases,
cycle representatives, tensor automorphism, event interpreter, or Kirby-move
realizations.  Presentations containing `speciallyDotted` components are
excluded from this direct-coordinate route until a separate, source-backed
translation into two-cycle coordinates is constructed.
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
the requested geometric class. The component index is complete for ordinary
components and is definitionally tied to the degree-two handle basis.
-/
structure IntegralTwoHandleCycleModel
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2) where
  twoHandleComponent : Fin topology.counts.h2 → ComponentSpec
  two_handle_component_mem :
    (index : Fin topology.counts.h2) →
      twoHandleComponent index ∈ topology.formal.raw.components
  two_handle_component_role :
    (index : Fin topology.counts.h2) →
      (twoHandleComponent index).role = .ordinary
  twoHandleIndex? : String → Option (Fin topology.counts.h2)
  two_handle_index_roundtrip :
    (index : Fin topology.counts.h2) →
      twoHandleIndex? (twoHandleComponent index).componentId = some index
  two_handle_index_sound :
    (componentId : String) →
    (index : Fin topology.counts.h2) →
      twoHandleIndex? componentId = some index →
        componentId = (twoHandleComponent index).componentId
  every_ordinary_component_indexed :
    (component : ComponentSpec) →
      component ∈ topology.formal.raw.components →
      component.role = .ordinary →
        ∃ index, twoHandleIndex? component.componentId = some index
  nonordinary_component_unindexed :
    (component : ComponentSpec) →
      component.role ≠ .ordinary →
        twoHandleIndex? component.componentId = none
  no_specially_dotted_components :
    (component : ComponentSpec) →
      component ∈ topology.formal.raw.components →
        component.role ≠ .speciallyDotted
  cycleRepresentative :
    H2 →+ topology.handleChain.complex.cycles 2
  cycle_class_sound :
    (alpha : H2) →
      topology.h2ModelEquiv
          (topology.handleChain.complex.homologyπ 2
            (cycleRepresentative alpha)) =
        alpha
  cycleCertificateHash : String
  cycle_certificate_hash_shape :
    RawPresentation.sha256Shape cycleCertificateHash = true
  componentIndexCertificateHash : String
  component_index_certificate_hash_shape :
    RawPresentation.sha256Shape componentIndexCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace IntegralTwoHandleCycleModel

/--
The degree-two handle coefficients of the certified cycle representative.
-/
noncomputable def handleCoefficients
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2) :
    Fin topology.counts.h2 → ℤ :=
  topology.handleChain.degreeTwoBasis.hom
    (topology.handleChain.complex.iCycles 2
      (model.cycleRepresentative alpha))

/--
The exponent attached to one raw component.

Every ordinary framed component receives the coefficient of its corresponding
two-handle in the certified cycle representative. Dotted components receive
zero. Specially dotted components are excluded by the model contract.
-/
noncomputable def componentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2)
    (component : ComponentSpec) : ℤ :=
  match model.twoHandleIndex? component.componentId with
  | none => 0
  | some index => model.handleCoefficients alpha index

/-- The zero marked class gives exponent zero on every component. -/
theorem componentExponent_zero
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology)
    (component : ComponentSpec) :
    model.componentExponent 0 component = 0 := by
  have coefficients_zero : model.handleCoefficients 0 = 0 := by
    simp [handleCoefficients]
  unfold componentExponent
  split
  · rfl
  · simpa using congrFun coefficients_zero _

/-- Integral exponents are additive in the marked homology class. -/
theorem componentExponent_add
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha beta : H2)
    (component : ComponentSpec) :
    model.componentExponent (alpha + beta) component =
      model.componentExponent alpha component +
        model.componentExponent beta component := by
  unfold componentExponent
  split <;> simp [handleCoefficients, map_add]

/-- A recorded two-handle component reads the matching cycle coefficient. -/
theorem two_handle_component_exponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2)
    (index : Fin topology.counts.h2) :
    model.componentExponent alpha (model.twoHandleComponent index) =
      model.handleCoefficients alpha index := by
  simp [componentExponent, model.two_handle_index_roundtrip index]

/-- Dotted one-handle components carry no degree-two cycle coefficient. -/
theorem nonordinary_component_exponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology)
    (alpha : H2)
    (component : ComponentSpec)
    (nonordinary : component.role ≠ .ordinary) :
    model.componentExponent alpha component = 0 := by
  simp [componentExponent,
    model.nonordinary_component_unindexed component nonordinary]

end IntegralTwoHandleCycleModel

/--
A certified integral cycle representative for every admitted presentation of
one manifold. Each presentation may have different handle coordinates; the
separately compiled handle-chain move controls their transport.
-/
structure IntegralCycleRepresentativeSystem
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  model :
    (topology : SpecialKirbyPresentation manifold H2) →
      IntegralTwoHandleCycleModel topology
  systemCertificateHash : String
  system_certificate_hash_shape :
    RawPresentation.sha256Shape systemCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

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

namespace TensorAutomorphismGenerator

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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (cycleSystem : IntegralCycleRepresentativeSystem manifold H2)
    (generator : TensorAutomorphismGenerator categoryData) :
    HomologicalKirbyColorWeights categoryData manifold H2 where
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (cycleSystem : IntegralCycleRepresentativeSystem manifold H2)
    (generator : TensorAutomorphismGenerator categoryData)
    (topology : SpecialKirbyPresentation manifold H2)
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
The final presentation compiler for the integral-character route.

Its category-bound predecessor is derived below.  Callers cannot supply a
    different `HomologicalKirbyColorWeights` value after the cycle model and tensor
automorphism have been fixed.
-/
structure IntegralCharacterBoundPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData) where
  cycleSystem : IntegralCycleRepresentativeSystem manifold H2
  generator : TensorAutomorphismGenerator categoryData
  eventCompiler :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        (integralCharacterWeights cycleSystem generator).toComponentExpansion
          topology) →
      CategoricalEventCompiler C topology.formal.raw
  eventCompilerBinding :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        (integralCharacterWeights cycleSystem generator).toComponentExpansion
          topology) →
      EventCompilerBinding
        (integralCharacterWeights cycleSystem generator)
        topology labeling algebra (eventCompiler topology alpha labeling)
  diagramCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      IntegralCharacterBoundPresentationCompiler
        categoryData manifold H2 algebra) :
    CategoryBoundPresentationCompiler
      categoryData manifold H2 algebra where
  weights :=
    integralCharacterWeights compiler.cycleSystem compiler.generator
  eventCompiler := compiler.eventCompiler
  eventCompilerBinding := compiler.eventCompilerBinding
  diagramCertificateHash := compiler.diagramCertificateHash
  diagram_certificate_hash_shape :=
    compiler.diagram_certificate_hash_shape
  decorationCertificateHash := compiler.decorationCertificateHash
  decoration_certificate_hash_shape :=
    compiler.decoration_certificate_hash_shape
  sourceRefs :=
    compiler.sourceRefs ++ compiler.cycleSystem.sourceRefs ++
      compiler.generator.sourceRefs
  exactEventScope := compiler.exactEventScope
  sourceScopeCaveat :=
    compiler.sourceScopeCaveat ++ " " ++
      compiler.cycleSystem.sourceScopeCaveat ++ " " ++
      compiler.generator.sourceScopeCaveat

/-- The derived coefficients are definitionally the integral-character formula. -/
theorem weights_are_integral_character_weights
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      IntegralCharacterBoundPresentationCompiler
      categoryData manifold H2 algebra) :
    compiler.toCategoryBound.weights =
      integralCharacterWeights compiler.cycleSystem compiler.generator := by
  rfl

end IntegralCharacterBoundPresentationCompiler

end TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
