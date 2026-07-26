import TwistedYetter.Kirby.SimultaneousDottedCutGeometry
import TwistedYetter.Kirby.KirbyCancellation

/-!
# Role-aware premodular Kirby evaluator

Ordinary components are expanded in the ordinary Kirby colour.  Dotted
one-handle components are absent from that finite label sum and are
interpreted only by the normalized tensor-unit cut primitive.

This distinction is enforced by the type of `OrdinaryLabeling`; it is not a
runtime convention or a caller-supplied Boolean.
-/

namespace TwistedYetter.Kirby.RoleAwarePremodularEvaluator

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

namespace CanonicalPresentation

/-- Registry indices whose components are not dotted one-handles. -/
abbrev OrdinaryComponentIndex
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) :=
  { index :
      Fin presentation.topology.formal.raw.components.length //
    (presentation.topology.formal.raw.components.get index).role ≠ .dotted }

/--
The complete Kirby-colour labeling domain of the role-aware evaluator.

There is deliberately no coordinate for a dotted component.
-/
abbrev OrdinaryLabeling
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) :=
  OrdinaryComponentIndex presentation → S

/-- Registry indices of dotted one-handle components. -/
abbrev DottedComponentIndex
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) :=
  { index :
      Fin presentation.topology.formal.raw.components.length //
    (presentation.topology.formal.raw.components.get index).role = .dotted }

/-- Labels used only when comparing with the legacy modular expansion. -/
abbrev DottedLabeling
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) :=
  DottedComponentIndex presentation → S

/-- Split one legacy global labeling along the component-role partition. -/
def splitGlobalLabeling
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (labeling : presentation.GlobalLabeling (S := S)) :
    OrdinaryLabeling (S := S) presentation ×
      DottedLabeling (S := S) presentation :=
  (fun index => labeling index.1, fun index => labeling index.1)

/-- Merge the disjoint ordinary and dotted labeling coordinates. -/
def mergeRoleLabeling
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (labeling :
      OrdinaryLabeling (S := S) presentation ×
        DottedLabeling (S := S) presentation) :
    presentation.GlobalLabeling (S := S) :=
  fun index =>
    if dotted :
        (presentation.topology.formal.raw.components.get index).role =
          .dotted then
      labeling.2 ⟨index, dotted⟩
    else
      labeling.1 ⟨index, dotted⟩

/--
The legacy labeling denominator is exactly ordinary labels times dotted
labels.  This is the finite-set foundation for the modular Fubini
calibration; no component may disappear or be counted twice.
-/
def globalLabelingEquivRoleLabelings
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) :
    presentation.GlobalLabeling (S := S) ≃
      OrdinaryLabeling (S := S) presentation ×
        DottedLabeling (S := S) presentation where
  toFun := splitGlobalLabeling presentation
  invFun := mergeRoleLabeling presentation
  left_inv := by
    intro labeling
    funext index
    simp only [mergeRoleLabeling, splitGlobalLabeling]
    split <;> rfl
  right_inv := by
    intro labeling
    apply Prod.ext
    · funext index
      simp only [splitGlobalLabeling, mergeRoleLabeling]
      split
      · rename_i dotted
        exact (index.2 dotted).elim
      · rfl
    · funext index
      simp only [splitGlobalLabeling, mergeRoleLabeling]
      split
      · rfl
      · rename_i notDotted
        exact (notDotted index.2).elim

/--
Resolve an ordinary component label relative to a selected unit index.

This category-independent core lets source-bound topology certificates prove
label transport without mentioning an evaluator or a category.
-/
def roleAwareLabelOfWithUnit
    {H2 : Type uH} [AddCommGroup H2]
    (unitIndex : S)
    (presentation : CanonicalPresentation H2)
    (labeling : OrdinaryLabeling (S := S) presentation)
    (componentId : String) : S :=
  match presentation.componentIndexing.indexOf componentId with
  | none =>
      unitIndex
  | some index =>
      if hOrdinary :
          (presentation.topology.formal.raw.components.get index).role ≠
            .dotted then
        labeling ⟨index, hOrdinary⟩
      else
        unitIndex

/--
Resolve an ordinary component label.  A dotted or unknown ID is forced to the
tensor unit; the caller cannot supply a label for it.
-/
noncomputable def roleAwareLabelOf
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    (labeling : OrdinaryLabeling (S := S) presentation)
    (componentId : String) : S :=
  roleAwareLabelOfWithUnit 𝒞.toFusionCategoryData.unitIndex
    presentation labeling componentId

@[simp]
theorem roleAwareLabelOf_ordinary
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    (labeling : OrdinaryLabeling (S := S) presentation)
    (index : OrdinaryComponentIndex presentation) :
    roleAwareLabelOf 𝒞 presentation labeling
        (presentation.topology.formal.raw.components.get
          index.1).componentId =
      labeling index := by
  simp only [roleAwareLabelOf,
    roleAwareLabelOfWithUnit,
    presentation.componentIndexing.index_roundtrip index.1]
  split
  · congr 1
  · rename_i notOrdinary
    exact (notOrdinary index.2).elim

theorem roleAwareLabelOf_dotted
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    (labeling : OrdinaryLabeling (S := S) presentation)
    (index : Fin presentation.topology.formal.raw.components.length)
    (dotted :
      (presentation.topology.formal.raw.components.get index).role =
        .dotted) :
    roleAwareLabelOf 𝒞 presentation labeling
        (presentation.topology.formal.raw.components.get index).componentId =
      𝒞.toFusionCategoryData.unitIndex := by
  simp only [roleAwareLabelOf,
    roleAwareLabelOfWithUnit,
    presentation.componentIndexing.index_roundtrip index]
  split
  · contradiction
  · rfl

/-- One term of the role-aware finite sum. -/
noncomputable def roleAwareTermDiagram
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (labeling : OrdinaryLabeling (S := S) presentation) :
    Diagram C .unit .unit :=
  geometry.cutDiagram.interpret 𝒞 η
    (roleAwareLabelOf 𝒞 presentation labeling)

/-- Ordinary Kirby-colour coefficient; dotted components are not indexed. -/
noncomputable def roleAwareGlobalWeight
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (cycle : presentation.DegreeTwoCycle)
    (labeling : OrdinaryLabeling (S := S) presentation) : K :=
  ∏ index,
    presentation.cycleComponentWeight 𝒞 η cycle
      (presentation.topology.formal.raw.components.get index.1)
      (labeling index)

/-- The formal role-aware premodular Kirby-colour sum. -/
noncomputable def roleAwareLinearDiagram
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum
    (roleAwareGlobalWeight 𝒞 η presentation cycle)
    (roleAwareTermDiagram 𝒞 η presentation geometry)

/-- Raw scalar produced by the role-aware premodular evaluator. -/
noncomputable def roleAwareRawNumerator
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) : K :=
  𝒞.toFusionCategoryData.closedScalar
    (LinearDiagram.eval
      (roleAwareLinearDiagram 𝒞 η presentation geometry cycle))

/--
Normalization for the special-cut evaluator.

The dotted cut itself supplies one global-dimension factor.  Consequently
the effective transparent factor is exactly one, even when the Müger centre
is nontrivial.
-/
noncomputable def roleAwareNormalizationProfile
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    GlobalDimensionProfile (K := K) where
  cDimension := 𝒞.globalDimension
  dDimension := 𝒞.globalDimension
  transparentDimension := 1
  cDimension_ne_zero := 𝒞.globalDimension_ne_zero
  dDimension_ne_zero := 𝒞.globalDimension_ne_zero
  transparentDimension_ne_zero := one_ne_zero
  source_ref := "ref:egnotc-proposition-8.14.2"
  source_locator :=
    "EGNO Proposition 8.14.2 and Remark 8.14.3; special dotted-cut "
      ++ "normalization fixes the effective transparent factor to one"

/-- Complete normalized state for one explicit handle-chain cycle. -/
noncomputable def roleAwareEvaluationState
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) :
    EvaluationState (K := K) where
  counts := presentation.topology.counts
  rawNumerator :=
    roleAwareRawNumerator 𝒞 η presentation geometry cycle

/-- Normalized role-aware value on an explicit degree-two cycle. -/
noncomputable def roleAwareCycleEval
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) : K :=
  (roleAwareEvaluationState 𝒞 η presentation geometry cycle).normalized
    (roleAwareNormalizationProfile 𝒞)

end CanonicalPresentation

end TwistedYetter.Kirby.RoleAwarePremodularEvaluator
