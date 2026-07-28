import TwistedYetter.Kirby.CategoricalPresentationCompiler
import TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

/-!
# Category-bound homological Kirby colours

The generic finite-label compiler deliberately supports arbitrary finite
state sums. That interface is too broad for the intended Kirby invariant:
its label fiber need not be the category's simple-index type, its weights
need not use the category's dimension profile, and its framing events need
not use the twist accepted by the graphical move algebra.

This module supplies the narrower construction boundary. Every component is
expanded over the exact simple-index type `S`. At the zero marked class, each
coefficient is forced to be the recorded category weight. Every active
strand is interpreted by the corresponding recorded simple or dual-simple
object, and every framing event uses the exact twist retained by the same
`RibbonKirbyGraphicalAlgebra.Input`.

The nonzero homological coefficients and the concrete event morphisms remain
explicit construction inputs. No universal-grading formula is postulated in
this mechanism.
-/

namespace TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
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
The coefficient of each simple summand for every component and marked class.

The zero-class law is mathematical data, not metadata: it forces the
untwisted specialization to use the exact weight stored in
`categoryData.encirclingData`. The behavior at nonzero classes is intentionally
left open for a source-backed character or universal-grading construction.
-/
structure HomologicalKirbyColorWeights
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2] where
  coefficient :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (component : ComponentSpec) →
    S → K
  zero_class_sound :
    (topology : SpecialKirbyPresentation H2) →
    (component : ComponentSpec) →
    (simple : S) →
      coefficient topology 0 component simple =
        categoryData.encirclingData.weight simple
  categorySnapshotHash : String
  category_snapshot_hash_sound :
    categorySnapshotHash = categoryData.categorySnapshotHash
  coefficientCertificateHash : String
  coefficient_certificate_hash_shape :
    RawPresentation.sha256Shape coefficientCertificateHash = true
  markingCertificateHash : String
  marking_certificate_hash_shape :
    RawPresentation.sha256Shape markingCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace HomologicalKirbyColorWeights

/--
Derive the generic component expansion while fixing every label fiber to the
category's exact simple-index type.
-/
noncomputable def toComponentExpansion
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (weights :
      HomologicalKirbyColorWeights categoryData H2) :
    ComponentLabelExpansion (K := K) (S := S) H2 where
  Label := fun _ => S
  labelFintype := fun _ => inferInstance
  componentWeight := weights.coefficient
  expansionSchema :=
    "twisted-yetter.category-bound-kirby-color-expansion.v1"
  expansionSnapshotHash := weights.coefficientCertificateHash
  expansion_snapshot_hash_shape :=
    weights.coefficient_certificate_hash_shape
  sourceRefs := weights.sourceRefs
  exactComponentScope := weights.exactScope
  sourceScopeCaveat := weights.sourceScopeCaveat

/-- No private or unrelated finite label type may enter this expansion. -/
theorem label_fiber_is_simple_index
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (weights :
      HomologicalKirbyColorWeights categoryData H2)
    (component : ComponentSpec) :
    (weights.toComponentExpansion.Label component) = S := by
  rfl

/-- The retained component coefficient is exactly the source-backed weight. -/
theorem component_weight_eq
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (weights :
      HomologicalKirbyColorWeights categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (component : ComponentSpec)
    (simple : S) :
    weights.toComponentExpansion.componentWeight
        topology alpha component simple =
      weights.coefficient topology alpha component simple := by
  rfl

/-- At `alpha = 0`, every component is the ordinary Kirby colour. -/
theorem zero_component_weight_eq_category_weight
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (weights :
      HomologicalKirbyColorWeights categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (component : ComponentSpec)
    (simple : S) :
    weights.toComponentExpansion.componentWeight
        topology 0 component simple =
      categoryData.encirclingData.weight simple :=
  weights.zero_class_sound topology component simple

end HomologicalKirbyColorWeights

/--
Resolve immutable component IDs to the exact global simple labeling.

Only the behavior on serialized component IDs is constrained. Invalid strand
IDs never enter an admitted execution trace because `RawPresentation` rejects
them before this compiler is called.
-/
structure LabelledComponentResolver
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (weights :
      HomologicalKirbyColorWeights categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        weights.toComponentExpansion topology) where
  labelOf : String → S
  component_sound :
    (index : Fin topology.formal.raw.components.length) →
      labelOf
          (topology.formal.raw.components.get index).componentId =
        labeling index

/-- Interpret orientation by the recorded simple or recorded dual simple. -/
def strandObject
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {weights :
      HomologicalKirbyColorWeights categoryData H2}
    {topology : SpecialKirbyPresentation H2}
    {labeling :
      ComponentLabelExpansion.GlobalLabeling
        weights.toComponentExpansion topology}
    (resolver : LabelledComponentResolver weights topology labeling)
    (strand : StrandState) : C :=
  match strand.orientation with
  | .positive =>
      categoryData.encirclingData.simple
        (resolver.labelOf strand.componentId)
  | .negative =>
      categoryData.encirclingData.dualSimple
        (resolver.labelOf strand.componentId)

/-- A deterministic right-associated boundary for one labelled slice. -/
def labelledBoundary
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {weights :
      HomologicalKirbyColorWeights categoryData H2}
    {topology : SpecialKirbyPresentation H2}
    {labeling :
      ComponentLabelExpansion.GlobalLabeling
        weights.toComponentExpansion topology}
    (resolver : LabelledComponentResolver weights topology labeling) :
    List StrandState → Boundary C :=
  boundaryWord (strandObject resolver)

/--
Semantic binding for one concrete event compiler.

The boundary equality rules out arbitrary object assignments, while the
twist equality prevents a framing compiler and the Kirby-move algebra from
silently using different ribbon conventions.
-/
structure EventCompilerBinding
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (weights :
      HomologicalKirbyColorWeights categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        weights.toComponentExpansion topology)
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData)
    (compiler : CategoricalEventCompiler C topology.formal.raw) where
  resolver : LabelledComponentResolver weights topology labeling
  boundary_sound :
    compiler.boundary = labelledBoundary resolver
  framing_twist_sound :
    compiler.framingTwistData = algebra.framedKink.twist

/--
The presentation compiler admitted by the final invariant route.

Its generic componentwise compiler is derived below; callers cannot replace
the simple-index expansion, whole-link product weight, boundary object
interpretation, or framing twist after the binding has been checked.
-/
structure CategoryBoundPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2]
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData) where
  weights : HomologicalKirbyColorWeights categoryData H2
  resolver :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        weights.toComponentExpansion topology) →
      LabelledComponentResolver weights topology labeling
  eventSemantics :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        weights.toComponentExpansion topology) →
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

namespace CategoryBoundPresentationCompiler

/--
Derive every whole event compiler from local windowed semantics.

There is no arbitrary `CategoricalEventCompiler` field on the admitted final
route.
-/
def eventCompiler
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      CategoryBoundPresentationCompiler
        categoryData H2 algebra)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        compiler.weights.toComponentExpansion topology) :
    CategoricalEventCompiler C topology.formal.raw :=
  (compiler.eventSemantics topology alpha labeling)
    |>.toCategoricalEventCompiler

/-- The old binding certificate is now a theorem-by-construction. -/
def eventCompilerBinding
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      CategoryBoundPresentationCompiler
        categoryData H2 algebra)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        compiler.weights.toComponentExpansion topology) :
    EventCompilerBinding compiler.weights topology labeling algebra
      (compiler.eventCompiler topology alpha labeling) where
  resolver := compiler.resolver topology alpha labeling
  boundary_sound := rfl
  framing_twist_sound := rfl

/-- Derive the older generic compiler only after all category bindings exist. -/
noncomputable def toComponentwise
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      CategoryBoundPresentationCompiler
        categoryData H2 algebra) :
    ComponentwiseFiniteLabelPresentationCompiler
      categoryData H2 where
  expansion := compiler.weights.toComponentExpansion
  eventCompiler := compiler.eventCompiler
  diagramCertificateHash := compiler.diagramCertificateHash
  diagram_certificate_hash_shape :=
    compiler.diagram_certificate_hash_shape
  decorationCertificateHash := compiler.decorationCertificateHash
  decoration_certificate_hash_shape :=
    compiler.decoration_certificate_hash_shape
  sourceRefs := compiler.sourceRefs ++ compiler.weights.sourceRefs
  exactEventScope := compiler.exactEventScope
  sourceScopeCaveat :=
    compiler.sourceScopeCaveat ++ " " ++
      compiler.weights.sourceScopeCaveat

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Every derived event compiler uses the graphical algebra's exact twist. -/
theorem event_twist_is_graphical_twist
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      CategoryBoundPresentationCompiler
        categoryData H2 algebra)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        compiler.weights.toComponentExpansion topology) :
    (compiler.eventCompiler topology alpha labeling).framingTwistData =
      algebra.framedKink.twist :=
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Every derived boundary is built from the same global simple labeling. -/
theorem event_boundary_is_labelled_boundary
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      CategoryBoundPresentationCompiler
        categoryData H2 algebra)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (labeling :
      ComponentLabelExpansion.GlobalLabeling
        compiler.weights.toComponentExpansion topology) :
    (compiler.eventCompiler topology alpha labeling).boundary =
      labelledBoundary
        (compiler.resolver topology alpha labeling) := by
  rfl

end CategoryBoundPresentationCompiler

end TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler
