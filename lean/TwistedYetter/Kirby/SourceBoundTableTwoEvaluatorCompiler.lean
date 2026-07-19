import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
import TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
import TwistedYetter.Kirby.SourceBoundGraphicalMoveCompiler
import TwistedYetter.Kirby.TableTwoEvaluatorCompiler

/-!
# Source-bound Table 2 evaluator compiler

`TableTwoEvaluatorCompiler` is the compact R11 interface, but its evaluation
field can in principle be filled by an arbitrary decorated presentation.
This module closes that path.

The evaluation used by every one of the eight cases below is definitionally
produced by an `IntegralCharacterBoundPresentationCompiler`. Its closed
diagram is a finite global-simple-label sum of complete event-by-event
traces. The formal Kirby colour is collapsed only after every component has
received one globally consistent category label and every resulting trace
has been compiled. The homological coefficient is forced to be the ordinary
category weight times the integer power of one categorical tensor
automorphism scalar. Strand objects, duals, and framing twists are bound to
the same admitted category and graphical algebra.

The eight R7/R8/R9 proof objects are derived from one source-bound graphical
move compiler. This module does not pretend that a categorical event
interpreter, a label expansion, or a concrete graphical compiler instance has
already been constructed.
-/

namespace TwistedYetter.Kirby.SourceBoundEvaluatorCompilation

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler
open TwistedYetter.Kirby.EvaluatorCompiler
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
open TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation

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
The exhaustive compiler whose presentation evaluator is source-compiled and
category-bound.

There is no `evaluation` field.  The presentation compiler is specifically
the category-bound global finite-label compiler, and all eight result types
mention its derived `decorate` method directly. A single-label or arbitrary
finite-state compiler cannot silently stand in for a formal Kirby-colour
expansion on this route, and a caller cannot replace the componentwise
product of weights, simple-object interpretation, or twist convention.
-/
structure SourceBoundTableTwoEvaluatorCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  graphicalAlgebra : RibbonKirbyGraphicalAlgebra.Input categoryData
  presentationCompiler :
    IntegralCharacterBoundPresentationCompiler
      categoryData manifold H2 graphicalAlgebra
  moveCompiler :
    SourceBoundGraphicalMoveCompiler
      categoryData manifold H2
        presentationCompiler.toCategoryBound.toComponentwise graphicalAlgebra
  categorySnapshotHash : String
  category_snapshot_hash_sound :
    categorySnapshotHash = categoryData.categorySnapshotHash
  compilerCertificateHash : String
  compiler_certificate_hash_shape :
    RawPresentation.sha256Shape compilerCertificateHash = true
  sourceRefs : List String
  exactFormulaScope : String
  sourceScopeCaveat : String

namespace SourceBoundTableTwoEvaluatorCompiler

/-- Forget only the source-compilation wrapper after deriving its evaluator. -/
noncomputable def toTableTwo
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundTableTwoEvaluatorCompiler
        categoryData manifold H2) :
    TableTwoEvaluatorCompiler categoryData manifold H2 where
  evaluation :=
    compiler.presentationCompiler.toCategoryBound.toComponentwise.decorate
  framedIsotopy := fun metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.framedIsotopy metadata counts transport) alpha
  oneOverOne := fun orientation metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.oneOverOne orientation metadata counts transport) alpha
  twoOverOne := fun orientation metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.twoOverOne orientation metadata counts transport) alpha
  twoOverTwo := fun orientation metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.twoOverTwo orientation metadata counts transport) alpha
  oneTwoBirth := fun metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.oneTwoBirth metadata counts transport) alpha
  oneTwoDeath := fun metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.oneTwoDeath metadata counts transport) alpha
  twoThreeBirth := fun metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.twoThreeBirth metadata counts transport) alpha
  twoThreeDeath := fun metadata counts transport alpha =>
    compiler.moveCompiler.compile
      (.twoThreeDeath metadata counts transport) alpha
  categorySnapshotHash := compiler.categorySnapshotHash
  category_snapshot_hash_sound := compiler.category_snapshot_hash_sound
  compilerCertificateHash := compiler.compilerCertificateHash
  compiler_certificate_hash_shape :=
    compiler.compiler_certificate_hash_shape
  sourceRefs := compiler.sourceRefs
  exactFormulaScope := compiler.exactFormulaScope
  sourceScopeCaveat := compiler.sourceScopeCaveat

theorem toTableTwo_evaluation_is_trace_compiled
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundTableTwoEvaluatorCompiler
        categoryData manifold H2)
    (presentation : SpecialKirbyPresentation manifold H2) :
    compiler.toTableTwo.evaluation presentation =
      compiler.presentationCompiler.toCategoryBound.toComponentwise.decorate
        presentation := by
  rfl

/-- The accepted graphical algebra is bound to the evaluator category hash. -/
theorem graphical_algebra_snapshot_bound
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2) :
    compiler.graphicalAlgebra.categorySnapshotHash =
      categoryData.categorySnapshotHash :=
  compiler.graphicalAlgebra.category_snapshot_hash_sound

/--
The diagram evaluated by the compact R11 compiler is exactly the
componentwise product-weighted sum of complete globally labelled traces.
-/
theorem toTableTwo_evaluation_is_componentwise_global_sum
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2)
    (presentation : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    Diagram.eval C
        ((compiler.toTableTwo.evaluation presentation).diagram alpha) =
      let expansion :=
        (integralCharacterWeights
          (IntegralCycleRepresentativeSystem.canonical manifold H2)
          compiler.presentationCompiler.selectedGenerator.generator
        ).toComponentExpansion
      letI := expansion.globalFintype presentation
      ∑ labeling,
        expansion.globalWeight presentation alpha labeling •
          Diagram.eval C
            ((compiler.presentationCompiler.eventCompiler
                presentation alpha labeling).compileClosed
              presentation.execution) := by
  exact
    compiler.presentationCompiler.toCategoryBound.toComponentwise
      |>.compileDiagram_eval_eq_componentwise_sum presentation alpha

/--
The final source-bound evaluator cannot carry an independently supplied
homological coefficient table. Its weights are definitionally generated by
the pinned integral cycle representatives and tensor automorphism.
-/
theorem presentation_weights_are_integral_character_weights
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2) :
    compiler.presentationCompiler.toCategoryBound.weights =
      integralCharacterWeights
        (IntegralCycleRepresentativeSystem.canonical manifold H2)
        compiler.presentationCompiler.selectedGenerator.generator := by
  rfl

end SourceBoundTableTwoEvaluatorCompiler

end TwistedYetter.Kirby.SourceBoundEvaluatorCompilation
