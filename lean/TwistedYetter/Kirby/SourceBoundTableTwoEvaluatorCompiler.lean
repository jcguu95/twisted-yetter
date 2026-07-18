import TwistedYetter.Kirby.CategoricalPresentationCompiler
import TwistedYetter.Kirby.TableTwoEvaluatorCompiler

/-!
# Source-bound Table 2 evaluator compiler

`TableTwoEvaluatorCompiler` is the compact R11 interface, but its evaluation
field can in principle be filled by an arbitrary decorated presentation.
This module closes that path.

The evaluation used by every one of the eight cases below is definitionally
`SourceBoundPresentationCompiler.decorate`: its closed diagram is compiled
event-by-event from the presentation's typed execution trace, and its raw
numerator is the scalarization of that exact diagram.

The eight R7/R8/R9 proof objects remain explicit fields. This module does not
pretend that a categorical event interpreter or those local proofs have
already been constructed.
-/

namespace TwistedYetter.Kirby.SourceBoundEvaluatorCompilation

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.EvaluatorCompiler
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
The exhaustive compiler whose presentation evaluator is source-compiled.

There is no `evaluation` field. All eight result types mention
`presentationCompiler.decorate` directly.
-/
structure SourceBoundTableTwoEvaluatorCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  presentationCompiler :
    SourceBoundPresentationCompiler categoryData manifold H2
  framedIsotopy :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .framedIsotopy source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.framedIsotopy metadata counts_sound transport) alpha
  oneOverOne :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .oneOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.oneOverOne orientation metadata counts_sound transport) alpha
  twoOverOne :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .twoOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.twoOverOne orientation metadata counts_sound transport) alpha
  twoOverTwo :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .twoOverTwo source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.twoOverTwo orientation metadata counts_sound transport) alpha
  oneTwoBirth :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .oneTwoBirth source target) →
    (counts_sound : target.counts = source.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.oneTwoBirth metadata counts_sound transport) alpha
  oneTwoDeath :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .oneTwoDeath source target) →
    (counts_sound : source.counts = target.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.oneTwoDeath metadata counts_sound transport) alpha
  twoThreeBirth :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .twoThreeBirth source target) →
    (counts_sound : target.counts = source.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.twoThreeBirth metadata counts_sound transport) alpha
  twoThreeDeath :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .twoThreeDeath source target) →
    (counts_sound : source.counts = target.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData
        (presentationCompiler.decorate source)
        (presentationCompiler.decorate target)
        (.twoThreeDeath metadata counts_sound transport) alpha
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
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2) :
    TableTwoEvaluatorCompiler categoryData manifold H2 where
  evaluation := compiler.presentationCompiler.decorate
  framedIsotopy := compiler.framedIsotopy
  oneOverOne := compiler.oneOverOne
  twoOverOne := compiler.twoOverOne
  twoOverTwo := compiler.twoOverTwo
  oneTwoBirth := compiler.oneTwoBirth
  oneTwoDeath := compiler.oneTwoDeath
  twoThreeBirth := compiler.twoThreeBirth
  twoThreeDeath := compiler.twoThreeDeath
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
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2)
    (presentation : SpecialKirbyPresentation manifold H2) :
    compiler.toTableTwo.evaluation presentation =
      compiler.presentationCompiler.decorate presentation := by
  rfl

end SourceBoundTableTwoEvaluatorCompiler

end TwistedYetter.Kirby.SourceBoundEvaluatorCompilation
