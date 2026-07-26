import TwistedYetter.Kirby.HomologicallyTwistedInvariant

/-!
# Exhaustive compiler for Table 2 evaluator steps

`HomologicallyTwistedKirbyPrescription` is the internal theorem interface:
its `localStep` field accepts every move at once.  That is convenient for
induction, but it is too opaque to serve as final construction evidence.

This module exposes the same obligation as eight separately named compiler
cases.  Every case is indexed by one exact `TableTwoMove` constructor and must
produce the corresponding closed R7/R8/R9 proof object.  The `compile`
function is a literal case split; it neither accepts nor manufactures a bare
equality of normalized values.

This closes only the structural coverage mechanism.  A concrete invariant
still needs an actual value of `TableTwoEvaluatorCompiler`, built from the
chosen category, presentation interpreter, coupon diagrams, slide witnesses,
and cancellation calculations.
-/

namespace TwistedYetter.Kirby.EvaluatorCompiler

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/-- Machine-visible denominator of compiler cases. -/
inductive CompilerCase where
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving Repr, BEq, DecidableEq

/-- Every directed Table 2 constructor occurs exactly once. -/
def requiredCompilerCases : List CompilerCase :=
  [
    .framedIsotopy,
    .oneOverOne,
    .twoOverOne,
    .twoOverTwo,
    .oneTwoBirth,
    .oneTwoDeath,
    .twoThreeBirth,
    .twoThreeDeath
  ]

theorem compiler_case_count :
    requiredCompilerCases.length = 8 := by
  rfl

/--
An evaluator compiler with one mandatory field per directed move family.

Each field returns an `EvaluatedTableTwoStep` indexed by the exact move being
compiled.  Therefore the field can only be filled by the matching R7, R8, or
R9 constructor and cannot be replaced by a final scalar equality.
-/
structure TableTwoEvaluatorCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2] where
  evaluation :
    (presentation : SpecialKirbyPresentation H2) →
      DecoratedKirbyPresentation categoryData presentation
  framedIsotopy :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .framedIsotopy source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.framedIsotopy metadata counts_sound transport) alpha
  oneOverOne :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .oneOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.oneOverOne metadata counts_sound transport) alpha
  twoOverOne :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .twoOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.twoOverOne metadata counts_sound transport) alpha
  twoOverTwo :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .twoOverTwo source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.twoOverTwo metadata counts_sound transport) alpha
  oneTwoBirth :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .oneTwoBirth source target) →
    (counts_sound : target.counts = source.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.oneTwoBirth metadata counts_sound transport) alpha
  oneTwoDeath :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .oneTwoDeath source target) →
    (counts_sound : source.counts = target.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.oneTwoDeath metadata counts_sound transport) alpha
  twoThreeBirth :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .twoThreeBirth source target) →
    (counts_sound : target.counts = source.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
        (.twoThreeBirth metadata counts_sound transport) alpha
  twoThreeDeath :
    {source target : SpecialKirbyPresentation H2} →
    (metadata : TableTwoMoveMetadata .twoThreeDeath source target) →
    (counts_sound : source.counts = target.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      EvaluatedTableTwoStep
        categoryData (evaluation source) (evaluation target)
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

namespace TableTwoEvaluatorCompiler

/-- Exhaustive dispatch from an exact topology move to its evaluator proof. -/
def compile
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (move : TableTwoMove source target)
    (alpha : H2) :
    EvaluatedTableTwoStep
      categoryData (compiler.evaluation source)
        (compiler.evaluation target) move alpha := by
  cases move with
  | framedIsotopy metadata counts transport =>
      exact compiler.framedIsotopy metadata counts transport alpha
  | oneOverOne metadata counts transport =>
      exact compiler.oneOverOne metadata counts transport alpha
  | twoOverOne metadata counts transport =>
      exact compiler.twoOverOne metadata counts transport alpha
  | twoOverTwo metadata counts transport =>
      exact compiler.twoOverTwo metadata counts transport alpha
  | oneTwoBirth metadata counts transport =>
      exact compiler.oneTwoBirth metadata counts transport alpha
  | oneTwoDeath metadata counts transport =>
      exact compiler.oneTwoDeath metadata counts transport alpha
  | twoThreeBirth metadata counts transport =>
      exact compiler.twoThreeBirth metadata counts transport alpha
  | twoThreeDeath metadata counts transport =>
      exact compiler.twoThreeDeath metadata counts transport alpha

theorem compile_framedIsotopy
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .framedIsotopy source target)
    (counts : source.counts = target.counts)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile (.framedIsotopy metadata counts transport) alpha =
      compiler.framedIsotopy metadata counts transport alpha := by
  rfl

theorem compile_oneOverOne
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .oneOverOne source target)
    (counts : source.counts = target.counts)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile
        (.oneOverOne metadata counts transport) alpha =
      compiler.oneOverOne
        metadata counts transport alpha := by
  rfl

theorem compile_twoOverOne
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .twoOverOne source target)
    (counts : source.counts = target.counts)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile
        (.twoOverOne metadata counts transport) alpha =
      compiler.twoOverOne
        metadata counts transport alpha := by
  rfl

theorem compile_twoOverTwo
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .twoOverTwo source target)
    (counts : source.counts = target.counts)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile
        (.twoOverTwo metadata counts transport) alpha =
      compiler.twoOverTwo
        metadata counts transport alpha := by
  rfl

theorem compile_oneTwoBirth
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .oneTwoBirth source target)
    (counts : target.counts = source.counts.addOneTwo)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile (.oneTwoBirth metadata counts transport) alpha =
      compiler.oneTwoBirth metadata counts transport alpha := by
  rfl

theorem compile_oneTwoDeath
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .oneTwoDeath source target)
    (counts : source.counts = target.counts.addOneTwo)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile (.oneTwoDeath metadata counts transport) alpha =
      compiler.oneTwoDeath metadata counts transport alpha := by
  rfl

theorem compile_twoThreeBirth
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .twoThreeBirth source target)
    (counts : target.counts = source.counts.addTwoThree)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile (.twoThreeBirth metadata counts transport) alpha =
      compiler.twoThreeBirth metadata counts transport alpha := by
  rfl

theorem compile_twoThreeDeath
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .twoThreeDeath source target)
    (counts : source.counts = target.counts.addTwoThree)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    compiler.compile (.twoThreeDeath metadata counts transport) alpha =
      compiler.twoThreeDeath metadata counts transport alpha := by
  rfl

/--
Convert the exhaustive compiler into the compact internal prescription used
by the movie induction.  This is the only route used by the final target.
-/
def toPrescription
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2) :
    HomologicallyTwistedKirbyPrescription categoryData H2 where
  evaluation := compiler.evaluation
  localStep := compiler.compile
  prescriptionCertificateHash := compiler.compilerCertificateHash
  prescription_certificate_hash_shape :=
    compiler.compiler_certificate_hash_shape
  sourceRefs := compiler.sourceRefs
  exactFormulaScope := compiler.exactFormulaScope
  sourceScopeCaveat := compiler.sourceScopeCaveat

end TableTwoEvaluatorCompiler

end TwistedYetter.Kirby.EvaluatorCompiler
