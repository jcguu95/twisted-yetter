import TwistedYetter.Kirby.TableTwoEvaluatorCompiler

namespace TwistedYetter.Kirby.EvaluatorCompiler.Mutations

open CategoryTheory
open TwistedYetter.Kirby.KirbyColorEncirclingTransport
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

example
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2) :
    TableTwoEvaluatorCompiler categoryData H2 where
  evaluation := compiler.evaluation
  framedIsotopy := compiler.framedIsotopy
  oneOverOne := compiler.oneOverOne
  twoOverOne := compiler.twoOverOne
  twoOverTwo := compiler.twoOverTwo
  oneTwoBirth := compiler.oneTwoBirth
  oneTwoDeath := compiler.oneTwoDeath
  twoThreeBirth := compiler.twoThreeBirth
  categorySnapshotHash := compiler.categorySnapshotHash
  category_snapshot_hash_sound := compiler.category_snapshot_hash_sound
  compilerCertificateHash := compiler.compilerCertificateHash
  compiler_certificate_hash_shape :=
    compiler.compiler_certificate_hash_shape
  sourceRefs := compiler.sourceRefs
  exactFormulaScope := compiler.exactFormulaScope
  sourceScopeCaveat := compiler.sourceScopeCaveat

end TwistedYetter.Kirby.EvaluatorCompiler.Mutations
