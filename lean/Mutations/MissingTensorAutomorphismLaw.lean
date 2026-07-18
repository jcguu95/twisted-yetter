import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.MissingTensorAutomorphismLaw

open CategoryTheory
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

universe uK uC vC uS uI

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
This must fail: arbitrary invertible scalars on simples are not accepted
without the tensor law for the underlying natural automorphism.
-/
def unsafeGenerator
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (generator : TensorAutomorphismGenerator categoryData) :
    TensorAutomorphismGenerator categoryData where
  automorphism := generator.automorphism
  unit_hom := generator.unit_hom
  simpleScalar := generator.simpleScalar
  simple_scalar_sound := generator.simple_scalar_sound
  categorySnapshotHash := generator.categorySnapshotHash
  category_snapshot_hash_sound :=
    generator.category_snapshot_hash_sound
  automorphismCertificateHash :=
    generator.automorphismCertificateHash
  automorphism_certificate_hash_shape :=
    generator.automorphism_certificate_hash_shape
  sourceRefs := generator.sourceRefs
  exactScope := generator.exactScope
  sourceScopeCaveat := generator.sourceScopeCaveat

end TwistedYetter.Mutations.MissingTensorAutomorphismLaw
