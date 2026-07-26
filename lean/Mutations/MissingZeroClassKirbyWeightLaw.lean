import TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler

namespace TwistedYetter.Mutations.MissingZeroClassKirbyWeightLaw

open CategoryTheory
open TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

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

/-- This must fail: the alpha-zero ordinary-specialization law is mandatory. -/
def unsafeWeights
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (coefficient :
      (topology : SpecialKirbyPresentation H2) →
      H2 → ComponentSpec → S → K)
    (categorySnapshotHash coefficientCertificateHash
      markingCertificateHash : String)
    (categoryHashSound :
      categorySnapshotHash = categoryData.categorySnapshotHash)
    (coefficientHashShape :
      RawPresentation.sha256Shape coefficientCertificateHash = true)
    (markingHashShape :
      RawPresentation.sha256Shape markingCertificateHash = true) :
    HomologicalKirbyColorWeights categoryData H2 where
  coefficient := coefficient
  categorySnapshotHash := categorySnapshotHash
  category_snapshot_hash_sound := categoryHashSound
  coefficientCertificateHash := coefficientCertificateHash
  coefficient_certificate_hash_shape := coefficientHashShape
  markingCertificateHash := markingCertificateHash
  marking_certificate_hash_shape := markingHashShape
  sourceRefs := []
  exactScope := "mutation"
  sourceScopeCaveat := "mutation"

end TwistedYetter.Mutations.MissingZeroClassKirbyWeightLaw
