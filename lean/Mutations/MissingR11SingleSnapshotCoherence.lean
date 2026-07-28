import TwistedYetter.Kirby.HomologicallyTwistedInvariant

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.KirbyColorEncirclingTransport
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.Presentation

universe uK uC vC uS uI

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

example
    (categorySnapshotHash : String)
    (category_hash_shape :
      RawPresentation.sha256Shape categorySnapshotHash = true)
    (profile : GlobalDimensionProfile (K := K))
    (encirclingData :
      EncirclingTransportData (R := K) (D := C) (S := S) (I := I))
    (closedScalar : (𝟙_ C ⟶ 𝟙_ C) → K)
    (scalarizationMatchesGroundField : Prop)
    (scalarization_witness : scalarizationMatchesGroundField)
    (singleSnapshotCoherent : Prop)
    (coherenceCertificateHash : String)
    (coherence_hash_shape :
      RawPresentation.sha256Shape coherenceCertificateHash = true)
    (sourceRefs : List String)
    (sourceScopeCaveat : String) :
    AdmissibleKirbyCategory
      (K := K) (C := C) (S := S) (I := I) where
  categorySnapshotHash := categorySnapshotHash
  category_snapshot_hash_shape := category_hash_shape
  dimensionProfile := profile
  encirclingData := encirclingData
  closedScalar := closedScalar
  scalarizationMatchesGroundField := scalarizationMatchesGroundField
  scalarization_witness := scalarization_witness
  singleSnapshotCoherent := singleSnapshotCoherent
  coherenceCertificateHash := coherenceCertificateHash
  coherence_certificate_hash_shape := coherence_hash_shape
  sourceRefs := sourceRefs
  sourceScopeCaveat := sourceScopeCaveat

end TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations
