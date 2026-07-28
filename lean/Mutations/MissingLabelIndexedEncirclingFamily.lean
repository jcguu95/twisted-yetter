import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.MissingLabelIndexedEncirclingFamily

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOKirbyColorEncircling
open TwistedYetter.Kirby.KirbyColorEncirclingTransport

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertion : PivotalInsertionLaw data)
    (mate : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S)
    (oneLabel :
      EncirclingTransportFamily
        (CategoryData.encirclingTransportData data insertion mate x))
    (hash : String)
    (hashShape :
      TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape hash =
        true) :
    LabelIndexedEncirclingMovies data insertion mate where
  family := oneLabel
  graphicalCertificateHash := hash
  graphical_certificate_hash_shape := hashShape

end TwistedYetter.Mutations.MissingLabelIndexedEncirclingFamily
