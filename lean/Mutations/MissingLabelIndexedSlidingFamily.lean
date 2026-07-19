import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.MissingLabelIndexedSlidingFamily

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.GeneralizedSliding

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertion : SphericalInsertionLaw data)
    (mate : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S)
    (oneLabel :
      SlidingFamily
        (CategoryData.slidingCategoryData data insertion mate x))
    (hash : String)
    (hashShape :
      TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape hash =
        true) :
    LabelIndexedSlidingMovies data insertion mate where
  family := oneLabel
  graphicalCertificateHash := hash
  graphical_certificate_hash_shape := hashShape

end TwistedYetter.Mutations.MissingLabelIndexedSlidingFamily
