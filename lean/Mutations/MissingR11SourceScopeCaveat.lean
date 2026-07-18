import TwistedYetter.Kirby.HomologicallyTwistedInvariant

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations

open CategoryTheory
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.KirbyCompleteness

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

example
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH)
    [AddCommGroup H2]
    (evaluation :
      (presentation : SpecialKirbyPresentation manifold H2) →
        DecoratedKirbyPresentation categoryData presentation)
    (localStep :
      {source target : SpecialKirbyPresentation manifold H2} →
      (move : TableTwoMove source target) →
      (alpha : H2) →
        EvaluatedTableTwoStep
          categoryData (evaluation source) (evaluation target) move alpha)
    (prescriptionCertificateHash : String)
    (hash_shape :
      TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
        prescriptionCertificateHash = true)
    (sourceRefs : List String)
    (exactFormulaScope : String) :
    HomologicallyTwistedKirbyPrescription categoryData manifold H2 where
  evaluation := evaluation
  localStep := localStep
  prescriptionCertificateHash := prescriptionCertificateHash
  prescription_certificate_hash_shape := hash_shape
  sourceRefs := sourceRefs
  exactFormulaScope := exactFormulaScope

end TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations
