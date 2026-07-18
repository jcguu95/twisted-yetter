import TwistedYetter.Kirby.FourManifoldInvariantTarget

namespace TwistedYetter.Kirby.FourManifoldInvariantTarget.Mutations

open CategoryTheory
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
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
    (H2 : Type uH) [AddCommGroup H2]
    (prescription :
      HomologicallyTwistedKirbyPrescription categoryData manifold H2)
    (markedSystem : MarkedPairPresentationSystem manifold H2) :
    FourManifoldInvariantInputs categoryData manifold H2 where
  prescription := prescription
  markedSystem := markedSystem

end TwistedYetter.Kirby.FourManifoldInvariantTarget.Mutations
