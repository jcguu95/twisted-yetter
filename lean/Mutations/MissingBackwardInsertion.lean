import TwistedYetter.Kirby.GeneralizedSliding

namespace TwistedYetter.Mutations.MissingBackwardInsertion

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Kirby.GeneralizedSliding

universe uR uD vD uS uI

variable {R : Type uR} [CommSemiring R]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable [MonoidalCategory D] [BraidedCategory D]
variable [MonoidalPreadditive D] [MonoidalLinear R D]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

-- Expected failure: forward insertion and duality do not authorize the final
-- collapse unless the inverse identity resolution is also proved.
def forgedSlidingData
    (fixed : D)
    (weight : S → R)
    (simple dualSimple : S → D)
    (matedPairing : (y z : S) →
      PerfectPairing R
        (simple y ⟶ dualSimple z ⊗ fixed)
        (dualSimple z ⊗ fixed ⟶ simple y))
    (matedFamily : (y z : S) →
      BiorthogonalFamily (ι := I y z) (matedPairing y z))
    (forwardProjection : (y z : S) → I y z →
      (fixed ⊗ dualSimple y ⟶ simple z))
    (forwardInclusion : (y z : S) → I y z →
      (simple z ⟶ fixed ⊗ dualSimple y))
    (forwardSound : (y : S) →
      ∑ z, ∑ i : I y z,
        weight z •
          (forwardProjection y z i ≫ forwardInclusion y z i) =
        𝟙 (fixed ⊗ dualSimple y)) :
    SlidingCategoryData (R := R) (D := D) (S := S) (I := I) where
  fixed := fixed
  weight := weight
  simple := simple
  dualSimple := dualSimple
  matedPairing := matedPairing
  matedFamily := matedFamily
  forwardProjection := forwardProjection
  forwardInclusion := forwardInclusion
  forwardSound := forwardSound

end TwistedYetter.Mutations.MissingBackwardInsertion
