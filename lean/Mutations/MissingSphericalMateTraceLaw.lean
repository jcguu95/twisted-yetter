import TwistedYetter.Fusion.EGNOTracePairing

namespace TwistedYetter.Mutations.MissingSphericalMateTraceLaw

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: spherical structure alone does not silently manufacture the
source-bound all-objects mate trace theorem.
-/
noncomputable def forgedMateTransport
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (spherical : SphericalStructure (C := C))
    (X Y Z : C) :
    PairingTransport
      (data.pivotalTracePerfectPairing
        spherical.toPivotalStructure Z (X ⊗ (Yᘁ)))
      (data.pivotalTracePerfectPairing
        spherical.toPivotalStructure Y ((Zᘁ) ⊗ X)) :=
  data.sphericalMatePairingTransport spherical X Y Z

end TwistedYetter.Mutations.MissingSphericalMateTraceLaw
