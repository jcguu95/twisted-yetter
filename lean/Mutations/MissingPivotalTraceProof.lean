import TwistedYetter.Fusion.PivotalMate

namespace TwistedYetter.Mutations.MissingPivotalTraceProof

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Fusion.PivotalMate

universe uR uC vC uD vD

variable {R : Type uR} [CommSemiring R]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [MonoidalLinear R C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable [MonoidalCategory D] [MonoidalPreadditive D]
variable [MonoidalLinear R D]
variable (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear R]

-- Expected failure: being linear and strong monoidal does not silently
-- provide the pivotal trace-pairing theorem.
def forgedPivotalTrace
    {X Y' Z : C}
    (source :
      PerfectPairing R (Z ⟶ X ⊗ Y') (X ⊗ Y' ⟶ Z))
    (image :
      PerfectPairing R
        (F.obj Z ⟶ F.obj X ⊗ F.obj Y')
        (F.obj X ⊗ F.obj Y' ⟶ F.obj Z)) :
    PivotalTraceCompatibility (R := R) F source image where

end TwistedYetter.Mutations.MissingPivotalTraceProof
