import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.OverrideTrivialGeneratorScalar

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
This must fail: the identity-control constructor cannot retain its proof while
an arbitrary caller replaces the scalar action on simple objects.
-/
def unsafeOverride
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (replacement : S → Kˣ) :
    TensorAutomorphismGenerator categoryData :=
  { TensorAutomorphismGenerator.trivial categoryData with
      simpleScalar := replacement }

end TwistedYetter.Mutations.OverrideTrivialGeneratorScalar
