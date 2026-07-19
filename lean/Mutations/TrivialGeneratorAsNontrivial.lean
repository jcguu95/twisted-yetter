import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.TrivialGeneratorAsNontrivial

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
This must fail: the identity control and a chosen simple do not establish the
required nontrivial scalar witness.
-/
def unsafeSelection
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (simple : S) :
    NontrivialTensorAutomorphismGenerator categoryData where
  generator := TensorAutomorphismGenerator.trivial categoryData
  witnessSimple := simple

end TwistedYetter.Mutations.TrivialGeneratorAsNontrivial
