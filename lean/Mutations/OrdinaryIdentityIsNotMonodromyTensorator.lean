import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.OrdinaryIdentityIsNotMonodromyTensorator

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
The underlying monodromy functor reduces to the identity, so this deliberately
selects the ordinary identity monoidal structure instead of the transported
double-braiding structure.
-/
@[implicit_reducible]
def ordinaryIdentityMonoidal :
    (monodromyIdFunctor (C := C)).Monoidal := by
  change (𝟭 C).Monoidal
  infer_instance

/--
This must fail: the ordinary identity tensorator is not definitionally the
positive double braiding.
-/
example (X Y : C) :
    @Functor.LaxMonoidal.μ C _ _ C _ _
        (monodromyIdFunctor (C := C))
        (ordinaryIdentityMonoidal (C := C)).toLaxMonoidal X Y =
      monodromyHom X Y := by
  rfl

end TwistedYetter.Mutations.OrdinaryIdentityIsNotMonodromyTensorator
