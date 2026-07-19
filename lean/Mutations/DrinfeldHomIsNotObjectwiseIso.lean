import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.DrinfeldHomIsNotObjectwiseIso

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
This must fail: a forward morphism alone is not an objectwise isomorphism.
The inverse data and its two inverse laws cannot be omitted.
-/
def homOnlyCandidate : 𝟭 C ≅ rightDoubleDualFunctor C :=
  NatIso.ofComponents (fun X => drinfeldHom X) (fun _ => by simp)

end TwistedYetter.Mutations.DrinfeldHomIsNotObjectwiseIso
