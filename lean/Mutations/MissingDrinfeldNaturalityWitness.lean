import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.MissingDrinfeldNaturalityWitness

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
This must fail: objectwise isomorphisms do not become a natural isomorphism
without a proof that every morphism makes the naturality square commute.
-/
def missingNaturalityWitness : 𝟭 C ≅ rightDoubleDualFunctor C :=
  NatIso.ofComponents (fun X => drinfeldIso X)

end TwistedYetter.Mutations.MissingDrinfeldNaturalityWitness
