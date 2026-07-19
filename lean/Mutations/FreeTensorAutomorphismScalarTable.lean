import TwistedYetter.Fusion.EGNOTensorAutomorphism

namespace TwistedYetter.Mutations.FreeTensorAutomorphismScalarTable

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

def rejected : TensorIdentityAutomorphism C where
  iso := Iso.refl (𝟭 C)
  monoidal := by
    change NatTrans.IsMonoidal (𝟙 (𝟭 C))
    infer_instance
  simpleScalar := fun _ => 1

end TwistedYetter.Mutations.FreeTensorAutomorphismScalarTable
