import TwistedYetter.Fusion.EGNOTensorAutomorphism

namespace TwistedYetter.Mutations.MissingTensorAutomorphismMonoidality

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

def rejected : TensorIdentityAutomorphism C where
  iso := Iso.refl (𝟭 C)

end TwistedYetter.Mutations.MissingTensorAutomorphismMonoidality
