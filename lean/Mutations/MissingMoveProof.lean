import TwistedYetter.Kirby.CategoricalMovie

namespace TwistedYetter.Mutations.MissingMoveProof

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalMovie

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]
variable {source target : Boundary C}
variable (before after : Diagram C source target)

-- Expected failure: a move cannot be constructed without evaluator equality.
def forgedMove : CertifiedMove before after where
  label := "forged-without-proof"

end TwistedYetter.Mutations.MissingMoveProof
