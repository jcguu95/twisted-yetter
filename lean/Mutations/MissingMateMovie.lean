import TwistedYetter.Kirby.KirbyColorEncirclingTransport

namespace TwistedYetter.Mutations.MissingMateMovie

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Kirby.KirbyColorEncirclingTransport

universe uR uD vD uS uI

variable {R : Type uR} [CommSemiring R]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable [MonoidalCategory D] [BraidedCategory D]
variable [MonoidalPreadditive D] [MonoidalLinear R D]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

-- Expected failure: a braided channel cannot be renamed a mated channel
-- without a certified cup/cap movie.
def forgedFiber
    (data : EncirclingTransportData (R := R) (D := D) (S := S) (I := I))
    (strand : D)
    (forwardContext : (y : S) →
      Context D
        (.atom (data.fixed ⊗ data.dualSimple y))
        (.atom (data.fixed ⊗ data.dualSimple y))
        (.atom (data.fixed ⊗ strand))
        (.atom (data.fixed ⊗ strand)))
    (backwardContext : (z : S) →
      Context D
        (.atom (data.dualSimple z ⊗ data.fixed))
        (.atom (data.dualSimple z ⊗ data.fixed))
        (.atom (data.fixed ⊗ strand))
        (.atom (data.fixed ⊗ strand)))
    (braidedChannel : (y z : S) → I y z →
      Diagram D
        (.atom (data.fixed ⊗ strand))
        (.atom (data.fixed ⊗ strand)))
    (braidingMovie : (y z : S) → (i : I y z) →
      Movie
        (Context.plug D (forwardContext y)
          (Diagram.coupon "kirby-encircling-forward-channel"
            (data.forwardProjection y z i ≫ data.forwardInclusion y z i)))
        (braidedChannel y z i)) :
    EncirclingTransportFiber data strand where
  forwardContext := forwardContext
  backwardContext := backwardContext
  braidedChannel := braidedChannel
  braidingMovie := braidingMovie

end TwistedYetter.Mutations.MissingMateMovie
