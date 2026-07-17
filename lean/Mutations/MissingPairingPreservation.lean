import TwistedYetter.Fusion.PairingTransport

namespace TwistedYetter.Mutations.MissingPairingPreservation

open TwistedYetter.Fusion
open TwistedYetter.Fusion.FiniteResolution

universe uR uV uW uV' uW'

variable {R : Type uR}
variable {V : Type uV} {W : Type uW}
variable {V' : Type uV'} {W' : Type uW'}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]
variable [AddCommMonoid V'] [Module R V']
variable [AddCommMonoid W'] [Module R W']

-- Expected failure: two linear equivalences alone cannot be promoted to mate
-- transport without a proof that they preserve the pairing.
def forgedTransport
    (source : PerfectPairing R V W)
    (target : PerfectPairing R V' W')
    (primalEquiv : V ≃ₗ[R] V')
    (dualEquiv : W ≃ₗ[R] W') :
    PairingTransport source target where
  primalEquiv := primalEquiv
  dualEquiv := dualEquiv

end TwistedYetter.Mutations.MissingPairingPreservation
