import TwistedYetter.Fusion.PairingTransport

namespace TwistedYetter.Mutations.WrongTransportedDualIndex

open TwistedYetter.Fusion
open TwistedYetter.Fusion.FiniteResolution

universe uR uV uW uV' uW' uI

variable {R : Type uR}
variable {V : Type uV} {W : Type uW}
variable {V' : Type uV'} {W' : Type uW'}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]
variable [AddCommMonoid V'] [Module R V']
variable [AddCommMonoid W'] [Module R W']
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]

-- Expected failure: the transported dual vector indexed by j pairs with basis
-- vector i as delta(i,j), not delta(i,i).
theorem forgedDiagonalPairing
    {source : PerfectPairing R V W}
    {target : PerfectPairing R V' W'}
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (i j : ι) :
    target.pair
        (transport.primalBasis data i)
        (transport.dualVector data j) =
      if i = i then 1 else 0 := by
  exact transport.pair_primal_dual data i j

end TwistedYetter.Mutations.WrongTransportedDualIndex
