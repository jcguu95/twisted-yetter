import TwistedYetter.Fusion.FiniteResolution

namespace TwistedYetter.Mutations.MissingDualBasisProof

open TwistedYetter.Fusion.FiniteResolution

universe uR uV uW uI

variable {R : Type uR} {V : Type uV} {W : Type uW} {ι : Type uI}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]
variable [Fintype ι] [DecidableEq ι]

-- Expected failure: vectors cannot be called a dual basis without the exact
-- equality to the algebraic dual basis.
def forgedDualBasis
    (pairing : PerfectPairing R V W)
    (basis : Module.Basis ι R V)
    (vectors : ι → W) :
    DualBasisData (ι := ι) pairing where
  primal := basis
  dual := vectors

end TwistedYetter.Mutations.MissingDualBasisProof
