import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.MissingUnitQuantumDimensionCertificate

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularKirbyMoves

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

def rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (nonzero : globalDimension data ≠ 0) :
    ModularDimensionCertificate data center where
  global_dimension_ne_zero := nonzero

end TwistedYetter.Mutations.MissingUnitQuantumDimensionCertificate
