import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant

namespace TwistedYetter.Mutations.OrdinarySlideAsGeneralized

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.KirbyHandleMoves

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

def rejected
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {before after :
      TwistedYetter.Kirby.LinearDiagram (R := K) (C := C) .unit .unit}
    (slide : BoundOrdinarySlide package .oneOverOne .positive
      "move" "source" "target" before after) :
    BoundGeneralizedSlide package before after :=
  slide

end TwistedYetter.Mutations.OrdinarySlideAsGeneralized
