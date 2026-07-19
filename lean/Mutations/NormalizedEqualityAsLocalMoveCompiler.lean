import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant

namespace TwistedYetter.Mutations.NormalizedEqualityAsLocalMoveCompiler

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

def rejected
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation :
      PresentationCompiler data package automorphism manifold H2}
    (finalEquality :
      {source target : SpecialKirbyPresentation manifold H2} →
      (move : TableTwoMove source target) →
      (alpha : H2) →
        presentation.value source alpha =
          presentation.value target
            (move.homologyTransport.targetClass alpha)) :
    LocalMoveCompiler data package automorphism manifold H2 presentation :=
  finalEquality

end TwistedYetter.Mutations.NormalizedEqualityAsLocalMoveCompiler
