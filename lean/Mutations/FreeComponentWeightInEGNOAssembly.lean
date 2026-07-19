import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant

namespace TwistedYetter.Mutations.FreeComponentWeightInEGNOAssembly

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
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

example
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2)
    (component : ComponentSpec)
    (simple : S)
    (freeCoefficient : K) :
    componentWeight data automorphism topology alpha component simple =
      freeCoefficient := by
  rfl

end TwistedYetter.Mutations.FreeComponentWeightInEGNOAssembly
