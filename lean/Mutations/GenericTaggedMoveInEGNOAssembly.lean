import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant

namespace TwistedYetter.Mutations.GenericTaggedMoveInEGNOAssembly

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.PresentationIsotopy

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
    {source target : Boundary C}
    {before after : Diagram C source target}
    (move : TaggedMove before after) :
    PackageTaggedMove package before after :=
  .generic move

end TwistedYetter.Mutations.GenericTaggedMoveInEGNOAssembly
