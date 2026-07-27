import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# Source-faithful framed-kink input for premodular categories

This is the small part of the former modular graphical environment used by
the role-aware main line.  It contains no modularity, Kirby colour, handle
move, or evaluator equality.
-/

namespace TwistedYetter.Kirby.EGNOModularKirbyMoves

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.PresentationIsotopy

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance premodularFramedKinkRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/--
The two blackboard-framing equations obtained by interpreting framed kinks in
the category's stored ribbon structure.
-/
structure RibbonFramedKinkLaw
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  positive_sound :
    (X : C) →
      Diagram.eval C (positiveKink data.ribbon X) =
        (NaturalTwist.ofRibbon data.ribbon).iso.hom.app X
  negative_sound :
    (X : C) →
      Diagram.eval C (negativeKink data.ribbon X) =
        (NaturalTwist.ofRibbon data.ribbon).iso.inv.app X
  source_ref : String := "ref:shum-tortile-1994"
  source_locator : String :=
    "Shum (1994), main framed-tangle coherence theorem; "
      ++ "Crane-Yetter, State-Sum Invariants I, Theorem 2.6"

namespace LiteratureBackedModularGraphicalEnvironment

/--
Shum's tortile coherence theorem, specialized exactly to
`RibbonFramedKinkLaw`.

References:
* M. C. Shum, *Tortile tensor categories*, J. Pure Appl. Algebra 93
  (1994), 57--110, main coherence theorem.
* L. Crane and D. Yetter, *State-Sum Invariants of 4-Manifolds I*,
  Theorem 2.6, which states that the free tortile category on one object is
  monoidally equivalent to framed tangles.
-/
axiom shum_ribbonFramedKink
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    RibbonFramedKinkLaw 𝒞

end LiteratureBackedModularGraphicalEnvironment
end TwistedYetter.Kirby.EGNOModularKirbyMoves
