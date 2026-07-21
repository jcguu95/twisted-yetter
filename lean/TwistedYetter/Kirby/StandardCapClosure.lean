import TwistedYetter.Kirby.BoundaryStandardization

/-!
# Closing a certified lower handlebody by the standard cap

Let `W_{\le 2}` be the lower handlebody and suppose its boundary has been
standardized as

`U_g = #^g (S^1 x S^2)`.

The standard cap is the four-dimensional genus-`g` one-handlebody viewed
upside down.  It contributes exactly `g` three-handles and one four-handle.

This file separates four facts that were previously hidden in one omnibus
"four-manifold correspondence":

1. the boundary movie produces an orientation-preserving diffeomorphism;
2. the genus of `U_g` is detected by first homology;
3. Laudenbach--Poenaru extends every self-diffeomorphism of `U_g` over the
   standard cap; and
4. an extending cap diffeomorphism induces a diffeomorphism of the glued
   closed four-manifolds.

Only item 1 was proved in `BoundaryStandardization` from movie semantics.
Items 2--4 remain individually visible topology inputs here.

Source boundary:

* `ref:laudenbach-poenaru-4d-handlebodies-1972`;
* `ref:moussard-lp-new-proof-2025`, Theorem 2.5.
-/

namespace TwistedYetter.Kirby.StandardCapClosure

open TwistedYetter.Kirby.BoundaryStandardization

universe uD uIso uSlide uM uHom uP uCapM uCapHom uX uXHom

/--
The genus of a standard boundary is a diffeomorphism invariant.

Mathematically this follows immediately from
`H_1(U_g; Z) = Z^g`.  It is kept separate from Kirby's surgery theorem and
from the Laudenbach--Poenaru extension theorem.
-/
structure StandardBoundaryGenusDetection
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    (semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus) where
  genus_eq_of_diffeomorphism :
    (leftGenus rightGenus : Nat) →
    semantics.orientedDiffeomorphism.Hom
      (semantics.standardBoundary leftGenus)
      (semantics.standardBoundary rightGenus) →
      leftGenus = rightGenus

/--
The standard four-dimensional cap and the restriction of its
orientation-preserving self-diffeomorphisms to the boundary.
-/
structure StandardCapTheory
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    (semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus) where
  FourManifoldWithBoundary : Type uCapM
  orientedDiffeomorphism :
    OrientedDiffeomorphismGroupoid.{uCapM, uCapHom}
      FourManifoldWithBoundary
  standardCap : Nat → FourManifoldWithBoundary
  boundaryRestriction :
    (genus : Nat) →
    orientedDiffeomorphism.Hom
      (standardCap genus) (standardCap genus) →
    semantics.orientedDiffeomorphism.Hom
      (semantics.standardBoundary genus)
      (semantics.standardBoundary genus)
  boundaryRestriction_identity :
    (genus : Nat) →
      boundaryRestriction genus
          (orientedDiffeomorphism.identity (standardCap genus)) =
        semantics.orientedDiffeomorphism.identity
          (semantics.standardBoundary genus)
  boundaryRestriction_compose :
    (genus : Nat) →
    (first second :
      orientedDiffeomorphism.Hom
        (standardCap genus) (standardCap genus)) →
      boundaryRestriction genus
          (orientedDiffeomorphism.compose first second) =
        semantics.orientedDiffeomorphism.compose
          (boundaryRestriction genus first)
          (boundaryRestriction genus second)
  boundaryRestriction_inverse :
    (genus : Nat) →
    (morphism :
      orientedDiffeomorphism.Hom
        (standardCap genus) (standardCap genus)) →
      boundaryRestriction genus
          (orientedDiffeomorphism.inverse morphism) =
        semantics.orientedDiffeomorphism.inverse
          (boundaryRestriction genus morphism)

/--
Exact formal interface of the Laudenbach--Poenaru theorem.

The result is a cap diffeomorphism together with the equation saying that its
boundary restriction is the requested map.  It is not a Boolean or a bare
existence proposition.
-/
structure LaudenbachPoenaruExtensionTheorem
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus}
    (cap : StandardCapTheory.{uD, uIso, uSlide, uM, uHom, uCapM, uCapHom}
      semantics) where
  extend :
    (genus : Nat) →
    (boundaryMap :
      semantics.orientedDiffeomorphism.Hom
        (semantics.standardBoundary genus)
        (semantics.standardBoundary genus)) →
    { capMap :
        cap.orientedDiffeomorphism.Hom
          (cap.standardCap genus) (cap.standardCap genus) //
      cap.boundaryRestriction genus capMap = boundaryMap }

/--
Smooth gluing of a lower handlebody to the standard cap.

`close lower genus standardization` includes the fixed orientation reversal
between the outward-oriented boundary of the lower handlebody and the
outward-oriented boundary of the cap.  Therefore `standardization` itself is
orientation preserving.

The last field is the ordinary gluing lemma: if a change of boundary
standardization extends over the cap, the two closed gluings are
diffeomorphic.
-/
structure StandardCapGluingTheory
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus}
    (lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus)
    (cap : StandardCapTheory.{uD, uIso, uSlide, uM, uHom, uCapM, uCapHom}
      semantics) where
  ClosedOrientedSmoothFourManifold : Type uX
  orientedDiffeomorphism :
    OrientedDiffeomorphismGroupoid.{uX, uXHom}
      ClosedOrientedSmoothFourManifold
  close :
    (lower : lowerTheory.Presentation) →
    (genus : Nat) →
    semantics.orientedDiffeomorphism.Hom
      (semantics.surgery
        (lowerTheory.boundarySurgeryDiagram lower))
      (semantics.standardBoundary genus) →
    ClosedOrientedSmoothFourManifold
  changeBoundaryStandardization :
    (lower : lowerTheory.Presentation) →
    (genus : Nat) →
    (first second :
      semantics.orientedDiffeomorphism.Hom
        (semantics.surgery
          (lowerTheory.boundarySurgeryDiagram lower))
        (semantics.standardBoundary genus)) →
    (capMap :
      cap.orientedDiffeomorphism.Hom
        (cap.standardCap genus) (cap.standardCap genus)) →
    cap.boundaryRestriction genus capMap =
      semantics.orientedDiffeomorphism.compose
        (semantics.orientedDiffeomorphism.inverse first) second →
    orientedDiffeomorphism.Hom
      (close lower genus first)
      (close lower genus second)

namespace BoundaryStandardizationCertificate

/-- Compare the two standard ends reached by two boundary certificates. -/
def standardBoundaryComparison
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {boundaryDiagram : calculus.Diagram}
    (semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus)
    (left right :
      BoundaryStandardizationCertificate calculus boundaryDiagram) :
    semantics.orientedDiffeomorphism.Hom
      (semantics.standardBoundary left.genus)
      (semantics.standardBoundary right.genus) :=
  semantics.orientedDiffeomorphism.compose
    (semantics.orientedDiffeomorphism.inverse
      (left.boundaryDiffeomorphism semantics))
    (right.boundaryDiffeomorphism semantics)

/--
Two valid standardizations of the same boundary necessarily have the same
genus.  The proof uses the separately named homology-rank input.
-/
theorem genus_unique
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {boundaryDiagram : calculus.Diagram}
    (semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus)
    (detector : StandardBoundaryGenusDetection semantics)
    (left right :
      BoundaryStandardizationCertificate calculus boundaryDiagram) :
    left.genus = right.genus :=
  detector.genus_eq_of_diffeomorphism
    left.genus right.genus
    (standardBoundaryComparison semantics left right)

end BoundaryStandardizationCertificate

namespace CertifiedClosedPresentation

/-- The actual closed four-manifold obtained by gluing the standard cap. -/
def closedManifold
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {cap : StandardCapTheory.{uD, uIso, uSlide, uM, uHom, uCapM, uCapHom}
      semantics}
    (gluing :
      StandardCapGluingTheory.{uD, uIso, uSlide, uM, uHom, uP,
        uCapM, uCapHom, uX, uXHom} lowerTheory cap)
    (presentation : CertifiedClosedPresentation lowerTheory) :
    gluing.ClosedOrientedSmoothFourManifold :=
  gluing.close presentation.lower
    presentation.boundaryCertificate.genus
    (presentation.boundaryCertificate.boundaryDiffeomorphism semantics)

end CertifiedClosedPresentation

/--
The closure of one fixed lower handlebody is independent of the chosen
boundary-standardization movie.

The proof does not assume an omnibus "same manifold" proposition:

1. compare the two movie-induced boundary diffeomorphisms;
2. detect that their standard genera agree;
3. extend their difference over the standard cap by Laudenbach--Poenaru; and
4. glue that extension to the identity of the lower handlebody.
-/
def closedCompletionChoiceDiffeomorphism
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {semantics : SurgerySemantics.{uD, uIso, uSlide, uM, uHom} calculus}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {cap : StandardCapTheory.{uD, uIso, uSlide, uM, uHom, uCapM, uCapHom}
      semantics}
    (detector : StandardBoundaryGenusDetection semantics)
    (extension : LaudenbachPoenaruExtensionTheorem cap)
    (gluing :
      StandardCapGluingTheory.{uD, uIso, uSlide, uM, uHom, uP,
        uCapM, uCapHom, uX, uXHom} lowerTheory cap)
    (lower : lowerTheory.Presentation)
    (left right :
      BoundaryStandardizationCertificate calculus
        (lowerTheory.boundarySurgeryDiagram lower)) :
    gluing.orientedDiffeomorphism.Hom
      (gluing.close lower left.genus
        (left.boundaryDiffeomorphism semantics))
      (gluing.close lower right.genus
        (right.boundaryDiffeomorphism semantics)) := by
  have genusEquality : left.genus = right.genus :=
    BoundaryStandardizationCertificate.genus_unique
      semantics detector left right
  rcases right with ⟨rightGenus, rightMovie⟩
  dsimp at genusEquality ⊢
  subst rightGenus
  let rightCertificate :
      BoundaryStandardizationCertificate calculus
        (lowerTheory.boundarySurgeryDiagram lower) :=
    ⟨left.genus, rightMovie⟩
  let comparison :
      semantics.orientedDiffeomorphism.Hom
        (semantics.standardBoundary left.genus)
        (semantics.standardBoundary left.genus) :=
    BoundaryStandardizationCertificate.standardBoundaryComparison
      semantics left rightCertificate
  let extended := extension.extend left.genus comparison
  exact gluing.changeBoundaryStandardization lower left.genus
    (left.boundaryDiffeomorphism semantics)
    (rightCertificate.boundaryDiffeomorphism semantics)
    extended.1 extended.2

end TwistedYetter.Kirby.StandardCapClosure
