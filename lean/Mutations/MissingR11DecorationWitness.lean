import TwistedYetter.Kirby.HomologicallyTwistedInvariant

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

example
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH}
    (topology : SpecialKirbyPresentation manifold H2)
    (diagram : H2 → Diagram C .unit .unit)
    (evaluationState : H2 → EvaluationState (K := K))
    (counts_sound :
      (alpha : H2) → (evaluationState alpha).counts = topology.counts)
    (raw_sound :
      (alpha : H2) →
        (evaluationState alpha).rawNumerator =
          categoryData.closedScalar (Diagram.eval C (diagram alpha)))
    (diagramRepresents : H2 → Prop)
    (diagram_witness : (alpha : H2) → diagramRepresents alpha)
    (decorationRepresents : H2 → Prop)
    (diagramCertificateHash decorationCertificateHash : String)
    (diagram_hash_shape :
      TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
        diagramCertificateHash = true)
    (decoration_hash_shape :
      TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
        decorationCertificateHash = true) :
    DecoratedKirbyPresentation categoryData topology where
  diagram := diagram
  evaluationState := evaluationState
  counts_sound := counts_sound
  raw_numerator_sound := raw_sound
  diagramRepresentsFormalPresentation := diagramRepresents
  diagram_representation_witness := diagram_witness
  decorationRepresentsClass := decorationRepresents
  diagramCertificateHash := diagramCertificateHash
  diagram_certificate_hash_shape := diagram_hash_shape
  decorationCertificateHash := decorationCertificateHash
  decoration_certificate_hash_shape := decoration_hash_shape

end TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations
