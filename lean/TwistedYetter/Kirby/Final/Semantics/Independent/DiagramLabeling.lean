import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

/-!
# Independent semantics: labels on a special Kirby diagram

This file contains the category-valued data shared by the intrinsic
cut-open syntax and the final evaluator.  In particular, it does not define
an evaluator or compile a diagram.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK

noncomputable section

abbrev TwoHandleLabeling
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram) :=
  Fin diagram.handles.hTwo → 𝒞.simples.Simple

instance
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram) :
    Fintype (TwoHandleLabeling 𝒞 diagram) :=
  inferInstance

/-!
## Dotted-handle incidence words

These words are the domain and codomain of the local morphism used in the
homology representative-independence argument.  Each factor reads the
simple label assigned once to its ordinary two-handle component.  Puncture
direction only partitions occurrences into domain and codomain; it never
chooses a dual object and never creates a character exponent.
-/

/-- The ordinary two-handle index named by one dotted puncture. -/
def dottedPunctureTwoHandleIndex
    (diagram : SpecialKirbyDiagram)
    (puncture : DottedPuncture diagram.trace) :
    Fin diagram.handles.hTwo :=
  diagram.handles.twoHandleIndex.symm
    ⟨puncture.twoHandleComponent, puncture.two_handle_role⟩

/-- Inbound punctures, expressed in the ordinary two-handle basis. -/
def dottedInboundTwoHandleWord
    (diagram : SpecialKirbyDiagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List (Fin diagram.handles.hTwo) :=
  (dottedInboundPunctures punctures).map
    (dottedPunctureTwoHandleIndex diagram)

/-- Outbound punctures, expressed in the ordinary two-handle basis. -/
def dottedOutboundTwoHandleWord
    (diagram : SpecialKirbyDiagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List (Fin diagram.handles.hTwo) :=
  (dottedOutboundPunctures punctures).map
    (dottedPunctureTwoHandleIndex diagram)

def dottedIncidenceLabel
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    𝒞.simples.Simple :=
  labeling (dottedPunctureTwoHandleIndex diagram puncture)

def dottedInboundLabelWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List 𝒞.simples.Simple :=
  (dottedInboundTwoHandleWord diagram punctures).map labeling

def dottedOutboundLabelWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List 𝒞.simples.Simple :=
  (dottedOutboundTwoHandleWord diagram punctures).map labeling

/-- Tensor product of component labels without reading strand orientation. -/
def simpleLabelWordObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    List 𝒞.simples.Simple → 𝒞.C
  | [] => 𝟙_ 𝒞.C
  | label :: rest =>
      𝒞.simples.simpleObject label ⊗ simpleLabelWordObject 𝒞 rest

/--
The exact type of the local dotted-handle morphism used by representative
independence.  This is only a type, not an assumed morphism and not an
evaluation equality.
-/
def DottedIncidenceMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) : Type _ :=
  simpleLabelWordObject 𝒞
      (dottedInboundLabelWord 𝒞 diagram labeling punctures) ⟶
    simpleLabelWordObject 𝒞
      (dottedOutboundLabelWord 𝒞 diagram labeling punctures)

end

end TwistedYetter.Semantics.Independent
