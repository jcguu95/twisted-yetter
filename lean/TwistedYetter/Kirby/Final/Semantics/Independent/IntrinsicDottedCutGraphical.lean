import TwistedYetter.Kirby.Final.Semantics.Independent.DiagramLabeling

/-!
# Independent semantics: graphical interpretation of intrinsic dotted cuts

The component colouring is fixed by `labeling`.  Internal forward/dual atoms
are interpreted using rigidity.  No dotted direction or physical planar
strand orientation is accepted by any definition in this file.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

def intrinsicRibbonAtomObject
    (𝒞 : BundledPremodularCategory K)
    {Component : Type*}
    (colour : Component → 𝒞.simples.Simple) :
    IntrinsicRibbonAtom Component → 𝒞.C
  | ⟨component, .forward⟩ => 𝒞.simples.simpleObject (colour component)
  | ⟨component, .dual⟩ => (𝒞.simples.simpleObject (colour component))ᘁ

def intrinsicRibbonWordObject
    (𝒞 : BundledPremodularCategory K)
    {Component : Type*}
    (colour : Component → 𝒞.simples.Simple) :
    List (IntrinsicRibbonAtom Component) → 𝒞.C
  | [] => 𝟙_ 𝒞.C
  | atom :: rest =>
      intrinsicRibbonAtomObject 𝒞 colour atom ⊗
        intrinsicRibbonWordObject 𝒞 colour rest

def intrinsicRibbonWordAppendIso
    (𝒞 : BundledPremodularCategory K)
    {Component : Type*}
    (colour : Component → 𝒞.simples.Simple) :
    (left right : List (IntrinsicRibbonAtom Component)) →
      intrinsicRibbonWordObject 𝒞 colour (left ++ right) ≅
        intrinsicRibbonWordObject 𝒞 colour left ⊗
          intrinsicRibbonWordObject 𝒞 colour right
  | [], right => (λ_ (intrinsicRibbonWordObject 𝒞 colour right)).symm
  | atom :: rest, right =>
      whiskerLeftIso (intrinsicRibbonAtomObject 𝒞 colour atom)
          (intrinsicRibbonWordAppendIso 𝒞 colour rest right) ≪≫
        (α_ (intrinsicRibbonAtomObject 𝒞 colour atom)
          (intrinsicRibbonWordObject 𝒞 colour rest)
          (intrinsicRibbonWordObject 𝒞 colour right)).symm

/-- Interpret the free intrinsic grammar in an arbitrary premodular category. -/
noncomputable def interpretIntrinsicRibbonTangle
    (𝒞 : BundledPremodularCategory K)
    {Component : Type*}
    (colour : Component → 𝒞.simples.Simple) :
    {source target : List (IntrinsicRibbonAtom Component)} →
      IntrinsicRibbonTangle Component source target →
        (intrinsicRibbonWordObject 𝒞 colour source ⟶
          intrinsicRibbonWordObject 𝒞 colour target)
  | _, _, .identity _ => 𝟙 _
  | _, _, .compose first second =>
      interpretIntrinsicRibbonTangle 𝒞 colour first ≫
        interpretIntrinsicRibbonTangle 𝒞 colour second
  | _, _, .tensor left right =>
      (intrinsicRibbonWordAppendIso
          𝒞 colour _ _).hom ≫
        (interpretIntrinsicRibbonTangle 𝒞 colour left ⊗ₘ
          interpretIntrinsicRibbonTangle 𝒞 colour right) ≫
        (intrinsicRibbonWordAppendIso
          𝒞 colour _ _).inv
  | _, _, .coevaluation component =>
      let X := 𝒞.simples.simpleObject (colour component)
      η_ X (Xᘁ) ≫
        (ρ_ (X ⊗ Xᘁ)).inv ≫
        (α_ X (Xᘁ) (𝟙_ 𝒞.C)).hom
  | _, _, .evaluation component =>
      let X := 𝒞.simples.simpleObject (colour component)
      (α_ (Xᘁ) X (𝟙_ 𝒞.C)).inv ≫
        (ε_ X (Xᘁ) ⊗ₘ 𝟙 (𝟙_ 𝒞.C)) ≫
        (λ_ (𝟙_ 𝒞.C)).hom
  | _, _, .positiveCrossing left right =>
      let X := intrinsicRibbonAtomObject 𝒞 colour left
      let Y := intrinsicRibbonAtomObject 𝒞 colour right
      (α_ X Y (𝟙_ 𝒞.C)).inv ≫
        ((β_ X Y).hom ⊗ₘ 𝟙 (𝟙_ 𝒞.C)) ≫
        (α_ Y X (𝟙_ 𝒞.C)).hom
  | _, _, .negativeCrossing left right =>
      let X := intrinsicRibbonAtomObject 𝒞 colour left
      let Y := intrinsicRibbonAtomObject 𝒞 colour right
      (α_ X Y (𝟙_ 𝒞.C)).inv ≫
        ((β_ Y X).inv ⊗ₘ 𝟙 (𝟙_ 𝒞.C)) ≫
        (α_ Y X (𝟙_ 𝒞.C)).hom
  | _, _, .positiveTwist strand =>
      let X := intrinsicRibbonAtomObject 𝒞 colour strand
      𝒞.twist.hom.app X ⊗ₘ 𝟙 (𝟙_ 𝒞.C)
  | _, _, .negativeTwist strand =>
      let X := intrinsicRibbonAtomObject 𝒞 colour strand
      𝒞.twist.inv.app X ⊗ₘ 𝟙 (𝟙_ 𝒞.C)

theorem intrinsicBoundaryWordObject_eq_simpleLabelWordObject
    (𝒞 : BundledPremodularCategory K)
    {Component : Type*}
    (colour : Component → 𝒞.simples.Simple)
    (components : List Component) :
    intrinsicRibbonWordObject 𝒞 colour
        (intrinsicBoundaryWord components) =
      simpleLabelWordObject 𝒞 (components.map colour) := by
  induction components with
  | nil => rfl
  | cons component rest ih =>
      simpa [intrinsicBoundaryWord, intrinsicRibbonAtomObject] using
        congrArg
          (fun object =>
            𝒞.simples.simpleObject (colour component) ⊗ object)
          ih

/--
Interpret an intrinsic dotted cut syntax as a morphism between its two public
component-colour boundary words.
-/
noncomputable def interpretIntrinsicDottedCutTangle
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    {punctures : List (DottedPuncture diagram.trace)}
    (cut : IntrinsicDottedCutTangle diagram punctures) :
    simpleLabelWordObject 𝒞
          ((intrinsicDottedCutInputWord diagram punctures).map labeling) ⟶
      simpleLabelWordObject 𝒞
          ((intrinsicDottedCutOutputWord diagram punctures).map labeling) :=
  eqToHom
      (intrinsicBoundaryWordObject_eq_simpleLabelWordObject
        𝒞 labeling (intrinsicDottedCutInputWord diagram punctures)).symm ≫
    interpretIntrinsicRibbonTangle 𝒞 labeling cut.term ≫
    eqToHom
      (intrinsicBoundaryWordObject_eq_simpleLabelWordObject
        𝒞 labeling (intrinsicDottedCutOutputWord diagram punctures))

theorem intrinsicDottedCutInputLabels_eq
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    (intrinsicDottedCutInputWord diagram punctures).map labeling =
      dottedInboundLabelWord 𝒞 diagram labeling punctures := by
  simp only [intrinsicDottedCutInputWord, dottedInboundLabelWord,
    List.map_map]
  rfl

theorem intrinsicDottedCutOutputLabels_eq
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    (intrinsicDottedCutOutputWord diagram punctures).map labeling =
      dottedOutboundLabelWord 𝒞 diagram labeling punctures := by
  simp only [intrinsicDottedCutOutputWord, dottedOutboundLabelWord,
    List.map_map]
  rfl

/--
The intrinsic cut syntax produces the exact morphism type required by the
representative-independence naturality theorem.  The endpoint casts only
unfold component-index bookkeeping; they never compare `X` with `X*`.
-/
noncomputable def intrinsicDottedCutMorphism
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    {punctures : List (DottedPuncture diagram.trace)}
    (cut : IntrinsicDottedCutTangle diagram punctures) :
    DottedIncidenceMorphism 𝒞 diagram labeling punctures :=
  eqToHom
      (congrArg (simpleLabelWordObject 𝒞)
        (intrinsicDottedCutInputLabels_eq
          𝒞 diagram labeling punctures)).symm ≫
    interpretIntrinsicDottedCutTangle 𝒞 diagram labeling cut ≫
    eqToHom
      (congrArg (simpleLabelWordObject 𝒞)
        (intrinsicDottedCutOutputLabels_eq
          𝒞 diagram labeling punctures))

end

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 2783
