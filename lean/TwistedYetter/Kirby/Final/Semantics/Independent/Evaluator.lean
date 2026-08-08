import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology
import TwistedYetter.Kirby.Final.Semantics.Independent.DottedTopologyAxioms

/-!
# Independent semantics: role-aware THAM-side evaluator

The definition below starts from a finite combinatorial special Kirby
diagram.  It does not start from a knot in `S³`, and it does not reuse an
existing evaluator.

Ordinary and specially-dotted two-handle components are summed over the
simple labels.  Literal dotted one-handle components are never assigned an
ordinary Kirby-colour label: every dotted puncture is compiled using the
normalized tensor-unit projector.

The displayed diagram keeps ordinary Kirby-calculus names.  Before evaluating,
the handle decomposition is read upside down as in Tham, Definition 5.11:
primal one-handles are THAM three-handles, primal two-handles remain
two-handles, and primal three-handles are THAM one-handles.  Character
exponents therefore come only from explicit two-handle coefficients.  The
unrecorded primal three-handle attachments are not evaluator inputs.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC uS v

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

def ordinaryKirbyWeight
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {diagram : SpecialKirbyDiagram}
    (labeling : TwoHandleLabeling 𝒞 diagram) : K :=
  ∏ handle, 𝒞.simples.quantumDimension (labeling handle)

noncomputable def characterWeight
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {diagram : SpecialKirbyDiagram}
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (coefficients : ThamTwoHandleCoefficients diagram) : K :=
  ((∏ handle,
      (𝒞η.character.value (labeling handle)) ^
        coefficients handle) : Kˣ)

/-!
The displayed formula stores the homological character exactly once, in
`characterWeight`.  A character coupon may be introduced later as a
graphical proof device when this scalar action is rewritten using Schur's
lemma and monoidal naturality; it is not inserted a second time by the
presentation compiler.
-/

/-- Convert the stored strand orientation to the graphical direction. -/
def ribbonDirectionOfStrandOrientation : StrandOrientation → RibbonDirection
  | .positive => .forward
  | .negative => .dual

def ribbonCrossingSign : CrossingSign → RibbonCrossingSign
  | .positive => .positive
  | .negative => .negative

/--
Read the simple label carried by one strand of the cut-open exterior.

The fallback to the tensor unit is definitionally total but unreachable on
every active exterior word by
`CutOpenExteriorTrace.activeStrandsAreTwoHandles`.
-/
def exteriorStrandLabel
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strand : diagram.trace.StrandId) :
    𝒞.simples.Simple :=
  let component := (diagram.trace.strands strand).component
  if role : (diagram.trace.components component).role ≠ .dotted then
    labeling (diagram.handles.twoHandleIndex.symm ⟨component, role⟩)
  else
    𝒞.simples.tensorUnit

def orientedExteriorStrand
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strand : diagram.trace.StrandId) :
    OrientedSimple 𝒞 where
  label := exteriorStrandLabel 𝒞 diagram labeling strand
  direction :=
    ribbonDirectionOfStrandOrientation
      (diagram.trace.strands strand).orientation

def exteriorWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strands : List diagram.trace.StrandId) :
    RibbonWord 𝒞 :=
  strands.map (orientedExteriorStrand 𝒞 diagram labeling)

/-!
## Dotted-handle incidence words

These words are the domain and codomain of the local morphism used in the
homology representative-independence argument.  They are intentionally not
the oriented strand word at the projector waist.

Each factor reads the simple label assigned once to its ordinary two-handle
component.  Puncture direction only decides whether the occurrence belongs
to the domain or codomain; it never chooses a dual object and never creates a
character exponent.
-/

def dottedIncidenceLabel
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    𝒞.simples.Simple :=
  labeling
    (diagram.handles.twoHandleIndex.symm
      ⟨puncture.twoHandleComponent, puncture.two_handle_role⟩)

def dottedInboundLabelWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List 𝒞.simples.Simple :=
  (dottedInboundPunctures punctures).map
    (dottedIncidenceLabel 𝒞 diagram labeling)

def dottedOutboundLabelWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List 𝒞.simples.Simple :=
  (dottedOutboundPunctures punctures).map
    (dottedIncidenceLabel 𝒞 diagram labeling)

/-- Tensor product of component labels without reading strand orientation. -/
def simpleLabelWordObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    List 𝒞.simples.Simple → 𝒞.C
  | [] => 𝟙_ 𝒞.C
  | label :: rest =>
      𝒞.simples.simpleObject label ⊗ simpleLabelWordObject 𝒞 rest

/--
The exact type of the local dotted-handle morphism required by the corrected
representative-independence proof.  This is only a type, not an assumed
morphism and not an evaluation equality.  `intrinsicDottedCutMorphism`
constructs a term of this type from the independent intrinsic ribbon grammar.
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

/--
The object at one all-strand projector-waist port.  Both its label and its
ribbon direction come from the original exterior strand.  This is not the
inbound/outbound incidence factor used for representative independence.
The oriented intersection with the dotted disk never decides whether this
waist object is `X` or `Xᘁ`.
-/
def orientedCutBoundaryPuncture
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    OrientedSimple 𝒞 where
  label :=
    exteriorStrandLabel 𝒞 diagram labeling puncture.inputStrand
  direction :=
    ribbonDirectionOfStrandOrientation
      (diagram.trace.strands puncture.inputStrand).orientation

def cutBoundaryWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    RibbonWord 𝒞 :=
  punctures.map (orientedCutBoundaryPuncture 𝒞 diagram labeling)

/-!
`cutBoundaryWord` is retained as the historical name of the all-strand
projector-waist word.  It must not be used as a substitute for
`dottedInboundLabelWord` or `dottedOutboundLabelWord`.
-/

theorem orientedExteriorInput_eq_cutBoundaryPuncture
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    orientedExteriorStrand 𝒞 diagram labeling puncture.inputStrand =
      orientedCutBoundaryPuncture 𝒞 diagram labeling puncture := by
  apply congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
  · rfl
  · rfl

theorem orientedExteriorOutput_eq_cutBoundaryPuncture
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    orientedExteriorStrand 𝒞 diagram labeling puncture.outputStrand =
      orientedCutBoundaryPuncture 𝒞 diagram labeling puncture := by
  have component_eq :
      (diagram.trace.strands puncture.outputStrand).component =
        (diagram.trace.strands puncture.inputStrand).component :=
    puncture.output_on_two_handle.trans puncture.input_on_two_handle.symm
  apply congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
  · unfold exteriorStrandLabel
    rw [component_eq]
  · calc
      ribbonDirectionOfStrandOrientation
          (diagram.trace.strands puncture.outputStrand).orientation =
        ribbonDirectionOfStrandOrientation
          (diagram.trace.strands puncture.inputStrand).orientation :=
            congrArg ribbonDirectionOfStrandOrientation
              puncture.orientation_preserved.symm

theorem exteriorInputWord_eq_cutBoundaryWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    exteriorWord 𝒞 diagram labeling
        (punctures.map DottedPuncture.inputStrand) =
      cutBoundaryWord 𝒞 diagram labeling punctures := by
  induction punctures with
  | nil => rfl
  | cons puncture rest ih =>
      simp only [List.map_cons, exteriorWord, cutBoundaryWord]
      rw [orientedExteriorInput_eq_cutBoundaryPuncture]
      congr 1

theorem exteriorOutputWord_eq_cutBoundaryWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    exteriorWord 𝒞 diagram labeling
        (punctures.map DottedPuncture.outputStrand) =
      cutBoundaryWord 𝒞 diagram labeling punctures := by
  induction punctures with
  | nil => rfl
  | cons puncture rest ih =>
      simp only [List.map_cons, exteriorWord, cutBoundaryWord]
      rw [orientedExteriorOutput_eq_cutBoundaryPuncture]
      congr 1

def ribbonWordAppendIso
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    (left right : RibbonWord 𝒞) →
      ribbonWordObject 𝒞 (List.append left right) ≅
        ribbonWordObject 𝒞 left ⊗ ribbonWordObject 𝒞 right
  | [], right => (λ_ (ribbonWordObject 𝒞 right)).symm
  | strand :: rest, right =>
      whiskerLeftIso (orientedSimpleObject 𝒞 strand)
          (ribbonWordAppendIso 𝒞 rest right) ≪≫
        (α_ (orientedSimpleObject 𝒞 strand)
          (ribbonWordObject 𝒞 rest)
          (ribbonWordObject 𝒞 right)).symm

theorem exteriorStrandLabel_eq_of_component_eq
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    {left right : diagram.trace.StrandId}
    (component_eq :
      (diagram.trace.strands left).component =
        (diagram.trace.strands right).component) :
    exteriorStrandLabel 𝒞 diagram labeling left =
      exteriorStrandLabel 𝒞 diagram labeling right := by
  unfold exteriorStrandLabel
  rw [component_eq]

theorem orientedExteriorStrand_eq_of_component_and_orientation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    {input output : diagram.trace.StrandId}
    (component_eq :
      (diagram.trace.strands input).component =
        (diagram.trace.strands output).component)
    (orientation_eq :
      (diagram.trace.strands input).orientation =
        (diagram.trace.strands output).orientation) :
    orientedExteriorStrand 𝒞 diagram labeling input =
      orientedExteriorStrand 𝒞 diagram labeling output := by
  exact congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
    (exteriorStrandLabel_eq_of_component_eq
      𝒞 diagram labeling component_eq)
    (congrArg ribbonDirectionOfStrandOrientation orientation_eq)

theorem exteriorWord_of_continuations_eq
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (continuations :
      List (diagram.trace.StrandId × diagram.trace.StrandId))
    (compatible :
      ∀ pair ∈ continuations,
        (diagram.trace.strands pair.1).component =
            (diagram.trace.strands pair.2).component ∧
          (diagram.trace.strands pair.1).orientation =
            (diagram.trace.strands pair.2).orientation) :
    exteriorWord 𝒞 diagram labeling (continuations.map Prod.fst) =
      exteriorWord 𝒞 diagram labeling (continuations.map Prod.snd) := by
  induction continuations with
  | nil => rfl
  | cons pair rest ih =>
      have head_compatible := compatible pair (by simp)
      have tail_compatible :
          ∀ p ∈ rest,
            (diagram.trace.strands p.1).component =
                (diagram.trace.strands p.2).component ∧
              (diagram.trace.strands p.1).orientation =
                (diagram.trace.strands p.2).orientation := by
        intro p hp
        exact compatible p (by simp [hp])
      exact congrArg₂ List.cons
        (orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling head_compatible.1 head_compatible.2)
        (ih tail_compatible)

theorem exteriorWord_of_punctures_eq
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    exteriorWord 𝒞 diagram labeling
        (punctures.map DottedPuncture.inputStrand) =
      exteriorWord 𝒞 diagram labeling
        (punctures.map DottedPuncture.outputStrand) := by
  induction punctures with
  | nil => rfl
  | cons puncture rest ih =>
      exact congrArg₂ List.cons
        (orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling
          (puncture.input_on_two_handle.trans
            puncture.output_on_two_handle.symm)
          puncture.orientation_preserved)
        ih

/-!
## Canonical dual pairs and diagram bindings

Rigidity creates a canonical dual pair before any diagram is consulted.
Separate word-identification theorems then attach that canonical pair to the
two concrete strands recorded by the combinatorial trace.
-/

def positiveNegativeDualPairWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (label : 𝒞.simples.Simple) : RibbonWord 𝒞 :=
  [{ label := label, direction := .forward },
    { label := label, direction := .dual }]

def negativePositiveDualPairWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (label : 𝒞.simples.Simple) : RibbonWord 𝒞 :=
  [{ label := label, direction := .dual },
    { label := label, direction := .forward }]

def canonicalPositiveNegativeBirth
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (label : 𝒞.simples.Simple) :
    ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) ⟶
      ribbonWordObject 𝒞 (positiveNegativeDualPairWord 𝒞 label) := by
  simp only [positiveNegativeDualPairWord, ribbonWordObject,
    orientedSimpleObject]
  exact
    (η_ (𝒞.simples.simpleObject label)
      ((𝒞.simples.simpleObject label)ᘁ)) ≫
      (𝟙 _ ⊗ₘ (ρ_ _).inv)

def canonicalNegativePositiveBirth
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (label : 𝒞.simples.Simple) :
    ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) ⟶
      ribbonWordObject 𝒞 (negativePositiveDualPairWord 𝒞 label) := by
  simp only [negativePositiveDualPairWord, ribbonWordObject,
    orientedSimpleObject]
  exact
    (η_ (𝒞.simples.simpleObject label)
      ((𝒞.simples.simpleObject label)ᘁ)) ≫
      (β_ _ _).hom ≫
      (𝟙 _ ⊗ₘ (ρ_ _).inv)

def canonicalPositiveNegativeDeath
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (label : 𝒞.simples.Simple) :
    ribbonWordObject 𝒞 (positiveNegativeDualPairWord 𝒞 label) ⟶
      ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) := by
  simp only [positiveNegativeDualPairWord, ribbonWordObject,
    orientedSimpleObject]
  exact
    (𝟙 _ ⊗ₘ (ρ_ _).hom) ≫
      (𝒞.twist.hom.app (𝒞.simples.simpleObject label) ⊗ₘ 𝟙 _) ≫
      (β_ _ _).hom ≫
      (ε_ (𝒞.simples.simpleObject label)
        ((𝒞.simples.simpleObject label)ᘁ))

def canonicalNegativePositiveDeath
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (label : 𝒞.simples.Simple) :
    ribbonWordObject 𝒞 (negativePositiveDualPairWord 𝒞 label) ⟶
      ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) := by
  simp only [negativePositiveDualPairWord, ribbonWordObject,
    orientedSimpleObject]
  exact
    (𝟙 _ ⊗ₘ (ρ_ _).hom) ≫
      (𝟙 _ ⊗ₘ 𝒞.twist.hom.app (𝒞.simples.simpleObject label)) ≫
      (ε_ (𝒞.simples.simpleObject label)
        ((𝒞.simples.simpleObject label)ᘁ))

theorem right_negative_of_left_positive_of_ne
    (left right : StrandOrientation)
    (opposite : left ≠ right)
    (left_eq : left = .positive) :
    right = .negative := by
  cases left <;> cases right <;> simp_all

theorem left_negative_of_not_positive
    (orientation : StrandOrientation)
    (not_positive : orientation ≠ .positive) :
    orientation = .negative := by
  cases orientation <;> simp_all

theorem right_positive_of_left_negative_of_ne
    (left right : StrandOrientation)
    (opposite : left ≠ right)
    (left_eq : left = .negative) :
    right = .positive := by
  cases left <;> cases right <;> simp_all

def positiveNegativeDualPairWord_eq_exteriorWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (left right : diagram.trace.StrandId)
    (component_eq :
      (diagram.trace.strands left).component =
        (diagram.trace.strands right).component)
    (left_positive :
      (diagram.trace.strands left).orientation = .positive)
    (right_negative :
      (diagram.trace.strands right).orientation = .negative) :
    positiveNegativeDualPairWord 𝒞
        (exteriorStrandLabel 𝒞 diagram labeling right) =
      exteriorWord 𝒞 diagram labeling [left, right] := by
  have label_eq :=
    exteriorStrandLabel_eq_of_component_eq 𝒞 diagram labeling component_eq
  simp [positiveNegativeDualPairWord, exteriorWord, orientedExteriorStrand,
    ribbonDirectionOfStrandOrientation, left_positive, right_negative, label_eq]

def negativePositiveDualPairWord_eq_exteriorWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (left right : diagram.trace.StrandId)
    (component_eq :
      (diagram.trace.strands left).component =
        (diagram.trace.strands right).component)
    (left_negative :
      (diagram.trace.strands left).orientation = .negative)
    (right_positive :
      (diagram.trace.strands right).orientation = .positive) :
    negativePositiveDualPairWord 𝒞
        (exteriorStrandLabel 𝒞 diagram labeling right) =
      exteriorWord 𝒞 diagram labeling [left, right] := by
  have label_eq :=
    exteriorStrandLabel_eq_of_component_eq 𝒞 diagram labeling component_eq
  simp [negativePositiveDualPairWord, exteriorWord, orientedExteriorStrand,
    ribbonDirectionOfStrandOrientation, left_negative, right_positive, label_eq]

def pairedBirthMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (left right : diagram.trace.StrandId)
    (component_eq :
      (diagram.trace.strands left).component =
        (diagram.trace.strands right).component)
    (orientation_ne :
      (diagram.trace.strands left).orientation ≠
        (diagram.trace.strands right).orientation) :
    ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling [left, right]) := by
  by_cases left_positive :
      (diagram.trace.strands left).orientation = .positive
  · have right_negative :=
      right_negative_of_left_positive_of_ne _ _ orientation_ne left_positive
    exact
      canonicalPositiveNegativeBirth 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling right) ≫
        eqToHom (congrArg (ribbonWordObject 𝒞)
          (positiveNegativeDualPairWord_eq_exteriorWord
            𝒞 diagram labeling left right component_eq
            left_positive right_negative))
  · have left_negative :=
      left_negative_of_not_positive _ left_positive
    have right_positive :=
      right_positive_of_left_negative_of_ne _ _ orientation_ne left_negative
    exact
      canonicalNegativePositiveBirth 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling right) ≫
        eqToHom (congrArg (ribbonWordObject 𝒞)
          (negativePositiveDualPairWord_eq_exteriorWord
            𝒞 diagram labeling left right component_eq
            left_negative right_positive))

def pairedDeathMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (left right : diagram.trace.StrandId)
    (component_eq :
      (diagram.trace.strands left).component =
        (diagram.trace.strands right).component)
    (orientation_ne :
      (diagram.trace.strands left).orientation ≠
        (diagram.trace.strands right).orientation) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling [left, right]) ⟶
      ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) := by
  by_cases left_positive :
      (diagram.trace.strands left).orientation = .positive
  · have right_negative :=
      right_negative_of_left_positive_of_ne _ _ orientation_ne left_positive
    exact
      eqToHom (congrArg (ribbonWordObject 𝒞)
          (positiveNegativeDualPairWord_eq_exteriorWord
            𝒞 diagram labeling left right component_eq
            left_positive right_negative)).symm ≫
        canonicalPositiveNegativeDeath 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling right)
  · have left_negative :=
      left_negative_of_not_positive _ left_positive
    have right_positive :=
      right_positive_of_left_negative_of_ne _ _ orientation_ne left_negative
    exact
      eqToHom (congrArg (ribbonWordObject 𝒞)
          (negativePositiveDualPairWord_eq_exteriorWord
            𝒞 diagram labeling left right component_eq
            left_negative right_positive)).symm ≫
        canonicalNegativePositiveDeath 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling right)

/-- Compile one exact cut-open event before adding its common exterior. -/
def compileCutOpenEventMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (pairing : event.StrandContinuationsAreWellFormed) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling event.beforeWord) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling event.afterWord) := by
  cases event with
  | birth left right =>
      exact pairedBirthMorphism 𝒞 diagram labeling left right pairing.1 pairing.2
  | death left right =>
      exact pairedDeathMorphism 𝒞 diagram labeling left right pairing.1 pairing.2
  | crossing overInput underInput overOutput underOutput sign =>
      have over_eq :=
        orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling pairing.1 pairing.2.1
      have under_eq :=
        orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling pairing.2.2.1 pairing.2.2.2
      simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
        exteriorWord, List.map_cons, List.map_nil, ribbonWordObject]
      rw [← over_eq, ← under_eq]
      cases sign with
      | positive =>
          exact
            (α_ _ _ _).inv ≫
              ((β_ _ _).hom ⊗ₘ 𝟙 _) ≫
              (α_ _ _ _).hom
      | negative =>
          exact
            (α_ _ _ _).inv ≫
              ((β_ _ _).inv ⊗ₘ 𝟙 _) ≫
              (α_ _ _ _).hom
  | framingTwist input output sign =>
      have output_eq :=
        orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling pairing.1 pairing.2
      simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
        exteriorWord, List.map_cons, List.map_nil, ribbonWordObject]
      rw [← output_eq]
      cases sign with
      | positive => exact 𝒞.twist.hom.app _ ⊗ₘ 𝟙 _
      | negative => exact 𝒞.twist.inv.app _ ⊗ₘ 𝟙 _
  | planarIsotopy continuations =>
      have word_eq :=
        exteriorWord_of_continuations_eq
          𝒞 diagram labeling continuations pairing
      simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord]
      rw [← word_eq]
      exact 𝟙 _
  | projectorHole _ punctures =>
      have input_eq :=
        exteriorInputWord_eq_cutBoundaryWord 𝒞 diagram labeling punctures
      have output_eq :=
        exteriorOutputWord_eq_cutBoundaryWord 𝒞 diagram labeling punctures
      simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord]
      exact
        eqToHom (congrArg (ribbonWordObject 𝒞) input_eq) ≫
          tensorUnitProjector 𝒞
            (ribbonWordObject 𝒞
              (cutBoundaryWord 𝒞 diagram labeling punctures)) ≫
          eqToHom (congrArg (ribbonWordObject 𝒞) output_eq.symm)

/-- The chosen left exterior context of one certified event transition. -/
noncomputable def eventLeftContext
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    List diagram.trace.StrandId :=
  Classical.choose
    (presentation.cut.exterior.transitionValid i)

/-- The chosen right exterior context of one certified event transition. -/
noncomputable def eventRightContext
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    List diagram.trace.StrandId :=
  Classical.choose
    (Classical.choose_spec
      (presentation.cut.exterior.transitionValid i))

theorem eventTransitionEquations
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    presentation.cut.exterior.activeOrder i.castSucc =
        eventLeftContext diagram presentation i ++
          (presentation.cut.exterior.events i).beforeWord ++
          eventRightContext diagram presentation i ∧
      presentation.cut.exterior.activeOrder i.succ =
        eventLeftContext diagram presentation i ++
          (presentation.cut.exterior.events i).afterWord ++
          eventRightContext diagram presentation i :=
  Classical.choose_spec
    (Classical.choose_spec
      (presentation.cut.exterior.transitionValid i))

def contextualizeRibbonMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left before after right : RibbonWord 𝒞)
    (map :
      ribbonWordObject 𝒞 before ⟶
        ribbonWordObject 𝒞 after) :
    ribbonWordObject 𝒞
        (List.append (List.append left before) right) ⟶
      ribbonWordObject 𝒞
        (List.append (List.append left after) right) :=
  (ribbonWordAppendIso 𝒞 (List.append left before) right).hom ≫
    ((ribbonWordAppendIso 𝒞 left before).hom ⊗ₘ 𝟙 _) ≫
    (α_ _ _ _).hom ≫
    (𝟙 _ ⊗ₘ (map ⊗ₘ 𝟙 _)) ≫
    (α_ _ _ _).inv ≫
    ((ribbonWordAppendIso 𝒞 left after).inv ⊗ₘ 𝟙 _) ≫
    (ribbonWordAppendIso 𝒞 (List.append left after) right).inv

/-- Compile one event together with the exact common exterior context. -/
noncomputable def compileContextualCutOpenEventMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder i.castSucc)) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder i.succ)) := by
  let event := presentation.cut.exterior.events i
  let left := eventLeftContext diagram presentation i
  let right := eventRightContext diagram presentation i
  have before_eq := (eventTransitionEquations diagram presentation i).1
  have after_eq := (eventTransitionEquations diagram presentation i).2
  have before_object_eq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      before_eq
  have after_object_eq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      after_eq
  have before_context_object_eq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (left ++ event.beforeWord ++ right)) =
        ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.beforeWord))
            (exteriorWord 𝒞 diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  have after_context_object_eq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (left ++ event.afterWord ++ right)) =
        ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.afterWord))
            (exteriorWord 𝒞 diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  exact
    eqToHom before_object_eq ≫
      eqToHom before_context_object_eq ≫
      contextualizeRibbonMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling left)
        (exteriorWord 𝒞 diagram labeling event.beforeWord)
        (exteriorWord 𝒞 diagram labeling event.afterWord)
        (exteriorWord 𝒞 diagram labeling right)
        (compileCutOpenEventMorphism 𝒞 diagram labeling event
          (presentation.cut.exterior.strandContinuationsAreWellFormed i)) ≫
      eqToHom after_context_object_eq.symm ≫
      eqToHom after_object_eq.symm

structure FiniteMorphismTrace
    (C : Type uC) [Category.{v} C] (eventCount : ℕ) where
  object : Fin (eventCount + 1) → C
  edge :
    (i : Fin eventCount) →
      object i.castSucc ⟶ object i.succ

def FiniteMorphismTrace.composePrefix
    {C : Type uC} [Category.{v} C]
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C eventCount) :
    (k : ℕ) →
      (bound : k ≤ eventCount) →
      trace.object 0 ⟶ trace.object ⟨k, Nat.lt_succ_iff.mpr bound⟩
  | 0, _ => 𝟙 _
  | k + 1, bound =>
      trace.composePrefix k (Nat.le_trans (Nat.le_succ k) bound) ≫
        trace.edge ⟨k, Nat.lt_of_succ_le bound⟩

def FiniteMorphismTrace.composeAll
    {C : Type uC} [Category.{v} C]
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C eventCount) :
    trace.object 0 ⟶ trace.object (Fin.last eventCount) :=
  trace.composePrefix eventCount (Nat.le_refl eventCount)

/--
Compile one finite category-neutral dotted-collar bending path.  The path
contains no projector event; this definition only interprets its explicit
cup/cap/braiding/isotopy events and composes them in order.
-/
noncomputable def compileDottedCollarBendingPathMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    {source target : List diagram.trace.StrandId}
    (path : DottedCollarBendingPath diagram.trace source target)
    (follows : path.FollowsExactBendingTransitions) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling source) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling target) := by
  let trace : FiniteMorphismTrace 𝒞.C path.eventCount :=
    {
      object := fun i =>
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling (path.activeOrder i))
      edge := fun i => by
        let event := path.events i
        have transition := follows.2.2.1 i
        let left : List diagram.trace.StrandId := Classical.choose transition
        let right : List diagram.trace.StrandId :=
          Classical.choose (Classical.choose_spec transition)
        have equations :=
          Classical.choose_spec
            (Classical.choose_spec transition)
        have before_eq := equations.1
        have after_eq := equations.2
        have before_object_eq :=
          congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            before_eq
        have after_object_eq :=
          congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            after_eq
        have before_context_object_eq :
            ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling
                  (left ++ event.beforeWord ++ right)) =
              ribbonWordObject 𝒞
                (List.append
                  (List.append
                    (exteriorWord 𝒞 diagram labeling left)
                    (exteriorWord 𝒞 diagram labeling event.beforeWord))
                  (exteriorWord 𝒞 diagram labeling right)) := by
          simp [exteriorWord, List.map_append]
        have after_context_object_eq :
            ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling
                  (left ++ event.afterWord ++ right)) =
              ribbonWordObject 𝒞
                (List.append
                  (List.append
                    (exteriorWord 𝒞 diagram labeling left)
                    (exteriorWord 𝒞 diagram labeling event.afterWord))
                  (exteriorWord 𝒞 diagram labeling right)) := by
          simp [exteriorWord, List.map_append]
        exact
          eqToHom before_object_eq ≫
            eqToHom before_context_object_eq ≫
            contextualizeRibbonMorphism 𝒞
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.beforeWord)
              (exteriorWord 𝒞 diagram labeling event.afterWord)
              (exteriorWord 𝒞 diagram labeling right)
              (compileCutOpenEventMorphism 𝒞 diagram labeling event
                (follows.2.2.2.1 i)) ≫
            eqToHom after_context_object_eq.symm ≫
            eqToHom after_object_eq.symm
    }
  have initial_object_eq :
      trace.object 0 =
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling source) :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      follows.1
  have final_object_eq :
      trace.object (Fin.last path.eventCount) =
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling target) :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      follows.2.1
  exact
    eqToHom initial_object_eq.symm ≫
      trace.composeAll ≫
      eqToHom final_object_eq

/--
An event uses the exact puncture word recorded for its literal dotted
component.  Non-projector events satisfy this predicate trivially.

This predicate is category-neutral.  In particular, it does not relate dotted
direction to object duality or to a character exponent.
-/
def CutOpenEvent.UsesExactDottedPunctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : CutOpenEvent trace → Prop
  | .projectorHole dotted punctures =>
      ∃ role : (trace.components dotted).role = .dotted,
        punctures = cut.punctureWord dotted role
  | _ => True

theorem DottedCutData.exteriorEvent_usesExactDottedPunctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (complete : cut.ProjectorEventsExactlyMatchDottedComponents)
    (i : Fin cut.exterior.eventCount) :
    (cut.exterior.events i).UsesExactDottedPunctureWord cut := by
  generalize eventEq : cut.exterior.events i = event
  cases event with
  | projectorHole dotted punctures =>
      obtain ⟨role, puncturesEq⟩ :=
        cut.projectorEvent_hasExactPunctureWord
          complete i dotted punctures eventEq
      exact ⟨role, puncturesEq⟩
  | birth => trivial
  | death => trivial
  | crossing => trivial
  | framingTwist => trivial
  | planarIsotopy => trivial

/--
Compile an explicit event from its exact role certificate.  Component labels
and forward/dual choices still come solely from `exteriorWord`; the role
certificate only ensures that a projector marker uses the puncture word of the
literal dotted component that created it.
-/
noncomputable def compileRoleAwareCutOpenEventMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (pairing : event.StrandContinuationsAreWellFormed)
    (exact : event.UsesExactDottedPunctureWord presentation.cut) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling event.beforeWord) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling event.afterWord) := by
  cases event with
  | projectorHole dotted punctures =>
      let role := Classical.choose exact
      have punctures_eq := Classical.choose_spec exact
      rw [punctures_eq]
      exact compileCutOpenEventMorphism 𝒞 diagram labeling
        (.projectorHole dotted
          (presentation.cut.punctureWord dotted role)) (by
            simpa only [punctures_eq] using pairing)
  | birth left right =>
      exact compileCutOpenEventMorphism 𝒞 diagram labeling
        (.birth left right) pairing
  | death left right =>
      exact compileCutOpenEventMorphism 𝒞 diagram labeling
        (.death left right) pairing
  | crossing overInput underInput overOutput underOutput sign =>
      exact compileCutOpenEventMorphism 𝒞 diagram labeling
        (.crossing overInput underInput overOutput underOutput sign) pairing
  | framingTwist input output sign =>
      exact compileCutOpenEventMorphism 𝒞 diagram labeling
        (.framingTwist input output sign) pairing
  | planarIsotopy continuations =>
      exact compileCutOpenEventMorphism 𝒞 diagram labeling
        (.planarIsotopy continuations) pairing

theorem compileRoleAwareCutOpenEventMorphism_eq_elementary
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (pairing : event.StrandContinuationsAreWellFormed)
    (exact : event.UsesExactDottedPunctureWord presentation.cut) :
    compileRoleAwareCutOpenEventMorphism
        𝒞 diagram presentation labeling event pairing exact =
      compileCutOpenEventMorphism 𝒞 diagram labeling event pairing := by
  cases event with
  | projectorHole =>
      rcases exact with ⟨role, puncturesEq⟩
      cases puncturesEq
      rfl
  | birth => rfl
  | death => rfl
  | crossing => rfl
  | framingTwist => rfl
  | planarIsotopy => rfl

/-- Compile one event at its certified position in the global cut-open trace. -/
noncomputable def compileRoleAwareCutOpenEventAt
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.events i).beforeWord) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.events i).afterWord) :=
  compileRoleAwareCutOpenEventMorphism 𝒞 diagram presentation labeling
    (presentation.cut.exterior.events i)
    (presentation.cut.exterior.strandContinuationsAreWellFormed i)
    (presentation.cut.exteriorEvent_usesExactDottedPunctureWord
      (standardDottedProjectorEventCompleteness diagram presentation) i)

theorem compileRoleAwareCutOpenEventAt_eq_elementary
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    compileRoleAwareCutOpenEventAt 𝒞 diagram presentation labeling i =
      compileCutOpenEventMorphism 𝒞 diagram labeling
        (presentation.cut.exterior.events i)
        (presentation.cut.exterior.strandContinuationsAreWellFormed i) := by
  unfold compileRoleAwareCutOpenEventAt
  exact compileRoleAwareCutOpenEventMorphism_eq_elementary
    𝒞 diagram presentation labeling
    (presentation.cut.exterior.events i)
    (presentation.cut.exterior.strandContinuationsAreWellFormed i)
    (presentation.cut.exteriorEvent_usesExactDottedPunctureWord
      (standardDottedProjectorEventCompleteness diagram presentation) i)

/-- Add the exact common exterior context to one role-aware event. -/
noncomputable def compileRoleAwareContextualCutOpenEventMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder i.castSucc)) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder i.succ)) := by
  let event := presentation.cut.exterior.events i
  let left := eventLeftContext diagram presentation i
  let right := eventRightContext diagram presentation i
  have before_eq := (eventTransitionEquations diagram presentation i).1
  have after_eq := (eventTransitionEquations diagram presentation i).2
  have before_object_eq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      before_eq
  have after_object_eq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      after_eq
  have before_context_object_eq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (left ++ event.beforeWord ++ right)) =
        ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.beforeWord))
            (exteriorWord 𝒞 diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  have after_context_object_eq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (left ++ event.afterWord ++ right)) =
        ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.afterWord))
            (exteriorWord 𝒞 diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  exact
    eqToHom before_object_eq ≫
      eqToHom before_context_object_eq ≫
      contextualizeRibbonMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling left)
        (exteriorWord 𝒞 diagram labeling event.beforeWord)
        (exteriorWord 𝒞 diagram labeling event.afterWord)
        (exteriorWord 𝒞 diagram labeling right)
        (compileRoleAwareCutOpenEventAt 𝒞 diagram presentation labeling i) ≫
      eqToHom after_context_object_eq.symm ≫
      eqToHom after_object_eq.symm

/-- Compile the complete finite cut-open exterior trace in sweep order. -/
noncomputable def compileCutOpenExteriorMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C := by
  let trace : FiniteMorphismTrace 𝒞.C
      presentation.cut.exterior.eventCount :=
    {
      object := fun i =>
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.activeOrder i))
      edge := fun i =>
        compileRoleAwareContextualCutOpenEventMorphism
          𝒞 diagram presentation labeling i
    }
  have initial_object_eq :
      trace.object 0 = 𝟙_ 𝒞.C :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      presentation.cut.exterior.initialBoundaryEmpty
  have final_object_eq :
      trace.object (Fin.last presentation.cut.exterior.eventCount) =
        𝟙_ 𝒞.C :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      presentation.cut.exterior.finalBoundaryEmpty
  exact
    eqToHom initial_object_eq.symm ≫
      trace.composeAll ≫
      eqToHom final_object_eq

/--
Fusion-channel resolutions belong to local graphical proofs, not to the
definition of the original closed link.  The canonical compiler therefore
returns the unique closed ribbon expression obtained by composing the
diagram's complete ordered cut-open event trace.  There is no wrapper field
through which a caller could replace this expression by an unrelated graph.
-/
noncomputable def canonicalRoleAwareGraphCompiler
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (_coefficients : ThamTwoHandleCoefficients diagram) :
    ClosedRibbonExpression 𝒞η.category :=
  .morphism
    (compileCutOpenExteriorMorphism
      𝒞η.category diagram presentation labeling)

/--
Tham Definition 5.11 normalization on the turned-over handle decomposition.

The arguments use THAM indices.  Thus `hOne` is the number of primal
three-handles, and the unique primal four-handle contributes the numerator
`globalDimension`.  The value is exactly

`globalDimension / globalDimension ^ hOne`.

There is no caller-supplied normalization datum or opaque conformance
predicate.
-/
def thamDefinition511Normalization
    {K : Type uK} [Field K]
    (globalDimension : K)
    (hOne _hTwo _hThree : ℕ) : K :=
  globalDimension / globalDimension ^ hOne

noncomputable def rawCoefficientSum
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (coefficients : ThamTwoHandleCoefficients diagram) : K :=
  ∑ labeling : TwoHandleLabeling 𝒞η.category diagram,
    ordinaryKirbyWeight 𝒞η.category labeling *
    characterWeight 𝒞η labeling coefficients *
    let term :=
      canonicalRoleAwareGraphCompiler
        𝒞η diagram presentation labeling coefficients
    canonicalRibbonGraphicalEvaluation 𝒞η.category term

noncomputable def evaluateCoefficients
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (coefficients : ThamTwoHandleCoefficients diagram) : K :=
  thamDefinition511Normalization
      𝒞η.category.globalDimension
      diagram.handles.hThree
      diagram.handles.hTwo
      diagram.handles.hOne *
    rawCoefficientSum 𝒞η diagram presentation coefficients

/--
Representative independence is not baked into the definition.  It is the
precise obligation required before `evaluateCoefficients` descends to the
visible ambient `ThamMarkingClass`.
-/
def RepresentativeIndependenceStatement
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram) : Prop :=
  ∀ left right : ThamTwoHandleCoefficients diagram,
    thamMarkingClass left = thamMarkingClass right →
    evaluateCoefficients 𝒞η diagram presentation left =
      evaluateCoefficients 𝒞η diagram presentation right

end

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 3422
