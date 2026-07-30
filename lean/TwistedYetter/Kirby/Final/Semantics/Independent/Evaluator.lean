import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

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
exponents therefore come only from `ThamTwoCycles`, never directly from a
primal representative.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC uS v

abbrev TwoHandleLabeling
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram) :=
  Fin diagram.handles.hTwo → 𝒞.simples.Simple

instance
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram) :
    Fintype (TwoHandleLabeling 𝒞 diagram) :=
  inferInstance

def ordinaryKirbyWeight
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {diagram : CombinatorialSpecialKirbyDiagram}
    (labeling : TwoHandleLabeling 𝒞 diagram) : K :=
  ∏ handle, 𝒞.simples.quantumDimension (labeling handle)

noncomputable def characterWeight
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles turnedOver) : K :=
  ((∏ handle,
      (𝒞η.character.value (labeling handle)) ^ (cycle.1 handle)) : Kˣ)

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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strand : diagram.trace.StrandId) :
    OrientedSimple 𝒞 where
  label := exteriorStrandLabel 𝒞 diagram labeling strand
  direction :=
    ribbonDirectionOfStrandOrientation
      (diagram.trace.strands strand).orientation

def exteriorWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (strands : List diagram.trace.StrandId) :
    RibbonWord 𝒞 :=
  strands.map (orientedExteriorStrand 𝒞 diagram labeling)

def ribbonWordAppendIso
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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

def pairedBirthMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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
  have label_eq :=
    exteriorStrandLabel_eq_of_component_eq 𝒞 diagram labeling component_eq
  unfold exteriorWord
  simp only [List.map_cons, List.map_nil, ribbonWordObject]
  cases left_orientation : (diagram.trace.strands left).orientation <;>
    cases right_orientation : (diagram.trace.strands right).orientation
  · exact False.elim (orientation_ne (left_orientation.trans right_orientation.symm))
  ·
    simp only [orientedSimpleObject, orientedExteriorStrand,
      ribbonDirectionOfStrandOrientation, left_orientation, right_orientation]
    have object_eq := congrArg 𝒞.simples.simpleObject label_eq
    have dual_eq := congrArg (fun X : 𝒞.C => Xᘁ) object_eq
    exact
      (η_
        (𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 diagram labeling left))
        ((𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 diagram labeling left))ᘁ)) ≫
        (𝟙 _ ⊗ₘ eqToHom dual_eq) ≫
        (𝟙 _ ⊗ₘ (ρ_ _).inv)
  ·
    simp only [orientedSimpleObject, orientedExteriorStrand,
      ribbonDirectionOfStrandOrientation, left_orientation, right_orientation]
    have object_eq := congrArg 𝒞.simples.simpleObject label_eq
    have dual_eq := congrArg (fun X : 𝒞.C => Xᘁ) object_eq
    exact
      (η_
        (𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 diagram labeling right))
        ((𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 diagram labeling right))ᘁ)) ≫
        (β_ _ _).hom ≫
        (eqToHom dual_eq.symm ⊗ₘ 𝟙 _) ≫
        (𝟙 _ ⊗ₘ (ρ_ _).inv)
  · exact False.elim (orientation_ne (left_orientation.trans right_orientation.symm))

def pairedDeathMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
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
  have label_eq :=
    exteriorStrandLabel_eq_of_component_eq 𝒞 diagram labeling component_eq
  unfold exteriorWord
  simp only [List.map_cons, List.map_nil, ribbonWordObject]
  cases left_orientation : (diagram.trace.strands left).orientation <;>
    cases right_orientation : (diagram.trace.strands right).orientation
  · exact False.elim (orientation_ne (left_orientation.trans right_orientation.symm))
  ·
    simp only [orientedSimpleObject, orientedExteriorStrand,
      ribbonDirectionOfStrandOrientation, left_orientation, right_orientation]
    have object_eq := congrArg 𝒞.simples.simpleObject label_eq
    have dual_eq := congrArg (fun X : 𝒞.C => Xᘁ) object_eq
    exact
      (𝟙 _ ⊗ₘ (ρ_ _).hom) ≫
        (𝟙 _ ⊗ₘ eqToHom dual_eq.symm) ≫
        (β_ _ _).hom ≫
        (ε_
          (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 diagram labeling left))
          ((𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 diagram labeling left))ᘁ))
  ·
    simp only [orientedSimpleObject, orientedExteriorStrand,
      ribbonDirectionOfStrandOrientation, left_orientation, right_orientation]
    have object_eq := congrArg 𝒞.simples.simpleObject label_eq
    have dual_eq := congrArg (fun X : 𝒞.C => Xᘁ) object_eq
    exact
      (𝟙 _ ⊗ₘ (ρ_ _).hom) ≫
        (eqToHom dual_eq ⊗ₘ 𝟙 _) ≫
        (ε_
          (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 diagram labeling right))
          ((𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 diagram labeling right))ᘁ))
  · exact False.elim (orientation_ne (left_orientation.trans right_orientation.symm))

/-- Compile one exact cut-open event before adding its common exterior. -/
def compileCutOpenEventMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (pairing : event.PairingCompatible) :
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
      | positive => exact 𝒞.ribbon.twist.hom.app _ ⊗ₘ 𝟙 _
      | negative => exact 𝒞.ribbon.twist.inv.app _ ⊗ₘ 𝟙 _
  | planarIsotopy continuations =>
      have word_eq :=
        exteriorWord_of_continuations_eq
          𝒞 diagram labeling continuations pairing
      simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord]
      rw [← word_eq]
      exact 𝟙 _
  | projectorHole _ punctures =>
      have word_eq :=
        exteriorWord_of_punctures_eq 𝒞 diagram labeling punctures
      simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord]
      rw [← word_eq]
      exact
        tensorUnitProjector 𝒞
          (ribbonWordObject 𝒞
            (exteriorWord 𝒞 diagram labeling
              (punctures.map DottedPuncture.inputStrand)))

/-- The chosen left exterior context of one certified event transition. -/
noncomputable def eventLeftContext
    (diagram : CombinatorialSpecialKirbyDiagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    List diagram.trace.StrandId :=
  Classical.choose
    (diagram.dottedCuts.exterior.transitionValid i)

/-- The chosen right exterior context of one certified event transition. -/
noncomputable def eventRightContext
    (diagram : CombinatorialSpecialKirbyDiagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    List diagram.trace.StrandId :=
  Classical.choose
    (Classical.choose_spec
      (diagram.dottedCuts.exterior.transitionValid i))

theorem eventTransitionEquations
    (diagram : CombinatorialSpecialKirbyDiagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    diagram.dottedCuts.exterior.activeOrder i.castSucc =
        eventLeftContext diagram i ++
          (diagram.dottedCuts.exterior.events i).beforeWord ++
          eventRightContext diagram i ∧
      diagram.dottedCuts.exterior.activeOrder i.succ =
        eventLeftContext diagram i ++
          (diagram.dottedCuts.exterior.events i).afterWord ++
          eventRightContext diagram i :=
  Classical.choose_spec
    (Classical.choose_spec
      (diagram.dottedCuts.exterior.transitionValid i))

def contextualizeRibbonMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
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
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (diagram.dottedCuts.exterior.activeOrder i.castSucc)) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (diagram.dottedCuts.exterior.activeOrder i.succ)) := by
  let event := diagram.dottedCuts.exterior.events i
  let left := eventLeftContext diagram i
  let right := eventRightContext diagram i
  have before_eq := (eventTransitionEquations diagram i).1
  have after_eq := (eventTransitionEquations diagram i).2
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
          (diagram.dottedCuts.exterior.pairingCompatible i)) ≫
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

/-- Compile the complete finite cut-open exterior trace in sweep order. -/
noncomputable def compileCutOpenExteriorMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C := by
  let trace : FiniteMorphismTrace 𝒞.C
      diagram.dottedCuts.exterior.eventCount :=
    {
      object := fun i =>
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (diagram.dottedCuts.exterior.activeOrder i))
      edge := fun i =>
        compileContextualCutOpenEventMorphism 𝒞 diagram labeling i
    }
  have initial_object_eq :
      trace.object 0 = 𝟙_ 𝒞.C :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      diagram.dottedCuts.exterior.initialBoundaryEmpty
  have final_object_eq :
      trace.object (Fin.last diagram.dottedCuts.exterior.eventCount) =
        𝟙_ 𝒞.C :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞 (exteriorWord 𝒞 diagram labeling word))
      diagram.dottedCuts.exterior.finalBoundaryEmpty
  exact
    eqToHom initial_object_eq.symm ≫
      trace.composeAll ≫
      eqToHom final_object_eq

/--
Fusion-channel resolutions belong to local graphical proofs, not to the
definition of the original closed link.  Therefore the canonical compiled
term is exactly one closed graph, with no auxiliary channel denominator.
-/
structure RoleAwareCompiledTerm
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (_primal : PrimalDegreeThreeBoundaryData diagram)
    (_turnedOver : TurnedOverBoundaryCertificate _primal)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (_cycle : ThamTwoCycles _turnedOver) where
  graph : ClosedRibbonExpression 𝒞η.category :=
    .morphism
      (compileCutOpenExteriorMorphism 𝒞η.category diagram labeling)

noncomputable def canonicalRoleAwareGraphCompiler
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles turnedOver) :
    RoleAwareCompiledTerm 𝒞η diagram primal turnedOver labeling cycle :=
  {}

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

noncomputable def evaluateCycle
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (cycle : ThamTwoCycles turnedOver) : K :=
  thamDefinition511Normalization
      𝒞η.category.globalDimension
      diagram.handles.hThree
      diagram.handles.hTwo
      diagram.handles.hOne *
    ∑ labeling : TwoHandleLabeling 𝒞η.category diagram,
      ordinaryKirbyWeight 𝒞η.category labeling *
      characterWeight 𝒞η turnedOver labeling cycle *
      let term :=
        canonicalRoleAwareGraphCompiler
          𝒞η diagram primal turnedOver labeling cycle
      canonicalRibbonGraphicalEvaluation 𝒞η.category term.graph

/--
Representative independence is not baked into the definition.  It is the
precise obligation required before `evaluateCycle` descends to `ThamKirbyH₂`.
-/
def RepresentativeIndependenceStatement
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (turnedOver : TurnedOverBoundaryCertificate primal) : Prop :=
  ∀ left right : ThamTwoCycles turnedOver,
    thamCycleClass turnedOver left = thamCycleClass turnedOver right →
    evaluateCycle 𝒞η
        diagram primal turnedOver left =
      evaluateCycle 𝒞η
        diagram primal turnedOver right

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 18113
