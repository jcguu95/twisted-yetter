import TwistedYetter.Kirby.Final.Proofs.CancellationNormalForms

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe v uC

namespace TwistedYetter.Semantics.Independent.FiniteMorphismTrace

variable {C : Type uC} [Category.{v} C]

def dropThree
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C (eventCount + 3)) :
    FiniteMorphismTrace C eventCount where
  object i :=
    trace.object
      ⟨i.1 + 3, by
        have := i.2
        omega⟩
  edge i :=
    trace.edge
      ⟨i.1 + 3, by
        have := i.2
        omega⟩

def dropLast
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C (eventCount + 1)) :
    FiniteMorphismTrace C eventCount where
  object i :=
    trace.object ⟨i.1, by
      have := i.2
      omega⟩
  edge i :=
    trace.edge ⟨i.1, by
      have := i.2
      omega⟩

theorem dropLast_composePrefix
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C (eventCount + 1))
    (k : ℕ) (bound : k ≤ eventCount) :
    trace.dropLast.composePrefix k bound =
      trace.composePrefix k (by omega) := by
  induction k with
  | zero => rfl
  | succ k inductionHypothesis =>
      simp only [FiniteMorphismTrace.composePrefix]
      rw [inductionHypothesis]
      rfl

theorem composePrefix_add_three
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C (eventCount + 3)) :
    trace.composePrefix (eventCount + 3) (Nat.le_refl _) =
      trace.composePrefix 3 (by omega) ≫
        (trace.dropThree.composeAll) := by
  induction eventCount with
  | zero =>
      simp [FiniteMorphismTrace.composeAll,
        FiniteMorphismTrace.composePrefix,
        FiniteMorphismTrace.dropThree]
  | succ eventCount inductionHypothesis =>
      let initialTrace := trace.dropLast
      have prefixEquality :
          initialTrace.composePrefix (eventCount + 3) (by omega) =
            trace.composePrefix (eventCount + 3) (by omega) := by
        exact dropLast_composePrefix trace _ _
      have suffixEquality :
          initialTrace.dropThree.composeAll =
            trace.dropThree.composePrefix eventCount (by omega) := by
        exact dropLast_composePrefix trace.dropThree _ _
      rw [FiniteMorphismTrace.composePrefix]
      rw [← prefixEquality]
      rw [inductionHypothesis initialTrace]
      rw [suffixEquality]
      simp only [FiniteMorphismTrace.composeAll,
        FiniteMorphismTrace.composePrefix,
        FiniteMorphismTrace.dropThree]
      have oneLt : 1 < eventCount + 3 := by omega
      have modOne : 1 % (eventCount + 3) = 1 :=
        Nat.mod_eq_of_lt oneLt
      have finOne :
          (⟨1 % (eventCount + 3), by omega⟩ :
              Fin (eventCount + 1 + 3)) =
            ⟨1, by omega⟩ :=
        Fin.ext modOne
      simp [initialTrace, FiniteMorphismTrace.dropLast,
        Category.assoc, finOne]
      congr 3 <;> simp [Fin.ext_iff, modOne]

theorem eq_of_object_edge
    {eventCount : ℕ}
    (left right : FiniteMorphismTrace C eventCount)
    (objectEq : ∀ i, left.object i = right.object i)
    (edgeEq : ∀ i, HEq (left.edge i) (right.edge i)) :
    left = right := by
  cases left with
  | mk leftObject leftEdge =>
      cases right with
      | mk rightObject rightEdge =>
          have objects : leftObject = rightObject :=
            funext objectEq
          subst rightObject
          have edges : leftEdge = rightEdge :=
            funext fun i => eq_of_heq (edgeEq i)
          subst rightEdge
          rfl

def castEventCount
    {leftCount rightCount : ℕ}
    (countEq : leftCount = rightCount)
    (trace : FiniteMorphismTrace C rightCount) :
    FiniteMorphismTrace C leftCount where
  object i :=
    trace.object
      (Fin.cast (congrArg (fun count => count + 1) countEq) i)
  edge i :=
    trace.edge (Fin.cast countEq i)

theorem castEventCount_composeAll
    {leftCount rightCount : ℕ}
    (countEq : leftCount = rightCount)
    (trace : FiniteMorphismTrace C rightCount) :
    HEq (castEventCount countEq trace).composeAll trace.composeAll := by
  subst rightCount
  rfl

theorem castEventCount_composePrefix
    {leftCount rightCount : ℕ}
    (countEq : leftCount = rightCount)
    (trace : FiniteMorphismTrace C rightCount)
    (k : ℕ)
    (leftBound : k ≤ leftCount)
    (rightBound : k ≤ rightCount) :
    HEq
      ((castEventCount countEq trace).composePrefix k leftBound)
      (trace.composePrefix k rightBound) := by
  subst rightCount
  have proofEq : leftBound = rightBound := Subsingleton.elim _ _
  cases proofEq
  rfl

end TwistedYetter.Semantics.Independent.FiniteMorphismTrace

namespace TwistedYetter.Kirby.Final.Proofs

theorem identity_heq_of_object_eq
    {C : Type uC} [Category.{v} C]
    {X Y : C} (objectEq : X = Y) :
    HEq (𝟙 X) (𝟙 Y) := by
  subst Y
  rfl

theorem middle_heq_of_transport_sandwich_eq
    {C : Type uC} [Category.{v} C]
    {W X Y Z : C}
    (leftEq : W = X) (rightEq : Y = Z)
    (middle : X ⟶ Y) (value : W ⟶ Z)
    (sandwichValue :
      eqToHom leftEq ≫ middle ≫ eqToHom rightEq = value) :
    HEq middle value := by
  have strip :
      HEq
        (eqToHom leftEq ≫ middle ≫ eqToHom rightEq)
        middle :=
    by
      rw [← Category.assoc]
      exact
        (CategoryTheory.comp_eqToHom_heq _ _).trans
          (CategoryTheory.eqToHom_comp_heq _ _)
  exact strip.symm.trans (heq_of_eq sandwichValue)

theorem transport_sandwich_heq
    {C : Type uC} [Category.{v} C]
    {W X Y Z : C}
    (leftEq : W = X) (rightEq : Y = Z)
    (middle : X ⟶ Y) :
    HEq
      (eqToHom leftEq ≫ middle ≫ eqToHom rightEq)
      middle := by
  rw [← Category.assoc]
  exact
    (CategoryTheory.comp_eqToHom_heq _ _).trans
      (CategoryTheory.eqToHom_comp_heq _ _)

/-- The local role-aware compiler agrees with the elementary interpretation
of the exact event stored at the same trace index. -/
theorem compileRoleAwareCutOpenEventAt_heq_elementary
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin presentation.cut.exterior.eventCount) :
    HEq (compileRoleAwareCutOpenEventAt 𝒞 diagram presentation labeling i)
      (compileCutOpenEventMorphism 𝒞 diagram labeling
        (presentation.cut.exterior.events i)
        (presentation.cut.exterior.strandContinuationsAreWellFormed i)) := by
  exact heq_of_eq
    (compileRoleAwareCutOpenEventAt_eq_elementary
      𝒞 diagram presentation labeling i)

noncomputable def compiledExteriorTrace
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    FiniteMorphismTrace 𝒞.C
      presentation.cut.exterior.eventCount where
  object i :=
    ribbonWordObject 𝒞
      (exteriorWord 𝒞 diagram labeling
        (presentation.cut.exterior.activeOrder i))
  edge i :=
    compileRoleAwareContextualCutOpenEventMorphism 𝒞 diagram presentation labeling i

noncomputable def compiledExteriorTraceFromUnit
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    𝟙_ 𝒞.C ⟶
      (compiledExteriorTrace 𝒞 diagram presentation labeling).object
        (Fin.last presentation.cut.exterior.eventCount) :=
  eqToHom
      (congrArg
        (fun word =>
          ribbonWordObject 𝒞
            (exteriorWord 𝒞 diagram labeling word))
        presentation.cut.exterior.initialBoundaryEmpty).symm ≫
    (compiledExteriorTrace 𝒞 diagram presentation labeling).composeAll

/--
The proof-internal coordinate information used by the graphical compiler.

Unlike the homology transport structures, this contains only the finite
reindexing needed to compare the unchanged labels and the one new meridian.
-/
structure OneTwoGraphCoordinates
    (lower higher : HomologicallyMarkedDiagram) where
  indexEquiv :
    (Fin lower.diagram.handles.hTwo ⊕ Unit) ≃
      Fin higher.diagram.handles.hTwo

def OneTwoGraphCoordinates.MatchesCanonicalMeridian
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates lower higher) : Prop :=
  (∀ i : Fin lower.diagram.handles.hTwo,
    (higher.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (lower.diagram.handles.twoHandleIndex i).1.1) ∧
  ((higher.diagram.handles.twoHandleIndex
    (coordinates.indexEquiv (Sum.inr ()))).1.1 =
      lower.diagram.trace.componentCount + 1)

theorem OneTwoGraphCoordinates.oldComponent
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates lower higher)
    (binding : coordinates.MatchesCanonicalMeridian)
    (i : Fin lower.diagram.handles.hTwo) :
    (higher.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (lower.diagram.handles.twoHandleIndex i).1.1 :=
  binding.1 i

theorem OneTwoGraphCoordinates.newComponent
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates lower higher)
    (binding : coordinates.MatchesCanonicalMeridian) :
    (higher.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inr ()))).1.1 =
        lower.diagram.trace.componentCount + 1 :=
  binding.2

def OneTwoGraphCoordinates.ofAdded
    {lower higher : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport lower higher}
    (coordinates :
      AddedTwoHandleCoordinates lower higher transport) :
    OneTwoGraphCoordinates lower higher where
  indexEquiv := coordinates.indexEquiv

theorem OneTwoGraphCoordinates.ofAdded_matchesCanonicalMeridian
    {lower higher : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport lower higher}
    (coordinates :
      AddedTwoHandleCoordinates lower higher transport)
    (binding : coordinates.MatchesOneTwoBirthMeridian) :
    (OneTwoGraphCoordinates.ofAdded coordinates).MatchesCanonicalMeridian :=
  binding

def OneTwoGraphCoordinates.ofRemoved
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport) :
    OneTwoGraphCoordinates lower higher where
  indexEquiv := coordinates.indexEquiv

theorem OneTwoGraphCoordinates.ofRemoved_matchesCanonicalMeridian
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport)
    (binding : coordinates.MatchesOneTwoDeathMeridian) :
    (OneTwoGraphCoordinates.ofRemoved coordinates).MatchesCanonicalMeridian :=
  binding

def OneTwoGraphCoordinates.mergeLabeling
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates lower higher)
    {Label : Type*}
    (lowerLabeling : Fin lower.diagram.handles.hTwo → Label)
    (newLabel : Label) :
    Fin higher.diagram.handles.hTwo → Label :=
  fun i =>
    match coordinates.indexEquiv.symm i with
    | .inl old => lowerLabeling old
    | .inr _ => newLabel

noncomputable def oneTwoBirthExpectedTraceMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    𝟙_ 𝒞.C ⟶
      (compiledExteriorTrace 𝒞 source.diagram source.cut sourceLabeling).object
        (Fin.last source.cut.cut.exterior.eventCount) :=
  specialCutMeridianMorphismWithoutExplicitTwist 𝒞
      (exteriorStrandLabel 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (oneTwoFirstStrand normalForm)) ≫
    compiledExteriorTraceFromUnit 𝒞 source.diagram source.cut sourceLabeling

noncomputable def standardOneTwoBirthTargetTrace
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (labeling : TwoHandleLabeling 𝒞 target) :
    FiniteMorphismTrace 𝒞.C
      (sourceCut.cut.exterior.eventCount + 3) :=
  FiniteMorphismTrace.castEventCount
    (standardOneTwoBirth_eventCount normalForm).symm
    (compiledExteriorTrace 𝒞 target targetCut labeling)

theorem standardOneTwoBirthTargetTrace_composeAll
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (labeling : TwoHandleLabeling 𝒞 target) :
    HEq
      (standardOneTwoBirthTargetTrace 𝒞 normalForm labeling).composeAll
      (compiledExteriorTrace 𝒞 target targetCut labeling).composeAll := by
  exact FiniteMorphismTrace.castEventCount_composeAll _ _

theorem compileCutOpenExteriorMorphism_eq_compiledTrace
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    compileCutOpenExteriorMorphism 𝒞 diagram presentation labeling =
      eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            presentation.cut.exterior.initialBoundaryEmpty).symm ≫
        (compiledExteriorTrace 𝒞 diagram presentation labeling).composeAll ≫
          eqToHom
            (congrArg
              (fun word =>
                ribbonWordObject 𝒞
                  (exteriorWord 𝒞 diagram labeling word))
              presentation.cut.exterior.finalBoundaryEmpty) := by
  rfl

theorem compileCutOpenExteriorMorphism_heq_compiledTrace
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    HEq
      (compileCutOpenExteriorMorphism 𝒞 diagram presentation labeling)
      ((compiledExteriorTrace 𝒞 diagram presentation labeling).composeAll) := by
  rw [compileCutOpenExteriorMorphism_eq_compiledTrace]
  exact transport_sandwich_heq _ _ _

theorem compileCutOpenExteriorMorphism_heq_fromUnit
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram) :
    HEq
      (compileCutOpenExteriorMorphism 𝒞 diagram presentation labeling)
      (compiledExteriorTraceFromUnit 𝒞 diagram presentation labeling) := by
  rw [compileCutOpenExteriorMorphism_eq_compiledTrace]
  unfold compiledExteriorTraceFromUnit
  rw [← Category.assoc]
  exact CategoryTheory.comp_eqToHom_heq _ _

theorem list_context_unique_of_nodup
    {α : Type*}
    {whole left₁ left₂ middle right₁ right₂ : List α}
    (wholeNodup : whole.Nodup)
    (middleNonempty : middle ≠ [])
    (first : whole = left₁ ++ middle ++ right₁)
    (second : whole = left₂ ++ middle ++ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  classical
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil middleNonempty
  have firstNodup : (left₁ ++ head :: tail ++ right₁).Nodup := by
    simpa [first] using wholeNodup
  have secondNodup : (left₂ ++ head :: tail ++ right₂).Nodup := by
    simpa [second] using wholeNodup
  have headNotLeft₁ : head ∉ left₁ := by
    have normalized :
        (left₁ ++ (head :: tail ++ right₁)).Nodup := by
      simpa [List.append_assoc] using firstNodup
    have disjoint := (List.nodup_append.mp normalized).2.2
    intro membership
    exact (disjoint head membership head (by simp)) rfl
  have headNotLeft₂ : head ∉ left₂ := by
    have normalized :
        (left₂ ++ (head :: tail ++ right₂)).Nodup := by
      simpa [List.append_assoc] using secondNodup
    have disjoint := (List.nodup_append.mp normalized).2.2
    intro membership
    exact (disjoint head membership head (by simp)) rfl
  have wholeEquality :
      left₁ ++ head :: tail ++ right₁ =
        left₂ ++ head :: tail ++ right₂ :=
    first.symm.trans second
  have lengthEquality : left₁.length = left₂.length := by
    have indices := congrArg (List.idxOf head) wholeEquality
    simp [List.idxOf_append, headNotLeft₁, headNotLeft₂] at indices
    exact indices
  have leftEquality : left₁ = left₂ := by
    have taken :=
      congrArg (List.take left₁.length) wholeEquality
    simpa [lengthEquality] using taken
  subst left₂
  have tails :
      head :: tail ++ right₁ =
        head :: tail ++ right₂ :=
    List.append_right_injective left₁ (by
      simpa [List.append_assoc] using wholeEquality)
  exact ⟨rfl, List.append_right_injective (head :: tail) (by
    simpa [List.append_assoc] using tails)⟩

def standardOneTwoBirthOldComponent
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (component : source.trace.ComponentId) :
    target.trace.ComponentId :=
  ⟨component.1, by
    rw [standardOneTwoBirth_componentCount normalForm]
    omega⟩

def standardOneTwoBirthOldStrand
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (strand : source.trace.StrandId) :
    target.trace.StrandId :=
  ⟨strand.1, by
    rw [standardOneTwoBirth_strandCount normalForm]
    omega⟩

theorem standardOneTwoBirth_oldComponentData
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (component : source.trace.ComponentId) :
    target.trace.components
        (standardOneTwoBirthOldComponent normalForm component) =
      source.trace.components component := by
  have targetBound :
      component.1 < target.trace.componentCount := by
    rw [standardOneTwoBirth_componentCount normalForm]
    omega
  have atIndex :=
    congrArg (fun components => components[component.1]?) normalForm.1
  simp [serializedComponents, oneTwoLocalComponents,
    standardOneTwoBirthOldComponent, component.2, targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [component.2])] at atIndex
  simp at atIndex
  exact atIndex

theorem standardOneTwoBirth_oldStrandComponentValue
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (strand : source.trace.StrandId) :
    (target.trace.strands
      (standardOneTwoBirthOldStrand normalForm strand)).component.1 =
      (source.trace.strands strand).component.1 := by
  have targetBound :
      strand.1 < target.trace.strandCount := by
    rw [standardOneTwoBirth_strandCount normalForm]
    omega
  have atIndex :=
    congrArg (fun strands => strands[strand.1]?) normalForm.2.1
  simp [serializedStrands, oneTwoLocalStrands,
    serializeStrand, standardOneTwoBirthOldStrand,
    strand.2, targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [strand.2])] at atIndex
  simp at atIndex
  exact atIndex.1

theorem standardOneTwoBirth_oldStrandComponent
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (strand : source.trace.StrandId) :
    (target.trace.strands
      (standardOneTwoBirthOldStrand normalForm strand)).component =
      standardOneTwoBirthOldComponent normalForm
        (source.trace.strands strand).component :=
  Fin.ext
    (standardOneTwoBirth_oldStrandComponentValue normalForm strand)

theorem standardOneTwoBirth_oldStrandOrientation
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (strand : source.trace.StrandId) :
    (target.trace.strands
      (standardOneTwoBirthOldStrand normalForm strand)).orientation =
      (source.trace.strands strand).orientation := by
  have targetBound :
      strand.1 < target.trace.strandCount := by
    rw [standardOneTwoBirth_strandCount normalForm]
    omega
  have atIndex :=
    congrArg (fun strands => strands[strand.1]?) normalForm.2.1
  simp [serializedStrands, oneTwoLocalStrands,
    serializeStrand, standardOneTwoBirthOldStrand,
    strand.2, targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [strand.2])] at atIndex
  simp at atIndex
  exact atIndex.2

theorem standardOneTwoBirth_oldExteriorStrandLabel
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (strand : source.diagram.trace.StrandId) :
    exteriorStrandLabel 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldStrand normalForm strand) =
      exteriorStrandLabel 𝒞 source.diagram sourceLabeling strand := by
  let sourceComponent :=
    (source.diagram.trace.strands strand).component
  let targetComponent :=
    (target.diagram.trace.strands
      (standardOneTwoBirthOldStrand normalForm strand)).component
  have componentValue :
      targetComponent.1 = sourceComponent.1 :=
    standardOneTwoBirth_oldStrandComponentValue normalForm strand
  have componentEq :
      targetComponent =
        standardOneTwoBirthOldComponent normalForm sourceComponent :=
    Fin.ext componentValue
  have componentData :
      target.diagram.trace.components targetComponent =
        source.diagram.trace.components sourceComponent := by
    rw [componentEq]
    exact standardOneTwoBirth_oldComponentData normalForm sourceComponent
  unfold exteriorStrandLabel
  dsimp only [targetComponent, sourceComponent] at componentEq componentData ⊢
  split <;> rename_i targetRole
  · have sourceRole :
        (source.diagram.trace.components
          (source.diagram.trace.strands strand).component).role ≠
            .dotted := by
        simpa [componentData] using targetRole
    rw [dif_pos sourceRole]
    let sourceIndex :=
      source.diagram.handles.twoHandleIndex.symm
        ⟨(source.diagram.trace.strands strand).component, sourceRole⟩
    have targetIndexEq :
        target.diagram.handles.twoHandleIndex.symm
            ⟨(target.diagram.trace.strands
                (standardOneTwoBirthOldStrand normalForm strand)).component,
              targetRole⟩ =
          coordinates.indexEquiv (Sum.inl sourceIndex) := by
      apply target.diagram.handles.twoHandleIndex.injective
      apply Subtype.ext
      apply Fin.ext
      rw [Equiv.apply_symm_apply]
      calc
        (target.diagram.trace.strands
            (standardOneTwoBirthOldStrand normalForm strand)).component.1 =
            (source.diagram.trace.strands strand).component.1 :=
          componentValue
        _ =
            (source.diagram.handles.twoHandleIndex sourceIndex).1.1 := by
          simp [sourceIndex]
        _ =
            (target.diagram.handles.twoHandleIndex
              (coordinates.indexEquiv (Sum.inl sourceIndex))).1.1 :=
          (coordinates.oldComponent coordinateBinding sourceIndex).symm
    rw [targetIndexEq]
    simp [OneTwoGraphCoordinates.mergeLabeling, sourceIndex]
  · have sourceRole :
        ¬(source.diagram.trace.components
          (source.diagram.trace.strands strand).component).role ≠
            .dotted := by
        simpa [componentData] using targetRole
    rw [dif_neg sourceRole]

theorem standardOneTwoBirth_oldOrientedExteriorStrand
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (strand : source.diagram.trace.StrandId) :
    orientedExteriorStrand 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldStrand normalForm strand) =
      orientedExteriorStrand 𝒞 source.diagram sourceLabeling strand := by
  apply congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
  · exact standardOneTwoBirth_oldExteriorStrandLabel
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel strand
  · exact congrArg ribbonDirectionOfStrandOrientation
      (standardOneTwoBirth_oldStrandOrientation normalForm strand)

theorem standardOneTwoBirth_newMeridianLabel
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    exteriorStrandLabel 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (oneTwoFirstStrand normalForm) =
      newLabel := by
  have firstComponent :=
    standardOneTwoBirth_firstStrandData normalForm
  have firstRole :
      (target.diagram.trace.components
        (target.diagram.trace.strands
          (oneTwoFirstStrand normalForm)).component).role ≠ .dotted := by
    have componentValue :=
      congrArg SerializedStrand.component firstComponent
    simp [serializeStrand] at componentValue
    have componentEq :
        (target.diagram.trace.strands
          (oneTwoFirstStrand normalForm)).component =
          ⟨source.diagram.trace.componentCount + 1, by
            rw [standardOneTwoBirth_componentCount normalForm]
            omega⟩ := Fin.ext componentValue
    rw [componentEq]
    have componentData :=
      congrArg
        (fun components =>
          components[source.diagram.trace.componentCount + 1]?)
        normalForm.1
    simp [serializedComponents, oneTwoLocalComponents] at componentData
    obtain ⟨_, componentData⟩ := componentData
    simpa [componentData]
  unfold exteriorStrandLabel
  rw [dif_pos firstRole]
  have indexEq :
      target.diagram.handles.twoHandleIndex.symm
          ⟨(target.diagram.trace.strands
              (oneTwoFirstStrand normalForm)).component,
            firstRole⟩ =
        coordinates.indexEquiv (Sum.inr ()) := by
    apply target.diagram.handles.twoHandleIndex.injective
    apply Subtype.ext
    apply Fin.ext
    rw [Equiv.apply_symm_apply]
    calc
      (target.diagram.trace.strands
          (oneTwoFirstStrand normalForm)).component.1 =
          source.diagram.trace.componentCount + 1 := by
        simpa [serializeStrand] using
          congrArg SerializedStrand.component firstComponent
      _ =
          (target.diagram.handles.twoHandleIndex
            (coordinates.indexEquiv (Sum.inr ()))).1.1 :=
        (coordinates.newComponent coordinateBinding).symm
  rw [indexEq]
  simp [OneTwoGraphCoordinates.mergeLabeling]

def standardOneTwoBirthOldStrands
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (strands : List source.trace.StrandId) :
    List target.trace.StrandId :=
  strands.map (standardOneTwoBirthOldStrand normalForm)

theorem standardOneTwoBirth_oldStrands_values
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (strands : List source.trace.StrandId) :
    List.map Fin.val
        (standardOneTwoBirthOldStrands normalForm strands) =
      List.map Fin.val strands := by
  induction strands with
  | nil => rfl
  | cons strand rest inductionHypothesis =>
      simp only [standardOneTwoBirthOldStrands, List.map_cons]
      exact congrArg (List.cons strand.1) inductionHypothesis

theorem standardOneTwoBirth_oldExteriorWord
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (strands : List source.diagram.trace.StrandId) :
    exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldStrands normalForm strands) =
      exteriorWord 𝒞 source.diagram sourceLabeling strands := by
  induction strands with
  | nil => rfl
  | cons strand rest inductionHypothesis =>
      simp only [standardOneTwoBirthOldStrands, List.map_cons,
        exteriorWord]
      rw [standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel strand]
      exact congrArg
        (List.cons
          (orientedExteriorStrand 𝒞 source.diagram
            sourceLabeling strand))
        inductionHypothesis

theorem standardOneTwoBirth_oldActiveOrder
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (state : Fin (sourceCut.cut.exterior.eventCount + 1)) :
    targetCut.cut.exterior.activeOrder
        ⟨state.1 + 3, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
      standardOneTwoBirthOldStrands normalForm
        (sourceCut.cut.exterior.activeOrder state) := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have atIndex :=
    congrArg (fun orders => orders[state.1 + 3]?)
      normalForm.2.2.2.1
  rcases state with ⟨_ | state, stateBound⟩
  · calc
      _ = List.map (@Fin.val source.trace.strandCount)
          (sourceCut.cut.exterior.activeOrder 0) := by
            simp [serializedActiveOrders,
              oneTwoLocalActiveOrders] at atIndex
            rcases atIndex with ⟨_, atIndex⟩
            exact atIndex
      _ = _ :=
        (standardOneTwoBirth_oldStrands_values normalForm _).symm
  · have sourceBound :
        state < sourceCut.cut.exterior.eventCount := by omega
    have targetBound :
        state + 3 < targetCut.cut.exterior.eventCount := by
      rw [standardOneTwoBirth_eventCount normalForm]
      omega
    simp [serializedActiveOrders, oneTwoLocalActiveOrders,
      sourceBound, targetBound] at atIndex
    calc
      _ = List.map (@Fin.val source.trace.strandCount)
          (sourceCut.cut.exterior.activeOrder
            ⟨state + 1, stateBound⟩) := by
              convert atIndex using 1
      _ = _ :=
        (standardOneTwoBirth_oldStrands_values normalForm _).symm

theorem standardOneTwoBirth_oldEventSerialized
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : Fin sourceCut.cut.exterior.eventCount) :
    serializeCutOpenEvent
        (targetCut.cut.exterior.events
          ⟨event.1 + 3, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      serializeCutOpenEvent
        (sourceCut.cut.exterior.events event) := by
  have atIndex :=
    congrArg (fun events => events[event.1 + 3]?)
      normalForm.2.2.1
  have targetBound :
      event.1 + 3 <
        (serializedExteriorEvents targetCut).length := by
    simp [serializedExteriorEvents,
      standardOneTwoBirth_eventCount normalForm]
  simp [serializedExteriorEvents, oneTwoLocalEvents,
    targetBound, event.2] at atIndex
  exact atIndex.choose_spec

theorem serializePuncture_injective
    {trace : CombinatorialLinkTrace} :
    Function.Injective
      (serializePuncture :
        DottedPuncture trace → SerializedPuncture) := by
  intro left right equality
  cases left
  cases right
  simp [serializePuncture] at equality
  rcases equality with
    ⟨dottedEq, twoHandleEq, inputEq, outputEq,
      directionEq, positionEq⟩
  cases Fin.ext dottedEq
  cases Fin.ext inputEq
  cases Fin.ext outputEq
  subst_vars
  rfl

theorem serializeCutOpenEvent_injective
    {trace : CombinatorialLinkTrace} :
    Function.Injective
      (serializeCutOpenEvent :
        CutOpenEvent trace → SerializedCutOpenEvent) := by
  intro left right equality
  cases left <;> cases right <;>
    simp [serializeCutOpenEvent] at equality ⊢
  case birth.birth =>
    exact ⟨Fin.ext equality.1, Fin.ext equality.2⟩
  case death.death =>
    exact ⟨Fin.ext equality.1, Fin.ext equality.2⟩
  case crossing.crossing =>
    exact
      ⟨Fin.ext equality.1, Fin.ext equality.2.1,
        Fin.ext equality.2.2.1, Fin.ext equality.2.2.2.1,
        equality.2.2.2.2⟩
  case framingTwist.framingTwist =>
    exact ⟨Fin.ext equality.1, Fin.ext equality.2.1, equality.2.2⟩
  case planarIsotopy.planarIsotopy =>
    apply List.ext_get
    · simpa using congrArg List.length equality
    · intro index leftBound rightBound
      have atIndex := congrArg (fun items => items[index]?) equality
      simp [leftBound, rightBound] at atIndex
      exact Prod.ext (Fin.ext atIndex.1) (Fin.ext atIndex.2)
  case projectorHole.projectorHole =>
    refine ⟨Fin.ext equality.1, ?_⟩
    exact
      (List.map_injective_iff.mpr serializePuncture_injective)
        equality.2

def standardOneTwoBirthOldPuncture
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (puncture : DottedPuncture source.trace) :
    DottedPuncture target.trace where
  dottedComponent :=
    standardOneTwoBirthOldComponent normalForm puncture.dottedComponent
  twoHandleComponent :=
    standardOneTwoBirthOldComponent normalForm puncture.twoHandleComponent
  inputStrand :=
    standardOneTwoBirthOldStrand normalForm puncture.inputStrand
  outputStrand :=
    standardOneTwoBirthOldStrand normalForm puncture.outputStrand
  direction := puncture.direction
  cutPosition := puncture.cutPosition
  dotted_role := by
    simpa [standardOneTwoBirth_oldComponentData normalForm] using
      puncture.dotted_role
  two_handle_role := by
    simpa [standardOneTwoBirth_oldComponentData normalForm] using
      puncture.two_handle_role
  input_on_two_handle := by
    apply Fin.ext
    calc
      (target.trace.strands
          (standardOneTwoBirthOldStrand normalForm
            puncture.inputStrand)).component.1 =
          (source.trace.strands puncture.inputStrand).component.1 :=
        standardOneTwoBirth_oldStrandComponentValue
          normalForm puncture.inputStrand
      _ = puncture.twoHandleComponent.1 :=
        congrArg Fin.val puncture.input_on_two_handle
  output_on_two_handle := by
    apply Fin.ext
    calc
      (target.trace.strands
          (standardOneTwoBirthOldStrand normalForm
            puncture.outputStrand)).component.1 =
          (source.trace.strands puncture.outputStrand).component.1 :=
        standardOneTwoBirth_oldStrandComponentValue
          normalForm puncture.outputStrand
      _ = puncture.twoHandleComponent.1 :=
        congrArg Fin.val puncture.output_on_two_handle
  orientation_preserved := by
    rw [standardOneTwoBirth_oldStrandOrientation normalForm,
      standardOneTwoBirth_oldStrandOrientation normalForm]
    exact puncture.orientation_preserved

def standardOneTwoBirthOldEvent
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut) :
    CutOpenEvent source.trace → CutOpenEvent target.trace
  | .birth left right =>
      .birth
        (standardOneTwoBirthOldStrand normalForm left)
        (standardOneTwoBirthOldStrand normalForm right)
  | .death left right =>
      .death
        (standardOneTwoBirthOldStrand normalForm left)
        (standardOneTwoBirthOldStrand normalForm right)
  | .crossing overInput underInput overOutput underOutput sign =>
      .crossing
        (standardOneTwoBirthOldStrand normalForm overInput)
        (standardOneTwoBirthOldStrand normalForm underInput)
        (standardOneTwoBirthOldStrand normalForm overOutput)
        (standardOneTwoBirthOldStrand normalForm underOutput)
        sign
  | .framingTwist input output sign =>
      .framingTwist
        (standardOneTwoBirthOldStrand normalForm input)
        (standardOneTwoBirthOldStrand normalForm output)
        sign
  | .planarIsotopy continuations =>
      .planarIsotopy
        (continuations.map fun pair =>
          (standardOneTwoBirthOldStrand normalForm pair.1,
            standardOneTwoBirthOldStrand normalForm pair.2))
  | .projectorHole dotted punctures =>
      .projectorHole
        (standardOneTwoBirthOldComponent normalForm dotted)
        (punctures.map
          (standardOneTwoBirthOldPuncture normalForm))

theorem standardOneTwoBirth_oldEventSerialization
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : CutOpenEvent source.trace) :
    serializeCutOpenEvent
        (standardOneTwoBirthOldEvent normalForm event) =
      serializeCutOpenEvent event := by
  cases event <;>
    simp [standardOneTwoBirthOldEvent,
      standardOneTwoBirthOldStrand,
      standardOneTwoBirthOldComponent,
      standardOneTwoBirthOldPuncture,
      serializeCutOpenEvent, serializePuncture]

theorem standardOneTwoBirth_oldEvent
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : Fin sourceCut.cut.exterior.eventCount) :
    targetCut.cut.exterior.events
        ⟨event.1 + 3, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
      standardOneTwoBirthOldEvent normalForm
        (sourceCut.cut.exterior.events event) := by
  apply serializeCutOpenEvent_injective
  rw [standardOneTwoBirth_oldEventSerialized normalForm event]
  exact
    (standardOneTwoBirth_oldEventSerialization normalForm _).symm

theorem standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : CutOpenEvent source.trace)
    (pairing : event.StrandContinuationsAreWellFormed) :
    (standardOneTwoBirthOldEvent normalForm event).StrandContinuationsAreWellFormed := by
  cases event with
  | birth left right =>
      exact
        ⟨by
          rw [standardOneTwoBirth_oldStrandComponent,
            standardOneTwoBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact pairing.2⟩
  | death left right =>
      exact
        ⟨by
          rw [standardOneTwoBirth_oldStrandComponent,
            standardOneTwoBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact pairing.2⟩
  | crossing overInput underInput overOutput underOutput sign =>
      exact
        ⟨by
          rw [standardOneTwoBirth_oldStrandComponent,
            standardOneTwoBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact pairing.2.1,
          by
            rw [standardOneTwoBirth_oldStrandComponent,
              standardOneTwoBirth_oldStrandComponent,
              pairing.2.2.1],
          by
            rw [standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact pairing.2.2.2⟩
  | framingTwist input output sign =>
      exact
        ⟨by
          rw [standardOneTwoBirth_oldStrandComponent,
            standardOneTwoBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact pairing.2⟩
  | planarIsotopy continuations =>
      intro pair membership
      simp only [standardOneTwoBirthOldEvent, List.mem_map] at membership
      rcases membership with ⟨sourcePair, sourceMembership, rfl⟩
      have sourcePairing := pairing sourcePair sourceMembership
      exact
        ⟨by
          rw [standardOneTwoBirth_oldStrandComponent,
            standardOneTwoBirth_oldStrandComponent,
            sourcePairing.1],
          by
            rw [standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact sourcePairing.2⟩
  | projectorHole dotted punctures =>
      intro puncture membership
      simp only [standardOneTwoBirthOldEvent, List.mem_map] at membership
      rcases membership with ⟨sourcePuncture, sourceMembership, rfl⟩
      have sourcePairing := pairing sourcePuncture sourceMembership
      exact
        ⟨by
          rw [standardOneTwoBirthOldPuncture,
            standardOneTwoBirth_oldStrandComponent,
            standardOneTwoBirth_oldStrandComponent,
            sourcePairing.1],
          by
            rw [standardOneTwoBirthOldPuncture,
              standardOneTwoBirth_oldStrandOrientation,
              standardOneTwoBirth_oldStrandOrientation]
            exact sourcePairing.2⟩

theorem standardOneTwoBirth_oldEventBeforeWord
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : CutOpenEvent source.trace) :
    (standardOneTwoBirthOldEvent normalForm event).beforeWord =
      standardOneTwoBirthOldStrands normalForm event.beforeWord := by
  cases event <;>
    simp [standardOneTwoBirthOldEvent,
      standardOneTwoBirthOldStrands,
      standardOneTwoBirthOldPuncture,
      CutOpenEvent.beforeWord]

theorem standardOneTwoBirth_oldEventAfterWord
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : CutOpenEvent source.trace) :
    (standardOneTwoBirthOldEvent normalForm event).afterWord =
      standardOneTwoBirthOldStrands normalForm event.afterWord := by
  cases event <;>
    simp [standardOneTwoBirthOldEvent,
      standardOneTwoBirthOldStrands,
      standardOneTwoBirthOldPuncture,
      CutOpenEvent.afterWord]

theorem canonicalPositiveNegativeBirth_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {left right : 𝒞.simples.Simple}
    (labelEq : left = right) :
    HEq
      (canonicalPositiveNegativeBirth 𝒞 left)
      (canonicalPositiveNegativeBirth 𝒞 right) := by
  cases labelEq
  rfl

theorem canonicalNegativePositiveBirth_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {left right : 𝒞.simples.Simple}
    (labelEq : left = right) :
    HEq
      (canonicalNegativePositiveBirth 𝒞 left)
      (canonicalNegativePositiveBirth 𝒞 right) := by
  cases labelEq
  rfl

theorem canonicalPositiveNegativeDeath_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {left right : 𝒞.simples.Simple}
    (labelEq : left = right) :
    HEq
      (canonicalPositiveNegativeDeath 𝒞 left)
      (canonicalPositiveNegativeDeath 𝒞 right) := by
  cases labelEq
  rfl

theorem canonicalNegativePositiveDeath_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {left right : 𝒞.simples.Simple}
    (labelEq : left = right) :
    HEq
      (canonicalNegativePositiveDeath 𝒞 left)
      (canonicalNegativePositiveDeath 𝒞 right) := by
  cases labelEq
  rfl

noncomputable def canonicalCrossingMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (overInput underInput overOutput underOutput :
      OrientedSimple 𝒞)
    (sign : CrossingSign)
    (overEq : overInput = overOutput)
    (underEq : underInput = underOutput) :
    ribbonWordObject 𝒞 [overInput, underInput] ⟶
      ribbonWordObject 𝒞 [underOutput, overOutput] := by
  rw [← overEq, ← underEq]
  cases sign with
  | positive =>
      exact
        (α_ _ _ (𝟙_ 𝒞.C)).inv ≫
          ((β_ _ _).hom ⊗ₘ 𝟙 (𝟙_ 𝒞.C)) ≫
          (α_ _ _ (𝟙_ 𝒞.C)).hom
  | negative =>
      exact
        (α_ _ _ (𝟙_ 𝒞.C)).inv ≫
          ((β_ _ _).inv ⊗ₘ 𝟙 (𝟙_ 𝒞.C)) ≫
          (α_ _ _ (𝟙_ 𝒞.C)).hom

theorem canonicalCrossingMorphism_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {overInput₁ overInput₂ underInput₁ underInput₂
      overOutput₁ overOutput₂ underOutput₁ underOutput₂ :
        OrientedSimple 𝒞}
    (overInputEq : overInput₁ = overInput₂)
    (underInputEq : underInput₁ = underInput₂)
    (overOutputEq : overOutput₁ = overOutput₂)
    (underOutputEq : underOutput₁ = underOutput₂)
    (sign : CrossingSign)
    (overEq₁ : overInput₁ = overOutput₁)
    (underEq₁ : underInput₁ = underOutput₁)
    (overEq₂ : overInput₂ = overOutput₂)
    (underEq₂ : underInput₂ = underOutput₂) :
    HEq
      (canonicalCrossingMorphism 𝒞
        overInput₁ underInput₁ overOutput₁ underOutput₁
        sign overEq₁ underEq₁)
      (canonicalCrossingMorphism 𝒞
        overInput₂ underInput₂ overOutput₂ underOutput₂
        sign overEq₂ underEq₂) := by
  cases overInputEq
  cases underInputEq
  cases overOutputEq
  cases underOutputEq
  have overProof : overEq₁ = overEq₂ := Subsingleton.elim _ _
  have underProof : underEq₁ = underEq₂ := Subsingleton.elim _ _
  cases overProof
  cases underProof
  rfl

noncomputable def canonicalFramingTwistMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (input output : OrientedSimple 𝒞)
    (sign : CrossingSign)
    (strandEq : input = output) :
    ribbonWordObject 𝒞 [input] ⟶
      ribbonWordObject 𝒞 [output] := by
  have objectEq :
      orientedSimpleObject 𝒞 input =
        orientedSimpleObject 𝒞 output :=
    congrArg (orientedSimpleObject 𝒞) strandEq
  cases sign with
  | positive =>
      exact
        (ρ_ _).hom ≫
          𝒞.twist.hom.app _ ≫
          eqToHom objectEq ≫
          (ρ_ _).inv
  | negative =>
      exact
        (ρ_ _).hom ≫
          𝒞.twist.inv.app _ ≫
          eqToHom objectEq ≫
          (ρ_ _).inv

theorem canonicalFramingTwistMorphism_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {input₁ input₂ output₁ output₂ : OrientedSimple 𝒞}
    (inputEq : input₁ = input₂)
    (outputEq : output₁ = output₂)
    (sign : CrossingSign)
    (strandEq₁ : input₁ = output₁)
    (strandEq₂ : input₂ = output₂) :
    HEq
      (canonicalFramingTwistMorphism 𝒞
        input₁ output₁ sign strandEq₁)
      (canonicalFramingTwistMorphism 𝒞
        input₂ output₂ sign strandEq₂) := by
  cases inputEq
  cases outputEq
  have strandProof : strandEq₁ = strandEq₂ := Subsingleton.elim _ _
  cases strandProof
  rfl

theorem compileCrossingMorphism_heq_canonical
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (overInput underInput overOutput underOutput :
      diagram.trace.StrandId)
    (sign : CrossingSign)
    (pairing :
      (CutOpenEvent.crossing overInput underInput
        overOutput underOutput sign).StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 diagram labeling
        (.crossing overInput underInput overOutput underOutput sign)
        pairing)
      (canonicalCrossingMorphism 𝒞
        (orientedExteriorStrand 𝒞 diagram labeling overInput)
        (orientedExteriorStrand 𝒞 diagram labeling underInput)
        (orientedExteriorStrand 𝒞 diagram labeling overOutput)
        (orientedExteriorStrand 𝒞 diagram labeling underOutput)
        sign
        (orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling pairing.1 pairing.2.1)
        (orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling pairing.2.2.1 pairing.2.2.2)) := by
  have overEq :=
    orientedExteriorStrand_eq_of_component_and_orientation
      𝒞 diagram labeling pairing.1 pairing.2.1
  have underEq :=
    orientedExteriorStrand_eq_of_component_and_orientation
      𝒞 diagram labeling pairing.2.2.1 pairing.2.2.2
  cases sign <;>
    simp [compileCutOpenEventMorphism,
      canonicalCrossingMorphism, overEq, underEq] <;>
    apply heq_of_eq <;>
    monoidal

theorem compileFramingTwistMorphism_heq_canonical
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (input output : diagram.trace.StrandId)
    (sign : CrossingSign)
    (pairing :
      (CutOpenEvent.framingTwist input output sign).StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 diagram labeling
        (.framingTwist input output sign) pairing)
      (canonicalFramingTwistMorphism 𝒞
        (orientedExteriorStrand 𝒞 diagram labeling input)
        (orientedExteriorStrand 𝒞 diagram labeling output)
        sign
        (orientedExteriorStrand_eq_of_component_and_orientation
          𝒞 diagram labeling pairing.1 pairing.2)) := by
  have outputEq :=
    orientedExteriorStrand_eq_of_component_and_orientation
      𝒞 diagram labeling pairing.1 pairing.2
  cases sign <;>
    simp [compileCutOpenEventMorphism,
      canonicalFramingTwistMorphism, outputEq] <;>
    congr!

noncomputable def canonicalPlanarIsotopyMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (before after : RibbonWord 𝒞)
    (wordEq : before = after) :
    ribbonWordObject 𝒞 before ⟶ ribbonWordObject 𝒞 after := by
  rw [← wordEq]
  exact 𝟙 _

theorem canonicalPlanarIsotopyMorphism_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {before₁ before₂ after₁ after₂ : RibbonWord 𝒞}
    (beforeEq : before₁ = before₂)
    (afterEq : after₁ = after₂)
    (wordEq₁ : before₁ = after₁)
    (wordEq₂ : before₂ = after₂) :
    HEq
      (canonicalPlanarIsotopyMorphism 𝒞 before₁ after₁ wordEq₁)
      (canonicalPlanarIsotopyMorphism 𝒞 before₂ after₂ wordEq₂) := by
  cases beforeEq
  cases afterEq
  have proofEq : wordEq₁ = wordEq₂ := Subsingleton.elim _ _
  cases proofEq
  rfl

theorem compilePlanarIsotopyMorphism_heq_canonical
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (continuations : List (diagram.trace.StrandId × diagram.trace.StrandId))
    (pairing : (CutOpenEvent.planarIsotopy continuations).StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 diagram labeling
        (.planarIsotopy continuations) pairing)
      (canonicalPlanarIsotopyMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling (continuations.map Prod.fst))
        (exteriorWord 𝒞 diagram labeling (continuations.map Prod.snd))
        (exteriorWord_of_continuations_eq
          𝒞 diagram labeling continuations pairing)) := by
  have wordEq :=
    exteriorWord_of_continuations_eq
      𝒞 diagram labeling continuations pairing
  have proofEq :
      wordEq =
        exteriorWord_of_continuations_eq
          𝒞 diagram labeling continuations pairing :=
    Subsingleton.elim _ _
  cases proofEq
  rfl

noncomputable def canonicalProjectorHoleMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (before after : RibbonWord 𝒞)
    (wordEq : before = after) :
    ribbonWordObject 𝒞 before ⟶ ribbonWordObject 𝒞 after :=
  tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 before) ≫
    eqToHom (congrArg (ribbonWordObject 𝒞) wordEq)

theorem transportedProjectorHoleMorphism_eq_canonical
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {before middle after : RibbonWord 𝒞}
    (inputEq : before = middle)
    (outputEq : after = middle)
    (wordEq : before = after) :
    eqToHom (congrArg (ribbonWordObject 𝒞) inputEq) ≫
        tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 middle) ≫
        eqToHom (congrArg (ribbonWordObject 𝒞) outputEq.symm) =
      canonicalProjectorHoleMorphism 𝒞 before after wordEq := by
  subst middle
  subst after
  simp [canonicalProjectorHoleMorphism]

theorem canonicalProjectorHoleMorphism_heq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {before₁ before₂ after₁ after₂ : RibbonWord 𝒞}
    (beforeEq : before₁ = before₂)
    (afterEq : after₁ = after₂)
    (wordEq₁ : before₁ = after₁)
    (wordEq₂ : before₂ = after₂) :
    HEq
      (canonicalProjectorHoleMorphism 𝒞 before₁ after₁ wordEq₁)
      (canonicalProjectorHoleMorphism 𝒞 before₂ after₂ wordEq₂) := by
  cases beforeEq
  cases afterEq
  have proofEq : wordEq₁ = wordEq₂ := Subsingleton.elim _ _
  cases proofEq
  rfl

theorem compileProjectorHoleMorphism_heq_canonical
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing : (CutOpenEvent.projectorHole dotted punctures).StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 diagram labeling
        (.projectorHole dotted punctures) pairing)
      (canonicalProjectorHoleMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling
          (punctures.map DottedPuncture.inputStrand))
        (exteriorWord 𝒞 diagram labeling
          (punctures.map DottedPuncture.outputStrand))
        (exteriorWord_of_punctures_eq
          𝒞 diagram labeling punctures)) := by
  have inputEq :=
    exteriorInputWord_eq_cutBoundaryWord 𝒞 diagram labeling punctures
  have outputEq :=
    exteriorOutputWord_eq_cutBoundaryWord 𝒞 diagram labeling punctures
  unfold compileCutOpenEventMorphism
  simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord]
  apply heq_of_eq
  exact transportedProjectorHoleMorphism_eq_canonical
    𝒞 inputEq outputEq
      (exteriorWord_of_punctures_eq 𝒞 diagram labeling punctures)

theorem standardOneTwoBirth_oldEventMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : CutOpenEvent source.diagram.trace)
    (pairing : event.StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldEvent normalForm event)
        (standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed
          normalForm event pairing))
      (compileCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event pairing) := by
  cases event with
  | birth left right =>
      have rightLabelEq :=
        standardOneTwoBirth_oldExteriorStrandLabel
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel right
      have leftOrientationEq :=
        standardOneTwoBirth_oldStrandOrientation normalForm left
      simp only [compileCutOpenEventMorphism,
        standardOneTwoBirthOldEvent]
      unfold pairedBirthMorphism
      by_cases leftPositive :
          (source.diagram.trace.strands left).orientation = .positive
      · have targetPositive :
            (target.diagram.trace.strands
              (standardOneTwoBirthOldStrand normalForm left)).orientation =
                .positive := leftOrientationEq.trans leftPositive
        simp only [leftPositive, targetPositive, ↓reduceDIte]
        exact
          (CategoryTheory.comp_eqToHom_heq _ _).trans
            ((canonicalPositiveNegativeBirth_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.comp_eqToHom_heq _ _).symm)
      · have targetNotPositive :
            ¬(target.diagram.trace.strands
              (standardOneTwoBirthOldStrand normalForm left)).orientation =
                .positive := by
          intro targetPositive
          exact leftPositive (leftOrientationEq.symm.trans targetPositive)
        simp only [leftPositive, targetNotPositive, ↓reduceDIte]
        exact
          (CategoryTheory.comp_eqToHom_heq _ _).trans
            ((canonicalNegativePositiveBirth_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.comp_eqToHom_heq _ _).symm)
  | death left right =>
      have rightLabelEq :=
        standardOneTwoBirth_oldExteriorStrandLabel
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel right
      have leftOrientationEq :=
        standardOneTwoBirth_oldStrandOrientation normalForm left
      simp only [compileCutOpenEventMorphism,
        standardOneTwoBirthOldEvent]
      unfold pairedDeathMorphism
      by_cases leftPositive :
          (source.diagram.trace.strands left).orientation = .positive
      · have targetPositive :
            (target.diagram.trace.strands
              (standardOneTwoBirthOldStrand normalForm left)).orientation =
                .positive := leftOrientationEq.trans leftPositive
        simp only [leftPositive, targetPositive, ↓reduceDIte]
        exact
          (CategoryTheory.eqToHom_comp_heq _ _).trans
            ((canonicalPositiveNegativeDeath_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.eqToHom_comp_heq _ _).symm)
      · have targetNotPositive :
            ¬(target.diagram.trace.strands
              (standardOneTwoBirthOldStrand normalForm left)).orientation =
                .positive := by
          intro targetPositive
          exact leftPositive (leftOrientationEq.symm.trans targetPositive)
        simp only [leftPositive, targetNotPositive, ↓reduceDIte]
        exact
          (CategoryTheory.eqToHom_comp_heq _ _).trans
            ((canonicalNegativePositiveDeath_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.eqToHom_comp_heq _ _).symm)
  | crossing overInput underInput overOutput underOutput sign =>
      have overInputEq :=
        standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel overInput
      have underInputEq :=
        standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel underInput
      have overOutputEq :=
        standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel overOutput
      have underOutputEq :=
        standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel underOutput
      exact
        (compileCrossingMorphism_heq_canonical
        𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardOneTwoBirthOldStrand normalForm overInput)
          (standardOneTwoBirthOldStrand normalForm underInput)
          (standardOneTwoBirthOldStrand normalForm overOutput)
          (standardOneTwoBirthOldStrand normalForm underOutput)
          sign
          (standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed
            normalForm
            (.crossing overInput underInput
              overOutput underOutput sign)
            pairing)).trans
          ((canonicalCrossingMorphism_heq
            𝒞 overInputEq underInputEq overOutputEq underOutputEq sign
            _ _ _ _).trans
              (compileCrossingMorphism_heq_canonical
        𝒞 source.diagram source.cut sourceLabeling
                overInput underInput overOutput underOutput
                sign pairing).symm)
  | framingTwist input output sign =>
      have inputEq :=
        standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel input
      have outputEq :=
        standardOneTwoBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel output
      exact
        (compileFramingTwistMorphism_heq_canonical
        𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardOneTwoBirthOldStrand normalForm input)
          (standardOneTwoBirthOldStrand normalForm output)
          sign
          (standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed
            normalForm
            (.framingTwist input output sign)
            pairing)).trans
          ((canonicalFramingTwistMorphism_heq
            𝒞 inputEq outputEq sign _ _).trans
              (compileFramingTwistMorphism_heq_canonical
        𝒞 source.diagram source.cut sourceLabeling
                input output sign pairing).symm)
  | planarIsotopy continuations =>
      have beforeEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardOneTwoBirth_oldEventBeforeWord normalForm
            (.planarIsotopy continuations))).trans
          (standardOneTwoBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (continuations.map Prod.fst))
      have afterEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardOneTwoBirth_oldEventAfterWord normalForm
            (.planarIsotopy continuations))).trans
          (standardOneTwoBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (continuations.map Prod.snd))
      exact
        (compilePlanarIsotopyMorphism_heq_canonical
        𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
          (continuations.map fun
              (continuation :
                source.diagram.trace.StrandId ×
                  source.diagram.trace.StrandId) =>
            (standardOneTwoBirthOldStrand normalForm continuation.1,
              standardOneTwoBirthOldStrand normalForm continuation.2))
          (standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed
            normalForm (.planarIsotopy continuations) pairing)).trans
          ((canonicalPlanarIsotopyMorphism_heq
            𝒞 beforeEq afterEq _ _).trans
              (compilePlanarIsotopyMorphism_heq_canonical
        𝒞 source.diagram source.cut sourceLabeling
                continuations pairing).symm)
  | projectorHole dotted punctures =>
      have beforeEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardOneTwoBirth_oldEventBeforeWord normalForm
            (.projectorHole dotted punctures))).trans
          (standardOneTwoBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (punctures.map DottedPuncture.inputStrand))
      have afterEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardOneTwoBirth_oldEventAfterWord normalForm
            (.projectorHole dotted punctures))).trans
          (standardOneTwoBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (punctures.map DottedPuncture.outputStrand))
      exact
        (compileProjectorHoleMorphism_heq_canonical
        𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardOneTwoBirthOldComponent normalForm dotted)
          (punctures.map (standardOneTwoBirthOldPuncture normalForm))
          (standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed
            normalForm (.projectorHole dotted punctures) pairing)).trans
          ((canonicalProjectorHoleMorphism_heq
            𝒞 beforeEq afterEq _ _).trans
              (compileProjectorHoleMorphism_heq_canonical
        𝒞 source.diagram source.cut sourceLabeling
                dotted punctures pairing).symm)

theorem standardOneTwoBirth_oldStateExteriorWord
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (state : Fin (source.cut.cut.exterior.eventCount + 1)) :
    exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (target.cut.cut.exterior.activeOrder
          ⟨state.1 + 3, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      exteriorWord 𝒞 source.diagram sourceLabeling
        (source.cut.cut.exterior.activeOrder state) := by
  rw [standardOneTwoBirth_oldActiveOrder normalForm state]
  exact standardOneTwoBirth_oldExteriorWord
    𝒞 coordinates coordinateBinding normalForm
    sourceLabeling newLabel _

def standardOneTwoBirthOldEventIndex
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : Fin sourceCut.cut.exterior.eventCount) :
    Fin targetCut.cut.exterior.eventCount :=
  ⟨event.1 + 3, by
    rw [standardOneTwoBirth_eventCount normalForm]
    omega⟩

theorem standardOneTwoBirth_oldContexts_of_before_nonempty
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : Fin sourceCut.cut.exterior.eventCount)
    (beforeNonempty :
      (sourceCut.cut.exterior.events event).beforeWord ≠ []) :
      eventLeftContext target targetCut
          (standardOneTwoBirthOldEventIndex normalForm event) =
        standardOneTwoBirthOldStrands normalForm
          (eventLeftContext source sourceCut event) ∧
        eventRightContext target targetCut
          (standardOneTwoBirthOldEventIndex normalForm event) =
        standardOneTwoBirthOldStrands normalForm
          (eventRightContext source sourceCut event) := by
  let targetEvent :=
    standardOneTwoBirthOldEventIndex normalForm event
  have eventEq :
      targetCut.cut.exterior.events targetEvent =
        standardOneTwoBirthOldEvent normalForm
          (sourceCut.cut.exterior.events event) := by
    simpa [targetEvent, standardOneTwoBirthOldEventIndex] using
      standardOneTwoBirth_oldEvent normalForm event
  have targetBefore :
      targetCut.cut.exterior.activeOrder targetEvent.castSucc =
        standardOneTwoBirthOldStrands normalForm
          (sourceCut.cut.exterior.activeOrder event.castSucc) := by
    simpa [targetEvent, standardOneTwoBirthOldEventIndex] using
      standardOneTwoBirth_oldActiveOrder normalForm event.castSucc
  have mappedSourceTransition :
      standardOneTwoBirthOldStrands normalForm
          (sourceCut.cut.exterior.activeOrder event.castSucc) =
        standardOneTwoBirthOldStrands normalForm
            (eventLeftContext source sourceCut event) ++
          (standardOneTwoBirthOldEvent normalForm
            (sourceCut.cut.exterior.events event)).beforeWord ++
          standardOneTwoBirthOldStrands normalForm
            (eventRightContext source sourceCut event) := by
    have mapped :=
      congrArg (standardOneTwoBirthOldStrands normalForm)
        (eventTransitionEquations source sourceCut event).1
    simpa [standardOneTwoBirthOldStrands, List.map_append,
      standardOneTwoBirth_oldEventBeforeWord] using mapped
  have secondDecomposition :
      targetCut.cut.exterior.activeOrder targetEvent.castSucc =
        standardOneTwoBirthOldStrands normalForm
            (eventLeftContext source sourceCut event) ++
          (targetCut.cut.exterior.events targetEvent).beforeWord ++
          standardOneTwoBirthOldStrands normalForm
            (eventRightContext source sourceCut event) := by
    rw [targetBefore, eventEq]
    exact mappedSourceTransition
  have middleNonempty :
      (targetCut.cut.exterior.events targetEvent).beforeWord ≠ [] := by
    rw [eventEq, standardOneTwoBirth_oldEventBeforeWord]
    simpa [standardOneTwoBirthOldStrands] using beforeNonempty
  exact
    list_context_unique_of_nodup
      (targetCut.cut.exterior.activeWordsNoDuplicates
        targetEvent.castSucc)
      middleNonempty
      (eventTransitionEquations target targetCut targetEvent).1
      secondDecomposition

theorem standardOneTwoBirth_oldContexts_of_after_nonempty
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (event : Fin sourceCut.cut.exterior.eventCount)
    (afterNonempty :
      (sourceCut.cut.exterior.events event).afterWord ≠ []) :
      eventLeftContext target targetCut
          (standardOneTwoBirthOldEventIndex normalForm event) =
        standardOneTwoBirthOldStrands normalForm
          (eventLeftContext source sourceCut event) ∧
        eventRightContext target targetCut
          (standardOneTwoBirthOldEventIndex normalForm event) =
        standardOneTwoBirthOldStrands normalForm
          (eventRightContext source sourceCut event) := by
  let targetEvent :=
    standardOneTwoBirthOldEventIndex normalForm event
  have eventEq :
      targetCut.cut.exterior.events targetEvent =
        standardOneTwoBirthOldEvent normalForm
          (sourceCut.cut.exterior.events event) := by
    simpa [targetEvent, standardOneTwoBirthOldEventIndex] using
      standardOneTwoBirth_oldEvent normalForm event
  have targetAfter :
      targetCut.cut.exterior.activeOrder targetEvent.succ =
        standardOneTwoBirthOldStrands normalForm
          (sourceCut.cut.exterior.activeOrder event.succ) := by
    simpa [targetEvent, standardOneTwoBirthOldEventIndex] using
      standardOneTwoBirth_oldActiveOrder normalForm event.succ
  have mappedSourceTransition :
      standardOneTwoBirthOldStrands normalForm
          (sourceCut.cut.exterior.activeOrder event.succ) =
        standardOneTwoBirthOldStrands normalForm
            (eventLeftContext source sourceCut event) ++
          (standardOneTwoBirthOldEvent normalForm
            (sourceCut.cut.exterior.events event)).afterWord ++
          standardOneTwoBirthOldStrands normalForm
            (eventRightContext source sourceCut event) := by
    have mapped :=
      congrArg (standardOneTwoBirthOldStrands normalForm)
        (eventTransitionEquations source sourceCut event).2
    simpa [standardOneTwoBirthOldStrands, List.map_append,
      standardOneTwoBirth_oldEventAfterWord] using mapped
  have secondDecomposition :
      targetCut.cut.exterior.activeOrder targetEvent.succ =
        standardOneTwoBirthOldStrands normalForm
            (eventLeftContext source sourceCut event) ++
          (targetCut.cut.exterior.events targetEvent).afterWord ++
          standardOneTwoBirthOldStrands normalForm
            (eventRightContext source sourceCut event) := by
    rw [targetAfter, eventEq]
    exact mappedSourceTransition
  have middleNonempty :
      (targetCut.cut.exterior.events targetEvent).afterWord ≠ [] := by
    rw [eventEq, standardOneTwoBirth_oldEventAfterWord]
    simpa [standardOneTwoBirthOldStrands] using afterNonempty
  exact
    list_context_unique_of_nodup
      (targetCut.cut.exterior.activeWordsNoDuplicates
        targetEvent.succ)
      middleNonempty
      (eventTransitionEquations target targetCut targetEvent).2
      secondDecomposition

theorem compileContextualCutOpenEventMorphism_heq_core
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : Fin presentation.cut.exterior.eventCount) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event)
      (contextualizeRibbonMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling
          (eventLeftContext diagram presentation event))
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.events event).beforeWord)
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.events event).afterWord)
        (exteriorWord 𝒞 diagram labeling
          (eventRightContext diagram presentation event))
        (compileCutOpenEventMorphism 𝒞 diagram labeling
          (presentation.cut.exterior.events event)
          (presentation.cut.exterior.strandContinuationsAreWellFormed event))) := by
  unfold compileContextualCutOpenEventMorphism
  simp only
  simp only [CategoryTheory.eqToHom_comp_heq_iff]
  rw [← Category.assoc]
  exact
    (CategoryTheory.comp_eqToHom_heq _ _).trans
      (CategoryTheory.comp_eqToHom_heq _ _)

theorem compileRoleAwareContextualCutOpenEventMorphism_heq_core
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : Fin presentation.cut.exterior.eventCount) :
    HEq
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event)
      (contextualizeRibbonMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling
          (eventLeftContext diagram presentation event))
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.events event).beforeWord)
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.events event).afterWord)
        (exteriorWord 𝒞 diagram labeling
          (eventRightContext diagram presentation event))
        (compileRoleAwareCutOpenEventAt 𝒞 diagram presentation labeling event)) := by
  unfold compileRoleAwareContextualCutOpenEventMorphism
  simp only
  simp only [CategoryTheory.eqToHom_comp_heq_iff]
  rw [← Category.assoc]
  exact
    (CategoryTheory.comp_eqToHom_heq _ _).trans
      (CategoryTheory.comp_eqToHom_heq _ _)

/--
For one certified trace event, adding the same exact exterior context preserves
the equality between the role-aware and elementary event interpretations.  The
projector branch uses only the exact puncture-word completeness certificate;
puncture direction does not select a dual or a character exponent.
-/
theorem compileRoleAwareContextualCutOpenEventMorphism_heq_elementary
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : Fin presentation.cut.exterior.eventCount) :
    HEq
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event)
      (compileContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event) := by
  exact
    (compileRoleAwareContextualCutOpenEventMorphism_heq_core
      𝒞 diagram presentation labeling event).trans
      ((contextualizeRibbonMorphism_heq 𝒞 rfl rfl rfl rfl
        (compileRoleAwareCutOpenEventAt_heq_elementary
      𝒞 diagram presentation labeling event)).trans
        (compileContextualCutOpenEventMorphism_heq_core
      𝒞 diagram presentation labeling event).symm)

theorem compileRoleAwareContextualCutOpenEventMorphism_eq_elementary
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : Fin presentation.cut.exterior.eventCount) :
    compileRoleAwareContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event =
      compileContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event :=
  eq_of_heq
    (compileRoleAwareContextualCutOpenEventMorphism_heq_elementary
      𝒞 diagram presentation labeling event)

theorem standardOneTwoBirth_oldContextualMorphism_of_contexts
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.cut.cut.exterior.eventCount)
    (contexts :
      eventLeftContext target.diagram target.cut (standardOneTwoBirthOldEventIndex normalForm event) =
          standardOneTwoBirthOldStrands normalForm
            (eventLeftContext source.diagram source.cut event) ∧
        eventRightContext target.diagram target.cut (standardOneTwoBirthOldEventIndex normalForm event) =
          standardOneTwoBirthOldStrands normalForm
            (eventRightContext source.diagram source.cut event)) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram source.cut sourceLabeling event) := by
  let targetEvent :=
    standardOneTwoBirthOldEventIndex normalForm event
  let sourceEvent :=
    source.cut.cut.exterior.events event
  have targetEventEq :
      target.cut.cut.exterior.events targetEvent =
        standardOneTwoBirthOldEvent normalForm sourceEvent := by
    simpa [targetEvent, sourceEvent,
      standardOneTwoBirthOldEventIndex] using
      standardOneTwoBirth_oldEvent normalForm event
  have leftEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (eventLeftContext target.diagram target.cut targetEvent) =
        exteriorWord 𝒞 source.diagram sourceLabeling
          (eventLeftContext source.diagram source.cut event) :=
    (congrArg
      (exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel))
      contexts.1).trans
      (standardOneTwoBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _)
  have rightEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (eventRightContext target.diagram target.cut targetEvent) =
        exteriorWord 𝒞 source.diagram sourceLabeling
          (eventRightContext source.diagram source.cut event) :=
    (congrArg
      (exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel))
      contexts.2).trans
      (standardOneTwoBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _)
  have beforeEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.cut.cut.exterior.events targetEvent).beforeWord =
        exteriorWord 𝒞 source.diagram sourceLabeling
          sourceEvent.beforeWord := by
    rw [targetEventEq,
      standardOneTwoBirth_oldEventBeforeWord]
    exact
      standardOneTwoBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _
  have afterEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.cut.cut.exterior.events targetEvent).afterWord =
        exteriorWord 𝒞 source.diagram sourceLabeling
          sourceEvent.afterWord := by
    rw [targetEventEq,
      standardOneTwoBirth_oldEventAfterWord]
    exact
      standardOneTwoBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _
  have targetMapEq :
      HEq
        (compileCutOpenEventMorphism 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.cut.cut.exterior.events targetEvent)
          (target.cut.cut.exterior.strandContinuationsAreWellFormed targetEvent))
        (compileCutOpenEventMorphism 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardOneTwoBirthOldEvent normalForm sourceEvent)
          (standardOneTwoBirth_oldEventStrandContinuationsAreWellFormed normalForm
            sourceEvent
            (source.cut.cut.exterior.strandContinuationsAreWellFormed event))) := by
    congr!
  have mapEq :
      HEq
        (compileCutOpenEventMorphism 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.cut.cut.exterior.events targetEvent)
          (target.cut.cut.exterior.strandContinuationsAreWellFormed targetEvent))
        (compileCutOpenEventMorphism 𝒞 source.diagram sourceLabeling
          sourceEvent
          (source.cut.cut.exterior.strandContinuationsAreWellFormed event)) :=
    targetMapEq.trans
      (standardOneTwoBirth_oldEventMorphism
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel sourceEvent
        (source.cut.cut.exterior.strandContinuationsAreWellFormed event))
  exact
    (compileContextualCutOpenEventMorphism_heq_core
      𝒞 target.diagram target.cut
      (coordinates.mergeLabeling sourceLabeling newLabel)
      targetEvent).trans
      ((contextualizeRibbonMorphism_heq
        𝒞 leftEq beforeEq afterEq rightEq mapEq).trans
        (compileContextualCutOpenEventMorphism_heq_core
          𝒞 source.diagram source.cut sourceLabeling event).symm)

theorem standardOneTwoBirth_oldBirthContextualMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.cut.cut.exterior.eventCount)
    (left right : source.diagram.trace.StrandId)
    (eventEq :
      source.cut.cut.exterior.events event =
        .birth left right) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram source.cut sourceLabeling event) := by
  have contexts :=
    standardOneTwoBirth_oldContexts_of_after_nonempty
      normalForm event (by
        rw [eventEq]
        simp [CutOpenEvent.afterWord])
  exact
    standardOneTwoBirth_oldContextualMorphism_of_contexts
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel event contexts

theorem standardOneTwoBirth_oldContextualMorphism_of_before_nonempty
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.cut.cut.exterior.eventCount)
    (beforeNonempty :
      (source.cut.cut.exterior.events event).beforeWord ≠ []) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram source.cut sourceLabeling event) := by
  have contexts :=
    standardOneTwoBirth_oldContexts_of_before_nonempty
      normalForm event beforeNonempty
  exact
    standardOneTwoBirth_oldContextualMorphism_of_contexts
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel event contexts

theorem standardOneTwoBirth_oldContextualMorphism_of_after_nonempty
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.cut.cut.exterior.eventCount)
    (afterNonempty :
      (source.cut.cut.exterior.events event).afterWord ≠ []) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram source.cut sourceLabeling event) := by
  have contexts :=
    standardOneTwoBirth_oldContexts_of_after_nonempty
      normalForm event afterNonempty
  exact
    standardOneTwoBirth_oldContextualMorphism_of_contexts
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel event contexts

theorem contextualizeRibbonMorphism_empty_identity
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : RibbonWord 𝒞) :
    contextualizeRibbonMorphism 𝒞 left [] [] right
      (𝟙 (𝟙_ 𝒞.C)) =
      𝟙 (ribbonWordObject 𝒞
        (List.append (List.append left []) right)) := by
  induction left with
  | nil =>
      simp [contextualizeRibbonMorphism,
        ribbonWordAppendIso, ribbonWordObject]
  | cons strand rest inductionHypothesis =>
      simp [contextualizeRibbonMorphism,
        ribbonWordAppendIso, ribbonWordObject]

theorem tensorUnitProjector_on_empty_word
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    tensorUnitProjector 𝒞
        (ribbonWordObject 𝒞 ([] : RibbonWord 𝒞)) =
      𝟙 (𝟙_ 𝒞.C) := by
  letI : CategoryTheory.Simple (𝟙_ 𝒞.C) :=
    FusionCategory.tensorUnit_simple (K := K)
  change tensorUnitProjector 𝒞 (𝟙_ 𝒞.C) = 𝟙 (𝟙_ 𝒞.C)
  exact
    tensorUnitProjector_eq_identity_of_simple_unit
      𝒞 (𝟙_ 𝒞.C) 𝒞.simples.unitIso.symm

theorem compileContextual_planarNil_heq_identity
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : Fin presentation.cut.exterior.eventCount)
    (eventEq :
      presentation.cut.exterior.events event =
        .planarIsotopy []) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event)
      (𝟙 (ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder event.castSucc)))) := by
  have core :=
    compileContextualCutOpenEventMorphism_heq_core
      𝒞 diagram presentation labeling event
  have coreIdentity :
      HEq
        (contextualizeRibbonMorphism 𝒞
          (exteriorWord 𝒞 diagram labeling
            (eventLeftContext diagram presentation event))
          (exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).beforeWord)
          (exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).afterWord)
          (exteriorWord 𝒞 diagram labeling
            (eventRightContext diagram presentation event))
          (compileCutOpenEventMorphism 𝒞 diagram labeling
            (presentation.cut.exterior.events event)
            (presentation.cut.exterior.strandContinuationsAreWellFormed event)))
        (𝟙 (ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling
                (eventLeftContext diagram presentation event)) [])
            (exteriorWord 𝒞 diagram labeling
              (eventRightContext diagram presentation event))))) := by
    have beforeEmpty :
        exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).beforeWord =
          [] := by
      rw [eventEq]
      rfl
    have afterEmpty :
        exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).afterWord =
          [] := by
      rw [eventEq]
      rfl
    have standardPair :
        (CutOpenEvent.planarIsotopy
          ([] : List (diagram.trace.StrandId × diagram.trace.StrandId))).StrandContinuationsAreWellFormed := by
      simp [CutOpenEvent.StrandContinuationsAreWellFormed]
    have eventMapEq :
        HEq
          (compileCutOpenEventMorphism 𝒞 diagram labeling
            (presentation.cut.exterior.events event)
            (presentation.cut.exterior.strandContinuationsAreWellFormed event))
          (𝟙 (𝟙_ 𝒞.C)) := by
      have toStandard :
          HEq
            (compileCutOpenEventMorphism 𝒞 diagram labeling
              (presentation.cut.exterior.events event)
              (presentation.cut.exterior.strandContinuationsAreWellFormed event))
            (compileCutOpenEventMorphism 𝒞 diagram labeling
              (.planarIsotopy []) standardPair) := by
        congr!
      exact toStandard.trans (HEq.refl _)
    exact
      (contextualizeRibbonMorphism_heq 𝒞
        rfl beforeEmpty afterEmpty rfl eventMapEq).trans
        (heq_of_eq
          (contextualizeRibbonMorphism_empty_identity 𝒞
            (exteriorWord 𝒞 diagram labeling
              (eventLeftContext diagram presentation event))
            (exteriorWord 𝒞 diagram labeling
              (eventRightContext diagram presentation event))))
  have boundaryEq :
      List.append
          (List.append
            (exteriorWord 𝒞 diagram labeling
              (eventLeftContext diagram presentation event)) [])
          (exteriorWord 𝒞 diagram labeling
            (eventRightContext diagram presentation event)) =
        exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder event.castSucc) := by
    have transition := (eventTransitionEquations diagram presentation event).1
    rw [eventEq] at transition
    have mapped :=
      congrArg (exteriorWord 𝒞 diagram labeling) transition.symm
    simpa [CutOpenEvent.beforeWord, exteriorWord,
      List.map_append] using mapped
  exact core.trans (coreIdentity.trans (by congr!))

theorem compileContextual_projectorNil_heq_identity
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : Fin presentation.cut.exterior.eventCount)
    (dotted : diagram.trace.ComponentId)
    (eventEq :
      presentation.cut.exterior.events event =
        .projectorHole dotted []) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 diagram presentation labeling event)
      (𝟙 (ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder event.castSucc)))) := by
  have core :=
    compileContextualCutOpenEventMorphism_heq_core
      𝒞 diagram presentation labeling event
  have coreIdentity :
      HEq
        (contextualizeRibbonMorphism 𝒞
          (exteriorWord 𝒞 diagram labeling
            (eventLeftContext diagram presentation event))
          (exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).beforeWord)
          (exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).afterWord)
          (exteriorWord 𝒞 diagram labeling
            (eventRightContext diagram presentation event))
          (compileCutOpenEventMorphism 𝒞 diagram labeling
            (presentation.cut.exterior.events event)
            (presentation.cut.exterior.strandContinuationsAreWellFormed event)))
        (𝟙 (ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling
                (eventLeftContext diagram presentation event)) [])
            (exteriorWord 𝒞 diagram labeling
              (eventRightContext diagram presentation event))))) := by
    have beforeEmpty :
        exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).beforeWord =
          [] := by
      rw [eventEq]
      rfl
    have afterEmpty :
        exteriorWord 𝒞 diagram labeling
            (presentation.cut.exterior.events event).afterWord =
          [] := by
      rw [eventEq]
      rfl
    have standardPair :
        (CutOpenEvent.projectorHole dotted []).StrandContinuationsAreWellFormed := by
      simp [CutOpenEvent.StrandContinuationsAreWellFormed]
    have eventMapEq :
        HEq
          (compileCutOpenEventMorphism 𝒞 diagram labeling
            (presentation.cut.exterior.events event)
            (presentation.cut.exterior.strandContinuationsAreWellFormed event))
          (𝟙 (𝟙_ 𝒞.C)) := by
      have toStandard :
          HEq
            (compileCutOpenEventMorphism 𝒞 diagram labeling
              (presentation.cut.exterior.events event)
              (presentation.cut.exterior.strandContinuationsAreWellFormed event))
            (compileCutOpenEventMorphism 𝒞 diagram labeling
              (.projectorHole dotted []) standardPair) := by
        congr!
      exact toStandard.trans
        ((compileProjectorHoleMorphism_heq_canonical
          𝒞 diagram presentation labeling dotted [] standardPair).trans
          ((CategoryTheory.comp_eqToHom_heq _ _).trans
            (heq_of_eq (tensorUnitProjector_on_empty_word 𝒞))))
    exact
      (contextualizeRibbonMorphism_heq 𝒞
        rfl beforeEmpty afterEmpty rfl eventMapEq).trans
        (heq_of_eq
          (contextualizeRibbonMorphism_empty_identity 𝒞
            (exteriorWord 𝒞 diagram labeling
              (eventLeftContext diagram presentation event))
            (exteriorWord 𝒞 diagram labeling
              (eventRightContext diagram presentation event))))
  have boundaryEq :
      List.append
          (List.append
            (exteriorWord 𝒞 diagram labeling
              (eventLeftContext diagram presentation event)) [])
          (exteriorWord 𝒞 diagram labeling
            (eventRightContext diagram presentation event)) =
        exteriorWord 𝒞 diagram labeling
          (presentation.cut.exterior.activeOrder event.castSucc) := by
    have transition := (eventTransitionEquations diagram presentation event).1
    rw [eventEq] at transition
    have mapped :=
      congrArg (exteriorWord 𝒞 diagram labeling) transition.symm
    simpa [CutOpenEvent.beforeWord, exteriorWord,
      List.map_append] using mapped
  exact core.trans (coreIdentity.trans (by congr!))

theorem standardOneTwoBirth_oldContextualMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.cut.cut.exterior.eventCount) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardOneTwoBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram source.cut sourceLabeling event) := by
  generalize eventEq :
    source.cut.cut.exterior.events event = sourceEvent
  cases sourceEvent with
  | birth left right =>
      apply standardOneTwoBirth_oldContextualMorphism_of_after_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.afterWord]
  | death left right =>
      apply standardOneTwoBirth_oldContextualMorphism_of_before_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.beforeWord]
  | crossing overInput underInput overOutput underOutput sign =>
      apply standardOneTwoBirth_oldContextualMorphism_of_before_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.beforeWord]
  | framingTwist input output sign =>
      apply standardOneTwoBirth_oldContextualMorphism_of_before_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.beforeWord]
  | planarIsotopy continuations =>
      cases continuations with
      | cons continuation rest =>
          apply standardOneTwoBirth_oldContextualMorphism_of_before_nonempty
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
          rw [eventEq]
          simp [CutOpenEvent.beforeWord]
      | nil =>
          have targetEventEq :=
            standardOneTwoBirth_oldEvent normalForm event
          rw [eventEq] at targetEventEq
          have targetIdentity :=
            compileContextual_planarNil_heq_identity
              𝒞 target.diagram target.cut
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (standardOneTwoBirthOldEventIndex normalForm event)
              targetEventEq
          have sourceIdentity :=
            compileContextual_planarNil_heq_identity
              𝒞 source.diagram source.cut sourceLabeling event eventEq
          have objectEq :
              ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.cut.cut.exterior.activeOrder
                      (standardOneTwoBirthOldEventIndex normalForm event).castSucc)) =
                ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.cut.cut.exterior.activeOrder
                      event.castSucc)) := by
            simpa [standardOneTwoBirthOldEventIndex] using
              congrArg (ribbonWordObject 𝒞)
                (standardOneTwoBirth_oldStateExteriorWord
                  𝒞 coordinates coordinateBinding normalForm
                  sourceLabeling newLabel
                  event.castSucc)
          have identityEq :
              HEq
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.cut.cut.exterior.activeOrder
                      (standardOneTwoBirthOldEventIndex normalForm event).castSucc))))
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.cut.cut.exterior.activeOrder
                      event.castSucc)))) := by
            exact identity_heq_of_object_eq objectEq
          exact targetIdentity.trans (identityEq.trans sourceIdentity.symm)
  | projectorHole dotted punctures =>
      cases punctures with
      | cons puncture rest =>
          apply standardOneTwoBirth_oldContextualMorphism_of_before_nonempty
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
          rw [eventEq]
          simp [CutOpenEvent.beforeWord]
      | nil =>
          have targetEventEq :=
            standardOneTwoBirth_oldEvent normalForm event
          rw [eventEq] at targetEventEq
          have targetIdentity :=
            compileContextual_projectorNil_heq_identity
              𝒞 target.diagram target.cut
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (standardOneTwoBirthOldEventIndex normalForm event)
              (standardOneTwoBirthOldComponent normalForm dotted)
              targetEventEq
          have sourceIdentity :=
            compileContextual_projectorNil_heq_identity
              𝒞 source.diagram source.cut sourceLabeling event dotted eventEq
          have objectEq :
              ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.cut.cut.exterior.activeOrder
                      (standardOneTwoBirthOldEventIndex normalForm event).castSucc)) =
                ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.cut.cut.exterior.activeOrder
                      event.castSucc)) := by
            simpa [standardOneTwoBirthOldEventIndex] using
              congrArg (ribbonWordObject 𝒞)
                (standardOneTwoBirth_oldStateExteriorWord
                  𝒞 coordinates coordinateBinding normalForm
                  sourceLabeling newLabel
                  event.castSucc)
          have identityEq :
              HEq
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.cut.cut.exterior.activeOrder
                      (standardOneTwoBirthOldEventIndex normalForm event).castSucc))))
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.cut.cut.exterior.activeOrder
                      event.castSucc)))) := by
            exact identity_heq_of_object_eq objectEq
          exact targetIdentity.trans (identityEq.trans sourceIdentity.symm)

theorem standardOneTwoBirth_dropThreeTrace_eq_source
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    (standardOneTwoBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree =
      compiledExteriorTrace 𝒞 source.diagram source.cut sourceLabeling := by
  apply FiniteMorphismTrace.eq_of_object_edge
  · intro state
    change
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (target.cut.cut.exterior.activeOrder
              ⟨state.1 + 3, by
                rw [standardOneTwoBirth_eventCount normalForm]
                omega⟩)) =
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 source.diagram sourceLabeling
            (source.cut.cut.exterior.activeOrder state))
    exact congrArg (ribbonWordObject 𝒞)
      (standardOneTwoBirth_oldStateExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel state)
  · intro event
    change HEq
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞 target.diagram target.cut
        (coordinates.mergeLabeling sourceLabeling newLabel)
        ⟨event.1 + 3, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩)
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞 source.diagram source.cut
        sourceLabeling event)
    rw [compileRoleAwareContextualCutOpenEventMorphism_eq_elementary,
      compileRoleAwareContextualCutOpenEventMorphism_eq_elementary]
    simpa [standardOneTwoBirthOldEventIndex] using
      standardOneTwoBirth_oldContextualMorphism
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel event

theorem standardOneTwoBirth_prefixThreeMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : SpecialKirbyDiagram}
    {sourceCut : DottedCutPresentation source}
    {targetCut : DottedCutPresentation target}
    (normalForm : IsStandardOneTwoBirth source target sourceCut targetCut)
    (labeling : TwoHandleLabeling 𝒞 target) :
    HEq
      ((standardOneTwoBirthTargetTrace 𝒞 normalForm labeling).composePrefix
        3 (by omega))
      (specialCutMeridianMorphismWithoutExplicitTwist 𝒞
        (exteriorStrandLabel 𝒞 target labeling
          (oneTwoFirstStrand normalForm))) := by
  have castPrefix :=
    FiniteMorphismTrace.castEventCount_composePrefix
      (standardOneTwoBirth_eventCount normalForm).symm
      (compiledExteriorTrace 𝒞 target targetCut labeling)
      3 (by omega) (by
        rw [standardOneTwoBirth_eventCount normalForm]
        omega)
  obtain ⟨dotted, puncture, eventEq, _dottedValue, serialized⟩ :=
    standardOneTwoBirth_eventOne_exists normalForm
  have localMorphism :=
    standardOneTwoBirth_localThreeEventMorphism
      𝒞 normalForm labeling dotted puncture serialized
      (eventEq ▸
        targetCut.cut.exterior.strandContinuationsAreWellFormed
          (oneTwoEventIndexOne normalForm))
  have first :=
    standardOneTwoBirth_firstContextualEdge
      𝒞 normalForm labeling
  have second :=
    standardOneTwoBirth_secondContextualEdge
      𝒞 normalForm labeling dotted puncture eventEq serialized
  have third :=
    standardOneTwoBirth_thirdContextualEdge
      𝒞 normalForm labeling
  have assembled :=
    congrArg₂ (fun f g => f ≫ g) first
      (congrArg₂ (fun f g => f ≫ g) second third)
  simp only [Category.assoc] at assembled localMorphism
  have assembledValue := assembled.trans localMorphism
  apply castPrefix.trans
  simp only [FiniteMorphismTrace.composePrefix,
    compiledExteriorTrace, Category.id_comp,
    compileRoleAwareContextualCutOpenEventMorphism_eq_elementary]
  apply middle_heq_of_transport_sandwich_eq
  simpa [oneTwoEventIndexZero, oneTwoEventIndexOne,
    oneTwoEventIndexTwo, Category.assoc] using assembledValue

theorem standardOneTwoBirth_targetTraceMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    HEq
      ((standardOneTwoBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).composeAll)
      (oneTwoBirthExpectedTraceMorphism 𝒞 coordinates normalForm
        sourceLabeling newLabel) := by
  have threeBound :
      3 ≤ source.cut.cut.exterior.eventCount + 3 := by
    omega
  have prefixMorphism :
      HEq
        ((standardOneTwoBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)).composePrefix
            3 threeBound)
        (specialCutMeridianMorphismWithoutExplicitTwist 𝒞
          (exteriorStrandLabel 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (oneTwoFirstStrand normalForm))) :=
    standardOneTwoBirth_prefixThreeMorphism
      𝒞 normalForm (coordinates.mergeLabeling sourceLabeling newLabel)
  have tracesEq :
      (standardOneTwoBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree =
          compiledExteriorTrace 𝒞 source.diagram source.cut sourceLabeling :=
    standardOneTwoBirth_dropThreeTrace_eq_source
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel
  have suffixRaw :
      HEq
        ((standardOneTwoBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree.composeAll)
        ((compiledExteriorTrace 𝒞 source.diagram source.cut sourceLabeling).composeAll) := by
    rw [tracesEq]
  have suffix :
      HEq
        ((standardOneTwoBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree.composeAll)
        (compiledExteriorTraceFromUnit
          𝒞 source.diagram source.cut sourceLabeling) :=
    suffixRaw.trans (CategoryTheory.eqToHom_comp_heq _ _).symm
  have sourceObjectEq :
      (standardOneTwoBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).object 0 =
          𝟙_ 𝒞.C := by
    change ribbonWordObject 𝒞
        (exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.cut.cut.exterior.activeOrder 0)) =
      𝟙_ 𝒞.C
    rw [target.cut.cut.exterior.initialBoundaryEmpty]
    rfl
  have middleObjectEq :
      (standardOneTwoBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).object
          ⟨3, by omega⟩ =
        𝟙_ 𝒞.C := by
    change ribbonWordObject 𝒞
        (exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.cut.cut.exterior.activeOrder
            ⟨3, by
              rw [standardOneTwoBirth_eventCount normalForm]
              omega⟩)) =
      𝟙_ 𝒞.C
    have middleWordEq :
        exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (target.cut.cut.exterior.activeOrder
              ⟨3, by
                rw [standardOneTwoBirth_eventCount normalForm]
                omega⟩) =
          exteriorWord 𝒞 source.diagram sourceLabeling
            (source.cut.cut.exterior.activeOrder 0) := by
      simpa using
        (standardOneTwoBirth_oldStateExteriorWord
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel
          (0 : Fin
            (source.cut.cut.exterior.eventCount + 1)))
    rw [middleWordEq]
    rw [source.cut.cut.exterior.initialBoundaryEmpty]
    rfl
  have targetObjectEq :
      (standardOneTwoBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree.object
          (Fin.last source.cut.cut.exterior.eventCount) =
        (compiledExteriorTrace 𝒞 source.diagram source.cut sourceLabeling).object
          (Fin.last source.cut.cut.exterior.eventCount) :=
    congrArg
      (fun trace =>
        trace.object (Fin.last source.cut.cut.exterior.eventCount))
      tracesEq
  exact
    (heq_of_eq
      (FiniteMorphismTrace.composePrefix_add_three
        (eventCount := source.cut.cut.exterior.eventCount)
        (standardOneTwoBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)))).trans
    (CategoryTheory.heq_comp
      sourceObjectEq middleObjectEq targetObjectEq prefixMorphism suffix)

theorem standardOneTwoBirth_compiledExteriorMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : OneTwoGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesCanonicalMeridian)
    (normalForm : IsStandardOneTwoBirth source.diagram target.diagram source.cut target.cut)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    compileCutOpenExteriorMorphism 𝒞 target.diagram target.cut
      (coordinates.mergeLabeling sourceLabeling newLabel) =
      (specialCutMeridianExpression 𝒞 newLabel).interpret ≫
        compileCutOpenExteriorMorphism 𝒞 source.diagram
          source.cut sourceLabeling := by
  have targetClosedToRaw :=
    compileCutOpenExteriorMorphism_heq_compiledTrace
      𝒞 target.diagram target.cut
      (coordinates.mergeLabeling sourceLabeling newLabel)
  have targetRawToStandard :=
    (standardOneTwoBirthTargetTrace_composeAll
      𝒞 normalForm
      (coordinates.mergeLabeling sourceLabeling newLabel)).symm
  have standardToExpected :=
    standardOneTwoBirth_targetTraceMorphism
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel
  have meridianLabel :=
    standardOneTwoBirth_newMeridianLabel
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel
  have localMorphismEq :
      specialCutMeridianMorphismWithoutExplicitTwist 𝒞
          (exteriorStrandLabel 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (oneTwoFirstStrand normalForm)) =
        (specialCutMeridianExpression 𝒞 newLabel).interpret := by
    rw [meridianLabel]
    exact specialCutMeridianMorphismWithoutExplicitTwist_eq 𝒞 newLabel
  have expectedToPublic :
      HEq
        (oneTwoBirthExpectedTraceMorphism 𝒞 coordinates normalForm
          sourceLabeling newLabel)
        ((specialCutMeridianExpression 𝒞 newLabel).interpret ≫
          compiledExteriorTraceFromUnit 𝒞 source.diagram
            source.cut sourceLabeling) := by
    unfold oneTwoBirthExpectedTraceMorphism
    exact CategoryTheory.heq_comp rfl rfl rfl
      (heq_of_eq localMorphismEq) (heq_of_eq rfl)
  have sourceClosedToFromUnit :=
    compileCutOpenExteriorMorphism_heq_fromUnit
      𝒞 source.diagram source.cut sourceLabeling
  have sourceFinalObjectEq :
      (compiledExteriorTrace 𝒞 source.diagram source.cut sourceLabeling).object
          (Fin.last source.cut.cut.exterior.eventCount) =
        𝟙_ 𝒞.C := by
    change ribbonWordObject 𝒞
        (exteriorWord 𝒞 source.diagram sourceLabeling
          (source.cut.cut.exterior.activeOrder
            (Fin.last source.cut.cut.exterior.eventCount))) =
      𝟙_ 𝒞.C
    rw [source.cut.cut.exterior.finalBoundaryEmpty]
    rfl
  have publicFromUnitToClosed :
      HEq
        ((specialCutMeridianExpression 𝒞 newLabel).interpret ≫
          compiledExteriorTraceFromUnit 𝒞 source.diagram
            source.cut sourceLabeling)
        ((specialCutMeridianExpression 𝒞 newLabel).interpret ≫
          compileCutOpenExteriorMorphism 𝒞 source.diagram
            source.cut sourceLabeling) :=
    CategoryTheory.heq_comp rfl rfl sourceFinalObjectEq (heq_of_eq rfl)
      sourceClosedToFromUnit.symm
  exact eq_of_heq
    (targetClosedToRaw.trans
      (targetRawToStandard.trans
        (standardToExpected.trans
          (expectedToPublic.trans publicFromUnitToClosed))))

end TwistedYetter.Kirby.Final.Proofs
