import TwistedYetter.Kirby.Final.Semantics.Independent.Diagram

/-!
# Independent semantics: H₂ marking

The chain groups are free abelian groups indexed by the special handles.
The two-to-one boundary is read from the signed dotted puncture words.  The
three-to-two boundary is part of the closing data because this semantic layer
does not encode three-handle attaching spheres.
-/

namespace TwistedYetter.Semantics.Independent

def HandleChainGroup (handleCount : ℕ) := Fin handleCount → ℤ

instance (handleCount : ℕ) :
    AddCommGroup (HandleChainGroup handleCount) :=
  Pi.addCommGroup

def twoOneIncidence
    (diagram : CombinatorialSpecialKirbyDiagram)
    (one : Fin diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) : ℤ :=
  let dotted := diagram.handles.oneHandleIndex one
  let ordinary := diagram.handles.twoHandleIndex two
  (diagram.dottedCuts.punctureWord dotted.1 dotted.2).foldl
    (fun total (puncture : DottedPuncture diagram.trace) =>
      if puncture.twoHandleComponent.val = ordinary.1.val then
        total + puncture.characterExponentSign
      else
        total)
    0

def boundaryTwo
    (diagram : CombinatorialSpecialKirbyDiagram) :
    HandleChainGroup diagram.handles.hTwo →+
      HandleChainGroup diagram.handles.hOne where
  toFun chain one :=
    ∑ two, twoOneIncidence diagram one two * chain two
  map_zero' := by
    change
      (fun one =>
        ∑ two, twoOneIncidence diagram one two * (0 : HandleChainGroup _ ) two) =
        0
    funext one
    apply Finset.sum_eq_zero
    intro two _
    have zero_coordinate :
        (0 : HandleChainGroup diagram.handles.hTwo) two = 0 := rfl
    rw [zero_coordinate, mul_zero]
  map_add' left right := by
    change
      (fun one =>
        ∑ two, twoOneIncidence diagram one two * (left two + right two)) =
        (fun one => ∑ two, twoOneIncidence diagram one two * left two) +
        (fun one => ∑ two, twoOneIncidence diagram one two * right two)
    funext one
    simp [mul_add, Finset.sum_add_distrib]

/--
The degree-three boundary map belongs to the special closing data.  Its only
algebraic coherence required here is `∂₂ ∂₃ = 0`.
-/
structure DegreeThreeBoundaryData
    (diagram : CombinatorialSpecialKirbyDiagram) where
  boundaryThree :
    HandleChainGroup diagram.handles.hThree →+
      HandleChainGroup diagram.handles.hTwo
  boundary_squared_zero :
    (boundaryTwo diagram).comp boundaryThree = 0

def TwoCycles
    (diagram : CombinatorialSpecialKirbyDiagram) :=
  (boundaryTwo diagram).ker

def boundaryAsCycle
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : DegreeThreeBoundaryData diagram) :
    HandleChainGroup diagram.handles.hThree →+ TwoCycles diagram where
  toFun chain :=
    ⟨degreeThree.boundaryThree chain, by
      change ((boundaryTwo diagram).comp degreeThree.boundaryThree) chain = 0
      rw [degreeThree.boundary_squared_zero]
      rfl⟩
  map_zero' := by
    ext
    simp
  map_add' left right := by
    ext
    simp

/-- `ker(∂₂) / im(∂₃)`, with no abbreviation to `ℤ`. -/
abbrev KirbyH₂
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : DegreeThreeBoundaryData diagram) :=
  TwoCycles diagram ⧸ (boundaryAsCycle degreeThree).range

def cycleClass
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : DegreeThreeBoundaryData diagram)
    (cycle : TwoCycles diagram) :
    KirbyH₂ degreeThree :=
  QuotientAddGroup.mk cycle

structure HomologicallyMarkedDiagram where
  diagram : CombinatorialSpecialKirbyDiagram
  degreeThree : DegreeThreeBoundaryData diagram
  alpha : KirbyH₂ degreeThree

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 562
