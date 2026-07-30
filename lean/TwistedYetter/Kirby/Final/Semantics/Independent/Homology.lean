import TwistedYetter.Kirby.Final.Semantics.Independent.Diagram

/-!
# Independent semantics: primal and THAM-side handle homology

The public Kirby terminology in this file is the usual one:

* literal dotted components are primal one-handles;
* ordinary framed components are primal two-handles; and
* the closing data records primal three-handles.

Tham, Definition 5.11 is applied to the handle decomposition turned upside
down.  Thus the evaluator sees primal indices `1, 2, 3` as THAM indices
`3, 2, 1`.  Neither convention is intrinsically preferred.  This file makes
their conversion explicit so that primal cycle coordinates can never be used
silently as THAM-side character exponents.

Reference: Ying Hong Tham, *On the Category of Boundary Values in the extended
Crane-Yetter TQFT* (2021), Definition 5.11 (PDF p. 58) and the dual-handle
application on PDF pp. 99--101.
-/

namespace TwistedYetter.Semantics.Independent

open scoped BigOperators

noncomputable section

abbrev HandleChainGroup (count : ℕ) := Fin count → ℤ

def twoOneIncidence
    (diagram : CombinatorialSpecialKirbyDiagram)
    (one : Fin diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) : ℤ := by
  classical
  let dotted := diagram.handles.oneHandleIndex one
  let twoHandle := diagram.handles.twoHandleIndex two
  exact
    (diagram.dottedCuts.punctureWord dotted.1 dotted.2).foldl
      (fun total puncture =>
        if puncture.twoHandleComponent = twoHandle.1 then
          total + puncture.characterExponentSign
        else
          total)
      0

/-- The primal cellular boundary `C₂ → C₁` in ordinary Kirby terminology. -/
def primalBoundaryTwo
    (diagram : CombinatorialSpecialKirbyDiagram) :
    HandleChainGroup diagram.handles.hTwo →+
      HandleChainGroup diagram.handles.hOne where
  toFun chain one :=
    ∑ two, twoOneIncidence diagram one two * chain two
  map_zero' := by
    funext one
    simp
  map_add' left right := by
    funext one
    simp [mul_add, Finset.sum_add_distrib]

/--
The primal degree-three boundary belongs to the special closing data.  Its
algebraic coherence is the ordinary handle-chain identity `∂₂ ∂₃ = 0`.
-/
structure PrimalDegreeThreeBoundaryData
    (diagram : CombinatorialSpecialKirbyDiagram) where
  boundaryThree :
    HandleChainGroup diagram.handles.hThree →+
      HandleChainGroup diagram.handles.hTwo
  boundary_squared_zero :
    (primalBoundaryTwo diagram).comp boundaryThree = 0

def PrimalTwoCycles
    (diagram : CombinatorialSpecialKirbyDiagram) :=
  (primalBoundaryTwo diagram).ker

def primalBoundaryAsCycle
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : PrimalDegreeThreeBoundaryData diagram) :
    HandleChainGroup diagram.handles.hThree →+ PrimalTwoCycles diagram where
  toFun chain :=
    ⟨degreeThree.boundaryThree chain, by
      change
        ((primalBoundaryTwo diagram).comp degreeThree.boundaryThree) chain = 0
      rw [degreeThree.boundary_squared_zero]
      rfl⟩
  map_zero' := by
    ext
    simp
  map_add' left right := by
    ext
    simp

/-- The ordinary Kirby-side group `ker(∂₂) / im(∂₃)`. -/
abbrev PrimalKirbyH₂
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : PrimalDegreeThreeBoundaryData diagram) :=
  PrimalTwoCycles diagram ⧸ (primalBoundaryAsCycle degreeThree).range

def primalCycleClass
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : PrimalDegreeThreeBoundaryData diagram)
    (cycle : PrimalTwoCycles diagram) :
    PrimalKirbyH₂ degreeThree :=
  QuotientAddGroup.mk cycle

/-- Integral coordinate pairing in a fixed finite handle basis. -/
def coordinatePairing {count : ℕ}
    (left right : HandleChainGroup count) : ℤ :=
  ∑ index, left index * right index

/-- Integral unit vector in a fixed handle basis. -/
def coordinateUnit (count : ℕ) (index coordinate : Fin count) : ℤ :=
  if coordinate = index then 1 else 0

theorem coordinatePairing_unit_left
    (count : ℕ)
    (index : Fin count)
    (vector : HandleChainGroup count) :
    coordinatePairing (coordinateUnit count index) vector = vector index := by
  classical
  simp [coordinatePairing, coordinateUnit, eq_comm]

/--
The transpose of an integral map between the finite handle-coordinate groups.
This is executable finite-basis algebra; no caller supplies the transpose.
-/
def transposeAddHom {sourceCount targetCount : ℕ}
    (map : HandleChainGroup sourceCount →+
      HandleChainGroup targetCount) :
    HandleChainGroup targetCount →+
      HandleChainGroup sourceCount where
  toFun target sourceIndex :=
    coordinatePairing
      (map (coordinateUnit sourceCount sourceIndex))
      target
  map_zero' := by
    funext sourceIndex
    simp [coordinatePairing]
  map_add' left right := by
    funext sourceIndex
    simp [coordinatePairing, mul_add, Finset.sum_add_distrib]

/--
There is no data field here: the turned-over maps are computed below from the
primal maps.  The wrapper keeps the primal source visible in dependent types.
-/
structure TurnedOverBoundaryCertificate
    {diagram : CombinatorialSpecialKirbyDiagram}
    (primal : PrimalDegreeThreeBoundaryData diagram) : Type where
  private mk ::

namespace TurnedOverBoundaryCertificate

/-- The canonical and unique finite-basis turnover certificate. -/
def canonical
    {diagram : CombinatorialSpecialKirbyDiagram}
    (primal : PrimalDegreeThreeBoundaryData diagram) :
    TurnedOverBoundaryCertificate primal :=
  .mk

/-- THAM `∂₂ : C₂ → C₁`, computed as the transpose of primal `∂₃`. -/
def thamBoundaryTwo
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (_ : TurnedOverBoundaryCertificate primal) :
    HandleChainGroup diagram.handles.hTwo →+
      HandleChainGroup diagram.handles.hThree :=
  transposeAddHom primal.boundaryThree

/-- THAM `∂₃ : C₃ → C₂`, computed as the transpose of primal `∂₂`. -/
def thamBoundaryThree
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (_ : TurnedOverBoundaryCertificate primal) :
    HandleChainGroup diagram.handles.hOne →+
      HandleChainGroup diagram.handles.hTwo :=
  transposeAddHom (primalBoundaryTwo diagram)

/--
Finite-basis adjointness for the computed transpose.  This elementary
identity is the only fact needed below to turn primal `∂² = 0` upside down.
-/
theorem transpose_adjoint
    {sourceCount targetCount : ℕ}
    (map : HandleChainGroup sourceCount →+
      HandleChainGroup targetCount)
    (source : HandleChainGroup sourceCount)
    (target : HandleChainGroup targetCount) :
    coordinatePairing (map source) target =
      coordinatePairing source (transposeAddHom map target) := by
  classical
  have source_decomposition :
      source =
        ∑ index, source index • coordinateUnit sourceCount index := by
    funext coordinate
    simp [coordinateUnit]
  have map_source_decomposition :
      map source =
        ∑ index,
          source index • map (coordinateUnit sourceCount index) := by
    calc
      map source =
          map (∑ index,
            source index • coordinateUnit sourceCount index) :=
        congrArg map source_decomposition
      _ = ∑ index,
          source index • map (coordinateUnit sourceCount index) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro index _
        exact map.map_zsmul
          (coordinateUnit sourceCount index) (source index)
  rw [map_source_decomposition]
  simp only [coordinatePairing, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, transposeAddHom]
  change
    (∑ targetIndex,
      (∑ sourceIndex,
        source sourceIndex *
          map (coordinateUnit sourceCount sourceIndex) targetIndex) *
        target targetIndex) =
      ∑ sourceIndex,
        source sourceIndex *
          (∑ targetIndex,
            map (coordinateUnit sourceCount sourceIndex) targetIndex *
              target targetIndex)
  calc
    _ = ∑ targetIndex, ∑ sourceIndex,
          (source sourceIndex *
            map (coordinateUnit sourceCount sourceIndex) targetIndex) *
              target targetIndex := by
        apply Finset.sum_congr rfl
        intro targetIndex _
        rw [Finset.sum_mul]
    _ = ∑ sourceIndex, ∑ targetIndex,
          (source sourceIndex *
            map (coordinateUnit sourceCount sourceIndex) targetIndex) *
              target targetIndex :=
        Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro targetIndex _
      ring

theorem boundaryTwo_is_transpose
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (certificate : TurnedOverBoundaryCertificate primal)
    (threeChain : HandleChainGroup diagram.handles.hThree)
    (twoChain : HandleChainGroup diagram.handles.hTwo) :
    coordinatePairing (primal.boundaryThree threeChain) twoChain =
      coordinatePairing threeChain (certificate.thamBoundaryTwo twoChain) :=
  transpose_adjoint primal.boundaryThree threeChain twoChain

theorem boundaryThree_is_transpose
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (certificate : TurnedOverBoundaryCertificate primal)
    (twoChain : HandleChainGroup diagram.handles.hTwo)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    coordinatePairing (primalBoundaryTwo diagram twoChain) oneChain =
      coordinatePairing twoChain (certificate.thamBoundaryThree oneChain) :=
  transpose_adjoint (primalBoundaryTwo diagram) twoChain oneChain

/-- The THAM-side transposed maps square to zero, proved from primal `∂²=0`. -/
theorem boundary_squared_zero
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (certificate : TurnedOverBoundaryCertificate primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    certificate.thamBoundaryTwo
        (certificate.thamBoundaryThree oneChain) = 0 := by
  funext index
  calc
    certificate.thamBoundaryTwo
          (certificate.thamBoundaryThree oneChain) index =
        coordinatePairing
          (coordinateUnit diagram.handles.hThree index)
          (certificate.thamBoundaryTwo
            (certificate.thamBoundaryThree oneChain)) :=
      (coordinatePairing_unit_left diagram.handles.hThree index _).symm
    _ = coordinatePairing
          (primal.boundaryThree
            (coordinateUnit diagram.handles.hThree index))
          (certificate.thamBoundaryThree oneChain) :=
      (certificate.boundaryTwo_is_transpose
        (coordinateUnit diagram.handles.hThree index)
        (certificate.thamBoundaryThree oneChain)).symm
    _ = coordinatePairing
          (primalBoundaryTwo diagram
            (primal.boundaryThree
              (coordinateUnit diagram.handles.hThree index)))
          oneChain :=
      (certificate.boundaryThree_is_transpose
        (primal.boundaryThree
          (coordinateUnit diagram.handles.hThree index))
        oneChain).symm
    _ = 0 := by
      have chainZero :=
        DFunLike.congr_fun primal.boundary_squared_zero
          (coordinateUnit diagram.handles.hThree index)
      change
        primalBoundaryTwo diagram
            (primal.boundaryThree
              (coordinateUnit diagram.handles.hThree index)) =
          0 at chainZero
      rw [chainZero]
      simp [coordinatePairing]
    _ = (0 : HandleChainGroup diagram.handles.hThree) index := rfl

end TurnedOverBoundaryCertificate

def ThamTwoCycles
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal) :=
  turnedOver.thamBoundaryTwo.ker

def thamBoundaryAsCycle
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal) :
    HandleChainGroup diagram.handles.hOne →+ ThamTwoCycles turnedOver where
  toFun chain :=
    ⟨turnedOver.thamBoundaryThree chain,
      turnedOver.boundary_squared_zero chain⟩
  map_zero' := by
    ext
    simp
  map_add' left right := by
    ext
    simp

/-- The evaluator-side second homology of the turned-over handle complex. -/
abbrev ThamKirbyH₂
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal) :=
  ThamTwoCycles turnedOver ⧸ (thamBoundaryAsCycle turnedOver).range

def thamCycleClass
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal)
    (cycle : ThamTwoCycles turnedOver) :
    ThamKirbyH₂ turnedOver :=
  QuotientAddGroup.mk cycle

/--
The algebraic part of the turnover identification.  Whether this equivalence
is the geometric Poincaré-duality/dual-handle map is deliberately not hidden
as a proof field here; that external topology responsibility is stated
separately in `EntranceAxioms`.
-/
structure TurnoverH₂Identification
    {diagram : CombinatorialSpecialKirbyDiagram}
    {primal : PrimalDegreeThreeBoundaryData diagram}
    (turnedOver : TurnedOverBoundaryCertificate primal) where
  equiv : PrimalKirbyH₂ primal ≃+ ThamKirbyH₂ turnedOver

/--
A marked diagram stores exactly one marking, on the ordinary Kirby/primal
side.  The THAM-side marking is derived from the turnover identification.
-/
structure HomologicallyMarkedDiagram where
  diagram : CombinatorialSpecialKirbyDiagram
  primalBoundary : PrimalDegreeThreeBoundaryData diagram
  turnedOver : TurnedOverBoundaryCertificate primalBoundary
  turnover : TurnoverH₂Identification turnedOver
  alpha : PrimalKirbyH₂ primalBoundary

def HomologicallyMarkedDiagram.thamAlpha
    (marked : HomologicallyMarkedDiagram) :
    ThamKirbyH₂ marked.turnedOver :=
  marked.turnover.equiv marked.alpha

end

end TwistedYetter.Semantics.Independent
-- semantic-freeze-padding: 3956
