import TwistedYetter.Kirby.Final.Semantics.FramedIsotopy
import TwistedYetter.Kirby.Final.Semantics.CancellationMoves

/-!
# Exhaustive semantic move assembly

The eight geometric constructors, induced H₂ transport, and exact move count.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

universe uH

/--
The exact eight-case geometric language, before attaching homology transport.
-/
inductive MoveGeometry
    {H₂ : Type uH} [AddCommGroup H₂] :
    Presentation H₂ → Presentation H₂ → Type (max 1 uH)
  | framedIsotopy {source target}
      (geometry : FramedIsotopy source target) :
      MoveGeometry source target
  | oneOverOne {source target}
      (geometry : OneOverOne source target) :
      MoveGeometry source target
  | twoOverOne {source target}
      (geometry : TwoOverOne source target) :
      MoveGeometry source target
  | twoOverTwo {source target}
      (geometry : TwoOverTwo source target) :
      MoveGeometry source target
  | oneTwoBirth {source target}
      (geometry : OneTwoBirth source target) :
      MoveGeometry source target
  | oneTwoDeath {source target}
      (geometry : OneTwoDeath source target) :
      MoveGeometry source target
  | twoThreeBirth {source target}
      (geometry : TwoThreeBirth source target) :
      MoveGeometry source target
  | twoThreeDeath {source target}
      (geometry : TwoThreeDeath source target) :
      MoveGeometry source target

/--
Trusted topology boundary: the displayed chain homotopy equivalence is the
one induced by this exact geometric move.

This proposition does not manufacture a map.  The full chain equivalence is
already present in `MarkingTransport`; the proposition only forbids pairing a
move with an unrelated equivalence that happens to act trivially on `H₂`.
-/
axiom IsInducedHandleChainTransport
    {H₂ : Type uH} [AddCommGroup H₂]
    {source target : Presentation H₂}
    (geometry : MoveGeometry source target)
    (transport : MarkingTransport source target) :
    Prop

/--
One exact elementary Kirby move.

Every value contains literal source/target geometry, an actual chain-level
transport whose displayed `H₂` square is fixed, and a certification that this
transport is induced by that geometry.  No evaluator equality appears here.
-/
structure ElementaryMove
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  geometry : MoveGeometry source target
  marking : MarkingTransport source target
  marking_is_induced :
    IsInducedHandleChainTransport geometry marking

/--
The machine-visible move denominator.

Unlike a separate list of names, this inductive type is used by the
projection from `ElementaryMove`; the advertised count therefore cannot
silently drift away from the actual case split.
-/
inductive MoveKind
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving Repr, BEq, DecidableEq

instance : Fintype MoveKind where
  elems :=
    {
      .framedIsotopy,
      .oneOverOne,
      .twoOverOne,
      .twoOverTwo,
      .oneTwoBirth,
      .oneTwoDeath,
      .twoThreeBirth,
      .twoThreeDeath
    }
  complete := by
    intro kind
    cases kind <;> simp

namespace MoveKind

/-- Stable human-readable name of one exact move kind. -/
def name : MoveKind → String
  | .framedIsotopy => "framed-isotopy"
  | .oneOverOne => "one-over-one"
  | .twoOverOne => "two-over-one"
  | .twoOverTwo => "two-over-two"
  | .oneTwoBirth => "one-two-birth"
  | .oneTwoDeath => "one-two-death"
  | .twoThreeBirth => "two-three-birth"
  | .twoThreeDeath => "two-three-death"

end MoveKind

namespace ElementaryMove

/-- Every exact constructor has one definitionally fixed kind. -/
def kind
    {H₂ : Type uH} [AddCommGroup H₂]
    {source target : Presentation H₂} :
    ElementaryMove source target → MoveKind
  | ⟨.framedIsotopy .., _, _⟩ => .framedIsotopy
  | ⟨.oneOverOne .., _, _⟩ => .oneOverOne
  | ⟨.twoOverOne .., _, _⟩ => .twoOverOne
  | ⟨.twoOverTwo .., _, _⟩ => .twoOverTwo
  | ⟨.oneTwoBirth .., _, _⟩ => .oneTwoBirth
  | ⟨.oneTwoDeath .., _, _⟩ => .oneTwoDeath
  | ⟨.twoThreeBirth .., _, _⟩ => .twoThreeBirth
  | ⟨.twoThreeDeath .., _, _⟩ => .twoThreeDeath

end ElementaryMove

theorem move_kind_count : Fintype.card MoveKind = 8 := by
  decide

end TwistedYetter.Kirby.Final.SemanticEightMoves

