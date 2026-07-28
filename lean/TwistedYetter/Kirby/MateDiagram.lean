import TwistedYetter.Fusion.FrobeniusLinear
import TwistedYetter.Kirby.CategoricalMovie

/-!
# Visible cup/cap realizations of the Lemma 3.3 mate maps

The two mate coupons in Bärenz--Barrett (3.1.10) are expanded here into
unitors, an explicit pairing cup or cap, an associator, and the original
coupon.  The collapse moves are proved from the definitions of Mathlib's
Frobenius reciprocity equivalences.
-/

namespace TwistedYetter.Kirby.MateDiagram

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.FrobeniusLinear
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalMovie

universe uR u v

variable {R : Type uR} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear R C]

/-- A cup for an explicit exact pairing, without hiding its chosen dual. -/
def pairingCup (Y Y' : C) [ExactPairing Y Y'] :
    Diagram C .unit (.tensor (.atom Y) (.atom Y')) :=
  Diagram.coupon "exact-pairing-coevaluation" (η_ Y Y')

/-- A cap for an explicit exact pairing, without hiding its chosen dual. -/
def pairingCap (Y Y' : C) [ExactPairing Y Y'] :
    Diagram C (.tensor (.atom Y') (.atom Y)) .unit :=
  Diagram.coupon "exact-pairing-evaluation" (ε_ Y Y')

/-- The visible expanded diagram for the forward mate in (3.1.10). -/
noncomputable def mateExpanded
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z]
    (f : Z ⟶ X ⊗ Y') :
    Diagram C (.atom Y) (.tensor (.atom Z') (.atom X)) :=
  let bent :
      Z ⊗ Y ⟶ X :=
    (tensorRightHomEquiv Z Y Y' X).symm f
  Diagram.coupon
      (source := .atom Y)
      (target := .tensor .unit (.atom Y))
      "left-unitor-inverse" (λ_ Y).inv ≫ᵈ
    (pairingCup Z' Z ⊗ᵈ Diagram.identity (.atom Y)) ≫ᵈ
    Diagram.coupon
      (source := .tensor (.tensor (.atom Z') (.atom Z)) (.atom Y))
      (target := .tensor (.atom Z') (.tensor (.atom Z) (.atom Y)))
      "associator"
      (α_ Z' Z Y).hom ≫ᵈ
    (Diagram.identity (.atom Z') ⊗ᵈ
      Diagram.coupon
        (source := .tensor (.atom Z) (.atom Y))
        (target := .atom X)
        "right-bent-source-coupon" bent)

/-- The single coupon carrying the concrete forward mate map. -/
noncomputable def mateCoupon
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z]
    (f : Z ⟶ X ⊗ Y') :
    Diagram C (.atom Y) (.tensor (.atom Z') (.atom X)) :=
  Diagram.coupon "mate(f)"
    (mateLinearEquiv (R := R) X Y Y' Z Z' f)

/-- Evaluation of the expanded forward mate is the concrete mate morphism. -/
theorem mateExpanded_sound
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z]
    (f : Z ⟶ X ⊗ Y') :
    Diagram.eval C (mateExpanded X Y Y' Z Z' f) =
      Diagram.eval C (mateCoupon (R := R) X Y Y' Z Z' f) := by
  simp only [mateExpanded, mateCoupon, pairingCup, Diagram.eval,
    mateLinearEquiv_apply, Boundary.denote]
  simp [tensorHom_def, tensorLeftHomEquiv]

/-- The visible expanded diagram for the oppositely oriented mate. -/
noncomputable def dualMateExpanded
    (X Y Y' Z Z' : C)
    [ExactPairing Y' Y] [ExactPairing Z Z']
    (g : X ⊗ Y' ⟶ Z) :
    Diagram C (.tensor (.atom Z') (.atom X)) (.atom Y) :=
  let bent :
      X ⟶ Z ⊗ Y :=
    tensorRightHomEquiv X Y' Y Z g
  (Diagram.identity (.atom Z') ⊗ᵈ
      Diagram.coupon
        (source := .atom X)
        (target := .tensor (.atom Z) (.atom Y))
        "right-bent-dual-coupon" bent) ≫ᵈ
    Diagram.coupon
      (source := .tensor (.atom Z') (.tensor (.atom Z) (.atom Y)))
      (target := .tensor (.tensor (.atom Z') (.atom Z)) (.atom Y))
      "associator-inverse"
      (α_ Z' Z Y).inv ≫ᵈ
    (pairingCap Z Z' ⊗ᵈ Diagram.identity (.atom Y)) ≫ᵈ
    Diagram.coupon
      (source := .tensor .unit (.atom Y))
      (target := .atom Y)
      "left-unitor" (λ_ Y).hom

/-- The single coupon carrying the concrete opposite mate map. -/
noncomputable def dualMateCoupon
    (X Y Y' Z Z' : C)
    [ExactPairing Y' Y] [ExactPairing Z Z']
    (g : X ⊗ Y' ⟶ Z) :
    Diagram C (.tensor (.atom Z') (.atom X)) (.atom Y) :=
  Diagram.coupon "dual-mate(g)"
    (dualMateLinearEquiv (R := R) X Y Y' Z Z' g)

/-- Evaluation of the expanded opposite mate is its concrete mate morphism. -/
theorem dualMateExpanded_sound
    (X Y Y' Z Z' : C)
    [ExactPairing Y' Y] [ExactPairing Z Z']
    (g : X ⊗ Y' ⟶ Z) :
    Diagram.eval C (dualMateExpanded X Y Y' Z Z' g) =
      Diagram.eval C (dualMateCoupon (R := R) X Y Y' Z Z' g) := by
  simp only [dualMateExpanded, dualMateCoupon, pairingCap, Diagram.eval,
    dualMateLinearEquiv_apply, Boundary.denote]
  simp [tensorHom_def, tensorLeftHomEquiv]

/-- The forward mate replacement as one certified local movie. -/
noncomputable def mateCollapseMovie
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z]
    (f : Z ⟶ X ⊗ Y') :
    Movie
      (mateExpanded X Y Y' Z Z' f)
      (mateCoupon (R := R) X Y Y' Z Z' f) :=
  Movie.one
    { label := "kirby-encircling-forward-mate-collapse"
      sound := mateExpanded_sound (R := R) X Y Y' Z Z' f }

/-- The opposite mate replacement as one certified local movie. -/
noncomputable def dualMateCollapseMovie
    (X Y Y' Z Z' : C)
    [ExactPairing Y' Y] [ExactPairing Z Z']
    (g : X ⊗ Y' ⟶ Z) :
    Movie
      (dualMateExpanded X Y Y' Z Z' g)
      (dualMateCoupon (R := R) X Y Y' Z Z' g) :=
  Movie.one
    { label := "kirby-encircling-opposite-mate-collapse"
      sound := dualMateExpanded_sound (R := R) X Y Y' Z Z' g }

end TwistedYetter.Kirby.MateDiagram
