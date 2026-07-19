import TwistedYetter.Fusion.EGNORibbon

/-!
# The EGNO canonical pivotal morphism

This module fixes the non-strict form of the Drinfeld morphism from EGNO
equation (8.30), printed page 214. For a ribbon twist `theta`, the candidate
canonical pivotal component is `theta_X` followed by the Drinfeld morphism, as
in EGNO equation (8.35) and Proposition 8.10.12.

The Drinfeld components are proved natural and are assembled into an
isomorphism `id_C ≅ (** )`. Monoidality and sphericality remain separate
obligations and are not claimed by this module.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

section Drinfeld

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
The non-strict cup-crossing-cap expansion of EGNO equation (8.30).
-/
def drinfeldExpandedHom (X : C) : X ⟶ (Xᘁ)ᘁ :=
  (ρ_ X).inv ≫
    X ◁ η_ (Xᘁ) ((Xᘁ)ᘁ) ≫
    (α_ X (Xᘁ) ((Xᘁ)ᘁ)).inv ≫
    (β_ X (Xᘁ)).hom ▷ ((Xᘁ)ᘁ) ≫
    ε_ X (Xᘁ) ▷ ((Xᘁ)ᘁ) ≫
    (λ_ ((Xᘁ)ᘁ)).hom

/--
The dual-uniqueness isomorphism underlying the Drinfeld morphism.

Braiding turns `X` into a right dual of `X*`; the chosen `X**` is another
right dual. Mathlib's `rightDualIso` compares exactly these two pairings.
-/
def drinfeldIso (X : C) : X ≅ (Xᘁ)ᘁ :=
  rightDualIso
    (BraidedCategory.exactPairing_swap X (Xᘁ))
    (inferInstance : ExactPairing (Xᘁ) ((Xᘁ)ᘁ))

/--
The Drinfeld morphism as the forward map of the canonical comparison between
the braided-swapped dual `X` and the chosen dual `X**` of `X*`.
-/
def drinfeldHom (X : C) : X ⟶ (Xᘁ)ᘁ :=
  (drinfeldIso X).hom

/--
The dual-uniqueness comparison has `drinfeldHom` as its forward morphism.
-/
theorem drinfeldIso_hom (X : C) :
    (drinfeldIso X).hom = drinfeldHom X :=
  rfl

/--
The abstract dual-uniqueness comparison expands to EGNO equation (8.30).
-/
theorem drinfeldHom_eq_expanded (X : C) :
    drinfeldHom X = drinfeldExpandedHom X := by
  dsimp [drinfeldHom, drinfeldIso, drinfeldExpandedHom, rightDualIso,
    rightAdjointMate, BraidedCategory.exactPairing_swap,
    ExactPairing.evaluation]
  change
    (ρ_ X).inv ≫
          X ◁ η_ (Xᘁ) ((Xᘁ)ᘁ) ≫
          X ◁ (𝟙 (Xᘁ)) ▷ ((Xᘁ)ᘁ) ≫
          (α_ X (Xᘁ) ((Xᘁ)ᘁ)).inv ≫
          (@ExactPairing.evaluation _ _ _ (Xᘁ) X
            (BraidedCategory.exactPairing_swap X (Xᘁ))) ▷ ((Xᘁ)ᘁ) ≫
          (λ_ ((Xᘁ)ᘁ)).hom =
      (ρ_ X).inv ≫
          X ◁ η_ (Xᘁ) ((Xᘁ)ᘁ) ≫
          (α_ X (Xᘁ) ((Xᘁ)ᘁ)).inv ≫
          (β_ X (Xᘁ)).hom ▷ ((Xᘁ)ᘁ) ≫
          ε_ X (Xᘁ) ▷ ((Xᘁ)ᘁ) ≫
          (λ_ ((Xᘁ)ᘁ)).hom
  rw [show
    @ExactPairing.evaluation _ _ _ (Xᘁ) X
        (BraidedCategory.exactPairing_swap X (Xᘁ)) =
      (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) from rfl]
  simp

/--
The cup-crossing-cap expression is natural in `X`.

The proof is the algebraic transcription of sliding `f` through the diagram:
braiding naturality moves it through the crossing, the evaluation mate law
turns it into `f*`, and the coevaluation mate law turns that into `f**`.
-/
theorem drinfeldExpandedHom_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ drinfeldExpandedHom Y =
      drinfeldExpandedHom X ≫ (fᘁ)ᘁ := by
  simp only [drinfeldExpandedHom, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc]
  rw [← whisker_exchange_assoc]
  rw [whiskerRight_tensor_assoc]
  rw [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  slice_lhs 5 6 =>
    rw [← comp_whiskerRight,
      ← rightAdjointMate_comp_evaluation]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  slice_lhs 4 5 =>
    rw [← comp_whiskerRight,
      ← BraidedCategory.braiding_naturality_right]
  simp only [comp_whiskerRight, Category.assoc]
  rw [whisker_assoc]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc]
  rw [← coevaluation_comp_rightAdjointMate]
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange_assoc]
  rw [leftUnitor_naturality]

/-- Naturality of the dual-uniqueness form of the Drinfeld morphism. -/
theorem drinfeldHom_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ drinfeldHom Y = drinfeldHom X ≫ (fᘁ)ᘁ := by
  rw [drinfeldHom_eq_expanded, drinfeldHom_eq_expanded]
  exact drinfeldExpandedHom_naturality f

/--
The canonical Drinfeld natural isomorphism `id_C ≅ (** )`.

Invertibility is supplied objectwise by uniqueness of right duals, while
naturality is the preceding cup-crossing-cap calculation.
-/
def drinfeldNatIso : 𝟭 C ≅ rightDoubleDualFunctor C :=
  NatIso.ofComponents (fun X => drinfeldIso X) (fun f => by
    simpa [drinfeldIso_hom, rightDoubleDualFunctor] using
      drinfeldHom_naturality f)

/--
The objectwise canonical pivotal candidate attached to a ribbon twist.

Composition in Lean is left-to-right, so this is the conventional
`u_X ◦ theta_X` written as `theta_X ≫ u_X`.
-/
def canonicalPivotalHom (ribbon : RibbonStructure C) (X : C) :
    X ⟶ (Xᘁ)ᘁ :=
  ribbon.toBalancedTwist.iso.hom.app X ≫ drinfeldHom X

/-- The composition order is fixed and visible to downstream audits. -/
theorem canonicalPivotalHom_eq (ribbon : RibbonStructure C) (X : C) :
    canonicalPivotalHom ribbon X =
      ribbon.toBalancedTwist.iso.hom.app X ≫ drinfeldHom X :=
  rfl

/--
The canonical pivotal candidate as a natural isomorphism.

This establishes naturality and invertibility, but not yet compatibility with
the monoidal structure on the double-dual functor.
-/
def canonicalPivotalIso (ribbon : RibbonStructure C) :
    𝟭 C ≅ rightDoubleDualFunctor C :=
  ribbon.toBalancedTwist.iso ≪≫ drinfeldNatIso

/-- The natural-isomorphism component is the objectwise EGNO formula. -/
theorem canonicalPivotalIso_hom_app
    (ribbon : RibbonStructure C) (X : C) :
    (canonicalPivotalIso ribbon).hom.app X =
      canonicalPivotalHom ribbon X :=
  rfl

end Drinfeld

end TwistedYetter.Fusion.EGNO
