import TwistedYetter.Fusion.EGNORibbon

/-!
# The EGNO canonical pivotal morphism

This module fixes the non-strict form of the Drinfeld morphism from EGNO
equation (8.30), printed page 214. For a ribbon twist `theta`, the candidate
canonical pivotal component is `theta_X` followed by the Drinfeld morphism, as
in EGNO equation (8.35) and Proposition 8.10.12.

The Drinfeld components are proved natural and are assembled into an
isomorphism `id_C ≅ (** )`. The positive double braiding is realized as the
tensorator obtained by crossing to the monoidal opposite and back. Transporting
that monoidal structure across the Drinfeld isomorphism gives the double-dual
tensorator of EGNO equation (8.31). The balancing law then proves that
`theta_X ≫ u_X` is monoidal, yielding the canonical pivotal structure.

Sphericality remains a separate obligation and is not claimed by this module.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite

universe u v

section Monodromy

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/-- The positive double braiding from EGNO equation (8.31). -/
def monodromyHom (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

/-- The definition exposes the order of the two crossings for audits. -/
theorem monodromyHom_eq (X Y : C) :
    monodromyHom X Y = (β_ X Y).hom ≫ (β_ Y X).hom :=
  rfl

/-- Positive double braiding is natural in both tensor factors. -/
@[reassoc]
theorem monodromyHom_naturality {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ monodromyHom X' Y' =
      monodromyHom X Y ≫ (f ⊗ₘ g) := by
  simp [monodromyHom, Category.assoc]

end Monodromy

section MonodromyIdentity

variable {C : Type u} [Category.{v} C]

/--
The identity endofunctor reached by crossing to the monoidal opposite and
back.
-/
def monodromyIdFunctor : C ⥤ C :=
  mopFunctor C ⋙ unmopFunctor C

/-- The underlying endofunctor is definitionally the identity. -/
theorem monodromyIdFunctor_eq :
    monodromyIdFunctor (C := C) = 𝟭 C :=
  rfl

end MonodromyIdentity

section MonodromyMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
The monoidal structure inherited from `mopFunctor ⋙ unmopFunctor`.

Its tensorator is the positive double braiding. This definition is explicit
because typeclass inference could otherwise choose the ordinary identity
tensorator after reducing the underlying functor.
-/
@[implicit_reducible]
def monodromyIdMonoidal : (monodromyIdFunctor (C := C)).Monoidal := by
  unfold monodromyIdFunctor
  exact Functor.Monoidal.instComp (mopFunctor C) (unmopFunctor C)

/-- The inherited tensorator is exactly the positive double braiding. -/
theorem monodromyId_μ (X Y : C) :
    @Functor.LaxMonoidal.μ C _ _ C _ _
        (monodromyIdFunctor (C := C))
        (monodromyIdMonoidal (C := C)).toLaxMonoidal X Y =
      monodromyHom X Y :=
  rfl

/-- The inherited unit map is the identity of the monoidal unit. -/
theorem monodromyId_ε :
    @Functor.LaxMonoidal.ε C _ _ C _ _
        (monodromyIdFunctor (C := C))
        (monodromyIdMonoidal (C := C)).toLaxMonoidal =
      𝟙 (𝟙_ C) := by
  change 𝟙 (𝟙_ C) ≫ (unmopFunctor C).map (𝟙 _) = 𝟙 (𝟙_ C)
  simp

/--
The balancing law and naturality force the twist on the monoidal unit to be
the identity; it is not an extra field of `BalancedTwist`.
-/
theorem balancedTwist_unit (twist : BalancedTwist C) :
    twist.iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  have h := twist.iso.hom.naturality (λ_ (𝟙_ C)).hom
  rw [twist.tensor] at h
  simp only [Functor.id_obj, unitors_equal, Functor.id_map,
    braiding_tensorUnit_right, Category.assoc, Iso.cancel_iso_hom_left] at h
  rw [← unitors_equal] at h
  simp [Category.assoc, MonoidalCategory.tensorHom_def] at h
  simp [← unitors_equal] at h
  simp [unitors_equal] at h
  apply (cancel_epi (twist.iso.hom.app (𝟙_ C))).1
  simpa using h.symm

/-- The balancing law written using the named monodromy morphism. -/
theorem balancedTwist_tensor_monodromy
    (twist : BalancedTwist C) (X Y : C) :
    twist.iso.hom.app (X ⊗ Y) =
      monodromyHom X Y ≫
        (twist.iso.hom.app X ⊗ₘ twist.iso.hom.app Y) := by
  simpa only [monodromyHom, Category.assoc] using twist.tensor X Y

end MonodromyMonoidal

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
The Drinfeld natural isomorphism with the monodromy identity functor exposed
as its source.
-/
def drinfeldMonodromyNatIso :
    monodromyIdFunctor (C := C) ≅ rightDoubleDualFunctor C :=
  drinfeldNatIso

/-- Forward components remain the chosen Drinfeld comparison morphisms. -/
theorem drinfeldMonodromyNatIso_hom_app (X : C) :
    (drinfeldMonodromyNatIso (C := C)).hom.app X =
      (drinfeldIso X).hom :=
  rfl

/-- Inverse components remain the inverse Drinfeld comparisons. -/
theorem drinfeldMonodromyNatIso_inv_app (X : C) :
    (drinfeldMonodromyNatIso (C := C)).inv.app X =
      (drinfeldIso X).inv :=
  rfl

/--
Transport the monodromy monoidal structure across the Drinfeld isomorphism.

This construction obtains coherence from Mathlib's monoidal-opposite functors
and transport theorem; it does not assume the desired pivotal structure.
-/
@[implicit_reducible]
def drinfeldDoubleDualMonoidal :
    (rightDoubleDualFunctor C).Monoidal := by
  letI : (monodromyIdFunctor (C := C)).Monoidal :=
    monodromyIdMonoidal (C := C)
  exact Functor.Monoidal.transport drinfeldMonodromyNatIso

/--
The transported tensorator in explicit non-strict form, corresponding to
EGNO equation (8.31).
-/
theorem drinfeldDoubleDual_μ (X Y : C) :
    @Functor.LaxMonoidal.μ C _ _ C _ _
        (rightDoubleDualFunctor C)
        (drinfeldDoubleDualMonoidal (C := C)).toLaxMonoidal X Y =
      ((drinfeldIso X).inv ⊗ₘ (drinfeldIso Y).inv) ≫
        monodromyHom X Y ≫
        (drinfeldIso (X ⊗ Y)).hom := by
  letI : (monodromyIdFunctor (C := C)).Monoidal :=
    monodromyIdMonoidal (C := C)
  letI : (rightDoubleDualFunctor C).Monoidal :=
    drinfeldDoubleDualMonoidal (C := C)
  change Functor.LaxMonoidal.μ (rightDoubleDualFunctor C) X Y = _
  rw [Functor.Monoidal.transport_μ
    (i := drinfeldMonodromyNatIso (C := C)) X Y]
  rw [monodromyId_μ]
  rw [drinfeldMonodromyNatIso_inv_app,
    drinfeldMonodromyNatIso_inv_app,
    drinfeldMonodromyNatIso_hom_app]
  rfl

/-- The transported unit map is the Drinfeld component at the unit. -/
theorem drinfeldDoubleDual_ε :
    @Functor.LaxMonoidal.ε C _ _ C _ _
        (rightDoubleDualFunctor C)
        (drinfeldDoubleDualMonoidal (C := C)).toLaxMonoidal =
      (drinfeldIso (𝟙_ C)).hom := by
  letI : (monodromyIdFunctor (C := C)).Monoidal :=
    monodromyIdMonoidal (C := C)
  letI : (rightDoubleDualFunctor C).Monoidal :=
    drinfeldDoubleDualMonoidal (C := C)
  change Functor.LaxMonoidal.ε (rightDoubleDualFunctor C) = _
  rw [Functor.Monoidal.transport_ε
    (i := drinfeldMonodromyNatIso (C := C))]
  rw [monodromyId_ε]
  rw [drinfeldMonodromyNatIso_hom_app]
  exact Category.id_comp _

/--
The Drinfeld morphism's monoidal defect is exactly positive monodromy.

This is equation (8.31), expressed using the transported tensorator.
-/
theorem drinfeld_tensor_defect (X Y : C) :
    (drinfeldHom X ⊗ₘ drinfeldHom Y) ≫
        @Functor.LaxMonoidal.μ C _ _ C _ _
          (rightDoubleDualFunctor C)
          (drinfeldDoubleDualMonoidal (C := C)).toLaxMonoidal X Y =
      monodromyHom X Y ≫ drinfeldHom (X ⊗ Y) := by
  rw [drinfeldDoubleDual_μ]
  simp only [drinfeldHom]
  simp

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

/--
The canonical pivotal natural isomorphism is monoidal.

The tensor proof combines four independently named facts: balancing,
monodromy naturality, the Drinfeld tensor defect, and tensor functoriality.
-/
theorem canonicalPivotal_isMonoidal (ribbon : RibbonStructure C) :
    letI := drinfeldDoubleDualMonoidal (C := C)
    NatTrans.IsMonoidal (canonicalPivotalIso ribbon).hom := by
  letI := drinfeldDoubleDualMonoidal (C := C)
  refine { unit := ?_, tensor := ?_ }
  · rw [show Functor.LaxMonoidal.ε (𝟭 C) = 𝟙 (𝟙_ C) from rfl]
    rw [canonicalPivotalIso_hom_app, drinfeldDoubleDual_ε]
    calc
      𝟙 (𝟙_ C) ≫ canonicalPivotalHom ribbon (𝟙_ C) =
          canonicalPivotalHom ribbon (𝟙_ C) := Category.id_comp _
      _ = (drinfeldIso (𝟙_ C)).hom := by
        simp [canonicalPivotalHom, drinfeldHom,
          balancedTwist_unit ribbon.toBalancedTwist]
  · intro X Y
    rw [show Functor.LaxMonoidal.μ (𝟭 C) X Y = 𝟙 (X ⊗ Y) from rfl]
    simp only [canonicalPivotalIso_hom_app]
    simp only [canonicalPivotalHom]
    rw [balancedTwist_tensor_monodromy]
    rw [← monodromyHom_naturality]
    simp only [Functor.id_obj, Category.id_comp]
    rw [Category.assoc]
    rw [← drinfeld_tensor_defect]
    exact
      (Category.assoc
        (ribbon.toBalancedTwist.iso.hom.app X ⊗ₘ
          ribbon.toBalancedTwist.iso.hom.app Y)
        (drinfeldHom X ⊗ₘ drinfeldHom Y)
        (Functor.LaxMonoidal.μ (rightDoubleDualFunctor C) X Y)).symm
        |>.trans
          (congrArg
            (fun k => k ≫
              Functor.LaxMonoidal.μ (rightDoubleDualFunctor C) X Y)
            (MonoidalCategory.tensorHom_comp_tensorHom
              (ribbon.toBalancedTwist.iso.hom.app X)
              (ribbon.toBalancedTwist.iso.hom.app Y)
              (drinfeldHom X) (drinfeldHom Y)))

/-- The canonical pivotal structure determined by a ribbon structure. -/
def canonicalPivotalStructure (ribbon : RibbonStructure C) :
    PivotalStructure C where
  doubleDualMonoidal := drinfeldDoubleDualMonoidal (C := C)
  iso := canonicalPivotalIso ribbon
  monoidal := canonicalPivotal_isMonoidal ribbon

end Drinfeld

end TwistedYetter.Fusion.EGNO
