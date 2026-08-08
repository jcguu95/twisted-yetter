module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Pivotal and spherical structures

The definitions follow EGNO, Definitions 4.7.7, 4.7.11, and 4.7.14. Mathlib
provides the chosen duals and their action on morphisms. The monoidal structure
on the double-dual functor is an ambient parameter, following Mathlib's usual
design for monoidal functor structures; a pivotal structure cannot silently
choose a second, incompatible tensorator.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/-- The right double-dual endofunctor `X ↦ X**`. -/
public abbrev rightDoubleDualFunctor : C ⥤ C where
  obj X := (Xᘁ)ᘁ
  map f := (fᘁ)ᘁ
  map_id X := by simp
  map_comp f g := by simp only [comp_rightAdjointMate]

/-- The monoidality condition in EGNO, Definition 4.7.7. -/
def IsPivotalIso [(rightDoubleDualFunctor C).Monoidal]
    (iso : 𝟭 C ≅ rightDoubleDualFunctor C) : Prop :=
  NatTrans.IsMonoidal iso.hom

/-- A pivotal structure in the sense of EGNO, Definition 4.7.7. -/
structure PivotalStructure [(rightDoubleDualFunctor C).Monoidal] where
  iso : 𝟭 C ≅ rightDoubleDualFunctor C
  monoidal : IsPivotalIso C iso

/-- A rigid monoidal category equipped with a pivotal structure. -/
class PivotalCategory [(rightDoubleDualFunctor C).Monoidal] where
  pivotalStructure : PivotalStructure C

variable {C}

/--
Taking the selected right mate twice is conjugation by the pivotal
isomorphism.  This is the basic dual-functor identity used when transporting
simple-object arguments across right duality.
-/
theorem rightAdjointMate_rightAdjointMate
    [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C)
    {X Y : C} (f : X ⟶ Y) :
    (fᘁ)ᘁ =
      pivotal.iso.inv.app X ≫ f ≫ pivotal.iso.hom.app Y := by
  change
    (rightDoubleDualFunctor C).map f =
      pivotal.iso.inv.app X ≫ (𝟭 C).map f ≫ pivotal.iso.hom.app Y
  rw [← cancel_mono (pivotal.iso.inv.app Y)]
  rw [pivotal.iso.inv.naturality]
  have h := congrArg
    (fun q => pivotal.iso.inv.app X ≫ (𝟭 C).map f ≫ q)
    (pivotal.iso.hom_inv_id_app Y)
  simpa only [Category.assoc, Category.comp_id] using h.symm

/-- EGNO left categorical trace, equation (4.8), for `a : X ⟶ X**`. -/
def leftCategoricalTrace {X : C} (a : X ⟶ (Xᘁ)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫
    (a ⊗ₘ 𝟙 (Xᘁ)) ≫
    ε_ (Xᘁ) ((Xᘁ)ᘁ)

/-- The pivotal trace of an endomorphism, as in EGNO equation (8.40). -/
def pivotalTrace [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C)
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftCategoricalTrace (f ≫ pivotal.iso.hom.app X)

/-- The pivotal trace is cyclic: `tr(fg) = tr(gf)`. -/
theorem pivotalTrace_comp_comm [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C)
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    pivotalTrace pivotal (f ≫ g) = pivotalTrace pivotal (g ≫ f) := by
  simp only [pivotalTrace, leftCategoricalTrace, tensorHom_id,
    comp_whiskerRight, Category.assoc]
  have pivotalNaturality :
      g ≫ pivotal.iso.hom.app X =
        pivotal.iso.hom.app Y ≫ (gᘁ)ᘁ := by
    simpa only [Functor.id_map] using pivotal.iso.hom.naturality g
  have pivotalNaturalityWhisker :
      (g ▷ Xᘁ) ≫ (pivotal.iso.hom.app X ▷ Xᘁ) =
        (pivotal.iso.hom.app Y ▷ Xᘁ) ≫ ((gᘁ)ᘁ ▷ Xᘁ) := by
    calc
      _ = (g ≫ pivotal.iso.hom.app X) ▷ Xᘁ :=
        (comp_whiskerRight _ _ _).symm
      _ = (pivotal.iso.hom.app Y ≫ (gᘁ)ᘁ) ▷ Xᘁ :=
        congrArg (fun q => q ▷ Xᘁ) pivotalNaturality
      _ = _ := comp_whiskerRight _ _ _
  have interchangeF :
      (Y ◁ (fᘁ)) ≫ (pivotal.iso.hom.app Y ▷ Xᘁ) =
        (pivotal.iso.hom.app Y ▷ Yᘁ) ≫ ((Yᘁ)ᘁ ◁ (fᘁ)) := by
    exact whisker_exchange (pivotal.iso.hom.app Y) (fᘁ)
  have evaluationG :
      ((gᘁ)ᘁ ▷ Xᘁ) ≫ ε_ Xᘁ Xᘁᘁ =
        ((Yᘁ)ᘁ ◁ (gᘁ)) ≫ ε_ Yᘁ Yᘁᘁ :=
    rightAdjointMate_comp_evaluation (gᘁ)
  have rearrangeComposite :
      (pivotal.iso.hom.app Y ▷ Yᘁ) ≫
          ((Yᘁ)ᘁ ◁ (fᘁ)) ≫ ((Yᘁ)ᘁ ◁ (gᘁ)) =
        (Y ◁ ((g ≫ f)ᘁ)) ≫
          (pivotal.iso.hom.app Y ▷ Yᘁ) := by
    calc
      _ = (pivotal.iso.hom.app Y ▷ Yᘁ) ≫
            ((Yᘁ)ᘁ ◁ ((fᘁ) ≫ (gᘁ))) := by
        rw [whiskerLeft_comp]
      _ = (pivotal.iso.hom.app Y ▷ Yᘁ) ≫
            ((Yᘁ)ᘁ ◁ ((g ≫ f)ᘁ)) := by
        rw [comp_rightAdjointMate]
      _ = _ := (whisker_exchange
        (pivotal.iso.hom.app Y) ((g ≫ f)ᘁ)).symm
  have coevaluationComposite :
      η_ Y Yᘁ ≫ Y ◁ ((g ≫ f)ᘁ) =
        η_ Y Yᘁ ≫ g ▷ Yᘁ ≫ f ▷ Yᘁ := by
    rw [coevaluation_comp_rightAdjointMate, comp_whiskerRight]
  calc
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫
          ((pivotal.iso.hom.app Y ▷ Xᘁ) ≫
            ((gᘁ)ᘁ ▷ Xᘁ)) ≫ ε_ Xᘁ Xᘁᘁ := by
      slice_lhs 3 4 => exact pivotalNaturalityWhisker
      rfl
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫
          pivotal.iso.hom.app Y ▷ Xᘁ ≫
          (gᘁ)ᘁ ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ := by
      simp only [Category.assoc]
    _ = η_ Y Yᘁ ≫ Y ◁ (fᘁ) ≫
          pivotal.iso.hom.app Y ▷ Xᘁ ≫
          (gᘁ)ᘁ ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ := by
      simpa only [← Category.assoc] using congrArg
        (fun q => q ≫ pivotal.iso.hom.app Y ▷ Xᘁ ≫
          (gᘁ)ᘁ ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ)
        (coevaluation_comp_rightAdjointMate f).symm
    _ = η_ Y Yᘁ ≫
          (((pivotal.iso.hom.app Y ▷ Yᘁ) ≫
            ((Yᘁ)ᘁ ◁ (fᘁ))) ≫
            ((gᘁ)ᘁ ▷ Xᘁ)) ≫ ε_ Xᘁ Xᘁᘁ := by
      slice_lhs 2 3 => exact interchangeF
      rfl
    _ = η_ Y Yᘁ ≫ pivotal.iso.hom.app Y ▷ Yᘁ ≫
          (Yᘁ)ᘁ ◁ (fᘁ) ≫
          (gᘁ)ᘁ ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ := by
      simp only [Category.assoc]
    _ = η_ Y Yᘁ ≫ pivotal.iso.hom.app Y ▷ Yᘁ ≫
          (Yᘁ)ᘁ ◁ (fᘁ) ≫
          (Yᘁ)ᘁ ◁ (gᘁ) ≫ ε_ Yᘁ Yᘁᘁ := by
      simpa only [← Category.assoc] using congrArg
        (fun q => η_ Y Yᘁ ≫ pivotal.iso.hom.app Y ▷ Yᘁ ≫
          (Yᘁ)ᘁ ◁ (fᘁ) ≫ q) evaluationG
    _ = η_ Y Yᘁ ≫ Y ◁ ((g ≫ f)ᘁ) ≫
          pivotal.iso.hom.app Y ▷ Yᘁ ≫ ε_ Yᘁ Yᘁᘁ := by
      slice_lhs 2 4 => exact rearrangeComposite
      simp only [Category.assoc]
    _ = _ := by
      simpa only [← Category.assoc] using congrArg
        (fun q => q ≫ pivotal.iso.hom.app Y ▷ Yᘁ ≫ ε_ Yᘁ Yᘁᘁ)
        coevaluationComposite

/-- EGNO, Definition 4.7.11: pivotal dimension. -/
def pivotalDimension [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C) (X : C) :
    𝟙_ C ⟶ 𝟙_ C :=
  leftCategoricalTrace (pivotal.iso.hom.app X)

/--
A spherical structure in the sense of EGNO, Definition 4.7.14:
`dim(X) = dim(X*)` for every object.
-/
structure SphericalStructure [(rightDoubleDualFunctor C).Monoidal]
    extends PivotalStructure C where
  dimension_dual (X : C) :
    pivotalDimension toPivotalStructure X =
      pivotalDimension toPivotalStructure (Xᘁ)

/-- A rigid monoidal category equipped with a spherical structure. -/
class SphericalCategory [(rightDoubleDualFunctor C).Monoidal] where
  sphericalStructure : SphericalStructure (C := C)

end CategoryTheory
