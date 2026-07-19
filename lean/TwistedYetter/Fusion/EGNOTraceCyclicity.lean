import TwistedYetter.Fusion.EGNOCanonicalSpherical

/-!
# Cyclicity of the EGNO pivotal trace

This module proves the cut-moving identity directly from pivotal naturality
and the mate identities for the chosen right duals.  The proof is the
two-morphism form of EGNO Proposition 4.7.3(4), printed page 74.

Sphericality is not needed for cyclicity itself.  It enters downstream because
the Kirby evaluator uses the canonical spherical structure supplied by a
ribbon category.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

section Pivotal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/--
The pivotal trace is cyclic: cutting a closed coupon composite before `f` or
before `g` gives the same scalar.

The proof moves `f` across the cup as `f*`, then across the cap as `f**`.
Naturality of the pivotal isomorphism identifies
`a_X ≫ f**` with `f ≫ a_Y`.
-/
theorem pivotalTrace_cyclic
    (pivotal : PivotalStructure C)
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    pivotalTrace pivotal (f ≫ g) =
      pivotalTrace pivotal (g ≫ f) := by
  simp only [pivotalTrace, leftCategoricalTrace]
  let aX : X ⟶ (Xᘁ)ᘁ := pivotal.iso.hom.app X
  let aY : Y ⟶ (Yᘁ)ᘁ := pivotal.iso.hom.app Y
  change
    η_ X (Xᘁ) ≫ (((f ≫ g) ≫ aX) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      η_ Y (Yᘁ) ≫ (((g ≫ f) ≫ aY) ⊗ₘ 𝟙 (Yᘁ)) ≫
        ε_ (Yᘁ) ((Yᘁ)ᘁ)
  have hSplitF :
      (((f ≫ g) ≫ aX) ⊗ₘ 𝟙 (Xᘁ)) =
        (f ⊗ₘ 𝟙 (Xᘁ)) ≫
          ((g ≫ aX) ⊗ₘ 𝟙 (Xᘁ)) := by
    simpa only [Category.assoc, Category.comp_id] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        f (𝟙 (Xᘁ)) (g ≫ aX) (𝟙 (Xᘁ))).symm
  rw [hSplitF]
  simp only [Category.assoc]
  rw [tensorHom_id]
  rw [← coevaluation_comp_rightAdjointMate_assoc f]
  rw [← id_tensorHom]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, Category.comp_id]
  have hSplitDual :
      ((g ≫ aX) ⊗ₘ fᘁ) =
        ((g ≫ aX) ⊗ₘ 𝟙 (Yᘁ)) ≫
          (𝟙 ((Xᘁ)ᘁ) ⊗ₘ fᘁ) := by
    simpa only [Category.comp_id, Category.id_comp] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        (g ≫ aX) (𝟙 (Yᘁ)) (𝟙 ((Xᘁ)ᘁ)) (fᘁ)).symm
  rw [hSplitDual]
  simp only [Category.assoc]
  rw [id_tensorHom]
  rw [← rightAdjointMate_comp_evaluation (fᘁ)]
  rw [← tensorHom_id]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]
  have hNatural :
      aX ≫ (fᘁ)ᘁ = f ≫ aY := by
    simpa only [aX, aY, Functor.id_map, rightDoubleDualFunctor] using
      (pivotal.iso.hom.naturality f).symm
  have hComposite :
      (g ≫ aX) ≫ (fᘁ)ᘁ = (g ≫ f) ≫ aY := by
    simp only [Category.assoc]
    rw [hNatural]
  have hCompositeAssoc :
      g ≫ aX ≫ (fᘁ)ᘁ = g ≫ f ≫ aY := by
    simpa only [Category.assoc] using hComposite
  slice_lhs 2 2 =>
    exact hCompositeAssoc

/--
Every spherical structure supplies the operational trace law used by the
Kirby cut-independence layer.  No extra theorem-valued field is requested from
the caller.
-/
def sphericalTraceLaws
    (spherical : SphericalStructure (C := C)) :
    SphericalTraceLaws spherical where
  cyclic := pivotalTrace_cyclic spherical.toPivotalStructure
  source_ref := "ref:egno-tensor-categories-2015"
  source_locator := "Proposition 4.7.3(4), printed page 74"

end Pivotal

section Ribbon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
A ribbon structure supplies both the canonical spherical structure and the
proved cut-moving trace law.
-/
def canonicalSphericalTraceLaws
    (ribbon : RibbonStructure C) :
    SphericalTraceLaws (canonicalSphericalStructure ribbon) :=
  sphericalTraceLaws (canonicalSphericalStructure ribbon)

end Ribbon

end TwistedYetter.Fusion.EGNO
