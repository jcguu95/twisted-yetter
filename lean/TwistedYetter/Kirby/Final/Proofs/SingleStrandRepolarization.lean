import TwistedYetter.Kirby.Final.Proofs.UnitProjectorFactorization

/-!
# Single-strand rigidity re-polarization

These are the two Hom-set equivalences needed when a physically dual strand
is exposed as a component-colour boundary.  They use only rigidity and the
unitors.  Dotted-disk incidence does not occur in either definition.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- Frobenius reciprocity in the form `Hom(Xᘁ, 𝟙) ≃ Hom(𝟙, X)`. -/
noncomputable def rightDualCovectorEquivVector
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C) :
    (Xᘁ ⟶ 𝟙_ 𝒸.C) ≃ (𝟙_ 𝒸.C ⟶ X) :=
  ((ρ_ (Xᘁ)).symm.homCongr (Iso.refl (𝟙_ 𝒸.C))).trans
    ((tensorLeftHomEquiv (𝟙_ 𝒸.C) X Xᘁ (𝟙_ 𝒸.C)).trans
      ((Iso.refl (𝟙_ 𝒸.C)).homCongr (ρ_ X)))

/-- Frobenius reciprocity in the form `Hom(𝟙, Xᘁ) ≃ Hom(X, 𝟙)`. -/
noncomputable def rightDualVectorEquivCovector
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C) :
    (𝟙_ 𝒸.C ⟶ Xᘁ) ≃ (X ⟶ 𝟙_ 𝒸.C) :=
  ((Iso.refl (𝟙_ 𝒸.C)).homCongr (λ_ Xᘁ).symm).trans
    ((tensorRightHomEquiv
      (𝟙_ 𝒸.C) X Xᘁ (𝟙_ 𝒸.C)).symm.trans
      ((λ_ X).homCongr (Iso.refl (𝟙_ 𝒸.C))))

theorem rightDualCovectorEquivVector_roundTrip
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (f : Xᘁ ⟶ 𝟙_ 𝒸.C) :
    (rightDualCovectorEquivVector 𝒸 X).symm
        (rightDualCovectorEquivVector 𝒸 X f) = f :=
  (rightDualCovectorEquivVector 𝒸 X).symm_apply_apply f

theorem rightDualVectorEquivCovector_roundTrip
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (f : 𝟙_ 𝒸.C ⟶ Xᘁ) :
    (rightDualVectorEquivCovector 𝒸 X).symm
        (rightDualVectorEquivCovector 𝒸 X f) = f :=
  (rightDualVectorEquivCovector 𝒸 X).symm_apply_apply f

end

end TwistedYetter.Kirby.Final.Proofs
