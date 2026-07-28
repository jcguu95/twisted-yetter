import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TwistedYetter.Fusion.EGNOTracePairing

/-!
# Spherical insertion from finite trace-dual bases

Bärenz--Barrett Lemma 2.37 states one global theorem: for every object of a
spherical fusion category and every finite trace-dual basis, the
dimension-weighted simple channels resolve the identity.  This module records
that standard theorem at its natural all-objects boundary and derives the
concrete finite resolutions used by Kirby-colour encircling transport.

The law is not attached to one diagram or one convenient basis.  In
particular, it can be applied after a pairing-preserving mate transport, where
the transported basis need not be the arbitrary basis selected by Mathlib.
-/

namespace TwistedYetter.Fusion.EGNO

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Fusion.Insertion

universe uK uC vC uI

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance braidedRightRigidCategory : RightRigidCategory C :=
  BraidedCategory.rightRigidCategoryOfLeftRigidCategory

/--
The all-objects, all-bases form of the spherical insertion lemma.

The field is precisely Bärenz--Barrett Lemma 2.37.  Quantifying over every
finite index family prevents a caller from proving only the basis used by one
chosen Kirby diagram.
-/
structure SphericalInsertionLaw
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  resolves :
    {I : S → Type uI} →
    [∀ s, Fintype (I s)] →
    [∀ s, DecidableEq (I s)] →
    (X : C) →
    (basis : (s : S) →
      DualBasisData (ι := I s)
        (data.toFusionCategoryData.pivotalTracePerfectPairing
          data.pivotal X (data.simple s))) →
      ∑ s, ∑ i : I s,
        data.quantumDimension s •
          ((basis s).primal i ≫ (basis s).dual i) =
        𝟙 X
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 2.37, equations (2.2.5)-(2.2.6), journal page 675"

namespace RibbonFusionCategoryData

variable (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))

/-- The canonical finite index chosen for a basis of `Hom(X, simple s)`. -/
abbrev InsertionIndex (X : C) (s : S) :=
  Module.Free.ChooseBasisIndex K (X ⟶ data.simple s)

/-- Every canonical insertion index is finite because every Hom space is. -/
noncomputable instance insertionIndexFintype (X : C) (s : S) :
    Fintype (data.InsertionIndex X s) := by
  letI : FiniteDimensional K (X ⟶ data.simple s) :=
    data.toFusionCategoryData.hom_finite X (data.simple s)
  exact Module.Free.ChooseBasisIndex.fintype K (X ⟶ data.simple s)

/--
The canonical trace-dual basis of `Hom(X, simple s)` and
`Hom(simple s, X)`.
-/
noncomputable def insertionDualBasis (X : C) (s : S) :
    DualBasisData (ι := data.InsertionIndex X s)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal X (data.simple s)) := by
  letI : FiniteDimensional K (X ⟶ data.simple s) :=
    data.toFusionCategoryData.hom_finite X (data.simple s)
  exact DualBasisData.ofBasis _
    (Module.Free.chooseBasis K (X ⟶ data.simple s))

/--
The dimension-weighted identity resolution selected canonically from the
category's finite Hom spaces.
-/
noncomputable def sphericalIdentityResolution
    (law : SphericalInsertionLaw data)
    (X : C) :
    IdentityResolution
      (R := K) (S := S) (I := data.InsertionIndex X) X where
  simple := data.simple
  weight := data.quantumDimension
  projection s i := (data.insertionDualBasis X s).primal i
  inclusion s i := (data.insertionDualBasis X s).dual i
  sound := law.resolves X (data.insertionDualBasis X)
  source_ref := law.source_ref
  source_locator := law.source_locator

end RibbonFusionCategoryData

end TwistedYetter.Fusion.EGNO

namespace TwistedYetter.Fusion.FiniteResolution.DualBasisData

universe uK uI

variable {K : Type uK} [Field K]
variable {V : Type*} {W : Type*}
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid W] [Module K W]
variable {forward : PerfectPairing K V W}
variable {backward : PerfectPairing K W V}
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]

/--
Reverse a finite dual basis when the two perfect pairings agree after cyclic
interchange.  This is the exact linear-algebra operation used for inverse
insertion after a mate change.
-/
noncomputable def reversed
    (_cyclic :
      (primal : V) → (dual : W) →
        backward.pair dual primal = forward.pair primal dual)
    (basis : DualBasisData (ι := ι) forward) :
    DualBasisData (ι := ι) backward :=
  DualBasisData.ofBasis backward
    (basis.primal.dualBasis.map forward.toDual.symm)

/-- The primal vector of the reversed basis is the old dual vector. -/
theorem reverse_primal
    (cyclic :
      (primal : V) → (dual : W) →
        backward.pair dual primal = forward.pair primal dual)
    (basis : DualBasisData (ι := ι) forward)
    (i : ι) :
    (basis.reversed cyclic).primal i = basis.dual i := by
  change forward.toDual.symm (basis.primal.dualBasis i) = basis.dual i
  rw [← basis.dual_eq i]
  exact forward.toDual.symm_apply_apply (basis.dual i)

/-- The dual vector of the reversed basis is the old primal vector. -/
theorem reverse_dual
    (cyclic :
      (primal : V) → (dual : W) →
        backward.pair dual primal = forward.pair primal dual)
    (basis : DualBasisData (ι := ι) forward)
    (i : ι) :
    (basis.reversed cyclic).dual i = basis.primal i := by
  apply backward.toDual.injective
  apply (basis.reversed cyclic).primal.ext
  intro j
  change
    backward.pair
        ((basis.reversed cyclic).primal j)
        ((basis.reversed cyclic).dual i) =
      backward.pair
        ((basis.reversed cyclic).primal j)
        (basis.primal i)
  rw [(basis.reversed cyclic).pair_primal_dual]
  rw [basis.reverse_primal cyclic j, cyclic]
  rw [basis.pair_primal_dual]
  simp only [eq_comm]

end TwistedYetter.Fusion.FiniteResolution.DualBasisData
