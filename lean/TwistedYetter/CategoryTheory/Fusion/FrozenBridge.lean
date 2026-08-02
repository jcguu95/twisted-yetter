import TwistedYetter.CategoryTheory.Fusion.Basic
import TwistedYetter.Kirby.Final.Semantics.Independent.Algebra

/-!
# Bridge from the frozen evaluator data to the abstract fusion-category API

This file intentionally points in one direction only: the existing
proof-relevant evaluator data must satisfy the independent abstract definition.
The abstract definition does not import or mention the evaluator.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC uS v

section Semisimple

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable (ambient : PremodularAmbient.{uK, uC, v} K)

local instance : Category.{v} ambient.C := ambient.category
local instance : Abelian ambient.C := ambient.abelian
local instance : Linear K ambient.C := ambient.linear
local instance : MonoidalCategory ambient.C := ambient.monoidal
local instance : RigidCategory ambient.C := ambient.rigid
local instance : BraidedCategory ambient.C := ambient.braided
local instance : MonoidalPreadditive ambient.C := ambient.monoidalPreadditive
local instance : MonoidalLinear K ambient.C := ambient.monoidalLinear

variable (data : FusionSemisimpleData.{uK, uC, uS, v} K ambient)

/-- The frozen simple-label list is a finite simple skeleton. -/
def FusionSemisimpleData.toFiniteSimpleSkeleton :
    FiniteSimpleSkeleton (C := ambient.C) where
  SimpleIndex := data.Simple
  simpleFintype := data.simpleFintype
  simpleDecidableEq := data.simpleDecidableEq
  simpleObject := data.simpleObject
  simple_isSimple := data.simple_isSimple
  simple_pairwise := data.simple_pairwise
  simple_complete := data.simple_complete

/-- The frozen inclusion/projection maps give a genuine finite simple decomposition. -/
def FusionSemisimpleData.toFiniteSimpleDecomposition (X : ambient.C) :
    FiniteSimpleDecomposition X where
  SummandIndex := Σ s, Fin (data.multiplicity X s)
  summandFintype := inferInstance
  summandDecidableEq := inferInstance
  summandObject p := data.simpleObject p.1
  summand_isSimple p := data.simple_isSimple p.1
  inclusion := data.summandInclusion X
  projection := data.summandProjection X
  pairing_same p := data.summand_pairing_same X p.1 p.2
  pairing_distinct := by
    rintro ⟨s, i⟩ ⟨t, j⟩ distinct
    by_cases labels : s = t
    · subst t
      apply data.summand_pairing_distinct_copy X s i j
      intro copies
      apply distinct
      subst j
      rfl
    · exact data.summand_pairing_distinct_simple X s t i j labels
  resolution_identity := by
    simpa only [Fintype.sum_sigma] using data.resolution_identity X

/-- The frozen finite semisimple data satisfies the abstract Mathlib-shaped class. -/
@[reducible] def FusionSemisimpleData.toFiniteSemisimpleCategory :
    FiniteSemisimpleCategory.{v, uK, uC, uS} K ambient.C where
  hom_finite := data.hom_finite
  finite_simple_skeleton := ⟨data.toFiniteSimpleSkeleton ambient⟩
  finite_simple_decomposition := fun X =>
    ⟨data.toFiniteSimpleDecomposition ambient X⟩

end Semisimple

section Fusion

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable (𝒞 : PremodularFusionCategory.{uK, uC, uS, v} K)

local instance : Category.{v} 𝒞.C := 𝒞.ambient.category
local instance : Abelian 𝒞.C := 𝒞.ambient.abelian
local instance : Linear K 𝒞.C := 𝒞.ambient.linear
local instance : MonoidalCategory 𝒞.C := 𝒞.ambient.monoidal
local instance : RigidCategory 𝒞.C := 𝒞.ambient.rigid
local instance : BraidedCategory 𝒞.C := 𝒞.ambient.braided
local instance : MonoidalPreadditive 𝒞.C := 𝒞.ambient.monoidalPreadditive
local instance : MonoidalLinear K 𝒞.C := 𝒞.ambient.monoidalLinear

/-- Every frozen premodular category has the underlying abstract fusion category. -/
@[reducible] noncomputable def PremodularFusionCategory.toFusionCategory :
    FusionCategory.{v, uK, uC, uS} K 𝒞.C where
  toFiniteSemisimpleCategory :=
    𝒞.semisimple.toFiniteSemisimpleCategory 𝒞.ambient
  tensorUnit_simple := by
    letI : Simple (𝒞.semisimple.simpleObject 𝒞.semisimple.tensorUnit) :=
      𝒞.semisimple.simple_isSimple 𝒞.semisimple.tensorUnit
    exact Simple.of_iso 𝒞.semisimple.unitIso.symm

end Fusion

end TwistedYetter.Semantics.Independent
