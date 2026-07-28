import TwistedYetter.Kirby.ComponentBoundaryCharacter
import TwistedYetter.Kirby.ComponentDottedEncircling

/-!
# Reindexing signed puncture products

This file proves the finite combinatorial step that must not be hidden in a
Kirby-colour calculation.  If every component ID in an oriented puncture word
is resolved by one finite registry, then the product over puncture occurrences
equals the product over the complete registry with exponent equal to signed
multiplicity.  Missing, duplicate, or unindexed IDs therefore cannot silently
drop out of the sum.
-/

namespace TwistedYetter.Kirby.ComponentBoundarySignedProduct

open scoped BigOperators
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.ComponentDottedEncircling
open TwistedYetter.Kirby.ComponentRibbonDiagram

universe uG uI uK uC vC

/-- Product contributed by every oriented occurrence in a boundary word. -/
def signedProduct
    {G : Type uG} [CommGroup G]
    (value : String → G)
    (coefficient : ℤ) : ComponentBoundary → G
  | .unit => 1
  | .atom component =>
      match component.orientation with
      | .positive => value component.componentId ^ coefficient
      | .negative => value component.componentId ^ (-coefficient)
  | .tensor left right =>
      signedProduct value coefficient left *
        signedProduct value coefficient right

/-- Distinct registry indices have distinct pinned IDs. -/
theorem registry_id_injective
    {I : Type uI} [Fintype I] [DecidableEq I]
    (indexOf : String → Option I)
    (idOf : I → String)
    (roundtrip : (index : I) → indexOf (idOf index) = some index) :
    Function.Injective idOf := by
  intro left right idEq
  have optionEq : (some left : Option I) = some right := by
    calc
      some left = indexOf (idOf left) := (roundtrip left).symm
      _ = indexOf (idOf right) := congrArg indexOf idEq
      _ = some right := roundtrip right
  exact Option.some.inj optionEq

/--
Reindex the occurrence product by a complete finite component registry.

`allIndexed` is intentionally explicit: it is the fail-closed check that no
puncture ID is absent from the denominator.
-/
theorem signedProduct_eq_indexedProduct
    {G : Type uG} [CommGroup G]
    {I : Type uI} [Fintype I] [DecidableEq I]
    (value : String → G)
    (coefficient : ℤ)
    (indexOf : String → Option I)
    (idOf : I → String)
    (roundtrip : (index : I) → indexOf (idOf index) = some index)
    (sound :
      (componentId : String) → (index : I) →
        indexOf componentId = some index → componentId = idOf index)
    (boundary : ComponentBoundary)
    (allIndexed :
      (componentId : String) →
        componentId ∈ boundary.componentIds →
          ∃ index, indexOf componentId = some index) :
    signedProduct value coefficient boundary =
      ∏ index,
        value (idOf index) ^
          (signedMultiplicity (idOf index) boundary * coefficient) := by
  induction boundary with
  | unit =>
      simp [signedProduct, signedMultiplicity]
  | atom component =>
      cases component with
      | mk componentId orientation =>
          obtain ⟨selected, selectedIndex⟩ :=
            allIndexed componentId (by simp [ComponentBoundary.componentIds])
          have selectedId : componentId = idOf selected :=
            sound componentId selected selectedIndex
          subst componentId
          have idsInjective := registry_id_injective indexOf idOf roundtrip
          cases orientation with
          | positive =>
              symm
              rw [Finset.prod_eq_single selected]
              · simp [signedProduct, signedMultiplicity]
              · intro other _ otherNe
                have idNe : idOf selected ≠ idOf other := by
                  intro idEq
                  exact otherNe (idsInjective idEq).symm
                simp [signedMultiplicity, idNe]
              · simp
          | negative =>
              symm
              rw [Finset.prod_eq_single selected]
              · simp [signedProduct, signedMultiplicity]
              · intro other _ otherNe
                have idNe : idOf selected ≠ idOf other := by
                  intro idEq
                  exact otherNe (idsInjective idEq).symm
                simp [signedMultiplicity, idNe]
              · simp
  | tensor left right leftIH rightIH =>
      have leftIndexed :
          (componentId : String) →
            componentId ∈ left.componentIds →
              ∃ index, indexOf componentId = some index := by
        intro componentId membership
        exact allIndexed componentId (by
          simp only [ComponentBoundary.componentIds, List.mem_append]
          exact Or.inl membership)
      have rightIndexed :
          (componentId : String) →
            componentId ∈ right.componentIds →
              ∃ index, indexOf componentId = some index := by
        intro componentId membership
        exact allIndexed componentId (by
          simp only [ComponentBoundary.componentIds, List.mem_append]
          exact Or.inr membership)
      rw [signedProduct, leftIH leftIndexed, rightIH rightIndexed]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro index _
      rw [← zpow_add]
      congr 1
      simp only [signedMultiplicity]
      ring

section CategoryCharacter

open TwistedYetter.Fusion.EGNO

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [CategoryTheory.Category.{vC} C] [CategoryTheory.Abelian C]
variable [CategoryTheory.Linear K C]
variable [CategoryTheory.MonoidalCategory C] [CategoryTheory.RigidCategory C]
variable [CategoryTheory.BraidedCategory C]
variable [CategoryTheory.MonoidalPreadditive C]
variable [CategoryTheory.MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The categorical boundary character is exactly the abstract signed product. -/
theorem boundaryCharacterPower_eq_signedProduct
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (boundary : ComponentBoundary)
    (coefficient : ℤ) :
    boundaryCharacterPower data automorphism labelOf boundary coefficient =
      signedProduct
        (fun componentId =>
          data.automorphismSimpleUnit automorphism (labelOf componentId))
        coefficient boundary := by
  induction boundary with
  | unit =>
      simp [signedProduct]
  | atom component =>
      cases component with
      | mk componentId orientation =>
          cases orientation <;>
            simp [signedProduct, boundaryCharacterPower,
              boundaryCharacterUnit, FusionCategoryData.automorphismScalarPower]
  | tensor left right leftIH rightIH =>
      simp [signedProduct, leftIH, rightIH]

end CategoryCharacter

/-- Machine-visible result: finite denominator reindexing is proved. -/
def currentStatus : String :=
  "PASS_SIGNED_PUNCTURE_PRODUCT_REINDEXED_OVER_COMPLETE_REGISTRY"

end TwistedYetter.Kirby.ComponentBoundarySignedProduct
