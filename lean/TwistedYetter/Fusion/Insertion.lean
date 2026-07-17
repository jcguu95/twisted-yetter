import Mathlib.CategoryTheory.Linear.LinearFunctor
import TwistedYetter.Fusion.FiniteResolution

/-!
# Source-backed fusion insertion

This is the exact categorical identity resolution of Bärenz--Barrett Lemma
2.37.  It is a standard semisimplicity input, kept much smaller than any
sliding diagram.  A linear functor carries the resolution to its image,
proving the algebraic content of Lemma 3.2.
-/

namespace TwistedYetter.Fusion.Insertion

open scoped BigOperators
open CategoryTheory

universe uR uC vC uD vD uS uI

variable {R : Type uR} [CommSemiring R]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable {S : Type uS} [Fintype S]
variable {I : S → Type uI}
variable [∀ s, Fintype (I s)]

/--
A finite simple-channel resolution of one identity morphism.

`projection : T ⟶ simple s` and `inclusion : simple s ⟶ T` follow the
orientation in Lemma 2.37, so their composite is an endomorphism of `T`.
-/
structure IdentityResolution (T : C) where
  simple : S → C
  weight : S → R
  projection : (s : S) → I s → (T ⟶ simple s)
  inclusion : (s : S) → I s → (simple s ⟶ T)
  sound :
    ∑ s, ∑ i : I s,
      weight s • (projection s i ≫ inclusion s i) = 𝟙 T
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 2.37, equations (2.2.5)-(2.2.6), journal page 675"

namespace IdentityResolution

variable {T : C}
variable (resolution : IdentityResolution (R := R) (S := S) (I := I) T)

/-- The inverse-insertion direction is not a second assumption. -/
theorem inverse_sound :
    𝟙 T =
      ∑ s, ∑ i : I s,
        resolution.weight s •
          (resolution.projection s i ≫ resolution.inclusion s i) :=
  resolution.sound.symm

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable (F : C ⥤ D) [F.Additive] [F.Linear R]

/--
The image identity resolution.  This proves Lemma 3.2's algebraic equality
from functoriality and linearity; no separate image-resolution axiom is used.
-/
theorem map_sound :
    ∑ s, ∑ i : I s,
      resolution.weight s •
        (F.map (resolution.projection s i) ≫
          F.map (resolution.inclusion s i)) =
      𝟙 (F.obj T) := by
  calc
    ∑ s, ∑ i : I s,
        resolution.weight s •
          (F.map (resolution.projection s i) ≫
            F.map (resolution.inclusion s i)) =
      F.map
        (∑ s, ∑ i : I s,
          resolution.weight s •
            (resolution.projection s i ≫ resolution.inclusion s i)) := by
      simp
    _ = F.map (𝟙 T) := by rw [resolution.sound]
    _ = 𝟙 (F.obj T) := F.map_id T

/-- Inverse insertion for the image is symmetry of `map_sound`. -/
theorem map_inverse_sound :
    𝟙 (F.obj T) =
      ∑ s, ∑ i : I s,
        resolution.weight s •
          (F.map (resolution.projection s i) ≫
            F.map (resolution.inclusion s i)) :=
  (resolution.map_sound F).symm

end IdentityResolution

end TwistedYetter.Fusion.Insertion
