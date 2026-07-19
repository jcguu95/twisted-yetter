import TwistedYetter.Fusion.EGNOTensorAutomorphism
import TwistedYetter.Kirby.LinearDiagram

/-!
# EGNO-bound Kirby-colour expansions

For a ribbon fusion category, the ordinary Kirby colour is the formal finite
family

`Ω = sum_s dim(s) · s`.

Given a monoidal natural automorphism of the identity and an integral
coordinate `n`, the homologically twisted family is

`Ω_n = sum_s dim(s) · χ_s^n · s`,

where `χ_s` is not a caller-supplied character table.  It is the unit scalar
derived by Schur's lemma from the actual categorical automorphism.

The family remains formal.  It is evaluated as a finite linear combination
of complete diagrams and is never presented as a nonexistent direct-sum
object with scalar multiplicities.
-/

namespace TwistedYetter.Kirby.EGNOKirbyColorExpansion

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.LinearDiagram

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The ordinary Kirby colour, with coefficients forced to be quantum dimensions. -/
noncomputable def ordinary
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) :
    WeightedFamily K S C where
  item := data.simple
  weight := data.quantumDimension

/--
The integral-character Kirby colour at one exponent.

Both factors in the coefficient are derived from `data` and the categorical
automorphism.
-/
noncomputable def integralCharacter
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    WeightedFamily K S C where
  item := data.simple
  weight := fun s =>
    data.quantumDimension s *
      data.toFusionCategoryData.automorphismScalarPower
        automorphism s exponent

@[simp]
theorem ordinary_item
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (s : S) :
    (ordinary data).item s = data.simple s :=
  rfl

@[simp]
theorem ordinary_weight
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (s : S) :
    (ordinary data).weight s = data.quantumDimension s :=
  rfl

@[simp]
theorem integralCharacter_item
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ)
    (s : S) :
    (integralCharacter data automorphism exponent).item s =
      data.simple s :=
  rfl

@[simp]
theorem integralCharacter_weight
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ)
    (s : S) :
    (integralCharacter data automorphism exponent).weight s =
      data.quantumDimension s *
        data.toFusionCategoryData.automorphismScalarPower
          automorphism s exponent :=
  rfl

/-- Exponent zero is exactly the ordinary Kirby colour. -/
theorem integralCharacter_zero
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    integralCharacter data automorphism 0 = ordinary data := by
  apply congrArg (WeightedFamily.mk data.simple)
  funext s
  simp [integralCharacter, ordinary]

/-- The identity automorphism gives the ordinary colour for every exponent. -/
theorem integralCharacter_identity
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (exponent : ℤ) :
    integralCharacter data
        (TensorIdentityAutomorphism.identity C) exponent =
      ordinary data := by
  apply congrArg (WeightedFamily.mk data.simple)
  funext s
  simp [integralCharacter, ordinary]

/--
Evaluate a formal Kirby colour by replacing each simple label with a complete
typed diagram and retaining the finite linear combination.
-/
noncomputable def diagramExpansion
    {source target : Boundary C}
    (colour : WeightedFamily K S C)
    (diagram : S → Diagram C source target) :
    LinearDiagram (R := K) source target :=
  weightedSum (R := K) colour.weight diagram

/-- Evaluation of a formal colour is the exact finite weighted sum. -/
theorem eval_diagramExpansion
    {source target : Boundary C}
    (colour : WeightedFamily K S C)
    (diagram : S → Diagram C source target) :
    eval (R := K) (diagramExpansion colour diagram) =
      ∑ s, colour.weight s • Diagram.eval C (diagram s) := by
  exact eval_weightedSum colour.weight diagram

/-- The ordinary expansion visibly uses only the derived quantum dimensions. -/
theorem eval_ordinary_expansion
    {source target : Boundary C}
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (diagram : S → Diagram C source target) :
    eval (R := K) (diagramExpansion (ordinary data) diagram) =
      ∑ s, data.quantumDimension s • Diagram.eval C (diagram s) := by
  simpa using eval_diagramExpansion (ordinary data) diagram

/-- The twisted expansion exposes the exact derived coefficient formula. -/
theorem eval_integralCharacter_expansion
    {source target : Boundary C}
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ)
    (diagram : S → Diagram C source target) :
    eval (R := K)
        (diagramExpansion
          (integralCharacter data automorphism exponent) diagram) =
      ∑ s,
        (data.quantumDimension s *
          data.toFusionCategoryData.automorphismScalarPower
            automorphism s exponent) •
          Diagram.eval C (diagram s) := by
  simpa using
    eval_diagramExpansion
      (integralCharacter data automorphism exponent) diagram

end TwistedYetter.Kirby.EGNOKirbyColorExpansion
