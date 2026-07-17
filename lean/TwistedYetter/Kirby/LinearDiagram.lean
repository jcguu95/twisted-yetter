import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Linear.Basic
import TwistedYetter.Kirby.CategoricalTangle

/-!
# Formal linear combinations of typed categorical diagrams

A Kirby colour is a finite linear combination, not an object of the target
category.  This module keeps that distinction in the type system.  A
`LinearDiagram` is the free module on typed diagrams, and evaluation is the
linear extension of the ordinary categorical evaluator.
-/

namespace TwistedYetter.Kirby

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle

universe uR u v

variable {R : Type uR} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [BraidedCategory C]

/-- The free `R`-module on diagrams with one fixed typed boundary. -/
abbrev LinearDiagram (source target : Boundary C) :=
  Diagram C source target →₀ R

namespace LinearDiagram

/-- Embed one typed diagram as a basis vector of the free module. -/
noncomputable def atom
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    LinearDiagram (R := R) source target :=
  Finsupp.single diagram 1

/-- Evaluate a formal linear combination by linear extension. -/
noncomputable def eval
    {source target : Boundary C} :
    LinearDiagram (R := R) source target →ₗ[R]
      (source.denote ⟶ target.denote) :=
  Finsupp.linearCombination R (Diagram.eval C)

@[simp]
theorem eval_atom
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    eval (R := R) (atom (R := R) diagram) = Diagram.eval C diagram := by
  simp [eval, atom]

/-- A visible finite dimension-weighted family of typed diagrams. -/
noncomputable def weightedSum
    {source target : Boundary C}
    {ι : Type*} [Fintype ι]
    (weight : ι → R)
    (diagram : ι → Diagram C source target) :
    LinearDiagram (R := R) source target :=
  ∑ i, weight i • atom (R := R) (diagram i)

@[simp]
theorem eval_weightedSum
    {source target : Boundary C}
    {ι : Type*} [Fintype ι]
    (weight : ι → R)
    (diagram : ι → Diagram C source target) :
    eval (R := R) (weightedSum (R := R) weight diagram) =
      ∑ i, weight i • Diagram.eval C (diagram i) := by
  simp [weightedSum]

/--
Collapse a proved formal sum to an ordinary coupon only at the API boundary.
The original `LinearDiagram` remains in the certificate that justifies it.
-/
noncomputable def collapse
    {source target : Boundary C}
    (name : String)
    (linearDiagram : LinearDiagram (R := R) source target) :
    Diagram C source target :=
  Diagram.coupon name (eval (R := R) linearDiagram)

@[simp]
theorem eval_collapse
    {source target : Boundary C}
    (name : String)
    (linearDiagram : LinearDiagram (R := R) source target) :
    Diagram.eval C (collapse (R := R) name linearDiagram) =
      eval (R := R) linearDiagram :=
  rfl

end LinearDiagram

end TwistedYetter.Kirby
