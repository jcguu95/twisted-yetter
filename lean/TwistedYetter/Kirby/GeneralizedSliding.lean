import TwistedYetter.Fusion.Biorthogonal
import TwistedYetter.Fusion.Insertion
import TwistedYetter.Kirby.HandleSlide
import TwistedYetter.Kirby.LinearContext
import TwistedYetter.Kirby.LinearDiagram

/-!
# Bärenz--Barrett generalized sliding calculation

This module records equations (3.1.2)--(3.1.11) as a typed finite calculation.
The two insertion equalities are explicit source-backed inputs corresponding
to Lemma 3.2.  Braiding and mate changes are supplied as certified categorical
movies.  Lean performs all weighting, finite-sum interchange, channel
transport, inverse insertion, and construction of the resulting functor-valued
sliding law.
-/

namespace TwistedYetter.Kirby.GeneralizedSliding

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Fusion.Insertion
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Kirby.HandleSlide
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.LinearDiagram

universe uR uD vD uS uI

variable {R : Type uR} [CommSemiring R]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable [MonoidalCategory D] [BraidedCategory D]
variable [MonoidalPreadditive D] [MonoidalLinear R D]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
Category-level data shared by every strand `A` in Lemma 3.3.

The finite mated family is only required to be biorthogonal.  This deliberately
does not assert that the image of a source basis spans a target Hom space.
-/
structure SlidingCategoryData where
  fixed : D
  weight : S → R
  simple : S → D
  dualSimple : S → D
  matedPairing : (y z : S) →
    PerfectPairing R
      (simple y ⟶ dualSimple z ⊗ fixed)
      (dualSimple z ⊗ fixed ⟶ simple y)
  matedFamily : (y z : S) →
    BiorthogonalFamily (ι := I y z) (matedPairing y z)
  forwardProjection : (y z : S) → I y z →
    (fixed ⊗ dualSimple y ⟶ simple z)
  forwardInclusion : (y z : S) → I y z →
    (simple z ⟶ fixed ⊗ dualSimple y)
  forwardSound : (y : S) →
    ∑ z, ∑ i : I y z,
      weight z •
        (forwardProjection y z i ≫ forwardInclusion y z i) =
      𝟙 (fixed ⊗ dualSimple y)
  backwardSound : (z : S) →
    ∑ y, ∑ i : I y z,
      weight y •
        ((matedFamily y z).dual i ≫ (matedFamily y z).primal i) =
      𝟙 (dualSimple z ⊗ fixed)
  pivotal_source_ref : String :=
    "ref:baerenz-barrett-dichromatic-2018"
  pivotal_source_locator : String :=
    "Lemma 2.23 and Lemma 3.3, equations (3.1.9)-(3.1.11)"

namespace SlidingCategoryData

variable (data : SlidingCategoryData (R := R) (D := D) (S := S) (I := I))

/-- The exact Kronecker equation used to authorize inverse insertion. -/
theorem equation_3_1_9_to_3_1_11 (y z : S) (i j : I y z) :
    (data.matedPairing y z).pair
        ((data.matedFamily y z).primal i)
        ((data.matedFamily y z).dual j) =
      if i = j then 1 else 0 :=
  (data.matedFamily y z).pair_eq i j

/-- The forward instance of the source-backed insertion lemma. -/
def forwardResolution (y : S) :
    IdentityResolution
      (R := R) (S := S) (I := fun z => I y z)
      (data.fixed ⊗ data.dualSimple y) where
  simple := data.simple
  weight := data.weight
  projection z i := data.forwardProjection y z i
  inclusion z i := data.forwardInclusion y z i
  sound := data.forwardSound y

/--
The inverse-insertion resolution after mate transport.  Its channels are
definitionally the recorded mated biorthogonal family.
-/
def backwardResolution (z : S) :
    IdentityResolution
      (R := R) (S := S) (I := fun y => I y z)
      (data.dualSimple z ⊗ data.fixed) where
  simple := data.simple
  weight := data.weight
  projection y i := (data.matedFamily y z).dual i
  inclusion y i := (data.matedFamily y z).primal i
  sound := data.backwardSound z

end SlidingCategoryData

/--
One pointwise instance of the graphical calculation, with endpoint object
`fixed ⊗ strand`.

No field states the desired endpoint equality.  The only equality inputs are
the two insertion resolutions and the soundness already carried by the local
movies.
-/
structure SlidingFiber
    (data : SlidingCategoryData (R := R) (D := D) (S := S) (I := I))
    (strand : D) where
  forwardContext : (y : S) →
    Context D
      (.atom (data.fixed ⊗ data.dualSimple y))
      (.atom (data.fixed ⊗ data.dualSimple y))
      (.atom (data.fixed ⊗ strand))
      (.atom (data.fixed ⊗ strand))
  backwardContext : (z : S) →
    Context D
      (.atom (data.dualSimple z ⊗ data.fixed))
      (.atom (data.dualSimple z ⊗ data.fixed))
      (.atom (data.fixed ⊗ strand))
      (.atom (data.fixed ⊗ strand))
  braidedChannel : (y z : S) → I y z →
    Diagram D (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand))
  braidingMovie : (y z : S) → (i : I y z) →
    Movie
      (Context.plug D (forwardContext y)
        (Diagram.coupon "BB-3.1.4-forward-channel"
          (data.forwardProjection y z i ≫ data.forwardInclusion y z i)))
      (braidedChannel y z i)
  mateMovie : (y z : S) → (i : I y z) →
    Movie (braidedChannel y z i)
      (Context.plug D (backwardContext z)
        (Diagram.coupon "BB-3.1.6-mated-channel"
          ((data.matedFamily y z).dual i ≫
            (data.matedFamily y z).primal i)))
  insertion_source_ref : String :=
    "ref:baerenz-barrett-dichromatic-2018"
  insertion_source_locator : String :=
    "Lemma 3.2 from Lemma 2.37; equations (3.1.4) and (3.1.7)"

namespace SlidingFiber

variable {data :
  SlidingCategoryData (R := R) (D := D) (S := S) (I := I)}
variable {strand : D}
variable (fiber : SlidingFiber data strand)

/-- The left simple-labelled term in equation (3.1.3). -/
def leftTerm (y : S) :
    Diagram D (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  Context.plug D (fiber.forwardContext y)
    (Diagram.identity (.atom (data.fixed ⊗ data.dualSimple y)))

/-- The right simple-labelled term in equation (3.1.7). -/
def rightTerm (z : S) :
    Diagram D (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  Context.plug D (fiber.backwardContext z)
    (Diagram.identity (.atom (data.dualSimple z ⊗ data.fixed)))

/-- The channel obtained by forward insertion in equation (3.1.4). -/
def insertedChannel (y z : S) (i : I y z) :
    Diagram D (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  Context.plug D (fiber.forwardContext y)
    (Diagram.coupon "BB-3.1.4-forward-channel"
      (data.forwardProjection y z i ≫ data.forwardInclusion y z i))

/-- The mated channel used in equations (3.1.6) and (3.1.7). -/
def matedChannel (y z : S) (i : I y z) :
    Diagram D (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  Context.plug D (fiber.backwardContext z)
    (Diagram.coupon "BB-3.1.6-mated-channel"
      ((data.matedFamily y z).dual i ≫
        (data.matedFamily y z).primal i))

/-- Equation (3.1.3), kept as a formal Kirby-colour sum. -/
noncomputable def stage313 :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  weightedSum (R := R) data.weight fiber.leftTerm

/-- Equation (3.1.4), after insertion of the second Kirby colour. -/
noncomputable def stage314 :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  ∑ y, ∑ z, ∑ i : I y z,
    (data.weight y * data.weight z) •
      atom (R := R) (fiber.insertedChannel y z i)

/-- Equation (3.1.5), after braiding naturality. -/
noncomputable def stage315 :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  ∑ y, ∑ z, ∑ i : I y z,
    (data.weight y * data.weight z) •
      atom (R := R) (fiber.braidedChannel y z i)

/-- Equation (3.1.6), after the pivotal mate change of variables. -/
noncomputable def stage316 :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  ∑ y, ∑ z, ∑ i : I y z,
    (data.weight y * data.weight z) •
      atom (R := R) (fiber.matedChannel y z i)

/-- Equations (3.1.7)--(3.1.8), after inverse insertion and collapse. -/
noncomputable def stage318 :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  weightedSum (R := R) data.weight fiber.rightTerm

/--
Equation (3.1.4) with an additional scalar weight attached to the internal
simple channel `z`.

For the homologically twisted application this weight will be the scalar by
which the tensor-identity automorphism acts on `z`.
-/
noncomputable def channelWeightedStage314
    (channelWeight : S → R) :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  ∑ y, ∑ z, ∑ i : I y z,
    ((data.weight y * data.weight z) * channelWeight z) •
      atom (R := R) (fiber.insertedChannel y z i)

/-- The channel-weighted stage after the braiding movie. -/
noncomputable def channelWeightedStage315
    (channelWeight : S → R) :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  ∑ y, ∑ z, ∑ i : I y z,
    ((data.weight y * data.weight z) * channelWeight z) •
      atom (R := R) (fiber.braidedChannel y z i)

/-- The channel-weighted stage after the pivotal mate movie. -/
noncomputable def channelWeightedStage316
    (channelWeight : S → R) :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  ∑ y, ∑ z, ∑ i : I y z,
    ((data.weight y * data.weight z) * channelWeight z) •
      atom (R := R) (fiber.matedChannel y z i)

/--
The weighted target endpoint.  The internal weight remains attached to the
surviving `z`-label after inverse insertion.
-/
noncomputable def channelWeightedStage318
    (channelWeight : S → R) :
    LinearDiagram (R := R)
      (.atom (data.fixed ⊗ strand)) (.atom (data.fixed ⊗ strand)) :=
  weightedSum (R := R)
    (fun z => data.weight z * channelWeight z) fiber.rightTerm

/-- Every channel weight survives the braiding movie term by term. -/
theorem channelWeighted_equation_3_1_5
    (channelWeight : S → R) :
    eval (R := R) (fiber.channelWeightedStage314 channelWeight) =
      eval (R := R) (fiber.channelWeightedStage315 channelWeight) := by
  simp only [channelWeightedStage314, channelWeightedStage315,
    map_sum, map_smul, eval_atom]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg
    (fun value =>
      ((data.weight y * data.weight z) * channelWeight z) • value)
    (by
      simpa only [insertedChannel] using
        (fiber.braidingMovie y z i).sound)

/-- Every channel weight survives the mate movie term by term. -/
theorem channelWeighted_equation_3_1_6
    (channelWeight : S → R) :
    eval (R := R) (fiber.channelWeightedStage315 channelWeight) =
      eval (R := R) (fiber.channelWeightedStage316 channelWeight) := by
  simp only [channelWeightedStage315, channelWeightedStage316,
    map_sum, map_smul, eval_atom]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg
    (fun value =>
      ((data.weight y * data.weight z) * channelWeight z) • value)
    (by
      simpa only [matedChannel] using
        (fiber.mateMovie y z i).sound)

/--
Inverse insertion removes only the `y`-resolution.  An arbitrary scalar
depending on `z` remains visible on the target endpoint.
-/
theorem channelWeighted_equation_3_1_7_to_3_1_8
    (channelWeight : S → R) :
    eval (R := R) (fiber.channelWeightedStage316 channelWeight) =
      eval (R := R) (fiber.channelWeightedStage318 channelWeight) := by
  simp only [channelWeightedStage316, channelWeightedStage318,
    map_sum, map_smul, eval_atom, eval_weightedSum]
  calc
    (∑ y, ∑ z, ∑ i : I y z,
        ((data.weight y * data.weight z) * channelWeight z) •
          Diagram.eval D (fiber.matedChannel y z i)) =
      ∑ z, ∑ y, ∑ i : I y z,
        ((data.weight y * data.weight z) * channelWeight z) •
          Diagram.eval D (fiber.matedChannel y z i) := by
        rw [Finset.sum_comm]
    _ = ∑ z, (data.weight z * channelWeight z) •
        (∑ y, ∑ i : I y z,
          data.weight y • Diagram.eval D (fiber.matedChannel y z i)) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ac_rfl
    _ = ∑ z, (data.weight z * channelWeight z) •
        Diagram.eval D (fiber.rightTerm z) := by
      apply Finset.sum_congr rfl
      intro z _
      exact congrArg
        (fun value => (data.weight z * channelWeight z) • value)
        (insertIdentity (data.backwardResolution z)
          (fiber.backwardContext z) "BB-3.1.6-mated-channel")

/-- The complete channel-weighted transport from insertion to target. -/
theorem channelWeighted_transport
    (channelWeight : S → R) :
    eval (R := R) (fiber.channelWeightedStage314 channelWeight) =
      eval (R := R) (fiber.channelWeightedStage318 channelWeight) :=
  fiber.channelWeighted_equation_3_1_5 channelWeight |>.trans <|
    fiber.channelWeighted_equation_3_1_6 channelWeight |>.trans <|
      fiber.channelWeighted_equation_3_1_7_to_3_1_8 channelWeight

/-- Equation (3.1.4): forward insertion, including both dimension weights. -/
theorem equation_3_1_4 :
    eval (R := R) fiber.stage313 =
      eval (R := R) fiber.stage314 := by
  simp only [stage313, eval_weightedSum, stage314, map_sum, map_smul,
    eval_atom]
  calc
    ∑ y, data.weight y • Diagram.eval D (fiber.leftTerm y) =
        ∑ y, data.weight y •
          (∑ z, ∑ i : I y z,
            data.weight z • Diagram.eval D (fiber.insertedChannel y z i)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact congrArg (fun value => data.weight y • value)
        (insertIdentity (data.forwardResolution y)
          (fiber.forwardContext y) "BB-3.1.4-forward-channel").symm
    _ = ∑ y, ∑ z, ∑ i : I y z,
          (data.weight y * data.weight z) •
            Diagram.eval D (fiber.insertedChannel y z i) := by
      simp only [Finset.smul_sum, smul_smul]

/-- Equation (3.1.5): every channel follows its certified braiding movie. -/
theorem equation_3_1_5 :
    eval (R := R) fiber.stage314 =
      eval (R := R) fiber.stage315 := by
  simp only [stage314, stage315, map_sum, map_smul, eval_atom]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg
    (fun value => (data.weight y * data.weight z) • value)
    (by
      simpa only [insertedChannel] using
        (fiber.braidingMovie y z i).sound)

/--
Equation (3.1.6): every channel follows its certified cup/cap mate movie.
The target coupons are the exact biorthogonal family recorded in `data`.
-/
theorem equation_3_1_6 :
    eval (R := R) fiber.stage315 =
      eval (R := R) fiber.stage316 := by
  simp only [stage315, stage316, map_sum, map_smul, eval_atom]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg
    (fun value => (data.weight y * data.weight z) • value)
    (by
      simpa only [matedChannel] using
        (fiber.mateMovie y z i).sound)

/--
Equations (3.1.7)--(3.1.8): commute the finite `Y,Z` sums, use commutativity
of the two dimension weights, and perform inverse insertion for each `Z`.
-/
theorem equation_3_1_7_to_3_1_8 :
    eval (R := R) fiber.stage316 =
      eval (R := R) fiber.stage318 := by
  simp only [stage316, stage318, map_sum, map_smul, eval_atom,
    eval_weightedSum]
  calc
    ∑ y, ∑ z, ∑ i : I y z,
        (data.weight y * data.weight z) •
          Diagram.eval D (fiber.matedChannel y z i) =
      ∑ z, ∑ y, ∑ i : I y z,
        (data.weight y * data.weight z) •
          Diagram.eval D (fiber.matedChannel y z i) := by
      rw [Finset.sum_comm]
    _ = ∑ z, data.weight z •
        (∑ y, ∑ i : I y z,
          data.weight y • Diagram.eval D (fiber.matedChannel y z i)) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _ = ∑ z, data.weight z • Diagram.eval D (fiber.rightTerm z) := by
      apply Finset.sum_congr rfl
      intro z _
      exact congrArg (fun value => data.weight z • value)
        (insertIdentity (data.backwardResolution z)
          (fiber.backwardContext z) "BB-3.1.6-mated-channel")

/-- The complete pointwise calculation from (3.1.3) through (3.1.8). -/
theorem core_sound :
    eval (R := R) fiber.stage313 =
      eval (R := R) fiber.stage318 :=
  fiber.equation_3_1_4.trans <|
    fiber.equation_3_1_5.trans <|
      fiber.equation_3_1_6.trans fiber.equation_3_1_7_to_3_1_8

end SlidingFiber

/--
All pointwise fibers and the two endpoint naturality proofs.

The endpoint naturality statements are local ribbon-graph facts; the central
sliding equality is not a field and is derived from every fiber's finite
calculation.
-/
structure SlidingFamily
    (data : SlidingCategoryData (R := R) (D := D) (S := S) (I := I)) where
  fiber : (strand : D) → SlidingFiber data strand
  before_naturality : {X Y : D} → (f : X ⟶ Y) →
    (tensorLeft data.fixed).map f ≫
        eval (R := R) (fiber Y).stage313 =
      eval (R := R) (fiber X).stage313 ≫
        (tensorLeft data.fixed).map f
  after_naturality : {X Y : D} → (f : X ⟶ Y) →
    (tensorLeft data.fixed).map f ≫
        eval (R := R) (fiber Y).stage318 =
      eval (R := R) (fiber X).stage318 ≫
        (tensorLeft data.fixed).map f
  diagram_schema : String := "twisted-yetter.linear-generalized-sliding.v1"
  diagram_content_hash : String
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 3.3, equations (3.1.2)-(3.1.11), journal pages 681-684"

namespace SlidingFamily

variable {data :
  SlidingCategoryData (R := R) (D := D) (S := S) (I := I)}
variable (family : SlidingFamily data)

/-- Natural transformation represented by the left side of (3.1.2). -/
noncomputable def before :
    tensorLeft data.fixed ⟶ tensorLeft data.fixed where
  app strand := eval (R := R) (family.fiber strand).stage313
  naturality _ _ f := family.before_naturality f

/-- Natural transformation represented by the right side of (3.1.2). -/
noncomputable def after :
    tensorLeft data.fixed ⟶ tensorLeft data.fixed where
  app strand := eval (R := R) (family.fiber strand).stage318
  naturality _ _ f := family.after_naturality f

/-- Equation (3.1.2) as equality of natural transformations. -/
theorem equation_3_1_2 : family.before = family.after := by
  ext strand
  exact (family.fiber strand).core_sound

/--
The completed diagram-backed Lemma 3.3 law.  Ordinary endpoint diagrams are
created only by collapsing the retained formal linear diagrams.
-/
noncomputable def sourcedFunctorSlidingLaw :
    SourcedFunctorSlidingLaw (tensorLeft data.fixed) where
  before_diagram strand :=
    collapse (R := R) "BB-3.3-before-linear-sum"
      (family.fiber strand).stage313
  after_diagram strand :=
    collapse (R := R) "BB-3.3-after-linear-sum"
      (family.fiber strand).stage318
  before := family.before
  after := family.after
  before_eval _ := rfl
  after_eval _ := rfl
  core_sound := family.equation_3_1_2
  diagram_schema := family.diagram_schema
  diagram_content_hash := family.diagram_content_hash
  source_ref := family.source_ref
  source_locator := family.source_locator

end SlidingFamily

end TwistedYetter.Kirby.GeneralizedSliding
