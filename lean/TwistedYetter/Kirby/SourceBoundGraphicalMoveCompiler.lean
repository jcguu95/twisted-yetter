import TwistedYetter.Kirby.CategoricalPresentationCompiler
import TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

/-!
# Source-bound graphical move compiler

This module is the proof-relevant bridge from one serialized local recipe to
the R7/R8/R9 evaluator proof objects.

A framed-isotopy script is interpreted one tagged generator at a time in an
exact typed context. Cancellation calculations are derived from the shared
category-level factors plus a presentation-specific disjoint-union
factorization. Later sections add the source-bound slide realizations and the
exhaustive eight-case compiler.

No structure below contains a bare equality of normalized invariant values.
-/

namespace TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramedSliding
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HandleSlide
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationIsotopy
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RightRigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
The exact category-level realization of one source generator tag.

The algebra-sensitive constructors are definitionally built from the accepted
framed kink, twist, or spherical trace. There is no constructor accepting an
arbitrary `TaggedMove` and a later assertion that it used the right algebra.
-/
inductive AlgebraBoundTaggedMove
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData) :
    FramedIsotopyGenerator → {source target : Boundary C} →
      Diagram C source target → Diagram C source target →
        Type (max uC vC)
  | planarIdentityBefore
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      AlgebraBoundTaggedMove algebra .planarIdentityBefore
        (identityBefore diagram) diagram
  | planarIdentityAfter
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      AlgebraBoundTaggedMove algebra .planarIdentityAfter
        (identityAfter diagram) diagram
  | planarCompAssoc
      {a b c d : Boundary C}
      (first : Diagram C a b)
      (second : Diagram C b c)
      (third : Diagram C c d) :
      AlgebraBoundTaggedMove algebra .planarCompAssoc
        (compAssocBefore first second third)
        (compAssocAfter first second third)
  | criticalInterchange
      {a b c e f g : Boundary C}
      (leftFirst : Diagram C a b)
      (leftSecond : Diagram C b c)
      (rightFirst : Diagram C e f)
      (rightSecond : Diagram C f g) :
      AlgebraBoundTaggedMove algebra .criticalInterchange
        (tensorInterchangeBefore
          leftFirst leftSecond rightFirst rightSecond)
        (tensorInterchangeAfter
          leftFirst leftSecond rightFirst rightSecond)
  | reidemeisterIIPositive (X Y : C) :
      AlgebraBoundTaggedMove algebra .reidemeisterIIPositive
        (reidemeisterIIPositiveBefore X Y)
        (reidemeisterIIAfter X Y)
  | reidemeisterIINegative (X Y : C) :
      AlgebraBoundTaggedMove algebra .reidemeisterIINegative
        (reidemeisterIINegativeBefore X Y)
        (reidemeisterIIAfter X Y)
  | reidemeisterIII (X Y Z : C) :
      AlgebraBoundTaggedMove algebra .reidemeisterIII
        (reidemeisterIIIBefore X Y Z)
        (reidemeisterIIIAfter X Y Z)
  | rightPrimalSnake (X : C) :
      AlgebraBoundTaggedMove algebra .rightPrimalSnake
        (rightPrimalSnakeBefore X) (Diagram.identity (atom X))
  | rightDualSnake (X : C) :
      AlgebraBoundTaggedMove algebra .rightDualSnake
        (rightDualSnakeBefore X) (Diagram.identity (atom Xᘁ))
  | leftPrimalSnake (X : C) :
      AlgebraBoundTaggedMove algebra .leftPrimalSnake
        (leftPrimalSnakeBefore X) (Diagram.identity (atom X))
  | leftDualSnake (X : C) :
      AlgebraBoundTaggedMove algebra .leftDualSnake
        (leftDualSnakeBefore X) (Diagram.identity (atom (ᘁX)))
  | framedPositive (X : C) :
      AlgebraBoundTaggedMove algebra .framedPositive
        (positiveKink algebra.framedKink.ribbon X)
        (algebra.framedKink.positiveTwistDiagram X)
  | framedNegative (X : C) :
      AlgebraBoundTaggedMove algebra .framedNegative
        (negativeKink algebra.framedKink.ribbon X)
        (algebra.framedKink.negativeTwistDiagram X)
  | couponPositiveCrossing
      {X X' Y Y' : C}
      (f : X ⟶ Y)
      (g : X' ⟶ Y') :
      AlgebraBoundTaggedMove algebra .couponPositiveCrossing
        (positiveCrossingBefore f g) (positiveCrossingAfter f g)
  | couponNegativeCrossing
      {X X' Y Y' : C}
      (f : X ⟶ Y)
      (g : X' ⟶ Y') :
      AlgebraBoundTaggedMove algebra .couponNegativeCrossing
        (negativeCrossingBefore f g) (negativeCrossingAfter f g)
  | couponRightCup
      {X Y : C}
      (f : X ⟶ Y) :
      AlgebraBoundTaggedMove algebra .couponRightCup
        (rightCupMateSide f) (rightCupOriginalSide f)
  | couponRightCap
      {X Y : C}
      (f : X ⟶ Y) :
      AlgebraBoundTaggedMove algebra .couponRightCap
        (rightCapMateSide f) (rightCapOriginalSide f)
  | couponLeftCup
      {X Y : C}
      (f : X ⟶ Y) :
      AlgebraBoundTaggedMove algebra .couponLeftCup
        (leftCupMateSide f) (leftCupOriginalSide f)
  | couponLeftCap
      {X Y : C}
      (f : X ⟶ Y) :
      AlgebraBoundTaggedMove algebra .couponLeftCap
        (leftCapMateSide f) (leftCapOriginalSide f)
  | couponPositiveTwist
      {X Y : C}
      (name : String)
      (f : X ⟶ Y) :
      AlgebraBoundTaggedMove algebra .couponPositiveTwist
        (algebra.framedKink.twist.positiveBefore name f)
        (algebra.framedKink.twist.positiveAfter name f)
  | couponNegativeTwist
      {X Y : C}
      (name : String)
      (f : X ⟶ Y) :
      AlgebraBoundTaggedMove algebra .couponNegativeTwist
        (algebra.framedKink.twist.negativeBefore name f)
        (algebra.framedKink.twist.negativeAfter name f)
  | closureCut
      {X Y : C}
      (f : X ⟶ Y)
      (g : Y ⟶ X) :
      AlgebraBoundTaggedMove algebra .closureCut
        (algebra.sphericalCut.cutBefore f g)
        (algebra.sphericalCut.cutAfter f g)

namespace AlgebraBoundTaggedMove

/-- Forget only the algebra binding after constructing the exact tagged move. -/
def toTaggedMove
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    {generator : FramedIsotopyGenerator}
    {source target : Boundary C}
    {before after : Diagram C source target} :
    AlgebraBoundTaggedMove algebra generator before after →
      TaggedMove before after
  | .planarIdentityBefore diagram =>
      .planarIdentityBefore diagram
  | .planarIdentityAfter diagram =>
      .planarIdentityAfter diagram
  | .planarCompAssoc first second third =>
      .planarCompAssoc first second third
  | .criticalInterchange leftFirst leftSecond rightFirst rightSecond =>
      .criticalInterchange leftFirst leftSecond rightFirst rightSecond
  | .reidemeisterIIPositive X Y =>
      .reidemeisterIIPositive X Y
  | .reidemeisterIINegative X Y =>
      .reidemeisterIINegative X Y
  | .reidemeisterIII X Y Z =>
      .reidemeisterIII X Y Z
  | .rightPrimalSnake X =>
      .rightPrimalSnake X
  | .rightDualSnake X =>
      .rightDualSnake X
  | .leftPrimalSnake X =>
      .leftPrimalSnake X
  | .leftDualSnake X =>
      .leftDualSnake X
  | .framedPositive X =>
      .framedPositive algebra.framedKink X
  | .framedNegative X =>
      .framedNegative algebra.framedKink X
  | .couponPositiveCrossing f g =>
      .couponPositiveCrossing f g
  | .couponNegativeCrossing f g =>
      .couponNegativeCrossing f g
  | .couponRightCup f =>
      .couponRightCup f
  | .couponRightCap f =>
      .couponRightCap f
  | .couponLeftCup f =>
      .couponLeftCup f
  | .couponLeftCap f =>
      .couponLeftCap f
  | .couponPositiveTwist name f =>
      .couponPositiveTwist algebra.framedKink.twist name f
  | .couponNegativeTwist name f =>
      .couponNegativeTwist algebra.framedKink.twist name f
  | .closureCut f g =>
      .closureCut algebra.sphericalCut f g

end AlgebraBoundTaggedMove

/--
One source-tagged isotopy generator interpreted in an exact closed context.

The endpoint fields are equalities of diagram syntax, not evaluator
equalities.
-/
structure InterpretedFramedIsotopyStep
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData)
    (generator : FramedIsotopyGenerator)
    (before after : Diagram C .unit .unit) where
  localSource : Boundary C
  localTarget : Boundary C
  localBefore : Diagram C localSource localTarget
  localAfter : Diagram C localSource localTarget
  move : AlgebraBoundTaggedMove algebra generator localBefore localAfter
  context : Context C localSource localTarget .unit .unit
  before_sound : Context.plug C context localBefore = before
  after_sound : Context.plug C context localAfter = after

namespace InterpretedFramedIsotopyStep

/-- Compile one source-tagged step to the generated-isotopy grammar. -/
def toGeneratedIsotopy
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    {generator : FramedIsotopyGenerator}
    {before after : Diagram C .unit .unit}
    (step :
      InterpretedFramedIsotopyStep algebra generator before after) :
    GeneratedIsotopy before after := by
  have contextual :
      GeneratedIsotopy
        (Context.plug C step.context step.localBefore)
        (Context.plug C step.context step.localAfter) :=
    .inContext step.context (.step step.move.toTaggedMove)
  simpa only [step.before_sound, step.after_sound] using contextual

end InterpretedFramedIsotopyStep

/--
Typed interpretation of the complete ordered framed-isotopy source script.

There is no constructor from a preassembled `GeneratedIsotopy`; every
non-reflexive step consumes exactly one retained source tag.
-/
inductive InterpretedFramedIsotopyProgram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData) :
    List (String × FramedIsotopyGenerator) →
      Diagram C .unit .unit → Diagram C .unit .unit →
        Type (max uC vC)
  | nil (frame : Diagram C .unit .unit) :
      InterpretedFramedIsotopyProgram algebra [] frame frame
  | cons
      {eventId : String}
      {generator : FramedIsotopyGenerator}
      {rest : List (String × FramedIsotopyGenerator)}
      {first middle last : Diagram C .unit .unit}
      (step :
        InterpretedFramedIsotopyStep
          algebra generator first middle)
      (tail :
        InterpretedFramedIsotopyProgram algebra rest middle last) :
      InterpretedFramedIsotopyProgram
        algebra ((eventId, generator) :: rest) first last

namespace InterpretedFramedIsotopyProgram

/-- Compile the exact ordered source script by structural recursion. -/
def toGeneratedIsotopy
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    {steps : List (String × FramedIsotopyGenerator)}
    {first last : Diagram C .unit .unit} :
    InterpretedFramedIsotopyProgram algebra steps first last →
      GeneratedIsotopy first last
  | .nil _ =>
      .refl _
  | .cons step tail =>
      .trans step.toGeneratedIsotopy tail.toGeneratedIsotopy

end InterpretedFramedIsotopyProgram

/-- The exact ordered source tags retained by a framed-isotopy recipe. -/
def framedRecipeSteps
    {edit : HandleEdit .framedIsotopy}
    (program : GraphicalEditProgram edit) :
    List (String × FramedIsotopyGenerator) :=
  match program with
  | .framedIsotopy _ _ steps _ _ => steps

/-- Exact interpreted framed-isotopy evidence for one source recipe. -/
structure FramedIsotopyRealization
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (metadata : TableTwoMoveMetadata .framedIsotopy source target)
    (before after : Diagram C .unit .unit) where
  program :
    InterpretedFramedIsotopyProgram algebra
      (framedRecipeSteps metadata.recipe.graphicalProgram) before after

/-- Extract the sliding law retained by an ordinary-slide proof object. -/
def ordinarySlideLaw
    {source target : Boundary C}
    {before after : Diagram C source target} :
    OrdinaryHandleSlide before after → SourcedSlidingLaw C
  | .oneOverOne _ _ _ law _ _ => law
  | .twoOverOne _ _ _ law _ _ => law

/-- Extract the generalized family retained by a 2-over-2 proof object. -/
def twoOverTwoSlidingFamily
    {source target : Boundary C}
    {before after : Diagram C source target}
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)} :
    TwoHandleOverTwoSlide
      (data := categoryData.slidingData) before after →
      SlidingFamily categoryData.slidingData
  | .twoOverTwo _ _ _ family _ _ => family

def oneOverOneOrientation : HandleEdit .oneOverOne → BandOrientation
  | .oneOverOne orientation _ _ _ => orientation

def oneOverOneSlidingId : HandleEdit .oneOverOne → String
  | .oneOverOne _ sliding _ _ => sliding

def oneOverOneStationaryId : HandleEdit .oneOverOne → String
  | .oneOverOne _ _ stationary _ => stationary

def twoOverOneOrientation : HandleEdit .twoOverOne → BandOrientation
  | .twoOverOne orientation _ _ _ => orientation

def twoOverOneSlidingId : HandleEdit .twoOverOne → String
  | .twoOverOne _ sliding _ _ => sliding

def twoOverOneStationaryId : HandleEdit .twoOverOne → String
  | .twoOverOne _ _ stationary _ => stationary

def twoOverTwoOrientation : HandleEdit .twoOverTwo → BandOrientation
  | .twoOverTwo orientation _ _ _ => orientation

def twoOverTwoSlidingId : HandleEdit .twoOverTwo → String
  | .twoOverTwo _ sliding _ _ => sliding

def twoOverTwoStationaryId : HandleEdit .twoOverTwo → String
  | .twoOverTwo _ _ stationary _ => stationary

/-- A 1-over-1 slide tied simultaneously to algebra and source recipe. -/
structure OneOverOneRealization
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (orientation : BandOrientation)
    (metadata : TableTwoMoveMetadata .oneOverOne source target)
    (before after : Diagram C .unit .unit) where
  slide : OrdinaryHandleSlide before after
  law_sound : ordinarySlideLaw slide = algebra.ordinarySliding
  kind_sound : (ordinarySlideMetadata slide).kind = .oneOverOne
  orientation_sound :
    (ordinarySlideMetadata slide).orientation = orientation
  move_id_sound :
    (ordinarySlideMetadata slide).moveId = metadata.moveId
  source_hash_sound :
    (ordinarySlideMetadata slide).sourcePresentationHash =
      metadata.sourcePresentationHash
  target_hash_sound :
    (ordinarySlideMetadata slide).targetPresentationHash =
      metadata.targetPresentationHash
  recipe_orientation_sound :
    oneOverOneOrientation metadata.recipe.handleEdit = orientation
  recipe_sliding_id_sound :
    (ordinarySlideMetadata slide).slidingComponentId =
      oneOverOneSlidingId metadata.recipe.handleEdit
  recipe_stationary_id_sound :
    (ordinarySlideMetadata slide).stationaryComponentId =
      oneOverOneStationaryId metadata.recipe.handleEdit

/-- A 2-over-1 slide tied simultaneously to algebra and source recipe. -/
structure TwoOverOneRealization
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (orientation : BandOrientation)
    (metadata : TableTwoMoveMetadata .twoOverOne source target)
    (before after : Diagram C .unit .unit) where
  slide : OrdinaryHandleSlide before after
  law_sound : ordinarySlideLaw slide = algebra.ordinarySliding
  kind_sound : (ordinarySlideMetadata slide).kind = .twoOverOne
  orientation_sound :
    (ordinarySlideMetadata slide).orientation = orientation
  move_id_sound :
    (ordinarySlideMetadata slide).moveId = metadata.moveId
  source_hash_sound :
    (ordinarySlideMetadata slide).sourcePresentationHash =
      metadata.sourcePresentationHash
  target_hash_sound :
    (ordinarySlideMetadata slide).targetPresentationHash =
      metadata.targetPresentationHash
  recipe_orientation_sound :
    twoOverOneOrientation metadata.recipe.handleEdit = orientation
  recipe_sliding_id_sound :
    (ordinarySlideMetadata slide).slidingComponentId =
      twoOverOneSlidingId metadata.recipe.handleEdit
  recipe_stationary_id_sound :
    (ordinarySlideMetadata slide).stationaryComponentId =
      twoOverOneStationaryId metadata.recipe.handleEdit

/-- A 2-over-2 slide tied to the generalized family and source recipe. -/
structure TwoOverTwoRealization
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (orientation : BandOrientation)
    (metadata : TableTwoMoveMetadata .twoOverTwo source target)
    (before after : Diagram C .unit .unit) where
  slide :
    TwoHandleOverTwoSlide
      (data := categoryData.slidingData) before after
  family_sound :
    twoOverTwoSlidingFamily slide = algebra.generalizedSliding
  orientation_sound :
    (twoOverTwoSlideMetadata slide).orientation = orientation
  move_id_sound :
    (twoOverTwoSlideMetadata slide).moveId = metadata.moveId
  source_hash_sound :
    (twoOverTwoSlideMetadata slide).sourcePresentationHash =
      metadata.sourcePresentationHash
  target_hash_sound :
    (twoOverTwoSlideMetadata slide).targetPresentationHash =
      metadata.targetPresentationHash
  recipe_orientation_sound :
    twoOverTwoOrientation metadata.recipe.handleEdit = orientation
  recipe_sliding_id_sound :
    (twoOverTwoSlideMetadata slide).slidingComponentId =
      twoOverTwoSlidingId metadata.recipe.handleEdit
  recipe_stationary_id_sound :
    (twoOverTwoSlideMetadata slide).stationaryComponentId =
      twoOverTwoStationaryId metadata.recipe.handleEdit

/--
Presentation-specific 1--2 factorization.

Only the disjoint-union decomposition is local input. Cutting, killing, and
transparent-twist data come from the shared category algebra.
-/
structure OneTwoFactorizationProgram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {profile : GlobalDimensionProfile (K := K)}
    (algebra : CancellationInput profile)
    (beforeDiagram afterDiagram : Diagram C .unit .unit)
    (before after : EvaluationState (K := K)) where
  counts_sound : before.counts = after.counts.addOneTwo
  localPairDiagram : Diagram C .unit .unit
  diagram_factorization :
    beforeDiagram =
      closedTensorDiagram localPairDiagram afterDiagram
  local_pair_scalar :
    categoryData.closedScalar
        (Diagram.eval C localPairDiagram) =
      algebra.oneTwoPairValue

namespace OneTwoFactorizationProgram

/-- Derive the complete R9 calculation from separated local inputs. -/
def toCalculation
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {profile : GlobalDimensionProfile (K := K)}
    {algebra : CancellationInput profile}
    {beforeDiagram afterDiagram : Diagram C .unit .unit}
    {before after : EvaluationState (K := K)}
    (program :
      OneTwoFactorizationProgram
        (categoryData := categoryData)
        algebra beforeDiagram afterDiagram before after)
    (before_raw_sound :
      before.rawNumerator =
        categoryData.closedScalar (Diagram.eval C beforeDiagram))
    (after_raw_sound :
      after.rawNumerator =
        categoryData.closedScalar (Diagram.eval C afterDiagram)) :
    OneTwoLocalCalculation profile where
  pairValue := algebra.oneTwoPairValue
  cutValue := algebra.oneTwoCutValue
  before := before
  after := after
  counts_sound := program.counts_sound
  isolated_from_rest :=
    beforeDiagram =
      closedTensorDiagram program.localPairDiagram afterDiagram
  isolated_from_rest_witness := program.diagram_factorization
  disjoint_union_sound := fun _ => by
    rw [before_raw_sound, program.diagram_factorization,
      categoryData.closed_tensor_multiplicative,
      program.local_pair_scalar, after_raw_sound]
  transparent_twist_trivial := algebra.transparentTwistTrivial
  transparent_twist_witness := algebra.transparent_twist_witness
  cutting_identity := algebra.cutting_identity
  killing_identity := algebra.killing_identity

end OneTwoFactorizationProgram

/--
Presentation-specific 2--3 factorization.

The local program proves only that an unlinked zero-framed unknot splits from
the exact numerator. Its value is fixed by the shared pivotal input.
-/
structure TwoThreeFactorizationProgram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {profile : GlobalDimensionProfile (K := K)}
    (algebra : CancellationInput profile)
    (beforeDiagram afterDiagram : Diagram C .unit .unit)
    (before after : EvaluationState (K := K)) where
  counts_sound : before.counts = after.counts.addTwoThree
  localUnknotDiagram : Diagram C .unit .unit
  diagram_factorization :
    beforeDiagram =
      closedTensorDiagram localUnknotDiagram afterDiagram
  local_unknot_scalar :
    categoryData.closedScalar
        (Diagram.eval C localUnknotDiagram) =
      algebra.twoThreeUnknotValue

namespace TwoThreeFactorizationProgram

/-- Derive the complete R9 calculation from separated local inputs. -/
def toCalculation
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {profile : GlobalDimensionProfile (K := K)}
    {algebra : CancellationInput profile}
    {beforeDiagram afterDiagram : Diagram C .unit .unit}
    {before after : EvaluationState (K := K)}
    (program :
      TwoThreeFactorizationProgram
        (categoryData := categoryData)
        algebra beforeDiagram afterDiagram before after)
    (before_raw_sound :
      before.rawNumerator =
        categoryData.closedScalar (Diagram.eval C beforeDiagram))
    (after_raw_sound :
      after.rawNumerator =
        categoryData.closedScalar (Diagram.eval C afterDiagram)) :
    TwoThreeLocalCalculation profile where
  unknotValue := algebra.twoThreeUnknotValue
  before := before
  after := after
  counts_sound := program.counts_sound
  unlinked_unknotted_zero_framed :=
    beforeDiagram =
      closedTensorDiagram program.localUnknotDiagram afterDiagram
  unlink_witness := program.diagram_factorization
  disjoint_union_sound := fun _ => by
    rw [before_raw_sound, program.diagram_factorization,
      categoryData.closed_tensor_multiplicative,
      program.local_unknot_scalar, after_raw_sound]
  pivotal_dimension_preserved :=
    algebra.pivotal_dimension_preserved

end TwoThreeFactorizationProgram

/-- Derive a hash-bound local binding without free move or presentation IDs. -/
def localEvaluationBinding
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target)
    (certificateHash : String)
    (hashShape : RawPresentation.sha256Shape certificateHash = true) :
    LocalEvaluationBinding move where
  moveId := tableTwoMoveId move
  move_id_sound := rfl
  sourcePresentationHash := source.formal.pinnedSourceHash
  source_hash_sound := rfl
  targetPresentationHash := target.formal.pinnedSourceHash
  target_hash_sound := rfl
  graphicalCertificateHash := certificateHash
  graphical_certificate_hash_shape := hashShape

/--
The only accepted lower-level compiler for the eight graphical move families.

Every field returns an interpreted program or factorization, never an
`EvaluatedTableTwoStep` and never a final normalized equality.
-/
structure SourceBoundGraphicalMoveCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (presentationCompiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2)
    (algebra : RibbonKirbyGraphicalAlgebra.Input categoryData) where
  framedIsotopy :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .framedIsotopy source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      FramedIsotopyRealization algebra metadata
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
  oneOverOne :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .oneOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      OneOverOneRealization algebra orientation metadata
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
  twoOverOne :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .twoOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      TwoOverOneRealization algebra orientation metadata
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
  twoOverTwo :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .twoOverTwo source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      TwoOverTwoRealization algebra orientation metadata
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
  oneTwoBirth :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .oneTwoBirth source target) →
    (counts_sound : target.counts = source.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      OneTwoFactorizationProgram
        (categoryData := categoryData) algebra.cancellation
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).evaluationState
          (transport.targetClass alpha))
        ((presentationCompiler.decorate source).evaluationState alpha)
  oneTwoDeath :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .oneTwoDeath source target) →
    (counts_sound : source.counts = target.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      OneTwoFactorizationProgram
        (categoryData := categoryData) algebra.cancellation
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
        ((presentationCompiler.decorate source).evaluationState alpha)
        ((presentationCompiler.decorate target).evaluationState
          (transport.targetClass alpha))
  twoThreeBirth :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .twoThreeBirth source target) →
    (counts_sound : target.counts = source.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      TwoThreeFactorizationProgram
        (categoryData := categoryData) algebra.cancellation
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).evaluationState
          (transport.targetClass alpha))
        ((presentationCompiler.decorate source).evaluationState alpha)
  twoThreeDeath :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .twoThreeDeath source target) →
    (counts_sound : source.counts = target.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      TwoThreeFactorizationProgram
        (categoryData := categoryData) algebra.cancellation
        ((presentationCompiler.decorate source).diagram alpha)
        ((presentationCompiler.decorate target).diagram
          (transport.targetClass alpha))
        ((presentationCompiler.decorate source).evaluationState alpha)
        ((presentationCompiler.decorate target).evaluationState
          (transport.targetClass alpha))
  graphicalCertificateHash :
    {kind : RecipeKind} →
    {source target : SpecialKirbyPresentation manifold H2} →
      TableTwoMoveMetadata kind source target → H2 → String
  graphical_certificate_hash_shape :
    {kind : RecipeKind} →
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata kind source target) →
    (alpha : H2) →
      RawPresentation.sha256Shape
        (graphicalCertificateHash metadata alpha) = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace SourceBoundGraphicalMoveCompiler

/-- Exhaustively compile the eight source-bound local program families. -/
noncomputable def compile
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentationCompiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2}
    {algebra : RibbonKirbyGraphicalAlgebra.Input categoryData}
    (compiler :
      SourceBoundGraphicalMoveCompiler
        categoryData manifold H2 presentationCompiler algebra)
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target)
    (alpha : H2) :
    EvaluatedTableTwoStep categoryData
      (presentationCompiler.decorate source)
      (presentationCompiler.decorate target) move alpha := by
  cases move with
  | framedIsotopy metadata counts transport =>
      let realization :=
        compiler.framedIsotopy metadata counts transport alpha
      exact EvaluatedTableTwoStep.framedIsotopy
        metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        realization.program.toGeneratedIsotopy
  | oneOverOne orientation metadata counts transport =>
      let realization :=
        compiler.oneOverOne orientation metadata counts transport alpha
      exact EvaluatedTableTwoStep.oneOverOne
        orientation metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        realization.slide realization.kind_sound
        realization.orientation_sound realization.move_id_sound
        realization.source_hash_sound realization.target_hash_sound
  | twoOverOne orientation metadata counts transport =>
      let realization :=
        compiler.twoOverOne orientation metadata counts transport alpha
      exact EvaluatedTableTwoStep.twoOverOne
        orientation metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        realization.slide realization.kind_sound
        realization.orientation_sound realization.move_id_sound
        realization.source_hash_sound realization.target_hash_sound
  | twoOverTwo orientation metadata counts transport =>
      let realization :=
        compiler.twoOverTwo orientation metadata counts transport alpha
      exact EvaluatedTableTwoStep.twoOverTwo
        orientation metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        realization.slide realization.orientation_sound
        realization.move_id_sound realization.source_hash_sound
        realization.target_hash_sound
  | oneTwoBirth metadata counts transport =>
      let program :=
        compiler.oneTwoBirth metadata counts transport alpha
      exact EvaluatedTableTwoStep.oneTwoBirth
        metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        (program.toCalculation
          ((presentationCompiler.decorate target).raw_numerator_sound
            (transport.targetClass alpha))
          ((presentationCompiler.decorate source).raw_numerator_sound alpha))
        rfl rfl
  | oneTwoDeath metadata counts transport =>
      let program :=
        compiler.oneTwoDeath metadata counts transport alpha
      exact EvaluatedTableTwoStep.oneTwoDeath
        metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        (program.toCalculation
          ((presentationCompiler.decorate source).raw_numerator_sound alpha)
          ((presentationCompiler.decorate target).raw_numerator_sound
            (transport.targetClass alpha)))
        rfl rfl
  | twoThreeBirth metadata counts transport =>
      let program :=
        compiler.twoThreeBirth metadata counts transport alpha
      exact EvaluatedTableTwoStep.twoThreeBirth
        metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        (program.toCalculation
          ((presentationCompiler.decorate target).raw_numerator_sound
            (transport.targetClass alpha))
          ((presentationCompiler.decorate source).raw_numerator_sound alpha))
        rfl rfl
  | twoThreeDeath metadata counts transport =>
      let program :=
        compiler.twoThreeDeath metadata counts transport alpha
      exact EvaluatedTableTwoStep.twoThreeDeath
        metadata counts transport alpha
        (localEvaluationBinding _
          (compiler.graphicalCertificateHash metadata alpha)
          (compiler.graphical_certificate_hash_shape metadata alpha))
        (program.toCalculation
          ((presentationCompiler.decorate source).raw_numerator_sound alpha)
          ((presentationCompiler.decorate target).raw_numerator_sound
            (transport.targetClass alpha)))
        rfl rfl

end SourceBoundGraphicalMoveCompiler

end TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation
