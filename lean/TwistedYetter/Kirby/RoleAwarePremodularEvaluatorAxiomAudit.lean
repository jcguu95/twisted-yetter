import TwistedYetter.Kirby.PremodularUnitCutSlides
import TwistedYetter.Kirby.PremodularOneTwoCutCancellation
import TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams
import TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo
import TwistedYetter.Kirby.SourceBoundUnitCutGeometry

/-!
# Axiom audit for the role-aware premodular route

The expected non-kernel inputs are:

* EGNO's nonvanishing theorem for global dimension; and
* the category-neutral simultaneous dotted-cut topology fact.

The local 1/1, 2/1, and 1--2 algebra must not depend on modular killing or on
the eight legacy ordinary-window slide axioms.
-/

#print axioms
  TwistedYetter.Kirby.RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval

#print axioms
  TwistedYetter.Kirby.PremodularUnitCutSlides.twoOverOne_positive

#print axioms
  TwistedYetter.Kirby.PremodularUnitCutSlides.twoOverOne_negative

#print axioms
  TwistedYetter.Kirby.PremodularUnitCutSlides.oneOverOne

#print axioms
  TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams.twoOverOnePositiveBoundary_eval_eq_inContext

#print axioms
  TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams.twoOverOneNegativeBoundary_eval_eq_inContext

#print axioms
  TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams.oneOverOneBoundary_eval_eq_inContext

#print axioms
  TwistedYetter.Kirby.RoleAwareComponentDiagram.RoleAwareDiagram.GeneratedIsotopy.eval_eq

#print axioms
  TwistedYetter.Kirby.SourceBoundUnitCutGeometry.TwoOverOneMovie.augmented_eval_eq

#print axioms
  TwistedYetter.Kirby.SourceBoundUnitCutGeometry.OneOverOneMovie.augmented_eval_eq

#print axioms
  TwistedYetter.Kirby.SourceBoundUnitCutGeometry.twoOverOne_roleAwareLinearDiagram_eval_eq

#print axioms
  TwistedYetter.Kirby.SourceBoundUnitCutGeometry.oneOverOne_roleAwareLinearDiagram_eval_eq

#print axioms
  TwistedYetter.Kirby.SourceBoundUnitCutGeometry.twoOverOne_roleAwareCycleEval_eq

#print axioms
  TwistedYetter.Kirby.SourceBoundUnitCutGeometry.oneOverOne_roleAwareCycleEval_eq

#print axioms
  TwistedYetter.Kirby.PremodularOneTwoCutCancellation.specialOneTwoPairValue_eq_one

#print axioms
  TwistedYetter.Kirby.PremodularOneTwoCutCancellation.specialCutMeridianClosedValue_eq

#print axioms
  TwistedYetter.Kirby.PremodularOneTwoCutCancellation.specialCutMeridianSum_eq_one

#print axioms
  TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo.BirthTopology.rawNumerator_birth_factor

#print axioms
  TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo.BirthTopology.roleAwareCycleEval_birth

#print axioms
  TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo.BirthTopology.roleAwareCycleEval_death
