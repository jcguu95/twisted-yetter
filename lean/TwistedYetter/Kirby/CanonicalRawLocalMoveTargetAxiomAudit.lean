import TwistedYetter.Kirby.CanonicalRawLocalMoveTarget

/-!
# Axiom audit for the raw local move completion target

The completion is inhabited from eight separately named local geometry
inputs.  The exhaustive dispatcher and the compiler add no new axiom.
-/

#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.instructionOfMove
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.Instruction.rewrittenCore_ofRecipe_eq_target
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.canonicalEngine.generates_exact_target
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.localCycleCalculation_of_completion
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.standardCompletion

#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.Engine
#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.Completion
#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.standardCompletion
#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.currentStatus
