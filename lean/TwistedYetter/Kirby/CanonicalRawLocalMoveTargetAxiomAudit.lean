import TwistedYetter.Kirby.CanonicalRawLocalMoveTarget

/-!
# Axiom audit for the raw local move completion target

The conditional replacement adds no new project axiom and does not depend on
`standardLocalCycleCalculation`.  This audit does not claim that
`Completion` is inhabited.
-/

#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.instructionOfMove
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.Instruction.rewrittenCore_ofRecipe_eq_target
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.canonicalEngine.generates_exact_target
#print axioms TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.localCycleCalculation_of_completion

#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.Engine
#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.Completion
#check TwistedYetter.Kirby.CanonicalRawLocalMoveTarget.currentStatus
