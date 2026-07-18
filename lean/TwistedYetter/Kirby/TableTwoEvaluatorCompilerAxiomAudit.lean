import TwistedYetter.Kirby.FourManifoldInvariantTarget

/-!
# Kernel axiom audit for the exhaustive evaluator compiler

The compiler mechanism itself must depend only on standard Lean axioms.  The
separate source-backed topology domain axiom is intentionally not used here.
-/

#print axioms TwistedYetter.Kirby.EvaluatorCompiler.compiler_case_count
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_framedIsotopy
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_oneOverOne
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_twoOverOne
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_twoOverTwo
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_oneTwoBirth
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_oneTwoDeath
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_twoThreeBirth
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.compile_twoThreeDeath
#print axioms TwistedYetter.Kirby.EvaluatorCompiler.TableTwoEvaluatorCompiler.toPrescription
#print axioms TwistedYetter.Kirby.FourManifoldInvariantTarget.FourManifoldInvariantInputs.prescription
