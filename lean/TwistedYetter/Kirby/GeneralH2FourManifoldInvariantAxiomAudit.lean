import TwistedYetter.Kirby.GeneralH2FourManifoldInvariant

/-!
# Axiom audit for the arbitrary-H2 four-manifold descent

`Completion` and `TopologyInput` are explicit theorem parameters.  This audit
therefore exposes only the category and source-backed handle-chain axioms used
inside the generated local calculation, not an assumed evaluator equality.
-/

#print axioms TwistedYetter.Kirby.GeneralH2FourManifoldInvariant.canonicalMarkedEvaluation_localInvariant
#print axioms TwistedYetter.Kirby.GeneralH2FourManifoldInvariant.evaluationOnCanonicalKirbyClass
#print axioms TwistedYetter.Kirby.GeneralH2FourManifoldInvariant.EvalC_diffeomorphism_invariant
#print axioms TwistedYetter.Kirby.GeneralH2FourManifoldInvariant.EvalC_on_presentation
