import TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget

/-!
# Axiom audit for the pinned homological four-manifold target

The final theorem itself is a Lean descent proof.  Its two mathematical
boundaries occur as explicit arguments:

* `AdmissibleKirbyCerfTheorem`, containing only presentation existence and
  connectivity; and
* `IsInvariantAlongAdmissibleMovies`, supplied by the categorical local-move
  proof.

No cycle representative occurs in the type of `EvalC` or in the final
diffeomorphism-invariance statement.
-/

open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget

#print axioms AdmissibleKirbyCerfTheorem.EvalC_eq_presentation
#print axioms AdmissibleKirbyCerfTheorem.EvalC_diffeomorphism_invariant
#print axioms AdmissibleKirbyCerfTheorem.constructInvariant
#print axioms
  AdmissibleKirbyCerfTheorem.constructInvariant_EvalC_eq_presentation
