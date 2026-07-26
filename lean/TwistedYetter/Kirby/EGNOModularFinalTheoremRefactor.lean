import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
import TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

/-!
# Internal implementation of the modular presentation evaluation

Status: historical implementation route.  This is not the public theorem
entry point.  See `Kirby.Final.TwistedYetter`.

This module removes the shared `H2` shell from the public marking type.

For a special Kirby presentation `P`, the marking type is exactly the second
homology of `P.handleChain`. An elementary Table 2 move acts by the homology
map induced by its stored chain homotopy equivalence. The older shared-coordinate
compiler is used only through each presentation's pinned `h2ModelEquiv`.

This is an implementation/evidence module. Its compiler and hash fields do
not belong to the paper-facing theorem interface in
`ModularFourManifoldInvariantFinalTarget`.

The six standard graphical laws are fixed by the named literature axioms in
`LiteratureBackedModularGraphicalEnvironment`. The remaining compiler fields
connect serialized presentations and the eight local move constructors to
those laws. They are proof-producing implementation data, not mathematical
parameters of the eventual theorem.
-/

namespace TwistedYetter.Kirby.EGNOModularFinalTheoremRefactor

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.Presentation

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance refactorSelectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/--
The concrete marked calculus whose marking on `P` is `H₂(P.handleChain)`.

The ambient `H2` parameter remains only because the legacy presentation schema
stores a coordinate equivalence to it. It is not the public marking type.
-/
noncomputable def handleHomologyCalculus
    (H2 : Type) [AddCommGroup H2] :
    HandlePresentationTheory.{1, 0, 1} where
  Presentation := SpecialKirbyPresentation H2
  Marking := fun presentation =>
    presentation.handleChain.SecondHomology
  ElementaryMove := fun source target =>
    TableTwoMove source target
  transport := fun move =>
    move.homologyTransport.chainEquivalence.secondHomologyAddEquiv

/--
The old ambient-coordinate transport is exactly the chain-induced transport,
conjugated by the two presentations' coordinate equivalences.
-/
theorem h2ModelEquiv_transport
    {H2 : Type} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TableTwoMove source target)
    (alpha : source.handleChain.SecondHomology) :
    target.h2ModelEquiv
        ((handleHomologyCalculus H2).transport move alpha) =
      move.homologyTransport.targetClass
        (source.h2ModelEquiv alpha) := by
  simp [handleHomologyCalculus, MarkedH2Transport.targetClass,
    MarkedH2Transport.homologyEquiv,
    MarkedH2Transport.homologyAddEquiv]

/--
All source-specific data needed to construct `Eval_C`.

The six global graphical laws are deliberately absent from the fields. They
are fixed once and for all by `LiteratureBackedModularGraphicalEnvironment`.
The two compiler fields remain because they certify how a concrete serialized
Kirby presentation and each of its eight local move constructors instantiate
the general graphical calculus.
-/
structure CompiledEvaluatorEvidence
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (H2 : Type) [AddCommGroup H2] where
  evidenceBinding :
    LiteratureBackedModularGraphicalEnvironment.EvidenceBinding
  automorphism : TensorIdentityAutomorphism C
  presentationCompiler :
    PresentationCompiler 𝒞.premodular
      (LiteratureBackedModularGraphicalEnvironment.build
        𝒞 evidenceBinding)
      automorphism H2
  localMoveCompiler :
    LocalMoveCompiler 𝒞.premodular
      (LiteratureBackedModularGraphicalEnvironment.build
        𝒞 evidenceBinding)
      automorphism H2 presentationCompiler
  assemblyCertificateHash : String
  assembly_certificate_hash_shape :
    RawPresentation.sha256Shape assemblyCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace CompiledEvaluatorEvidence

/--
The internally compiled evaluation on each presentation's handle homology.

This is intentionally not named `EvalC`: the public mathematical `Eval_C`
will be introduced only after its canonical construction no longer requires a
caller-supplied compiler.
-/
noncomputable def compiledEvaluation
    {H2 : Type} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (inputs : CompiledEvaluatorEvidence 𝒞 H2) :
    PresentationEvaluation (handleHomologyCalculus H2) K where
  value := fun presentation alpha =>
    inputs.presentationCompiler.value presentation
      (presentation.h2ModelEquiv alpha)

/--
The concrete evaluator preserves every elementary Table 2 move.

The proof changes coordinates only at the boundary: it evaluates the source
handle class in the old coordinates, invokes the source-specific local compiler
against the six fixed literature-backed graphical laws, and rewrites the target
coordinate by `h2ModelEquiv_transport`.
-/
theorem evalC_local_move_invariant
    {H2 : Type} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    (inputs : CompiledEvaluatorEvidence 𝒞 H2) :
    IsInvariantUnderElementaryMoves
      (compiledEvaluation 𝒞 inputs) := by
  intro source target move alpha
  change
    inputs.presentationCompiler.value source (source.h2ModelEquiv alpha) =
      inputs.presentationCompiler.value target
        (target.h2ModelEquiv
          ((handleHomologyCalculus H2).transport move alpha))
  rw [h2ModelEquiv_transport move alpha]
  exact inputs.localMoveCompiler.move_invariant move
    (source.h2ModelEquiv alpha)

end CompiledEvaluatorEvidence

/--
The implementation evidence produces a well-defined scalar on the marked
Kirby quotient.

This is the strongest conclusion available before supplying the separate
closed-four-manifold correspondence. It does not use the old
`representsFixedManifold` witness.
-/
noncomputable def compiledEvaluationOnKirbyClass
    {H2 : Type} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    (inputs : CompiledEvaluatorEvidence 𝒞 H2) :
    (handleHomologyCalculus H2).KirbyClass → K :=
  (inputs.compiledEvaluation 𝒞).descendToKirbyClass
    inputs.evalC_local_move_invariant

/--
The quotient evaluation agrees definitionally with the compiled presentation
formula.
-/
theorem compiledEvaluationOnKirbyClass_mk
    {H2 : Type} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    (inputs : CompiledEvaluatorEvidence 𝒞 H2)
    (marked :
      (handleHomologyCalculus H2).MarkedPresentation) :
    compiledEvaluationOnKirbyClass inputs (Quotient.mk _ marked) =
      (inputs.compiledEvaluation 𝒞).markedValue marked :=
  rfl

/-!
There is intentionally no declaration named `EvalC` and no final theorem in
this implementation module.  Those names become honest only after two
remaining constructions are fixed without caller-supplied engineering data:

* the canonical event-by-event definition of `Eval_C` from `𝒞` and the
  twisting automorphism; and
* the standard topology correspondence from the admitted Kirby quotient to
  marked closed oriented smooth four-manifolds, including the omitted
  3-handle completion/uniqueness theorem.

The generic descent theorem for the second step is
`ModularFourManifoldInvariantFinalTarget.fourManifoldInvariant_on_presentation`.
Its quotient equivalence is derived from separately supplied move soundness,
presentation existence, and Kirby--Cerf completeness; no caller supplies an
omnibus equivalence.
-/

end TwistedYetter.Kirby.EGNOModularFinalTheoremRefactor
