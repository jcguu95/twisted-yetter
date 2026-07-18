import TwistedYetter.Kirby.SourceBoundGeometricH2Compiler

/-!
# Source-backed handle-chain naturality

This module isolates the standard homology-domain input needed by the marked
Kirby construction.

For an admitted local Kirby move, the cellular handle complexes before and
after the move are related by the familiar basis change or by insertion /
removal of a contractible adjacent-handle summand.  The induced map agrees
with the common geometric `H2(X)` coordinates.

That handle-theoretic statement is not reconstructed here from attaching
maps.  It is one explicit domain axiom below.  In particular, the axiom
returns the actual chain homotopy equivalence and its coordinate-naturality
square; it does not return the final identity map on `H2`.

The downstream identity is still a kernel-checked consequence of
`SourceBoundChainMoveCertificate.transport_homologyAddEquiv_eq_refl`.
-/

namespace TwistedYetter.Kirby.SourceBackedHandleChainNaturality

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation

universe uH

/-- Stable references delimiting the imported handle-homology fact. -/
def sourceRefs : List String :=
  [
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:baerenz-barrett-dichromatic-2018"
  ]

/-- Exact mathematical content imported at this boundary. -/
def exactScope : String :=
  "For each certified framed-isotopy, handle-slide, or adjacent cancelling "
    ++ "pair move between special handle presentations of one fixed closed "
    ++ "oriented four-manifold, the associated integral handle chain "
    ++ "complexes are chain-homotopy equivalent and the induced H2 map is "
    ++ "natural in the presentations' certified geometric H2 coordinates."

/-- What this domain axiom deliberately does not establish. -/
def sourceScopeCaveat : String :=
  "Lean does not reconstruct attaching maps, boundary matrices, elementary "
    ++ "basis changes, or contractible summand homotopies from the serialized "
    ++ "Kirby diagram in this module. The geometric meaning of each "
    ++ "presentation's H2 model certificate remains external input. This "
    ++ "axiom supplies no categorical evaluator equality and no final "
    ++ "handwritten identity map on H2."

/--
The complete imported handle-homology package.

Every result is indexed by the exact move and its shared recipe identity.  It
contains an actual `HandleChainEquivalence` and the geometric-coordinate
naturality square.  The assembly hash is provenance metadata; its shape proof
is kept in the same imported package so no native proof oracle is introduced.
-/
structure StandardHandleChainNaturalityInput
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    (H2 : Type uH) [AddCommGroup H2] where
  compile :
    {source target : SpecialKirbyPresentation manifold H2} →
    (move : TopologicalTableTwoMove source target) →
      SourceBoundChainMoveCertificate move
  assemblyCertificateHash : String
  assembly_certificate_hash_shape :
    RawPresentation.sha256Shape assemblyCertificateHash = true

/--
The sole handle-homology domain axiom.

It imports standard chain naturality plus content-addressed provenance.  It
does not import an evaluator equality or a final identity map on `H2`.
-/
axiom standardHandleChainNaturalityInput
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] :
    StandardHandleChainNaturalityInput (manifold := manifold) H2

/--
Canonical marked-homology compiler relative to the one explicit standard
handle-chain naturality axiom.
-/
noncomputable def sourceBackedGeometricH2Compiler
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] :
    SourceBoundGeometricH2Compiler manifold H2 where
  compile := (standardHandleChainNaturalityInput manifold H2).compile
  assemblyCertificateHash :=
    (standardHandleChainNaturalityInput manifold H2).assemblyCertificateHash
  assembly_certificate_hash_shape :=
    (standardHandleChainNaturalityInput manifold H2)
      |>.assembly_certificate_hash_shape
  sourceRefs := sourceRefs
  exactMarkedScope := exactScope
  sourceScopeCaveat := sourceScopeCaveat

/--
Every local ambient transport produced by the source-backed compiler is the
identity in the common geometric coordinates.

This theorem depends on the visible handle-chain domain axiom, but the
identity itself is derived rather than assumed.
-/
theorem local_transport_is_identity
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TopologicalTableTwoMove source target) :
    ((sourceBackedGeometricH2Compiler manifold H2).localCompiler.transport
      move).homologyAddEquiv =
        AddEquiv.refl H2 :=
  (sourceBackedGeometricH2Compiler manifold H2).local_transport_is_identity
    move

end TwistedYetter.Kirby.SourceBackedHandleChainNaturality
