import TwistedYetter.Kirby.ConcreteMarkedPairAssembly

/-!
# Source-bound geometric H2 compiler

The older `GeometricMarkedH2Compiler` accepts the final statement that each
ambient `H2` transport is the identity. This module replaces that direct
field at the target boundary with a more local certificate.

For every exact source-backed topology move, the certificate supplies:

* the actual handle-chain homotopy equivalence;
* the exact shared recipe identity; and
* the commutative square between chain homology and the two presentations'
  geometric `H2` coordinates.

The identity ambient transport is then a theorem. No map on `H2` and no final
identity equality is supplied independently.
-/

namespace TwistedYetter.Kirby.SourceBoundGeometricH2Compilation

open TwistedYetter.Kirby.ConcreteMarkedPairAssembly
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uH

/-- Exact recipe identity carried by a bare topology move. -/
def topologicalMoveRecipeId
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TopologicalTableTwoMove source target) : String :=
  match move with
  | .framedIsotopy metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .oneOverOne _ metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .twoOverOne _ metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .twoOverTwo _ metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .oneTwoBirth metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .oneTwoDeath metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .twoThreeBirth metadata _ =>
      metadata.recipe.chainCompilerRecipeId
  | .twoThreeDeath metadata _ =>
      metadata.recipe.chainCompilerRecipeId

/--
One exact chain-level realization of one source-bound topology recipe.

`coordinate_naturality` says that first applying the chain-induced map and
then reading target geometric coordinates equals reading source geometric
coordinates directly.
-/
structure SourceBoundChainMoveCertificate
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TopologicalTableTwoMove source target) where
  recipeId : String
  recipe_id_sound : recipeId = topologicalMoveRecipeId move
  chainEquivalence :
    HandleChainEquivalence source.handleChain target.handleChain
  coordinate_naturality :
    chainEquivalence.secondHomologyAddEquiv.trans
        target.h2ModelEquiv =
      source.h2ModelEquiv
  chainCertificateHash : String
  chain_certificate_hash_shape :
    RawPresentation.sha256Shape chainCertificateHash = true

namespace SourceBoundChainMoveCertificate

/-- The marked transport is forced by the certificate's chain equivalence. -/
noncomputable def transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    {move : TopologicalTableTwoMove source target}
    (certificate : SourceBoundChainMoveCertificate move) :
    MarkedH2Transport source target where
  chainEquivalence := certificate.chainEquivalence

/--
The coordinate square forces the ambient `H2` map to be the identity.

This is the theorem that was previously accepted directly as a compiler
field.
-/
theorem transport_homologyAddEquiv_eq_refl
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    {move : TopologicalTableTwoMove source target}
    (certificate : SourceBoundChainMoveCertificate move) :
    certificate.transport.homologyAddEquiv = AddEquiv.refl H2 := by
  ext alpha
  change
    target.h2ModelEquiv
        (certificate.chainEquivalence.secondHomologyAddEquiv
          (source.h2ModelEquiv.symm alpha)) =
      alpha
  have squareAt :=
    DFunLike.congr_fun certificate.coordinate_naturality
      (source.h2ModelEquiv.symm alpha)
  exact squareAt.trans (source.h2ModelEquiv.apply_symm_apply alpha)

end SourceBoundChainMoveCertificate

/--
The local chain compiler accepted by the final target.

Every output is indexed by the exact topology move and therefore by its exact
source-bound recipe.
-/
structure SourceBoundGeometricH2Compiler
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  compile :
    {source target : SpecialKirbyPresentation manifold H2} →
    (move : TopologicalTableTwoMove source target) →
      SourceBoundChainMoveCertificate move
  assemblyCertificateHash : String
  assembly_certificate_hash_shape :
    RawPresentation.sha256Shape assemblyCertificateHash = true
  sourceRefs : List String
  exactMarkedScope : String
  sourceScopeCaveat : String

namespace SourceBoundGeometricH2Compiler

/-- Derive the old local transport interface from exact move certificates. -/
noncomputable def localCompiler
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : SourceBoundGeometricH2Compiler manifold H2) :
    LocalMarkedH2Compiler manifold H2 where
  transport := fun move => (compiler.compile move).transport

/-- Every derived local ambient transport is the identity. -/
theorem local_transport_is_identity
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : SourceBoundGeometricH2Compiler manifold H2)
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TopologicalTableTwoMove source target) :
    (compiler.localCompiler.transport move).homologyAddEquiv =
      AddEquiv.refl H2 :=
  (compiler.compile move).transport_homologyAddEquiv_eq_refl

/-- Derive the existing marked-pair assembly compiler without a direct law. -/
noncomputable def toGeometricMarkedH2Compiler
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : SourceBoundGeometricH2Compiler manifold H2) :
    GeometricMarkedH2Compiler manifold H2 where
  localCompiler := compiler.localCompiler
  transport_is_identity := compiler.local_transport_is_identity
  assemblyCertificateHash := compiler.assemblyCertificateHash
  assembly_certificate_hash_shape :=
    compiler.assembly_certificate_hash_shape
  sourceRefs := compiler.sourceRefs
  exactMarkedScope := compiler.exactMarkedScope
  sourceScopeCaveat := compiler.sourceScopeCaveat

end SourceBoundGeometricH2Compiler

end TwistedYetter.Kirby.SourceBoundGeometricH2Compilation
