import TwistedYetter.Kirby.BoundaryDerivedHandleChain
import TwistedYetter.Kirby.HandleChainHomology

/-!
# A Mathlib handle-chain model derived from the boundary certificate

This module is the strict adapter between the boundary-derived topology and
the existing categorical evaluator.

The chain groups are the free integral modules on the handles.  The degree
two and degree three differentials are exactly the lower `d2` and the
boundary-derived `d3`; the end differentials are zero.  In particular, this
file does not accept a prebuilt `HandleChainModel`, a second-homology
equivalence, or an independently supplied `d3`.
-/

namespace TwistedYetter.Kirby.BoundaryDerivedHandleChainModel

open CategoryTheory
open CategoryTheory.Limits
open TwistedYetter.Kirby.BoundaryDerivedHandleChain
open TwistedYetter.Kirby.BoundaryDerivedHandleChain.CertifiedClosedPresentation
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.Presentation

noncomputable section

universe uD uIso uSlide uP uSphere

/-- The free handle module in degrees zero through four, and zero afterward. -/
def chainObject (counts : HandleCounts) : Nat → ModuleCat ℤ
  | 0 => HandleModule counts.h0
  | 1 => HandleModule counts.h1
  | 2 => HandleModule counts.h2
  | 3 => HandleModule counts.h3
  | 4 => HandleModule counts.h4
  | _ => HandleModule 0

/--
The handle differential.  Only `d2` and `d3` carry nonzero geometric data.
-/
def chainDifferential
    (counts : HandleCounts)
    (data :
      ClosedHandleBoundaryData counts.h1 counts.h2 counts.h3) :
    (degree : Nat) →
      chainObject counts (degree + 1) ⟶ chainObject counts degree
  | 0 => 0
  | 1 => ModuleCat.ofHom data.d2.toIntLinearMap
  | 2 => ModuleCat.ofHom data.d3.toIntLinearMap
  | 3 => 0
  | _ => 0

/-- The derived differential squares to zero in every degree. -/
theorem chainDifferential_squared
    (counts : HandleCounts)
    (data :
      ClosedHandleBoundaryData counts.h1 counts.h2 counts.h3)
    (degree : Nat) :
    chainDifferential counts data (degree + 1) ≫
        chainDifferential counts data degree =
      0 := by
  rcases degree with _ | _ | _ | _ | degree
  · simp [chainDifferential]
  · apply ModuleCat.hom_ext
    ext coefficient
    exact data.d2_d3_zero coefficient
  · simp [chainDifferential]
  · simp [chainDifferential]
  · simp [chainDifferential]

/-- The five-term chain complex forced by the derived boundary data. -/
def derivedComplex
    (counts : HandleCounts)
    (data :
      ClosedHandleBoundaryData counts.h1 counts.h2 counts.h3) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (chainObject counts)
    (chainDifferential counts data)
    (chainDifferential_squared counts data)

@[simp]
theorem derivedComplex_d2
    (counts : HandleCounts)
    (data :
      ClosedHandleBoundaryData counts.h1 counts.h2 counts.h3) :
    (derivedComplex counts data).d 2 1 =
      ModuleCat.ofHom data.d2.toIntLinearMap := by
  change
    (ChainComplex.of
      (chainObject counts)
      (chainDifferential counts data)
      (chainDifferential_squared counts data)).d (1 + 1) 1 =
        ModuleCat.ofHom data.d2.toIntLinearMap
  rw [ChainComplex.of_d]
  rfl

@[simp]
theorem derivedComplex_d3
    (counts : HandleCounts)
    (data :
      ClosedHandleBoundaryData counts.h1 counts.h2 counts.h3) :
    (derivedComplex counts data).d 3 2 =
      ModuleCat.ofHom data.d3.toIntLinearMap := by
  change
    (ChainComplex.of
      (chainObject counts)
      (chainDifferential counts data)
      (chainDifferential_squared counts data)).d (2 + 1) 2 =
        ModuleCat.ofHom data.d3.toIntLinearMap
  rw [ChainComplex.of_d]
  rfl

/--
Hashes for the concrete derivation.  These fields record provenance only;
they do not influence any chain group or differential.
-/
structure DerivationProvenance where
  chainSnapshotHash : String
  chain_snapshot_hash_shape :
    RawPresentation.sha256Shape chainSnapshotHash = true
  boundaryMatrixCertificateHash : String
  boundary_matrix_certificate_hash_shape :
    RawPresentation.sha256Shape boundaryMatrixCertificateHash = true
  basisCertificateHash : String
  basis_certificate_hash_shape :
    RawPresentation.sha256Shape basisCertificateHash = true

/--
Build the evaluator's existing `HandleChainModel` from the derived complex.
-/
def derivedHandleChainModel
    (counts : HandleCounts)
    (data :
      ClosedHandleBoundaryData counts.h1 counts.h2 counts.h3)
    (provenance : DerivationProvenance) :
    HandleChainModel counts where
  complex := derivedComplex counts data
  degreeZeroBasis := Iso.refl _
  degreeOneBasis := Iso.refl _
  degreeTwoBasis := Iso.refl _
  degreeThreeBasis := Iso.refl _
  degreeFourBasis := Iso.refl _
  higherDegreeZero := by
    intro degree lowerBound
    rcases degree with _ | _ | _ | _ | _ | degree
    all_goals try omega
    change IsZero (HandleModule 0)
    exact ModuleCat.isZero_of_subsingleton _
  chainSnapshotHash := provenance.chainSnapshotHash
  chain_snapshot_hash_shape := provenance.chain_snapshot_hash_shape
  boundaryMatrixCertificateHash :=
    provenance.boundaryMatrixCertificateHash
  boundary_matrix_certificate_hash_shape :=
    provenance.boundary_matrix_certificate_hash_shape
  basisCertificateHash := provenance.basisCertificateHash
  basis_certificate_hash_shape :=
    provenance.basis_certificate_hash_shape

/--
Specialize the builder to a certified closed presentation.

The handle counts, `d2`, and `d3` are all computed from the presentation and
the global geometric semantics.  No presentation-local chain complex enters
as an argument.
-/
def CertifiedClosedPresentation.derivedHandleChainModel
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (presentation : CertifiedClosedPresentation lowerTheory)
    (provenance : DerivationProvenance) :
    HandleChainModel presentation.handleCounts :=
  BoundaryDerivedHandleChainModel.derivedHandleChainModel
    presentation.handleCounts
    (derivedHandleBoundaryData
      lowerBoundary sphereTransport intersection presentation)
    provenance

end

end TwistedYetter.Kirby.BoundaryDerivedHandleChainModel
