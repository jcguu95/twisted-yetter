import Mathlib.Data.List.Defs

/-!
# Independent human specification of a special Kirby diagram

This file is normative.  It was written from the human Kirby-diagram
definition without importing or inspecting this repository's presentation,
move, evaluator, Sage, or compatibility implementations.

A `SpecialKirbyDiagram` is deliberately not a complete handle presentation.
In particular, it does not contain attaching spheres for 3-handles.  It
contains:

* a dotted unlink encoding primal 1-handles;
* a framed link encoding primal 2-handles;
* a chosen simultaneous family of dotted spanning disks;
* the complete finite puncture and bunching data at those disks;
* a certificate that the boundary after the 0-, 1-, and 2-handles is
  `#^hThree (S¹ × S²)`.

The last certificate is exactly what permits closure by `hThree` 3-handles
and one 4-handle without storing their attaching spheres.

No component orientation, category, character, homology class, label,
coupon, projector, evaluation, or scalar normalization occurs here.
-/

namespace TwistedYetter.Kirby.Final.IndependentPresentationSpecification

universe uKnot uFramed uDisk uPoint uBunching uThreeManifold

/--
The geometric/topological primitives that this project does not reconstruct.

These names have their literal human meanings.  This boundary contains no
category-theoretic or evaluator data.
-/
structure KirbyGeometrySemantics where
  KnotInS3 : Type uKnot
  FramedKnotInS3 : Type uFramed
  EmbeddedDiskInS3 : Type uDisk
  IntersectionPoint : Type uPoint
  BunchingDatum : Type uBunching
  ClosedThreeManifold : Type uThreeManifold

  underlyingKnot : FramedKnotInS3 → KnotInS3
  diskBoundary : EmbeddedDiskInS3 → KnotInS3

  pairwiseDisjointKnots : List KnotInS3 → Prop
  pairwiseDisjointDisks : List EmbeddedDiskInS3 → Prop
  isUnlink : List KnotInS3 → Prop

  isTransverseIntersection :
    IntersectionPoint →
      EmbeddedDiskInS3 →
      FramedKnotInS3 →
      Prop

  bunchesExactly :
    BunchingDatum →
      List IntersectionPoint →
      Prop

  boundaryAfterZeroOneTwoHandles :
    {nOne nTwo : ℕ} →
      (Fin nOne → KnotInS3) →
      (Fin nTwo → FramedKnotInS3) →
      ClosedThreeManifold

  connectedSumS1TimesS2 :
    ℕ → ClosedThreeManifold

  orientationPreservingDiffeomorphic :
    ClosedThreeManifold →
      ClosedThreeManifold →
      Prop

/--
One occurrence of an ordinary framed component through one chosen dotted
spanning disk.

There is intentionally no sign here.  Intersection signs are introduced
only after choosing the handle-chain coordinate orientations in the separate
H₂ semantics.
-/
structure DottedPuncture
    (geometry : KirbyGeometrySemantics)
    (nTwo : ℕ) where
  point : geometry.IntersectionPoint
  ordinaryComponent : Fin nTwo

/--
All evaluation-relevant geometry at one dotted component.

`punctures` is an ordered finite list.  The soundness and completeness fields
state that it is exactly the geometric intersection set, with no omitted or
foreign puncture.  `bunching` fixes the finite tensor-word reading needed by
the later unit-only cut.
-/
structure DottedSpanningDiskData
    (geometry : KirbyGeometrySemantics)
    {nOne nTwo : ℕ}
    (dotted : Fin nOne → geometry.KnotInS3)
    (ordinary : Fin nTwo → geometry.FramedKnotInS3)
    (dottedComponent : Fin nOne) where
  disk : geometry.EmbeddedDiskInS3
  boundary_is_dotted :
    geometry.diskBoundary disk = dotted dottedComponent

  punctures :
    List (DottedPuncture geometry nTwo)
  punctures_no_duplicates :
    punctures.Nodup

  punctures_sound :
    ∀ puncture ∈ punctures,
      geometry.isTransverseIntersection
        puncture.point
        disk
        (ordinary puncture.ordinaryComponent)

  punctures_complete :
    ∀ (point : geometry.IntersectionPoint)
      (component : Fin nTwo),
      geometry.isTransverseIntersection
        point
        disk
        (ordinary component) →
      ∃ puncture ∈ punctures,
        puncture.point = point ∧
          puncture.ordinaryComponent = component

  bunching : geometry.BunchingDatum
  bunching_exact :
    geometry.bunchesExactly
      bunching
      (punctures.map DottedPuncture.point)

/--
The complete independent semantic input called a "special Kirby diagram" in
this project.

The unique primal 0-handle and unique primal 4-handle are part of the word
"special" and therefore are not mutable fields.  The actual 3-handle
attaching spheres are intentionally absent.
-/
structure SpecialKirbyDiagram
    (geometry : KirbyGeometrySemantics) where
  hOne : ℕ
  hTwo : ℕ
  hThree : ℕ

  dotted :
    Fin hOne → geometry.KnotInS3
  ordinary :
    Fin hTwo → geometry.FramedKnotInS3

  all_components_disjoint :
    geometry.pairwiseDisjointKnots
      (List.ofFn dotted ++
        List.ofFn (fun j => geometry.underlyingKnot (ordinary j)))

  dotted_is_unlink :
    geometry.isUnlink (List.ofFn dotted)

  dottedDisk :
    (i : Fin hOne) →
      DottedSpanningDiskData geometry dotted ordinary i

  dotted_disks_pairwise_disjoint :
    geometry.pairwiseDisjointDisks
      (List.ofFn fun i => (dottedDisk i).disk)

  closing_boundary_certificate :
    geometry.orientationPreservingDiffeomorphic
      (geometry.boundaryAfterZeroOneTwoHandles dotted ordinary)
      (geometry.connectedSumS1TimesS2 hThree)

/--
The mathematical meaning of the boundary certificate, kept explicit as a
named proposition for later audits.

It says only that the 0/1/2-handlebody can be closed by `hThree` 3-handles and
one 4-handle.  It contains no evaluator equality.
-/
def HasStandardClosedCompletion
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagram geometry) : Prop :=
  geometry.orientationPreservingDiffeomorphic
    (geometry.boundaryAfterZeroOneTwoHandles
      diagram.dotted
      diagram.ordinary)
    (geometry.connectedSumS1TimesS2 diagram.hThree)

theorem hasStandardClosedCompletion
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagram geometry) :
    HasStandardClosedCompletion diagram :=
  diagram.closing_boundary_certificate

end TwistedYetter.Kirby.Final.IndependentPresentationSpecification
