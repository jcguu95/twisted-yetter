import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

def invalidIncompleteDistribution : DistributionCertificate where
  expectedSectorCount := 4
  observedSectorCount := 3
  valueBucketCounts := [3]
  projectorBucketCounts := [3]
  observed_eq_expected := rfl
  value_bucket_sum := by norm_num
  projector_bucket_sum := by norm_num
