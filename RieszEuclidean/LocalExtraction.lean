import RieszEuclidean.SeparatedConfigurations
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sequences
open Filter TopologicalSpace
namespace RieszEuclidean
/-- Restrict a closed configuration to a compact region as a closed subset of that region. -/
def compactRestriction {d : ℕ} (K Γ : Set (Euclidean d)) (hΓ : IsClosed Γ) : Closeds K :=
  ⟨{x : K | (x : Euclidean d) ∈ Γ}, hΓ.preimage continuous_subtype_val⟩
/-- On a fixed compact region a sequence of closed configurations has a Hausdorff-convergent subsequence. -/
theorem compactRestriction_subsequence {d : ℕ} (K : Set (Euclidean d)) (hK : IsCompact K)
    (Γ : ℕ → Set (Euclidean d)) (hΓ : ∀ n, IsClosed (Γ n)) :
    ∃ C : Closeds K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => compactRestriction K (Γ (φ n)) (hΓ (φ n))) atTop (nhds C) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact CompactSpace.tendsto_subseq (fun n => compactRestriction K (Γ n) (hΓ n))
/-- One subsequence converges on every integer-radius compact window simultaneously. -/
theorem compactRestrictions_diagonal {d : ℕ}
    (Γ : ℕ → Set (Euclidean d)) (hΓ : ∀ n, IsClosed (Γ n)) :
    ∃ C : ∀ k : ℕ, Closeds (Metric.closedBall (0 : Euclidean d) (k + 1 : ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ,
        Tendsto (fun n => compactRestriction (Metric.closedBall 0 (k + 1 : ℝ))
          (Γ (φ n)) (hΓ (φ n))) atTop (nhds (C k)) := by
  letI (k : ℕ) : CompactSpace (Metric.closedBall (0 : Euclidean d) (k + 1 : ℝ)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 _)
  obtain ⟨C, φ, hφ, hc⟩ := CompactSpace.tendsto_subseq
    (fun n (k : ℕ) => compactRestriction (Metric.closedBall 0 (k + 1 : ℝ)) (Γ n) (hΓ n))
  exact ⟨C, φ, hφ, fun k => ((continuous_apply k).tendsto C).comp hc⟩
end RieszEuclidean
