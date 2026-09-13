import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
open Set Metric Topology
namespace RieszEuclidean
/-- Positive normalized functionals in the weak-star unit ball. -/
def meanFunctionals (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    Set (WeakDual ℝ C(X, ℝ)) :=
  {L | ‖WeakDual.toNormedDual L‖ ≤ 1 ∧ L 1 = 1 ∧ ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f}
/-- Normalization and positivity are closed conditions in the weak-star topology. -/
theorem isClosed_normalized_positive (X : Type*) [TopologicalSpace X] :
    IsClosed {L : WeakDual ℝ C(X, ℝ) | L 1 = 1 ∧ ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f} := by
  apply IsClosed.inter
  · exact isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  · convert (isClosed_iInter fun (f : C(X, ℝ)) => isClosed_iInter fun (_ : 0 ≤ f) =>
      isClosed_le (show Continuous (fun _ : WeakDual ℝ C(X, ℝ) => (0 : ℝ)) from continuous_const)
        (WeakDual.eval_continuous (𝕜 := ℝ) f)) using 1
    ext L
    simp only [mem_iInter, mem_setOf_eq]
    rfl
/-- The normalized positive functionals form a compact set. -/
theorem isCompact_meanFunctionals (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    IsCompact (meanFunctionals X) := by
  have hc := (WeakDual.isCompact_closedBall ℝ (0 : NormedSpace.Dual ℝ C(X, ℝ)) 1).inter_right
    (isClosed_normalized_positive X)
  simpa [meanFunctionals, Set.preimage, Metric.mem_closedBall, dist_zero_right] using hc
/-- Evaluation at a point is a normalized positive functional. -/
theorem evaluation_mem_meanFunctionals {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : X) : NormedSpace.Dual.toWeakDual (ContinuousMap.evalCLM ℝ x) ∈ meanFunctionals X := by
  refine ⟨?_, rfl, fun f hf => hf x⟩
  change ‖(ContinuousMap.evalCLM ℝ x : C(X, ℝ) →L[ℝ] ℝ)‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  simpa using f.norm_coe_le_norm x
/-- Any sequence of normalized positive functionals has a weak-star cluster point
that remains normalized and positive. -/
theorem meanFunctionals_clusterPt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : ℕ → WeakDual ℝ C(X, ℝ)) (hA : ∀ n, A n ∈ meanFunctionals X) :
    ∃ L ∈ meanFunctionals X, ClusterPt L (Filter.map A Filter.atTop) := by
  exact isCompact_meanFunctionals X (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hA))
/-- An asymptotically vanishing difference of evaluations vanishes at every weak-star
cluster point. -/
theorem mean_clusterPt_eq_of_tendsto_sub {X : Type*} [TopologicalSpace X]
    {A : ℕ → WeakDual ℝ C(X, ℝ)} {L : WeakDual ℝ C(X, ℝ)}
    (hL : ClusterPt L (Filter.map A Filter.atTop)) (f g : C(X, ℝ))
    (hfg : Filter.Tendsto (fun n => A n f - A n g) Filter.atTop (nhds 0)) : L f = L g := by
  have hc : Continuous (fun M : WeakDual ℝ C(X, ℝ) => M f - M g) :=
    (WeakDual.eval_continuous f).sub (WeakDual.eval_continuous g)
  have hp := (show MapClusterPt L Filter.atTop A from hL).continuousAt_comp hc.continuousAt
  have hz : ClusterPt (L f - L g) (nhds (0 : ℝ)) := hp.clusterPt.mono hfg
  exact sub_eq_zero.mp (eq_of_nhds_neBot hz)
/-- A compact weak-star limit preserves every asymptotic invariance identity at once. -/
theorem exists_invariant_mean_of_averages {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : ℕ → WeakDual ℝ C(X, ℝ)) (hA : ∀ n, A n ∈ meanFunctionals X)
    (T : I → C(X, ℝ) → C(X, ℝ))
    (hT : ∀ i f, Filter.Tendsto (fun n => A n (T i f) - A n f) Filter.atTop (nhds 0)) :
    ∃ L ∈ meanFunctionals X, ∀ i f, L (T i f) = L f := by
  obtain ⟨L, hL, hc⟩ := meanFunctionals_clusterPt A hA
  exact ⟨L, hL, fun i f => mean_clusterPt_eq_of_tendsto_sub hc (T i f) f (hT i f)⟩
end RieszEuclidean
