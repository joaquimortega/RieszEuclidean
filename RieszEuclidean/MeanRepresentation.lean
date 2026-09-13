import RieszEuclidean.CompactMeans
import RieszEuclidean.PositiveFunctionalMeasure
open MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported
namespace RieszEuclidean
/-- Restrict a continuous-function functional to compactly supported functions. -/
def meanToFunctional {X : Type*} [TopologicalSpace X]
    (L : WeakDual ℝ C(X, ℝ)) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := L f.toContinuousMap
  map_add' f g := L.map_add f.toContinuousMap g.toContinuousMap
  map_smul' r f := L.map_smul r f.toContinuousMap
/-- Normalized positive averages with vanishing translation defects supply an invariant
probability measure. Actual continuous-box averages must satisfy the hypotheses separately. -/
theorem exists_invariant_probability_of_averages {X I : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [HasOuterApproxClosed X]
    [MeasurableSpace X] [BorelSpace X]
    (A : ℕ → WeakDual ℝ C(X, ℝ)) (hA : ∀ n, A n ∈ meanFunctionals X)
    (T : I → C(X, X))
    (hT : ∀ i f, Filter.Tendsto (fun n => A n (f.comp (T i)) - A n f)
      Filter.atTop (nhds 0)) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ ∀ i, MeasurePreserving (T i) μ μ := by
  obtain ⟨L, hL, hInv⟩ := exists_invariant_mean_of_averages A hA (fun i f => f.comp (T i)) hT
  have hpos : ∀ f, 0 ≤ f → 0 ≤ meanToFunctional L f := fun f hf => hL.2.2 f.toContinuousMap hf
  have h1 : meanToFunctional L (ContinuousMap.liftCompactlySupported (ContinuousMap.const X 1)) = 1 :=
    hL.2.1
  refine ⟨RealRMK.rieszMeasure hpos, rieszMeasure_isProbability hpos h1, fun i => ?_⟩
  apply rieszMeasure_measurePreserving hpos h1 (T i)
  intro f
  exact hInv i f.toContinuousMap
end RieszEuclidean
