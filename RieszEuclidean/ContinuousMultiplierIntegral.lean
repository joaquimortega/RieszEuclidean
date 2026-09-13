import RieszEuclidean.StationaryComparison
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open MeasureTheory
namespace RieszEuclidean
variable {X : Type} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
/-- The concrete multiplier has its expected almost-everywhere representative. -/
theorem continuousL2Multiplier_coe (μ : Measure X) (m : C(X, ℂ)) (g : Lp ℂ 2 μ) :
    (continuousL2Multiplier μ m g : X → ℂ) =ᵐ[μ] fun x => m x * g x :=
  l2Multiplier_coe m m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => m.norm_coe_le_norm x) g
/-- Multiplication of a fixed L² vector is complex linear in the continuous coefficient. -/
noncomputable def continuousL2MultiplierVectorLinear (μ : Measure X) (g : Lp ℂ 2 μ) :
    C(X, ℂ) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun m := continuousL2Multiplier μ m g
  map_add' m n := by
    apply Lp.ext
    filter_upwards [continuousL2Multiplier_coe μ (m + n) g,
      continuousL2Multiplier_coe μ m g, continuousL2Multiplier_coe μ n g,
      Lp.coeFn_add (continuousL2Multiplier μ m g) (continuousL2Multiplier μ n g)] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    simp [add_mul]
  map_smul' c m := by
    apply Lp.ext
    filter_upwards [continuousL2Multiplier_coe μ (c • m) g,
      continuousL2Multiplier_coe μ m g, Lp.coeFn_smul c (continuousL2Multiplier μ m g)] with x h1 h2 h3
    simp only [RingHom.id_apply]
    rw [h1, h3, Pi.smul_apply, h2]
    simp [mul_assoc]
/-- The coefficient-to-vector multiplier map is continuous linear. -/
noncomputable def continuousL2MultiplierVectorCLM (μ : Measure X) (g : Lp ℂ 2 μ) :
    C(X, ℂ) →L[ℂ] Lp ℂ 2 μ :=
  { continuousL2MultiplierVectorLinear μ g with
    cont := (continuous_continuousL2Multiplier μ).clm_apply continuous_const }
/-- Evaluation of the coefficient-to-vector map is multiplication. -/
theorem continuousL2MultiplierVectorCLM_apply (μ : Measure X) (g : Lp ℂ 2 μ) (m : C(X, ℂ)) :
    continuousL2MultiplierVectorCLM μ g m = continuousL2Multiplier μ m g := rfl
/-- A continuous coefficient can be integrated before multiplying a fixed L² vector. -/
theorem integral_continuousL2Multiplier {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (μ : Measure X) (g : Lp ℂ 2 μ) {c : Y → C(X, ℂ)}
    (hc : Integrable c ν) :
    (∫ y, continuousL2Multiplier μ (c y) g ∂ν) = continuousL2Multiplier μ (∫ y, c y ∂ν) g := by
  exact (continuousL2MultiplierVectorCLM μ g).integral_comp_comm hc
omit [MeasurableSpace X] [BorelSpace X] in
/-- Evaluation commutes with the continuous-map integral. -/
theorem integral_continuousMap_apply {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {c : Y → C(X, ℂ)} (hc : Integrable c ν) (x : X) :
    (∫ y, c y ∂ν) x = ∫ y, c y x ∂ν := by
  exact ((ContinuousMap.evalCLM ℂ x).integral_comp_comm hc).symm
end RieszEuclidean
