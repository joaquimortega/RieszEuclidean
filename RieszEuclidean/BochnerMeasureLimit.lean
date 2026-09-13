import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction ZeroAtInfty
namespace RieszEuclidean

/-- The bounded continuous map associated to a compactly supported test function. -/
def compactTestToBCF {X : Type*} [TopologicalSpace X] :
    C_c(X, ℝ) →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun f := ofCompactSupport f f.continuous f.hasCompactSupport
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Integration against a finite measure, as a bounded functional. -/
noncomputable def finiteMeasureFunctional {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    (X →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun c f => integral_smul c f }
    (μ.real univ) (fun f => f.norm_integral_le_mul_norm μ)

/-- A positive bounded functional on bounded continuous functions has a finite
Riesz measure representing all compactly supported tests. -/
theorem exists_finiteMeasure_of_positive_bounded {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (L : (X →ᵇ ℝ) →L[ℝ] ℝ) (hL : ∀ f, 0 ≤ f → 0 ≤ L f) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ univ ≤ ENNReal.ofReal ‖L‖ ∧
      ∀ f : C_c(X, ℝ), (∫ x, f x ∂μ) = L (compactTestToBCF f) := by
  let Λ := L.toLinearMap.comp compactTestToBCF
  have hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f := fun f hf => hL _ hf
  let μ := RealRMK.rieszMeasure hΛ
  have hmass : μ univ ≤ ENNReal.ofReal ‖L‖ := by
    letI : μ.Regular := by
      dsimp [μ, RealRMK.rieszMeasure]
      infer_instance
    rw [isOpen_univ.measure_eq_iSup_isCompact μ]
    refine iSup_le fun K => iSup_le fun _ => iSup_le fun hK => ?_
    obtain ⟨f, hf, _, hfc, hfb⟩ :=
      exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
    let g : C_c(X, ℝ) := ⟨f, hfc⟩
    calc μ K
      _ ≤ ENNReal.ofReal (Λ g) :=
        RealRMK.rieszMeasure_le_of_eq_one hΛ (fun x => (hfb x).1) hK hf
      _ ≤ ENNReal.ofReal ‖L‖ := by
        apply ENNReal.ofReal_le_ofReal
        calc Λ g
          _ ≤ ‖L (compactTestToBCF g)‖ := le_abs_self _
          _ ≤ ‖L‖ * ‖compactTestToBCF g‖ := L.le_opNorm _
          _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left
            ((BoundedContinuousFunction.norm_le (by norm_num)).mpr
              (fun x => by
                change ‖f x‖ ≤ 1
                simpa [Real.norm_eq_abs, abs_of_nonneg (hfb x).1] using (hfb x).2))
            (ContinuousLinearMap.opNorm_nonneg L)
          _ = ‖L‖ := mul_one _
  exact ⟨μ, ⟨lt_of_le_of_lt hmass ENNReal.ofReal_lt_top⟩, hmass,
    fun f => RealRMK.integral_rieszMeasure hΛ f⟩

/-- Vanishing continuous functions can be uniformly approximated by compact tests. -/
theorem exists_compactTest_uniform_approx {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (f : C₀(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X, ℝ), ‖f.toBCF - compactTestToBCF g‖ ≤ ε := by
  obtain ⟨K, hK, hfK⟩ := mem_cocompact.mp
    (tendsto_def.mp (ZeroAtInftyContinuousMapClass.zero_at_infty f) _
      (Metric.closedBall_mem_nhds (0 : ℝ) hε))
  obtain ⟨b, hbK, _, hbc, hb⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let g : C_c(X, ℝ) := ⟨f.toContinuousMap * b, hbc.mul_left⟩
  refine ⟨g, (BoundedContinuousFunction.norm_le hε.le).mpr fun x => ?_⟩
  change ‖f x - f x * b x‖ ≤ ε
  by_cases hx : x ∈ K
  · simp [hbK hx, hε.le]
  · have hf : ‖f x‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hfK hx
    have hbabs : |1 - b x| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      linarith [(hb x).1]
    calc ‖f x - f x * b x‖
      _ = ‖f x‖ * |1 - b x| := by rw [← mul_one_sub, norm_mul, Real.norm_eq_abs (1 - b x)]
      _ ≤ ε * 1 := mul_le_mul hf hbabs (abs_nonneg _) hε.le
      _ = ε := mul_one _

/-- Agreement on compact tests determines a bounded functional on every real
continuous function vanishing at infinity. -/
theorem boundedFunctional_eq_of_compactTests {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (L G : (X →ᵇ ℝ) →L[ℝ] ℝ)
    (h : ∀ g : C_c(X, ℝ), L (compactTestToBCF g) = G (compactTestToBCF g))
    (f : C₀(X, ℝ)) : L f.toBCF = G f.toBCF := by
  have hf : f.toBCF ∈ closure (range (compactTestToBCF (X := X))) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨g, hg⟩ := exists_compactTest_uniform_approx f (half_pos hε)
    refine ⟨compactTestToBCF g, mem_range_self g, ?_⟩
    rw [dist_eq_norm]
    exact hg.trans_lt (half_lt_self hε)
  exact (closure_minimal (by rintro _ ⟨g, rfl⟩; exact h g)
    (isClosed_eq L.continuous G.continuous)) hf

/-- Positive bounded functionals form a weak-star compact set. -/
theorem isCompact_positive_boundedFunctionals (X : Type*) [TopologicalSpace X] (M : ℝ) :
    IsCompact {L : WeakDual ℝ (X →ᵇ ℝ) |
      ‖WeakDual.toNormedDual L‖ ≤ M ∧ ∀ f, 0 ≤ f → 0 ≤ L f} := by
  have hp : IsClosed {L : WeakDual ℝ (X →ᵇ ℝ) | ∀ f, 0 ≤ f → 0 ≤ L f} := by
    convert (isClosed_iInter fun (f : X →ᵇ ℝ) => isClosed_iInter fun (_ : 0 ≤ f) =>
      isClosed_le (show Continuous (fun _ : WeakDual ℝ (X →ᵇ ℝ) => (0 : ℝ))
        from continuous_const) (WeakDual.eval_continuous (𝕜 := ℝ) f)) using 1
    ext L
    simp only [mem_iInter, mem_setOf_eq]
  have hc := (WeakDual.isCompact_closedBall ℝ
    (0 : NormedSpace.Dual ℝ (X →ᵇ ℝ)) M).inter_right hp
  simpa [Set.preimage, Metric.mem_closedBall, dist_zero_right] using hc

/-- Uniformly mass-bounded positive measures admit a finite vague limit along
some nontrivial filter refining the given sequence filter. -/
theorem exists_finiteMeasure_vague_limit {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → Measure X) [∀ n, IsFiniteMeasure (μs n)]
    {M : ℝ} (hM : 0 ≤ M) (hmass : ∀ n, (μs n).real univ ≤ M) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ univ ≤ ENNReal.ofReal M ∧
      ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
        ∀ f : C₀(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μs n) l (𝓝 (∫ x, f x ∂μ)) := by
  let A : ℕ → WeakDual ℝ (X →ᵇ ℝ) :=
    fun n => NormedSpace.Dual.toWeakDual (finiteMeasureFunctional (μs n))
  have hA : ∀ n, A n ∈ {L : WeakDual ℝ (X →ᵇ ℝ) |
      ‖WeakDual.toNormedDual L‖ ≤ M ∧ ∀ f, 0 ≤ f → 0 ≤ L f} := by
    intro n
    refine ⟨?_, fun f hf => integral_nonneg hf⟩
    apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro f
    exact (f.norm_integral_le_mul_norm (μs n)).trans
      (mul_le_mul_of_nonneg_right (hmass n) (norm_nonneg f))
  obtain ⟨L, hL, hc⟩ := isCompact_positive_boundedFunctionals X M
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hA) :
      Tendsto A atTop (𝓟 _))
  obtain ⟨μ, hμ, hμmass, hμtest⟩ :=
    exists_finiteMeasure_of_positive_bounded (WeakDual.toNormedDual L) hL.2
  let l := comap A (𝓝 L) ⊓ atTop
  have hl : l.NeBot := by
    rw [← Filter.map_neBot_iff (f := A), Filter.push_pull']
    exact hc
  have ht : Tendsto A l (𝓝 L) := tendsto_iff_comap.mpr inf_le_left
  refine ⟨μ, hμ, hμmass.trans (ENNReal.ofReal_le_ofReal hL.1), l, hl, inf_le_right, ?_⟩
  intro f
  letI := hμ
  have heq : (∫ x, f x ∂μ) = L f.toBCF :=
    (boundedFunctional_eq_of_compactTests (WeakDual.toNormedDual L)
      (finiteMeasureFunctional μ) (fun g => (hμtest g).symm) f).symm
  rw [heq]
  exact (WeakDual.eval_continuous f.toBCF).continuousAt.tendsto.comp ht

end RieszEuclidean
