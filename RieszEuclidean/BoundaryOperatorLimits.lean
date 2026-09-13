import RieszEuclidean.StrongOperatorLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory Filter Topology
namespace RieszEuclidean
variable {ι X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H]
/-- A finite-measure spectral difference identity makes bounded convergent symbols Cauchy in H. -/
theorem cauchy_of_spectral_symbol_difference {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (v : ι → H) (σ : Measure X) [IsFiniteMeasure σ] (a : ι → X → ℂ)
    (ha : ∀ i, AEStronglyMeasurable (a i) σ)
    (hb : ∀ i, ∀ᵐ θ ∂σ, ‖a i θ‖ ≤ 1)
    {m : X → ℂ} (ht : ∀ᵐ θ ∂σ, Tendsto (fun i => a i θ) l (𝓝 (m θ)))
    (hdiff : ∀ i j, ‖v i - v j‖ ^ 2 = ∫ θ, ‖a i θ - a j θ‖ ^ 2 ∂σ) :
    Cauchy (l.map v) := by
  have hlim : Tendsto (fun p : ι × ι => ∫ θ, ‖a p.1 θ - a p.2 θ‖ ^ 2 ∂σ)
      (l ×ˢ l) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := σ) (l := l ×ˢ l) (F := fun p θ => ‖a p.1 θ - a p.2 θ‖ ^ 2)
      (f := fun _ : X => (0 : ℝ)) (fun _ => (4 : ℝ))
    apply (by simpa only [integral_zero] using hh) <;> clear hh
    · exact Filter.Eventually.of_forall fun p => ((ha p.1).sub (ha p.2)).norm.pow 2
    · exact Filter.Eventually.of_forall fun p => by
        filter_upwards [hb p.1, hb p.2] with θ h1 h2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [norm_sub_le (a p.1 θ) (a p.2 θ), norm_nonneg (a p.1 θ - a p.2 θ)]
    · exact integrable_const _
    · filter_upwards [ht] with θ hθ
      simpa using ((hθ.comp tendsto_fst).sub (hθ.comp tendsto_snd)).norm.pow 2
  rw [cauchy_map_iff']
  apply Metric.uniformity_basis_dist.tendsto_right_iff.mpr
  intro ε hε
  have he := hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [he] with p hp
  rw [dist_eq_norm]
  rw [← hdiff] at hp
  nlinarith [norm_nonneg (v p.1 - v p.2)]
/-- The spectral norm formula passes to a vector limit for bounded convergent symbols. -/
theorem limit_norm_of_spectral_symbols {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (v : ι → H) (σ : Measure X) [IsFiniteMeasure σ] (a : ι → X → ℂ)
    (ha : ∀ i, AEStronglyMeasurable (a i) σ)
    (hb : ∀ i, ∀ᵐ θ ∂σ, ‖a i θ‖ ≤ 1)
    {m : X → ℂ} (ht : ∀ᵐ θ ∂σ, Tendsto (fun i => a i θ) l (𝓝 (m θ)))
    (hnorm : ∀ i, ‖v i‖ ^ 2 = ∫ θ, ‖a i θ‖ ^ 2 ∂σ)
    {g : H} (hg : Tendsto v l (𝓝 g)) : ‖g‖ ^ 2 = ∫ θ, ‖m θ‖ ^ 2 ∂σ := by
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := σ) (l := l) (F := fun i θ => ‖a i θ‖ ^ 2)
    (f := fun θ => ‖m θ‖ ^ 2) (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun i => (ha i).norm.pow 2)
    (Filter.Eventually.of_forall fun i => by
      filter_upwards [hb i] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (a i θ)])
    (integrable_const _) (ht.mono fun θ hθ => hθ.norm.pow 2)
  apply tendsto_nhds_unique (hg.norm.pow 2)
  exact hi.congr' (Filter.Eventually.of_forall fun i => (hnorm i).symm)
variable [InnerProductSpace ℂ H]
/-- Boundary limits of already constructed spectral projections are orthogonal projections. -/
theorem exists_projection_of_spectral_difference_limit [CompleteSpace H]
    {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (P : ι → H →L[ℂ] H) (hP : ∀ i, ‖P i‖ ≤ 1)
    (hself : ∀ i, IsSelfAdjoint (P i)) (hidem : ∀ i, (P i).comp (P i) = P i)
    (σ : H → Measure X) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (a : ι → X → ℂ) (m : X → ℂ)
    (ha : ∀ f i, AEStronglyMeasurable (a i) (σ f))
    (hb : ∀ f i, ∀ᵐ θ ∂σ f, ‖a i θ‖ ≤ 1)
    (ht : ∀ f, ∀ᵐ θ ∂σ f, Tendsto (fun i => a i θ) l (𝓝 (m θ)))
    (hdiff : ∀ f i j, ‖P i f - P j f‖ ^ 2 = ∫ θ, ‖a i θ - a j θ‖ ^ 2 ∂σ f) :
    ∃ Q : H →L[ℂ] H, ‖Q‖ ≤ 1 ∧ IsSelfAdjoint Q ∧ Q.comp Q = Q ∧
      ∀ f, Tendsto (fun i => P i f) l (𝓝 (Q f)) := by
  have hc f : Cauchy (l.map (fun i => P i f)) := by
    letI := hfinite f
    exact cauchy_of_spectral_symbol_difference (fun i => P i f) (σ f) a
      (ha f) (hb f) (ht f) (hdiff f)
  have hi f : Tendsto (fun i => ‖P i (P i f) - P i f‖) l (𝓝 0) := by
    have he i : P i (P i f) = P i f := DFunLike.congr_fun (hidem i) f
    simpa only [he, _root_.sub_self, norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
  exact exists_projection_of_cauchy_contractions P hP hself hc hi
/-- Boundary limits of already constructed spectral projections are orthogonal projections. -/
theorem exists_projection_of_spectral_symbol_limit [CompleteSpace H]
    {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (P : ι → H →L[ℂ] H) (hP : ∀ i, ‖P i‖ ≤ 1)
    (hself : ∀ i, IsSelfAdjoint (P i)) (hidem : ∀ i, (P i).comp (P i) = P i)
    (σ : H → Measure X) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (a : ι → X → ℂ) (m : X → ℂ)
    (ha : ∀ f i, AEStronglyMeasurable (a i) (σ f))
    (hb : ∀ f i, ∀ᵐ θ ∂σ f, ‖a i θ‖ ≤ 1)
    (ht : ∀ f, ∀ᵐ θ ∂σ f, Tendsto (fun i => a i θ) l (𝓝 (m θ)))
    (hdiff : ∀ f i j, ‖P i f - P j f‖ ^ 2 = ∫ θ, ‖a i θ - a j θ‖ ^ 2 ∂σ f)
    (hnorm : ∀ f i, ‖P i f‖ ^ 2 = ∫ θ, ‖a i θ‖ ^ 2 ∂σ f) :
    ∃ Q : H →L[ℂ] H, ‖Q‖ ≤ 1 ∧ IsSelfAdjoint Q ∧ Q.comp Q = Q ∧
      (∀ f, Tendsto (fun i => P i f) l (𝓝 (Q f))) ∧
      ∀ f, ‖Q f‖ ^ 2 = ∫ θ, ‖m θ‖ ^ 2 ∂σ f := by
  obtain ⟨Q, hQ, hQs, hQi, hQt⟩ := exists_projection_of_spectral_difference_limit
    P hP hself hidem σ hfinite a m ha hb ht hdiff
  refine ⟨Q, hQ, hQs, hQi, hQt, fun f => ?_⟩
  letI := hfinite f
  exact limit_norm_of_spectral_symbols (fun i => P i f) (σ f) a
    (ha f) (hb f) (ht f) (hnorm f) (hQt f)
end RieszEuclidean
