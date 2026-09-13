import RieszEuclidean.BoundaryFubini
import RieszEuclidean.BoundarySymbols
import RieszEuclidean.BoundaryOperatorLimits
import RieszEuclidean.ProjectionOrder
import RieszEuclidean.MovingComparison
open MeasureTheory Filter Topology
namespace RieszEuclidean
/-- The concrete translated-domain symbol is bounded and measurable. -/
theorem measurable_cutoffSymbol {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (t : Euclidean d) : Measurable (cutoffSymbol Ω t) :=
  (measurable_const.indicator hΩ).comp (measurable_const.add measurable_id)
/-- The actual cutoff indicator has norm at most one. -/
theorem norm_cutoffSymbol_le_one {d : ℕ} (Ω : Set (Euclidean d)) (t θ : Euclidean d) :
    ‖cutoffSymbol Ω t θ‖ ≤ 1 := by
  by_cases h : t + θ ∈ Ω <;> simp [cutoffSymbol, h]
/-- The square of an actual cutoff symbol is integrable against every finite measure. -/
theorem integrable_cutoffSymbol_norm_sq {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (t : Euclidean d) (σ : Measure (Euclidean d)) [IsFiniteMeasure σ] :
    Integrable (fun θ => ‖cutoffSymbol Ω t θ‖ ^ 2) σ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_cutoffSymbol hΩ t).aestronglyMeasurable.norm.pow 2)
  apply Filter.Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖cutoffSymbol Ω t θ‖ ^ 2 ≤ 1
  nlinarith [norm_cutoffSymbol_le_one Ω t θ, norm_nonneg (cutoffSymbol Ω t θ)]
/-- The interior boundary symbol has an integrable squared norm. -/
theorem integrable_interiorBoundarySymbol_norm_sq {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) {t : Euclidean d} (ht : t ∉ Ω)
    (σ : Measure (Euclidean d)) [IsFiniteMeasure σ] :
    Integrable (fun θ => ‖interiorBoundarySymbol Ω t θ‖ ^ 2) σ := by
  simp_rw [interiorBoundarySymbol_norm_sq Ω ht]
  exact (integrable_cutoffSymbol_norm_sq hΩ t σ).add
    ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton 0))
/-- Actual cutoffs approaching a clean boundary point from either ambient open side
have orthogonal strong limits with the paper's two limiting spectral norms. -/
theorem exists_boundary_cutoff_limits {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Ω G : Set (Euclidean d)} (hΩ : IsOpen Ω) (hG : volume Gᶜ = 0)
    {t₀ : Euclidean d} (hx : t₀ ∈ frontier Ω) (hout : t₀ ∈ closure (closure Ω)ᶜ)
    (σ : H → Measure (Euclidean d)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (hclean : ∀ f, σ f {θ | θ ≠ 0 ∧ t₀ + θ ∈ frontier Ω} = 0)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ s t f, ‖P s f - P t f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol Ω s θ - cutoffSymbol Ω t θ‖ ^ 2 ∂σ f) :
    ∃ (tm tp : ℕ → G) (Rm Rp : H →L[ℂ] H),
      (∀ n, (tm n : Euclidean d) ∉ closure Ω ∧ (tp n : Euclidean d) ∈ Ω) ∧
      Tendsto (fun n => (tm n : Euclidean d)) atTop (𝓝 t₀) ∧
      Tendsto (fun n => (tp n : Euclidean d)) atTop (𝓝 t₀) ∧
      (‖Rm‖ ≤ 1 ∧ IsSelfAdjoint Rm ∧ Rm.comp Rm = Rm) ∧
      (‖Rp‖ ≤ 1 ∧ IsSelfAdjoint Rp ∧ Rp.comp Rp = Rp) ∧
      (∀ f, Tendsto (fun n => P (tm n) f) atTop (𝓝 (Rm f))) ∧
      (∀ f, Tendsto (fun n => P (tp n) f) atTop (𝓝 (Rp f))) ∧
      (∀ f, ‖Rm f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t₀ θ‖ ^ 2 ∂σ f) ∧
      (∀ f, ‖Rp f‖ ^ 2 = ∫ θ, ‖interiorBoundarySymbol Ω t₀ θ‖ ^ 2 ∂σ f) := by
  obtain ⟨⟨tp', hp', htp⟩, ⟨tm', hm', htm⟩⟩ :=
    exists_conull_sequences_two_sides hG hΩ (frontier_subset_closure hx) hout
  let tp : ℕ → G := fun n => ⟨tp' n, (hp' n).1⟩
  let tm : ℕ → G := fun n => ⟨tm' n, (hm' n).1⟩
  have ha (t : ℕ → G) (f : H) (n : ℕ) :
      AEStronglyMeasurable (cutoffSymbol Ω (t n)) (σ f) :=
    (measurable_cutoffSymbol hΩ.measurableSet (t n)).aestronglyMeasurable
  have hb (t : ℕ → G) (f : H) (n : ℕ) :
      ∀ᵐ θ ∂σ f, ‖cutoffSymbol Ω (t n) θ‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_cutoffSymbol_le_one Ω (t n))
  obtain ⟨Rm, hRm, hRms, hRmi, hRmt, hRmn⟩ :=
    exists_projection_of_spectral_symbol_limit (l := atTop) (fun n => P (tm n))
      (fun n => (hP (tm n)).1) (fun n => (hP (tm n)).2.1)
      (fun n => (hP (tm n)).2.2) σ hfinite
      (fun n => cutoffSymbol Ω (tm n)) (cutoffSymbol Ω t₀) (ha tm) (hb tm)
      (fun f => cutoffSymbol_exterior_ae_tendsto hΩ hx (σ f) (hclean f) htm
        (fun n => (hm' n).2))
      (fun f i j => hdiff (tm i) (tm j) f) (fun f n => hnorm (tm n) f)
  obtain ⟨Rp, hRp, hRps, hRpi, hRpt, hRpn⟩ :=
    exists_projection_of_spectral_symbol_limit (l := atTop) (fun n => P (tp n))
      (fun n => (hP (tp n)).1) (fun n => (hP (tp n)).2.1)
      (fun n => (hP (tp n)).2.2) σ hfinite
      (fun n => cutoffSymbol Ω (tp n)) (interiorBoundarySymbol Ω t₀) (ha tp) (hb tp)
      (fun f => cutoffSymbol_interior_ae_tendsto hΩ hx (σ f) (hclean f) htp
        (fun n => (hp' n).2))
      (fun f i j => hdiff (tp i) (tp j) f) (fun f n => hnorm (tp n) f)
  exact ⟨tm, tp, Rm, Rp, fun n => ⟨(hm' n).2, (hp' n).2⟩, htm, htp,
    ⟨hRm, hRms, hRmi⟩, ⟨hRp, hRps, hRpi⟩, hRmt, hRpt, hRmn, hRpn⟩
/-- The two concrete boundary norm identities and Dirac invariant vector force strict inclusion. -/
theorem boundary_cutoff_ranges_strict {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) {t₀ : Euclidean d} (hx : t₀ ∉ Ω)
    (σ : H → Measure (Euclidean d)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (Rm Rp : H →L[ℂ] H) (hRms : IsSelfAdjoint Rm) (hRps : IsSelfAdjoint Rp)
    (hRmi : Rm.comp Rm = Rm) (hRpi : Rp.comp Rp = Rp)
    (hRmn : ∀ f, ‖Rm f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t₀ θ‖ ^ 2 ∂σ f)
    (hRpn : ∀ f, ‖Rp f‖ ^ 2 = ∫ θ, ‖interiorBoundarySymbol Ω t₀ θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0) :
    Rm u = 0 ∧ Rp u = u ∧
      LinearMap.range Rm.toLinearMap < LinearMap.range Rp.toLinearMap := by
  have horder (f : H) : ‖Rm f‖ ≤ ‖Rp f‖ := by
    letI := hfinite f
    have h := integral_mono (integrable_cutoffSymbol_norm_sq hΩ t₀ (σ f))
      (integrable_interiorBoundarySymbol_norm_sq hΩ hx (σ f))
      (boundarySymbol_norm_sq_le Ω hx)
    rw [← hRmn, ← hRpn] at h
    nlinarith [norm_nonneg (Rm f), norm_nonneg (Rp f)]
  have hm : ‖Rm u‖ ^ 2 = 0 := by
    rw [hRmn, hσu]
    exact (boundarySymbol_dirac_norms Ω hx).1
  have hp : ‖Rp u‖ ^ 2 = 1 := by
    rw [hRpn, hσu]
    exact (boundarySymbol_dirac_norms Ω hx).2
  have hmu : Rm u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hm)
  have hpu : ‖Rp u‖ = 1 := by nlinarith [norm_nonneg (Rp u)]
  exact ⟨hmu, projection_range_lt_of_unit_witness Rm Rp hRms hRps hRmi hRpi horder u hu hmu hpu⟩
/-- The boundary construction contradicts a common gap below one to a norm-continuous
family of actual orthogonal comparison projections. -/
theorem boundary_cutoffs_continuous_comparison_obstruction {d : ℕ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Ω G : Set (Euclidean d)} (hΩ : IsOpen Ω) (hG : volume Gᶜ = 0)
    {t₀ : Euclidean d} (hx : t₀ ∈ frontier Ω) (hout : t₀ ∈ closure (closure Ω)ᶜ)
    (σ : H → Measure (Euclidean d)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (hclean : ∀ f, σ f {θ | θ ≠ 0 ∧ t₀ + θ ∈ frontier Ω} = 0)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ s t f, ‖P s f - P t f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol Ω s θ - cutoffSymbol Ω t θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0)
    (M : Euclidean d → H →L[ℂ] H) (hM : ContinuousAt M t₀)
    (hMs : IsSelfAdjoint (M t₀)) (hMi : (M t₀).comp (M t₀) = M t₀)
    {γ : ℝ} (hγ : γ < 1) (hgap : ∀ t : G, ‖P t - M t‖ ≤ γ) : False := by
  obtain ⟨tm, tp, Rm, Rp, _, htm, htp, hRm, hRp, hRmt, hRpt, hRmn, hRpn⟩ :=
    exists_boundary_cutoff_limits hΩ hG hx hout σ hfinite hclean P hP hnorm hdiff
  have hxnot : t₀ ∉ Ω := by rw [hΩ.frontier_eq] at hx; exact hx.2
  obtain ⟨_, _, hstrict⟩ := boundary_cutoff_ranges_strict hΩ.measurableSet hxnot
    σ hfinite Rm Rp hRm.2.1 hRp.2.1 hRm.2.2 hRp.2.2 hRmn hRpn u hu hσu
  let Rminus : OrthProjection H := ⟨Rm, hRm.2.2, hRm.2.1.isSymmetric⟩
  let Rplus : OrthProjection H := ⟨Rp, hRp.2.2, hRp.2.1.isSymmetric⟩
  let Q : OrthProjection H := ⟨M t₀, hMi, hMs.isSymmetric⟩
  exact OrthProjection.moving_comparison_obstruction
    (fun n => P (tm n)) (fun n => P (tp n))
    (fun n => M (tm n)) (fun n => M (tp n)) Rminus Rplus Q γ hγ
    hRmt hRpt (hM.tendsto.comp htm) (hM.tendsto.comp htp)
    (fun n => hgap (tm n)) (fun n => hgap (tp n)) hstrict
end RieszEuclidean
