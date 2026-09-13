import Mathlib.MeasureTheory.Constructions.Polish.Basic
import RieszEuclidean.HullInvariantMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
open MeasureTheory
open scoped ENNReal
namespace RieszEuclidean
variable {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace Z] {μ : Measure X}
/-- Pullback along a measure-preserving map acts isometrically on complex L². -/
noncomputable def koopmanIsometry (T : C(X, X)) (hT : MeasurePreserving T μ μ) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ T hT
/-- A continuous family of measure-preserving maps gives a jointly continuous
pullback action on L², hence strong continuity. -/
theorem continuous_koopman [BorelSpace X] [R1Space X]
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] (T : Z → C(X, X)) (hT : Continuous T)
    (hμ : ∀ z, MeasurePreserving (T z) μ μ) :
    Continuous (fun p : Z × Lp ℂ 2 μ => koopmanIsometry (T p.1) (hμ p.1) p.2) := by
  exact continuous_snd.compMeasurePreservingLp (hT.comp continuous_fst)
    (fun p => hμ p.1) (by norm_num)
/-- Pullbacks compose in reverse order. -/
theorem koopmanIsometry_comp (S T : C(X, X))
    (hS : MeasurePreserving S μ μ) (hT : MeasurePreserving T μ μ)
    (f : Lp ℂ 2 μ) :
    koopmanIsometry S hS (koopmanIsometry T hT f) =
      koopmanIsometry (T.comp S) (hT.comp hS) f := by
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving (koopmanIsometry T hT f) hS
  have h₂ := hS.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hT)
  have h₃ := Lp.coeFn_compMeasurePreserving f (hT.comp hS)
  filter_upwards [h₁, h₂, h₃] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

/-- Inverse transformations give inverse pullbacks. -/
theorem koopmanIsometry_inverse (S T : C(X, X))
    (hS : MeasurePreserving S μ μ) (hT : MeasurePreserving T μ μ)
    (hST : ∀ x, T (S x) = x) (f : Lp ℂ 2 μ) :
    koopmanIsometry S hS (koopmanIsometry T hT f) = f := by
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving (koopmanIsometry T hT f) hS
  have h₂ := hS.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hT)
  filter_upwards [h₁, h₂] with x hx hy
  exact hx.trans (hy.trans (congrArg f (hST x)))
/-- An invertible measure-preserving transformation induces a unitary operator. -/
noncomputable def koopmanUnitary (S T : C(X, X))
    (hS : MeasurePreserving S μ μ) (hT : MeasurePreserving T μ μ)
    (hST : ∀ x, T (S x) = x) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (koopmanIsometry S hS)
    (fun f => ⟨koopmanIsometry T hT f, koopmanIsometry_inverse S T hS hT hST f⟩)

/-- Constants are fixed by measure-preserving pullback. -/
theorem koopmanIsometry_const [IsFiniteMeasure μ] (T : C(X, X))
    (hT : MeasurePreserving T μ μ) (c : ℂ) :
    koopmanIsometry T hT (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving (Lp.const 2 μ c) hT
  have h₂ := hT.quasiMeasurePreserving.ae (Lp.coeFn_const (μ := μ) (p := 2) c)
  have h₃ := Lp.coeFn_const (μ := μ) (p := 2) c
  filter_upwards [h₁, h₂, h₃] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)
omit [TopologicalSpace X] in
/-- The constant one is a unit vector for every probability measure. -/
theorem norm_stationary_one [IsProbabilityMeasure μ] :
    ‖Lp.const 2 μ (1 : ℂ)‖ = 1 := by
  rw [Lp.norm_const' (μ := μ) (p := 2) (c := (1 : ℂ)) (by norm_num) (by norm_num)]
  simp

namespace SeparatedConfiguration
/-- Each hull translation induces a unitary on the stationary L² space. -/
noncomputable def hullPullbackUnitary {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z : Euclidean d) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ := by
  let T : Euclidean d → C(hull Γ, hull Γ) := fun y =>
    ⟨hullTranslate hδ Γ y,
      (continuous_hullTranslate hδ Γ).comp (continuous_const.prodMk continuous_id)⟩
  apply koopmanUnitary (T z) (T (-z)) (hμ z) (hμ (-z))
  intro x
  apply Subtype.ext
  change translate (-z) (translate z (x : SeparatedConfiguration d δ)) = x
  rw [translate_add, neg_add_cancel, translate_zero]

/-- The translation pullback is represented by composition on L². -/
theorem hullPullbackUnitary_apply {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z : Euclidean d) (f : Lp ℂ 2 μ) :
    hullPullbackUnitary hδ Γ μ hμ z f =
      Lp.compMeasurePreserving (hullTranslate hδ Γ z) (hμ z) f := rfl

/-- The Koopman operators satisfy the additive Euclidean group law. -/
theorem hull_pullback_add {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z y : Euclidean d) (f : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving (hullTranslate hδ Γ z) (hμ z)
      (Lp.compMeasurePreserving (hullTranslate hδ Γ y) (hμ y) f) =
      Lp.compMeasurePreserving (hullTranslate hδ Γ (z + y)) (hμ (z + y)) f := by
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving (hullTranslate hδ Γ y) (hμ y) f) (hμ z)
  have h₂ := (hμ z).quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f (hμ y))
  have h₃ := Lp.coeFn_compMeasurePreserving f (hμ (z + y))
  filter_upwards [h₁, h₂, h₃] with x hx hy hz
  refine hx.trans (hy.trans ((congrArg f ?_).trans hz.symm))
  apply Subtype.ext
  change translate y (translate z (x : SeparatedConfiguration d δ)) = translate (z + y) x
  rw [translate_add, add_comm y z]
/-- The zero translation induces the identity Koopman operator. -/
theorem hull_pullback_zero {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving (hullTranslate hδ Γ 0) (hμ 0) f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hμ 0)] with x hx
  refine hx.trans (congrArg f ?_)
  apply Subtype.ext
  exact translate_zero (x : SeparatedConfiguration d δ)

/-- Joint continuity of the Koopman operators on the compact translation hull. -/
theorem continuous_hull_pullback {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ) :
    Continuous (fun p : Euclidean d × Lp ℂ 2 μ =>
      Lp.compMeasurePreserving (hullTranslate hδ Γ p.1) (hμ p.1) p.2) := by
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  letI := TopologicalSpace.metrizableSpaceMetric (hull Γ)
  let T : Euclidean d → C(hull Γ, hull Γ) := fun z =>
    ⟨hullTranslate hδ Γ z,
      (continuous_hullTranslate hδ Γ).comp (continuous_const.prodMk continuous_id)⟩
  exact continuous_koopman T
    (ContinuousMap.continuous_of_continuous_uncurry T (continuous_hullTranslate hδ Γ)) hμ
/-- Strong continuity of the unitary representation on the stationary hull. -/
theorem strongContinuous_hullPullbackUnitary {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) : Continuous (fun z => hullPullbackUnitary hδ Γ μ hμ z f) := by
  simpa only [hullPullbackUnitary_apply] using
    (continuous_hull_pullback hδ Γ μ hμ).comp (continuous_id.prodMk continuous_const)
/-- The paper's operator U_z f(Γ) = f(Γ + z), namely pullback by T_{-z}. -/
noncomputable def hullKoopmanUnitary {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z : Euclidean d) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  hullPullbackUnitary hδ Γ μ hμ (-z)
/-- Actual composition formula with the manuscript's sign. -/
theorem hullKoopmanUnitary_apply {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z : Euclidean d) (f : Lp ℂ 2 μ) :
    hullKoopmanUnitary hδ Γ μ hμ z f =
      Lp.compMeasurePreserving (hullTranslate hδ Γ (-z)) (hμ (-z)) f := rfl
/-- Strong continuity with the manuscript's sign convention. -/
theorem strongContinuous_hullKoopmanUnitary {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) : Continuous (fun z => hullKoopmanUnitary hδ Γ μ hμ z f) :=
  (strongContinuous_hullPullbackUnitary hδ Γ μ hμ f).comp continuous_neg
/-- The paper's Koopman unitaries satisfy U_z U_y = U_{z+y}. -/
theorem hullKoopmanUnitary_add {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z y : Euclidean d) (f : Lp ℂ 2 μ) :
    hullKoopmanUnitary hδ Γ μ hμ z (hullKoopmanUnitary hδ Γ μ hμ y f) =
      hullKoopmanUnitary hδ Γ μ hμ (z + y) f := by
  simpa only [hullKoopmanUnitary_apply, neg_add] using
    hull_pullback_add hδ Γ μ hμ (-z) (-y) f
/-- The zero Koopman operator is the identity. -/
theorem hullKoopmanUnitary_zero {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) : hullKoopmanUnitary hδ Γ μ hμ 0 f = f := by
  simpa only [hullKoopmanUnitary_apply, neg_zero] using hull_pullback_zero hδ Γ μ hμ f
/-- The constant vector is fixed by every paper Koopman operator. -/
theorem hullKoopmanUnitary_const {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsFiniteMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z : Euclidean d) (c : ℂ) :
    hullKoopmanUnitary hδ Γ μ hμ z (Lp.const 2 μ c) = Lp.const 2 μ c := by
  let T : C(hull Γ, hull Γ) :=
    ⟨hullTranslate hδ Γ (-z),
      (continuous_hullTranslate hδ Γ).comp (continuous_const.prodMk continuous_id)⟩
  exact koopmanIsometry_const T (hμ (-z)) c
/-- The stationary Hilbert space of the compact metrizable hull is separable. -/
theorem separableSpace_hullLp {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ] :
    TopologicalSpace.SeparableSpace (Lp ℂ 2 μ) := by
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  letI := TopologicalSpace.metrizableSpaceMetric (hull Γ)
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance
end SeparatedConfiguration
end RieszEuclidean
