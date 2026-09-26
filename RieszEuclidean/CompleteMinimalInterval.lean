import RieszEuclidean.CompleteMinimalBasic
import RieszEuclidean.CompleteMinimalEllipsoid
import RieszEuclidean.SeparatedConfigurations
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue

/-!
# The complete and minimal interval exponential system

The Fourier completeness input is Mathlib's proved `fourierBasis`; the
quotient-circle pullback is proved below using a measurable interval section.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace RieszEuclidean.CompleteMinimal

section CircleInterval

variable (T a : ℝ) [hT : Fact (0 < T)]

/-- The measurable representative in the fundamental interval `(a,a+T]`. -/
def circleRepresentative (x : AddCircle T) : ℝ :=
  (AddCircle.measurableEquivIoc T a x).val

theorem circleRepresentative_measurable : Measurable (circleRepresentative T a) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc T a).measurable

theorem circleRepresentative_quotient (x : AddCircle T) :
    (circleRepresentative T a x : AddCircle T) = x := by
  exact (AddCircle.measurableEquivIoc T a).symm_apply_apply x

theorem circleRepresentative_coe {x : ℝ} (hx : x ∈ Ioc a (a + T)) :
    circleRepresentative T a (x : AddCircle T) = x := by
  exact congrArg Subtype.val ((AddCircle.measurableEquivIoc T a).apply_symm_apply ⟨x, hx⟩)

theorem circleRepresentative_map_volume :
    Measure.map (circleRepresentative T a) (volume : Measure (AddCircle T)) =
      volume.restrict (Ioo a (a + T)) := by
  rw [restrict_Ioo_eq_restrict_Ioc,
    ← (AddCircle.measurePreserving_mk T a).map_eq,
    Measure.map_map (circleRepresentative_measurable T a) AddCircle.measurable_mk']
  calc
    _ = Measure.map id (volume.restrict (Ioc a (a + T))) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact circleRepresentative_coe T a hx
    _ = _ := Measure.map_id

theorem circleRepresentative_map_haar :
    Measure.map (circleRepresentative T a) AddCircle.haarAddCircle =
      (ENNReal.ofReal T)⁻¹ • volume.restrict (Ioo a (a + T)) := by
  have hc : ENNReal.ofReal T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hT.out
  have h := circleRepresentative_map_volume T a
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.map_smul] at h
  rw [← h, smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]

theorem intervalQuotient_map :
    Measure.map ((↑) : ℝ → AddCircle T) (volume.restrict (Ioo a (a + T))) =
      ENNReal.ofReal T • AddCircle.haarAddCircle := by
  rw [restrict_Ioo_eq_restrict_Ioc,
    (AddCircle.measurePreserving_mk T a).map_eq, AddCircle.volume_eq_smul_haarAddCircle]

/-- The a.e. circle/interval correspondence, including its actual volume factor. -/
def intervalCircleEquiv :
    Lp ℂ 2 (@AddCircle.haarAddCircle T hT) ≃L[ℂ]
      Lp ℂ 2 (volume.restrict (Ioo a (a + T))) := by
  let p := scaledL2Pullback ((↑) : ℝ → AddCircle T) AddCircle.measurable_mk'
    (intervalQuotient_map T a) ENNReal.ofReal_ne_top
  let q := scaledL2Pullback (circleRepresentative T a) (circleRepresentative_measurable T a)
    (circleRepresentative_map_haar T a)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hT.out))
  have hp (g : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
      (p g : ℝ → ℂ) =ᵐ[volume.restrict (Ioo a (a + T))]
        fun x => g (x : AddCircle T) := scaledL2Pullback_ae _ _ _ _ g
  have hq (g : Lp ℂ 2 (volume.restrict (Ioo a (a + T)))) :
      (q g : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
        fun x => g (circleRepresentative T a x) := scaledL2Pullback_ae _ _ _ _ g
  have hmp : QuasiMeasurePreserving ((↑) : ℝ → AddCircle T)
      (volume.restrict (Ioo a (a + T))) AddCircle.haarAddCircle :=
    ⟨AddCircle.measurable_mk', by rw [intervalQuotient_map]; exact smul_absolutelyContinuous⟩
  have hmq : QuasiMeasurePreserving (circleRepresentative T a) AddCircle.haarAddCircle
      (volume.restrict (Ioo a (a + T))) :=
    ⟨circleRepresentative_measurable T a,
      by rw [circleRepresentative_map_haar]; exact smul_absolutelyContinuous⟩
  exact
    { toLinearEquiv :=
        { p.toLinearMap with
          invFun := q
          left_inv := fun g => Lp.ext (by
            filter_upwards [hq (p g), hmq.ae (hp g)] with x hx hy
            exact hx.trans (hy.trans (congrArg g (circleRepresentative_quotient T a x))))
          right_inv := fun g => Lp.ext (by
            filter_upwards [hp (q g), hmp.ae (hq g), ae_restrict_mem measurableSet_Ioo]
              with x hx hy hmem
            exact hx.trans (hy.trans (congrArg g (circleRepresentative_coe T a
              (Ioo_subset_Ioc_self hmem))))) }
      continuous_toFun := p.continuous
      continuous_invFun := q.continuous }

theorem intervalCircleEquiv_ae (g : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    (intervalCircleEquiv T a g : ℝ → ℂ) =ᵐ[volume.restrict (Ioo a (a + T))]
      fun x => g (x : AddCircle T) :=
  scaledL2Pullback_ae _ _ _ _ g

/-- Pullback scales the Hilbert inner product by the length of the interval. -/
theorem intervalCircleEquiv_inner (f g : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    inner (𝕜 := ℂ) (intervalCircleEquiv T a f) (intervalCircleEquiv T a g) =
      (T : ℂ) * inner (𝕜 := ℂ) f g := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in Ioo a (a + T), inner (𝕜 := ℂ) (f (x : AddCircle T))
        (g (x : AddCircle T)) := by
      apply integral_congr_ae
      filter_upwards [intervalCircleEquiv_ae T a f, intervalCircleEquiv_ae T a g]
        with x hx hy
      rw [hx, hy]
    _ = ∫ x : AddCircle T, inner (𝕜 := ℂ) (f x) (g x)
        ∂(ENNReal.ofReal T • AddCircle.haarAddCircle) := by
      rw [← intervalQuotient_map T a]
      exact (integral_map_of_stronglyMeasurable
        (f := fun x : AddCircle T => inner (𝕜 := ℂ) (f x) (g x)) AddCircle.measurable_mk'
        ((Lp.stronglyMeasurable f).inner (Lp.stronglyMeasurable g))).symm
    _ = _ := by
      rw [integral_smul_measure, L2.inner_def]
      simp [ENNReal.toReal_ofReal hT.out.le, Complex.real_smul]

/-- The ordinary real-interval exponential modes transported from the circle. -/
def intervalMode (k : ℤ) : Lp ℂ 2 (volume.restrict (Ioo a (a + T))) :=
  intervalCircleEquiv T a (_root_.fourierLp 2 k)

theorem intervalMode_ae (k : ℤ) :
    (intervalMode T a k : ℝ → ℂ) =ᵐ[volume.restrict (Ioo a (a + T))]
      fun x => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x / T) := by
  have hq : QuasiMeasurePreserving ((↑) : ℝ → AddCircle T)
      (volume.restrict (Ioo a (a + T))) AddCircle.haarAddCircle :=
    ⟨AddCircle.measurable_mk', by rw [intervalQuotient_map]; exact smul_absolutelyContinuous⟩
  filter_upwards [intervalCircleEquiv_ae T a (_root_.fourierLp 2 k),
    hq.ae (_root_.coeFn_fourierLp 2 k)] with x hx hy
  exact hx.trans (hy.trans _root_.fourier_coe_apply)

theorem intervalMode_inner (k l : ℤ) :
    inner (𝕜 := ℂ) (intervalMode T a k) (intervalMode T a l) =
      (T : ℂ) * if k = l then 1 else 0 := by
  rw [intervalMode, intervalMode, intervalCircleEquiv_inner]
  congr 1
  exact (orthonormal_iff_ite.mp (_root_.orthonormal_fourier (T := T))) k l

theorem intervalMode_complete : IsComplete (intervalMode T a) := by
  have hd := (intervalCircleEquiv T a).surjective.denseRange
  have hh := hd.topologicalClosure_map_submodule
    (_root_.span_fourierLp_closure_eq_top (T := T) (p := 2) (by norm_num))
  rw [Submodule.map_span, ← Set.range_comp] at hh
  exact hh

theorem intervalMode_biorthogonal :
    IsBiorthogonal (intervalMode T a) (fun k => (T : ℂ)⁻¹ • intervalMode T a k) := by
  classical
  intro k l
  rw [inner_smul_left, intervalMode_inner]
  have hstar : starRingEnd ℂ ((T : ℂ)⁻¹) = (T : ℂ)⁻¹ := by simp
  rw [hstar, ← mul_assoc]
  rw [inv_mul_cancel₀ (by exact_mod_cast hT.out.ne'), one_mul]
  by_cases h : k = l <;> simp [h]

theorem intervalMode_minimal : IsMinimal (intervalMode T a) :=
  (intervalMode_biorthogonal T a).isMinimal

end CircleInterval

/-- Evaluation at the unique coordinate identifies one-dimensional Euclidean space with ℝ. -/
def lineIsometry : Euclidean 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv.trans
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ)
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]

@[simp] theorem lineIsometry_apply (x : Euclidean 1) : lineIsometry x = x 0 := rfl

/-- The physical Euclidean realization of an ordinary open interval. -/
def lineInterval (a b : ℝ) : Set (Euclidean 1) := lineIsometry ⁻¹' Ioo a b

theorem lineInterval_measurable (a b : ℝ) : MeasurableSet (lineInterval a b) :=
  measurableSet_Ioo.preimage lineIsometry.continuous.measurable

theorem lineInterval_map (a b : ℝ) :
    Measure.map lineIsometry (volume.restrict (lineInterval a b)) =
      (1 : ℝ≥0∞) • volume.restrict (Ioo a b) := by
  let e := lineIsometry.toHomeomorph.toMeasurableEquiv
  change Measure.map e (volume.restrict (e ⁻¹' Ioo a b)) = _
  rw [← e.restrict_map]
  change (Measure.map lineIsometry volume).restrict (Ioo a b) = _
  rw [lineIsometry.measurePreserving.map_eq, one_smul]

/-- Pullback of real-interval L² along the Euclidean coordinate isometry. -/
def lineL2Equiv (a b : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioo a b)) ≃L[ℂ] DomainL2 (lineInterval a b) :=
  scaledL2Equiv lineIsometry.toHomeomorph.toMeasurableEquiv (lineInterval_map a b)
    one_ne_zero ENNReal.one_ne_top

theorem lineL2Equiv_ae (a b : ℝ) (f : Lp ℂ 2 (volume.restrict (Ioo a b))) :
    (lineL2Equiv a b f : Euclidean 1 → ℂ) =ᵐ[volume.restrict (lineInterval a b)]
      fun x => f (lineIsometry x) :=
  scaledL2Equiv_ae _ _ _ _ f

theorem lineL2Equiv_inner (a b : ℝ) (f g : Lp ℂ 2 (volume.restrict (Ioo a b))) :
    inner (𝕜 := ℂ) (lineL2Equiv a b f) (lineL2Equiv a b g) = inner (𝕜 := ℂ) f g := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in lineInterval a b,
        inner (𝕜 := ℂ) (f (lineIsometry x)) (g (lineIsometry x)) := by
      apply integral_congr_ae
      filter_upwards [lineL2Equiv_ae a b f, lineL2Equiv_ae a b g] with x hx hy
      rw [hx, hy]
    _ = _ := by
      have h := integral_map_of_stronglyMeasurable
        (μ := volume.restrict (lineInterval a b))
        (f := fun x : ℝ => inner (𝕜 := ℂ) (f x) (g x)) lineIsometry.continuous.measurable
        ((Lp.stronglyMeasurable f).inner (Lp.stronglyMeasurable g))
      rw [lineInterval_map, one_smul] at h
      exact h.symm

section EuclideanInterval

variable (T a : ℝ) [hT : Fact (0 < T)]

/-- The integer lattice of frequencies divided by the length of the interval. -/
def intervalFrequency (k : ℤ) : Euclidean 1 := lineIsometry.symm ((k : ℝ) / T)

/-- The actual Euclidean domain vectors obtained from the Fourier modes. -/
def lineMode (k : ℤ) : DomainL2 (lineInterval a (a + T)) :=
  lineL2Equiv a (a + T) (intervalMode T a k)

theorem lineMode_ae (k : ℤ) :
    (lineMode T a k : Euclidean 1 → ℂ) =ᵐ[volume.restrict (lineInterval a (a + T))]
      exponential (intervalFrequency T k) := by
  have hq : QuasiMeasurePreserving lineIsometry
      (volume.restrict (lineInterval a (a + T))) (volume.restrict (Ioo a (a + T))) :=
    ⟨lineIsometry.continuous.measurable,
      by rw [lineInterval_map, one_smul]⟩
  filter_upwards [lineL2Equiv_ae a (a + T) (intervalMode T a k),
    hq.ae (intervalMode_ae T a k)] with x hx hy
  change (lineL2Equiv a (a + T) (intervalMode T a k)) x = _
  rw [hx, hy]
  unfold exponential intervalFrequency
  congr 1
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_one, RCLike.inner_apply, conj_trivial]
  change _ = 2 * (Real.pi : ℂ) * Complex.I *
    ((x 0 * (lineIsometry.symm ((k : ℝ) / T)) 0 : ℝ) : ℂ)
  have hs : (lineIsometry.symm ((k : ℝ) / T)) 0 = (k : ℝ) / T :=
    lineIsometry.apply_symm_apply _
  rw [hs, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast]
  change _ = 2 * (Real.pi : ℂ) * Complex.I * (lineIsometry x * ((k : ℂ) / T))
  ring

theorem lineMode_inner (k l : ℤ) :
    inner (𝕜 := ℂ) (lineMode T a k) (lineMode T a l) =
      (T : ℂ) * if k = l then 1 else 0 := by
  rw [lineMode, lineMode, lineL2Equiv_inner, intervalMode_inner]

theorem lineMode_complete : IsComplete (lineMode T a) := by
  have hd := (lineL2Equiv a (a + T)).surjective.denseRange
  have hh := hd.topologicalClosure_map_submodule (intervalMode_complete T a)
  rw [Submodule.map_span, ← Set.range_comp] at hh
  exact hh

theorem lineMode_biorthogonal :
    IsBiorthogonal (lineMode T a) (fun k => (T : ℂ)⁻¹ • lineMode T a k) := by
  classical
  intro k l
  rw [inner_smul_left, lineMode_inner]
  have hstar : starRingEnd ℂ ((T : ℂ)⁻¹) = (T : ℂ)⁻¹ := by simp
  rw [hstar, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hT.out.ne'), one_mul]
  by_cases h : k = l <;> simp [h]

theorem intervalFrequency_injective : Function.Injective (intervalFrequency T) := by
  intro k l h
  have hr : (k : ℝ) / T = (l : ℝ) / T := lineIsometry.symm.injective h
  exact_mod_cast (div_left_inj' hT.out.ne').mp hr

/-- The frequency configuration for a length-T interval. -/
def intervalSpectrum : Set (Euclidean 1) := range (intervalFrequency T)

theorem intervalSpectrum_separated : Separated (1 / T) (intervalSpectrum T) := by
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ hne
  have hkl : k ≠ l := fun h => hne (congrArg (intervalFrequency T) h)
  have hi : (1 : ℤ) ≤ |k - l| := by
    have hp : (0 : ℤ) < |k - l| := abs_pos.mpr (sub_ne_zero.mpr hkl)
    omega
  have hr : (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by exact_mod_cast hi
  change 1 / T ≤ dist (lineIsometry.symm ((k : ℝ) / T))
    (lineIsometry.symm ((l : ℝ) / T))
  rw [lineIsometry.symm.isometry.dist_eq, Real.dist_eq, ← sub_div,
    abs_div, abs_of_pos hT.out]
  exact div_le_div_of_nonneg_right hr hT.out.le

/-- This interval spectrum has finitely many points in every compact region. -/
theorem intervalSpectrum_locallyFinite (K : Set (Euclidean 1)) (hK : IsCompact K) :
    (intervalSpectrum T ∩ K).Finite :=
  (intervalSpectrum_separated T).finite_inter_compact (one_div_pos.mpr hT.out) hK

theorem lineMode_eq_exponentialL2 (hfinite : volume (lineInterval a (a + T)) ≠ ⊤)
    (k : ℤ) : lineMode T a k = exponentialL2 (lineInterval a (a + T)) hfinite
      (intervalFrequency T k) := by
  apply Lp.ext
  exact (lineMode_ae T a k).trans (exponentialL2_ae _ _ _).symm

/-- The lattice exponential system is complete in the actual Euclidean interval L². -/
theorem interval_exponentials_complete (hfinite : volume (lineInterval a (a + T)) ≠ ⊤) :
    IsCompleteExponential (lineInterval a (a + T)) hfinite (intervalSpectrum T) := by
  have hr : range (exponentialFamily (lineInterval a (a + T)) hfinite (intervalSpectrum T)) =
      range (lineMode T a) := by
    ext f
    constructor
    · rintro ⟨ξ, rfl⟩
      obtain ⟨k, hk⟩ := ξ.property
      refine ⟨k, ?_⟩
      rw [lineMode_eq_exponentialL2 T a hfinite k]
      exact congrArg (exponentialL2 _ hfinite) hk
    · rintro ⟨k, rfl⟩
      refine ⟨⟨intervalFrequency T k, mem_range_self k⟩, ?_⟩
      exact (lineMode_eq_exponentialL2 T a hfinite k).symm
  change (Submodule.span ℂ _).topologicalClosure = ⊤
  rw [hr]
  exact lineMode_complete T a

/-- Reciprocal-length multiples of the exponentials are their individual biorthogonals. -/
theorem interval_exponentials_biorthogonal
    (hfinite : volume (lineInterval a (a + T)) ≠ ⊤) :
    IsBiorthogonal (exponentialFamily (lineInterval a (a + T)) hfinite (intervalSpectrum T))
      (fun ξ => (T : ℂ)⁻¹ • exponentialL2 (lineInterval a (a + T)) hfinite ξ.val) := by
  classical
  intro ξ η
  obtain ⟨k, hk⟩ := ξ.property
  obtain ⟨l, hl⟩ := η.property
  have hvk : exponentialL2 (lineInterval a (a + T)) hfinite ξ.val = lineMode T a k := by
    rw [lineMode_eq_exponentialL2 T a hfinite, hk]
  have hvl : exponentialL2 (lineInterval a (a + T)) hfinite η.val = lineMode T a l := by
    rw [lineMode_eq_exponentialL2 T a hfinite, hl]
  change inner (𝕜 := ℂ) ((T : ℂ)⁻¹ • exponentialL2 _ hfinite ξ.val)
    (exponentialL2 _ hfinite η.val) = _
  rw [hvk, hvl, lineMode_biorthogonal T a k l]
  have heq : k = l ↔ ξ = η := by
    constructor
    · intro h
      apply Subtype.ext
      rw [← hk, ← hl, h]
    · intro h
      apply intervalFrequency_injective T
      rw [hk, hl, h]
  simp only [heq]
  by_cases h : ξ = η <;> simp [h]

theorem interval_exponentials_minimal (hfinite : volume (lineInterval a (a + T)) ≠ ⊤) :
    IsMinimalExponential (lineInterval a (a + T)) hfinite (intervalSpectrum T) :=
  (interval_exponentials_biorthogonal T a hfinite).isMinimal

end EuclideanInterval

theorem lineInterval_isBounded (a b : ℝ) : Bornology.IsBounded (lineInterval a b) := by
  have hc := (isCompact_Icc : IsCompact (Icc a b)).image lineIsometry.symm.continuous
  apply hc.isBounded.subset
  intro x hx
  refine ⟨lineIsometry x, Ioo_subset_Icc_self hx, ?_⟩
  exact lineIsometry.symm_apply_apply x

/-- Every nondegenerate Euclidean interval admits a locally finite, complete minimal
exponential system with individual biorthogonals supported in its closure. -/
theorem complete_minimal_interval (a b : ℝ) (hab : a < b) :
    ∃ Λ : Set (Euclidean 1),
      (∀ K : Set (Euclidean 1), IsCompact K → (Λ ∩ K).Finite) ∧
      IsCompleteExponential (lineInterval a b) (lineInterval_isBounded a b).measure_lt_top.ne Λ ∧
      IsMinimalExponential (lineInterval a b) (lineInterval_isBounded a b).measure_lt_top.ne Λ ∧
      ∃ g : Λ → DomainL2 (lineInterval a b),
        IsBiorthogonal (exponentialFamily (lineInterval a b)
          (lineInterval_isBounded a b).measure_lt_top.ne Λ) g ∧
        ∀ ξ, SupportedOn (lineInterval a b) (g ξ) (closure (lineInterval a b)) := by
  let T := b - a
  haveI : Fact (0 < T) := ⟨sub_pos.mpr hab⟩
  have hab' : a + T = b := by dsimp [T]; ring
  rw [← hab']
  refine ⟨intervalSpectrum T, intervalSpectrum_locallyFinite T,
    interval_exponentials_complete T a _, interval_exponentials_minimal T a _,
    fun ξ => (T : ℂ)⁻¹ • exponentialL2 _ _ ξ.val,
    interval_exponentials_biorthogonal T a _, ?_⟩
  intro ξ
  exact (supportedOn_domain _ (lineInterval_measurable _ _) _).mono subset_closure

/-- A nonempty bounded open convex one-dimensional domain is an ordinary interval. -/
theorem exists_lineInterval {Ω : Set (Euclidean 1)} (hne : Ω.Nonempty)
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ a b : ℝ, a < b ∧ Ω = lineInterval a b := by
  let S := lineIsometry '' Ω
  have hSn : S.Nonempty := hne.image lineIsometry
  have hSo : IsOpen S := lineIsometry.toHomeomorph.isOpenMap Ω hopen
  have hSc : Convex ℝ S := hconvex.linear_image lineIsometry.toLinearMap
  have hcompact : IsCompact (closure S) := by
    change IsCompact (closure (lineIsometry.toHomeomorph '' Ω))
    rw [← lineIsometry.toHomeomorph.image_closure]
    exact hbounded.isCompact_closure.image lineIsometry.continuous
  have hclosed : closure S = Icc (sInf (closure S)) (sSup (closure S)) :=
    eq_Icc_csInf_csSup_of_connected_bdd_closed
      (hSc.closure.isConnected (hSn.mono subset_closure))
      hcompact.bddBelow hcompact.bddAbove isClosed_closure
  have hreg := hSc.interior_closure_eq_interior_of_nonempty_interior
    (by rwa [hSo.interior_eq])
  rw [hclosed, interior_Icc, hSo.interior_eq] at hreg
  refine ⟨sInf (closure S), sSup (closure S), ?_, ?_⟩
  · exact nonempty_Ioo.mp (hreg.symm ▸ hSn)
  · change Ω = lineIsometry ⁻¹' _
    rw [hreg]
    exact (preimage_image_eq Ω lineIsometry.injective).symm

/-- The closure of a nondegenerate interval is a full-dimensional ellipsoid. -/
theorem lineInterval_closure_isEllipsoid (a b : ℝ) (hab : a < b) :
    IsEllipsoid (closure (lineInterval a b)) := by
  let m := (a + b) / 2
  let r := (b - a) / 2
  have hr : 0 < r := div_pos (sub_pos.mpr hab) (by norm_num)
  let A := (LinearEquiv.smulOfNeZero ℝ (Euclidean 1) r hr.ne').toContinuousLinearEquiv
  refine ⟨lineIsometry.symm m, A, ?_⟩
  apply (Set.image_injective.mpr lineIsometry.injective)
  have hleft : lineIsometry '' closure (lineInterval a b) = Icc a b := by
    change lineIsometry.toHomeomorph '' closure (lineInterval a b) = Icc a b
    rw [lineIsometry.toHomeomorph.image_closure]
    have he : lineIsometry '' lineInterval a b = Ioo a b :=
      image_preimage_eq _ lineIsometry.surjective
    change closure (lineIsometry '' lineInterval a b) = Icc a b
    rw [he, closure_Ioo hab.ne]
  rw [hleft]
  symm
  calc
    _ = (fun y : ℝ => r * y + m) '' (lineIsometry '' Metric.closedBall (0 : Euclidean 1) 1) := by
      rw [closedEllipsoid, image_image, image_image]
      funext x
      simp [planeAffine, A, map_add, map_smul, smul_eq_mul, add_comm]
    _ = Icc a b := by
      change (fun y : ℝ => r * y + m) ''
        (lineIsometry.toIsometryEquiv '' Metric.closedBall (0 : Euclidean 1) 1) = Icc a b
      rw [lineIsometry.toIsometryEquiv.image_closedBall]
      change (fun y : ℝ => r * y + m) ''
        Metric.closedBall (lineIsometry (0 : Euclidean 1)) 1 = Icc a b
      simp only [map_zero, Real.closedBall_eq_Icc, _root_.zero_sub, zero_add]
      rw [image_affine_Icc' hr]
      have hleft : r * (-1) + m = a := by dsimp [r, m]; ring
      have hright : r * 1 + m = b := by dsimp [r, m]; ring
      rw [hleft, hright]

/-- In one dimension the entire domain closure is its John ellipsoid. -/
theorem johnEllipsoid_closure_dim_one {Ω : Set (Euclidean 1)} (hne : Ω.Nonempty)
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    IsJohnEllipsoid (closure Ω) (closure Ω) := by
  obtain ⟨a, b, hab, rfl⟩ := exists_lineInterval hne hbounded hopen hconvex
  exact (lineInterval_closure_isEllipsoid a b hab).isJohnEllipsoid_self

/-- The full one-dimensional complete-minimal theorem, including John-ellipsoid support. -/
theorem complete_minimal_dim_one {Ω : Set (Euclidean 1)} (hne : Ω.Nonempty)
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ Λ : Set (Euclidean 1),
      (∀ K : Set (Euclidean 1), IsCompact K → (Λ ∩ K).Finite) ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean 1), IsJohnEllipsoid (closure Ω) E ∧
        ∃ g : Λ → DomainL2 Ω, IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          ∀ ξ, SupportedOn Ω (g ξ) E := by
  obtain ⟨a, b, hab, hΩ⟩ := exists_lineInterval hne hbounded hopen hconvex
  subst Ω
  obtain ⟨Λ, hlocal, hcomplete, hminimal, g, hg, hsupp⟩ := complete_minimal_interval a b hab
  exact ⟨Λ, hlocal, hcomplete, hminimal, closure (lineInterval a b),
    (lineInterval_closure_isEllipsoid a b hab).isJohnEllipsoid_self, g, hg, hsupp⟩

end RieszEuclidean.CompleteMinimal
