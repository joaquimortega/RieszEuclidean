import RieszEuclidean.SurfaceNullity
import Mathlib.Analysis.Calculus.Implicit

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace RieszEuclidean

/-- A regular level is locally the Lipschitz image of the derivative's kernel.
Consequently it is null in every larger Hausdorff dimension. Strict
differentiability suffices; no smoothness theorem for the implicit function
is needed. -/
theorem regular_level_locally_hausdorff_null {n k : ℕ}
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : Euclidean n → F} {a : Euclidean n}
    {L : Euclidean n →L[ℝ] F} (hf : HasStrictFDerivAt f L a)
    (hL : LinearMap.range L = ⊤) (hk : Module.finrank ℝ (LinearMap.ker L) < k) :
    ∃ V ∈ nhds a, (Measure.hausdorffMeasure (k : ℝ))
      (V ∩ {x | f x = f a}) = 0 := by
  let φ := hf.implicitFunction f L hL (f a)
  let e := hf.implicitToPartialHomeomorph f L hL
  have hd := hf.to_implicitFunction hL
  obtain ⟨D, hD, happ⟩ := hd.approximates_deriv_on_nhds
    (Or.inr (show (0 : ℝ≥0) < 1 by norm_num))
  have hlip : LipschitzOnWith (‖(LinearMap.ker L).subtypeL‖₊ + 1) φ D := by
    intro x hx y hy
    exact happ.lipschitz ⟨x, hx⟩ ⟨y, hy⟩
  have hnull : (Measure.hausdorffMeasure (k : ℝ)) (φ '' D) = 0 := by
    apply hausdorffMeasure_of_dimH_lt (d := (k : ℝ≥0))
    calc
      dimH (φ '' D) ≤ dimH D := hlip.dimH_image_le
      _ ≤ dimH (Set.univ : Set (LinearMap.ker L)) := dimH_mono (Set.subset_univ D)
      _ = Module.finrank ℝ (LinearMap.ker L) := Real.dimH_univ_eq_finrank _
      _ < (k : ℝ≥0) := by exact_mod_cast hk
  have he : Tendsto (fun x => (e x).2) (nhds a) (nhds 0) := by
    have ht := (e.continuousAt (hf.mem_implicitToPartialHomeomorph_source hL)).snd
    simpa only [e, hf.implicitToPartialHomeomorph_self hL, Prod.snd_zero] using ht.tendsto
  have hall : ∀ᶠ x in nhds a, (e x).2 ∈ D ∧
      hf.implicitFunction f L hL (f x) (e x).2 = x :=
    (he.eventually hD).and (hf.eq_implicitFunction hL)
  refine ⟨{x | (e x).2 ∈ D ∧ hf.implicitFunction f L hL (f x) (e x).2 = x}, hall, ?_⟩
  apply measure_mono_null _ hnull
  intro x hx
  refine ⟨(e x).2, hx.1.1, ?_⟩
  change hf.implicitFunction f L hL (f a) (e x).2 = x
  rw [← hx.2]
  exact hx.1.2

/-- Local nullity implies nullity in a second-countable Euclidean space. -/
theorem measure_null_of_locally_null {n : ℕ} (μ : Measure (Euclidean n))
    (T : Set (Euclidean n))
    (hlocal : ∀ a ∈ T, ∃ V ∈ nhds a, μ (V ∩ T) = 0) : μ T = 0 := by
  classical
  choose V hV hn using hlocal
  obtain ⟨J, hJ, hcover⟩ :=
    (HereditarilyLindelof_LindelofSets T).elim_nhds_subcover' V hV
  have hnull : μ (⋃ a ∈ J, V a a.property ∩ T) = 0 :=
    (measure_biUnion_null_iff hJ).mpr (fun a _ => hn a a.property)
  apply measure_mono_null _ hnull
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hcover hx)
  exact Set.mem_iUnion₂.mpr ⟨a, ha, hxa, hx⟩

/-- A set locally contained in regular levels whose derivative kernels have
 dimension less than `k` has zero `k`-dimensional Hausdorff measure. -/
theorem regular_levels_hausdorff_null {n k : ℕ}
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T : Set (Euclidean n))
    (hlocal : ∀ a ∈ T, ∃ (f : Euclidean n → F)
      (L : Euclidean n →L[ℝ] F),
      HasStrictFDerivAt f L a ∧ LinearMap.range L = ⊤ ∧
      Module.finrank ℝ (LinearMap.ker L) < k ∧
      ∀ᶠ x in nhds a, x ∈ T → f x = f a) :
    (Measure.hausdorffMeasure (k : ℝ)) T = 0 := by
  apply measure_null_of_locally_null
  intro a ha
  obtain ⟨f, L, hf, hL, hk, he⟩ := hlocal a ha
  obtain ⟨V, hV, hn⟩ := regular_level_locally_hausdorff_null hf hL hk
  refine ⟨V ∩ {x | x ∈ T → f x = f a}, inter_mem hV he, ?_⟩
  apply measure_mono_null _ hn
  intro x hx
  exact ⟨hx.1.1, hx.1.2 hx.2⟩

end RieszEuclidean
