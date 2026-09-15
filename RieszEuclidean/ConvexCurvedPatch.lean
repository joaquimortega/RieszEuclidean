import RieszEuclidean.ConvexContactPoint
import RieszEuclidean.RegularBoundaryChart
import RieszEuclidean.ContactChartConcavity
import RieszEuclidean.ConcaveChartFaces

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- Data of a relatively open boundary patch with strict curvature and singleton
supporting faces. The projection is an affine inverse to the regular chart. -/
structure CurvedBoundaryPatch {n : ℕ} (Ω : Set (Euclidean n)) where
  /-- The contact point of the containing ball. -/
  point : Euclidean n
  /-- The nonzero derivative defining the tangent parameter space. -/
  functional : Euclidean n →L[ℝ] ℝ
  functional_ne_zero : functional ≠ 0
  /-- The local C² parametrization of the boundary. -/
  chart : LinearMap.ker functional → Euclidean n
  /-- The continuous linear part of the inverse chart. -/
  projection : Euclidean n →L[ℝ] LinearMap.ker functional
  /-- The ambient open set defining the relatively open patch. -/
  neighborhood : Set (Euclidean n)
  isOpen_neighborhood : IsOpen neighborhood
  point_mem : point ∈ neighborhood ∩ frontier Ω
  chart_zero : chart 0 = point
  chart_deriv : HasStrictFDerivAt chart (LinearMap.ker functional).subtypeL 0
  chart_mem : ∀ᶠ u in nhds 0, chart u ∈ neighborhood ∩ frontier Ω
  projection_chart : ∀ᶠ u in nhds 0, projection (chart u-point) = u
  /-- A fixed linear height with uniformly negative chart Hessian. -/
  height : Euclidean n →L[ℝ] ℝ
  curvature : ∀ᶠ u in nhds 0, ∀ v,
    height (fderiv ℝ (fderiv ℝ chart) u v v) ≤ -(1/2 : ℝ) * ‖v‖ ^ 2
  singleton_faces : ∀ x ∈ neighborhood ∩ frontier Ω,
    ∀ J : Euclidean n →L[ℝ] ℝ, J ≠ 0 →
      FunctionalSupportsAt (closure Ω) x J → FunctionalSingletonFace (closure Ω) x J

/-- Lemma 8.2: a bounded nonempty convex C² domain admits a nonempty relatively
open strictly curved patch whose supporting hyperplanes have singleton faces. -/
theorem exists_convex_curved_patch {n : ℕ} (hn : 0 < n)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (hC : HasC2Boundary Ω) :
    Nonempty (CurvedBoundaryPatch Ω) := by
  obtain ⟨c, hcΩ⟩ := hne
  obtain ⟨p, hpS, _, hfar⟩ := exists_convex_contact_point hn hΩ hb hcΩ
  obtain ⟨V, f, hV, hpV, hf, hL, _, hzero⟩ := hC p hpS
  let L := fderiv ℝ f p
  have hfC : ContDiffAt ℝ 2 f p := hf.contDiffAt (hV.mem_nhds hpV)
  have hstrict : HasStrictFDerivAt f L p := hfC.hasStrictFDerivAt (by norm_num)
  have hlevel : ∀ᶠ x in nhds p, x ∈ frontier Ω ↔ f x = f p := by
    filter_upwards [hV.mem_nhds hpV] with x hx
    rw [(hzero p hpV).mp hpS]
    exact hzero x hx
  obtain ⟨φ, P, hφ0, hφC, hφd, hforward, hinverse⟩ :=
    regular_boundary_chart hstrict (hL p hpV) hfC hlevel
  have hball : ∀ᶠ u in nhds 0, ‖φ u-c‖ ≤ ‖p-c‖ :=
    hforward.mono fun _ hu => hfar _ (frontier_subset_closure hu.1)
  obtain ⟨r, hr, hconc, _, hcurv⟩ := contact_chart_strictConcavity φ p c hφC hφ0
    (LinearMap.ker L).subtypeₗᵢ hφd.hasFDerivAt hball
  have hP : ContinuousAt (fun x => P (x-p)) p := P.continuous.continuousAt.comp
    (continuousAt_id.sub continuousAt_const)
  have hparam : ∀ᶠ x in nhds p, P (x-p) ∈ Metric.ball 0 r := by
    apply hP.eventually
    simpa only [_root_.sub_self, map_zero] using Metric.ball_mem_nhds (0 : LinearMap.ker L) hr
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp (hinverse.and hparam)
  let W := Metric.ball p δ
  have hface := strictConcave_chart_singleton_faces hΩ hc Metric.isOpen_ball (convex_ball p δ)
    φ P p (innerSL ℝ (p-c)) hconc (fun x hx => (hsmall hx).1) (fun x hx => (hsmall hx).2)
  have ht : Tendsto φ (nhds 0) (nhds p) := hφ0 ▸ hφd.continuousAt.tendsto
  refine ⟨{
    point := p
    functional := L
    functional_ne_zero := hL p hpV
    chart := φ
    projection := P
    neighborhood := W
    isOpen_neighborhood := Metric.isOpen_ball
    point_mem := ⟨Metric.mem_ball_self hδ, hpS⟩
    chart_zero := hφ0
    chart_deriv := hφd
    chart_mem := ?_
    projection_chart := hforward.mono fun _ hu => hu.2
    height := innerSL ℝ (p-c)
    curvature := Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) hcurv
    singleton_faces := hface }⟩
  exact (ht.eventually (Metric.ball_mem_nhds p hδ)).and (hforward.mono fun _ hu => hu.1)

end RieszEuclidean
