import RieszEuclidean.NegativeBilinear

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- A negative definite second Fréchet derivative implies strict concavity on
a convex set. The proof restricts to each segment and uses the scalar test. -/
theorem strictConcaveOn_of_hessian_neg
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} {f : E → ℝ} (hD : Convex ℝ D)
    (hf : ∀ x ∈ D, ContDiffAt ℝ 2 f x)
    (hneg : ∀ x ∈ D, ∀ v : E, v ≠ 0 → fderiv ℝ (fderiv ℝ f) x v v < 0) :
    StrictConcaveOn ℝ D f := by
  refine ⟨hD, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let q : ℝ → E := fun t => x + t • (y - x)
  have hq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : q t ∈ D := by
    have he : q t = (1-t) • x + t • y := by dsimp [q]; module
    rw [he]
    exact hD hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hqc : ContDiff ℝ 2 q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hcont : ContinuousOn (f ∘ q) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hf _ (hq t ht)).continuousAt.comp hqc.continuous.continuousAt).continuousWithinAt
  have hs : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ q) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont
    intro t ht
    have ht' := interior_subset ht
    have he := second_derivative_along_line x (y-x) t (hf _ (hq t ht'))
    change deriv (deriv (fun s => f (q s))) t < 0
    rw [he]
    exact hneg _ (hq t ht') _ (sub_ne_zero.mpr hxy.symm)
  obtain ⟨_, hstrict⟩ := hs
  have hh := hstrict (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have he : q b = a • x + b • y := by
    dsimp [q]
    have haeq : a = 1-b := by linarith
    rw [haeq]
    module
  simp only [Function.comp_def, smul_eq_mul, mul_zero, mul_one, zero_add] at hh
  rw [he] at hh
  simpa only [q, zero_smul, add_zero, one_smul, add_sub_cancel] using hh

end RieszEuclidean
