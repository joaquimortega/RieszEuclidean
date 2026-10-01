import RieszEuclidean.CompleteMinimalAnalyticAssembly
import RieszEuclidean.CompleteMinimalMain
import RieszEuclidean.CompleteMinimalScope
import RieszEuclidean.TitchmarshLions

/-! The unconditional Section 9 main theorem and scope corollary. -/

noncomputable section
open MeasureTheory Set Metric

namespace RieszEuclidean.CompleteMinimal

/-- The actual normalized complete-minimal exponential system, constructed on
the enumerated Bessel spheres with individual duals supported in the unit ball.
All analytic package fields, including Titchmarsh–Lions, are proved. -/
theorem complete_minimal_normalized_domain (n : ℕ)
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (hconvex : Convex ℝ Ω)
    (hJ : IsJohnEllipsoid (closure Ω) (closedBall (0 : Euclidean (n + 1)) 1))
    (hB : ball (0 : Euclidean (n + 1)) 1 ⊆ Ω) :
    ∃ Λ : Set (Euclidean (n + 1)), Λ ⊆ sphereFrequencies (ballZeroRadius n) ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧ IsLocallyFiniteSet Λ ∧
      ∃ g : Λ → DomainL2 Ω,
        IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
        ∀ ξ, SupportedOn Ω (g ξ) (closedBall 0 1) :=
  complete_minimal_exponentials_of_sphere_analytic_inputs (by omega) Ω hΩ hbounded
    hbounded.measure_lt_top.ne (ballZeroRadius n) (ballZeroRadius_zero n)
    (fun j hj => ballZeroRadius_pos n hj) (ballZeroRadius_strictMono n)
    (ballZeroRadius_tendsto n) (closedBall 0 1)
    (sphereAnalyticInputs n (titchmarshLions (n + 1))
      Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB)

/-- The manuscript main theorem: every nonempty bounded open convex domain in
positive dimension has actual locally finite complete-minimal exponentials,
with their biorthogonal functions supported in a John ellipsoid of its closure. -/
theorem complete_minimal_bounded_open_convex {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (Euclidean d)} (hne : Ω.Nonempty)
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean d), IsJohnEllipsoid (closure Ω) E ∧
        ∃ g : Λ → DomainL2 Ω,
          IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          ∀ ξ, SupportedOn Ω (g ξ) E := by
  cases d with
  | zero => omega
  | succ n =>
    apply complete_minimal_from_normalized_domains hd ?_ hne hbounded hopen hconvex
    intro _hd2 D _hneD hboundedD hopenD hconvexD hJD hBD _htranslateD
    obtain ⟨Λ, _hspheres, hcomplete, _hminimal, hlocal, g, hg, hs⟩ :=
      complete_minimal_normalized_domain n D hopenD.measurableSet hboundedD hconvexD hJD hBD
    exact ⟨Λ, hlocal, hcomplete, g, hg, hs⟩

/-- The manuscript scope corollary, simultaneously for every measurable
intermediate domain up to null sets, using the same selected frequencies and
actual restrictions of the original duals. Proper ellipsoid-supported duals
are not complete on the original domain. -/
theorem complete_minimal_scope {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (Euclidean d)} (hne : Ω.Nonempty)
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean d), IsJohnEllipsoid (closure Ω) E ∧ interior E ⊆ Ω ∧
        ∃ g : Λ → DomainL2 Ω,
          IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          (∀ ξ, SupportedOn Ω (g ξ) E) ∧
          (∀ (D : Set (Euclidean d)), MeasurableSet D →
            interior E ≤ᵐ[volume] D → D ≤ᵐ[volume] Ω →
            ∃ hD : volume D ≠ ⊤,
              IsCompleteExponential D hD Λ ∧ IsMinimalExponential D hD Λ ∧
              IsBiorthogonal (exponentialFamily D hD Λ)
                (fun ξ => domainToDomain Ω D hopen.measurableSet (g ξ)) ∧
              ∀ ξ, SupportedOn D (domainToDomain Ω D hopen.measurableSet (g ξ)) E) ∧
          (0 < volume (Ω \ E) → ¬ IsComplete g) ∧
          (interior E ⊂ Ω → ¬ IsComplete g) :=
  complete_minimal_scope_of_existence hne hbounded hopen hconvex
    (complete_minimal_bounded_open_convex hd hne hbounded hopen hconvex)

end RieszEuclidean.CompleteMinimal
