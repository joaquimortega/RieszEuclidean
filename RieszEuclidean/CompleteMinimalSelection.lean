import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Filter.Cofinite

/-!
# Selection from finite interpolation stages

This is the abstract selection argument in the proof of `cm:thm:main`.
The hypotheses concern finite interpolation and one finite extension step;
totality and the global biorthogonals are conclusions of the construction.
-/

namespace RieszEuclidean.CompleteMinimal

open scoped ComplexInnerProductSpace

open Classical

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An interpolating finite set at a finite frequency level. The subspace `V N`
contains the permitted interpolants at level `N`. -/
structure FiniteStage (e : X → H) (level : X → ℕ) (V : ℕ → Submodule ℂ H) where
  /-- The finite set of frequencies chosen at this stage. -/
  points : Finset X
  /-- The largest sphere level admitted at this stage. -/
  cutoff : ℕ
  bounded : ∀ x ∈ points, level x ≤ cutoff
  interpolate : ∀ x ∈ points, ∃ g ∈ V cutoff,
    ∀ y ∈ points, @inner ℂ H _ g (e y) = if x = y then 1 else 0

/-- The finite-step input: extend any interpolating stage, using only new
frequency levels, while approximating an arbitrary finite list of targets. -/
def HasFiniteExtensions (e : X → H) (level : X → ℕ) (V : ℕ → Submodule ℂ H) : Prop :=
  ∀ (A : FiniteStage e level V) (targets : Finset H) (ε : ℝ), 0 < ε →
    ∃ B : FiniteStage e level V,
      A.points ⊆ B.points ∧ A.cutoff < B.cutoff ∧
      (∀ x ∈ B.points, x ∉ A.points → A.cutoff < level x) ∧
      ∀ f ∈ targets, ∃ v ∈ Submodule.span ℂ (e '' (B.points : Set X)), dist f v < ε

/-- The data produced by iterating the finite extension step. -/
structure SelectionStages (e : X → H) (level : X → ℕ)
    (V : ℕ → Submodule ℂ H) (f : ℕ → H) where
  /-- The sequence of finite interpolation stages. -/
  stage : ℕ → FiniteStage e level V
  nested : ∀ n, (stage n).points ⊆ (stage (n + 1)).points
  increasing : ∀ n, (stage n).cutoff < (stage (n + 1)).cutoff
  fresh : ∀ n x, x ∈ (stage (n + 1)).points → x ∉ (stage n).points →
    (stage n).cutoff < level x
  approximate : ∀ n j, j ≤ n →
    ∃ v ∈ Submodule.span ℂ (e '' ((stage (n + 1)).points : Set X)),
      dist (f j) v < 1 / (n + 1 : ℝ)

/-- The elementary dependent recursion that selects all stages. -/
theorem exists_selectionStages (e : X → H) (level : X → ℕ)
    (V : ℕ → Submodule ℂ H) (initial : FiniteStage e level V)
    (extend : HasFiniteExtensions e level V) (f : ℕ → H) :
    ∃ S : SelectionStages e level V f, S.stage 0 = initial := by
  classical
  let next : ℕ → FiniteStage e level V → FiniteStage e level V := fun n A =>
    Classical.choose (extend A ((Finset.range (n + 1)).image f)
      (1 / (n + 1 : ℝ)) (by positivity))
  have next_spec (n : ℕ) (A : FiniteStage e level V) :
      A.points ⊆ (next n A).points ∧ A.cutoff < (next n A).cutoff ∧
      (∀ x ∈ (next n A).points, x ∉ A.points → A.cutoff < level x) ∧
      ∀ j ≤ n, ∃ v ∈ Submodule.span ℂ (e '' ((next n A).points : Set X)),
        dist (f j) v < 1 / (n + 1 : ℝ) := by
    obtain ⟨hsub, hcut, hfresh, happ⟩ := Classical.choose_spec
      (extend A ((Finset.range (n + 1)).image f) (1 / (n + 1 : ℝ)) (by positivity))
    refine ⟨hsub, hcut, hfresh, ?_⟩
    intro j hj
    exact happ (f j) (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  let stages : ℕ → FiniteStage e level V := fun n => Nat.rec initial next n
  refine ⟨{ stage := stages
            nested := fun n => (next_spec n (stages n)).1
            increasing := fun n => (next_spec n (stages n)).2.1
            fresh := fun n => (next_spec n (stages n)).2.2.1
            approximate := fun n => (next_spec n (stages n)).2.2.2 }, rfl⟩

namespace SelectionStages

variable {e : X → H} {level : X → ℕ} {V : ℕ → Submodule ℂ H} {f : ℕ → H}
variable (S : SelectionStages e level V f)

/-- The selected frequency set. -/
def selected : Set X := {x | ∃ n, x ∈ (S.stage n).points}

theorem points_monotone : Monotone (fun n => ((S.stage n).points : Set X)) := by
  exact monotone_nat_of_le_succ (fun n => S.nested n)

theorem cutoff_strictMono : StrictMono (fun n => (S.stage n).cutoff) :=
  strictMono_nat_of_lt_succ S.increasing

/-- Future selections cannot add points at or below an old cutoff. -/
theorem low_level_mem (n : ℕ) {x : X} (hx : x ∈ S.selected)
    (hlevel : level x ≤ (S.stage n).cutoff) : x ∈ (S.stage n).points := by
  obtain ⟨m, hm⟩ := hx
  by_cases hmn : m ≤ n
  · exact S.points_monotone hmn hm
  · have hnm : n ≤ m := by omega
    clear hmn
    induction m, hnm using Nat.le_induction with
    | base => exact hm
    | succ m hnm ih =>
        by_cases hmem : x ∈ (S.stage m).points
        · exact ih hmem
        · have hh := S.fresh m x hm hmem
          have hc := S.cutoff_strictMono.monotone hnm
          omega

/-- Only finitely many selected frequencies can lie in any bounded level range. -/
theorem finite_bounded_levels (R : ℕ) : (S.selected ∩ {x | level x ≤ R}).Finite := by
  have hc : R ≤ (S.stage R).cutoff := S.cutoff_strictMono.id_le R
  apply (S.stage R).points.finite_toSet.subset
  intro x hx
  exact S.low_level_mem R hx.1 (hx.2.trans hc)

/-- A bounded level set meets the selected frequencies in finitely many points. -/
theorem finite_intersection_of_level_bounded {K : Set X} (R : ℕ)
    (hK : ∀ x ∈ K, level x ≤ R) : (S.selected ∩ K).Finite :=
  (S.finite_bounded_levels R).subset (fun x hx => ⟨hx.1, hK x hx.2⟩)

/-- Locally bounded frequency levels turn block finiteness into local finiteness. -/
theorem locally_finite [TopologicalSpace X]
    (bounded : ∀ x : X, ∃ U ∈ nhds x, ∃ R : ℕ, ∀ y ∈ U, level y ≤ R) :
    ∀ x : X, ∃ U ∈ nhds x, (S.selected ∩ U).Finite := by
  intro x
  obtain ⟨U, hU, R, hR⟩ := bounded x
  exact ⟨U, hU, S.finite_intersection_of_level_bounded R hR⟩

/-- Every enumeration without repetitions escapes all bounded frequency levels. -/
theorem escape_levels (a : ℕ → X) (ha : Function.Injective a)
    (hselected : ∀ n, a n ∈ S.selected) :
    Filter.Tendsto (fun n => level (a n)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro R
  have hfin : (a ⁻¹' (S.selected ∩ {x | level x ≤ R})).Finite :=
    (S.finite_bounded_levels R).preimage ha.injOn
  have he : ∀ᶠ n in Filter.atTop, a n ∉ S.selected ∩ {x | level x ≤ R} := by
    rw [← Nat.cofinite_eq_atTop]
    exact hfin.compl_mem_cofinite
  filter_upwards [he] with n hn
  have hnlevel : ¬ level (a n) ≤ R := fun h => hn ⟨hselected n, h⟩
  omega

/-- If high frequency levels have large radius, every enumeration without
repetitions also escapes to infinity in radius. -/
theorem escape_radius (radius : X → ℝ)
    (high_level : ∀ R : ℝ, ∃ N : ℕ, ∀ x, N ≤ level x → R ≤ radius x)
    (a : ℕ → X) (ha : Function.Injective a) (hselected : ∀ n, a n ∈ S.selected) :
    Filter.Tendsto (fun n => radius (a n)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro R
  obtain ⟨N, hN⟩ := high_level R
  filter_upwards [(Filter.tendsto_atTop.mp (S.escape_levels a ha hselected)) N] with n hn
  exact hN (a n) hn

/-- Every member of a dense target sequence lies in the closed selected span. -/
theorem target_mem_closure (j : ℕ) :
    f j ∈ (Submodule.span ℂ (e '' S.selected)).topologicalClosure := by
  classical
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let n := max j k
  obtain ⟨v, hv, hd⟩ := S.approximate n j (le_max_left _ _)
  have hspan : Submodule.span ℂ (e '' ((S.stage (n + 1)).points : Set X)) ≤
      Submodule.span ℂ (e '' S.selected) := by
    apply Submodule.span_mono
    exact Set.image_mono (fun x hx => ⟨n + 1, hx⟩)
  refine ⟨v, hspan hv, hd.trans_le ?_⟩
  have hden : (k + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right (le_max_right j k) 1
  exact (one_div_le_one_div_of_le (by positivity) hden).trans (le_of_lt hk)

/-- The approximation conditions imply totality; completeness is not a stage hypothesis. -/
theorem complete (hf : DenseRange f) :
    (Submodule.span ℂ (e '' S.selected)).topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  have hsub : Set.range f ⊆
      ((Submodule.span ℂ (e '' S.selected)).topologicalClosure : Set H) := by
    rintro _ ⟨j, rfl⟩
    exact S.target_mem_closure j
  exact closure_minimal hsub (Submodule.isClosed_topologicalClosure _) (hf x)

/-- An interpolant at a selected point remains biorthogonal to every future point. -/
theorem exists_global_interpolant
    (vanish : ∀ N g, g ∈ V N → ∀ x, N < level x → @inner ℂ H _ g (e x) = 0)
    {x : X} (hx : x ∈ S.selected) :
    ∃ N g, g ∈ V N ∧ ∀ y ∈ S.selected,
      @inner ℂ H _ g (e y) = if x = y then 1 else 0 := by
  classical
  obtain ⟨n, hn⟩ := hx
  obtain ⟨g, hg, hint⟩ := (S.stage n).interpolate x hn
  refine ⟨(S.stage n).cutoff, g, hg, ?_⟩
  intro y hy
  by_cases hymem : y ∈ (S.stage n).points
  · exact hint y hymem
  · have hxy : x ≠ y := by rintro rfl; exact hymem hn
    have hlevel : (S.stage n).cutoff < level y := by
      by_contra hh
      exact hymem (S.low_level_mem n hy (by omega))
    simp only [if_neg hxy]
    exact vanish _ g hg y hlevel

/-- Choosing the individual witnesses produces an actual global dual family. -/
theorem exists_biorthogonal
    (vanish : ∀ N g, g ∈ V N → ∀ x, N < level x → @inner ℂ H _ g (e x) = 0) :
    ∃ g : S.selected → H,
      (∀ x, ∃ N, g x ∈ V N) ∧
      ∀ x y : S.selected, @inner ℂ H _ (g x) (e y) = if x = y then 1 else 0 := by
  classical
  have h := fun x : S.selected => S.exists_global_interpolant vanish x.property
  choose N g hg hint using h
  refine ⟨g, fun x => ⟨N x, hg x⟩, ?_⟩
  intro x y
  simpa only [Subtype.ext_iff] using hint x y y.property

end SelectionStages

/-- Abstract finite-stage selection for a separable complex Hilbert space.
The conclusion includes totality, a global biorthogonal family with interpolant
membership, and finiteness in bounded frequency levels. -/
theorem select_complete_biorthogonal [TopologicalSpace.SeparableSpace H]
    (e : X → H) (level : X → ℕ) (V : ℕ → Submodule ℂ H)
    (initial : FiniteStage e level V) (extend : HasFiniteExtensions e level V)
    (vanish : ∀ N g, g ∈ V N → ∀ x, N < level x → @inner ℂ H _ g (e x) = 0) :
    ∃ Λ : Set X, (Submodule.span ℂ (e '' Λ)).topologicalClosure = ⊤ ∧
      (∀ R : ℕ, (Λ ∩ {x | level x ≤ R}).Finite) ∧
      ∃ g : Λ → H, (∀ x, ∃ N, g x ∈ V N) ∧
        ∀ x y : Λ, @inner ℂ H _ (g x) (e y) = if x = y then 1 else 0 := by
  obtain ⟨f, hf⟩ := TopologicalSpace.exists_dense_seq H
  obtain ⟨S, _⟩ := exists_selectionStages e level V initial extend f
  exact ⟨S.selected, S.complete hf, S.finite_bounded_levels, S.exists_biorthogonal vanish⟩

end RieszEuclidean.CompleteMinimal
