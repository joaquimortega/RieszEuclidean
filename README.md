# Riesz bases and complete minimal exponentials in Euclidean space

A Lean 4 and Mathlib formalization of Joaquim Ortega-Cerdà's
[Riesz bases in Euclidean space](paper/RieszEuclidean.pdf)
([LaTeX source](paper/RieszEuclidean.tex)).

The project proves geometric obstructions to exponential Riesz bases and
constructs complete and minimal exponential systems on every nonempty bounded
open convex domain. The results concern the functions

$$
e_\lambda(x)=e^{2\pi i\langle\lambda,x\rangle},
\qquad \lambda\in\Lambda\subset\mathbb R^n,
$$

in $L^2(\Omega)$ with respect to Lebesgue measure. An exponential Riesz basis
is a complete family satisfying

$$
A\sum_{\lambda\in\Lambda}|c_\lambda|^2
\leq
\left\|\sum_{\lambda\in\Lambda}c_\lambda e_\lambda\right\|_{L^2(\Omega)}^2
\leq
B\sum_{\lambda\in\Lambda}|c_\lambda|^2
$$

for some $0<A\leq B<\infty$ and every finitely supported coefficient family.
In Lean, this is expressed by a continuous linear equivalence from
$\ell^2(\Lambda)$ to $L^2(\Omega)$ sending each coordinate vector to its
exponential.

## Nonexistence of exponential Riesz bases

**Convex domains with smooth boundary.** If $n\geq2$ and
$\Omega\subset\mathbb R^n$ is nonempty, bounded, open, and convex with
$C^2$ boundary, then $L^2(\Omega)$ admits no exponential Riesz basis.
The theorem requires neither strict convexity nor positive curvature at every
boundary point. Its geometric ingredient is a positively curved boundary patch
whose intersections with nontrivial translates of the boundary have surface
measure zero.

The formalization also proves nonexistence for:

- Every ball of positive radius in dimension $n\geq2$.
- Every invertible affine image of a ball in dimension $n\geq2$.
- Every noncollinear planar triangle.
- Every bounded convex planar polygon with a maximal side parallel to no other
  maximal side. In particular, this covers polygons with an odd number of
  maximal sides.

The polygon statements use finite irredundant supporting halfspace
presentations with nonzero normals and nonempty faces. The side count refers
to actual maximal boundary segments. All these nonexistence results quantify
over arbitrary real frequency sets $\Lambda$.

### A general boundary measure criterion

Let $\Omega\subset\mathbb R^n$ be nonempty, bounded, and open, with
Lebesgue-null boundary. Suppose there is a finite nonzero positive measure
$\nu$ supported on $\partial\Omega$ such that

$$
\nu\bigl(\partial\Omega\cap(\partial\Omega+\theta)\bigr)=0
\qquad\text{for every }\theta\neq0,
$$

and, for $\nu$-almost every boundary point, every neighborhood meets both
$\Omega$ and $\mathbb R^n\setminus\overline\Omega$ in sets of positive
Lebesgue measure. Then $L^2(\Omega)$ admits no exponential Riesz basis.

This criterion supplies the analytic obstruction behind the geometric results.
The proof compares stationary Fourier cutoff projections with a continuous
family of bump projections; the boundary creates a jump incompatible with a
uniform projection distance below one.

## Complete and minimal exponentials on convex domains

**Existence theorem.** For every $n\geq1$ and every nonempty bounded open
convex set $\Omega\subset\mathbb R^n$, there is a locally finite frequency
set $\Lambda$ such that $(e_\lambda)_{\lambda\in\Lambda}$ is complete and
minimal in $L^2(\Omega)$. There are biorthogonal functions
$(g_\lambda)_{\lambda\in\Lambda}$ supported in the John ellipsoid $E$ of
$\overline\Omega$, satisfying

$$
\int_\Omega e_\mu(x)\overline{g_\lambda(x)}\,dx
=\delta_{\lambda\mu}.
$$

Here completeness means that the complex linear span is dense, and minimality
means that no exponential belongs to the closed span of the others. This is
ordinary minimality: the biorthogonal functions have individual finite norms,
with no uniform norm bound required. Local finiteness means that every compact
set contains only finitely many frequencies. The John ellipsoid is an inscribed
ellipsoid of maximal volume. The theorem assumes no boundary smoothness or
strict convexity.

The same frequency set is complete and minimal in $L^2(D)$ for every measurable
intermediate set

$$
\operatorname{int}E\subseteq D\subseteq\Omega
\qquad\text{up to Lebesgue-null sets}.
$$

The supported biorthogonal functions restrict to biorthogonals on each such
$D$. If $\operatorname{int}E$ is a proper subset of $\Omega$, the biorthogonal
family is incomplete in $L^2(\Omega)$.

After normalizing the John ellipsoid to the closed unit ball, the construction
uses nested interpolation spaces of dimension $\binom{2N+n}{n}$. Their
functions are supported in the unit ball, and the spaces are exactly the
orthogonal annihilators of the later frequency spheres.

## Fourier analysis and convolution support

The project proves the analytic results used in these constructions:

- **Euclidean Fourier analysis:** the unitary $L^2$ Fourier transform,
  Schwartz density and Parseval, measurable-domain cutoff projections, their
  integral kernels, and compatibility with translations.
- **Stationary spectral measures:** every vector correlation of a strongly
  continuous unitary representation of $\mathbb R^n$ on a separable complex
  Hilbert space is represented by a finite positive measure.
- **Paley–Wiener–Schwartz:** an entire function of finite exponential type with
  polynomial growth on $\mathbb R^n$ is the Fourier transform of a compactly
  supported tempered distribution.
- **Entire division:** an entire quotient of finite exponential type functions
  has finite exponential type when the denominator is nonzero at the origin.
- **Titchmarsh–Lions:** for nonzero compactly supported tempered distributions
  $u,v$ and a distribution $w$ representing their convolution,

  $$
  \operatorname{conv}(\operatorname{supp}w)
  =\operatorname{conv}(\operatorname{supp}u)
  +\operatorname{conv}(\operatorname{supp}v),
  $$

  where $+$ denotes the Minkowski sum.

Other proved tools include affine invariance, the equivalence between
exponential Riesz bases and the small-bump projection gap condition, and the
orthogonal projection gap lemmas. The configuration space of uniformly
separated sets is compact and metrizable; Beurling weak convergence agrees
with vague convergence of counting measures, and translation hulls carry
invariant probability measures.

## Formal statements and verification

[MainResults.lean](MainResults.lean) presents the public definitions and theorem
statements in the namespace `RieszEuclidean.Results`. The main entry points are
`convex_C2_no_exponentialRieszBasis`,
`general_boundary_no_exponentialRieszBasis`,
`complete_minimal_bounded_open_convex`, `complete_minimal_scope`, and
`titchmarsh_lions`.

The modular proofs are in [RieszEuclidean/](RieszEuclidean/).
[RieszEuclideanStandalone.lean](RieszEuclideanStandalone.lean) contains the
generated single-file formalization. The proofs use only Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. CI checks compilation, linters,
blueprint completeness, standalone source correspondence, metadata, and
transitive axioms. See the [blueprint](blueprint/README.md) for the proof
structure and [verification record](reviews/titchmarsh-progress.md) for the
kernel and Comparator checks.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/joaquimortega/RieszEuclidean.git
cd RieszEuclidean
lake exe cache get
lake build
lake build MainResults RieszEuclideanStandalone
lake env lean -DwarningAsError=true scripts/Lint.lean
lake env lean -DwarningAsError=true scripts/LintMainResults.lean
lake env lean -DwarningAsError=true scripts/LintStandalone.lean
python3 scripts/check_blueprint.py --require-complete
python3 scripts/build_standalone.py --check
python3 scripts/check_axioms.py
```

The repository pins Lean 4.19.0 and its Mathlib dependencies. All project proof
sources are included; Lake fetches Mathlib and its transitive dependencies.
Additional documentation covers [formalization metadata](formalization.yaml),
[code provenance](PROVENANCE.md), and [Comparator tooling](standalone/TOOLS.md).
