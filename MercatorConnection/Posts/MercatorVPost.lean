import VersoBlog
import Mathlib

open Verso.Genre Blog
open Real Set Metric Manifold Bundle
open scoped BigOperators Manifold ContDiff

set_option linter.style.longLine false

#doc (Post) "The Mercator Connection on S²" =>

```leanInit mercatorV
```

The second file in the Mercator connection development defines `mercatorCov`
itself — the connection map sending a section σ of TS² to a section of
Hom(TS², TS²). At a point x with colatitude θ, the sole nonzero Christoffel
symbol is $`Γ^φ_{θφ} = \cot θ`, contributing a correction term
`cot θ · dφ(σ) · dθ` to the φ-component of the covariant derivative.
All other Christoffel symbols are zero. This makes the rhumb lines — lines of
constant bearing on a nautical chart — the geodesics of the connection, and
gives it nonzero torsion $`T(e_1, e_2) = \cot θ \cdot e_2`.

The connection is built from the genuine differential-geometric coframe and
frame of the spherical chart, defined in a companion file `MercatorGeom`. The
covectors `dθ x = mvfderiv (𝓡 2) θ_coord x` and
`dφ x = mvfderiv (𝓡 2) φ_coord x` are smooth sections of the cotangent bundle —
the honest differentials of `θ_coord = arccos z` and `φ_coord = arg`. The
vectors `Xθ`, `Xφ` are the push-forwards of the standard basis under the chart
inverse `sphInv`, forming the dual frame. Because these are honest smooth
objects rather than constant model-space vectors, `mercatorCov` satisfies
Mathlib's upstream `IsCovariantDerivativeOn` interface, whose `add` and
`leibniz` axioms are stated for sections differentiable as bundled sections of
the tangent bundle.

The key technical bridge is `mdifferentiableAt_mfderiv_apply` (from
`MercatorGeom`): bundled differentiability of σ implies differentiability of
the scalar functions `y ↦ dθ y (σ y)` and `y ↦ dφ y (σ y)`, so that
`mvfderiv` can be applied to them inside the axiom proofs. The product rule
for `mvfderiv` is not in Mathlib in this pointwise form, so it is proved
locally. We need a variable context:

```lean mercatorV
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
```

The product rule follows immediately from `hasMFDerivAt.mul`:

```lean mercatorV
lemma mvfderiv_mul_S2 {S2 : Type*} [TopologicalSpace S2]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S2]
    [IsManifold (𝓡 2) ⊤ S2]
    {g f : S2 → ℝ} {x : S2}
    (hg : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) g x)
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f x) :
    mvfderiv (𝓡 2) (g * f) x =
      g x • mvfderiv (𝓡 2) f x + f x • mvfderiv (𝓡 2) g x :=
  (hg.hasMFDerivAt.mul hf.hasMFDerivAt).mfderiv

end
```

The `add` axiom of `IsCovariantDerivativeOn` reduces to linearity of
`mvfderiv` (`mvfderiv_add`), linearity of the frame covectors `dθ`, `dφ`, and
a `module` call to close the linear algebra. The `leibniz` axiom uses the
product rule, then the frame-dual identity
`σ x = dθ(σ x) · Xθ x + dφ(σ x) · Xφ x` to expand σ in the correction term,
after which `module` closes it again. The proofs are short because the design
is right: honest smooth objects, honest bundled differentiability, and a named
bridge lemma.

This file also absorbed a migration from Lean 4.30 to 4.31. The function
`extDerivFun` — the manifold exterior derivative of a scalar function — was
renamed `mvfderiv` throughout Mathlib. The signatures are identical: both take
an explicit model-with-corners argument `I`, the function `g : M → F`, and the
point `x : M`, returning an element of `TangentSpace I x →L[𝕜] F`. The
corresponding lemma `extDerivFun_add` became `mvfderiv_add`. A pure rename,
but a reminder that even a stable API surface shifts between toolchain bumps,
and that keeping version-sensitive infrastructure quarantined from the
geometrically essential definitions is worth the discipline.
