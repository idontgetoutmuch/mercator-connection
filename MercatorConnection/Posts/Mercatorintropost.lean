import VersoBlog
import Mathlib
import MercatorConnection.MercatorGeom

open Verso.Genre Blog
open Real Set Manifold Bundle
open scoped BigOperators Manifold ContDiff
set_option maxRecDepth 4000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

#doc (Post) "Mercator: A Connection with Torsion" =>

```leanInit mercatorIntro
```

In most presentations of Riemannian geometry the fundamental theorem —
sometimes called "the miracle of Riemannian geometry" — is given pride of
place: for any semi-Riemannian manifold there is a *unique* torsion-free metric
connection, the Levi-Civita connection. Because of this, and because the
primary application is General Relativity, connections with torsion receive
little attention. It turns out we are all familiar with one: the Mercator
projection. Some mathematical physics texts, e.g. Nakahara (2003), allude to
this but leave the details to the reader.

In 2016 I worked through the details using SageManifolds. Here I redo as much
as possible in Lean 4 with Mathlib, and explain what the formalization reveals
that the Sage version could not.

*The manifold and chart.*

We work on $`S^2` minus the closed anti-meridian — the set `sphSource` defined
in `MercatorGeom`. In Sage the polar chart is declared by giving the parameter
range `th:(0,pi)`, `ph:(0,2*pi)` and the domain is only that range. In Lean the
chart domain is a *subset of the sphere*, and you must prove the chart inverse
lands in it. This is where `sphSource` — not the poles but the closed
anti-meridian — emerged as the correct domain, catching an earlier false axiom
`sphericalChart.source = S2_open` that Sage's workflow cannot surface.

The chart inverse `sphInv` sends `(θ, φ)` to
`(sin θ cos φ, sin θ sin φ, cos θ)`. Its smoothness is:

```lean mercatorIntro
open Real Set Metric Manifold Bundle
open scoped BigOperators Real Nat Pointwise Manifold ContDiff
set_option maxRecDepth 4000
set_option synthInstance.maxSize 128

#check @sphInv_contMDiff
-- ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) ⊤ sphInv
```

*The coframe and frame.*

Rather than constant model-space vectors, we use the genuine
differential-geometric coframe. The covectors `dθ` and `dφ` are the honest
differentials of `θ_coord = arccos z` and `φ_coord = arg`, and `Xθ`, `Xφ`
are push-forwards of the standard basis under `sphInv`. Their duality:

```lean mercatorIntro
#check @frame_dual
-- ∀ {x : S2}, x ∈ sphSource →
--   ∀ (v : TangentSpace (𝓡 2) x), v = dθ x v • Xθ x + dφ x v • Xφ x
```

*The Mercator connection.*

Let us define two vectors to be parallel if their angles to a given meridian
are the same. For this to be true we must have a connection $`\nabla` with
$`\nabla e_1 = \nabla e_2 = 0`, where
$`\{e_1, e_2\} = \{\partial_\theta, \frac{1}{\sin\theta}\partial_\phi\}` is the
orthonormal frame.

Since $`\partial_\phi = \sin\theta \cdot e_2`, the condition
$`\nabla e_2 = 0` gives
$`\nabla_X \partial_\phi = X(\sin\theta)\, e_2 = \cot\theta \, X(\theta)\, \partial_\phi`,
so in the coordinate frame the sole nonzero Christoffel symbol is
$`\Gamma^\phi_{\theta\phi} = \cot\theta`. In Lean:

```lean mercatorIntro
open Classical in
noncomputable def mercatorCov :
    (Π x : S2, TangentSpace (𝓡 2) x) →
    (Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) :=
  fun σ x =>
    if _hx : x ∈ sphSource then
      let θ    := θ_coord x
      let cotθ := Real.cos θ / Real.sin θ
      let Dσθ : TangentSpace (𝓡 2) x →L[ℝ] ℝ := mvfderiv (𝓡 2) (fun y ↦ dθ y (σ y)) x
      let Dσφ : TangentSpace (𝓡 2) x →L[ℝ] ℝ := mvfderiv (𝓡 2) (fun y ↦ dφ y (σ y)) x
      let Γ : TangentSpace (𝓡 2) x →L[ℝ] ℝ := (cotθ * dφ x (σ x)) • dθ x
      (Dσθ.smulRight (Xθ x)) + ((Dσφ + Γ).smulRight (Xφ x))
    else 0
```

The formula: the covariant derivative of σ in direction v has θ-component
`Dσθ(v)` (unchanged, since $`\Gamma^\theta = 0`) and φ-component
`Dσφ(v) + cot θ · dφ(σ x) · dθ(v)`.

*Verification: the Leibniz rule.*

Sage verifies the connection axioms by symbolic computation. In Lean we prove
them from the definitions. The key bridge — from bundled differentiability of σ
to differentiability of the scalar components `y ↦ dθ y (σ y)` — is
`mdifferentiableAt_mfderiv_apply` from `MercatorGeom`. The Leibniz rule uses
the product rule for `mvfderiv` and the frame-dual identity. The unfolding
lemma:

```lean mercatorIntro
lemma mercatorCov_apply (σ : Π y : S2, TangentSpace (𝓡 2) y) {x : S2}
    (hx : x ∈ sphSource) :
    mercatorCov σ x =
      (mvfderiv (𝓡 2) (fun y ↦ dθ y (σ y)) x).smulRight (Xθ x) +
      (mvfderiv (𝓡 2) (fun y ↦ dφ y (σ y)) x +
        ((Real.cos (θ_coord x) / Real.sin (θ_coord x)) * dφ x (σ x)) • dθ x).smulRight
        (Xφ x) := by
  simp only [mercatorCov, dif_pos hx]
```

*Torsion and geodesics.*

The torsion of `mercatorCov` is $`T(e_1, e_2) = \cot\theta \cdot e_2`. Since
the Levi-Civita connection is the unique torsion-free metric connection, and
`mercatorCov` is metric-compatible but has nonzero torsion, it is distinct.
Mathlib does not yet have a torsion API, so this remains a calculation rather
than a formal theorem.

The geodesic equations in polar coordinates are
$`\ddot\gamma^\theta = 0` and
$`\ddot\gamma^\phi + \cot\theta \cdot \dot\gamma^\phi \dot\gamma^\theta = 0`.
The solutions $`\gamma^\theta(t) = t`,
$`\gamma^\phi(t) = \alpha\log\tan(t/2)` become straight lines in Mercator
coordinates — the *rhumb lines* of constant compass bearing that made the
projection indispensable to navigators for four centuries.

*What Lean does that Sage cannot.*

When I wrote the 2016 post, specifying `(0, π) × (0, 2π)` as the coordinate
range seemed natural and I moved on. Lean forced me to identify the precise
subset of S² on which the chart is defined and prove the chart inverse lands
in it. The natural first attempt `sphSource = S2_open` is false: the
anti-meridian is not the same as the poles. Lean caught it:

```lean mercatorIntro
example : sphSource ⊆ S2_open := sphSource_subset_S2_open
```

Sage cannot make this error visible because it does not track chart domains as
subsets of the manifold. Lean cannot avoid noticing it.
