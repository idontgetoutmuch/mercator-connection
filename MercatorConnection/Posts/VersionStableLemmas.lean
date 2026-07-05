import VersoBlog
import Mathlib

open Verso.Genre Blog
open Bundle
open scoped Manifold Topology ContDiff

set_option linter.style.longLine false

#doc (Post) "Version-stable geometric lemmas for the Mercator connection" =>
```leanInit mercator
```

I am formalizing the Mercator connection on $`S^2` — a connection with torsion
whose sole nonzero Christoffel symbol is $`Γ^φ_{θφ} = \cot θ`. Along the way I
need a small stock of differential-geometry lemmas that do *not* depend on the
`extDerivFun` / `IsCovariantDerivativeOn` API, which entered Mathlib later.
They concern the tangent bundle of a general smooth manifold, and since they
are insulated from the moving parts, they should survive toolchain bumps that
the rest of the development does not.

The central result says: pairing the differential of a $`C^2` scalar function
(a smooth section of the cotangent bundle) with a differentiable vector field
yields a differentiable scalar function. This is the key tool that lets
differentiability of a *bundled* section be transferred to differentiability
of its components in the smooth coframe $`\{dθ, dφ\}`.

We work over an arbitrary nontrivially normed field, on a manifold modelled on
a normed space:

```lean mercator
open Bundle
open scoped Manifold Topology ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
```

The statement quantifies the vector field as a dependent function
`σ : Π y : M, TangentSpace I y`, with its differentiability expressed through
the associated section of the total space — the honest way to say "the vector
field is differentiable" in Mathlib's bundle language. Note the hypothesis on
`f` is `C^2`, not `C^1`: we differentiate `f` once to form `mfderiv`, and then
need one more degree for the *result* to be differentiable.

```lean mercator
lemma mdifferentiableAt_mfderiv_apply
    (f : M → 𝕜) (σ : Π y : M, TangentSpace I y) (x : M)
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) 2 f x)
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, E))
      (fun y => TotalSpace.mk' E y (σ y)) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (fun y => (mfderiv I 𝓘(𝕜, 𝕜) f y) (σ y)) x := by
  have h_map : MDifferentiableAt I (𝓘(𝕜, 𝕜).prod 𝓘(𝕜, 𝕜)) (fun y => TotalSpace.mk' 𝕜 (f y)
    ((mfderiv I 𝓘(𝕜, 𝕜) f y) (σ y))) x := by
    have h_map : MDifferentiableAt I (𝓘(𝕜, E →L[𝕜] 𝕜))
      (fun y => (inTangentCoordinates I 𝓘(𝕜, 𝕜) id f (fun y => mfderiv I 𝓘(𝕜, 𝕜) f y) x) y) x := by
      convert ( hf.mfderiv_const ( show 1 + 1 ≤ 2 by norm_num ) ) |>
        ContMDiffAt.mdifferentiableAt using 1;
      simp +decide only [forall_const];
    convert MDifferentiableAt.clm_apply_of_inCoordinates h_map hσ
      ( hf.mdifferentiableAt ( by norm_num ) ) using 1;
    exact rfl
  rw [ mdifferentiableAt_totalSpace ] at h_map;
  convert h_map.2.congr_of_eventuallyEq _ using 1;
  simp +decide only [trivializationAt, trivializationAt_model_space_apply, Filter.EventuallyEq.refl]

end
```

The proof pivots on `MDifferentiableAt.clm_apply_of_inCoordinates`: the
differential `y ↦ mfderiv f y` is a family of continuous linear maps living in
varying fibres, so to apply it to `σ y` one first expresses it
`inTangentCoordinates` — reading everything through the tangent-bundle
trivialization at the basepoint — where the pairing becomes an honest
application of a continuous-linear-map-valued function to a vector-valued
function. The final `mdifferentiableAt_totalSpace` step peels the base
component off the resulting section, and since the target bundle is trivial
(`𝕜 × 𝕜`), the trivialization there is the identity, which is what the closing
`simp` says.
