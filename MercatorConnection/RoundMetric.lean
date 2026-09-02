/-
# The round metric `dθ² + sin²θ dφ²` as a `ContMDiffRiemannianMetric`

This file builds on `MercatorGeom.lean` (the unit sphere `S2` in `EuclideanSpace ℝ (Fin 3)`
modelled on `𝓡 2`, the spherical chart with open domain `sphSource`, the coordinate functions
`θ_coord`, `φ_coord` and the coordinate coframe `dθ`, `dφ`).

The main results are:

* `roundMetricOnSphSource` : a `Bundle.ContMDiffRiemannianMetric (𝓡 2) ⊤` structure on the
  tangent bundle of the open submanifold `sphSourceOpens` of `S2`, whose underlying bilinear
  form is the orthonormal-coframe expression `dθ ⊗ dθ + sin²θ · dφ ⊗ dφ`.
* `roundMetricS2` : a `Bundle.ContMDiffRiemannianMetric (𝓡 2) ⊤` structure on the tangent
  bundle of all of `S2`, obtained by pulling back the ambient inner product of
  `EuclideanSpace ℝ (Fin 3)` along the inclusion.  (The coframe expression above cannot be used
  globally: `sin θ` vanishes at the poles and `dφ` is not even defined across the anti-meridian.)
* `sphereInner_eq_roundInner` : on `sphSource` the two metrics agree, so the global metric
  really is an extension of the round metric `dθ² + sin²θ dφ²`.

Along the way we prove some general-purpose lemmas about open submanifolds, von Neumann
boundedness of the unit ball of a positive definite form, and smoothness of sections of the
bundle of bilinear forms on a tangent bundle.
-/

import MercatorConnection.MercatorGeom

open Bundle Set Bornology TopologicalSpace ContinuousLinearMap
open scoped Manifold Topology ContDiff

noncomputable section

/-! ## Open submanifolds: the differential of the inclusion is the identity -/

section OpenSubmanifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The inclusion of an open submanifold has the identity as its differential:
in the charts of `U` (which are the restrictions of the charts of `M`) it *is* the identity. -/
theorem hasMFDerivAt_subtype_val (U : Opens M) (x : U) :
    HasMFDerivAt I I (Subtype.val : U → M) x (ContinuousLinearMap.id 𝕜 E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have key : ∀ᶠ y in 𝓝[range I] ((extChartAt I x) x),
      writtenInExtChartAt I I x (Subtype.val : U → M) y = id y := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    show extChartAt I (x : M) (((extChartAt I x).symm y : U) : M) = y
    exact (extChartAt I x).right_inv hy
  refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq key ?_
  show extChartAt I (x : M) ((((extChartAt I x).symm ((extChartAt I x) x)) : U) : M) = _
  rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  exact rfl

theorem mfderiv_subtype_val (U : Opens M) (x : U) :
    mfderiv I I (Subtype.val : U → M) x = ContinuousLinearMap.id 𝕜 E :=
  (hasMFDerivAt_subtype_val U x).mfderiv

/-- Restricting a function to an open submanifold does not change its differential. -/
theorem mfderiv_comp_subtype_val {U : Opens M} {f : M → M'} {x : U}
    (hf : MDifferentiableAt I I' f x.val) :
    mfderiv I I' (fun y : U => f y.val) x = mfderiv I I' f x.val := by
  have h := (hf.hasMFDerivAt).comp x (hasMFDerivAt_subtype_val (I := I) U x)
  exact HasMFDerivAt.mfderiv h

end OpenSubmanifold

/-! ## Von Neumann boundedness of the unit ball of a positive definite form -/

section VonNeumann

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- On a finite-dimensional real normed space, the "unit ball" `{v | b v v < 1}` of a positive
definite continuous bilinear form `b` is von Neumann bounded.  Indeed `v ↦ b v v` attains a
positive minimum `m` on the (compact) unit sphere, so `{v | b v v < 1} ⊆ closedBall 0 (√(1/m))`. -/
theorem isVonNBounded_of_posDef (b : F →L[ℝ] F →L[ℝ] ℝ) (hb : ∀ v : F, v ≠ 0 → 0 < b v v) :
    IsVonNBounded ℝ {v : F | b v v < 1} := by
  rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
  rcases subsingleton_or_nontrivial F with hF | hF
  · exact ⟨0, fun v _ => by simp [Subsingleton.elim v 0]⟩
  obtain ⟨u, hu, hmin⟩ : ∃ u ∈ Metric.sphere (0 : F) 1, IsMinOn (fun v => b v v)
      (Metric.sphere (0 : F) 1) u :=
    (isCompact_sphere (0 : F) 1).exists_isMinOn (NormedSpace.sphere_nonempty.2 zero_le_one)
      (Continuous.continuousOn (by fun_prop))
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  set m : ℝ := b u u with hm
  have hmpos : 0 < m := hb u hu0
  refine ⟨Real.sqrt (1 / m), fun v hv => ?_⟩
  simp only [mem_setOf_eq] at hv
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · have hnorm : (0:ℝ) < ‖v‖ := norm_pos_iff.2 hv0
    have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : F) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hnorm.ne']
    have hle : m ≤ b (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := hmin hmem
    have hexp : b (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = (‖v‖⁻¹)^2 * b v v := by
      simp [map_smul]; ring
    rw [hexp] at hle
    have h2 : (0:ℝ) < ‖v‖^2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hle (le_of_lt h2)
    have h4 : (‖v‖⁻¹)^2 * b v v * ‖v‖^2 = b v v := by field_simp
    rw [h4] at h3
    have h5 : ‖v‖^2 ≤ 1 / m := by
      rw [le_div_iff₀ hmpos]; nlinarith
    exact (Real.le_sqrt (norm_nonneg v) (by positivity)).2 h5

end VonNeumann

/-! ## Sections of the bundle of bilinear forms

Two general lemmas which reduce smoothness of a section `x ↦ g x` of the bundle of bilinear
forms to smoothness of its expression in a local trivialization, and identify the differential
of a scalar function read in coordinates. -/

section BilinearSection

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The bundle of bilinear forms `E ⊗ E → ℝ` is the hom-bundle `Hom (E, Hom (E, ℝ))`; reading
a bilinear form in the trivialization at `x₀` just means precomposing both arguments with the
inverse of that trivialization. -/
theorem inCoordinates_bilin_apply {x₀ x : B} (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (g : E x →L[ℝ] E x →L[ℝ] ℝ) (v w : F) :
    inCoordinates F E (F →L[ℝ] ℝ) (fun b ↦ E b →L[ℝ] ℝ) x₀ x x₀ x g v w
      = g ((trivializationAt F E x₀).symm x v) ((trivializationAt F E x₀).symm x w) := by
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial B ℝ) hx hx (by simp)]
  simp

/-- Smoothness of a section of the bundle of bilinear forms, reduced to smoothness of its
expression `G` in the trivialization at the point. -/
theorem contMDiffAt_bilin_section {g : Π b : B, E b →L[ℝ] E b →L[ℝ] ℝ}
    {G : B → (F →L[ℝ] F →L[ℝ] ℝ)} {x₀ : B}
    (hG : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n G x₀)
    (hEq : ∀ᶠ x in 𝓝 x₀, ∀ v w : F, G x v w =
      g x ((trivializationAt F E x₀).symm x v) ((trivializationAt F E x₀).symm x w)) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, hG.congr_of_eventuallyEq ?_⟩
  filter_upwards [hEq, (trivializationAt F E x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x₀)] with x h1 h2
  ext v w
  rw [inCoordinates_bilin_apply h2, h1]

end BilinearSection

section MFDerivCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m n : WithTop ℕ∞}

/-- The differential of a scalar function, read in the trivialization of the tangent bundle
at `x₀` (the target tangent bundle, over the model space `ℝ`, is canonically trivial). -/
theorem inTangentCoordinates_scalar_apply [IsManifold I 1 M] (f : M → ℝ) (x₀ x : M) (v : E) :
    inTangentCoordinates I 𝓘(ℝ, ℝ) id f (mfderiv I 𝓘(ℝ, ℝ) f) x₀ x v
      = mfderiv I 𝓘(ℝ, ℝ) f x ((trivializationAt E (TangentSpace I) x₀).symm x v) := by
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, Trivialization.symmL_apply]
  rfl

end MFDerivCoordinates

/-! ## (a) The round metric `dθ² + sin²θ dφ²` on the chart domain `sphSource` -/

section RoundOnSphSource

open Real

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

local notation "F₂" => EuclideanSpace ℝ (Fin 2)

/-- The chart domain `sphSource`, as an open submanifold of `S2`. -/
def sphSourceOpens : Opens S2 := ⟨sphSource, sph_open_source⟩

lemma mem_sphSourceOpens (x : sphSourceOpens) : (x : S2) ∈ sphSource := x.2

lemma mem_S2_open_of_sphSourceOpens (x : sphSourceOpens) : (x : S2) ∈ S2_open :=
  sphSource_subset_S2_open x.2

/-- The `θ` coordinate as a function on the open submanifold. -/
def θU (x : sphSourceOpens) : ℝ := θ_coord (x : S2)

/-- The `φ` coordinate as a function on the open submanifold. -/
def φU (x : sphSourceOpens) : ℝ := φ_coord (x : S2)

lemma θU_contMDiffAt (x : sphSourceOpens) : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ⊤ θU x :=
  (θ_coord_contMDiffAt (mem_S2_open_of_sphSourceOpens x)).of_le le_top |>.comp x
    (contMDiff_subtype_val.contMDiffAt)

lemma φU_contMDiffAt (x : sphSourceOpens) : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ φU x :=
  (φ_coord_contMDiffAt (mem_sphSourceOpens x)).comp x (contMDiff_subtype_val.contMDiffAt)

/-- The intrinsic differential of `θ` on the open submanifold is the restriction of `dθ`. -/
lemma mfderiv_θU (x : sphSourceOpens) : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) θU x = dθ (x : S2) :=
  mfderiv_comp_subtype_val
    ((θ_coord_contMDiffAt (mem_S2_open_of_sphSourceOpens x)).mdifferentiableAt (by simp))

/-- The intrinsic differential of `φ` on the open submanifold is the restriction of `dφ`. -/
lemma mfderiv_φU (x : sphSourceOpens) : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φU x = dφ (x : S2) :=
  mfderiv_comp_subtype_val
    ((φ_coord_contMDiffAt (mem_sphSourceOpens x)).mdifferentiableAt (by simp))

/-- The round metric on `sphSource`, in the orthonormal coframe form
`g = dθ ⊗ dθ + sin²θ · dφ ⊗ dφ = ε₁ ⊗ ε₁ + ε₂ ⊗ ε₂` with `ε₁ = dθ`, `ε₂ = sin θ · dφ`. -/
def roundInner (x : sphSourceOpens) :
    TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  (dθ (x : S2)).smulRight (dθ (x : S2))
    + (Real.sin (θ_coord (x : S2))) ^ 2 • (dφ (x : S2)).smulRight (dφ (x : S2))

lemma roundInner_apply (x : sphSourceOpens) (v w : TangentSpace (𝓡 2) x) :
    roundInner x v w = dθ (x : S2) v * dθ (x : S2) w
      + (Real.sin (θ_coord (x : S2))) ^ 2 * (dφ (x : S2) v * dφ (x : S2) w) := by
  rfl

lemma roundInner_symm (x : sphSourceOpens) (v w : TangentSpace (𝓡 2) x) :
    roundInner x v w = roundInner x w v := by
  rw [roundInner_apply, roundInner_apply, mul_comm (dθ (x : S2) v), mul_comm (dφ (x : S2) v)]

lemma roundInner_pos (x : sphSourceOpens) (v : TangentSpace (𝓡 2) x) (hv : v ≠ 0) :
    0 < roundInner x v v := by
  have hsin : Real.sin (θ_coord (x : S2)) ≠ 0 :=
    sinθ_ne_zero _ (mem_S2_open_of_sphSourceOpens x)
  rw [roundInner_apply]
  rcases eq_or_ne (dθ (x : S2) v) 0 with h1 | h1
  · rcases eq_or_ne (dφ (x : S2) v) 0 with h2 | h2
    · refine absurd ?_ hv
      have := frame_dual (mem_sphSourceOpens x) v
      rw [h1, h2] at this
      have h := this.symm
      rw [zero_smul, zero_smul, add_zero] at h
      exact h
    · have : 0 < (Real.sin (θ_coord (x : S2))) ^ 2 * (dφ (x : S2) v * dφ (x : S2) v) := by
        have h3 : 0 < dφ (x : S2) v * dφ (x : S2) v := mul_self_pos.2 h2
        positivity
      rw [h1]; simpa using this
  · have h3 : 0 < dθ (x : S2) v * dθ (x : S2) v := mul_self_pos.2 h1
    have h4 : 0 ≤ (Real.sin (θ_coord (x : S2))) ^ 2 * (dφ (x : S2) v * dφ (x : S2) v) := by
      have : 0 ≤ dφ (x : S2) v * dφ (x : S2) v := mul_self_nonneg _
      positivity
    linarith

lemma roundInner_isVonNBounded (x : sphSourceOpens) :
    IsVonNBounded ℝ {v : TangentSpace (𝓡 2) x | roundInner x v v < 1} :=
  isVonNBounded_of_posDef (F := EuclideanSpace ℝ (Fin 2)) (roundInner x) (roundInner_pos x)

lemma roundInner_contMDiff :
    ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) ∞
      (fun b : sphSourceOpens ↦ TotalSpace.mk'
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) b (roundInner b)) := by
  intro x₀
  -- `A` and `Bc` are `dθ` and `dφ` read in the trivialization of the tangent bundle at `x₀`.
  set A : sphSourceOpens → (F₂ →L[ℝ] ℝ) :=
    inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ) id θU (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) θU) x₀ with hAdef
  set Bc : sphSourceOpens → (F₂ →L[ℝ] ℝ) :=
    inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ) id φU (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φU) x₀ with hBdef
  have hAsm : ContMDiffAt (𝓡 2) 𝓘(ℝ, F₂ →L[ℝ] ℝ) ∞ A x₀ :=
    (θU_contMDiffAt x₀).mfderiv_const le_top
  have hBsm : ContMDiffAt (𝓡 2) 𝓘(ℝ, F₂ →L[ℝ] ℝ) ∞ Bc x₀ :=
    (φU_contMDiffAt x₀).mfderiv_const (by simp)
  have hsin : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => (Real.sin (θU x)) ^ 2) x₀ :=
    ((((Real.contDiff_sin (n := ⊤)).pow 2).contDiffAt).contMDiffAt.comp x₀
      (θU_contMDiffAt x₀)).of_le le_top
  have hbil : ContDiff ℝ ∞
      (fun p : (F₂ →L[ℝ] ℝ) × (F₂ →L[ℝ] ℝ) => p.1.smulRight p.2) :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := F₂) (F := F₂ →L[ℝ] ℝ)).contDiff.of_le le_top

  have hadd : ContDiff ℝ ∞
      (fun p : (F₂ →L[ℝ] F₂ →L[ℝ] ℝ) × (F₂ →L[ℝ] F₂ →L[ℝ] ℝ) => p.1 + p.2) :=
    contDiff_fst.add contDiff_snd

  let V := F₂ →L[ℝ] F₂ →L[ℝ] ℝ

  letI : IsBoundedSMul ℝ (F₂ →L[ℝ] F₂ →L[ℝ] ℝ) :=
    ⟨
      fun x y₁ y₂ => by
        rw [dist_eq_norm']
        have h1 : dist y₁ y₂ = ‖y₂ - y₁‖ := by rw [dist_eq_norm' y₁ y₂]
        have hnorm := (inferInstance : NormedSpace ℝ (F₂ →L[ℝ] F₂ →L[ℝ] ℝ)).norm_smul_le x (y₂ - y₁)
        calc
          dist (x • y₁) (x • y₂) = ‖x • y₂ - x • y₁‖ := by rw [dist_eq_norm' (x • y₁) (x • y₂)]
          _ = ‖x • (y₂ - y₁)‖ := by
            congr 1
            rw [smul_sub x y₂ y₁]
          _ ≤ ‖x‖ * ‖y₂ - y₁‖ := by exact hnorm
          _ = dist x 0 * dist y₁ y₂ := by rw [dist_eq_norm' x 0, dist_eq_norm' y₁ y₂]; simp
          _ ≤ ‖0 - x‖ * dist y₁ y₂ := by rw [dist_eq_norm' x 0],
      fun x₁ x₂ y => by
        have h1 : dist x₁ x₂ = ‖x₂ - x₁‖ := by
          exact dist_eq_norm' x₁ x₂
        have hnorm :=
          (inferInstance : NormedSpace ℝ
            (F₂ →L[ℝ] F₂ →L[ℝ] ℝ)).norm_smul_le (x₂ - x₁) y
        calc
          dist (x₁ • y) (x₂ • y) = ‖x₂ • y - x₁ • y‖ := by
            exact dist_eq_norm' (x₁ • y) (x₂ • y)
          _ = ‖(x₂ - x₁) • y‖ := by
            congr 1
            rw [sub_smul x₂ x₁ y]
          _ ≤ ‖x₂ - x₁‖ * ‖y‖ := by
            exact hnorm
          _ = ‖x₂ - x₁‖ * dist y 0 := by
            rw [dist_eq_norm' y 0]
            rw [zero_sub y, norm_neg y]
          _ = dist x₁ x₂ * dist y 0 := by
            rw [h1]
    ⟩

  have hsmul : ContDiff ℝ ∞
      (fun p : ℝ × (F₂ →L[ℝ] F₂ →L[ℝ] ℝ) => p.1 • p.2) :=
    contDiff_fst.smul contDiff_snd

  have hG : ContMDiffAt (𝓡 2) 𝓘(ℝ, F₂ →L[ℝ] F₂ →L[ℝ] ℝ) ∞
      (fun x => (A x).smulRight (A x)
        + (Real.sin (θU x)) ^ 2 • (Bc x).smulRight (Bc x)) x₀ :=
    hadd.contDiffAt.comp_contMDiffAt
      ((hbil.contDiffAt.comp_contMDiffAt (hAsm.prodMk_space hAsm)).prodMk_space
        (hsmul.contDiffAt.comp_contMDiffAt
          (hsin.prodMk_space
            (hbil.contDiffAt.comp_contMDiffAt (hBsm.prodMk_space hBsm)))))

  refine contMDiffAt_bilin_section hG (Filter.Eventually.of_forall fun x v w => ?_)
  have hAv : ∀ u : F₂, A x u
      = dθ (x : S2) ((trivializationAt F₂ (TangentSpace (𝓡 2)) x₀).symm x u) := fun u => by
    rw [hAdef, inTangentCoordinates_scalar_apply, mfderiv_θU]
    rfl
  have hBv : ∀ u : F₂, Bc x u
      = dφ (x : S2) ((trivializationAt F₂ (TangentSpace (𝓡 2)) x₀).symm x u) := fun u => by
    rw [hBdef, inTangentCoordinates_scalar_apply, mfderiv_φU]
    rfl
  show A x v * A x w + (Real.sin (θU x)) ^ 2 * (Bc x v * Bc x w) = _
  rw [roundInner_apply, hAv, hAv, hBv, hBv]
  rfl

/-- **The round metric on the chart domain.**  `g = dθ² + sin²θ dφ²` is a smooth Riemannian
metric on the tangent bundle of the open submanifold `sphSource` of `S2`. -/
def roundMetricOnSphSource :
    Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (fun x : sphSourceOpens ↦ TangentSpace (𝓡 2) x) where
  inner := roundInner
  symm := roundInner_symm
  pos := roundInner_pos
  isVonNBounded := roundInner_isVonNBounded
  contMDiff := roundInner_contMDiff

end RoundOnSphSource

/-! ## (b) A Riemannian metric on all of `S2`

The coframe expression of part (a) does **not** extend to all of `S2`:

* `sin θ` vanishes at the two poles, so the second term of `dθ ⊗ dθ + sin²θ dφ ⊗ dφ`
  degenerates there and `frame_dual` (which is what makes the form positive definite) fails;
* worse, `φ_coord` is not even continuous across the anti-meridian `{x ≤ 0, y = 0}`
  (`Complex.arg` jumps by `2π`), so `dφ` is not a smooth section of the cotangent bundle
  outside `sphSource`.

A global metric therefore has to be built differently.  We use the *first fundamental form*:
the pullback `g x v w = ⟪dι_x v, dι_x w⟫` of the ambient inner product of
`EuclideanSpace ℝ (Fin 3)` along the inclusion `ι : S2 → EuclideanSpace ℝ (Fin 3)`.
(On `sphSource` this is exactly the round metric of part (a); this is proved below as
`sphereInner_eq_roundInner`.)

Writing the ambient inner product as a sum of coordinate products, the pullback is
`∑ i, d(xᵢ) ⊗ d(xᵢ)`, so the very same argument as in part (a) applies, with the three
globally smooth functions `x ↦ xᵢ` in place of `θ` and `φ`. -/

section RoundOnS2

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

local notation "F₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

instance factFinrankE₃ : Fact (Module.finrank ℝ E₃ = 2 + 1) :=
  ⟨by simp only [finrank_euclideanSpace, Fintype.card_fin]⟩

/-- The differential `dι_x` of the inclusion `S2 → EuclideanSpace ℝ (Fin 3)`. -/
def dIota (x : S2) : TangentSpace (𝓡 2) x →L[ℝ] E₃ :=
  mfderiv (𝓡 2) 𝓘(ℝ, E₃) Subtype.val x

/-- The `i`-th ambient coordinate, as a function on the sphere. -/
def ambCoord (i : Fin 3) (x : S2) : ℝ := (x : E₃) i

lemma ambCoord_contMDiff (i : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ⊤ (ambCoord i) :=
  ((EuclideanSpace.proj i).contMDiff).comp contMDiff_coe_sphere

/-- The differential of the `i`-th ambient coordinate: a section of the cotangent bundle. -/
def dAmb (i : Fin 3) (x : S2) : TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (ambCoord i) x

lemma dAmb_eq_proj_comp (i : Fin 3) (x : S2) :
    dAmb i x = (EuclideanSpace.proj i).comp (dIota x) := by
  have h : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ)
      ((EuclideanSpace.proj i : E₃ →L[ℝ] ℝ) ∘ (Subtype.val : S2 → E₃)) x
      ((EuclideanSpace.proj i).comp (dIota x)) :=
    (ContinuousLinearMap.hasMFDerivAt (EuclideanSpace.proj i)).comp x
      ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  exact h.mfderiv

/-- The first fundamental form of the unit sphere: the pullback of the ambient inner product,
written as `∑ i, d(xᵢ) ⊗ d(xᵢ)`. -/
def sphereInner (x : S2) : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  ∑ i : Fin 3, (dAmb i x).smulRight (dAmb i x)

lemma sphereInner_apply (x : S2) (v w : TangentSpace (𝓡 2) x) :
    sphereInner x v w = ∑ i : Fin 3, dAmb i x v * dAmb i x w := by
  simp only [sphereInner, sum_apply]
  rfl

/-- The first fundamental form really is the pullback of the ambient inner product. -/
lemma sphereInner_eq_inner (x : S2) (v w : TangentSpace (𝓡 2) x) :
    sphereInner x v w = inner ℝ (dIota x v) (dIota x w) := by
  rw [sphereInner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dAmb_eq_proj_comp]
  simp [mul_comm]

lemma sphereInner_symm (x : S2) (v w : TangentSpace (𝓡 2) x) :
    sphereInner x v w = sphereInner x w v := by
  rw [sphereInner_eq_inner, sphereInner_eq_inner, real_inner_comm]

lemma sphereInner_pos (x : S2) (v : TangentSpace (𝓡 2) x) (hv : v ≠ 0) :
    0 < sphereInner x v v := by
  rw [sphereInner_eq_inner, real_inner_self_eq_norm_sq]
  have h : dIota x v ≠ 0 := by
    intro h
    apply hv
    apply mfderiv_coe_sphere_injective (n := 2) x
    rw [map_zero]
    exact h
  positivity

lemma sphereInner_isVonNBounded (x : S2) :
    IsVonNBounded ℝ {v : TangentSpace (𝓡 2) x | sphereInner x v v < 1} :=
  isVonNBounded_of_posDef (F := F₂) (sphereInner x) (sphereInner_pos x)

lemma sphereInner_contMDiff :
    ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F₂ →L[ℝ] F₂ →L[ℝ] ℝ)) ⊤
      (fun b : S2 ↦ TotalSpace.mk' (F₂ →L[ℝ] F₂ →L[ℝ] ℝ) b (sphereInner b)) := by
  intro x₀
  set A : Fin 3 → S2 → (F₂ →L[ℝ] ℝ) := fun i =>
    inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ) id (ambCoord i)
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (ambCoord i)) x₀ with hAdef
  have hAsm : ∀ i, ContMDiffAt (𝓡 2) 𝓘(ℝ, F₂ →L[ℝ] ℝ) ⊤ (A i) x₀ := fun i =>
    ((ambCoord_contMDiff i).contMDiffAt).mfderiv_const (by simp)
  have hbil : ContDiff ℝ ⊤ (fun p : (F₂ →L[ℝ] ℝ) × (F₂ →L[ℝ] ℝ) => p.1.smulRight p.2) :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := F₂) (F := F₂ →L[ℝ] ℝ)).contDiff
  have hG : ContMDiffAt (𝓡 2) 𝓘(ℝ, F₂ →L[ℝ] F₂ →L[ℝ] ℝ) ⊤
      (fun x => ∑ i : Fin 3, (A i x).smulRight (A i x)) x₀ :=
    ContMDiffAt.sum fun i _ => hbil.contDiffAt.comp_contMDiffAt ((hAsm i).prodMk_space (hAsm i))
  refine contMDiffAt_bilin_section hG (Filter.Eventually.of_forall fun x v w => ?_)
  have hAv : ∀ (i : Fin 3) (u : F₂), A i x u
      = dAmb i x ((trivializationAt F₂ (TangentSpace (𝓡 2)) x₀).symm x u) := fun i u => by
    rw [hAdef, inTangentCoordinates_scalar_apply]
    rfl
  show ∑ i : Fin 3, A i x v * A i x w = _
  rw [sphereInner_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [hAv, hAv]

/-- **A global Riemannian metric on `S2`.**  The first fundamental form
`g x v w = ⟪dι_x v, dι_x w⟫`, the pullback of the ambient inner product of
`EuclideanSpace ℝ (Fin 3)` along the inclusion, is a `C^ω` Riemannian metric on the whole
tangent bundle of `S2`.  It restricts to the round metric `dθ² + sin²θ dφ²` on `sphSource`
(`sphereInner_eq_roundInner`). -/
def roundMetricS2 :
    Bundle.ContMDiffRiemannianMetric (𝓡 2) ⊤ F₂ (fun x : S2 ↦ TangentSpace (𝓡 2) x) where
  inner := sphereInner
  symm := sphereInner_symm
  pos := sphereInner_pos
  isVonNBounded := sphereInner_isVonNBounded
  contMDiff := sphereInner_contMDiff

end RoundOnS2

/-! ## The two metrics agree on `sphSource`

We now verify the claim made above: on the chart domain, the first fundamental form
`sphereInner` really is the coframe metric `roundInner = dθ ⊗ dθ + sin²θ dφ ⊗ dφ`.

The computation is the classical one: the inclusion pulled back along the parametrization
`sphInv : (θ, φ) ↦ (sin θ cos φ, sin θ sin φ, cos θ)` has partial derivatives
`∂_θ = (cos θ cos φ, cos θ sin φ, -sin θ)` and `∂_φ = (-sin θ sin φ, sin θ cos φ, 0)`,
which are orthogonal with `‖∂_θ‖ = 1` and `‖∂_φ‖ = sin θ`. -/

section Agreement

open Real

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

local notation "F₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The `θ`-partial derivative of the spherical parametrization. -/
def sphUvec (t p : ℝ) : E₃ :=
  (cos t * cos p) • EuclideanSpace.single 0 1
    + (cos t * sin p) • EuclideanSpace.single 1 1
    + (-sin t) • EuclideanSpace.single 2 1

/-- The `φ`-partial derivative of the spherical parametrization. -/
def sphVvec (t p : ℝ) : E₃ :=
  (-(sin t * sin p)) • EuclideanSpace.single 0 1
    + (sin t * cos p) • EuclideanSpace.single 1 1
    + (0 : ℝ) • EuclideanSpace.single 2 1

lemma sphUvec_apply (t p : ℝ) (i : Fin 3) :
    sphUvec t p i = ![cos t * cos p, cos t * sin p, -sin t] i := by
  fin_cases i <;>
    simp [sphUvec]

lemma sphVvec_apply (t p : ℝ) (i : Fin 3) :
    sphVvec t p i = ![-(sin t * sin p), sin t * cos p, 0] i := by
  fin_cases i <;>
    simp [sphVvec]

lemma inner_sphUvec_self (t p : ℝ) : inner ℝ (sphUvec t p) (sphUvec t p) = 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    sphUvec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  nlinarith [sin_sq_add_cos_sq t, sin_sq_add_cos_sq p]

lemma inner_sphUvec_sphVvec (t p : ℝ) : inner ℝ (sphUvec t p) (sphVvec t p) = 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    sphUvec_apply, sphVvec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

lemma inner_sphVvec_sphUvec (t p : ℝ) : inner ℝ (sphVvec t p) (sphUvec t p) = 0 := by
  rw [real_inner_comm]
  exact inner_sphUvec_sphVvec t p

lemma inner_sphVvec_self (t p : ℝ) : inner ℝ (sphVvec t p) (sphVvec t p) = sin t ^ 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    sphVvec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  nlinarith [sin_sq_add_cos_sq p]

/-- The spherical parametrization written as a combination of the standard basis vectors. -/
lemma sphInvVec_eq_smul (q : F₂) :
    sphInvVec q = (sin (q 0) * cos (q 1)) • (EuclideanSpace.single 0 1 : E₃)
      + (sin (q 0) * sin (q 1)) • (EuclideanSpace.single 1 1 : E₃)
      + (cos (q 0)) • (EuclideanSpace.single 2 1 : E₃) := by
  ext i
  fin_cases i <;>
    simp [sphInvVec]

/-- The (Fréchet) derivative of the spherical parametrization: its two partial derivatives
are `sphUvec` and `sphVvec`. -/
lemma hasFDerivAt_sphInvVec (q : F₂) :
    HasFDerivAt sphInvVec
      ((EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ).smulRight (sphUvec (q 0) (q 1))
        + (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ).smulRight (sphVvec (q 0) (q 1))) q := by
  have h0 : HasFDerivAt (fun q : F₂ => q 0) (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ) q :=
    (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun q : F₂ => q 1) (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ) q :=
    (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ).hasFDerivAt
  have hs0 : HasFDerivAt (fun q : F₂ => sin (q 0))
      (cos (q 0) • (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ)) q :=
    by simpa [Function.comp_def] using (Real.hasDerivAt_sin (q 0)).comp_hasFDerivAt q h0
  have hc0 : HasFDerivAt (fun q : F₂ => cos (q 0))
      ((-sin (q 0)) • (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ)) q :=
    by simpa [Function.comp_def] using (Real.hasDerivAt_cos (q 0)).comp_hasFDerivAt q h0
  have hs1 : HasFDerivAt (fun q : F₂ => sin (q 1))
      (cos (q 1) • (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ)) q :=
    by simpa [Function.comp_def] using (Real.hasDerivAt_sin (q 1)).comp_hasFDerivAt q h1
  have hc1 : HasFDerivAt (fun q : F₂ => cos (q 1))
      ((-sin (q 1)) • (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ)) q :=
    by simpa [Function.comp_def] using (Real.hasDerivAt_cos (q 1)).comp_hasFDerivAt q h1
  have h := (((hs0.mul hc1).smul_const (EuclideanSpace.single 0 1 : E₃)).add
      ((hs0.mul hs1).smul_const (EuclideanSpace.single 1 1 : E₃))).add
      (hc0.smul_const (EuclideanSpace.single 2 1 : E₃))
  have hfun : sphInvVec = fun q : F₂ =>
      (sin (q 0) * cos (q 1)) • (EuclideanSpace.single 0 1 : E₃)
        + (sin (q 0) * sin (q 1)) • (EuclideanSpace.single 1 1 : E₃)
        + (cos (q 0)) • (EuclideanSpace.single 2 1 : E₃) := funext sphInvVec_eq_smul
  rw [hfun]
  have hEq :
      ((EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ).smulRight (sphUvec (q 0) (q 1))
        + (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ).smulRight (sphVvec (q 0) (q 1)))
      =
      (ContinuousLinearMap.smulRight
          (sin (q 0) • -sin (q 1) • (EuclideanSpace.proj 1 : F₂ →L[ℝ] ℝ)
            + cos (q 1) • cos (q 0) • (EuclideanSpace.proj 0 : F₂ →L[ℝ] ℝ))
          (EuclideanSpace.single 0 1 : E₃)
        + ContinuousLinearMap.smulRight
          (sin (q 0) • cos (q 1) • (EuclideanSpace.proj 1 : F₂ →L[ℝ] ℝ)
            + sin (q 1) • cos (q 0) • (EuclideanSpace.proj 0 : F₂ →L[ℝ] ℝ))
          (EuclideanSpace.single 1 1 : E₃)
        + ContinuousLinearMap.smulRight
          (-sin (q 0) • (EuclideanSpace.proj 0 : F₂ →L[ℝ] ℝ))
          (EuclideanSpace.single 2 1 : E₃)) := by
    ext u i
    fin_cases i <;>
      simp [sphUvec, sphVvec, EuclideanSpace.proj] <;>
      ring
  rw [hEq]
  exact h

lemma fderiv_sphInvVec_e0 (q : F₂) :
    fderiv ℝ sphInvVec q (EuclideanSpace.single 0 1) = sphUvec (q 0) (q 1) := by
  rw [(hasFDerivAt_sphInvVec q).fderiv]
  simp

lemma fderiv_sphInvVec_e1 (q : F₂) :
    fderiv ℝ sphInvVec q (EuclideanSpace.single 1 1) = sphVvec (q 0) (q 1) := by
  rw [(hasFDerivAt_sphInvVec q).fderiv]
  simp

/-- The differential of the inclusion, composed with the differential of the parametrization,
is the ordinary derivative of `sphInvVec`. -/
lemma dIota_mfderiv_sphInv {x : S2} (hx : x ∈ sphSource) (u : F₂) :
    dIota x (mfderiv 𝓘(ℝ, F₂) (𝓡 2) sphInv (sphFwd x) u)
      = fderiv ℝ sphInvVec (sphFwd x) u := by
  have hxx : sphInv (sphFwd x) = x := sph_left_inv x hx
  have hcomp : mfderiv 𝓘(ℝ, F₂) 𝓘(ℝ, E₃) (fun q : F₂ => ((sphInv q : S2) : E₃)) (sphFwd x)
      = (mfderiv (𝓡 2) 𝓘(ℝ, E₃) (Subtype.val : S2 → E₃) (sphInv (sphFwd x))).comp
        (mfderiv 𝓘(ℝ, F₂) (𝓡 2) sphInv (sphFwd x)) :=
    mfderiv_comp _ ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero)
      (sphInv_contMDiff.contMDiffAt.mdifferentiableAt (by norm_num))
  rw [hxx] at hcomp
  have hsv : (fun q : F₂ => ((sphInv q : S2) : E₃)) = sphInvVec := rfl
  rw [hsv, mfderiv_eq_fderiv] at hcomp
  rw [hcomp]
  rfl

lemma sphFwd_apply_zero (x : S2) : sphFwd x 0 = θ_coord x := rfl

lemma sphFwd_apply_one (x : S2) : sphFwd x 1 = φ_coord x := rfl

/-- The image of the coordinate vector field `∂θ` in the ambient space. -/
lemma dIota_Xθ {x : S2} (hx : x ∈ sphSource) :
    dIota x (Xθ x) = sphUvec (θ_coord x) (φ_coord x) := by
  simp only [Xθ]
  rw [dIota_mfderiv_sphInv hx, fderiv_sphInvVec_e0, sphFwd_apply_zero, sphFwd_apply_one]

/-- The image of the coordinate vector field `∂φ` in the ambient space. -/
lemma dIota_Xφ {x : S2} (hx : x ∈ sphSource) :
    dIota x (Xφ x) = sphVvec (θ_coord x) (φ_coord x) := by
  simp only [Xφ]
  rw [dIota_mfderiv_sphInv hx, fderiv_sphInvVec_e1, sphFwd_apply_zero, sphFwd_apply_one]

/-- `sphFwd` and `sphInv` are mutually inverse, so their differentials are too. -/
lemma mfderiv_sphFwd_mfderiv_sphInv {x : S2} (hx : x ∈ sphSource) (u : F₂) :
    mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x (mfderiv 𝓘(ℝ, F₂) (𝓡 2) sphInv (sphFwd x) u) = u := by
  have hq : sphFwd x ∈ sphTarget := sph_map_source hx
  have hxx : sphInv (sphFwd x) = x := sph_left_inv x hx
  have hid : mfderiv 𝓘(ℝ, F₂) 𝓘(ℝ, F₂) (sphFwd ∘ sphInv) (sphFwd x)
      = ContinuousLinearMap.id ℝ F₂ := by
    have hev : ∀ᶠ r in nhds (sphFwd x), sphFwd (sphInv r) = r :=
      Filter.eventually_of_mem (sph_open_target.mem_nhds hq) fun r hr => sph_right_inv r hr
    exact HasMFDerivAt.mfderiv ((hasMFDerivAt_id _).congr_of_eventuallyEq hev)
  have hcomp : mfderiv 𝓘(ℝ, F₂) 𝓘(ℝ, F₂) (sphFwd ∘ sphInv) (sphFwd x)
      = (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd (sphInv (sphFwd x))).comp
        (mfderiv 𝓘(ℝ, F₂) (𝓡 2) sphInv (sphFwd x)) :=
    mfderiv_comp _ (by rw [hxx]; exact sphFwd_mdiffAt hx)
      (sphInv_contMDiff.contMDiffAt.mdifferentiableAt (by norm_num))
  rw [hxx] at hcomp
  rw [hcomp] at hid
  calc mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x (mfderiv 𝓘(ℝ, F₂) (𝓡 2) sphInv (sphFwd x) u)
      = ((mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x).comp
          (mfderiv 𝓘(ℝ, F₂) (𝓡 2) sphInv (sphFwd x))) u := rfl
    _ = u := by rw [hid]; rfl

lemma dθ_eq_proj_comp {x : S2} (hx : x ∈ sphSource) :
    dθ x = (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ).comp
      (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x) := by
  have h : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ)
      ((EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ) ∘ sphFwd) x
      ((EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ).comp
        (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x)) :=
    (ContinuousLinearMap.hasMFDerivAt _).comp x (sphFwd_mdiffAt hx).hasMFDerivAt
  exact h.mfderiv

lemma dφ_eq_proj_comp {x : S2} (hx : x ∈ sphSource) :
    dφ x = (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ).comp
      (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x) :=
  HasMFDerivAt.mfderiv
    (HasMFDerivAt.comp x (ContinuousLinearMap.hasMFDerivAt (EuclideanSpace.proj 1))
      (sphFwd_mdiffAt hx).hasMFDerivAt)

lemma dθ_Xθ {x : S2} (hx : x ∈ sphSource) : dθ x (Xθ x) = 1 := by
  rw [dθ_eq_proj_comp hx]
  show (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ)
    (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x (Xθ x)) = 1
  simp only [Xθ]
  rw [mfderiv_sphFwd_mfderiv_sphInv hx]
  simp

lemma dθ_Xφ {x : S2} (hx : x ∈ sphSource) : dθ x (Xφ x) = 0 := by
  rw [dθ_eq_proj_comp hx]
  show (EuclideanSpace.proj (0 : Fin 2) : F₂ →L[ℝ] ℝ)
    (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x (Xφ x)) = 0
  simp only [Xφ]
  rw [mfderiv_sphFwd_mfderiv_sphInv hx]
  simp

lemma dφ_Xθ {x : S2} (hx : x ∈ sphSource) : dφ x (Xθ x) = 0 := by
  rw [dφ_eq_proj_comp hx]
  show (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ)
    (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x (Xθ x)) = 0
  simp only [Xθ]
  rw [mfderiv_sphFwd_mfderiv_sphInv hx]
  simp

lemma dφ_Xφ {x : S2} (hx : x ∈ sphSource) : dφ x (Xφ x) = 1 := by
  rw [dφ_eq_proj_comp hx]
  show (EuclideanSpace.proj (1 : Fin 2) : F₂ →L[ℝ] ℝ)
    (mfderiv (𝓡 2) 𝓘(ℝ, F₂) sphFwd x (Xφ x)) = 1
  simp only [Xφ]
  rw [mfderiv_sphFwd_mfderiv_sphInv hx]
  simp

/-- Expansion of the differential of the inclusion in the coordinate frame. -/
lemma dIota_apply {x : S2} (hx : x ∈ sphSource) (v : TangentSpace (𝓡 2) x) :
    dIota x v = dθ x v • sphUvec (θ_coord x) (φ_coord x)
      + dφ x v • sphVvec (θ_coord x) (φ_coord x) := by
  conv_lhs => rw [← frame_dual hx v]
  rw [map_add, map_smul, map_smul, dIota_Xθ hx, dIota_Xφ hx]

/-- **The two metrics agree.**  On the chart domain, the first fundamental form of the sphere
is the coframe metric `dθ ⊗ dθ + sin²θ · dφ ⊗ dφ`. -/
theorem sphereInner_eq_roundInner (x : sphSourceOpens) (v w : TangentSpace (𝓡 2) (x : S2)) :
    sphereInner (x : S2) v w = roundInner x v w := by
  have hx : (x : S2) ∈ sphSource := x.2
  rw [sphereInner_eq_inner, dIota_apply hx v, dIota_apply hx w, roundInner_apply]
  rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    inner_sphUvec_self, inner_sphUvec_sphVvec, inner_sphVvec_sphUvec, inner_sphVvec_self]
  ring

end Agreement
