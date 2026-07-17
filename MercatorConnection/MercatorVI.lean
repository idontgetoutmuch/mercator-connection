/-
# The Mercator Connection on S² — frame-first formulation

A bearing is a direction held fixed relative to the compass frame
{e₁, e₂} = {∂_θ, (1/sin θ) ∂_φ}.  Accordingly the Mercator connection is
DEFINED by: the compass frame is parallel — all connection coefficients
vanish in that frame.  This matches the SageManifolds construction
`nab.add_coef(e)` from the 2016 blog post, where the coefficients were set
in the orthonormal frame (and were all zero).

DEFINITION: ∇e₁ = ∇e₂ = 0 — a bearing is a direction held fixed relative to
the compass frame, so the connection is the one making that frame parallel.
`mercatorCov_e₁` / `mercatorCov_e₂` verify that the formula below (zero
coefficients relative to the coframe ε) faithfully encodes this definition,
i.e. that ε really is dual to e.

Consequences, now theorems rather than definitions:
  - Γ^φ_{θφ} = cot θ in the coordinate frame  (`proof_wanted`, see below)
  - Torsion T(e₁, e₂) = cot θ · e₂      (future work)

New here relative to `MercatorGeom`: the pairing identities
`dθ(Xθ) = 1, dφ(Xθ) = 0, dθ(Xφ) = 0, dφ(Xφ) = 1` (`frame_pairing`), proved
from the right inverse `sph_right_inv` exactly as `frame_dual` is proved from
the left inverse `sph_left_inv`.  These belong in `MercatorGeom` eventually.
-/

import Mathlib
import MercatorConnection.MercatorGeom

open scoped BigOperators Real Nat Pointwise Manifold ContDiff
set_option maxRecDepth 4000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Set Metric Manifold Bundle

noncomputable section

/-! ## `mvfderiv` helpers -/

/-- `mvfderiv` of a function locally constant near `x` vanishes. -/
lemma mvfderiv_of_eventuallyEq_const {f : S2 → ℝ} {c : ℝ} {x : S2}
    (h : f =ᶠ[nhds x] fun _ ↦ c) :
    mvfderiv (𝓡 2) f x = 0 := by
  have h1 : mvfderiv (𝓡 2) f x = mvfderiv (𝓡 2) (fun _ : S2 ↦ c) x := h.mfderiv_eq
  rw [h1]
  exact mfderiv_const

/-! ## The component-differentiability bridge (unchanged) -/

lemma mdiffAt_dθcomp {σ : Π y : S2, TangentSpace (𝓡 2) y} {x : S2}
    (hσ : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) y (σ y)) x)
    (hx : x ∈ S2_open) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ dθ y (σ y)) x :=
  mdifferentiableAt_mfderiv_apply θ_coord σ x ((θ_coord_contMDiffAt hx).of_le (by norm_num)) hσ

lemma mdiffAt_dφcomp {σ : Π y : S2, TangentSpace (𝓡 2) y} {x : S2}
    (hσ : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) y (σ y)) x)
    (hx : x ∈ sphSource) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ dφ y (σ y)) x :=
  mdifferentiableAt_mfderiv_apply φ_coord σ x
    ((φ_coord_contMDiffAt hx).of_le (by decide)) hσ

/-! ## Pairing identities: `{dθ, dφ}` is dual to `{Xθ, Xφ}` on `sphSource`

`frame_dual` (in `MercatorGeom`) uses the left inverse `sphInv ∘ sphFwd = id`;
the pairings use the right inverse `sphFwd ∘ sphInv = id` in exactly the same
way.  Belongs in `MercatorGeom` eventually. -/

lemma frame_pairing {x : S2} (hx : x ∈ sphSource) :
    dθ x (Xθ x) = 1 ∧ dφ x (Xθ x) = 0 ∧ dθ x (Xφ x) = 0 ∧ dφ x (Xφ x) = 1 := by
  set Dfwd : TangentSpace (𝓡 2) x →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) sphFwd x
  set Dinv : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace (𝓡 2) x :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) sphInv (sphFwd x)
  -- the coframe through `Dfwd`, exactly as in `frame_dual`
  have hdθ : dθ x = (EuclideanSpace.proj (0 : Fin 2)).comp Dfwd := by
    apply HasMFDerivAt.mfderiv
    apply HasMFDerivAt.comp x
      (ContinuousLinearMap.hasMFDerivAt (EuclideanSpace.proj (0 : Fin 2)))
      (sphFwd_mdiffAt hx).hasMFDerivAt
  have hdφ : dφ x = (EuclideanSpace.proj (1 : Fin 2)).comp Dfwd := by
    apply HasMFDerivAt.mfderiv
    apply HasMFDerivAt.comp x
      (ContinuousLinearMap.hasMFDerivAt (EuclideanSpace.proj (1 : Fin 2)))
      (sphFwd_mdiffAt hx).hasMFDerivAt
  -- the frame through `Dinv`, definitionally
  have hXθ : Xθ x = Dinv (EuclideanSpace.single (0 : Fin 2) 1) := rfl
  have hXφ : Xφ x = Dinv (EuclideanSpace.single (1 : Fin 2) 1) := rfl
  -- right inverse: `Dfwd ∘ Dinv = id`, mirroring `h_Dinv_Dfwd` in `frame_dual`
  have hxx : sphInv (sphFwd x) = x := sph_left_inv x hx
  have h_right : Dfwd.comp Dinv = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
    have h_inv : ∀ᶠ q in nhds (sphFwd x), sphFwd (sphInv q) = q :=
      Filter.eventually_of_mem (IsOpen.mem_nhds sph_open_target (sph_map_source hx))
        fun q hq => sph_right_inv q hq
    have hid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (sphFwd ∘ sphInv) (sphFwd x)
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :=
      HasMFDerivAt.mfderiv
        (HasMFDerivAt.congr_of_eventuallyEq (hasMFDerivAt_id _) h_inv)
    have hg : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) sphFwd
        (sphInv (sphFwd x)) := by
      rw [hxx]; exact sphFwd_mdiffAt hx
    have hf : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) sphInv (sphFwd x) :=
      sphInv_contMDiff.contMDiffAt.mdifferentiableAt (by norm_num)
    have hcomp := mfderiv_comp (sphFwd x) hg hf
    rw [hxx] at hcomp
    exact hcomp.symm.trans hid
  -- evaluate: `Dfwd (Dinv (single j 1)) = single j 1`
  have key : ∀ j : Fin 2,
      Dfwd (Dinv (EuclideanSpace.single j (1 : ℝ))) = EuclideanSpace.single j 1 := by
    intro j
    have := congrArg (fun L ↦ L (EuclideanSpace.single j (1 : ℝ))) h_right
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdθ, hXθ]
    simp [key 0]
  · rw [hdφ, hXθ]
    simp [key 0]
  · rw [hdθ, hXφ]
    simp [key 1]
  · rw [hdφ, hXφ]
    simp [key 1]

lemma dθ_Xθ {x : S2} (hx : x ∈ sphSource) : dθ x (Xθ x) = 1 := (frame_pairing hx).1
lemma dφ_Xθ {x : S2} (hx : x ∈ sphSource) : dφ x (Xθ x) = 0 := (frame_pairing hx).2.1
lemma dθ_Xφ {x : S2} (hx : x ∈ sphSource) : dθ x (Xφ x) = 0 := (frame_pairing hx).2.2.1
lemma dφ_Xφ {x : S2} (hx : x ∈ sphSource) : dφ x (Xφ x) = 1 := (frame_pairing hx).2.2.2

/-! ## Connections from coefficients in a frame

The analogue of SageManifolds' `nabla.add_coef(e)`: specify a covariant
derivative by its connection coefficients `Γ` relative to a frame `e` with
dual coframe `ε`, supported on a set `s`.  `Γ i j k` is Γ^i_{jk}: output
component `i`, direction covector `j`, pairing `k` with the section. -/

open Classical in
def covDerivOfFrame (s : Set S2)
    (e : Fin 2 → Π x : S2, TangentSpace (𝓡 2) x)
    (ε : Fin 2 → Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] ℝ)
    (Γ : Fin 2 → Fin 2 → Fin 2 → S2 → ℝ) :
    (Π x : S2, TangentSpace (𝓡 2) x) →
    (Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) :=
  fun σ x =>
    if x ∈ s then
      ∑ i, ((mvfderiv (𝓡 2) (fun y ↦ ε i y (σ y)) x)
          + ∑ j, ∑ k, (Γ i j k x * ε k x (σ x)) • ε j x).smulRight (e i x)
    else 0

/-! ## The compass frame and the Mercator connection -/

/-- e₁ = ∂_θ. -/
def e₁ : Π x : S2, TangentSpace (𝓡 2) x := Xθ

/-- e₂ = (1/sin θ) ∂_φ. -/
def e₂ : Π x : S2, TangentSpace (𝓡 2) x :=
  fun x ↦ (Real.sin (θ_coord x))⁻¹ • Xφ x

/-- ε¹ = dθ. -/
abbrev ε₁ : Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] ℝ := dθ

/-- ε² = sin θ · dφ. -/
def ε₂ : Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  fun x ↦ Real.sin (θ_coord x) • dφ x

/-- The Mercator connection: parallelism is constancy of bearing, i.e. ALL
connection coefficients vanish in the compass frame. -/
def mercatorCov :
    (Π x : S2, TangentSpace (𝓡 2) x) →
    (Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) :=
  covDerivOfFrame sphSource ![e₁, e₂] ![ε₁, ε₂] 0

local infixr:70 " ⊗ " => fun c w => ContinuousLinearMap.smulRight c w

lemma mercatorCov_apply (σ : Π y : S2, TangentSpace (𝓡 2) y) {x : S2}
    (hx : x ∈ sphSource) :
    mercatorCov σ x =
      (mvfderiv (𝓡 2) (fun y ↦ ε₁ y (σ y)) x) ⊗ (e₁ x) +
      (mvfderiv (𝓡 2) (fun y ↦ ε₂ y (σ y)) x) ⊗ (e₂ x) := by
  simp only [mercatorCov, covDerivOfFrame, if_pos hx, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.zero_apply, zero_mul, zero_smul, Finset.sum_const_zero, add_zero]

/-! ## The frame is parallel — the machine confirming the definition -/

lemma ε₁_e₁ {y : S2} (hy : y ∈ sphSource) : ε₁ y (e₁ y) = 1 :=
  dθ_Xθ hy

lemma ε₂_e₁ {y : S2} (hy : y ∈ sphSource) : ε₂ y (e₁ y) = 0 := by
  simp only [ε₂, e₁, smul_apply, smul_eq_mul, dφ_Xθ hy, mul_zero]

lemma ε₁_e₂ {y : S2} (hy : y ∈ sphSource) : ε₁ y (e₂ y) = 0 := by
  simp only [ε₁, e₂, map_smul, smul_eq_mul, dθ_Xφ hy, mul_zero]

lemma ε₂_e₂ {y : S2} (hy : y ∈ sphSource) : ε₂ y (e₂ y) = 1 := by
  have hs : Real.sin (θ_coord y) ≠ 0 :=
    sinθ_ne_zero y (sphSource_subset_S2_open hy)
  simp only [ε₂, e₂, smul_apply, map_smul, smul_eq_mul, dφ_Xφ hy, mul_one]
  field_simp

/-- ∇e₁ = 0: the meridian direction is parallel. -/
lemma mercatorCov_e₁ {x : S2} (hx : x ∈ sphSource) : mercatorCov e₁ x = 0 := by
  rw [mercatorCov_apply _ hx]
  have hmem := IsOpen.mem_nhds sph_open_source hx
  rw [mvfderiv_of_eventuallyEq_const
        (Filter.eventuallyEq_of_mem hmem fun y hy ↦ ε₁_e₁ hy),
      mvfderiv_of_eventuallyEq_const
        (Filter.eventuallyEq_of_mem hmem fun y hy ↦ ε₂_e₁ hy)]
  ext v; simp

/-- ∇e₂ = 0: the east direction is parallel. -/
lemma mercatorCov_e₂ {x : S2} (hx : x ∈ sphSource) : mercatorCov e₂ x = 0 := by
  rw [mercatorCov_apply _ hx]
  have hmem := IsOpen.mem_nhds sph_open_source hx
  rw [mvfderiv_of_eventuallyEq_const
        (Filter.eventuallyEq_of_mem hmem fun y hy ↦ ε₁_e₂ hy),
      mvfderiv_of_eventuallyEq_const
        (Filter.eventuallyEq_of_mem hmem fun y hy ↦ ε₂_e₂ hy)]
  ext v; simp

/-! ## Duality and component differentiability in the compass frame -/

/-- Frame-dual identity in the compass frame. -/
lemma compass_dual {x : S2} (hx : x ∈ sphSource) (v : TangentSpace (𝓡 2) x) :
    v = ε₁ x v • e₁ x + ε₂ x v • e₂ x := by
  have hs : Real.sin (θ_coord x) ≠ 0 :=
    sinθ_ne_zero x (sphSource_subset_S2_open hx)
  have h := frame_dual hx v
  simp only [ε₁, ε₂, e₁, e₂, smul_apply, smul_eq_mul, smul_smul]
  rw [mul_comm (Real.sin (θ_coord x)) (dφ x v), mul_inv_cancel_right₀ hs]
  exact h.symm

/-- Differentiability of the ε₂-component of a bundle-differentiable section. -/
lemma mdiffAt_ε₂comp {σ : Π y : S2, TangentSpace (𝓡 2) y} {x : S2}
    (hσ : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) y (σ y)) x)
    (hx : x ∈ sphSource) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ ε₂ y (σ y)) x := by
  have hxo := sphSource_subset_S2_open hx
  have hcm : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ⊤ (fun y ↦ Real.sin (θ_coord y)) x :=
    (Real.contDiff_sin.contMDiff.contMDiffAt).comp x (θ_coord_contMDiffAt hxo)
  have hsin : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ Real.sin (θ_coord y)) x :=
    hcm.mdifferentiableAt (by norm_num)
  have h := hsin.mul (mdiffAt_dφcomp hσ hx)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
    simp only [ε₂, smul_apply, smul_eq_mul, Pi.mul_apply])

/-! ## Verification: the upstream `IsCovariantDerivativeOn`

With all coefficients zero, both axioms are pure `mvfderiv` calculus plus
compass duality — there is no correction term to juggle. -/

theorem mercatorCov_isCovariantDerivativeOn :
    IsCovariantDerivativeOn (EuclideanSpace ℝ (Fin 2)) mercatorCov sphSource where
  add := by
    intro σ σ' x hσ hσ' hx
    have hxo := sphSource_subset_S2_open hx
    have hc1 : (fun y ↦ ε₁ y ((σ + σ') y)) =
        (fun y ↦ ε₁ y (σ y)) + fun y ↦ ε₁ y (σ' y) := by
      funext y; simp only [Pi.add_apply, map_add]
    have hc2 : (fun y ↦ ε₂ y ((σ + σ') y)) =
        (fun y ↦ ε₂ y (σ y)) + fun y ↦ ε₂ y (σ' y) := by
      funext y; simp only [Pi.add_apply, map_add]
    rw [mercatorCov_apply (σ + σ') hx, mercatorCov_apply σ hx, mercatorCov_apply σ' hx,
      hc1, hc2,
      mvfderiv_add (mdiffAt_dθcomp hσ hxo) (mdiffAt_dθcomp hσ' hxo),
      mvfderiv_add (mdiffAt_ε₂comp hσ hx) (mdiffAt_ε₂comp hσ' hx)]
    ext v
    simp only [add_apply, ContinuousLinearMap.smulRight_apply]
    module
  leibniz := by
    intro σ g x hσ hg hx
    have hxo := sphSource_subset_S2_open hx
    have hc1 : (fun y ↦ ε₁ y ((g • σ) y)) = g * fun y ↦ ε₁ y (σ y) := by
      funext y; simp only [Pi.smul_apply', Pi.mul_apply, map_smul, smul_eq_mul]
    have hc2 : (fun y ↦ ε₂ y ((g • σ) y)) = g * fun y ↦ ε₂ y (σ y) := by
      funext y; simp only [Pi.smul_apply', Pi.mul_apply, map_smul, smul_eq_mul]
    rw [mercatorCov_apply (g • σ) hx, mercatorCov_apply σ hx, hc1, hc2,
      mvfderiv_mul hg (mdiffAt_dθcomp hσ hxo),
      mvfderiv_mul hg (mdiffAt_ε₂comp hσ hx)]
    set a := ε₁ x (σ x) with ha
    set b := ε₂ x (σ x) with hb
    have hdual : σ x = a • e₁ x + b • e₂ x := by
      rw [ha, hb]; exact compass_dual hx (σ x)
    rw [hdual]
    ext v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    module

/-! ## The coordinate expression — the classical Christoffel symbol -/

/-- d(sin θ) = cos θ · dθ. -/
theorem mvfderiv_sin_θcoord {x : S2} (hx : x ∈ S2_open) :
    mvfderiv (𝓡 2) (fun y ↦ Real.sin (θ_coord y)) x
      = Real.cos (θ_coord x) • dθ x := by
  have h_chain : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) θ_coord x (dθ x) :=
    ((θ_coord_contMDiffAt hx).mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hsin : HasFDerivAt Real.sin
      (ContinuousLinearMap.toSpanSingleton ℝ (Real.cos (θ_coord x))) (θ_coord x) :=
    (Real.hasDerivAt_sin (θ_coord x)).hasFDerivAt
  have hcomp : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (Real.sin ∘ θ_coord) x
      ((ContinuousLinearMap.toSpanSingleton ℝ (Real.cos (θ_coord x))).comp (dθ x)) :=
    HasMFDerivAt.comp x hsin.hasMFDerivAt h_chain
  have heq : (ContinuousLinearMap.toSpanSingleton ℝ (Real.cos (θ_coord x))).comp (dθ x)
      = Real.cos (θ_coord x) • dθ x := by
    ext v
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    exact mul_comm' ((dθ x) v) (cos (θ_coord x))
  exact heq ▸ hcomp.mfderiv

/-
Γ^φ_{θφ} = cot θ: the compass-frame connection, written in the coordinate
frame, is the classical Mercator connection.
-/
theorem mercatorCov_coord (σ : Π y : S2, TangentSpace (𝓡 2) y) {x : S2}
    (hx : x ∈ sphSource)
    (hσ : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) y (σ y)) x) :
    mercatorCov σ x =
      (mvfderiv (𝓡 2) (fun y ↦ dθ y (σ y)) x).smulRight (Xθ x) +
      (mvfderiv (𝓡 2) (fun y ↦ dφ y (σ y)) x +
        ((Real.cos (θ_coord x) / Real.sin (θ_coord x)) * dφ x (σ x)) • dθ x).smulRight
        (Xφ x) := by
  have hxo := sphSource_subset_S2_open hx
  have hs : Real.sin (θ_coord x) ≠ 0 := sinθ_ne_zero x hxo
  have hcm : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ⊤ (fun y ↦ Real.sin (θ_coord y)) x :=
    (Real.contDiff_sin.contMDiff.contMDiffAt).comp x (θ_coord_contMDiffAt hxo)
  have hsin_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ Real.sin (θ_coord y)) x :=
    hcm.mdifferentiableAt (by norm_num)
  have hφ : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ dφ y (σ y)) x :=
    mdiffAt_dφcomp hσ hx
  have hprod : (fun y ↦ ε₂ y (σ y)) =
      (fun y ↦ Real.sin (θ_coord y)) * fun y ↦ dφ y (σ y) := by
    funext y
    simp only [ε₂, smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [mercatorCov_apply σ hx, hprod, mvfderiv_mul hsin_diff hφ,
    mvfderiv_sin_θcoord hxo]
  ext v
  simp only [e₁, e₂, ε₁, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, smul_smul]
  congr 1
  congr 1
  field_simp

end
