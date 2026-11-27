import BrendleHungFormal.Section2.Multivar
import BrendleHungFormal.Section2.TaylorAsymptotics
import BrendleHungFormal.Section2.Definitions
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open Function (uncurry)
open Filter
open scoped BigOperators Matrix Topology

section BrendleHung.Section2

open BrendleHung.Section2.Multivar
open BrendleHung.Section2.TaylorAsymptotics

-- Keep the short name `norm` for the coordinate-space norm in this file,
-- without clashing with Mathlib's global `norm`.
local notation "norm" => BrendleHung.Section2.Multivar.norm
local notation "↓" f => uncurry f

/-- The derivative of `u0(x, ·)` vanishes at `w = 0`, by the quadratic lower bound. -/
lemma u0WAtZero (x : ℝ^m) (hx : inBounds x) : u0W x 0 = 0
:= by
  have hAtZero : asm.u0 x 0 = 0 := asm.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ B asm.r0 →
      asm.u0 x w ≥ asm.σ * (norm w ^ 2) := by
    intro w hw
    exact asm.u0Quadratic x w hx (B_subset_D hw)
  have hderiv := ineq_zero_deriv (asm.u0 x) asm.r0 asm.hr0 asm.σ asm.hσ hAtZero hquad
  ext w
  simpa [u0W] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L w) hderiv

/-- The Hessian of `u0(x, ·)` at `w = 0` is positive definite. -/
lemma u0WWAtZero (x : ℝ^m) (hx : inBounds x) : Matrix.PosDef (u0WW x 0)
:= by
  have hAtZero : asm.u0 x 0 = 0 := asm.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ B asm.r0 →
      asm.u0 x w ≥ asm.σ * (norm w ^ 2) := by
    intro w hw
    exact asm.u0Quadratic x w hx (B_subset_D hw)
  have hsmooth : SmoothGlobal (asm.u0 x) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))
  simpa [u0WW, matrixOf] using
    (ineq_pos_def (asm.u0 x) asm.r0 asm.hr0 asm.σ asm.hσ
      hsmooth hAtZero hquad)

-- This is equation (1) in the paper, rewritten as
-- `∑ β, u0WW x 0 α β * barw x β = - u1W x 0 (e α)`.
lemma barw_spec (x : ℝ^m) (hx : inBounds x) :
  u0WW x 0 *ᵥ bud.barw x = fun α : Fin n => - u1W x 0 (e α)
:= by
  have hpos : (u0WW x 0).PosDef := u0WWAtZero x hx
  have hdet : IsUnit (u0WW x 0).det :=
    (Matrix.isUnit_iff_isUnit_det (u0WW x 0)).mp hpos.isUnit
  ext α
  change (u0WW x 0 *ᵥ ((u0WW x 0)⁻¹ *ᵥ (fun β : Fin n => - u1W x 0 (e β))) : Fin n → ℝ) α = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

-- At `s = 0`, the expansion assumption reduces `u` to `u0` on the domain.
lemma data_u_zero (x : ℝ^m) (hx : inBounds x) (w : ℝ^n) (hw : inBounds w) :
    asm.u x w 0 = asm.u0 x w
:= by
  rcases asm.uExp with ⟨ρ, hρSmooth, hρ⟩
  have hseg0 : (0 : ℝ) ∈ BrendleHung.Section2.Multivar.segment asm.s0 := by
    change |(0 : ℝ)| ≤ asm.s0
    simpa using (le_of_lt asm.hs0)
  have hp : (x, w) ∈ D asm.r0 ×ˢ D asm.r0 := ⟨hx, hw⟩
  simpa using hρ (x, w) 0 hp hseg0

-- Differentiating the expansion assumption in the `s` variable at `s = 0`.
lemma hasDerivAt_u_s (x : ℝ^m) (hx : inBounds x) (w : ℝ^n) (hw : inBounds w) :
    HasDerivAt (asm.u x w) (asm.u1 x w) 0
:= by
  rcases asm.uExp with ⟨ρ, hρSmooth, hρ⟩
  have hseg : ∀ᶠ s : ℝ in 𝓝 0, s ∈ segment asm.s0 :=
    segment_mem_nhds_zero asm.hs0
  have hEq : (asm.u x w) =ᶠ[𝓝 0]
      (fun s : ℝ => asm.u0 x w + s * asm.u1 x w + s ^ 2 * asm.u2 x w
        + s ^ 3 * asm.u3 x w + s ^ 4 * ρ ((x, w), s)) := by
    filter_upwards [hseg] with s hs
    exact hρ (x, w) s ⟨hx, hw⟩ hs
  have hρdiff : HasDerivAt (fun s : ℝ => ρ ((x, w), s))
      (deriv (fun s : ℝ => ρ ((x, w), s)) 0) 0 := by
    exact ((contDiffOn_univ.mp hρSmooth).differentiable (by simp) ((x, w), 0)).comp
      0 (by fun_prop) |>.hasDerivAt
  have hpoly : HasDerivAt
      (fun s : ℝ => asm.u0 x w + s * asm.u1 x w + s ^ 2 * asm.u2 x w
        + s ^ 3 * asm.u3 x w + s ^ 4 * ρ ((x, w), s)) (asm.u1 x w) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (asm.u0 x w)).add
        (((hasDerivAt_id (0 : ℝ)).mul_const (asm.u1 x w)).add
          (((hasDerivAt_pow 2 (0 : ℝ)).mul_const (asm.u2 x w)).add
            (((hasDerivAt_pow 3 (0 : ℝ)).mul_const (asm.u3 x w)).add
              ((hasDerivAt_pow 4 (0 : ℝ)).mul hρdiff)))) using 1
    · ext s
      simp only [Pi.add_apply, Pi.mul_apply, id_eq]
      ring
    · simp
  exact hpoly.congr_of_eventuallyEq hEq

-- Gradient of `u` in the `w` variables, represented in the standard basis.
noncomputable def gradW (p : ℝ^m) (w : ℝ^n) (s : ℝ) : ℝ^n :=
  fun α => fderiv ℝ (fun w' : ℝ^n => asm.u p w' s) w (e α)

/-- The critical point equation holds at `(w,s) = (0,0)`. -/
lemma gradW_zero (p : ℝ^m) (hp : inBounds p) : gradW p 0 0 = 0 := by
  have hB : B asm.r0 ∈ 𝓝 (0 : ℝ^n) := B_mem_nhds_zero asm.hr0
  have hEq : (fun w : ℝ^n => asm.u p w 0) =ᶠ[𝓝 (0 : ℝ^n)] asm.u0 p := by
    filter_upwards [hB] with w hw
    exact data_u_zero p hp w (B_subset_D hw)
  ext α
  have hderiv : fderiv ℝ (fun w : ℝ^n => asm.u p w 0) 0 = diff (asm.u0 p) 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hEq]
  have hz : u0W p 0 = 0 := u0WAtZero p hp
  simpa [gradW, u0W, hderiv] using congrArg (fun L : ℝ^n → ℝ => L (e α)) hz

/-- One coordinate of the derivative of `w ↦ gradW p w 0` is the corresponding row of `u0WW p 0`. -/
lemma hasFDerivAt_gradW_w_comp (p : ℝ^m) (hp : inBounds p) (α : Fin n) :
    HasFDerivAt (fun w : ℝ^n => gradW p w 0 α)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
        ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap)) 0
:= by
  have hB : B asm.r0 ∈ 𝓝 (0 : ℝ^n) := B_mem_nhds_zero asm.hr0
  have hu0Smooth : SmoothGlobal (asm.u0 p) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) p))
  have hgSmooth : SmoothGlobal (fun w : ℝ^n => asm.u p w 0) := by
    have hcomp : SmoothGlobal (fun w : ℝ^n => (p, w, (0 : ℝ))) := by fun_prop
    simpa [Function.comp_def] using asm.uSmooth.comp hcomp
  have hclm : HasFDerivAt (fun w : ℝ^n => fderiv ℝ (fun w' => asm.u p w' 0) w (e α))
      ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fderiv ℝ (fun w' => asm.u p w' 0)) 0)) 0 := by
    have hc : HasFDerivAt (fderiv ℝ (fun w' => asm.u p w' 0))
        (fderiv ℝ (fderiv ℝ (fun w' => asm.u p w' 0)) 0) 0 :=
      ((hgSmooth.fderiv_right (m := 1) (by simp)).differentiable (by simp) 0).hasFDerivAt
    have hu : HasFDerivAt (fun _ : ℝ^n => e α) (0 : ℝ^n →L[ℝ] ℝ^n) 0 :=
      (hasFDerivAt_const (e α) (0 : ℝ^n))
    simpa using hc.clm_apply hu
  have hdiff2 : fderiv ℝ (fderiv ℝ (fun w' => asm.u p w' 0)) 0
      = diff2 (asm.u0 p) 0 := by
    have hEq' : (fderiv ℝ (fun w' => asm.u p w' 0))
        =ᶠ[𝓝 0] (fderiv ℝ (asm.u0 p)) := by
      filter_upwards [hB] with w hw
      have hEqw : (fun w' : ℝ^n => asm.u p w' 0) =ᶠ[𝓝 w] asm.u0 p := by
        filter_upwards [B_mem_nhds hw] with w' hw'
        exact data_u_zero p hp w' (B_subset_D hw')
      simpa using hEqw.fderiv_eq
    rw [hEq'.fderiv_eq]
  have hsymm : IsSymmSndFDerivAt ℝ (asm.u0 p) 0 := by
    have hf2 : ContDiff ℝ (2 : WithTop ℕ∞) (asm.u0 p) := hu0Smooth.of_le le_top
    exact hf2.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hL : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
        ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap))
      = ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fderiv ℝ (fun w' => asm.u p w' 0)) 0)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.apply_apply]
    rw [hdiff2]
    show (u0WW p 0 *ᵥ v) α = diff2 (asm.u0 p) 0 v (e α)
    have hsymm' : diff2 (asm.u0 p) 0 v (e α) = diff2 (asm.u0 p) 0 (e α) v := by
      simpa [diff2, diff] using (hsymm.eq v (e α))
    rw [hsymm']
    have hv : v = ∑ j : Fin n, v j • e j := by
      ext i
      simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
    have hrhs : diff2 (asm.u0 p) 0 (e α) v =
        ∑ j : Fin n, diff2 (asm.u0 p) 0 (e α) (e j) * v j := by
      calc
        diff2 (asm.u0 p) 0 (e α) v
            = diff2 (asm.u0 p) 0 (e α) (∑ j : Fin n, v j • e j) := by
              exact congrArg _ hv
        _ = ∑ j : Fin n, v j * diff2 (asm.u0 p) 0 (e α) (e j) := by
              simp [map_sum, map_smul, smul_eq_mul]
        _ = ∑ j : Fin n, diff2 (asm.u0 p) 0 (e α) (e j) * v j := by
              simp [mul_comm]
    rw [hrhs]
    simp [Matrix.mulVec, dotProduct, u0WW, Matrix.of_apply, mul_comm]
  have hmain : HasFDerivAt (fun w : ℝ^n => gradW p w 0 α)
      ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fderiv ℝ (fun w' => asm.u p w' 0)) 0)) 0 := by
    simpa [gradW] using hclm
  simpa [hL] using hmain

/-- The derivative in `w` of `gradW p w 0` at `w = 0` is the Hessian map `u0WW p 0`. -/
lemma hasFDerivAt_gradW_w (p : ℝ^m) (hp : inBounds p) :
    HasFDerivAt (fun w : ℝ^n => gradW p w 0)
      ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap) 0
:= by
  have hcomp : ∀ α : Fin n,
      HasFDerivAt (fun w : ℝ^n => gradW p w 0 α)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
          ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap)) 0 :=
    fun α => hasFDerivAt_gradW_w_comp p hp α
  have hpi := (hasFDerivAt_pi.mpr hcomp)
  -- rewrite the derivative as the matrix CLM
  have hL : ContinuousLinearMap.pi
      (fun α : Fin n =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
          ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap))
      = ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap) := by
    ext v α
    simp
  simpa [hL] using hpi

/-- One coordinate of the derivative of `s ↦ gradW x 0 s` at `s = 0` is `u1W x 0 (e α)`. -/
lemma hasDerivAt_gradW_s_comp (x : ℝ^m) (hx : inBounds x) (α : Fin n) :
    HasDerivAt (fun s : ℝ => gradW x 0 s α) (u1W x 0 (e α)) 0
:= by
  let F : ℝ × ℝ^n → ℝ := fun z => asm.u x z.2 z.1
  have hFsmooth : SmoothGlobal F := by
    have hcomp : SmoothGlobal (fun z : ℝ × ℝ^n => (x, z.2, z.1)) := by fun_prop
    simpa [F, Function.comp_def] using asm.uSmooth.comp hcomp
  have hF2 : ContDiff ℝ (2 : WithTop ℕ∞) F := hFsmooth.of_le le_top
  let p0 : ℝ × ℝ^n := ((0 : ℝ), (0 : ℝ^n))
  have hfderivSmooth : SmoothGlobal (fderiv ℝ F) :=
    hFsmooth.fderiv_right (m := ⊤) (by simp)
  have hsecond : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) p0) p0 :=
    (hfderivSmooth.differentiable (by simp) p0).hasFDerivAt
  -- partial derivative in s at (0,w) equals u1
  have hKpoint (w : ℝ^n) (hw : inBounds w) :
      fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n)) = asm.u1 x w := by
    have hFderiv : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), w)) ((0 : ℝ), w) :=
      (hFsmooth.differentiable (by simp) ((0 : ℝ), w)).hasFDerivAt
    have hline : HasFDerivAt (fun s : ℝ => (s, w))
        (ContinuousLinearMap.inl ℝ ℝ (ℝ^n)) 0 :=
      hasFDerivAt_prodMk_left (e₀ := (0 : ℝ)) (f₀ := w)
    have hcomp := hFderiv.comp 0 hline
    have hfd : fderiv ℝ (fun s : ℝ => F (s, w)) 0 =
        (fderiv ℝ F ((0 : ℝ), w)) ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ^n) := hcomp.fderiv
    have hval := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hfd
    have hder : HasDerivAt (fun s : ℝ => F (s, w)) (asm.u1 x w) 0 := by
      simpa [F] using hasDerivAt_u_s x hx w hw
    have hval2 : fderiv ℝ (fun s : ℝ => F (s, w)) 0 1 = asm.u1 x w := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using
        congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hder.hasFDerivAt.fderiv
    exact hval.symm.trans hval2
  have hB : B asm.r0 ∈ 𝓝 (0 : ℝ^n) := B_mem_nhds_zero asm.hr0
  have hK_eq : (fun w : ℝ^n => fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n)))
      =ᶠ[𝓝 (0 : ℝ^n)] asm.u1 x := by
    filter_upwards [hB] with w hw
    exact hKpoint w (B_subset_D hw)
  have hKderiv : HasFDerivAt
      (fun z : ℝ × ℝ^n => fderiv ℝ F z ((1 : ℝ), (0 : ℝ^n)))
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ^n))).comp
        (fderiv ℝ (fderiv ℝ F) p0)) p0 := by
    have hconst : HasFDerivAt (fun _ : ℝ × ℝ^n => ((1 : ℝ), (0 : ℝ^n))) 0 p0 :=
      hasFDerivAt_const (𝕜 := ℝ) ((1 : ℝ), (0 : ℝ^n)) p0
    simpa using hsecond.clm_apply hconst
  have hlineW : HasFDerivAt (fun w : ℝ^n => ((0 : ℝ), w))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ^n)) 0 :=
    hasFDerivAt_prodMk_right (e₀ := (0 : ℝ)) (f₀ := (0 : ℝ^n))
  have hKcomp := hKderiv.comp 0 hlineW
  have hK_fd : fderiv ℝ
      (fun w : ℝ^n => fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n))) 0 =
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ^n))).comp
        (fderiv ℝ (fderiv ℝ F) p0)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ^n)) := hKcomp.fderiv
  have hK_fd' : fderiv ℝ
      (fun w : ℝ^n => fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n))) 0 =
      diff (asm.u1 x) 0 := by
    rw [hK_eq.fderiv_eq]
  have hsnd : (fderiv ℝ (fderiv ℝ F) p0) ((0 : ℝ), e α) ((1 : ℝ), (0 : ℝ^n))
      = u1W x 0 (e α) := by
    have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) (hK_fd.symm.trans hK_fd')
    simpa [ContinuousLinearMap.comp_apply, u1W] using hval
  have hHderiv : HasFDerivAt
      (fun z : ℝ × ℝ^n => fderiv ℝ F z ((0 : ℝ), e α))
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), e α)).comp
        (fderiv ℝ (fderiv ℝ F) p0)) p0 := by
    have hconst : HasFDerivAt (fun _ : ℝ × ℝ^n => ((0 : ℝ), e α)) 0 p0 :=
      hasFDerivAt_const (𝕜 := ℝ) ((0 : ℝ), e α) p0
    simpa using hsecond.clm_apply hconst
  have hlineS : HasFDerivAt (fun s : ℝ => (s, (0 : ℝ^n)))
      (ContinuousLinearMap.inl ℝ ℝ (ℝ^n)) 0 :=
    hasFDerivAt_prodMk_left (e₀ := (0 : ℝ)) (f₀ := (0 : ℝ^n))
  have hHcomp : HasFDerivAt
      ((fun z : ℝ × ℝ^n => fderiv ℝ F z ((0 : ℝ), e α)) ∘
        (fun s : ℝ => (s, (0 : ℝ^n))))
      (((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), e α)).comp
        (fderiv ℝ (fderiv ℝ F) p0)).comp
        (ContinuousLinearMap.inl ℝ ℝ (ℝ^n))) 0 :=
    hHderiv.comp (0 : ℝ) hlineS
  have hsymm : IsSymmSndFDerivAt ℝ F p0 :=
    hF2.contDiffAt.isSymmSndFDerivAt (by simp)
  have hH_L : (((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), e α)).comp
        (fderiv ℝ (fderiv ℝ F) p0)).comp
        (ContinuousLinearMap.inl ℝ ℝ (ℝ^n)))
      = ContinuousLinearMap.toSpanSingleton ℝ (u1W x 0 (e α)) := by
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [show ((t, (0 : ℝ^n)) : ℝ × ℝ^n) = t • ((1 : ℝ), (0 : ℝ^n)) by ext <;> simp]
    rw [map_smul]
    simp only [ContinuousLinearMap.smul_apply]
    rw [hsymm.eq ((1 : ℝ), (0 : ℝ^n)) ((0 : ℝ), e α)]
    rw [hsnd]
  have hHcomp' : HasDerivAt
      (fun s : ℝ => fderiv ℝ F (s, (0 : ℝ^n)) ((0 : ℝ), e α))
      (u1W x 0 (e α)) 0 := by
    have htmp : HasFDerivAt
        (fun s : ℝ => fderiv ℝ F (s, (0 : ℝ^n)) ((0 : ℝ), e α))
        (ContinuousLinearMap.toSpanSingleton ℝ (u1W x 0 (e α))) 0 := by
      simpa [hH_L] using hHcomp
    simpa using htmp.hasDerivAt
  have hgrad_eq (s : ℝ) : gradW x 0 s α = fderiv ℝ F (s, (0 : ℝ^n)) ((0 : ℝ), e α) := by
    have hFderiv : HasFDerivAt F (fderiv ℝ F (s, (0 : ℝ^n))) (s, (0 : ℝ^n)) :=
      (hFsmooth.differentiable (by simp) (s, (0 : ℝ^n))).hasFDerivAt
    have hline : HasFDerivAt (fun w : ℝ^n => (s, w))
        (ContinuousLinearMap.inr ℝ ℝ (ℝ^n)) 0 :=
      hasFDerivAt_prodMk_right s 0
    have hcomp := hFderiv.comp 0 hline
    have hfd := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hcomp.fderiv
    simpa [F, gradW, Function.comp_def] using hfd
  have hfun_eq : (fun s : ℝ => gradW x 0 s α) =
      (fun s : ℝ => fderiv ℝ F (s, (0 : ℝ^n)) ((0 : ℝ), e α)) := by
    funext s
    exact hgrad_eq s
  rw [hfun_eq]
  exact hHcomp'


/-- The derivative in `s` of `gradW x 0 s` at `s = 0` is the vector with components `u1W x 0 (e α)`. -/
lemma hasFDerivAt_gradW_s (x : ℝ^m) (hx : inBounds x) :
    HasFDerivAt (gradW x 0)
      (ContinuousLinearMap.toSpanSingleton ℝ (fun α : Fin n => u1W x 0 (e α))) 0
:= by
  let v : ℝ^n := fun α => u1W x 0 (e α)
  have hcomp : ∀ α : Fin n,
      HasFDerivAt (fun s : ℝ => gradW x 0 s α)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
          (ContinuousLinearMap.toSpanSingleton ℝ v)) 0 := by
    intro α
    have h := hasDerivAt_gradW_s_comp x hx α
    simpa [v] using h.hasFDerivAt
  have hpi := hasFDerivAt_pi.mpr hcomp
  have hL : ContinuousLinearMap.pi
      (fun α : Fin n =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
          (ContinuousLinearMap.toSpanSingleton ℝ v))
      = ContinuousLinearMap.toSpanSingleton ℝ v := by
    ext s
    simp
  simpa [hL, v] using hpi

/-- Smoothness of the parametrized gradient map `F((x,s),w) = gradW x w s`. -/
lemma gradWParam_smooth :
    SmoothGlobal (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
:= by
  rw [contDiff_pi]
  intro α
  let g : (ℝ^m × ℝ) × ℝ^n → ℝ^n → ℝ := fun z w => asm.u z.1.1 w z.1.2
  have hg : SmoothGlobal (uncurry g) := by
    have hcomp : SmoothGlobal (fun q : ((ℝ^m × ℝ) × ℝ^n) × ℝ^n => (q.1.1.1, q.2, q.1.1.2)) := by
      fun_prop
    simpa [g, Function.uncurry_def] using asm.uSmooth.comp hcomp
  simpa [gradW, g] using
    (hg.fderiv_apply (g := fun z : (ℝ^m × ℝ) × ℝ^n => z.2)
      (k := fun _ : (ℝ^m × ℝ) × ℝ^n => e α)
      (by fun_prop) (by fun_prop) (by simp))

-- The derivative in the `w` variables of the gradient map is the Hessian
-- `u0WW`, which is invertible by the quadratic lower bound on `u0`.
lemma u0WW_toLin_isInvertible (x : ℝ^m) (hx : inBounds x) :
    ((Matrix.toLin' (u0WW x 0)).toContinuousLinearMap).IsInvertible
:= by
  classical
  have hunit : IsUnit (u0WW x 0).det :=
    (Matrix.isUnit_iff_isUnit_det (u0WW x 0)).mp (u0WWAtZero x hx).isUnit
  let eLin : (ℝ^n) ≃ₗ[ℝ] (ℝ^n) :=
    (u0WW x 0).toLinearEquiv (Pi.basisFun ℝ (Fin n)) hunit
  refine ⟨eLin.toContinuousLinearEquiv, ?_⟩
  ext v i
  simp [eLin, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

-- The partial derivative of `F(q,w) = gradW q.1.1 w q.1.2` with respect to
-- `w` at `(x,0),0` is exactly the map induced by `u0WW x 0`.
lemma gradWParam_partial_eq (x : ℝ^m) (hx : inBounds x) :
    (fderiv ℝ
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2) (((x, (0 : ℝ)), (0 : ℝ^n)))
      ∘L ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n))
      = (Matrix.toLin' (u0WW x 0)).toContinuousLinearMap
:= by
  let F : (ℝ^m × ℝ) × ℝ^n → ℝ^n :=
    fun z => gradW z.1.1 z.2 z.1.2
  have hF : HasFDerivAt F
      (fderiv ℝ F (((x, (0 : ℝ)), (0 : ℝ^n)))) (((x, (0 : ℝ)), (0 : ℝ^n))) :=
    ((gradWParam_smooth.differentiable (by simp) (((x, (0 : ℝ)), (0 : ℝ^n)))).hasFDerivAt)
  have hline : HasFDerivAt
      (fun w : ℝ^n => (((x, (0 : ℝ)), w) : (ℝ^m × ℝ) × ℝ^n))
      (ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)) (0 : ℝ^n) :=
    hasFDerivAt_prodMk_right (((x, (0 : ℝ)) : ℝ^m × ℝ)) (0 : ℝ^n)
  have hcomp : HasFDerivAt (fun w : ℝ^n => gradW x w 0)
      ((fderiv ℝ F (((x, (0 : ℝ)), (0 : ℝ^n))))
        ∘L ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)) (0 : ℝ^n) := by
    simpa [F, Function.comp_def] using hF.comp (0 : ℝ^n) hline
  exact hcomp.unique (hasFDerivAt_gradW_w x hx)

/-- The partial derivative of `F` in the `w` variables at the base point is invertible. -/
lemma gradWParam_partial_isInvertible (x : ℝ^m) (hx : inBounds x) :
    ((fderiv ℝ (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2) ((x, (0 : ℝ)), (0 : ℝ^n))
      ∘L ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)).IsInvertible)
:= by simpa [gradWParam_partial_eq x hx] using (u0WW_toLin_isInvertible x hx)

-- The implicit function supplied by the IFT, based at `((x,0),0)`.  It is a
-- local smooth function of `(x,s)` near the base point.
noncomputable def wStarAt (x : ℝ^m) (hx : inBounds x) : ℝ^m × ℝ → ℝ^n :=
  (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
      (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt).implicitFunction
    (by simp) (gradWParam_partial_isInvertible x hx)

/-- The implicit solution vanishes at the base point: `wStarAt x hx (x,0) = 0`. -/
lemma wStarAt_self (x : ℝ^m) (hx : inBounds x) : wStarAt x hx (x, 0) = 0 := by
  simpa [wStarAt] using
    (ContDiffAt.implicitFunction_apply_self
      (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
        (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt)
      (by simp) (gradWParam_partial_isInvertible x hx))

/-- Smoothness of `wStarAt x hx` at the base point `(x,0)`. -/
lemma wStarAt_contDiffAt (x : ℝ^m) (hx : inBounds x) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (wStarAt x hx) (x, 0)
:= by simpa [wStarAt] using
  (ContDiffAt.contDiffAt_implicitFunction
    (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
      (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt)
    (by simp) (gradWParam_partial_isInvertible x hx))

-- Differentiating the IFT formula at the base point gives the first-order
-- term of `w*`:  `d/ds w*(x,s)|₀ = \bar w(x)`.
lemma hasDerivAt_wStarAt_s (x : ℝ^m) (hx : inBounds x) :
    HasDerivAt (fun s : ℝ => wStarAt x hx (x, s)) (bud.barw x) 0
:= by
  let E₁ := ℝ^m × ℝ
  let E₂ := ℝ^n
  let F : E₁ × E₂ → E₂ := fun z => gradW z.1.1 z.2 z.1.2
  let u : E₁ × E₂ := ((x, (0 : ℝ)), (0 : ℝ^n))
  let H : E₁ × E₂ →L[ℝ] E₂ := fderiv ℝ F u
  let P : E₁ →L[ℝ] E₂ := H ∘L ContinuousLinearMap.inl ℝ E₁ E₂
  let Q : E₂ →L[ℝ] E₂ := H ∘L ContinuousLinearMap.inr ℝ E₁ E₂
  let v1 : E₂ := fun α => u1W x 0 (e α)
  have hP_eq : P ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ v1 := by
    apply ContinuousLinearMap.ext
    intro t
    have hF : HasFDerivAt F H u := (gradWParam_smooth.differentiable (by simp) u).hasFDerivAt
    have hq : HasFDerivAt (fun s : ℝ => (x, s)) (ContinuousLinearMap.inr ℝ ℝ^m ℝ) 0 :=
      hasFDerivAt_prodMk_right (e₀ := x) (f₀ := (0 : ℝ))
    have hw : HasFDerivAt (fun _ : ℝ => (0 : ℝ^n)) 0 0 :=
      hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ^n) 0
    have hline := hq.prodMk hw
    have hcomp := hF.comp (0 : ℝ) hline
    have ht := congrArg (fun L : ℝ →L[ℝ] ℝ^n => L t) hcomp.fderiv
    change fderiv ℝ (gradW x 0) 0 t =
      (H ∘L ((ContinuousLinearMap.inr ℝ ℝ^m ℝ).prod (0 : ℝ →L[ℝ] ℝ^n))) t at ht
    have hgrad := congrArg (fun L : ℝ →L[ℝ] ℝ^n => L t)
      (hasFDerivAt_gradW_s x hx).fderiv
    change fderiv ℝ (gradW x 0) 0 t =
      (ContinuousLinearMap.toSpanSingleton ℝ v1) t at hgrad
    have hright : (H ∘L ((ContinuousLinearMap.inr ℝ ℝ^m ℝ).prod (0 : ℝ →L[ℝ] ℝ^n))) t
        = (P ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ) t := by
      simp [P, H, E₁, E₂]
    rw [hright] at ht
    exact ht.symm.trans hgrad
  have hInvQ : ((Matrix.toLin' (u0WW x 0)).toContinuousLinearMap).IsInvertible :=
    u0WW_toLin_isInvertible x hx
  have hQeq : Q = (Matrix.toLin' (u0WW x 0)).toContinuousLinearMap := by
    simpa [Q, H, F, u, E₁, E₂] using gradWParam_partial_eq x hx
  have hInvQ' : Q.IsInvertible := by
    simpa [hQeq] using hInvQ
  have hQbar : Q (bud.barw x) = -v1 := by
    rw [hQeq]
    ext α
    simpa [v1, Matrix.toLin'_apply] using congrFun (barw_spec x hx) α
  have hinv_v1 : Q.inverse v1 = - bud.barw x := by
    apply hInvQ'.inverse_apply_eq.mpr
    rw [map_neg, hQbar, neg_neg]
  let cdf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) F u := gradWParam_smooth.contDiffAt
  have hIFT : HasFDerivAt (wStarAt x hx) (-(Q.inverse) ∘L P) u.1 := by
    have hraw := (ContDiffAt.hasStrictFDerivAt_implicitFunction cdf (by simp)
      (gradWParam_partial_isInvertible x hx)).hasFDerivAt
    simpa [wStarAt, F, u, P, Q, H, E₁, E₂, cdf] using hraw
  have hline : HasFDerivAt (fun s : ℝ => (x, s))
      (ContinuousLinearMap.inr ℝ ℝ^m ℝ) 0 :=
    hasFDerivAt_prodMk_right (e₀ := x) (f₀ := (0 : ℝ))
  have hcomp := hIFT.comp (0 : ℝ) hline
  have hL : (-(Q.inverse) ∘L P).comp
      (ContinuousLinearMap.inr ℝ ℝ^m ℝ)
      = ContinuousLinearMap.toSpanSingleton ℝ (bud.barw x) := by
    apply ContinuousLinearMap.ext
    intro t
    have hP_t : (P ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ) t = t • v1 := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun L : ℝ →L[ℝ] ℝ^n => L t) hP_eq
    change -(Q.inverse (P (ContinuousLinearMap.inr ℝ ℝ^m ℝ t))) =
      (ContinuousLinearMap.toSpanSingleton ℝ (bud.barw x)) t
    have hdir : P (ContinuousLinearMap.inr ℝ ℝ^m ℝ t) =
        (P ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ) t := rfl
    rw [hdir, hP_t, map_smul, hinv_v1]
    rw [smul_neg, neg_neg]
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  have htmp : HasFDerivAt (fun s : ℝ => wStarAt x hx (x, s))
      (ContinuousLinearMap.toSpanSingleton ℝ (bud.barw x)) 0 := by
    simpa [hL, u, E₁, E₂, Function.comp_def] using hcomp
  simpa using htmp.hasDerivAt

-- The Euclidean norm of the paper is bounded below by the sup norm on
-- coordinate space.  This is used to get compactness of the closed ball `D`.
lemma pi_norm_le_euclid {d : ℕ} (w : ℝ^d) : ‖w‖ ≤ BrendleHung.Section2.Multivar.norm w := by
  rw [Pi.norm_def]
  have hnn : 0 ≤ BrendleHung.Section2.Multivar.norm w := Real.sqrt_nonneg _
  have h' : (Finset.univ.sup fun i : Fin d => ‖w i‖₊) ≤
      ⟨BrendleHung.Section2.Multivar.norm w, hnn⟩ := by
    rw [Finset.sup_le_iff]
    intro i hi
    have hcoord : ‖w i‖ ≤ BrendleHung.Section2.Multivar.norm w := by
      rw [BrendleHung.Section2.Multivar.norm, Real.norm_eq_abs]
      exact Real.abs_le_sqrt
        (Finset.single_le_sum (fun j hj => sq_nonneg (w j)) (Finset.mem_univ i))
    exact_mod_cast hcoord
  exact_mod_cast h'

/-- The closed coordinate ball `D r` is compact. -/
lemma isCompact_D (r : ℝ) : IsCompact (BrendleHung.Section2.Multivar.D (d := n) r) := by
  refine Metric.isCompact_iff_isClosed_bounded.2 ⟨?_, ?_⟩
  · exact isClosed_D (d := n) r
  · refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ^n)).2 ⟨max r 0, ?_⟩
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using (pi_norm_le_euclid w).trans
      ((show BrendleHung.Section2.Multivar.norm w ≤ r from hw).trans (le_max_left r 0))

/-- The origin belongs to the domain ball `D r0`. -/
lemma D_zero_mem : (0 : ℝ^n) ∈ D (d := n) asm.r0 :=
  zero_mem_D (d := n) (r := asm.r0) (le_of_lt asm.hr0)

-- Existence of a minimizer of `w ↦ u(x,w,s)` on the compact set `D r0`, and
-- the fact that `U(x,s)` is equal to the minimum.
lemma exists_minimizer (x : ℝ^m) (s : ℝ) :
    ∃ w ∈ D (d := n) asm.r0,
      IsMinOn (fun w : ℝ^n => asm.u x w s) (D (d := n) asm.r0) w ∧
      bud.U x s = asm.u x w s
:= by
  have hucont : Continuous (fun w : ℝ^n => asm.u x w s) := by
    have hcomp : Continuous (fun w : ℝ^n => (x, w, s)) := by fun_prop
    exact asm.uSmooth.continuous.comp hcomp
  rcases (isCompact_D asm.r0).exists_isMinOn ⟨0, D_zero_mem⟩ hucont.continuousOn with
    ⟨w, hwD, hwmin⟩
  refine ⟨w, hwD, hwmin, ?_⟩
  have hbdd : BddBelow (Set.range (fun wsub : D (d := n) asm.r0 => asm.u x wsub.1 s)) := by
    refine ⟨asm.u x w s, ?_⟩
    rintro _ ⟨wsub, rfl⟩
    exact hwmin wsub.2
  apply le_antisymm
  · simpa [bud] using (ciInf_le hbdd ⟨w, hwD⟩)
  · haveI : Nonempty (D (d := n) asm.r0) := ⟨⟨0, D_zero_mem⟩⟩
    simpa [bud] using
      (le_ciInf (c := asm.u x w s) (fun wsub : D (d := n) asm.r0 => hwmin wsub.2))

-- Local uniqueness of the implicit solution: near the base point, the
-- critical point equation `gradW = 0` is equivalent to `w = wStarAt`.
lemma wStarAt_eventually_eq_iff_critical (x : ℝ^m) (hx : inBounds x) :
    ∀ᶠ z : (ℝ^m × ℝ) × ℝ^n in 𝓝 (((x, (0 : ℝ)), (0 : ℝ^n))),
      gradW z.1.1 z.2 z.1.2 = 0 ↔ wStarAt x hx z.1 = z.2
:= by
  have hev := ContDiffAt.eventually_apply_eq_iff_implicitFunction
      (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
        (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt)
      (by simp) (gradWParam_partial_isInvertible x hx)
  filter_upwards [hev] with z hz
  have hz0 : gradW x 0 0 = 0 := gradW_zero x hx
  simpa [wStarAt, hz0] using hz

/-- An interior constrained minimizer is a critical point: `gradW x w s = 0`. -/
lemma minimizer_critical (x : ℝ^m) (s : ℝ) (w : ℝ^n)
    (hwin : norm w < asm.r0)
    (hwmin : IsMinOn (fun w : ℝ^n => asm.u x w s) (D (d := n) asm.r0) w) :
    gradW x w s = 0
:= by
  have hBnhds : B asm.r0 ∈ 𝓝 w := B_mem_nhds_of_norm_lt hwin
  have hDnhds : D (d := n) asm.r0 ∈ 𝓝 w :=
    mem_of_superset hBnhds (B_subset_D (d := n) (r := asm.r0))
  have hlocalOn : IsLocalMinOn (fun w : ℝ^n => asm.u x w s) (D (d := n) asm.r0) w :=
    hwmin.localize
  have hlocal : IsLocalMin (fun w : ℝ^n => asm.u x w s) w :=
    hlocalOn.isLocalMin hDnhds
  have hfderiv : fderiv ℝ (fun w : ℝ^n => asm.u x w s) w = 0 :=
    hlocal.fderiv_eq_zero
  ext α
  have h := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hfderiv
  simpa [gradW] using h

-- The minimizer in the definition of `U` is eventually the implicit function
-- `wStarAt`.  The argument is a compactness contradiction: a minimizing
-- sequence must converge to `0` by the quadratic lower bound for `u0`, and
-- then the local uniqueness of critical points gives the result.
lemma bud_U_eq_u_wStarAt_eventually (x : ℝ^m) (hx : inBounds x) :
    ∀ᶠ s : ℝ in 𝓝 0, bud.U x s = asm.u x (wStarAt x hx (x, s)) s
:= by
  classical
  have hwstar_tendsto : Tendsto (fun s : ℝ => wStarAt x hx (x, s)) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (wStarAt x hx) (x, 0) := wStarAt_contDiffAt x hx |>.continuousAt
    have hline : Tendsto (fun s : ℝ => (x, s)) (𝓝 0) (𝓝 (x, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have ht := hcont.tendsto.comp hline
    simpa [wStarAt_self x hx] using ht
  have hmem : ∀ᶠ s : ℝ in 𝓝 0, norm (wStarAt x hx (x, s)) < asm.r0 := by
    have hnorm : Tendsto (fun s : ℝ => norm (wStarAt x hx (x, s))) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (BrendleHung.Section2.Multivar.norm (d := n)) (0 : ℝ^n) :=
        (normCont n).continuousAt
      simpa [BrendleHung.Section2.Multivar.norm] using hc.tendsto.comp hwstar_tendsto
    have hopen : {v : ℝ | v < asm.r0} ∈ 𝓝 (0 : ℝ) :=
      IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) asm.hr0
    exact hnorm.eventually hopen
  have hUle : ∀ᶠ s : ℝ in 𝓝 0,
      bud.U x s ≤ asm.u x (wStarAt x hx (x, s)) s := by
    filter_upwards [hmem] with s hs
    rcases exists_minimizer x s with ⟨w, hwD, hwmin, hUeq⟩
    rw [hUeq]
    exact hwmin (le_of_lt hs)
  by_contra hnot
  have hneq : ∃ᶠ s : ℝ in 𝓝 0,
      bud.U x s ≠ asm.u x (wStarAt x hx (x, s)) s := by
    simpa [not_eventually] using hnot
  have hbad : ∃ᶠ s : ℝ in 𝓝 0,
      bud.U x s < asm.u x (wStarAt x hx (x, s)) s := by
    exact (hneq.and_eventually hUle).mono fun s hs =>
      lt_of_le_of_ne hs.2 hs.1
  let bad : Set ℝ := {s | bud.U x s < asm.u x (wStarAt x hx (x, s)) s}
  haveI : NeBot (𝓝 (0 : ℝ) ⊓ 𝓟 bad) := by
    rw [← frequently_iff_neBot]
    exact hbad
  rcases exists_seq_tendsto (𝓝 (0 : ℝ) ⊓ 𝓟 bad) with ⟨sseq, hsseq⟩
  have hs_tendsto : Tendsto sseq atTop (𝓝 (0 : ℝ)) := (tendsto_inf.1 hsseq).1
  have hs_bad : ∀ᶠ n in atTop, sseq n ∈ bad := by
    simpa [tendsto_principal] using (tendsto_inf.1 hsseq).2
  have hmin_exists : ∀ k : ℕ, ∃ w ∈ D (d := n) asm.r0,
      IsMinOn (fun w : ℝ^n => asm.u x w (sseq k)) (D (d := n) asm.r0) w ∧
      bud.U x (sseq k) = asm.u x w (sseq k) := by
    intro k
    simpa using exists_minimizer x (sseq k)
  choose w hw using hmin_exists
  have hwD : ∀ k, w k ∈ D (d := n) asm.r0 := fun k => (hw k).1
  have hwmin : ∀ k, IsMinOn (fun w : ℝ^n => asm.u x w (sseq k))
      (D (d := n) asm.r0) (w k) := fun k => (hw k).2.1
  have hUeq : ∀ k, bud.U x (sseq k) = asm.u x (w k) (sseq k) := fun k => (hw k).2.2
  have hbad_w : ∀ᶠ k in atTop,
      asm.u x (w k) (sseq k) < asm.u x (wStarAt x hx (x, sseq k)) (sseq k) := by
    filter_upwards [hs_bad] with k hk
    change bud.U x (sseq k) < asm.u x (wStarAt x hx (x, sseq k)) (sseq k) at hk
    rw [hUeq k] at hk
    exact hk
  rcases (isCompact_D asm.r0).tendsto_subseq hwD with
    ⟨w0, hw0D, φ, hφmono, hwsub⟩
  have hφ : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hs_sub : Tendsto (fun k => sseq (φ k)) atTop (𝓝 (0 : ℝ)) := hs_tendsto.comp hφ
  have hbad_sub : ∀ᶠ k in atTop,
      asm.u x (w (φ k)) (sseq (φ k)) <
        asm.u x (wStarAt x hx (x, sseq (φ k))) (sseq (φ k)) :=
    hφ.eventually hbad_w
  have hucontAt : ∀ w : ℝ^n, ∀ s : ℝ,
      ContinuousAt (fun q : ℝ^n × ℝ => asm.u x q.1 q.2) (w, s) := by
    intro w s
    have hcomp : ContinuousAt (fun q : ℝ^n × ℝ => (x, q.1, q.2)) (w, s) := by fun_prop
    have hu : ContinuousAt (fun y : ℝ^m × ℝ^n × ℝ => asm.u y.1 y.2.1 y.2.2)
        (x, w, s) := asm.uSmooth.continuous.continuousAt
    simpa [Function.comp_def] using hu.comp hcomp
  have hR_tendsto : Tendsto
      (fun k => asm.u x (wStarAt x hx (x, sseq k)) (sseq k)) atTop (𝓝 0) := by
    have hpair : Tendsto (fun k => (wStarAt x hx (x, sseq k), sseq k)) atTop
        (𝓝 ((0 : ℝ^n), (0 : ℝ))) :=
      (hwstar_tendsto.comp hs_tendsto).prodMk_nhds hs_tendsto
    have ht := (hucontAt 0 0).tendsto.comp hpair
    have h00 : asm.u x 0 0 = 0 := by
      have h0 := asm.u0AtZero x hx
      simpa [data_u_zero x hx 0 D_zero_mem] using h0
    simpa [h00] using ht
  have hL_tendsto : Tendsto
      (fun k => asm.u x (w (φ k)) (sseq (φ k))) atTop
      (𝓝 (asm.u x w0 0)) := by
    have hpair : Tendsto (fun k => (w (φ k), sseq (φ k))) atTop (𝓝 (w0, 0)) :=
      hwsub.prodMk_nhds hs_sub
    exact (hucontAt w0 0).tendsto.comp hpair
  have hu0_le : asm.u x w0 0 ≤ 0 :=
    le_of_tendsto_of_tendsto hL_tendsto (hR_tendsto.comp hφ)
      (hbad_sub.mono fun k hk => le_of_lt hk)
  have hu0_nonneg : 0 ≤ asm.u x w0 0 := by
    have hquad := asm.u0Quadratic x w0 hx hw0D
    have hnonneg : 0 ≤ asm.σ * (norm w0 ^ 2) :=
      mul_nonneg (le_of_lt asm.hσ) (sq_nonneg _)
    have hEq : asm.u x w0 0 = asm.u0 x w0 := data_u_zero x hx w0 hw0D
    rw [hEq]
    linarith
  have hu0_eq : asm.u x w0 0 = 0 := le_antisymm hu0_le hu0_nonneg
  have hw0 : w0 = 0 := by
    have hquad := asm.u0Quadratic x w0 hx hw0D
    have hsig : asm.σ * (norm w0 ^ 2) ≤ 0 := by
      rw [← data_u_zero x hx w0 hw0D, hu0_eq] at hquad
      exact hquad
    have hn2 : norm w0 ^ 2 = 0 := by nlinarith [asm.hσ, sq_nonneg (norm w0)]
    by_contra hne
    have hpos : 0 < norm w0 := ne_zero_norm_pos hne
    nlinarith
  have hwnorm : Tendsto (fun k => norm (w (φ k))) atTop (𝓝 0) := by
    have ht := (normCont n).continuousAt.tendsto.comp hwsub
    simpa [hw0, BrendleHung.Section2.Multivar.norm] using ht
  have hwin_ev : ∀ᶠ k in atTop, norm (w (φ k)) < asm.r0 := by
    have hopen : {v : ℝ | v < asm.r0} ∈ 𝓝 (0 : ℝ) :=
      IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) asm.hr0
    exact hwnorm.eventually hopen
  have hgrad_ev : ∀ᶠ k in atTop, gradW x (w (φ k)) (sseq (φ k)) = 0 := by
    filter_upwards [hwin_ev] with k hwin
    exact minimizer_critical x (sseq (φ k)) (w (φ k)) hwin (hwmin (φ k))
  have hz_tendsto : Tendsto (fun k => ((x, sseq (φ k)), w (φ k))) atTop
      (𝓝 (((x, (0 : ℝ)), (0 : ℝ^n)))) := by
    have hq : Tendsto (fun k => (x, sseq (φ k))) atTop (𝓝 (x, (0 : ℝ))) :=
      tendsto_const_nhds.prodMk_nhds hs_sub
    have hw : Tendsto (fun k => w (φ k)) atTop (𝓝 (0 : ℝ^n)) := by simpa [hw0] using hwsub
    exact hq.prodMk_nhds hw
  have heqiff_ev : ∀ᶠ k in atTop,
      gradW x (w (φ k)) (sseq (φ k)) = 0 ↔
        wStarAt x hx (x, sseq (φ k)) = w (φ k) :=
    hz_tendsto.eventually (wStarAt_eventually_eq_iff_critical x hx)
  have hw_eq_ev : ∀ᶠ k in atTop,
      w (φ k) = wStarAt x hx (x, sseq (φ k)) := by
    filter_upwards [hgrad_ev, heqiff_ev] with k hg heq
    exact (heq.mp hg).symm
  rcases (hbad_sub.and hw_eq_ev).exists with ⟨k, hlt, heq⟩
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

-- Coordinate-sum expansions for continuous multilinear maps on `ℝ^n`.
lemma clm_apply_eq_sum_basis (L : ℝ^n →L[ℝ] ℝ) (v : ℝ^n) :
    L v = ∑ i : Fin n, v i * L (e i)
:= by
  have hv : v = ∑ i : Fin n, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  rw [hv]
  simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ, map_sum, map_smul, smul_eq_mul]

/-- Expansion of a bilinear map in the standard basis of `ℝ^n`. -/
lemma bilinear_apply_eq_sum_basis
    (B : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)) (v w : ℝ^n) :
    B v w = ∑ i : Fin n, ∑ j : Fin n, v i * w j * B (e i) (e j)
:= by
  have hv : v = ∑ i : Fin n, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  have hw : w = ∑ j : Fin n, w j • e j := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  rw [hv, hw]
  simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ, map_sum, map_smul,
    smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [Finset.sum_comm]

/-- Expansion of a trilinear map in the standard basis of `ℝ^n`. -/
lemma trilinear_apply_eq_sum_basis
    (T : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ))) (u v w : ℝ^n) :
    T u v w = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      u i * v j * w k * T (e i) (e j) (e k)
:= by
  have hu : u = ∑ i : Fin n, u i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  have hv : v = ∑ j : Fin n, v j • e j := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  have hw : w = ∑ k : Fin n, w k • e k := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  rw [hu, hv, hw]
  simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ, map_sum, map_smul,
    smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2]
    intro b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

-- The Hessian action cancels the linear term in the direction of `barw`.
lemma barw_cross_cancel (x : ℝ^m) (hx : inBounds x) (v : ℝ^n) :
    diff2 (asm.u0 x) 0 (bud.barw x) v + diff (asm.u1 x) 0 v = 0
:= by
  let B : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := diff2 (asm.u0 x) 0
  let L : ℝ^n →L[ℝ] ℝ := diff (asm.u1 x) 0
  have hsymm : IsSymmSndFDerivAt ℝ (asm.u0 x) (0 : ℝ^n) := by
    have hsmooth : ContDiff ℝ (2 : WithTop ℕ∞) (asm.u0 x) := by
      simpa [Function.comp_def, Function.uncurry_def] using
        (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x)).of_le le_top
    exact hsmooth.contDiffAt.isSymmSndFDerivAt (by simp)
  have hsymmBV : B (bud.barw x) v = B v (bud.barw x) := by
    simpa [B, diff2, diff] using hsymm.eq (bud.barw x) v
  have hrow (α : Fin n) :
      (∑ β : Fin n, B (e α) (e β) * bud.barw x β) = - u1W x 0 (e α) := by
    have h := congrFun (barw_spec x hx) α
    simpa [Matrix.mulVec, dotProduct, u0WW, Matrix.of_apply, B, diff2, diff] using h
  have hBsum : B v (bud.barw x) = ∑ α : Fin n, v α * (- u1W x 0 (e α)) := by
    rw [bilinear_apply_eq_sum_basis B v (bud.barw x)]
    apply Finset.sum_congr rfl
    intro α hα
    calc
      ∑ β : Fin n, v α * bud.barw x β * B (e α) (e β)
          = v α * (∑ β : Fin n, B (e α) (e β) * bud.barw x β) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro β hβ
            ring
      _ = v α * (- u1W x 0 (e α)) := by rw [hrow]
  have hLsum : L v = ∑ α : Fin n, v α * u1W x 0 (e α) := by
    simpa [L, u1W] using clm_apply_eq_sum_basis L v
  change B (bud.barw x) v + L v = 0
  rw [hsymmBV, hBsum, hLsum]
  simp

/-- The coordinate sum defining `bud.U2` equals the derivative form used in the expansion proof. -/
lemma bud_U2_eq (x : ℝ^m) (_ : inBounds x) :
    bud.U2 x = asm.u2 x 0 + (1 / 2 : ℝ) * diff (asm.u1 x) 0 (bud.barw x)
:= by
  have hsum := clm_apply_eq_sum_basis (diff (asm.u1 x) 0) (bud.barw x)
  change asm.u2 x 0 + ((1 : ℝ) / 2) * ∑ α : Fin n, u1W x 0 (e α) * bud.barw x α =
    asm.u2 x 0 + (1 / 2 : ℝ) * diff (asm.u1 x) 0 (bud.barw x)
  congr 1
  rw [hsum]
  simp [u1W, mul_comm]

/-- The coordinate sums defining `bud.U3` equal their derivative/tensor form. -/
lemma bud_U3_eq (x : ℝ^m) (_ : inBounds x) :
    bud.U3 x =
      asm.u3 x 0 + diff (asm.u2 x) 0 (bud.barw x)
        + (1 / 2 : ℝ) * diff2 (asm.u1 x) 0 (bud.barw x) (bud.barw x)
        + (1 / 6 : ℝ) * diff3 (asm.u0 x) 0 (bud.barw x) (bud.barw x) (bud.barw x)
:= by
  have h1 := clm_apply_eq_sum_basis (diff (asm.u2 x) 0) (bud.barw x)
  have h2 := bilinear_apply_eq_sum_basis (diff2 (asm.u1 x) 0) (bud.barw x) (bud.barw x)
  have h3 := trilinear_apply_eq_sum_basis (diff3 (asm.u0 x) 0)
    (bud.barw x) (bud.barw x) (bud.barw x)
  have h1' : (∑ α : Fin n, u2W x 0 (e α) * bud.barw x α) =
      diff (asm.u2 x) 0 (bud.barw x) := by
    simpa [u2W, mul_comm] using h1.symm
  have h2' : (∑ α : Fin n, ∑ β : Fin n,
      u1WW x 0 α β * bud.barw x α * bud.barw x β) =
      diff2 (asm.u1 x) 0 (bud.barw x) (bud.barw x) := by
    simpa [u1WW, mul_comm, mul_left_comm, mul_assoc] using h2.symm
  have h3' : (∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
      u0WWW x 0 α β γ * bud.barw x α * bud.barw x β * bud.barw x γ) =
      diff3 (asm.u0 x) 0 (bud.barw x) (bud.barw x) (bud.barw x) := by
    simpa [u0WWW, mul_comm, mul_left_comm, mul_assoc] using h3.symm
  change asm.u3 x 0
      + ∑ α : Fin n, u2W x 0 (e α) * bud.barw x α
      + ((1 : ℝ) / 2) * ∑ α : Fin n, ∑ β : Fin n,
          u1WW x 0 α β * bud.barw x α * bud.barw x β
      + ((1 : ℝ) / 6) * ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
          u0WWW x 0 α β γ * bud.barw x α * bud.barw x β * bud.barw x γ =
    asm.u3 x 0 + diff (asm.u2 x) 0 (bud.barw x)
      + (1 / 2 : ℝ) * diff2 (asm.u1 x) 0 (bud.barw x) (bud.barw x)
      + (1 / 6 : ℝ) * diff3 (asm.u0 x) 0 (bud.barw x) (bud.barw x) (bud.barw x)
  rw [h1', h2', h3']

/-- The reduced function vanishes at `s = 0`. -/
lemma bud_U_zero (x : ℝ^m) (hx : inBounds x) : bud.U x 0 = 0 := by
  rcases exists_minimizer x 0 with ⟨w, hwD, hwmin, hUeq⟩
  have hu00 : asm.u x 0 0 = 0 := by
    have h0 := asm.u0AtZero x hx
    simpa [data_u_zero x hx 0 D_zero_mem] using h0
  have hle : bud.U x 0 ≤ 0 := by
    rw [hUeq]
    calc
      asm.u x w 0 ≤ asm.u x 0 0 := hwmin D_zero_mem
      _ = 0 := hu00
  have hge : 0 ≤ bud.U x 0 := by
    rw [hUeq, data_u_zero x hx w hwD]
    have hquad := asm.u0Quadratic x w hx hwD
    have hnonneg : 0 ≤ asm.σ * (norm w ^ 2) :=
      mul_nonneg (le_of_lt asm.hσ) (sq_nonneg _)
    linarith
  exact le_antisymm hle hge

/-- Smoothness of `u0` after fixing the parameter `x`. -/
lemma u0_x_smooth (x : ℝ^m) : SmoothGlobal (asm.u0 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- Smoothness of `u1` after fixing the parameter `x`. -/
lemma u1_x_smooth (x : ℝ^m) : SmoothGlobal (asm.u1 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u1Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- Smoothness of `u2` after fixing the parameter `x`. -/
lemma u2_x_smooth (x : ℝ^m) : SmoothGlobal (asm.u2 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u2Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- Smoothness of `u3` after fixing the parameter `x`. -/
lemma u3_x_smooth (x : ℝ^m) : SmoothGlobal (asm.u3 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u3Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- The fixed-parameter expansion of `u(x, w*(x,s), s)`.  This is the analytic
core of the paper's Section 2 computation: all unknown second-order terms of
`w*` cancel by the critical-point equation, leaving only the stated
`O(s⁴)` remainder. -/
lemma u_remainder_isBigO (x : ℝ^m) (hx : inBounds x) :
    (fun s : ℝ => asm.u x (wStarAt x hx (x, s)) s
        - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4)
:= by
  classical
  rcases asm.uExp with ⟨ρ, hρSmooth, hρeq⟩
  let b : ℝ^n := bud.barw x
  let W : ℝ → ℝ^n := fun s => wStarAt x hx (x, s)
  let R : ℝ → ℝ^n := fun s => W s - s • b
  let B0 : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := diff2 (asm.u0 x) 0
  let C0 : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)) := diff3 (asm.u0 x) 0
  let L1 : ℝ^n →L[ℝ] ℝ := diff (asm.u1 x) 0
  let B1 : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := diff2 (asm.u1 x) 0
  let L2 : ℝ^n →L[ℝ] ℝ := diff (asm.u2 x) 0

  have hWR : ∀ s : ℝ, W s = s • b + R s := by
    intro s
    simp [R]
  have hW0 : W 0 = 0 := by simp [W, wStarAt_self x hx]
  have hWderiv : HasDerivAt W b 0 := by
    simpa [W, b] using hasDerivAt_wStarAt_s x hx
  have hWbig : W =O[𝓝 (0 : ℝ)] (fun s : ℝ => s) := by
    have h := hWderiv.isBigO_sub
    simpa [hW0] using h
  have hWtendsto : Tendsto W (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ^n)) := by
    have ht := hWderiv.continuousAt.tendsto
    simpa [hW0] using ht
  have hWcd : ContDiffAt ℝ (⊤ : WithTop ℕ∞) W 0 := by
    have hline : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun s : ℝ => (x, s)) 0 := by fun_prop
    simpa [W, Function.comp_def] using (wStarAt_contDiffAt x hx).comp (0 : ℝ) hline
  have hRnorm := taylor_one_isBigO_of_contDiffAt hWcd
  have hR : R =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) := by
    have htmp : R =O[𝓝 (0 : ℝ)] (fun s : ℝ => ‖s‖ ^ (2 : ℕ)) :=
      hRnorm.congr_left (fun s => by
        simp [R, taylorRemainderOne, hW0, hWderiv.hasFDerivAt.fderiv,
          ContinuousLinearMap.toSpanSingleton_apply])
    exact htmp.trans (isBigO_norm_pow_eq 2)

  have hcompose : ∀ {k : ℕ} {f : ℝ^n → ℝ},
      f =O[𝓝 (0 : ℝ^n)] (fun w : ℝ^n => ‖w‖ ^ k) →
      (fun s : ℝ => f (W s)) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ k) := by
    intro k f hf
    exact (hf.comp_tendsto hWtendsto).trans (hWbig.norm_left.pow k)

  have hWmem : ∀ᶠ s : ℝ in 𝓝 0, W s ∈ D (d := n) asm.r0 := by
    filter_upwards [hWtendsto.eventually (B_mem_nhds_zero asm.hr0)] with s hs
    exact le_of_lt hs
  have hseg : ∀ᶠ s : ℝ in 𝓝 0, s ∈ segment asm.s0 :=
    segment_mem_nhds_zero asm.hs0
  have hExpEq : (fun s : ℝ => asm.u x (W s) s) =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => asm.u0 x (W s) + s * asm.u1 x (W s)
        + s ^ 2 * asm.u2 x (W s) + s ^ 3 * asm.u3 x (W s)
        + s ^ 4 * ρ ((x, W s), s)) := by
    filter_upwards [hWmem, hseg] with s hWs hs
    exact hρeq (x, W s) s ⟨hx, hWs⟩ hs

  have hρline : Tendsto (fun s : ℝ => ((x, W s), s)) (𝓝 (0 : ℝ))
      (𝓝 ((x, W 0), (0 : ℝ))) := by
    simpa [hW0] using
      ((tendsto_const_nhds.prodMk_nhds hWtendsto).prodMk_nhds tendsto_id)
  have hρcont : ContinuousAt (fun s : ℝ => ρ ((x, W s), s)) 0 := by
    exact (contDiffOn_univ.mp hρSmooth).continuous.continuousAt.tendsto.comp hρline
  have hρO : (fun s : ℝ => ρ ((x, W s), s)) =O[𝓝 (0 : ℝ)]
      (fun _ : ℝ => (1 : ℝ)) := isBigO_one_of_continuousAt hρcont
  have hρ4 : (fun s : ℝ => s ^ 4 * ρ ((x, W s), s)) =O[𝓝 (0 : ℝ)]
      (fun s : ℝ => s ^ 4) := by
    refine (hρO.mul (Asymptotics.isBigO_refl (fun s : ℝ => s ^ 4) (𝓝 (0 : ℝ)))).congr ?_ ?_
    · intro s
      ring
    · intro s
      ring

  have hdu0 : diff (asm.u0 x) 0 = 0 := by
    ext v
    simpa [u0W] using congrFun (u0WAtZero x hx) v
  have hu00 : asm.u0 x 0 = 0 := asm.u0AtZero x hx
  have hu10 : asm.u1 x 0 = 0 := asm.u1AtZero x hx
  have h0rem : (fun s : ℝ =>
      asm.u0 x (W s)
        - (1 / 2 : ℝ) * B0 (W s) (W s)
        - (1 / 6 : ℝ) * C0 (W s) (W s) (W s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa [taylorRemainderThree, B0, C0, hdu0, hu00, smul_eq_mul] using
      hcompose (k := 4) (smooth_taylor_three_isBigO (u0_x_smooth x))
  have h1rem : (fun s : ℝ =>
      asm.u1 x (W s) - L1 (W s) - (1 / 2 : ℝ) * B1 (W s) (W s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 3) := by
    simpa [taylorRemainderTwo, L1, B1, hu10, smul_eq_mul] using
      hcompose (k := 3) (smooth_taylor_two_isBigO (u1_x_smooth x))
  have h2rem : (fun s : ℝ =>
      asm.u2 x (W s) - asm.u2 x 0 - L2 (W s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) := by
    simpa [L2] using hcompose (k := 2) (smooth_taylor_one_isBigO (u2_x_smooth x))
  have h3base : (fun z : ℝ^n => asm.u3 x z - asm.u3 x 0)
      =O[𝓝 (0 : ℝ^n)] (fun z : ℝ^n => ‖z‖ ^ (1 : ℕ)) := by
    simpa using smooth_taylor_zero_isBigO (u3_x_smooth x)
  have h3rem : (fun s : ℝ => asm.u3 x (W s) - asm.u3 x 0)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ (1 : ℕ)) := by
    simpa using hcompose (k := 1) h3base
  have h1s : (fun s : ℝ =>
      s * (asm.u1 x (W s) - L1 (W s) - (1 / 2 : ℝ) * B1 (W s) (W s)))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow h1rem 1
  have h2s : (fun s : ℝ => s ^ 2 * (asm.u2 x (W s) - asm.u2 x 0 - L2 (W s)))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow h2rem 2
  have h3s : (fun s : ℝ => s ^ 3 * (asm.u3 x (W s) - asm.u3 x 0))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow h3rem 3
  have hsmall : (fun s : ℝ =>
      (asm.u0 x (W s)
          - (1 / 2 : ℝ) * B0 (W s) (W s)
          - (1 / 6 : ℝ) * C0 (W s) (W s) (W s))
      + s * (asm.u1 x (W s) - L1 (W s) - (1 / 2 : ℝ) * B1 (W s) (W s))
      + s ^ 2 * (asm.u2 x (W s) - asm.u2 x 0 - L2 (W s))
      + s ^ 3 * (asm.u3 x (W s) - asm.u3 x 0)
      + s ^ 4 * ρ ((x, W s), s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) :=
    (((h0rem.add h1s).add h2s).add h3s).add hρ4

  have hsymm0 : IsSymmSndFDerivAt ℝ (asm.u0 x) (0 : ℝ^n) :=
    (u0_x_smooth x).contDiffAt.isSymmSndFDerivAt (by simp)
  have hB0symm : ∀ v w : ℝ^n, B0 v w = B0 w v := by
    intro v w
    simpa [B0, diff2, diff] using hsymm0.eq v w
  have hBRR : (fun s : ℝ => B0 (R s) (R s)) =O[𝓝 (0 : ℝ)]
      (fun s : ℝ => s ^ 4) := by
    exact (isBigO_bilinear_apply B0 hR hR).congr (fun _ => rfl) (fun s => by ring)
  have hlead0half : (1 / 2 : ℝ) * B0 b b + (1 / 2 : ℝ) * L1 b = 0 := by
    have hlead0raw : B0 b b + L1 b = 0 := by
      simpa [b, B0, L1] using barw_cross_cancel x hx b
    linarith
  have hA0eq : (fun s : ℝ =>
      (1 / 2 : ℝ) * B0 (W s) (W s) + s * L1 (W s)
        - s ^ 2 * (1 / 2 : ℝ) * L1 b) =
      (fun s : ℝ => (1 / 2 : ℝ) * B0 (R s) (R s)) := by
    funext s
    have hsymmRs : B0 (R s) b = B0 b (R s) := hB0symm (R s) b
    have hcross : B0 b (R s) + L1 (R s) = 0 := by
      simpa [b, B0, L1] using barw_cross_cancel x hx (R s)
    calc
      (1 / 2 : ℝ) * B0 (W s) (W s) + s * L1 (W s)
          - s ^ 2 * (1 / 2 : ℝ) * L1 b
          = s ^ 2 * ((1 / 2 : ℝ) * B0 b b + (1 / 2 : ℝ) * L1 b)
              + s * (B0 b (R s) + L1 (R s))
              + (1 / 2 : ℝ) * B0 (R s) (R s) := by
            rw [hWR s]
            simp [map_add, map_smul, smul_eq_mul, hsymmRs]
            ring
      _ = (1 / 2 : ℝ) * B0 (R s) (R s) := by
            rw [hlead0half, hcross]
            ring
  have hA0 : (fun s : ℝ =>
      (1 / 2 : ℝ) * B0 (W s) (W s) + s * L1 (W s)
        - s ^ 2 * (1 / 2 : ℝ) * L1 b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    rw [hA0eq]
    exact hBRR.const_mul_left (1 / 2 : ℝ)

  have hCdiff : (fun s : ℝ =>
      C0 (W s) (W s) (W s) - s ^ 3 * C0 b b b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    exact (trilinear_leading_isBigO C0 b hR).congr_left (fun s => by
      rw [← hWR s])
  have hA1 : (fun s : ℝ =>
      (1 / 6 : ℝ) * (C0 (W s) (W s) (W s) - s ^ 3 * C0 b b b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) :=
    hCdiff.const_mul_left (1 / 6 : ℝ)

  have hB1diff : (fun s : ℝ =>
      B1 (W s) (W s) - s ^ 2 * B1 b b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 3) := by
    exact (bilinear_leading_isBigO B1 b hR).congr_left (fun s => by
      rw [← hWR s])
  have hA2 : (fun s : ℝ =>
      (s / 2) * (B1 (W s) (W s) - s ^ 2 * B1 b b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    have hraw := hB1diff.const_mul_left (1 / 2 : ℝ)
    refine (isBigO_mul_pow_of_isBigO_pow hraw 1).congr_left ?_
    intro s
    ring

  have hL2diff : (fun s : ℝ => L2 (W s) - s * L2 b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) := by
    have hL2R : (fun s : ℝ => L2 (R s)) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) :=
      isBigO_clm_apply (α := ℝ) (E := ℝ^n) (F := ℝ^n) (G := ℝ)
        (l := 𝓝 (0 : ℝ)) L2 hR
    refine hL2R.congr_left ?_
    intro s
    rw [hWR s]
    simp [map_add, map_smul, smul_eq_mul]
  have hA3 : (fun s : ℝ => s ^ 2 * (L2 (W s) - s * L2 b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hL2diff 2

  have hleadSum : (fun s : ℝ =>
      ((1 / 2 : ℝ) * B0 (W s) (W s) + s * L1 (W s)
          - s ^ 2 * (1 / 2 : ℝ) * L1 b)
      + (1 / 6 : ℝ) * (C0 (W s) (W s) (W s) - s ^ 3 * C0 b b b)
      + (s / 2) * (B1 (W s) (W s) - s ^ 2 * B1 b b)
      + s ^ 2 * (L2 (W s) - s * L2 b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) :=
    (((hA0.add hA1).add hA2).add hA3)
  have hlead : (fun s : ℝ =>
      (1 / 2 : ℝ) * B0 (W s) (W s)
      + (1 / 6 : ℝ) * C0 (W s) (W s) (W s)
      + s * L1 (W s)
      + (s / 2) * B1 (W s) (W s)
      + s ^ 2 * asm.u2 x 0
      + s ^ 2 * L2 (W s)
      + s ^ 3 * asm.u3 x 0
      - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    refine hleadSum.congr_left ?_
    intro s
    rw [bud_U2_eq x hx, bud_U3_eq x hx]
    simp [b, B0, C0, L1, B1, L2]
    ring

  have hpoly : (fun s : ℝ =>
      asm.u0 x (W s) + s * asm.u1 x (W s)
      + s ^ 2 * asm.u2 x (W s) + s ^ 3 * asm.u3 x (W s)
      + s ^ 4 * ρ ((x, W s), s)
      - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    have htotal := hsmall.add hlead
    refine htotal.congr_left ?_
    intro s
    simp [B0, C0, L1, B1, L2]
    ring
  have htarget : (fun s : ℝ =>
      asm.u x (W s) s - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    refine hpoly.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hExpEq] with s hs
    rw [hs]
  simpa [W] using htarget

/-- Hessian of `u0(x, ·)` at zero as a continuous linear map. -/
noncomputable abbrev u0WWLin (x : ℝ^m) : ℝ^n →L[ℝ] ℝ^n
:= (Matrix.toLin' (u0WW x 0)).toContinuousLinearMap

/-- Gradient of `u1(x, ·)` at zero as a vector in the standard basis. -/
noncomputable abbrev u1WVec (x : ℝ^m) : ℝ^n
:= fun α : Fin n => u1W x 0 (e α)

/-- Smoothness in `x` of one Hessian component of `u0(x, ·)` at zero. -/
lemma u0WW_smooth_apply (α β : Fin n) : SmoothGlobal (fun x : ℝ^m => u0WW x 0 α β)
:= by
  let f : ((ℝ^m × ℝ^n) × ℝ^n) → ℝ^n → ℝ :=
    fun z w => asm.u0 z.1.1 w
  have hf : SmoothGlobal (uncurry f) := by
    have hcomp : SmoothGlobal (fun z : (((ℝ^m × ℝ^n) × ℝ^n) × ℝ^n) =>
        (z.1.1.1, z.2)) := by fun_prop
    simpa [f, Function.uncurry_def] using asm.u0Smooth.comp hcomp
  have hD : SmoothGlobal (fun z : (ℝ^m × ℝ^n) × ℝ^n =>
      fderiv ℝ (fun w : ℝ^n => asm.u0 z.1.1 w) z.2) := by
    simpa [f] using hf.fderiv
      (g := fun z : (ℝ^m × ℝ^n) × ℝ^n => z.2)
      (by fun_prop) (by simp)
  have hDapp : SmoothGlobal (fun z : (ℝ^m × ℝ^n) × ℝ^n =>
      fderiv ℝ (fun w : ℝ^n => asm.u0 z.1.1 w) z.2 (e β)) := by
    simpa using hD.clm_apply
      (contDiff_const : SmoothGlobal (fun _ : (ℝ^m × ℝ^n) × ℝ^n => e β))
  let f2 : (ℝ^m × ℝ^n) → ℝ^n → ℝ :=
    fun q w => fderiv ℝ (fun v : ℝ^n => asm.u0 q.1 v) w (e β)
  have hf2 : SmoothGlobal (uncurry f2) := by
    simpa [f2] using hDapp
  have h2prod : SmoothGlobal (fun q : ℝ^m × ℝ^n =>
      fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun v : ℝ^n => asm.u0 q.1 v) w (e β))
        q.2 (e α)) := by
    simpa [f2] using hf2.fderiv_apply
      (g := fun q : ℝ^m × ℝ^n => q.2)
      (k := fun _ : ℝ^m × ℝ^n => e α)
      (by fun_prop) (by fun_prop) (by simp)
  have hincl : SmoothGlobal (fun x : ℝ^m => (x, (0 : ℝ^n))) := by fun_prop
  have h2 : SmoothGlobal (fun x : ℝ^m =>
      fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun v : ℝ^n => asm.u0 x v) w (e β))
        0 (e α)) := by
    simpa using h2prod.comp hincl
  have hEq : (fun x : ℝ^m => u0WW x 0 α β) =
      (fun x : ℝ^m =>
        fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun v : ℝ^n => asm.u0 x v) w (e β))
          0 (e α)) := by
    funext x
    have hc : DifferentiableAt ℝ (fun w : ℝ^n => fderiv ℝ (asm.u0 x) w) 0 := by
      exact ((u0_x_smooth x).fderiv_right (m := ⊤) (by simp)).differentiable (by simp) 0
    rw [fderiv_clm_apply hc (differentiableAt_const (c := e β))]
    simp [u0WW, diff2, diff]
  rw [hEq]
  exact h2

/-- The Hessian matrix of `u0(x, ·)` at zero is symmetric. -/
lemma u0WW_symm (x : ℝ^m) (α β : Fin n) : u0WW x 0 α β = u0WW x 0 β α
:= by
  have hsymm : IsSymmSndFDerivAt ℝ (asm.u0 x) (0 : ℝ^n) :=
    (u0_x_smooth x).contDiffAt.isSymmSndFDerivAt (by simp)
  simpa [u0WW, diff2, diff] using hsymm.eq (e α) (e β)

/-- Smoothness in `x` of one component of the gradient of `u1(x, ·)` at zero. -/
lemma u1W_smooth_apply (α : Fin n) : SmoothGlobal (fun x : ℝ^m => u1W x 0 (e α))
:= by
  let f : ℝ^m → ℝ^n → ℝ := fun x w => asm.u1 x w
  have hf : SmoothGlobal (uncurry f) := by
    simpa [f, Function.uncurry_def] using asm.u1Smooth
  simpa [f, u1W] using hf.fderiv_apply
    (g := fun x : ℝ^m => (0 : ℝ^n)) (k := fun _ : ℝ^m => e α)
    (by fun_prop) (by fun_prop) (by simp)

/-- Smoothness of the Hessian of `u0(x, ·)` at zero as a linear map. -/
lemma u0WWLin_smooth : SmoothGlobal u0WWLin
:= by
  rw [contDiff_clm_apply_iff]
  intro z
  rw [contDiff_pi]
  intro α
  have hsum : SmoothGlobal (fun x : ℝ^m => ∑ β : Fin n, u0WW x 0 α β * z β) := by
    exact ContDiff.sum (s := Finset.univ) (fun β _ =>
      (u0WW_smooth_apply α β).mul contDiff_const)
  simpa [u0WWLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hsum

/-- Smoothness of the gradient vector of `u1(x, ·)` at zero. -/
lemma u1WVec_smooth : SmoothGlobal u1WVec
:= by
  rw [contDiff_pi]
  intro α
  simpa [u1WVec] using u1W_smooth_apply α

/-- The defining equation for `barw` holds wherever the Hessian determinant is nonzero. -/
lemma barw_spec_of_det_ne_zero (x : ℝ^m) (hdet : (u0WW x 0).det ≠ 0) :
    u0WW x 0 *ᵥ bud.barw x = - u1WVec x
:= by
  classical
  have hunitDet : IsUnit (u0WW x 0).det := isUnit_iff_ne_zero.mpr hdet
  have hmul : u0WW x 0 *ᵥ ((u0WW x 0)⁻¹ *ᵥ (-u1WVec x)) = -u1WVec x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunitDet, Matrix.one_mulVec]
  ext α
  simpa [bud, u1WVec] using congrFun hmul α

/-- The reduced direction `barw` is smooth at an admissible point. -/
lemma barw_contDiffAt (x : ℝ^m) (hx : inBounds x) : ContDiffAt ℝ ⊤ bud.barw x
:= by
  have hA : ContDiffAt ℝ ⊤ u0WWLin x := u0WWLin_smooth.contDiffAt
  have hInv : ContDiffAt ℝ ⊤ (fun y => (u0WWLin y).inverse) x := by
    exact (u0WW_toLin_isInvertible x hx).contDiffAt_map_inverse.comp x hA
  have hVec : ContDiffAt ℝ ⊤ (fun y => -u1WVec y) x :=
    u1WVec_smooth.contDiffAt.neg
  have hExpr : ContDiffAt ℝ ⊤ (fun y => (u0WWLin y).inverse (-u1WVec y)) x :=
    hInv.clm_apply hVec
  have hdetx : (u0WW x 0).det ≠ 0 := by
    have hunitDet : IsUnit (u0WW x 0).det :=
      (Matrix.isUnit_iff_isUnit_det (u0WW x 0)).mp (u0WWAtZero x hx).isUnit
    exact hunitDet.ne_zero
  have hMat : Continuous (fun y : ℝ^m => u0WW y 0) :=
    continuous_matrix (fun α β => (u0WW_smooth_apply α β).continuous)
  have hdetCont : ContinuousAt (fun y : ℝ^m => (u0WW y 0).det) x :=
    hMat.matrix_det.continuousAt
  have hdetEv : ∀ᶠ y : ℝ^m in 𝓝 x, (u0WW y 0).det ≠ 0 :=
    hdetCont.eventually_ne hdetx
  have hEqEv : (fun y : ℝ^m => (u0WWLin y).inverse (-u1WVec y)) =ᶠ[𝓝 x] bud.barw := by
    filter_upwards [hdetEv] with y hydet
    have hunitDet : IsUnit (u0WW y 0).det := isUnit_iff_ne_zero.mpr hydet
    have hyinv : (u0WWLin y).IsInvertible := by
      classical
      let eLin : (ℝ^n) ≃ₗ[ℝ] (ℝ^n) :=
        (u0WW y 0).toLinearEquiv (Pi.basisFun ℝ (Fin n)) hunitDet
      refine ⟨eLin.toContinuousLinearEquiv, ?_⟩
      ext v i
      simp [u0WWLin, eLin, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    exact hyinv.inverse_apply_eq.mpr (barw_spec_of_det_ne_zero y hydet).symm
  exact hExpr.congr_of_eventuallyEq hEqEv.symm

/-- For `y ∈ Ω`, the `z`-slice of `ψ` is globally smooth near `z = 0`. -/
lemma CoordChangeAssumptions.psi_z_smoothAt
    (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (fun z : ℝ^n => cca.ψ (y, z)) 0
:= by
  have hopen : IsOpen (cca.Ω ×ˢ (B (d := n) cca.r1)) :=
    cca.Ω_open.prod (isOpen_B (d := n) cca.r1)
  have hmem : (y, (0 : ℝ^n)) ∈ cca.Ω ×ˢ (B (d := n) cca.r1) := by
    refine ⟨hy, ?_⟩
    simpa [B, BrendleHung.Section2.Multivar.norm] using cca.r1_pos
  have hψat : ContDiffAt ℝ ⊤ cca.ψ (y, 0) :=
    cca.ψ_smooth.contDiffAt (hopen.mem_nhds hmem)
  have hslice : Smooth (fun z : ℝ^n => (y, z)) on (Set.univ : Set ℝ^n) :=
    (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) y).contDiffOn
  exact hψat.comp 0 (hslice.contDiffAt (by simp))

noncomputable section

/-- The uncurried zero-order function `u0` on the product space. -/
abbrev u0Prod (q : ℝ^m × ℝ^n) : ℝ := asm.u0 q.1 q.2

/-- First derivative of `u0Prod`. -/
abbrev u0D1 (q : ℝ^m × ℝ^n) : (ℝ^m × ℝ^n) →L[ℝ] ℝ := fderiv ℝ u0Prod q

/-- Second derivative of `u0Prod`. -/
abbrev u0D2 (q : ℝ^m × ℝ^n) : (ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) := fderiv ℝ u0D1 q

/-- Third derivative of `u0Prod`. -/
abbrev u0D3 (q : ℝ^m × ℝ^n) : (ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ)) :=
  fderiv ℝ u0D2 q

/-- The `i`-th coordinate direction in the `x` factor of the product. -/
abbrev ix (i : Fin m) : ℝ^m × ℝ^n := (e i, 0)
/-- The `α`-th coordinate direction in the `w` factor of the product. -/
abbrev iw (α : Fin n) : ℝ^m × ℝ^n := (0, e α)

/-- Mixed `x^i w^α w^β` derivative of `u0` at `(x,0)`. -/
abbrev u0XWW (x : ℝ^m) (i : Fin m) (α β : Fin n) : ℝ :=
  fderiv ℝ (fun x' : ℝ^m => u0WW x' 0 α β) x (e i)

/-- The first derivative in the `z^α` direction at zero. -/
abbrev zD1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ^n → E) (α : Fin n) : E := fderiv ℝ F 0 (e α)

/-- The second derivative in the `z^α`, `z^β` directions at zero. -/
abbrev zD2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ^n → E) (α β : Fin n) : E :=
  fderiv ℝ (fun z : ℝ^n => fderiv ℝ F z (e β)) 0 (e α)

/-- The third derivative in the `z^α`, `z^β`, `z^γ` directions at zero. -/
abbrev zD3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ^n → E) (α β γ : Fin n) : E :=
  fderiv ℝ (fun z : ℝ^n => fderiv ℝ (fun z' : ℝ^n => fderiv ℝ F z' (e γ)) z (e β)) 0 (e α)

/-- Smoothness of the product-space version of `u0`. -/
lemma u0Prod_smooth : SmoothGlobal u0Prod := by
  simpa [u0Prod] using asm.u0Smooth

/-- Smoothness of the first derivative of `u0Prod`. -/
lemma u0D1_smooth : SmoothGlobal u0D1 := by
  simpa [u0D1] using u0Prod_smooth.fderiv_right (m := ⊤) (by simp)

/-- Smoothness of the second derivative of `u0Prod`. -/
lemma u0D2_smooth : SmoothGlobal u0D2 := by
  simpa [u0D2, u0D1] using u0D1_smooth.fderiv_right (m := ⊤) (by simp)

/-- The first `z`-derivative of a coordinate-change map `G`. -/
abbrev dG (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n) (α : Fin n) : ℝ^m × ℝ^n :=
  fderiv ℝ G z (e α)

/-- The mixed `z^α z^β` derivative of `G`, differentiating `e β` first. -/
abbrev d2G (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n) (α β : Fin n) : ℝ^m × ℝ^n :=
  fderiv ℝ (fun z' : ℝ^n => dG G z' β) z (e α)

/-- The mixed `z^α z^β z^γ` derivative of `G`, differentiating `e γ`, then `e β`,
then `e α`. -/
abbrev d3G (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n) (α β γ : Fin n) : ℝ^m × ℝ^n :=
  fderiv ℝ (fun z' : ℝ^n => d2G G z' β γ) z (e α)

/-- The derivative of `u0Prod` in a pure `w` direction is the `w`-derivative of `u0`. -/
lemma u0D1_snd (x : ℝ^m) (w v : ℝ^n) :
    u0D1 (x, w) (0, v) = diff (asm.u0 x) w v := by
  have hG : DifferentiableAt ℝ (fun w' : ℝ^n => (x, w')) w := by fun_prop
  have hU : DifferentiableAt ℝ u0Prod (x, w) := u0Prod_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun w' : ℝ^n => (x, w')) w =
      ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_right x w).fderiv
  have hEq : fderiv ℝ (fun w' : ℝ^n => u0Prod (x, w')) w =
      u0D1 (x, w) ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := by
    simpa [u0D1, hGderiv] using fderiv_comp' w hU hG
  have hSlice : (fun w' : ℝ^n => u0Prod (x, w')) = (fun w' : ℝ^n => asm.u0 x w') := rfl
  rw [hSlice] at hEq
  simpa using (congrArg (fun L : ℝ^n →L[ℝ] ℝ => L v) hEq).symm

/-- The derivative of `u0Prod` in a pure `x` direction is the `x`-derivative at fixed `w`. -/
lemma u0D1_fst (x v : ℝ^m) (w : ℝ^n) :
    u0D1 (x, w) (v, 0) = fderiv ℝ (fun x' : ℝ^m => asm.u0 x' w) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u0Prod (x, w) := u0Prod_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u0Prod (x', w)) x =
      u0D1 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u0D1, hGderiv] using fderiv_comp' x hU hG
  have hSlice : (fun x' : ℝ^m => u0Prod (x', w)) = (fun x' : ℝ^m => asm.u0 x' w) := rfl
  rw [hSlice] at hEq
  simpa using (congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hEq).symm

/-- A vector in the product splits into its `x` and `w` components. -/
lemma prod_vec_split (v : ℝ^m × ℝ^n) : (v.1, (0 : ℝ^n)) + (0, v.2) = v := by
  ext <;> simp

/-- A finite-dimensional vector is the sum of its coordinate multiples of the basis vectors. -/
lemma pi_sum_basis {d : ℕ} (v : ℝ^d) : v = ∑ i : Fin d, v i • e i := by
  ext j
  simp [e, Pi.single_apply]

/-- The first derivative of `u0Prod` splits into pure `x` and `w` parts. -/
lemma u0D1_split (q : ℝ^m × ℝ^n) (v : ℝ^m × ℝ^n) :
    u0D1 q v = u0D1 q (v.1, 0) + u0D1 q (0, v.2) := by
  conv_lhs => rw [← prod_vec_split v]
  rw [map_add]

/-- The first derivative of `u0Prod` vanishes at `(y,0)` for `y ∈ Ω`. -/
lemma u0D1_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : u0D1 (y, 0) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hx : fderiv ℝ (fun x : ℝ^m => asm.u0 x 0) y = 0 := by
    have h : (fun x : ℝ^m => asm.u0 x 0) =ᶠ[𝓝 y] (fun _ : ℝ^m => 0) := by
      filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
      exact asm.u0AtZero x (B_subset_D (cca.Ω_subset_B hx))
    simpa using h.fderiv_eq
  have hw : diff (asm.u0 y) 0 = 0 := by
    ext w
    simpa [u0W] using congrFun (u0WAtZero y (B_subset_D (cca.Ω_subset_B hy))) w
  rw [u0D1_split, u0D1_fst, u0D1_snd]
  simp [hx, hw]

/-- Second derivative of `u0Prod` in two pure `w` directions. -/
lemma u0D2_snd_snd (x : ℝ^m) (w v dv : ℝ^n) :
    u0D2 (x, w) (0, v) (0, dv) =
      fderiv ℝ (fun w' : ℝ^n => diff (asm.u0 x) w' dv) w v := by
  have hG : DifferentiableAt ℝ (fun w' : ℝ^n => (x, w')) w := by fun_prop
  have hU : DifferentiableAt ℝ u0D1 (x, w) := u0D1_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun w' : ℝ^n => (x, w')) w =
      ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_right x w).fderiv
  have hEq : fderiv ℝ (fun w' : ℝ^n => u0D1 (x, w')) w =
      u0D2 (x, w) ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := by
    simpa [u0D2, hGderiv] using fderiv_comp' w hU hG
  have hfun : (fun w' : ℝ^n => u0D1 (x, w') (0, dv)) =
      (fun w' : ℝ^n => diff (asm.u0 x) w' dv) := by
    funext w'
    exact u0D1_snd x w' dv
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L v (0, dv)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hval
  have hc : DifferentiableAt ℝ (fun w' : ℝ^n => u0D1 (x, w')) w := hU.comp w hG
  have happ := fderiv_clm_apply hc (differentiableAt_const (c := (0, dv)))
  have hval2 : (fderiv ℝ (fun w' : ℝ^n => u0D1 (x, w') (0, dv)) w) v =
      ((fderiv ℝ (fun w' : ℝ^n => u0D1 (x, w')) w) v) (0, dv) := by
    simpa using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L v) happ
  calc
    u0D2 (x, w) (0, v) (0, dv) = ((fderiv ℝ (fun w' : ℝ^n => u0D1 (x, w')) w) v) (0, dv) := hval.symm
    _ = (fderiv ℝ (fun w' : ℝ^n => u0D1 (x, w') (0, dv)) w) v := hval2.symm
    _ = (fderiv ℝ (fun w' : ℝ^n => diff (asm.u0 x) w' dv) w) v := by rw [hfun]

/-- Second derivative of `u0Prod` in coordinate `w` directions recovers `u0WW`. -/
lemma u0D2_ww (x : ℝ^m) (w : ℝ^n) (α β : Fin n) :
    u0D2 (x, w) (iw α) (iw β) = u0WW x w α β := by
  rw [u0D2_snd_snd]
  have hc : DifferentiableAt ℝ (diff (asm.u0 x)) w :=
    ((u0_x_smooth x).fderiv_right (m := ⊤) (by simp)).differentiable (by simp) w
  rw [fderiv_clm_apply hc (differentiableAt_const (c := e β))]
  simp [u0WW, diff2, Matrix.of_apply]

/-- Second derivative of `u0Prod` in an `x` direction then a `w` direction. -/
lemma u0D2_fst_snd (x : ℝ^m) (v : ℝ^m) (w dv : ℝ^n) :
    u0D2 (x, w) (v, 0) (0, dv) =
      fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w) (0, dv)) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u0D1 (x, w) := u0D1_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w)) x =
      u0D2 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u0D2, hGderiv] using fderiv_comp' x hU hG
  have hval := congrArg (fun L : ℝ^m →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L v (0, dv)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at hval
  have hc : DifferentiableAt ℝ (fun x' : ℝ^m => u0D1 (x', w)) x := hU.comp x hG
  have happ := fderiv_clm_apply hc (differentiableAt_const (c := (0, dv)))
  have hval2 : (fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w) (0, dv)) x) v =
      ((fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w)) x) v) (0, dv) := by
    simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) happ
  calc
    u0D2 (x, w) (v, 0) (0, dv) = ((fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w)) x) v) (0, dv) := hval.symm
    _ = (fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w) (0, dv)) x) v := hval2.symm

/-- Second derivative of `u0Prod` in two pure `x` directions. -/
lemma u0D2_fst_fst (x : ℝ^m) (v dv : ℝ^m) (w : ℝ^n) :
    u0D2 (x, w) (v, 0) (dv, 0) =
      fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w) (dv, 0)) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u0D1 (x, w) := u0D1_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w)) x =
      u0D2 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u0D2, hGderiv] using fderiv_comp' x hU hG
  have hval := congrArg (fun L : ℝ^m →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L v (dv, 0)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at hval
  have hc : DifferentiableAt ℝ (fun x' : ℝ^m => u0D1 (x', w)) x := hU.comp x hG
  have happ := fderiv_clm_apply hc (differentiableAt_const (c := (dv, 0)))
  have hval2 : (fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w) (dv, 0)) x) v =
      ((fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w)) x) v) (dv, 0) := by
    simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) happ
  calc
    u0D2 (x, w) (v, 0) (dv, 0) = ((fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w)) x) v) (dv, 0) := hval.symm
    _ = (fderiv ℝ (fun x' : ℝ^m => u0D1 (x', w) (dv, 0)) x) v := hval2.symm

/-- The mixed `x`-then-`w` second derivative of `u0Prod` vanishes at `(y,0)`. -/
lemma u0D2_cross_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (v : ℝ^m) (ζ : ℝ^n) :
    u0D2 (y, 0) (v, 0) (0, ζ) = 0 := by
  rw [u0D2_fst_snd]
  have hfun : (fun x' : ℝ^m => u0D1 (x', 0) (0, ζ)) =ᶠ[𝓝 y] (fun _ : ℝ^m => 0) := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
    rw [u0D1_snd]
    have h := congrArg (fun f : ℝ^n → ℝ => f ζ)
      (u0WAtZero x (B_subset_D (cca.Ω_subset_B hx)))
    simpa [u0W] using h
  have hfd : fderiv ℝ (fun x' : ℝ^m => u0D1 (x', 0) (0, ζ)) y =
      fderiv ℝ (fun _ : ℝ^m => (0 : ℝ)) y := hfun.fderiv_eq
  simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hfd

/-- The pure `x` second derivative of `u0Prod` vanishes at `(y,0)`. -/
lemma u0D2_xx_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (v dv : ℝ^m) :
    u0D2 (y, 0) (v, 0) (dv, 0) = 0 := by
  rw [u0D2_fst_fst]
  have hfun : (fun x' : ℝ^m => u0D1 (x', 0) (dv, 0)) =ᶠ[𝓝 y] (fun _ : ℝ^m => 0) := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
    rw [u0D1_fst]
    have hzero : (fun x'' : ℝ^m => asm.u0 x'' 0) =ᶠ[𝓝 x] (fun _ : ℝ^m => 0) := by
      filter_upwards [cca.Ω_open.mem_nhds hx] with x'' hx''
      exact asm.u0AtZero x'' (B_subset_D (cca.Ω_subset_B hx''))
    have hFd : fderiv ℝ (fun x'' : ℝ^m => asm.u0 x'' 0) x = 0 := by
      simpa using hzero.fderiv_eq
    rw [hFd]
    simp
  have hfd : fderiv ℝ (fun x' : ℝ^m => u0D1 (x', 0) (dv, 0)) y =
      fderiv ℝ (fun _ : ℝ^m => (0 : ℝ)) y := hfun.fderiv_eq
  simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hfd

/-- Symmetry of the second derivative of `u0Prod`. -/
lemma u0D2_symm (q : ℝ^m × ℝ^n) (v dv : ℝ^m × ℝ^n) :
    u0D2 q v dv = u0D2 q dv v := by
  have hsymm : IsSymmSndFDerivAt ℝ u0Prod q :=
    u0Prod_smooth.contDiffAt.isSymmSndFDerivAt (by simp)
  simpa [u0D2] using hsymm.eq v dv

/-- Second derivative of `u0Prod` at `(y,0)` reduces to the `u0WW` bilinear form. -/
lemma u0D2_at_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (v dv : ℝ^m × ℝ^n) :
    u0D2 (y, 0) v dv =
      ∑ γ : Fin n, ∑ δ : Fin n, u0WW y 0 γ δ * dv.2 δ * v.2 γ := by
  have hsplit : u0D2 (y, 0) v dv =
      u0D2 (y, 0) (v.1, 0) (dv.1, 0) + u0D2 (y, 0) (v.1, 0) (0, dv.2) +
        u0D2 (y, 0) (0, v.2) (dv.1, 0) + u0D2 (y, 0) (0, v.2) (0, dv.2) := by
    calc
      u0D2 (y, 0) v dv = u0D2 (y, 0) ((v.1, 0) + (0, v.2)) dv := by rw [prod_vec_split]
      _ = u0D2 (y, 0) (v.1, 0) dv + u0D2 (y, 0) (0, v.2) dv := by rw [map_add]; rfl
      _ = u0D2 (y, 0) (v.1, 0) ((dv.1, 0) + (0, dv.2)) +
          u0D2 (y, 0) (0, v.2) ((dv.1, 0) + (0, dv.2)) := by rw [prod_vec_split]
      _ = _ := by rw [map_add, map_add]; abel
  rw [hsplit, u0D2_xx_zero y hy, u0D2_cross_zero y hy]
  rw [u0D2_symm (y, 0) (0, v.2) (dv.1, 0), u0D2_cross_zero y hy]
  simp only [zero_add]
  let L : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) :=
    (u0D2 (y, 0)).comp (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n)
  have hL : L v.2 = ∑ γ : Fin n, v.2 γ • L (e γ) := by
    conv_lhs => rw [pi_sum_basis v.2]
    rw [map_sum]
    simp
  calc
    u0D2 (y, 0) (0, v.2) (0, dv.2) = (L v.2) (0, dv.2) := rfl
    _ = (∑ γ : Fin n, v.2 γ • L (e γ)) (0, dv.2) := by rw [hL]
    _ = ∑ γ : Fin n, v.2 γ * (L (e γ)) (0, dv.2) := by
      simp [Finset.sum_apply]
    _ = ∑ γ : Fin n, v.2 γ * (∑ δ : Fin n, dv.2 δ * u0WW y 0 γ δ) := by
      apply Finset.sum_congr rfl
      intro γ _
      have hb := clm_apply_eq_sum_basis (((u0D2 (y, 0)) (0, e γ)).comp
        (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n)) dv.2
      simpa [L, u0WW, u0D2_ww] using congrArg (fun r : ℝ => v.2 γ * r) hb
    _ = ∑ γ : Fin n, ∑ δ : Fin n, u0WW y 0 γ δ * dv.2 δ * v.2 γ := by
      simp [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      apply Finset.sum_congr rfl
      intro δ _
      simp [mul_comm]
      try abel

/-- The derivative of the scalar-valued second derivative of `u0Prod` is the third derivative. -/
lemma u0D3_apply (q : ℝ^m × ℝ^n) (u v dv : ℝ^m × ℝ^n) :
    fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v dv) q u = u0D3 q u v dv := by
  have hc : DifferentiableAt ℝ u0D2 q := u0D2_smooth.differentiable (by simp) q
  have hcv : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v) q :=
    hc.clm_apply (differentiableAt_const (c := v))
  have h₁ := fderiv_clm_apply hcv (differentiableAt_const (c := dv))
  have h₂ : fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v dv) q u =
      fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v) q u dv := by
    simpa using congrArg (fun L : (ℝ^m × ℝ^n) →L[ℝ] ℝ => L u) h₁
  have h₃ := fderiv_clm_apply hc (differentiableAt_const (c := v))
  have h₄ : fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v) q u dv = u0D3 q u v dv := by
    simpa [u0D3] using congrArg
      (fun L : (ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L u dv) h₃
  exact h₂.trans h₄

/-- Symmetry of the first two arguments of the third derivative of `u0Prod`. -/
lemma u0D3_symm_left (q : ℝ^m × ℝ^n) (u v dv : ℝ^m × ℝ^n) :
    u0D3 q u v dv = u0D3 q v u dv := by
  have hsymm : IsSymmSndFDerivAt ℝ u0D1 q :=
    u0D1_smooth.contDiffAt.isSymmSndFDerivAt (by simp)
  have h := hsymm.eq u v
  simpa [u0D3] using congrArg (fun L : (ℝ^m × ℝ^n) →L[ℝ] ℝ => L dv) h

/-- A pure `x` first direction reduces `u0D3` to the `x`-derivative of the remaining derivative. -/
lemma u0D3_fst_apply (x v : ℝ^m) (w : ℝ^n) (v' dv' : ℝ^m × ℝ^n) :
    u0D3 (x, w) (v, 0) v' dv' =
      fderiv ℝ (fun x' : ℝ^m => u0D2 (x', w) v' dv') x v := by
  have hD : DifferentiableAt ℝ u0D2 (x, w) := u0D2_smooth.differentiable (by simp) _
  have hD₁ : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v') (x, w) :=
    hD.clm_apply (differentiableAt_const (c := v'))
  have hF : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v' dv') (x, w) :=
    hD₁.clm_apply (differentiableAt_const (c := dv'))
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hcomp := fderiv_comp' x hF hG
  have hval := congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply] at hval
  rw [hGderiv] at hval
  simp at hval
  have happ := u0D3_apply (x, w) (v, 0) v' dv'
  calc
    u0D3 (x, w) (v, 0) v' dv' =
        fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r v' dv') (x, w) (v, 0) := happ.symm
    _ = (fderiv ℝ (fun x' : ℝ^m => u0D2 (x', w) v' dv') x) v := hval.symm

/-- Symmetry of the last two arguments of the third derivative of `u0Prod`. -/
lemma u0D3_symm_right (q : ℝ^m × ℝ^n) (u v dv : ℝ^m × ℝ^n) :
    u0D3 q u v dv = u0D3 q u dv v := by
  have hfun : (fun r : ℝ^m × ℝ^n => u0D2 r v dv) =
      (fun r : ℝ^m × ℝ^n => u0D2 r dv v) := by
    funext r
    exact u0D2_symm r v dv
  have h := congrArg (fun f : (ℝ^m × ℝ^n) → ℝ => fderiv ℝ f q u) hfun
  simpa [u0D3_apply] using h

/-- Third derivative of `u0Prod` in three pure `w` directions. -/
lemma u0D3_snd_snd_snd (x : ℝ^m) (w v dv dv2 : ℝ^n) :
    u0D3 (x, w) (0, v) (0, dv) (0, dv2) =
      fderiv ℝ (fun w' : ℝ^n =>
        fderiv ℝ (fun w'' : ℝ^n => diff (asm.u0 x) w'' dv2) w' dv) w v := by
  have hD : DifferentiableAt ℝ u0D2 (x, w) := u0D2_smooth.differentiable (by simp) _
  have hD₁ : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r (0, dv)) (x, w) :=
    hD.clm_apply (differentiableAt_const (c := (0, dv)))
  have hF : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r (0, dv) (0, dv2)) (x, w) :=
    hD₁.clm_apply (differentiableAt_const (c := (0, dv2)))
  have hG : DifferentiableAt ℝ (fun w' : ℝ^n => (x, w')) w := by fun_prop
  have hGderiv : fderiv ℝ (fun w' : ℝ^n => (x, w')) w =
      ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_right x w).fderiv
  have hcomp := fderiv_comp' w hF hG
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply] at hval
  rw [hGderiv] at hval
  simp at hval
  have happ := u0D3_apply (x, w) (0, v) (0, dv) (0, dv2)
  have hfun : (fun w' : ℝ^n => u0D2 (x, w') (0, dv) (0, dv2)) =
      (fun w' : ℝ^n => fderiv ℝ (fun w'' : ℝ^n => diff (asm.u0 x) w'' dv2) w' dv) := by
    funext w'
    exact u0D2_snd_snd x w' dv dv2
  calc
    u0D3 (x, w) (0, v) (0, dv) (0, dv2) =
        fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r (0, dv) (0, dv2)) (x, w) (0, v) := happ.symm
    _ = (fderiv ℝ (fun w' : ℝ^n => u0D2 (x, w') (0, dv) (0, dv2)) w) v := hval.symm
    _ = (fderiv ℝ (fun w' : ℝ^n =>
        fderiv ℝ (fun w'' : ℝ^n => diff (asm.u0 x) w'' dv2) w' dv) w) v := by rw [hfun]

/-- Third derivative of `u0Prod` with one pure `x` direction and two pure `w` directions. -/
lemma u0D3_fst_snd_snd (x v : ℝ^m) (w dv dv2 : ℝ^n) :
    u0D3 (x, w) (v, 0) (0, dv) (0, dv2) =
      fderiv ℝ (fun x' : ℝ^m => u0D2 (x', w) (0, dv) (0, dv2)) x v := by
  have hD : DifferentiableAt ℝ u0D2 (x, w) := u0D2_smooth.differentiable (by simp) _
  have hD₁ : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r (0, dv)) (x, w) :=
    hD.clm_apply (differentiableAt_const (c := (0, dv)))
  have hF : DifferentiableAt ℝ (fun r : ℝ^m × ℝ^n => u0D2 r (0, dv) (0, dv2)) (x, w) :=
    hD₁.clm_apply (differentiableAt_const (c := (0, dv2)))
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hcomp := fderiv_comp' x hF hG
  have hval := congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply] at hval
  rw [hGderiv] at hval
  simp at hval
  have happ := u0D3_apply (x, w) (v, 0) (0, dv) (0, dv2)
  calc
    u0D3 (x, w) (v, 0) (0, dv) (0, dv2) =
        fderiv ℝ (fun r : ℝ^m × ℝ^n => u0D2 r (0, dv) (0, dv2)) (x, w) (v, 0) := happ.symm
    _ = (fderiv ℝ (fun x' : ℝ^m => u0D2 (x', w) (0, dv) (0, dv2)) x) v := hval.symm

/-- Expand the first argument of `u0D3` at `(y,0)` in the product basis. -/
lemma u0D3_expand₁ (y : ℝ^m) (u v dv : ℝ^m × ℝ^n) :
    u0D3 (y, 0) u v dv =
      (∑ i : Fin m, u.1 i * u0D3 (y, 0) (ix i) v dv) +
        ∑ δ : Fin n, u.2 δ * u0D3 (y, 0) (iw δ) v dv := by
  let Lx : ℝ^m →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ)) :=
    (u0D3 (y, 0)).comp (ContinuousLinearMap.inl ℝ ℝ^m ℝ^n)
  let Lw : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ)) :=
    (u0D3 (y, 0)).comp (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n)
  have hx : Lx u.1 = ∑ i : Fin m, u.1 i • Lx (e i) := by
    conv_lhs => rw [pi_sum_basis u.1]
    rw [map_sum]
    simp
  have hw : Lw u.2 = ∑ δ : Fin n, u.2 δ • Lw (e δ) := by
    conv_lhs => rw [pi_sum_basis u.2]
    rw [map_sum]
    simp
  calc
    u0D3 (y, 0) u v dv = u0D3 (y, 0) ((u.1, 0) + (0, u.2)) v dv := by rw [prod_vec_split]
    _ = (u0D3 (y, 0) (u.1, 0) + u0D3 (y, 0) (0, u.2)) v dv := by rw [map_add]
    _ = (Lx u.1) v dv + (Lw u.2) v dv := by simp [Lx, Lw]
    _ = (∑ i : Fin m, u.1 i * u0D3 (y, 0) (ix i) v dv) +
        ∑ δ : Fin n, u.2 δ * u0D3 (y, 0) (iw δ) v dv := by
      rw [hx, hw]
      simp [Lx, Lw, ix, iw, Finset.sum_apply]

/-- Expand the second argument of `u0D3` at `(y,0)` in the product basis. -/
lemma u0D3_expand₂ (y : ℝ^m) (u v dv : ℝ^m × ℝ^n) :
    u0D3 (y, 0) u v dv =
      (∑ i : Fin m, v.1 i * u0D3 (y, 0) u (ix i) dv) +
        ∑ ζ : Fin n, v.2 ζ * u0D3 (y, 0) u (iw ζ) dv := by
  let Lx : ℝ^m →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) :=
    (u0D3 (y, 0) u).comp (ContinuousLinearMap.inl ℝ ℝ^m ℝ^n)
  let Lw : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) :=
    (u0D3 (y, 0) u).comp (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n)
  have hx : Lx v.1 = ∑ i : Fin m, v.1 i • Lx (e i) := by
    conv_lhs => rw [pi_sum_basis v.1]
    rw [map_sum]
    simp
  have hw : Lw v.2 = ∑ ζ : Fin n, v.2 ζ • Lw (e ζ) := by
    conv_lhs => rw [pi_sum_basis v.2]
    rw [map_sum]
    simp
  calc
    u0D3 (y, 0) u v dv = u0D3 (y, 0) u ((v.1, 0) + (0, v.2)) dv := by rw [prod_vec_split]
    _ = (u0D3 (y, 0) u (v.1, 0) + u0D3 (y, 0) u (0, v.2)) dv := by rw [map_add]
    _ = (Lx v.1) dv + (Lw v.2) dv := by simp [Lx, Lw]
    _ = (∑ i : Fin m, v.1 i * u0D3 (y, 0) u (ix i) dv) +
        ∑ ζ : Fin n, v.2 ζ * u0D3 (y, 0) u (iw ζ) dv := by
      rw [hx, hw]
      simp [Lx, Lw, ix, iw, Finset.sum_apply]

/-- Expand the third argument of `u0D3` at `(y,0)` in the product basis. -/
lemma u0D3_expand₃ (y : ℝ^m) (u v dv : ℝ^m × ℝ^n) :
    u0D3 (y, 0) u v dv =
      (∑ i : Fin m, dv.1 i * u0D3 (y, 0) u v (ix i)) +
        ∑ η : Fin n, dv.2 η * u0D3 (y, 0) u v (iw η) := by
  let Lx : ℝ^m →L[ℝ] ℝ :=
    ((u0D3 (y, 0) u v).comp (ContinuousLinearMap.inl ℝ ℝ^m ℝ^n))
  let Lw : ℝ^n →L[ℝ] ℝ :=
    ((u0D3 (y, 0) u v).comp (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n))
  have hx : Lx dv.1 = ∑ i : Fin m, dv.1 i • Lx (e i) := by
    conv_lhs => rw [pi_sum_basis dv.1]
    rw [map_sum]
    simp
  have hw : Lw dv.2 = ∑ η : Fin n, dv.2 η • Lw (e η) := by
    conv_lhs => rw [pi_sum_basis dv.2]
    rw [map_sum]
    simp
  calc
    u0D3 (y, 0) u v dv = u0D3 (y, 0) u v ((dv.1, 0) + (0, dv.2)) := by rw [prod_vec_split]
    _ = u0D3 (y, 0) u v (dv.1, 0) + u0D3 (y, 0) u v (0, dv.2) := by rw [map_add]
    _ = Lx dv.1 + Lw dv.2 := by simp [Lx, Lw]
    _ = (∑ i : Fin m, dv.1 i * u0D3 (y, 0) u v (ix i)) +
        ∑ η : Fin n, dv.2 η * u0D3 (y, 0) u v (iw η) := by
      rw [hx, hw]
      simp [Lx, Lw, ix, iw]

/-- Third derivative of `u0Prod` in coordinate `w` directions recovers `u0WWW`. -/
lemma u0D3_www (x : ℝ^m) (w : ℝ^n) (δ ζ η : Fin n) :
    u0D3 (x, w) (iw δ) (iw ζ) (iw η) = u0WWW x w δ ζ η := by
  rw [u0D3_snd_snd_snd]
  have hfun : (fun w' : ℝ^n =>
      fderiv ℝ (fun w'' : ℝ^n => diff (asm.u0 x) w'' (e η)) w' (e ζ)) =
      (fun w' : ℝ^n => diff2 (asm.u0 x) w' (e ζ) (e η)) := by
    funext w'
    have hdiff : DifferentiableAt ℝ (fderiv ℝ (asm.u0 x)) w' :=
      ((u0_x_smooth x).fderiv_right (m := ⊤) (by simp)).differentiable (by simp) w'
    have h := fderiv_clm_apply hdiff (differentiableAt_const (c := e η))
    simpa [diff2] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e ζ)) h
  rw [hfun]
  have hdiff2 : DifferentiableAt ℝ (diff2 (asm.u0 x)) w :=
    ((((u0_x_smooth x).fderiv_right (m := ⊤) (by simp)).fderiv_right
      (m := ⊤) (by simp)).differentiable (by simp) w)
  have hdiffζ : DifferentiableAt ℝ (fun w' : ℝ^n => diff2 (asm.u0 x) w' (e ζ)) w :=
    hdiff2.clm_apply (differentiableAt_const (c := e ζ))
  have hstep₁ : fderiv ℝ (fun w' : ℝ^n => diff2 (asm.u0 x) w' (e ζ) (e η)) w (e δ) =
      fderiv ℝ (fun w' : ℝ^n => diff2 (asm.u0 x) w' (e ζ)) w (e δ) (e η) := by
    simpa using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e δ))
      (fderiv_clm_apply hdiffζ (differentiableAt_const (c := e η)))
  have hstep₂ : fderiv ℝ (fun w' : ℝ^n => diff2 (asm.u0 x) w' (e ζ)) w (e δ) =
      fderiv ℝ (diff2 (asm.u0 x)) w (e δ) (e ζ) := by
    simpa using congrArg (fun L : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) => L (e δ))
      (fderiv_clm_apply hdiff2 (differentiableAt_const (c := e ζ)))
  rw [hstep₁, hstep₂]

/-- Third derivative of `u0Prod` with one `x` direction and two `w` directions recovers `u0XWW`. -/
lemma u0D3_xww (y : ℝ^m) (i : Fin m) (ζ η : Fin n) :
    u0D3 (y, 0) (ix i) (iw ζ) (iw η) = u0XWW y i ζ η := by
  rw [u0D3_fst_snd_snd]
  have hfun : (fun x' : ℝ^m => u0D2 (x', 0) (0, e ζ) (0, e η)) =
      (fun x' : ℝ^m => u0WW x' 0 ζ η) := by
    funext x'
    exact u0D2_ww x' 0 ζ η
  rw [hfun]

/-- Symmetry of the last two indices of `u0XWW`. -/
lemma u0XWW_symm (x : ℝ^m) (i : Fin m) (α β : Fin n) :
    u0XWW x i α β = u0XWW x i β α := by
  have hfun : (fun x' : ℝ^m => u0WW x' 0 α β) =
      (fun x' : ℝ^m => u0WW x' 0 β α) := by
    funext x'
    exact u0WW_symm x' α β
  have h := congrArg (fun f : ℝ^m → ℝ => fderiv ℝ f x (e i)) hfun
  simpa [u0XWW] using h

/-- Mixed third derivative with the `x` direction in the middle reduces to `u0XWW`. -/
lemma u0D3_wxw (y : ℝ^m) (δ : Fin n) (i : Fin m) (η : Fin n) :
    u0D3 (y, 0) (iw δ) (ix i) (iw η) = u0XWW y i δ η := by
  rw [u0D3_symm_left, u0D3_xww]

/-- Mixed third derivative with the `x` direction last reduces to `u0XWW`. -/
lemma u0D3_wwx (y : ℝ^m) (δ ζ : Fin n) (i : Fin m) :
    u0D3 (y, 0) (iw δ) (iw ζ) (ix i) = u0XWW y i δ ζ := by
  rw [u0D3_symm_right, u0D3_symm_left, u0D3_xww, u0XWW_symm]

/-- Third derivative of `u0Prod` at `(y,0)` with one `w` and two `x` directions vanishes. -/
lemma u0D3_wxx_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (δ : Fin n) (i j : Fin m) :
    u0D3 (y, 0) (iw δ) (ix i) (ix j) = 0 := by
  rw [u0D3_symm_left, u0D3_symm_right, u0D3_symm_left, u0D3_fst_apply]
  have hfun : (fun x' : ℝ^m => u0D2 (x', 0) (ix i) (iw δ)) =ᶠ[𝓝 y]
      (fun _ : ℝ^m => (0 : ℝ)) := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
    exact u0D2_cross_zero x hx (e i) (e δ)
  have hfd : fderiv ℝ (fun x' : ℝ^m => u0D2 (x', 0) (ix i) (iw δ)) y =
      fderiv ℝ (fun _ : ℝ^m => (0 : ℝ)) y := hfun.fderiv_eq
  simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L (e j)) hfd

/-- The pure `x` third derivative of `u0Prod` at `(y,0)` vanishes. -/
lemma u0D3_xxx_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (i j k : Fin m) :
    u0D3 (y, 0) (ix i) (ix j) (ix k) = 0 := by
  rw [u0D3_symm_right, u0D3_symm_left, u0D3_fst_apply]
  have hfun : (fun x' : ℝ^m => u0D2 (x', 0) (ix i) (ix j)) =ᶠ[𝓝 y]
      (fun _ : ℝ^m => (0 : ℝ)) := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
    exact u0D2_xx_zero x hx (e i) (e j)
  have hfd : fderiv ℝ (fun x' : ℝ^m => u0D2 (x', 0) (ix i) (ix j)) y =
      fderiv ℝ (fun _ : ℝ^m => (0 : ℝ)) y := hfun.fderiv_eq
  simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L (e k)) hfd

/-- Third derivative at `(y,0)` with two `x` directions then one `w` direction vanishes. -/
lemma u0D3_xxw_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (i j : Fin m) (ζ : Fin n) :
    u0D3 (y, 0) (ix i) (ix j) (iw ζ) = 0 := by
  rw [u0D3_symm_right, u0D3_symm_left]
  exact u0D3_wxx_zero y hy ζ i j

/-- Third derivative at `(y,0)` with `x`, `w`, `x` directions vanishes. -/
lemma u0D3_xwx_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (i : Fin m) (ζ : Fin n) (j : Fin m) :
    u0D3 (y, 0) (ix i) (iw ζ) (ix j) = 0 := by
  rw [u0D3_symm_left]
  exact u0D3_wxx_zero y hy ζ i j

/-- Value of `u0D3` at `(y,0)` with first direction `ix i`. -/
lemma u0D3_ix_at_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (i : Fin m)
    (v dv : ℝ^m × ℝ^n) :
    u0D3 (y, 0) (ix i) v dv =
      ∑ ζ : Fin n, ∑ η : Fin n, u0XWW y i ζ η * v.2 ζ * dv.2 η := by
  rw [u0D3_expand₂ y (ix i) v dv]
  calc
    (∑ j : Fin m, v.1 j * u0D3 (y, 0) (ix i) (ix j) dv) +
        ∑ ζ : Fin n, v.2 ζ * u0D3 (y, 0) (ix i) (iw ζ) dv =
      (∑ j : Fin m, v.1 j *
          ((∑ k : Fin m, dv.1 k * u0D3 (y, 0) (ix i) (ix j) (ix k)) +
            ∑ η : Fin n, dv.2 η * u0D3 (y, 0) (ix i) (ix j) (iw η))) +
        (∑ ζ : Fin n, v.2 ζ *
          ((∑ k : Fin m, dv.1 k * u0D3 (y, 0) (ix i) (iw ζ) (ix k)) +
            ∑ η : Fin n, dv.2 η * u0D3 (y, 0) (ix i) (iw ζ) (iw η))) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j _
              rw [u0D3_expand₃ y (ix i) (ix j) dv]
            · apply Finset.sum_congr rfl
              intro ζ _
              rw [u0D3_expand₃ y (ix i) (iw ζ) dv]
    _ = ∑ ζ : Fin n, ∑ η : Fin n, u0XWW y i ζ η * v.2 ζ * dv.2 η := by
      simp only [u0D3_xxx_zero y hy, u0D3_xxw_zero y hy, u0D3_xwx_zero y hy,
        u0D3_xww, mul_zero]
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      simp [mul_comm, mul_left_comm]
      try abel

/-- Value of `u0D3` at `(y,0)` with first direction `iw δ`. -/
lemma u0D3_iw_at_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (δ : Fin n)
    (v dv : ℝ^m × ℝ^n) :
    u0D3 (y, 0) (iw δ) v dv =
      (∑ j : Fin m, ∑ η : Fin n, u0XWW y j δ η * v.1 j * dv.2 η) +
      (∑ ζ : Fin n, ∑ k : Fin m, u0XWW y k δ ζ * v.2 ζ * dv.1 k) +
      (∑ ζ : Fin n, ∑ η : Fin n, u0WWW y 0 δ ζ η * v.2 ζ * dv.2 η) := by
  rw [u0D3_expand₂ y (iw δ) v dv]
  calc
    (∑ j : Fin m, v.1 j * u0D3 (y, 0) (iw δ) (ix j) dv) +
        ∑ ζ : Fin n, v.2 ζ * u0D3 (y, 0) (iw δ) (iw ζ) dv =
      (∑ j : Fin m, v.1 j *
          ((∑ k : Fin m, dv.1 k * u0D3 (y, 0) (iw δ) (ix j) (ix k)) +
            ∑ η : Fin n, dv.2 η * u0D3 (y, 0) (iw δ) (ix j) (iw η))) +
        (∑ ζ : Fin n, v.2 ζ *
          ((∑ k : Fin m, dv.1 k * u0D3 (y, 0) (iw δ) (iw ζ) (ix k)) +
            ∑ η : Fin n, dv.2 η * u0D3 (y, 0) (iw δ) (iw ζ) (iw η))) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j _
              rw [u0D3_expand₃ y (iw δ) (ix j) dv]
            · apply Finset.sum_congr rfl
              intro ζ _
              rw [u0D3_expand₃ y (iw δ) (iw ζ) dv]
    _ = _ := by
      simp only [u0D3_wxx_zero y hy, u0D3_wxw, u0D3_wwx, u0D3_www,
        mul_zero]
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      simp [mul_comm, mul_left_comm]
      try abel

/-- Full coordinate expansion of `u0D3` at `(y,0)`. -/
lemma u0D3_at_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (u v dv : ℝ^m × ℝ^n) :
    u0D3 (y, 0) u v dv =
      (∑ δ : Fin n, ∑ ζ : Fin n, ∑ η : Fin n,
        u0WWW y 0 δ ζ η * dv.2 η * v.2 ζ * u.2 δ) +
      (∑ i : Fin m, ∑ ζ : Fin n, ∑ η : Fin n,
        u0XWW y i ζ η * u.1 i * v.2 ζ * dv.2 η) +
      (∑ δ : Fin n, ∑ j : Fin m, ∑ η : Fin n,
        u0XWW y j δ η * u.2 δ * v.1 j * dv.2 η) +
      (∑ δ : Fin n, ∑ ζ : Fin n, ∑ k : Fin m,
        u0XWW y k δ ζ * u.2 δ * v.2 ζ * dv.1 k) := by
  rw [u0D3_expand₁ y u v dv]
  simp_rw [u0D3_ix_at_zero y hy, u0D3_iw_at_zero y hy]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp [mul_comm, mul_left_comm]
  try abel

/-- The uncurried first-order coefficient `u1` on the product space. -/
abbrev u1Prod (q : ℝ^m × ℝ^n) : ℝ := asm.u1 q.1 q.2

/-- First derivative of `u1Prod`. -/
abbrev u1D1 (q : ℝ^m × ℝ^n) : (ℝ^m × ℝ^n) →L[ℝ] ℝ := fderiv ℝ u1Prod q

/-- Second derivative of `u1Prod`. -/
abbrev u1D2 (q : ℝ^m × ℝ^n) : (ℝ^m × ℝ^n) →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) := fderiv ℝ u1D1 q

/-- Mixed `x^i w^α` derivative of `u1` at `(x,0)`. -/
abbrev u1XW (x : ℝ^m) (i : Fin m) (α : Fin n) : ℝ :=
  fderiv ℝ (fun x' : ℝ^m => u1W x' 0 (e α)) x (e i)

/-- Smoothness of the product-space version of `u1`. -/
lemma u1Prod_smooth : SmoothGlobal u1Prod := by
  simpa [u1Prod] using asm.u1Smooth

/-- Smoothness of the first derivative of `u1Prod`. -/
lemma u1D1_smooth : SmoothGlobal u1D1 := by
  simpa [u1D1] using u1Prod_smooth.fderiv_right (m := ⊤) (by simp)

/-- The derivative of `u1Prod` in a pure `w` direction is the `w`-derivative of `u1`. -/
lemma u1D1_snd (x : ℝ^m) (w v : ℝ^n) :
    u1D1 (x, w) (0, v) = diff (asm.u1 x) w v := by
  have hG : DifferentiableAt ℝ (fun w' : ℝ^n => (x, w')) w := by fun_prop
  have hU : DifferentiableAt ℝ u1Prod (x, w) := u1Prod_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun w' : ℝ^n => (x, w')) w =
      ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_right x w).fderiv
  have hEq : fderiv ℝ (fun w' : ℝ^n => u1Prod (x, w')) w =
      u1D1 (x, w) ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := by
    simpa [u1D1, hGderiv] using fderiv_comp' w hU hG
  have hSlice : (fun w' : ℝ^n => u1Prod (x, w')) = (fun w' : ℝ^n => asm.u1 x w') := rfl
  rw [hSlice] at hEq
  simpa using (congrArg (fun L : ℝ^n →L[ℝ] ℝ => L v) hEq).symm

/-- The derivative of `u1Prod` in a pure `x` direction is the `x`-derivative at fixed `w`. -/
lemma u1D1_fst (x v : ℝ^m) (w : ℝ^n) :
    u1D1 (x, w) (v, 0) = fderiv ℝ (fun x' : ℝ^m => asm.u1 x' w) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u1Prod (x, w) := u1Prod_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u1Prod (x', w)) x =
      u1D1 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u1D1, hGderiv] using fderiv_comp' x hU hG
  have hSlice : (fun x' : ℝ^m => u1Prod (x', w)) = (fun x' : ℝ^m => asm.u1 x' w) := rfl
  rw [hSlice] at hEq
  simpa using (congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hEq).symm

/-- The first derivative of `u1Prod` splits into pure `x` and `w` parts. -/
lemma u1D1_split (q : ℝ^m × ℝ^n) (v : ℝ^m × ℝ^n) :
    u1D1 q v = u1D1 q (v.1, 0) + u1D1 q (0, v.2) := by
  conv_lhs => rw [← prod_vec_split v]
  rw [map_add]

/-- The pure `x` derivative of `u1Prod` vanishes at `(y,0)` for `y ∈ Ω`. -/
lemma u1D1_fst_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (v : ℝ^m) :
    u1D1 (y, 0) (v, 0) = 0 := by
  rw [u1D1_fst]
  have h : (fun x : ℝ^m => asm.u1 x 0) =ᶠ[𝓝 y] (fun _ : ℝ^m => 0) := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
    exact asm.u1AtZero x (B_subset_D (cca.Ω_subset_B hx))
  have hfd : fderiv ℝ (fun x : ℝ^m => asm.u1 x 0) y =
      fderiv ℝ (fun _ : ℝ^m => (0 : ℝ)) y := h.fderiv_eq
  simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hfd

/-- The first derivative of `u1Prod` at `(y,0)` only has a `w` contribution. -/
lemma u1D1_at_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (v : ℝ^m × ℝ^n) :
    u1D1 (y, 0) v = ∑ α : Fin n, u1W y 0 (e α) * v.2 α := by
  rw [u1D1_split, u1D1_fst_zero y hy, u1D1_snd]
  have h := clm_apply_eq_sum_basis (diff (asm.u1 y) 0) v.2
  simpa [u1W, mul_comm] using h

/-- Second derivative of `u1Prod` in two pure `w` directions. -/
lemma u1D2_snd_snd (x : ℝ^m) (w v dv : ℝ^n) :
    u1D2 (x, w) (0, v) (0, dv) =
      fderiv ℝ (fun w' : ℝ^n => diff (asm.u1 x) w' dv) w v := by
  have hG : DifferentiableAt ℝ (fun w' : ℝ^n => (x, w')) w := by fun_prop
  have hU : DifferentiableAt ℝ u1D1 (x, w) := u1D1_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun w' : ℝ^n => (x, w')) w =
      ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_right x w).fderiv
  have hEq : fderiv ℝ (fun w' : ℝ^n => u1D1 (x, w')) w =
      u1D2 (x, w) ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := by
    simpa [u1D2, hGderiv] using fderiv_comp' w hU hG
  have hfun : (fun w' : ℝ^n => u1D1 (x, w') (0, dv)) =
      (fun w' : ℝ^n => diff (asm.u1 x) w' dv) := by
    funext w'
    exact u1D1_snd x w' dv
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L v (0, dv)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hval
  have hc : DifferentiableAt ℝ (fun w' : ℝ^n => u1D1 (x, w')) w := hU.comp w hG
  have happ := fderiv_clm_apply hc (differentiableAt_const (c := (0, dv)))
  have hval2 : (fderiv ℝ (fun w' : ℝ^n => u1D1 (x, w') (0, dv)) w) v =
      ((fderiv ℝ (fun w' : ℝ^n => u1D1 (x, w')) w) v) (0, dv) := by
    simpa using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L v) happ
  calc
    u1D2 (x, w) (0, v) (0, dv) = ((fderiv ℝ (fun w' : ℝ^n => u1D1 (x, w')) w) v) (0, dv) := hval.symm
    _ = (fderiv ℝ (fun w' : ℝ^n => u1D1 (x, w') (0, dv)) w) v := hval2.symm
    _ = (fderiv ℝ (fun w' : ℝ^n => diff (asm.u1 x) w' dv) w) v := by rw [hfun]

/-- Second derivative of `u1Prod` in coordinate `w` directions recovers `u1WW`. -/
lemma u1D2_ww (x : ℝ^m) (w : ℝ^n) (α β : Fin n) :
    u1D2 (x, w) (iw α) (iw β) = u1WW x w α β := by
  rw [u1D2_snd_snd]
  have hc : DifferentiableAt ℝ (diff (asm.u1 x)) w :=
    ((u1_x_smooth x).fderiv_right (m := ⊤) (by simp)).differentiable (by simp) w
  rw [fderiv_clm_apply hc (differentiableAt_const (c := e β))]
  simp [u1WW, diff2, Matrix.of_apply]

/-- Second derivative of `u1Prod` in an `x` direction then a `w` direction. -/
lemma u1D2_fst_snd (x : ℝ^m) (v : ℝ^m) (w dv : ℝ^n) :
    u1D2 (x, w) (v, 0) (0, dv) =
      fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w) (0, dv)) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u1D1 (x, w) := u1D1_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w)) x =
      u1D2 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u1D2, hGderiv] using fderiv_comp' x hU hG
  have hval := congrArg (fun L : ℝ^m →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L v (0, dv)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at hval
  have hc : DifferentiableAt ℝ (fun x' : ℝ^m => u1D1 (x', w)) x := hU.comp x hG
  have happ := fderiv_clm_apply hc (differentiableAt_const (c := (0, dv)))
  have hval2 : (fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w) (0, dv)) x) v =
      ((fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w)) x) v) (0, dv) := by
    simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) happ
  calc
    u1D2 (x, w) (v, 0) (0, dv) = ((fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w)) x) v) (0, dv) := hval.symm
    _ = (fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w) (0, dv)) x) v := hval2.symm

/-- Second derivative of `u1Prod` in two pure `x` directions. -/
lemma u1D2_fst_fst (x : ℝ^m) (v dv : ℝ^m) (w : ℝ^n) :
    u1D2 (x, w) (v, 0) (dv, 0) =
      fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w) (dv, 0)) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u1D1 (x, w) := u1D1_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w)) x =
      u1D2 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u1D2, hGderiv] using fderiv_comp' x hU hG
  have hval := congrArg (fun L : ℝ^m →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L v (dv, 0)) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at hval
  have hc : DifferentiableAt ℝ (fun x' : ℝ^m => u1D1 (x', w)) x := hU.comp x hG
  have happ := fderiv_clm_apply hc (differentiableAt_const (c := (dv, 0)))
  have hval2 : (fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w) (dv, 0)) x) v =
      ((fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w)) x) v) (dv, 0) := by
    simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) happ
  calc
    u1D2 (x, w) (v, 0) (dv, 0) = ((fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w)) x) v) (dv, 0) := hval.symm
    _ = (fderiv ℝ (fun x' : ℝ^m => u1D1 (x', w) (dv, 0)) x) v := hval2.symm

/-- The pure `x` second derivative of `u1Prod` vanishes at `(y,0)`. -/
lemma u1D2_fst_fst_zero (y : ℝ^m) (hy : y ∈ cca.Ω) (v dv : ℝ^m) :
    u1D2 (y, 0) (v, 0) (dv, 0) = 0 := by
  rw [u1D2_fst_fst]
  have hfun : (fun x : ℝ^m => u1D1 (x, 0) (dv, 0)) =ᶠ[𝓝 y] (fun _ : ℝ^m => 0) := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with x hx
    exact u1D1_fst_zero x hx dv
  have hfd : fderiv ℝ (fun x : ℝ^m => u1D1 (x, 0) (dv, 0)) y =
      fderiv ℝ (fun _ : ℝ^m => (0 : ℝ)) y := hfun.fderiv_eq
  simpa using congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hfd

/-- The mixed `x^i w^α` derivative of `u1Prod` at `(y,0)` in a basis `w` direction. -/
lemma u1D2_fst_snd_basis (y : ℝ^m) (v : ℝ^m) (α : Fin n) :
    u1D2 (y, 0) (v, 0) (0, e α) = ∑ i : Fin m, v i * u1XW y i α := by
  rw [u1D2_fst_snd]
  have hfun : (fun x' : ℝ^m => u1D1 (x', 0) (0, e α)) =
      (fun x' : ℝ^m => u1W x' 0 (e α)) := by
    funext x'
    rw [u1D1_snd]
  rw [hfun]
  have hv : v = ∑ i : Fin m, v i • e i := pi_sum_basis v
  have hL := congrArg (fun w : ℝ^m => (fderiv ℝ (fun x' : ℝ^m => u1W x' 0 (e α)) y) w) hv
  change (fun w : ℝ^m => (fderiv ℝ (fun x' : ℝ^m => u1W x' 0 (e α)) y) w) v = _
  rw [hL]
  change (fderiv ℝ (fun x' : ℝ^m => u1W x' 0 (e α)) y) (∑ i : Fin m, v i • e i) = _
  rw [map_sum]
  simp [u1XW, smul_eq_mul]

/-- The mixed `x` then `w` second derivative of `u1Prod` at `(y,0)`. -/
lemma u1D2_fst_snd_at_zero (y : ℝ^m) (v : ℝ^m) (ζ : ℝ^n) :
    u1D2 (y, 0) (v, 0) (0, ζ) =
      ∑ i : Fin m, ∑ α : Fin n, u1XW y i α * ζ α * v i := by
  have hpair : ((0 : ℝ^m), ζ) = ∑ α : Fin n, ζ α • ((0 : ℝ^m), e α) := by
    apply Prod.ext
    · funext j
      change (0 : ℝ) = (ContinuousLinearMap.fst ℝ ℝ^m ℝ^n
        (∑ α : Fin n, ζ α • ((0 : ℝ^m), e α))) j
      rw [map_sum]
      simp
    · funext j
      change ζ j = (ContinuousLinearMap.snd ℝ ℝ^m ℝ^n
        (∑ α : Fin n, ζ α • ((0 : ℝ^m), e α))) j
      rw [map_sum]
      simp [e, Pi.single_apply]
  calc
    u1D2 (y, 0) (v, 0) (0, ζ) =
        u1D2 (y, 0) (v, 0) (∑ α : Fin n, ζ α • (0, e α)) := by rw [hpair]
    _ = ∑ α : Fin n, ζ α * u1D2 (y, 0) (v, 0) (0, e α) := by
      rw [map_sum]
      simp only [ContinuousLinearMap.map_smulₛₗ, RingHom.id_apply]
      simp [smul_eq_mul]
    _ = ∑ α : Fin n, ζ α * (∑ i : Fin m, v i * u1XW y i α) := by
      apply Finset.sum_congr rfl
      intro α _
      rw [u1D2_fst_snd_basis]
    _ = ∑ i : Fin m, ∑ α : Fin n, u1XW y i α * ζ α * v i := by
      rw [Finset.sum_comm]
      simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- Symmetry of the second derivative of `u1Prod`. -/
lemma u1D2_symm (q : ℝ^m × ℝ^n) (v dv : ℝ^m × ℝ^n) :
    u1D2 q v dv = u1D2 q dv v := by
  have hsymm : IsSymmSndFDerivAt ℝ u1Prod q :=
    u1Prod_smooth.contDiffAt.isSymmSndFDerivAt (by simp)
  simpa [u1D2] using hsymm.eq v dv

/-- The second derivative of `u1Prod` at `(y,0)` in the product basis. -/
lemma u1D2_at_zero (y : ℝ^m) (hy : y ∈ cca.Ω)
    (v dv : ℝ^m × ℝ^n) :
    u1D2 (y, 0) v dv =
      (∑ γ : Fin n, ∑ δ : Fin n, u1WW y 0 γ δ * dv.2 δ * v.2 γ) +
      (∑ i : Fin m, ∑ α : Fin n, u1XW y i α * dv.2 α * v.1 i) +
      (∑ i : Fin m, ∑ α : Fin n, u1XW y i α * v.2 α * dv.1 i) := by
  have hsplit : u1D2 (y, 0) v dv =
      u1D2 (y, 0) (v.1, 0) (dv.1, 0) + u1D2 (y, 0) (v.1, 0) (0, dv.2) +
        u1D2 (y, 0) (0, v.2) (dv.1, 0) + u1D2 (y, 0) (0, v.2) (0, dv.2) := by
    calc
      u1D2 (y, 0) v dv = u1D2 (y, 0) ((v.1, 0) + (0, v.2)) dv := by rw [prod_vec_split]
      _ = u1D2 (y, 0) (v.1, 0) dv + u1D2 (y, 0) (0, v.2) dv := by rw [map_add]; rfl
      _ = u1D2 (y, 0) (v.1, 0) ((dv.1, 0) + (0, dv.2)) +
          u1D2 (y, 0) (0, v.2) ((dv.1, 0) + (0, dv.2)) := by rw [prod_vec_split]
      _ = _ := by rw [map_add, map_add]; abel
  have hpure : u1D2 (y, 0) (0, v.2) (0, dv.2) =
      ∑ γ : Fin n, ∑ δ : Fin n, u1WW y 0 γ δ * dv.2 δ * v.2 γ := by
    let L : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) :=
      (u1D2 (y, 0)).comp (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n)
    have hL : L v.2 = ∑ γ : Fin n, v.2 γ • L (e γ) := by
      conv_lhs => rw [pi_sum_basis v.2]
      rw [map_sum]
      simp
    calc
      u1D2 (y, 0) (0, v.2) (0, dv.2) = (L v.2) (0, dv.2) := rfl
      _ = (∑ γ : Fin n, v.2 γ • L (e γ)) (0, dv.2) := by rw [hL]
      _ = ∑ γ : Fin n, v.2 γ * (L (e γ)) (0, dv.2) := by
        simp [Finset.sum_apply]
      _ = ∑ γ : Fin n, v.2 γ * (∑ δ : Fin n, dv.2 δ * u1WW y 0 γ δ) := by
        apply Finset.sum_congr rfl
        intro γ _
        have hb := clm_apply_eq_sum_basis (((u1D2 (y, 0)) (0, e γ)).comp
          (ContinuousLinearMap.inr ℝ ℝ^m ℝ^n)) dv.2
        simpa [L, u1WW, u1D2_ww] using congrArg (fun r : ℝ => v.2 γ * r) hb
      _ = ∑ γ : Fin n, ∑ δ : Fin n, u1WW y 0 γ δ * dv.2 δ * v.2 γ := by
        simp [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        apply Finset.sum_congr rfl
        intro δ _
        ring
  rw [hsplit, u1D2_fst_fst_zero y hy, u1D2_fst_snd_at_zero y v.1 dv.2,
    u1D2_symm (y, 0) (0, v.2) (dv.1, 0), u1D2_fst_snd_at_zero y dv.1 v.2, hpure]
  abel

/-- The derivative of `u0Prod ∘ G` in the direction `e α`. -/
lemma zD1_comp_at (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n)
    (hG : ContDiffAt ℝ ⊤ G z) (α : Fin n) :
    fderiv ℝ (fun z' : ℝ^n => u0Prod (G z')) z (e α) =
      u0D1 (G z) (fderiv ℝ G z (e α)) := by
  have hU : DifferentiableAt ℝ u0Prod (G z) := u0Prod_smooth.differentiable (by simp) _
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by simp)
  have hcomp := fderiv_comp' z hU hGd
  simpa [u0D1] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hcomp

/-- The mixed derivative of `u0Prod ∘ G`, with the inner direction `e γ` and
the outer direction `e β`. -/
lemma zD2_comp_at (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n)
    (hG : ContDiffAt ℝ ⊤ G z) (β γ : Fin n) :
    fderiv ℝ (fun z' : ℝ^n =>
        fderiv ℝ (fun z'' : ℝ^n => u0Prod (G z'')) z' (e γ)) z (e β) =
      u0D2 (G z) (fderiv ℝ G z (e β)) (fderiv ℝ G z (e γ)) +
      u0D1 (G z) (fderiv ℝ (fun z' : ℝ^n => fderiv ℝ G z' (e γ)) z (e β)) := by
  let Dγ : ℝ^n → ℝ^m × ℝ^n := fun z' => fderiv ℝ G z' (e γ)
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by simp)
  have hfdG : ContDiffAt ℝ ⊤ (fderiv ℝ G) z := hG.fderiv_right (m := ⊤) (by simp)
  have hDγd : DifferentiableAt ℝ Dγ z := by
    exact ((hfdG.clm_apply (contDiffAt_const (c := e γ))).differentiableAt (by simp))
  have hU1d : DifferentiableAt ℝ u0D1 (G z) := u0D1_smooth.differentiable (by simp) _
  have hcd : DifferentiableAt ℝ (fun z' : ℝ^n => u0D1 (G z')) z := hU1d.comp z hGd
  have hT : (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n => u0Prod (G z'')) z' (e γ)) =ᶠ[𝓝 z]
      (fun z' : ℝ^n => u0D1 (G z') (Dγ z')) := by
    filter_upwards [hG.eventually (by simp)] with z' hz'
    exact zD1_comp_at G z' hz' γ
  have hTderiv : fderiv ℝ (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n => u0Prod (G z'')) z' (e γ)) z =
      fderiv ℝ (fun z' : ℝ^n => u0D1 (G z') (Dγ z')) z := hT.fderiv_eq
  rw [hTderiv]
  have happ := fderiv_clm_apply hcd hDγd
  have hcderiv : fderiv ℝ (fun z' : ℝ^n => u0D1 (G z')) z =
      u0D2 (G z) ∘L fderiv ℝ G z := by
    simpa [u0D2] using fderiv_comp' z hU1d hGd
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e β)) happ
  rw [hcderiv] at hval
  simpa only [Dγ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_comm] using hval

/-- The derivative of `u1Prod ∘ G` in the direction `e α`. -/
lemma zD1_u1_comp_at (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n)
    (hG : ContDiffAt ℝ ⊤ G z) (α : Fin n) :
    fderiv ℝ (fun z' : ℝ^n => u1Prod (G z')) z (e α) =
      u1D1 (G z) (fderiv ℝ G z (e α)) := by
  have hU : DifferentiableAt ℝ u1Prod (G z) := u1Prod_smooth.differentiable (by simp) _
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by simp)
  have hcomp := fderiv_comp' z hU hGd
  simpa [u1D1] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hcomp

/-- The mixed derivative of `u1Prod ∘ G`, with the inner direction `e γ` and
the outer direction `e β`. -/
lemma zD2_u1_comp_at (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n)
    (hG : ContDiffAt ℝ ⊤ G z) (β γ : Fin n) :
    fderiv ℝ (fun z' : ℝ^n =>
        fderiv ℝ (fun z'' : ℝ^n => u1Prod (G z'')) z' (e γ)) z (e β) =
      u1D2 (G z) (fderiv ℝ G z (e β)) (fderiv ℝ G z (e γ)) +
      u1D1 (G z) (fderiv ℝ (fun z' : ℝ^n => fderiv ℝ G z' (e γ)) z (e β)) := by
  let Dγ : ℝ^n → ℝ^m × ℝ^n := fun z' => fderiv ℝ G z' (e γ)
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by simp)
  have hfdG : ContDiffAt ℝ ⊤ (fderiv ℝ G) z := hG.fderiv_right (m := ⊤) (by simp)
  have hDγd : DifferentiableAt ℝ Dγ z := by
    exact ((hfdG.clm_apply (contDiffAt_const (c := e γ))).differentiableAt (by simp))
  have hU1d : DifferentiableAt ℝ u1D1 (G z) := u1D1_smooth.differentiable (by simp) _
  have hcd : DifferentiableAt ℝ (fun z' : ℝ^n => u1D1 (G z')) z := hU1d.comp z hGd
  have hT : (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n => u1Prod (G z'')) z' (e γ)) =ᶠ[𝓝 z]
      (fun z' : ℝ^n => u1D1 (G z') (Dγ z')) := by
    filter_upwards [hG.eventually (by simp)] with z' hz'
    exact zD1_u1_comp_at G z' hz' γ
  have hTderiv : fderiv ℝ (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n => u1Prod (G z'')) z' (e γ)) z =
      fderiv ℝ (fun z' : ℝ^n => u1D1 (G z') (Dγ z')) z := hT.fderiv_eq
  rw [hTderiv]
  have happ := fderiv_clm_apply hcd hDγd
  have hcderiv : fderiv ℝ (fun z' : ℝ^n => u1D1 (G z')) z =
      u1D2 (G z) ∘L fderiv ℝ G z := by
    simpa [u1D2] using fderiv_comp' z hU1d hGd
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e β)) happ
  rw [hcderiv] at hval
  simpa only [Dγ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_comm] using hval
/-- The third mixed derivative of `u0Prod ∘ G`, with the innermost direction
`e γ`, middle direction `e β`, and outermost direction `e α`. -/
lemma zD3_comp_at (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n)
    (hG : ContDiffAt ℝ ⊤ G z) (α β γ : Fin n) :
    fderiv ℝ (fun z' : ℝ^n =>
        fderiv ℝ (fun z'' : ℝ^n =>
          fderiv ℝ (fun z''' : ℝ^n => u0Prod (G z''')) z'' (e γ)) z' (e β)) z (e α) =
      u0D1 (G z) (d3G G z α β γ) +
      u0D2 (G z) (dG G z α) (d2G G z β γ) +
      u0D2 (G z) (d2G G z α β) (dG G z γ) +
      u0D2 (G z) (dG G z β) (d2G G z α γ) +
      u0D3 (G z) (dG G z α) (dG G z β) (dG G z γ) := by
  let Dβ : ℝ^n → ℝ^m × ℝ^n := fun z' => fderiv ℝ G z' (e β)
  let Dγ : ℝ^n → ℝ^m × ℝ^n := fun z' => fderiv ℝ G z' (e γ)
  let D2βγ : ℝ^n → ℝ^m × ℝ^n :=
    fun z' => fderiv ℝ (fun z'' : ℝ^n => fderiv ℝ G z'' (e γ)) z' (e β)
  let F1 : ℝ^n → ℝ := fun z' => u0D2 (G z') (Dβ z') (Dγ z')
  let F2 : ℝ^n → ℝ := fun z' => u0D1 (G z') (D2βγ z')
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by simp)
  have hfdG : ContDiffAt ℝ ⊤ (fderiv ℝ G) z := hG.fderiv_right (m := ⊤) (by simp)
  have hDβd : DifferentiableAt ℝ Dβ z := by
    exact ((hfdG.clm_apply (contDiffAt_const (c := e β))).differentiableAt (by simp))
  have hDγd : DifferentiableAt ℝ Dγ z := by
    exact ((hfdG.clm_apply (contDiffAt_const (c := e γ))).differentiableAt (by simp))
  have huγcd : ContDiffAt ℝ ⊤ (fun z' : ℝ^n => fderiv ℝ G z' (e γ)) z :=
    hfdG.clm_apply (contDiffAt_const (c := e γ))
  have hfd_uγ : ContDiffAt ℝ ⊤
      (fderiv ℝ (fun z' : ℝ^n => fderiv ℝ G z' (e γ))) z :=
    huγcd.fderiv_right (m := ⊤) (by simp)
  have hD2βγd : DifferentiableAt ℝ D2βγ z := by
    exact ((hfd_uγ.clm_apply (contDiffAt_const (c := e β))).differentiableAt (by simp))
  have hU2d : DifferentiableAt ℝ u0D2 (G z) := u0D2_smooth.differentiable (by simp) _
  have hc2cd : ContDiffAt ℝ ⊤ (fun z' : ℝ^n => u0D2 (G z')) z := by
    simpa [Function.comp_def] using u0D2_smooth.contDiffAt.comp z hG
  have hc2d : DifferentiableAt ℝ (fun z' : ℝ^n => u0D2 (G z')) z :=
    hc2cd.differentiableAt (by simp)
  have hc2Dβd : DifferentiableAt ℝ (fun z' : ℝ^n => u0D2 (G z') (Dβ z')) z :=
    hc2d.clm_apply hDβd
  have hF1d : DifferentiableAt ℝ F1 z := by
    exact hc2Dβd.clm_apply hDγd
  have hU1d : DifferentiableAt ℝ u0D1 (G z) := u0D1_smooth.differentiable (by simp) _
  have hc1d : DifferentiableAt ℝ (fun z' : ℝ^n => u0D1 (G z')) z := hU1d.comp z hGd
  have hF2d : DifferentiableAt ℝ F2 z := hc1d.clm_apply hD2βγd
  have hT : (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n =>
        fderiv ℝ (fun z''' : ℝ^n => u0Prod (G z''')) z'' (e γ)) z' (e β)) =ᶠ[𝓝 z]
      (fun z' => F1 z' + F2 z') := by
    filter_upwards [hG.eventually (by simp)] with z' hz'
    simpa [F1, F2, Dβ, Dγ, D2βγ] using zD2_comp_at G z' hz' β γ
  rw [hT.fderiv_eq]
  have hc2val (w dv : ℝ^m × ℝ^n) :
      ((fderiv ℝ (fun z' : ℝ^n => u0D2 (G z')) z (e α)) w) dv =
        u0D3 (G z) (fderiv ℝ G z (e α)) w dv := by
    have hUscalar : DifferentiableAt ℝ (fun q : ℝ^m × ℝ^n => u0D2 q w dv) (G z) := by
      have hc : ContDiffAt ℝ ⊤ (fun q : ℝ^m × ℝ^n => u0D2 q w) (G z) :=
        u0D2_smooth.contDiffAt.clm_apply (contDiffAt_const (c := w))
      have hc' : ContDiffAt ℝ ⊤ (fun q : ℝ^m × ℝ^n => u0D2 q w dv) (G z) :=
        hc.clm_apply (contDiffAt_const (c := dv))
      exact hc'.differentiableAt (by simp)
    have hscalar : fderiv ℝ (fun z' : ℝ^n => u0D2 (G z') w dv) z (e α) =
        u0D3 (G z) (fderiv ℝ G z (e α)) w dv := by
      have hcomp := fderiv_comp' z hUscalar hGd
      have hcompval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hcomp
      simp only [ContinuousLinearMap.comp_apply] at hcompval
      rw [u0D3_apply] at hcompval
      exact hcompval
    have happ1 := fderiv_clm_apply hc2d (differentiableAt_const (c := w))
    have hval1 := congrArg
      (fun L : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L (e α) dv) happ1
    have happ2 := fderiv_clm_apply
      (hc2d.clm_apply (differentiableAt_const (c := w))) (differentiableAt_const (c := dv))
    have hval2 := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) happ2
    simp [ContinuousLinearMap.flip_apply] at hval1 hval2
    rw [← hval1, ← hval2]
    exact hscalar
  have hc2val_clm :
      (fderiv ℝ (fun z' : ℝ^n => u0D2 (G z')) z (e α)) (Dβ z) =
        u0D3 (G z) (fderiv ℝ G z (e α)) (Dβ z) := by
    apply ContinuousLinearMap.ext
    intro dv
    exact hc2val (Dβ z) dv
  have hcdβ := fderiv_clm_apply hc2d hDβd
  have hvalβ := congrArg
    (fun L : ℝ^n →L[ℝ] ((ℝ^m × ℝ^n) →L[ℝ] ℝ) => L (e α)) hcdβ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply] at hvalβ
  rw [hc2val_clm] at hvalβ
  have hF1 := fderiv_clm_apply hc2Dβd hDγd
  have hval1 := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hF1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply] at hval1
  rw [hvalβ] at hval1
  have hF1val : fderiv ℝ F1 z (e α) =
      u0D2 (G z) (Dβ z) (fderiv ℝ Dγ z (e α)) +
      u0D2 (G z) (fderiv ℝ Dβ z (e α)) (Dγ z) +
      u0D3 (G z) (fderiv ℝ G z (e α)) (Dβ z) (Dγ z) := by
    simpa [F1, add_assoc] using hval1
  have hc1deriv : fderiv ℝ (fun z' : ℝ^n => u0D1 (G z')) z =
      u0D2 (G z) ∘L fderiv ℝ G z := by
    simpa [u0D2] using fderiv_comp' z hU1d hGd
  have hF2 := fderiv_clm_apply hc1d hD2βγd
  have hval2 := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hF2
  rw [hc1deriv] at hval2
  have hF2val : fderiv ℝ F2 z (e α) =
      u0D1 (G z) (fderiv ℝ D2βγ z (e α)) +
      u0D2 (G z) (fderiv ℝ G z (e α)) (D2βγ z) := by
    simpa [F2] using hval2
  have hsum : fderiv ℝ (fun z' : ℝ^n => F1 z' + F2 z') z =
      fderiv ℝ F1 z + fderiv ℝ F2 z := fderiv_fun_add hF1d hF2d
  rw [hsum]
  simp only [ContinuousLinearMap.add_apply]
  rw [hF1val, hF2val]
  simp only [Dβ, Dγ, D2βγ, dG, d2G, d3G]
  abel

/-- The first derivative of a product of scalar functions. -/
lemma zD1_mul_at (A B : ℝ^n → ℝ) (z : ℝ^n)
    (hA : ContDiffAt ℝ ⊤ A z) (hB : ContDiffAt ℝ ⊤ B z) (α : Fin n) :
    fderiv ℝ (fun z' : ℝ^n => A z' * B z') z (e α) =
      A z * fderiv ℝ B z (e α) + fderiv ℝ A z (e α) * B z := by
  have hAd : DifferentiableAt ℝ A z := hA.differentiableAt (by simp)
  have hBd : DifferentiableAt ℝ B z := hB.differentiableAt (by simp)
  have hmul := fderiv_fun_mul hAd hBd
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hmul
  simpa [smul_eq_mul, mul_comm] using hval

/-- The second mixed `z`-derivative of a product of scalar functions. -/
lemma zD2_mul_at (A B : ℝ^n → ℝ) (z : ℝ^n)
    (hA : ContDiffAt ℝ ⊤ A z) (hB : ContDiffAt ℝ ⊤ B z) (α β : Fin n) :
    fderiv ℝ (fun z' : ℝ^n =>
        fderiv ℝ (fun z'' : ℝ^n => A z'' * B z'') z' (e β)) z (e α) =
      A z * fderiv ℝ (fun z' : ℝ^n => fderiv ℝ B z' (e β)) z (e α) +
      fderiv ℝ A z (e β) * fderiv ℝ B z (e α) +
      fderiv ℝ A z (e α) * fderiv ℝ B z (e β) +
      fderiv ℝ (fun z' : ℝ^n => fderiv ℝ A z' (e β)) z (e α) * B z := by
  have hAev := hA.eventually (by simp)
  have hBev := hB.eventually (by simp)
  have hEq : (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n => A z'' * B z'') z' (e β)) =ᶠ[𝓝 z]
      (fun z' : ℝ^n => A z' * fderiv ℝ B z' (e β) +
        fderiv ℝ A z' (e β) * B z') := by
    filter_upwards [hAev, hBev] with z' hA' hB'
    exact zD1_mul_at A B z' hA' hB' β
  rw [hEq.fderiv_eq]
  have hAd : DifferentiableAt ℝ A z := hA.differentiableAt (by simp)
  have hBd : DifferentiableAt ℝ B z := hB.differentiableAt (by simp)
  have hAβd : DifferentiableAt ℝ (fun z' : ℝ^n => fderiv ℝ A z' (e β)) z := by
    exact ((hA.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hBβd : DifferentiableAt ℝ (fun z' : ℝ^n => fderiv ℝ B z' (e β)) z := by
    exact ((hB.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hp1d : DifferentiableAt ℝ (fun z' : ℝ^n => A z' * fderiv ℝ B z' (e β)) z :=
    hAd.mul hBβd
  have hp2d : DifferentiableAt ℝ (fun z' : ℝ^n => fderiv ℝ A z' (e β) * B z') z :=
    hAβd.mul hBd
  have hsum := fderiv_fun_add hp1d hp2d
  rw [hsum]
  simp only [ContinuousLinearMap.add_apply]
  have hp1 := fderiv_fun_mul hAd hBβd
  have hp2 := fderiv_fun_mul hAβd hBd
  have hp1val := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hp1
  have hp2val := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hp2
  dsimp at hp1val hp2val
  rw [hp1val, hp2val]
  simp [mul_comm]
  try abel

/-- The third derivative of a product when the second factor vanishes to first
order at the base point. -/
lemma zD3_mul_at_of_zero (A B : ℝ^n → ℝ) (hA : ContDiffAt ℝ ⊤ A 0)
    (hB : ContDiffAt ℝ ⊤ B 0) (hB0 : B 0 = 0)
    (hB1 : ∀ δ : Fin n, fderiv ℝ B 0 (e δ) = 0) (α β γ : Fin n) :
    zD3 (fun z : ℝ^n => A z * B z) α β γ =
      A 0 * zD3 B α β γ +
      fderiv ℝ A 0 (e α) * zD2 B β γ +
      fderiv ℝ A 0 (e β) * zD2 B α γ +
      fderiv ℝ A 0 (e γ) * zD2 B α β := by
  let D2B : ℝ^n → ℝ := fun z' =>
    fderiv ℝ (fun z'' : ℝ^n => fderiv ℝ B z'' (e γ)) z' (e β)
  let D2A : ℝ^n → ℝ := fun z' =>
    fderiv ℝ (fun z'' : ℝ^n => fderiv ℝ A z'' (e γ)) z' (e β)
  let Bβ : ℝ^n → ℝ := fun z' => fderiv ℝ B z' (e β)
  let Bγ : ℝ^n → ℝ := fun z' => fderiv ℝ B z' (e γ)
  let Aβ : ℝ^n → ℝ := fun z' => fderiv ℝ A z' (e β)
  let Aγ : ℝ^n → ℝ := fun z' => fderiv ℝ A z' (e γ)
  let T1 : ℝ^n → ℝ := fun z' => A z' * D2B z'
  let T2 : ℝ^n → ℝ := fun z' => Aγ z' * Bβ z'
  let T3 : ℝ^n → ℝ := fun z' => Aβ z' * Bγ z'
  let T4 : ℝ^n → ℝ := fun z' => D2A z' * B z'
  have hAev := hA.eventually (by simp)
  have hBev := hB.eventually (by simp)
  have hEq : (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n =>
        fderiv ℝ (fun z''' : ℝ^n => A z''' * B z''') z'' (e γ)) z' (e β)) =ᶠ[𝓝 0]
      (fun z' => T1 z' + (T2 z' + (T3 z' + T4 z'))) := by
    filter_upwards [hAev, hBev] with z' hA' hB'
    simpa [T1, T2, T3, T4, D2B, D2A, Bβ, Bγ, Aβ, Aγ, add_assoc]
      using zD2_mul_at A B z' hA' hB' β γ
  change fderiv ℝ (fun z' : ℝ^n =>
      fderiv ℝ (fun z'' : ℝ^n =>
        fderiv ℝ (fun z''' : ℝ^n => A z''' * B z''') z'' (e γ)) z' (e β)) 0 (e α) = _
  rw [hEq.fderiv_eq]
  have hAd : DifferentiableAt ℝ A 0 := hA.differentiableAt (by simp)
  have hBd : DifferentiableAt ℝ B 0 := hB.differentiableAt (by simp)
  have hAβd : DifferentiableAt ℝ Aβ 0 := by
    exact ((hA.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hAγd : DifferentiableAt ℝ Aγ 0 := by
    exact ((hA.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e γ))).differentiableAt (by simp)
  have hBβd : DifferentiableAt ℝ Bβ 0 := by
    exact ((hB.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hBγd : DifferentiableAt ℝ Bγ 0 := by
    exact ((hB.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e γ))).differentiableAt (by simp)
  have hBγcd : ContDiffAt ℝ ⊤ (fun z' : ℝ^n => fderiv ℝ B z' (e γ)) 0 :=
    (hB.fderiv_right (m := ⊤) (by simp)).clm_apply (contDiffAt_const (c := e γ))
  have hD2Bd : DifferentiableAt ℝ D2B 0 := by
    exact ((hBγcd.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hAγcd : ContDiffAt ℝ ⊤ (fun z' : ℝ^n => fderiv ℝ A z' (e γ)) 0 :=
    (hA.fderiv_right (m := ⊤) (by simp)).clm_apply (contDiffAt_const (c := e γ))
  have hD2Ad : DifferentiableAt ℝ D2A 0 := by
    exact ((hAγcd.fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hT1d : DifferentiableAt ℝ T1 0 := hAd.mul hD2Bd
  have hT2d : DifferentiableAt ℝ T2 0 := hAγd.mul hBβd
  have hT3d : DifferentiableAt ℝ T3 0 := hAβd.mul hBγd
  have hT4d : DifferentiableAt ℝ T4 0 := hD2Ad.mul hBd
  have hRest : DifferentiableAt ℝ (fun z' : ℝ^n => T2 z' + (T3 z' + T4 z')) 0 :=
    hT2d.add (hT3d.add hT4d)
  have hRest2 : DifferentiableAt ℝ (fun z' : ℝ^n => T3 z' + T4 z') 0 := hT3d.add hT4d
  rw [fderiv_fun_add hT1d hRest]
  simp only [ContinuousLinearMap.add_apply]
  rw [fderiv_fun_add hT2d hRest2, fderiv_fun_add hT3d hT4d]
  simp only [ContinuousLinearMap.add_apply]
  have hp1 := fderiv_fun_mul hAd hD2Bd
  have hp2 := fderiv_fun_mul hAγd hBβd
  have hp3 := fderiv_fun_mul hAβd hBγd
  have hp4 := fderiv_fun_mul hD2Ad hBd
  have hp1v := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hp1
  have hp2v := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hp2
  have hp3v := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hp3
  have hp4v := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hp4
  dsimp at hp1v hp2v hp3v hp4v
  rw [hp1v, hp2v, hp3v, hp4v]
  simp [D2B, D2A, Bβ, Bγ, Aβ, Aγ, zD2, zD3, hB0, hB1, mul_comm]
  try abel

/-- The curried version of φ. -/
abbrev φc (y : ℝ^m) (z : ℝ^n) : ℝ^m := cca.φ (y, z)
/-- The curried version of ψ. -/
abbrev ψc (y : ℝ^m) (z : ℝ^n) : ℝ^n := cca.ψ (y, z)
/-- The curried version of Υ. -/
abbrev Υc (y : ℝ^m) (z : ℝ^n) : ℝ := cca.Υ (y, z)
/-- The coordinate-change map `z ↦ (φ(y,z), ψ(y,z))`. -/
abbrev coordG (y : ℝ^m) (z : ℝ^n) : ℝ^m × ℝ^n := (φc y z, ψc y z)
/-- The `u0` factor of `v0` after the coordinate change. -/
abbrev v0B (y : ℝ^m) (z : ℝ^n) : ℝ := u0Prod (coordG y z)

/-- Smoothness at `z=0` of the `z`-slice of `φ` at fixed `y`. -/
lemma phi_z_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (φc y) 0 := by
  have hopen : IsOpen (cca.Ω ×ˢ (B (d := n) cca.r1)) :=
    cca.Ω_open.prod (isOpen_B (d := n) cca.r1)
  have hmem : (y, (0 : ℝ^n)) ∈ cca.Ω ×ˢ (B (d := n) cca.r1) := by
    refine ⟨hy, ?_⟩
    simpa [B, BrendleHung.Section2.Multivar.norm] using cca.r1_pos
  have hφat : ContDiffAt ℝ ⊤ cca.φ (y, 0) :=
    cca.φ_smooth.contDiffAt (hopen.mem_nhds hmem)
  have hslice : Smooth (fun z : ℝ^n => (y, z)) on (Set.univ : Set ℝ^n) :=
    (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) y).contDiffOn
  simpa [φc, Function.comp_def] using hφat.comp 0 (hslice.contDiffAt (by simp))

/-- Smoothness at `z=0` of the `z`-slice of `Υ` at fixed `y`. -/
lemma upsilon_z_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (Υc y) 0 := by
  have hopen : IsOpen (cca.Ω ×ˢ (B (d := n) cca.r1)) :=
    cca.Ω_open.prod (isOpen_B (d := n) cca.r1)
  have hmem : (y, (0 : ℝ^n)) ∈ cca.Ω ×ˢ (B (d := n) cca.r1) := by
    refine ⟨hy, ?_⟩
    simpa [B, BrendleHung.Section2.Multivar.norm] using cca.r1_pos
  have hΥat : ContDiffAt ℝ ⊤ cca.Υ (y, 0) :=
    cca.Υ_smooth.contDiffAt (hopen.mem_nhds hmem)
  have hslice : Smooth (fun z : ℝ^n => (y, z)) on (Set.univ : Set ℝ^n) :=
    (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) y).contDiffOn
  simpa [Υc, Function.comp_def] using hΥat.comp 0 (hslice.contDiffAt (by simp))

/-- Smoothness at `z=0` of the coordinate-change map `coordG y`. -/
lemma coordG_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (coordG y) 0 := by
  simpa [coordG, ψc] using (phi_z_smoothAt y hy).prodMk (CoordChangeAssumptions.psi_z_smoothAt y hy)

/-- Smoothness at `z=0` of the `u0` factor `v0B y`. -/
lemma v0B_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (v0B y) 0 := by
  simpa [v0B, Function.comp_def] using u0Prod_smooth.contDiffAt.comp 0 (coordG_smoothAt y hy)

/-- The coordinate-change map sends `z=0` to `(y,0)`. -/
lemma coordG_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : coordG y 0 = (y, (0 : ℝ^n)) := by
  ext <;> simp [φc, ψc, cca.φ_y_0 y hy, cca.ψ_y_0 y hy]

/-- The factor `v0B y` vanishes at `z=0`. -/
lemma v0B_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : v0B y 0 = 0 := by
  rw [v0B, coordG_zero y hy]
  exact asm.u0AtZero y (B_subset_D (cca.Ω_subset_B hy))

/-- The first `z`-derivative of `v0B y` vanishes at zero. -/
lemma zD1_v0B (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) : zD1 (v0B y) α = 0 := by
  calc
    zD1 (v0B y) α = u0D1 (coordG y 0) (dG (coordG y) 0 α) := by
      simpa [v0B, zD1] using zD1_comp_at (coordG y) 0 (coordG_smoothAt y hy) α
    _ = 0 := by
      rw [coordG_zero y hy, u0D1_zero y hy]
      simp

/-- The second `z`-derivative of `v0B y` reduces to the `u0D2` term at zero. -/
lemma zD2_v0B (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (v0B y) α β =
      u0D2 (y, 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) := by
  calc
    zD2 (v0B y) α β =
        u0D2 (coordG y 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) +
        u0D1 (coordG y 0) (d2G (coordG y) 0 α β) := by
          simpa [v0B, zD2, d2G] using zD2_comp_at (coordG y) 0 (coordG_smoothAt y hy) α β
    _ = u0D2 (y, 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) := by
      rw [coordG_zero y hy, u0D1_zero y hy]
      simp

/-- The third `z`-derivative of `v0B y` reduces to second and third `u0` derivatives at zero. -/
lemma zD3_v0B (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    zD3 (v0B y) α β γ =
      u0D2 (y, 0) (dG (coordG y) 0 α) (d2G (coordG y) 0 β γ) +
      u0D2 (y, 0) (d2G (coordG y) 0 α β) (dG (coordG y) 0 γ) +
      u0D2 (y, 0) (dG (coordG y) 0 β) (d2G (coordG y) 0 α γ) +
      u0D3 (y, 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) (dG (coordG y) 0 γ) := by
  calc
    zD3 (v0B y) α β γ =
        u0D1 (coordG y 0) (d3G (coordG y) 0 α β γ) +
        u0D2 (coordG y 0) (dG (coordG y) 0 α) (d2G (coordG y) 0 β γ) +
        u0D2 (coordG y 0) (d2G (coordG y) 0 α β) (dG (coordG y) 0 γ) +
        u0D2 (coordG y 0) (dG (coordG y) 0 β) (d2G (coordG y) 0 α γ) +
        u0D3 (coordG y 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) (dG (coordG y) 0 γ) := by
          simpa [v0B, zD3] using zD3_comp_at (coordG y) 0 (coordG_smoothAt y hy) α β γ
    _ = _ := by
      rw [coordG_zero y hy, u0D1_zero y hy]
      simp

/-- First component of the first `z`-derivative of `coordG`. -/
lemma dG_coordG_fst (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    (dG (coordG y) 0 α).1 = fderiv ℝ (φc y) 0 (e α) := by
  have hφd := (phi_z_smoothAt y hy).differentiableAt (by simp)
  have hψd := (CoordChangeAssumptions.psi_z_smoothAt y hy).differentiableAt (by simp)
  have hprod : fderiv ℝ (coordG y) 0 =
      (fderiv ℝ (φc y) 0).prod (fderiv ℝ (ψc y) 0) := by
    simpa [coordG] using hφd.fderiv_prodMk hψd
  have hval := congrArg (fun L : ℝ^n →L[ℝ] (ℝ^m × ℝ^n) => L (e α)) hprod
  simpa [dG] using congrArg Prod.fst hval

/-- Second component of the first `z`-derivative of `coordG`. -/
lemma dG_coordG_snd (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    (dG (coordG y) 0 α).2 = fderiv ℝ (ψc y) 0 (e α) := by
  have hφd := (phi_z_smoothAt y hy).differentiableAt (by simp)
  have hψd := (CoordChangeAssumptions.psi_z_smoothAt y hy).differentiableAt (by simp)
  have hprod : fderiv ℝ (coordG y) 0 =
      (fderiv ℝ (φc y) 0).prod (fderiv ℝ (ψc y) 0) := by
    simpa [coordG] using hφd.fderiv_prodMk hψd
  have hval := congrArg (fun L : ℝ^n →L[ℝ] (ℝ^m × ℝ^n) => L (e α)) hprod
  simpa [dG] using congrArg Prod.snd hval

/-- Second component of the mixed second `z`-derivative of `coordG`. -/
lemma d2G_coordG_snd (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    (d2G (coordG y) 0 α β).2 =
      fderiv ℝ (fun z' : ℝ^n => fderiv ℝ (ψc y) z' (e β)) 0 (e α) := by
  have hφev := (phi_z_smoothAt y hy).eventually (by simp)
  have hψev := (CoordChangeAssumptions.psi_z_smoothAt y hy).eventually (by simp)
  have hEq : (fun z : ℝ^n => dG (coordG y) z β) =ᶠ[𝓝 0]
      (fun z : ℝ^n => (fderiv ℝ (φc y) z (e β), fderiv ℝ (ψc y) z (e β))) := by
    filter_upwards [hφev, hψev] with z hφ hψ
    have hφd := hφ.differentiableAt (by simp)
    have hψd := hψ.differentiableAt (by simp)
    have hprod := hφd.fderiv_prodMk hψd
    simpa [dG, coordG] using congrArg (fun L : ℝ^n →L[ℝ] (ℝ^m × ℝ^n) => L (e β)) hprod
  have hφβd : DifferentiableAt ℝ (fun z : ℝ^n => fderiv ℝ (φc y) z (e β)) 0 := by
    exact (((phi_z_smoothAt y hy).fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hψβd : DifferentiableAt ℝ (fun z : ℝ^n => fderiv ℝ (ψc y) z (e β)) 0 := by
    exact (((CoordChangeAssumptions.psi_z_smoothAt y hy).fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiffAt_const (c := e β))).differentiableAt (by simp)
  have hprod2 : fderiv ℝ (fun z : ℝ^n =>
      (fderiv ℝ (φc y) z (e β), fderiv ℝ (ψc y) z (e β))) 0 =
      (fderiv ℝ (fun z : ℝ^n => fderiv ℝ (φc y) z (e β)) 0).prod
        (fderiv ℝ (fun z : ℝ^n => fderiv ℝ (ψc y) z (e β)) 0) :=
    hφβd.fderiv_prodMk hψβd
  have hval := congrArg (fun L : ℝ^n →L[ℝ] (ℝ^m × ℝ^n) => L (e α)) (hEq.fderiv_eq.trans hprod2)
  simpa [d2G] using congrArg Prod.snd hval

/-- Express `zD2` as the second Fréchet derivative of `F`. -/
lemma zD2_eq_fderiv_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ^n → E) (hF : ContDiffAt ℝ ⊤ F 0) (α β : Fin n) :
    zD2 F α β = (fderiv ℝ (fderiv ℝ F) 0 (e α)) (e β) := by
  have hfdF : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)
  have happ := fderiv_clm_apply hfdF (differentiableAt_const (c := e β))
  simpa [zD2] using congrArg (fun L : ℝ^n →L[ℝ] E => L (e α)) happ

/-- Symmetry of `zD2` for a smooth `F`. -/
lemma zD2_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ^n → E) (hF : ContDiffAt ℝ ⊤ F 0) (α β : Fin n) :
    zD2 F α β = zD2 F β α := by
  rw [zD2_eq_fderiv_fderiv F hF α β, zD2_eq_fderiv_fderiv F hF β α]
  exact (hF.isSymmSndFDerivAt (by simp)).eq (e α) (e β)

/-- Second-derivative contribution with one `dG` direction and one `d2G` direction. -/
lemma u0D2_dG_d2G (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    u0D2 (y, 0) (dG (coordG y) 0 α) (d2G (coordG y) 0 β γ) =
      ∑ δ : Fin n, ∑ ζ : Fin n,
        u0WW y 0 δ ζ * zD1 (ψc y) α δ * zD2 (ψc y) β γ ζ := by
  rw [u0D2_at_zero y hy]
  simp_rw [dG_coordG_snd y hy, d2G_coordG_snd y hy]
  simp [zD1, zD2, mul_comm, mul_left_comm, mul_assoc]

/-- Second-derivative contribution with `d2G` followed by `dG`. -/
lemma u0D2_d2G_dG (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    u0D2 (y, 0) (d2G (coordG y) 0 α β) (dG (coordG y) 0 γ) =
      ∑ δ : Fin n, ∑ ζ : Fin n,
        u0WW y 0 δ ζ * zD1 (ψc y) γ δ * zD2 (ψc y) α β ζ := by
  rw [u0D2_at_zero y hy]
  simp_rw [dG_coordG_snd y hy, d2G_coordG_snd y hy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro ζ _
  rw [u0WW_symm y ζ δ]

/-- Symmetrized second-derivative contribution used in the third-derivative formula. -/
lemma u0D2_dG_d2G_symm (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    u0D2 (y, 0) (dG (coordG y) 0 β) (d2G (coordG y) 0 α γ) =
      ∑ δ : Fin n, ∑ ζ : Fin n,
        u0WW y 0 δ ζ * zD1 (ψc y) β δ * zD2 (ψc y) γ α ζ := by
  rw [u0D2_dG_d2G y hy β α γ]
  have hψ : ContDiffAt ℝ ⊤ (ψc y) 0 := by
    simpa [ψc] using CoordChangeAssumptions.psi_z_smoothAt y hy
  simp_rw [zD2_symm (ψc y) hψ α γ]

/-- Reindex the `x`-derivative term with the middle direction as `φ`. -/
lemma u0D3_X_middle_expand (y : ℝ^m) (α β γ : Fin n) :
    (∑ δ : Fin n, ∑ j : Fin m, ∑ η : Fin n,
      u0XWW y j δ η * zD1 (ψc y) α δ * zD1 (φc y) β j *
        zD1 (ψc y) γ η) =
    (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
      u0XWW y i δ ζ * zD1 (φc y) β i * zD1 (ψc y) γ δ *
        zD1 (ψc y) α ζ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro ζ _
  rw [u0XWW_symm y j ζ δ]
  ring

/-- Reindex the `x`-derivative term with the last direction as `φ`. -/
lemma u0D3_X_last_expand (y : ℝ^m) (α β γ : Fin n) :
    (∑ δ : Fin n, ∑ ζ : Fin n, ∑ k : Fin m,
      u0XWW y k δ ζ * zD1 (ψc y) α δ * zD1 (ψc y) β ζ *
        zD1 (φc y) γ k) =
    (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
      u0XWW y i δ ζ * zD1 (φc y) γ i * zD1 (ψc y) α δ *
        zD1 (ψc y) β ζ) := by
  calc
    (∑ δ : Fin n, ∑ ζ : Fin n, ∑ k : Fin m,
      u0XWW y k δ ζ * zD1 (ψc y) α δ * zD1 (ψc y) β ζ *
        zD1 (φc y) γ k) =
        ∑ δ : Fin n, ∑ k : Fin m, ∑ ζ : Fin n,
          u0XWW y k δ ζ * zD1 (ψc y) α δ * zD1 (ψc y) β ζ *
            zD1 (φc y) γ k := by
          apply Finset.sum_congr rfl
          intro δ _
          rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
          u0XWW y k δ ζ * zD1 (ψc y) α δ * zD1 (ψc y) β ζ *
            zD1 (φc y) γ k := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
          u0XWW y i δ ζ * zD1 (φc y) γ i * zD1 (ψc y) α δ *
            zD1 (ψc y) β ζ := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro δ _
          apply Finset.sum_congr rfl
          intro ζ _
          ring

set_option maxHeartbeats 2000000 in
/-- Third `z`-derivative contribution from three first derivatives of `coordG`. -/
lemma u0D3_dG_dG_dG (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    u0D3 (y, 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) (dG (coordG y) 0 γ) =
      (∑ δ : Fin n, ∑ ζ : Fin n, ∑ η : Fin n,
        u0WWW y 0 δ ζ η * zD1 (ψc y) α δ *
          zD1 (ψc y) β ζ * zD1 (ψc y) γ η) +
      (∑ i : Fin m, ∑ ζ : Fin n, ∑ η : Fin n,
        u0XWW y i ζ η * zD1 (φc y) α i *
          zD1 (ψc y) β ζ * zD1 (ψc y) γ η) +
      (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
        u0XWW y i δ ζ * zD1 (φc y) β i *
          zD1 (ψc y) γ δ * zD1 (ψc y) α ζ) +
      (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
        u0XWW y i δ ζ * zD1 (φc y) γ i *
          zD1 (ψc y) α δ * zD1 (ψc y) β ζ) := by
  rw [u0D3_at_zero y hy]
  simp_rw [dG_coordG_fst y hy, dG_coordG_snd y hy]
  rw [u0D3_X_middle_expand y α β γ, u0D3_X_last_expand y α β γ]
  simp [zD1, mul_comm, mul_left_comm, mul_assoc]

/-- Coordinate expansion of the second `z`-derivative of `v0B`. -/
lemma zD2_v0B_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (v0B y) α β =
      ∑ γ : Fin n, ∑ δ : Fin n,
        u0WW y 0 γ δ * zD1 (ψc y) α γ * zD1 (ψc y) β δ := by
  rw [zD2_v0B y hy α β, u0D2_at_zero y hy]
  simp_rw [dG_coordG_snd y hy]
  simp [zD1, mul_comm, mul_left_comm]

/-- Second `z`-derivative of the product `Υ * v0B` at zero. -/
lemma zD2_v0_prod (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (ccd.v0 y) α β = Υc y 0 * zD2 (v0B y) α β := by
  change zD2 (fun z : ℝ^n => Υc y z * v0B y z) α β = _
  have h := zD2_mul_at (Υc y) (v0B y) 0
    (upsilon_z_smoothAt y hy) (v0B_smoothAt y hy) α β
  simpa [zD1, zD2, v0B_zero y hy, zD1_v0B y hy] using h

/-- Coordinate expansion of the third `z`-derivative of `v0B`. -/
lemma zD3_v0B_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    zD3 (v0B y) α β γ =
      (∑ δ : Fin n, ∑ ζ : Fin n,
        u0WW y 0 δ ζ * zD1 (ψc y) α δ * zD2 (ψc y) β γ ζ) +
      (∑ δ : Fin n, ∑ ζ : Fin n,
        u0WW y 0 δ ζ * zD1 (ψc y) γ δ * zD2 (ψc y) α β ζ) +
      (∑ δ : Fin n, ∑ ζ : Fin n,
        u0WW y 0 δ ζ * zD1 (ψc y) β δ * zD2 (ψc y) γ α ζ) +
      (∑ δ : Fin n, ∑ ζ : Fin n, ∑ η : Fin n,
        u0WWW y 0 δ ζ η * zD1 (ψc y) α δ *
          zD1 (ψc y) β ζ * zD1 (ψc y) γ η) +
      (∑ i : Fin m, ∑ ζ : Fin n, ∑ η : Fin n,
        u0XWW y i ζ η * zD1 (φc y) α i *
          zD1 (ψc y) β ζ * zD1 (ψc y) γ η) +
      (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
        u0XWW y i δ ζ * zD1 (φc y) β i *
          zD1 (ψc y) γ δ * zD1 (ψc y) α ζ) +
      (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
        u0XWW y i δ ζ * zD1 (φc y) γ i *
          zD1 (ψc y) α δ * zD1 (ψc y) β ζ) := by
  rw [zD3_v0B y hy α β γ]
  rw [u0D2_dG_d2G y hy α β γ, u0D2_d2G_dG y hy α β γ,
    u0D2_dG_d2G_symm y hy α β γ, u0D3_dG_dG_dG y hy α β γ]
  abel

/-- Third `z`-derivative of the product `Υ * v0B` at zero. -/
lemma zD3_v0_prod (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    zD3 (ccd.v0 y) α β γ =
      Υc y 0 * zD3 (v0B y) α β γ +
      zD1 (Υc y) α * zD2 (v0B y) β γ +
      zD1 (Υc y) β * zD2 (v0B y) α γ +
      zD1 (Υc y) γ * zD2 (v0B y) α β := by
  change zD3 (fun z : ℝ^n => Υc y z * v0B y z) α β γ = _
  have hB1 : ∀ δ : Fin n, fderiv ℝ (v0B y) 0 (e δ) = 0 := by
    intro δ
    simpa [zD1] using zD1_v0B y hy δ
  have h := zD3_mul_at_of_zero (Υc y) (v0B y)
    (upsilon_z_smoothAt y hy) (v0B_smoothAt y hy)
    (v0B_zero y hy) hB1 α β γ
  simpa [zD1, zD2] using h

/-- The `u1` factor of `v1` after the coordinate change. -/
abbrev u1B (y : ℝ^m) (z : ℝ^n) : ℝ := u1Prod (coordG y z)

/-- Smoothness at `z=0` of the `u1` factor `u1B y`. -/
lemma u1B_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (u1B y) 0 := by
  simpa [u1B, Function.comp_def] using
    u1Prod_smooth.contDiffAt.comp 0 (coordG_smoothAt y hy)

/-- The factor `u1B y` vanishes at `z=0`. -/
lemma u1B_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : u1B y 0 = 0 := by
  rw [u1B, coordG_zero y hy]
  exact asm.u1AtZero y (B_subset_D (cca.Ω_subset_B hy))

/-- The first `z`-derivative of `u1B y` at zero. -/
lemma zD1_u1B (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (u1B y) α = u1D1 (y, 0) (dG (coordG y) 0 α) := by
  calc
    zD1 (u1B y) α = u1D1 (coordG y 0) (dG (coordG y) 0 α) := by
      simpa [u1B, zD1] using zD1_u1_comp_at (coordG y) 0 (coordG_smoothAt y hy) α
    _ = u1D1 (y, 0) (dG (coordG y) 0 α) := by rw [coordG_zero y hy]

/-- The second `z`-derivative of `u1B y` at zero. -/
lemma zD2_u1B (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (u1B y) α β =
      u1D2 (y, 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) +
      u1D1 (y, 0) (d2G (coordG y) 0 α β) := by
  calc
    zD2 (u1B y) α β =
        u1D2 (coordG y 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) +
        u1D1 (coordG y 0) (d2G (coordG y) 0 α β) := by
          simpa [u1B, zD2, d2G] using
            zD2_u1_comp_at (coordG y) 0 (coordG_smoothAt y hy) α β
    _ = _ := by rw [coordG_zero y hy]

/-- The first `z`-derivative of `u1B` in the coordinate basis. -/
lemma zD1_u1B_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (u1B y) α = ∑ γ : Fin n, u1W y 0 (e γ) * zD1 (ψc y) α γ := by
  rw [zD1_u1B y hy α, u1D1_at_zero y hy]
  simp [zD1, dG_coordG_snd y hy]

/-- The second-derivative `u1D2` contribution from two first `z`-derivatives of `coordG`. -/
lemma u1D2_dG_dG_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    u1D2 (y, 0) (dG (coordG y) 0 α) (dG (coordG y) 0 β) =
      (∑ γ : Fin n, ∑ δ : Fin n,
        u1WW y 0 γ δ * zD1 (ψc y) α γ * zD1 (ψc y) β δ) +
      (∑ i : Fin m, ∑ γ : Fin n,
        u1XW y i γ * zD1 (ψc y) β γ * zD1 (φc y) α i) +
      (∑ i : Fin m, ∑ γ : Fin n,
        u1XW y i γ * zD1 (ψc y) α γ * zD1 (φc y) β i) := by
  rw [u1D2_at_zero y hy]
  simp_rw [dG_coordG_fst y hy, dG_coordG_snd y hy]
  simp [zD1, mul_comm, mul_left_comm]

/-- The first-derivative contribution from the second `z`-derivative of `coordG`. -/
lemma u1D1_d2G_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    u1D1 (y, 0) (d2G (coordG y) 0 α β) =
      ∑ γ : Fin n, u1W y 0 (e γ) * zD2 (ψc y) α β γ := by
  rw [u1D1_at_zero y hy]
  simp [zD2, d2G_coordG_snd y hy]

/-- The second `z`-derivative of `u1B` in the coordinate basis. -/
lemma zD2_u1B_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (u1B y) α β =
      (∑ γ : Fin n, ∑ δ : Fin n,
        u1WW y 0 γ δ * zD1 (ψc y) α γ * zD1 (ψc y) β δ) +
      (∑ i : Fin m, ∑ γ : Fin n,
        u1XW y i γ * zD1 (ψc y) β γ * zD1 (φc y) α i) +
      (∑ i : Fin m, ∑ γ : Fin n,
        u1XW y i γ * zD1 (ψc y) α γ * zD1 (φc y) β i) +
      (∑ γ : Fin n, u1W y 0 (e γ) * zD2 (ψc y) α β γ) := by
  rw [zD2_u1B y hy α β, u1D2_dG_dG_expanded y hy α β, u1D1_d2G_expanded y hy α β]

/-- Product-rule formula for the first `z`-derivative of `v1`. -/
lemma zD1_v1_prod (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (ccd.v1 y) α =
      Υc y 0 * zD1 (u1B y) α + zD1 (Υc y) α * u1B y 0 := by
  change zD1 (fun z : ℝ^n => Υc y z * u1B y z) α = _
  simpa [zD1] using zD1_mul_at (Υc y) (u1B y) 0
    (upsilon_z_smoothAt y hy) (u1B_smoothAt y hy) α

/-- Product-rule formula for the second `z`-derivative of `v1`. -/
lemma zD2_v1_prod (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (ccd.v1 y) α β =
      Υc y 0 * zD2 (u1B y) α β +
      zD1 (Υc y) β * zD1 (u1B y) α +
      zD1 (Υc y) α * zD1 (u1B y) β := by
  change zD2 (fun z : ℝ^n => Υc y z * u1B y z) α β = _
  have h := zD2_mul_at (Υc y) (u1B y) 0
    (upsilon_z_smoothAt y hy) (u1B_smoothAt y hy) α β
  simpa [zD1, zD2, u1B_zero y hy] using h

/-- The uncurried second-order coefficient `u2` on the product space. -/
abbrev u2Prod (q : ℝ^m × ℝ^n) : ℝ := asm.u2 q.1 q.2

/-- First derivative of `u2Prod`. -/
abbrev u2D1 (q : ℝ^m × ℝ^n) : (ℝ^m × ℝ^n) →L[ℝ] ℝ := fderiv ℝ u2Prod q

/-- The coordinate `x^i` derivative of `u2` at fixed `w = 0`. -/
abbrev u2X (x : ℝ^m) (i : Fin m) : ℝ :=
  fderiv ℝ (fun x' : ℝ^m => asm.u2 x' 0) x (e i)

/-- Smoothness of the product-space version of `u2`. -/
lemma u2Prod_smooth : SmoothGlobal u2Prod := by
  simpa [u2Prod] using asm.u2Smooth

/-- The derivative of `u2Prod` in a pure `w` direction is the `w`-derivative of `u2`. -/
lemma u2D1_snd (x : ℝ^m) (w v : ℝ^n) :
    u2D1 (x, w) (0, v) = diff (asm.u2 x) w v := by
  have hG : DifferentiableAt ℝ (fun w' : ℝ^n => (x, w')) w := by fun_prop
  have hU : DifferentiableAt ℝ u2Prod (x, w) := u2Prod_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun w' : ℝ^n => (x, w')) w =
      ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_right x w).fderiv
  have hEq : fderiv ℝ (fun w' : ℝ^n => u2Prod (x, w')) w =
      u2D1 (x, w) ∘L ContinuousLinearMap.inr ℝ ℝ^m ℝ^n := by
    simpa [u2D1, hGderiv] using fderiv_comp' w hU hG
  have hSlice : (fun w' : ℝ^n => u2Prod (x, w')) = (fun w' : ℝ^n => asm.u2 x w') := rfl
  rw [hSlice] at hEq
  simpa using (congrArg (fun L : ℝ^n →L[ℝ] ℝ => L v) hEq).symm

/-- The derivative of `u2Prod` in a pure `x` direction is the fixed-`w` derivative of `u2`. -/
lemma u2D1_fst (x v : ℝ^m) (w : ℝ^n) :
    u2D1 (x, w) (v, 0) = fderiv ℝ (fun x' : ℝ^m => asm.u2 x' w) x v := by
  have hG : DifferentiableAt ℝ (fun x' : ℝ^m => (x', w)) x := by fun_prop
  have hU : DifferentiableAt ℝ u2Prod (x, w) := u2Prod_smooth.differentiable (by simp) _
  have hGderiv : fderiv ℝ (fun x' : ℝ^m => (x', w)) x =
      ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := (hasFDerivAt_prodMk_left x w).fderiv
  have hEq : fderiv ℝ (fun x' : ℝ^m => u2Prod (x', w)) x =
      u2D1 (x, w) ∘L ContinuousLinearMap.inl ℝ ℝ^m ℝ^n := by
    simpa [u2D1, hGderiv] using fderiv_comp' x hU hG
  have hSlice : (fun x' : ℝ^m => u2Prod (x', w)) = (fun x' : ℝ^m => asm.u2 x' w) := rfl
  rw [hSlice] at hEq
  simpa using (congrArg (fun L : ℝ^m →L[ℝ] ℝ => L v) hEq).symm

/-- The first derivative of `u2Prod` splits into pure `x` and `w` parts. -/
lemma u2D1_split (q : ℝ^m × ℝ^n) (v : ℝ^m × ℝ^n) :
    u2D1 q v = u2D1 q (v.1, 0) + u2D1 q (0, v.2) := by
  conv_lhs => rw [← prod_vec_split v]
  rw [map_add]

/-- The first derivative of `u2Prod` at `(y,0)` has an `x` and a `w` contribution. -/
lemma u2D1_at_zero (y : ℝ^m) (v : ℝ^m × ℝ^n) :
    u2D1 (y, 0) v =
      (∑ β : Fin n, u2W y 0 (e β) * v.2 β) +
        fderiv ℝ (fun x' : ℝ^m => asm.u2 x' 0) y v.1 := by
  calc
    u2D1 (y, 0) v = u2D1 (y, 0) (v.1, 0) + u2D1 (y, 0) (0, v.2) :=
      u2D1_split (y, 0) v
    _ = fderiv ℝ (fun x' : ℝ^m => asm.u2 x' 0) y v.1
          + diff (asm.u2 y) 0 v.2 := by rw [u2D1_fst, u2D1_snd]
    _ = (∑ β : Fin n, u2W y 0 (e β) * v.2 β) +
          fderiv ℝ (fun x' : ℝ^m => asm.u2 x' 0) y v.1 := by
      have h := clm_apply_eq_sum_basis (diff (asm.u2 y) 0) v.2
      have hsum : (∑ β : Fin n, u2W y 0 (e β) * v.2 β) =
          diff (asm.u2 y) 0 v.2 := by
        simpa [u2W, mul_comm] using h.symm
      rw [hsum]
      ring

/-- Expand a continuous linear functional on `ℝ^m` in the standard basis. -/
lemma clm_apply_eq_sum_basis_m (L : ℝ^m →L[ℝ] ℝ) (v : ℝ^m) :
    L v = ∑ i : Fin m, v i * L (e i) := by
  have hv : v = ∑ i : Fin m, v i • e i := pi_sum_basis v
  rw [hv]
  simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ, map_sum, map_smul,
    smul_eq_mul]

/-- Expand a derivative of `u2(·,0)` in the standard basis of `ℝ^m`. -/
lemma u2X_sum_basis (y : ℝ^m) (v : ℝ^m) :
    fderiv ℝ (fun x' : ℝ^m => asm.u2 x' 0) y v =
      ∑ i : Fin m, u2X y i * v i := by
  have h := clm_apply_eq_sum_basis_m (fderiv ℝ (fun x' : ℝ^m => asm.u2 x' 0) y) v
  simpa [u2X, mul_comm] using h

/-- The derivative of `u2Prod ∘ G` in the direction `e α`. -/
lemma zD1_u2_comp_at (G : ℝ^n → ℝ^m × ℝ^n) (z : ℝ^n)
    (hG : ContDiffAt ℝ ⊤ G z) (α : Fin n) :
    fderiv ℝ (fun z' : ℝ^n => u2Prod (G z')) z (e α) =
      u2D1 (G z) (fderiv ℝ G z (e α)) := by
  have hU : DifferentiableAt ℝ u2Prod (G z) := u2Prod_smooth.differentiable (by simp) _
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by simp)
  have hcomp := fderiv_comp' z hU hGd
  simpa [u2D1] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hcomp

/-- The `u2` factor of `v2` after the coordinate change. -/
abbrev u2B (y : ℝ^m) (z : ℝ^n) : ℝ := u2Prod (coordG y z)

/-- Smoothness at `z=0` of the `u2` factor `u2B y`. -/
lemma u2B_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ (u2B y) 0 := by
  simpa [u2B, Function.comp_def] using
    u2Prod_smooth.contDiffAt.comp 0 (coordG_smoothAt y hy)

/-- The factor `u2B y` specializes to `u2(y,0)` at `z=0`. -/
lemma u2B_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : u2B y 0 = asm.u2 y 0 := by
  rw [u2B, coordG_zero y hy]

/-- The first `z`-derivative of `u2B y` at zero. -/
lemma zD1_u2B (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (u2B y) α = u2D1 (y, 0) (dG (coordG y) 0 α) := by
  calc
    zD1 (u2B y) α = u2D1 (coordG y 0) (dG (coordG y) 0 α) := by
      simpa [u2B, zD1] using zD1_u2_comp_at (coordG y) 0 (coordG_smoothAt y hy) α
    _ = u2D1 (y, 0) (dG (coordG y) 0 α) := by rw [coordG_zero y hy]

/-- The first `z`-derivative of `u2B` in the coordinate basis. -/
lemma zD1_u2B_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (u2B y) α =
      (∑ β : Fin n, u2W y 0 (e β) * zD1 (ψc y) α β) +
      (∑ i : Fin m, u2X y i * zD1 (φc y) α i) := by
  rw [zD1_u2B y hy α, u2D1_at_zero y (dG (coordG y) 0 α),
    u2X_sum_basis y (dG (coordG y) 0 α).1]
  simp_rw [dG_coordG_fst y hy, dG_coordG_snd y hy]

/-- Product-rule formula for the first `z`-derivative of `v2`. -/
lemma zD1_v2_prod (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (ccd.v2 y) α =
      Υc y 0 * zD1 (u2B y) α + zD1 (Υc y) α * u2B y 0 := by
  change zD1 (fun z : ℝ^n => Υc y z * u2B y z) α = _
  simpa [zD1] using zD1_mul_at (Υc y) (u2B y) 0
    (upsilon_z_smoothAt y hy) (u2B_smoothAt y hy) α

/-- The Hessian matrix of `v0` in the `z` variables at zero. -/
abbrev v0Hessian (y : ℝ^m) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun α β => zD2 (ccd.v0 y) α β

/-- Coordinate expansion of the second `z`-derivative of `v0` at zero. -/
lemma zD2_v0_expanded (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (ccd.v0 y) α β =
      ∑ γ : Fin n, ∑ δ : Fin n,
        Υc y 0 * u0WW y 0 γ δ *
          zD1 (ψc y) α γ * zD1 (ψc y) β δ := by
  rw [zD2_v0_prod y hy α β, zD2_v0B_expanded y hy α β]
  simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- Smoothness in `y` of one entry of the `z`-Jacobian of `ψ` at `z=0`. -/
lemma psi_z_entry_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) (β α : Fin n) :
    ContDiffAt ℝ ⊤ (fun y' : ℝ^m => zJacobian cca.ψ y' β α) y := by
  have hopen : IsOpen (cca.Ω ×ˢ (B (d := n) cca.r1)) :=
    cca.Ω_open.prod (isOpen_B (d := n) cca.r1)
  have hmem : (y, (0 : ℝ^n)) ∈ cca.Ω ×ˢ (B (d := n) cca.r1) := by
    refine ⟨hy, ?_⟩
    simpa [B, BrendleHung.Section2.Multivar.norm] using cca.r1_pos
  have hψat : ContDiffAt ℝ ⊤ cca.ψ (y, 0) :=
    cca.ψ_smooth.contDiffAt (hopen.mem_nhds hmem)
  have hcoord : ContDiffAt ℝ ⊤ (fun q : ℝ^m × ℝ^n => cca.ψ q β) (y, 0) :=
    (contDiffAt_apply (𝕜 := ℝ) (E := ℝ) (n := ⊤) β (cca.ψ (y, 0))).comp (y, 0) hψat
  have hcurried : ContDiffAt ℝ ⊤
      (Function.uncurry (fun y' : ℝ^m => fun z : ℝ^n => cca.ψ (y', z) β)) (y, 0) := by
    simpa [Function.uncurry_def] using hcoord
  have hfd : ContDiffAt ℝ ⊤
      (fun y' : ℝ^m => fderiv ℝ (fun z : ℝ^n => cca.ψ (y', z) β) (0 : ℝ^n)) y := by
    exact ContDiffAt.fderiv (f := fun y' : ℝ^m => fun z : ℝ^n => cca.ψ (y', z) β)
      hcurried (g := fun _ : ℝ^m => (0 : ℝ^n)) contDiffAt_const (by simp)
  simpa [zJacobian] using hfd.clm_apply (contDiffAt_const (c := e α))

/-- The `z`-Jacobian entry of `ψ` agrees with the coordinate of its `zD1`. -/
lemma zJacobian_psi_apply (y : ℝ^m) (hy : y ∈ cca.Ω) (β α : Fin n) :
    zJacobian cca.ψ y β α = zD1 (ψc y) α β := by
  have hψd : DifferentiableAt ℝ (ψc y) 0 :=
    (CoordChangeAssumptions.psi_z_smoothAt y hy).differentiableAt (by simp)
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := (0 : ℝ^n))
    (f := ψc y) (g := fun v : ℝ^n => v β)
    ((contDiffAt_apply (𝕜 := ℝ) (E := ℝ) (n := ⊤) β (ψc y 0)).differentiableAt (by simp)) hψd
  have hcoordFd : fderiv ℝ (fun v : ℝ^n => v β) (ψc y 0) =
      ContinuousLinearMap.proj β :=
    (hasFDerivAt_apply (𝕜 := ℝ) β (ψc y 0)).fderiv
  have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hcomp
  rw [hcoordFd] at hval
  simpa [zJacobian, ψc, zD1, Function.comp_def, ContinuousLinearMap.proj_apply] using hval

/-- The `z`-Jacobian of `ψ` as a continuous linear map. -/
noncomputable abbrev psiJacLin (y : ℝ^m) : ℝ^n →L[ℝ] ℝ^n :=
  (Matrix.toLin' (zJacobian cca.ψ y)).toContinuousLinearMap

/-- Smoothness in `y` of the `z`-Jacobian of `ψ` at `z=0`. -/
lemma psiJacLin_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ContDiffAt ℝ ⊤ psiJacLin y := by
  have hOn : ContDiffOn ℝ ⊤ psiJacLin cca.Ω := by
    rw [contDiffOn_clm_apply]
    intro z y' hy'
    have hentry (β α : Fin n) : ContDiffWithinAt ℝ ⊤
        (fun y'' : ℝ^m => zJacobian cca.ψ y'' β α) cca.Ω y' :=
      (psi_z_entry_smoothAt y' hy' β α).contDiffWithinAt
    have hsum : ContDiffWithinAt ℝ ⊤
        (fun y'' : ℝ^m => fun β : Fin n =>
          ∑ α : Fin n, zJacobian cca.ψ y'' β α * z α) cca.Ω y' := by
      rw [contDiffWithinAt_pi]
      intro β
      exact ContDiffWithinAt.sum (s := Finset.univ) (fun α _ =>
        (hentry β α).mul contDiffWithinAt_const)
    simpa [psiJacLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hsum
  exact hOn.contDiffAt (cca.Ω_open.mem_nhds hy)

/-- The `z`-Jacobian of `ψ` is invertible on `Ω`. -/
lemma psiJac_isInvertible (y : ℝ^m) (hy : y ∈ cca.Ω) :
    (psiJacLin y).IsInvertible := by
  classical
  have hunitMat : IsUnit (zJacobian cca.ψ y) := cca.ψ_jacobian_inv y hy
  have hunitDet : IsUnit (zJacobian cca.ψ y).det :=
    (Matrix.isUnit_iff_isUnit_det (zJacobian cca.ψ y)).mp hunitMat
  let eLin : ℝ^n ≃ₗ[ℝ] ℝ^n :=
    (zJacobian cca.ψ y).toLinearEquiv (Pi.basisFun ℝ (Fin n)) hunitDet
  refine ⟨eLin.toContinuousLinearEquiv, ?_⟩
  ext v i
  simp [psiJacLin, eLin, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

/-- The Jacobian characterization of `bar z`, used as an intermediate result. -/
noncomputable def barzViaPsi (y : ℝ^m) : ℝ^n := (psiJacLin y).inverse (bud.barw y)

/-- Smoothness of the Jacobian characterization of `bar z` on `Ω`. -/
lemma barzViaPsi_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) : ContDiffAt ℝ ⊤ barzViaPsi y := by
  have hInv : ContDiffAt ℝ ⊤ (fun y' : ℝ^m => (psiJacLin y').inverse) y :=
    (psiJac_isInvertible y hy).contDiffAt_map_inverse.comp y (psiJacLin_smoothAt y hy)
  have hVec : ContDiffAt ℝ ⊤ (fun y' : ℝ^m => bud.barw y') y :=
    barw_contDiffAt y (B_subset_D (cca.Ω_subset_B hy))
  simpa [barzViaPsi] using hInv.clm_apply hVec

/-- The Jacobian relation for the intermediate vector. -/
lemma barzViaPsi_spec (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    ∑ β : Fin n, zD1 (ψc y) β α * barzViaPsi y β = bud.barw y α := by
  have hlin := (psiJac_isInvertible y hy).self_apply_inverse (bud.barw y)
  have h := congrFun hlin α
  simpa [barzViaPsi, psiJacLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    zJacobian_psi_apply y hy] using h

/-- The Hessian of `v0` is the positive `Υ(y,0)` multiple of a congruence of the positive Hessian of `u0`. -/
lemma v0Hessian_eq (y : ℝ^m) (hy : y ∈ cca.Ω) :
    v0Hessian y = Υc y 0 • ((zJacobian cca.ψ y)ᴴ * u0WW y 0 * zJacobian cca.ψ y) := by
  ext α β
  change zD2 (ccd.v0 y) α β =
    Υc y 0 * ((zJacobian cca.ψ y)ᴴ * u0WW y 0 * zJacobian cca.ψ y) α β
  rw [zD2_v0_expanded y hy α β]
  have hR : Υc y 0 * ((zJacobian cca.ψ y)ᴴ * u0WW y 0 * zJacobian cca.ψ y) α β =
      ∑ δ : Fin n, ∑ γ : Fin n,
        Υc y 0 * u0WW y 0 γ δ * zD1 (ψc y) α γ * zD1 (ψc y) β δ := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro δ _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    rw [zJacobian_psi_apply y hy γ α, zJacobian_psi_apply y hy δ β]
    ring
  conv_lhs => rw [Finset.sum_comm]
  exact hR.symm

/-- The Hessian of `v0` in the `z` variables is positive definite. -/
lemma v0Hessian_posDef (y : ℝ^m) (hy : y ∈ cca.Ω) : (v0Hessian y).PosDef := by
  classical
  have hz : (0 : ℝ^n) ∈ B (d := n) cca.r1 := by
    simpa [B, BrendleHung.Section2.Multivar.norm] using cca.r1_pos
  have hΥpos : 0 < Υc y 0 := cca.Υ_pos y 0 hy hz
  have hJunit : IsUnit (zJacobian cca.ψ y) := cca.ψ_jacobian_inv y hy
  have hJinj : Function.Injective (zJacobian cca.ψ y).mulVec :=
    Matrix.mulVec_injective_of_isUnit hJunit
  have hcong : ((zJacobian cca.ψ y)ᴴ * u0WW y 0 * zJacobian cca.ψ y).PosDef :=
    (u0WWAtZero y (B_subset_D (cca.Ω_subset_B hy))).conjTranspose_mul_mul_same hJinj
  have hscaled : (Υc y 0 • ((zJacobian cca.ψ y)ᴴ * u0WW y 0 * zJacobian cca.ψ y)).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (hcong.isHermitian.smul (IsSelfAdjoint.of_nonneg hΥpos.le)) ?_
    intro x hx
    simpa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using
      mul_pos hΥpos (hcong.dotProduct_mulVec_pos hx)
  rw [v0Hessian_eq y hy]
  exact hscaled

/-- Swap the last two summations of a triple finite sum. -/
lemma sum_swap₃ (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ β : Fin n, ∑ γ : Fin n, ∑ δ : Fin n, f β γ δ) =
      ∑ γ : Fin n, ∑ δ : Fin n, ∑ β : Fin n, f β γ δ := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]

/-- The defining equation for the Jacobian characterization of `bar z`. -/
lemma barzViaPsi_defining_equation (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    ∑ β : Fin n, zD2 (ccd.v0 y) α β * barzViaPsi y β = - zD1 (ccd.v1 y) α := by
  classical
  have hbarw := barw_spec y (B_subset_D (cca.Ω_subset_B hy))
  have hrow (γ : Fin n) : ∑ δ : Fin n, u0WW y 0 γ δ * bud.barw y δ =
      - u1W y 0 (e γ) := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hbarw γ
  calc
    ∑ β : Fin n, zD2 (ccd.v0 y) α β * barzViaPsi y β
        = ∑ β : Fin n, (∑ γ : Fin n, ∑ δ : Fin n,
            Υc y 0 * u0WW y 0 γ δ *
              zD1 (ψc y) α γ * zD1 (ψc y) β δ) * barzViaPsi y β := by
          simp_rw [zD2_v0_expanded y hy α]
    _ = ∑ γ : Fin n, ∑ δ : Fin n,
          (Υc y 0 * u0WW y 0 γ δ * zD1 (ψc y) α γ) *
            (∑ β : Fin n, zD1 (ψc y) β δ * barzViaPsi y β) := by
          simp_rw [Finset.sum_mul]
          rw [sum_swap₃]
          apply Finset.sum_congr rfl
          intro γ _
          apply Finset.sum_congr rfl
          intro δ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro β _
          ring
    _ = ∑ γ : Fin n, ∑ δ : Fin n,
          (Υc y 0 * u0WW y 0 γ δ * zD1 (ψc y) α γ) * bud.barw y δ := by
          simp_rw [barzViaPsi_spec y hy]
    _ = ∑ γ : Fin n, Υc y 0 * zD1 (ψc y) α γ *
          (∑ δ : Fin n, u0WW y 0 γ δ * bud.barw y δ) := by
          apply Finset.sum_congr rfl
          intro γ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro δ _
          ring
    _ = ∑ γ : Fin n, Υc y 0 * zD1 (ψc y) α γ * (- u1W y 0 (e γ)) := by
          simp_rw [hrow]
    _ = -(∑ γ : Fin n, Υc y 0 * u1W y 0 (e γ) * zD1 (ψc y) α γ) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro γ _
          ring
    _ = - zD1 (ccd.v1 y) α := by
          rw [zD1_v1_prod y hy α, u1B_zero y hy, zD1_u1B_expanded y hy α]
          simp [Finset.mul_sum, mul_assoc, mul_comm]

/-- The Hessian of `v0` as a continuous linear map. -/
noncomputable abbrev v0HessianLin (y : ℝ^m) : ℝ^n →L[ℝ] ℝ^n :=
  (Matrix.toLin' (v0Hessian y)).toContinuousLinearMap

/-- The `z`-gradient of `v1` at zero as a vector. -/
abbrev v1GradVec (y : ℝ^m) : ℝ^n := fun α : Fin n => zD1 (ccd.v1 y) α

/-- The `v0` Hessian is invertible on `Ω`. -/
lemma v0HessianLin_isInvertible (y : ℝ^m) (hy : y ∈ cca.Ω) :
    (v0HessianLin y).IsInvertible := by
  classical
  have hunitMat : IsUnit (v0Hessian y) := (v0Hessian_posDef y hy).isUnit
  have hunitDet : IsUnit (v0Hessian y).det :=
    (Matrix.isUnit_iff_isUnit_det (v0Hessian y)).mp hunitMat
  let eLin : ℝ^n ≃ₗ[ℝ] ℝ^n :=
    (v0Hessian y).toLinearEquiv (Pi.basisFun ℝ (Fin n)) hunitDet
  refine ⟨eLin.toContinuousLinearEquiv, ?_⟩
  ext v i
  simp [v0HessianLin, eLin, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

/-- The reduced `z`-direction as defined in the paper. -/
noncomputable def barz (y : ℝ^m) : ℝ^n := (v0HessianLin y).inverse (-v1GradVec y)

/-- The paper's `bar z` agrees with the Jacobian characterization on `Ω`. -/
lemma barz_eq_barzViaPsi (y : ℝ^m) (hy : y ∈ cca.Ω) : barz y = barzViaPsi y := by
  have hinv := v0HessianLin_isInvertible y hy
  have hvec : v0HessianLin y (barzViaPsi y) = -v1GradVec y := by
    ext α
    simpa [v0HessianLin, v1GradVec, v0Hessian, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct] using barzViaPsi_defining_equation y hy α
  simpa [barz] using hinv.inverse_apply_eq.mpr hvec.symm

/-- Smoothness of the paper's `bar z` on `Ω`. -/
lemma barz_smoothAt (y : ℝ^m) (hy : y ∈ cca.Ω) : ContDiffAt ℝ ⊤ barz y := by
  have hEq : barz =ᶠ[𝓝 y] barzViaPsi := by
    filter_upwards [cca.Ω_open.mem_nhds hy] with y' hy'
    exact barz_eq_barzViaPsi y' hy'
  exact (barzViaPsi_smoothAt y hy).congr_of_eventuallyEq hEq

/-- The defining equation for the paper's `bar z`. -/
lemma barz_defining_equation (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    ∑ β : Fin n, zD2 (ccd.v0 y) α β * barz y β = - zD1 (ccd.v1 y) α := by
  rw [barz_eq_barzViaPsi y hy]
  exact barzViaPsi_defining_equation y hy α

/-- The relation `J barz = barw` in coordinates. -/
lemma barz_spec (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    ∑ β : Fin n, zD1 (ψc y) β α * barz y β = bud.barw y α := by
  rw [barz_eq_barzViaPsi y hy]
  exact barzViaPsi_spec y hy α

end

end Section2
