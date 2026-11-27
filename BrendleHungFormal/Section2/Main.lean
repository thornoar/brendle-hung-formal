import BrendleHungFormal.Section2.Multivar
import BrendleHungFormal.Section2.TaylorAsymptotics
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

/-- Fixed radii, smooth model functions, and asymptotic coefficients from Section 2. -/
structure InitialData where
  r0 : ℝ
  s0 : ℝ
  u : ℝ^m -> ℝ^n -> ℝ -> ℝ
  u0 : ℝ^m -> ℝ^n -> ℝ
  u1 : ℝ^m -> ℝ^n -> ℝ
  u2 : ℝ^m -> ℝ^n -> ℝ
  u3 : ℝ^m -> ℝ^n -> ℝ

/-- An arbitrary choice of the Section 2 initial data. -/
axiom data : InitialData

/-- Hypotheses on the data: positivity, smoothness, normalization, a quadratic lower bound, and a smooth third-order expansion. -/
structure InitialAssumptions where
  hr0 : data.r0 > 0
  hs0 : data.s0 > 0
  σ : ℝ
  hσ : σ > 0
  u0Smooth : Smooth (↓data.u0)
  uSmooth : Smooth (fun (x, w, s) => data.u x w s)
  u0AtZero : ∀ x : ℝ^m, x ∈ D r0 -> data.u0 x 0 = 0
  u0Quadratic :
    ∀ x : ℝ^m, ∀ w : ℝ^n,
      x ∈ D r0 →
      w ∈ D r0 →
      data.u0 x w ≥ σ * (norm w ^ 2)
  u1Smooth : Smooth (↓data.u1)
  u1AtZero : ∀ x : ℝ^m, x ∈ D data.r0 -> data.u1 x 0 = 0
  u2Smooth : Smooth (↓data.u2)
  u3Smooth : Smooth (↓data.u3)
  uExp : HasSmoothExpansion3 (D r0 ×ˢ D r0) s0
          (↓data.u0) (↓data.u1) (↓data.u2) (↓data.u3)
          (↓data.u)

/-- An arbitrary choice of the Section 2 hypotheses. -/
axiom asm : InitialAssumptions

/-- The closed coordinate ball used as the domain for parameters and `w` variables. -/
abbrev inBounds {m : ℕ} (x : ℝ^m) : Prop
:= x ∈ D data.r0

noncomputable section

/-- Derivative of `u0(x, ·)` at `w`, as a continuous linear functional. -/
abbrev u0W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (data.u0 x) w

/-- Derivative of `u1(x, ·)` at `w`, as a continuous linear functional. -/
abbrev u1W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (data.u1 x) w

/-- Derivative of `u2(x, ·)` at `w`, as a continuous linear functional. -/
abbrev u2W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (data.u2 x) w

/-- Hessian matrix of `u0(x, ·)` at `w` in the standard basis. -/
abbrev u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (data.u0 x) w (e i) (e j)

/-- Hessian matrix of `u1(x, ·)` at `w` in the standard basis. -/
abbrev u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (data.u1 x) w (e i) (e j)

/-- Third derivative tensor component of `u0(x, ·)` at `w` in the standard basis. -/
abbrev u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ
:= diff3 (data.u0 x) w (e i) (e j) (e k)

end

/-- The derivative of `u0(x, ·)` vanishes at `w = 0`, by the quadratic lower bound. -/
lemma u0WAtZero (x : ℝ^m) (hx : inBounds x) : u0W x 0 = 0
:= by
  have hAtZero : data.u0 x 0 = 0 := asm.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ B data.r0 →
      data.u0 x w ≥ asm.σ * (norm w ^ 2) := by
    intro w hw
    exact asm.u0Quadratic x w hx (B_subset_D hw)
  have hderiv := ineq_zero_deriv (data.u0 x) data.r0 asm.hr0 asm.σ asm.hσ hAtZero hquad
  ext w
  simpa [u0W] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L w) hderiv

/-- The Hessian of `u0(x, ·)` at `w = 0` is positive definite. -/
lemma u0WWAtZero (x : ℝ^m) (hx : inBounds x) : Matrix.PosDef (u0WW x 0)
:= by
  have hAtZero : data.u0 x 0 = 0 := asm.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ B data.r0 →
      data.u0 x w ≥ asm.σ * (norm w ^ 2) := by
    intro w hw
    exact asm.u0Quadratic x w hx (B_subset_D hw)
  have hsmooth : Smooth (data.u0 x) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))
  simpa [u0WW, matrixOf] using
    (ineq_pos_def (data.u0 x) data.r0 asm.hr0 asm.σ asm.hσ
      hsmooth hAtZero hquad)

/-- Bundle holding the reduced function `U`, its direction `barw`, and its second- and third-order coefficients. -/
structure BigUData where
  U : ℝ^m -> ℝ -> ℝ
  barw : ℝ^m -> ℝ^n
  U2 : ℝ^m -> ℝ
  U3 : ℝ^m -> ℝ

-- The following four definitions correspond to the objects introduced in
-- Section 2 of the paper: U(x,s), \bar w(x), U^{(2)}(x), and U^{(3)}(x).

noncomputable def bud : BigUData :=
  let barw x := (u0WW x 0)⁻¹ *ᵥ (fun α : Fin n => - u1W x 0 (e α))
  {
    U x s := ⨅ w : D (d := n) data.r0, data.u x w s
    barw := barw
    U2 x := data.u2 x 0 + ((1 : ℝ) / 2) * ∑ α : Fin n, u1W x 0 (e α) * barw x α
    U3 x :=
      data.u3 x 0
       + ∑ α : Fin n, u2W x 0 (e α) * barw x α
       + ((1 : ℝ) / 2) * ∑ α : Fin n, ∑ β : Fin n,
           u1WW x 0 α β * barw x α * barw x β
       + ((1 : ℝ) / 6) * ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
           u0WWW x 0 α β γ * barw x α * barw x β * barw x γ
  }

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
    data.u x w 0 = data.u0 x w
:= by
  rcases asm.uExp with ⟨ρ, hρSmooth, hρ⟩
  have hseg0 : (0 : ℝ) ∈ BrendleHung.Section2.Multivar.segment data.s0 := by
    change |(0 : ℝ)| ≤ data.s0
    simpa using (le_of_lt asm.hs0)
  have hp : (x, w) ∈ D data.r0 ×ˢ D data.r0 := ⟨hx, hw⟩
  simpa using hρ (x, w) 0 hp hseg0

-- Differentiating the expansion assumption in the `s` variable at `s = 0`.
lemma hasDerivAt_u_s (x : ℝ^m) (hx : inBounds x) (w : ℝ^n) (hw : inBounds w) :
    HasDerivAt (data.u x w) (data.u1 x w) 0 := by
  rcases asm.uExp with ⟨ρ, hρSmooth, hρ⟩
  have hseg : ∀ᶠ s : ℝ in 𝓝 0, s ∈ segment data.s0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) asm.hs0] with s hs
    change |s| ≤ data.s0
    simpa [Real.dist_eq] using (le_of_lt (by simpa [Real.dist_eq] using hs))
  have hEq : (data.u x w) =ᶠ[𝓝 0]
      (fun s : ℝ => data.u0 x w + s * data.u1 x w + s ^ 2 * data.u2 x w
        + s ^ 3 * data.u3 x w + s ^ 4 * ρ ((x, w), s)) := by
    filter_upwards [hseg] with s hs
    exact hρ (x, w) s ⟨hx, hw⟩ hs
  have hρdiff : HasDerivAt (fun s : ℝ => ρ ((x, w), s))
      (deriv (fun s : ℝ => ρ ((x, w), s)) 0) 0 := by
    exact ((hρSmooth.differentiable (by simp) ((x, w), 0)).comp 0 (by fun_prop)).hasDerivAt
  have hpoly : HasDerivAt
      (fun s : ℝ => data.u0 x w + s * data.u1 x w + s ^ 2 * data.u2 x w
        + s ^ 3 * data.u3 x w + s ^ 4 * ρ ((x, w), s)) (data.u1 x w) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (data.u0 x w)).add
        (((hasDerivAt_id (0 : ℝ)).mul_const (data.u1 x w)).add
          (((hasDerivAt_pow 2 (0 : ℝ)).mul_const (data.u2 x w)).add
            (((hasDerivAt_pow 3 (0 : ℝ)).mul_const (data.u3 x w)).add
              ((hasDerivAt_pow 4 (0 : ℝ)).mul hρdiff)))) using 1
    · ext s
      simp only [Pi.add_apply, Pi.mul_apply, id_eq]
      ring
    · simp
  exact hpoly.congr_of_eventuallyEq hEq

-- Gradient of `u` in the `w` variables, represented in the standard basis.
noncomputable def gradW (p : ℝ^m) (w : ℝ^n) (s : ℝ) : ℝ^n :=
  fun α => fderiv ℝ (fun w' : ℝ^n => data.u p w' s) w (e α)

/-- For fixed `p`, the map `(w,s) ↦ gradW p w s` is smooth. -/
lemma gradW_smooth (p : ℝ^m) :
    Smooth (fun q : ℝ^n × ℝ => gradW p q.1 q.2) := by
  rw [contDiff_pi]
  intro α
  let f : ℝ^n × ℝ → ℝ^n → ℝ := fun q w => data.u p w q.2
  have hf : Smooth (uncurry f) := by
    have hcomp : Smooth (fun z : (ℝ^n × ℝ) × ℝ^n => (p, z.2, z.1.2)) := by fun_prop
    simpa [f, Function.uncurry_def] using asm.uSmooth.comp hcomp
  simpa [gradW, f] using
    (hf.fderiv_apply (g := fun q : ℝ^n × ℝ => q.1) (k := fun _ : ℝ^n × ℝ => e α)
      (by fun_prop) (by fun_prop) (by simp))

/-- The critical point equation holds at `(w,s) = (0,0)`. -/
lemma gradW_zero (p : ℝ^m) (hp : inBounds p) : gradW p 0 0 = 0 := by
  have hB : B data.r0 ∈ 𝓝 (0 : ℝ^n) := B_mem_nhds_zero asm.hr0
  have hEq : (fun w : ℝ^n => data.u p w 0) =ᶠ[𝓝 (0 : ℝ^n)] data.u0 p := by
    filter_upwards [hB] with w hw
    exact data_u_zero p hp w (B_subset_D hw)
  ext α
  have hderiv : fderiv ℝ (fun w : ℝ^n => data.u p w 0) 0 = diff (data.u0 p) 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hEq]
  have hz : u0W p 0 = 0 := u0WAtZero p hp
  simpa [gradW, u0W, hderiv] using congrArg (fun L : ℝ^n → ℝ => L (e α)) hz

-- The vector \hat w(x) appearing in the paper's expansion proof.
noncomputable def hatw (x : ℝ^m) : ℝ^n :=
  (u0WW x 0)⁻¹ *ᵥ (fun α : Fin n =>
    - u2W x 0 (e α)
    - ∑ β : Fin n, u1WW x 0 α β * bud.barw x β
    - ((1 : ℝ) / 2) * ∑ β : Fin n, ∑ γ : Fin n,
        u0WWW x 0 α β γ * bud.barw x β * bud.barw x γ)

/-- Defining identity for `hatw`, obtained by applying `u0WW(x,0)` to its definition. -/
lemma hatw_spec (x : ℝ^m) (hx : inBounds x) :
    u0WW x 0 *ᵥ hatw x =
      fun α : Fin n =>
        - u2W x 0 (e α)
        - ∑ β : Fin n, u1WW x 0 α β * bud.barw x β
        - ((1 : ℝ) / 2) * ∑ β : Fin n, ∑ γ : Fin n,
            u0WWW x 0 α β γ * bud.barw x β * bud.barw x γ := by
  have hpos : (u0WW x 0).PosDef := u0WWAtZero x hx
  have hdet : IsUnit (u0WW x 0).det :=
    (Matrix.isUnit_iff_isUnit_det (u0WW x 0)).mp hpos.isUnit
  ext α
  change (u0WW x 0 *ᵥ ((u0WW x 0)⁻¹ *ᵥ
    (fun β : Fin n =>
      - u2W x 0 (e β)
      - ∑ γ : Fin n, u1WW x 0 β γ * bud.barw x γ
      - ((1 : ℝ) / 2) * ∑ γ : Fin n, ∑ δ : Fin n,
          u0WWW x 0 β γ δ * bud.barw x γ * bud.barw x δ)) : Fin n → ℝ) α = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- One coordinate of the derivative of `w ↦ gradW p w 0` is the corresponding row of `u0WW p 0`. -/
lemma hasFDerivAt_gradW_w_comp (p : ℝ^m) (hp : inBounds p) (α : Fin n) :
    HasFDerivAt (fun w : ℝ^n => gradW p w 0 α)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
        ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap)) 0 := by
  have hB : B data.r0 ∈ 𝓝 (0 : ℝ^n) := B_mem_nhds_zero asm.hr0
  have hu0Smooth : Smooth (data.u0 p) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) p))
  have hgSmooth : Smooth (fun w : ℝ^n => data.u p w 0) := by
    have hcomp : Smooth (fun w : ℝ^n => (p, w, (0 : ℝ))) := by fun_prop
    simpa [Function.comp_def] using asm.uSmooth.comp hcomp
  have hclm : HasFDerivAt (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w (e α))
      ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fderiv ℝ (fun w' => data.u p w' 0)) 0)) 0 := by
    have hc : HasFDerivAt (fderiv ℝ (fun w' => data.u p w' 0))
        (fderiv ℝ (fderiv ℝ (fun w' => data.u p w' 0)) 0) 0 :=
      ((hgSmooth.fderiv_right (m := 1) (by simp)).differentiable (by simp) 0).hasFDerivAt
    have hu : HasFDerivAt (fun _ : ℝ^n => e α) (0 : ℝ^n →L[ℝ] ℝ^n) 0 :=
      (hasFDerivAt_const (e α) (0 : ℝ^n))
    simpa using hc.clm_apply hu
  have hdiff2 : fderiv ℝ (fderiv ℝ (fun w' => data.u p w' 0)) 0
      = diff2 (data.u0 p) 0 := by
    have hEq' : (fderiv ℝ (fun w' => data.u p w' 0))
        =ᶠ[𝓝 0] (fderiv ℝ (data.u0 p)) := by
      filter_upwards [hB] with w hw
      have hEqw : (fun w' : ℝ^n => data.u p w' 0) =ᶠ[𝓝 w] data.u0 p := by
        filter_upwards [B_mem_nhds hw] with w' hw'
        exact data_u_zero p hp w' (B_subset_D hw')
      simpa using hEqw.fderiv_eq
    rw [hEq'.fderiv_eq]
  have hsymm : IsSymmSndFDerivAt ℝ (data.u0 p) 0 := by
    have hf2 : ContDiff ℝ (2 : WithTop ℕ∞) (data.u0 p) := hu0Smooth.of_le le_top
    exact hf2.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hL : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
        ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap))
      = ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fderiv ℝ (fun w' => data.u p w' 0)) 0)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.apply_apply]
    rw [hdiff2]
    show (u0WW p 0 *ᵥ v) α = diff2 (data.u0 p) 0 v (e α)
    have hsymm' : diff2 (data.u0 p) 0 v (e α) = diff2 (data.u0 p) 0 (e α) v := by
      simpa [diff2, diff] using (hsymm.eq v (e α))
    rw [hsymm']
    have hv : v = ∑ j : Fin n, v j • e j := by
      ext i
      simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
    have hrhs : diff2 (data.u0 p) 0 (e α) v =
        ∑ j : Fin n, diff2 (data.u0 p) 0 (e α) (e j) * v j := by
      calc
        diff2 (data.u0 p) 0 (e α) v
            = diff2 (data.u0 p) 0 (e α) (∑ j : Fin n, v j • e j) := by
              exact congrArg _ hv
        _ = ∑ j : Fin n, v j * diff2 (data.u0 p) 0 (e α) (e j) := by
              simp [map_sum, map_smul, smul_eq_mul]
        _ = ∑ j : Fin n, diff2 (data.u0 p) 0 (e α) (e j) * v j := by
              simp [mul_comm]
    rw [hrhs]
    simp [Matrix.mulVec, dotProduct, u0WW, Matrix.of_apply, mul_comm]
  have hmain : HasFDerivAt (fun w : ℝ^n => gradW p w 0 α)
      ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fderiv ℝ (fun w' => data.u p w' 0)) 0)) 0 := by
    simpa [gradW] using hclm
  simpa [hL] using hmain

/-- The derivative in `w` of `gradW p w 0` at `w = 0` is the Hessian map `u0WW p 0`. -/
lemma hasFDerivAt_gradW_w (p : ℝ^m) (hp : inBounds p) :
    HasFDerivAt (fun w : ℝ^n => gradW p w 0)
      ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap) 0 := by
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
    HasDerivAt (fun s : ℝ => gradW x 0 s α) (u1W x 0 (e α)) 0 := by
  let F : ℝ × ℝ^n → ℝ := fun z => data.u x z.2 z.1
  have hFsmooth : Smooth F := by
    have hcomp : Smooth (fun z : ℝ × ℝ^n => (x, z.2, z.1)) := by fun_prop
    simpa [F, Function.comp_def] using asm.uSmooth.comp hcomp
  have hF2 : ContDiff ℝ (2 : WithTop ℕ∞) F := hFsmooth.of_le le_top
  let p0 : ℝ × ℝ^n := ((0 : ℝ), (0 : ℝ^n))
  have hfderivSmooth : Smooth (fderiv ℝ F) :=
    hFsmooth.fderiv_right (m := ⊤) (by simp)
  have hsecond : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) p0) p0 :=
    (hfderivSmooth.differentiable (by simp) p0).hasFDerivAt
  -- partial derivative in s at (0,w) equals u1
  have hKpoint (w : ℝ^n) (hw : inBounds w) :
      fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n)) = data.u1 x w := by
    have hFderiv : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), w)) ((0 : ℝ), w) :=
      (hFsmooth.differentiable (by simp) ((0 : ℝ), w)).hasFDerivAt
    have hline : HasFDerivAt (fun s : ℝ => (s, w))
        (ContinuousLinearMap.inl ℝ ℝ (ℝ^n)) 0 :=
      hasFDerivAt_prodMk_left (e₀ := (0 : ℝ)) (f₀ := w)
    have hcomp := hFderiv.comp 0 hline
    have hfd : fderiv ℝ (fun s : ℝ => F (s, w)) 0 =
        (fderiv ℝ F ((0 : ℝ), w)) ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ^n) := hcomp.fderiv
    have hval := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hfd
    have hder : HasDerivAt (fun s : ℝ => F (s, w)) (data.u1 x w) 0 := by
      simpa [F] using hasDerivAt_u_s x hx w hw
    have hval2 : fderiv ℝ (fun s : ℝ => F (s, w)) 0 1 = data.u1 x w := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using
        congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hder.hasFDerivAt.fderiv
    exact hval.symm.trans hval2
  have hB : B data.r0 ∈ 𝓝 (0 : ℝ^n) := B_mem_nhds_zero asm.hr0
  have hK_eq : (fun w : ℝ^n => fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n)))
      =ᶠ[𝓝 (0 : ℝ^n)] data.u1 x := by
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
      diff (data.u1 x) 0 := by
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
      (ContinuousLinearMap.toSpanSingleton ℝ (fun α : Fin n => u1W x 0 (e α))) 0 := by
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
    Smooth (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2) := by
  rw [contDiff_pi]
  intro α
  let g : (ℝ^m × ℝ) × ℝ^n → ℝ^n → ℝ := fun z w => data.u z.1.1 w z.1.2
  have hg : Smooth (uncurry g) := by
    have hcomp : Smooth (fun q : ((ℝ^m × ℝ) × ℝ^n) × ℝ^n => (q.1.1.1, q.2, q.1.1.2)) := by
      fun_prop
    simpa [g, Function.uncurry_def] using asm.uSmooth.comp hcomp
  simpa [gradW, g] using
    (hg.fderiv_apply (g := fun z : (ℝ^m × ℝ) × ℝ^n => z.2)
      (k := fun _ : (ℝ^m × ℝ) × ℝ^n => e α)
      (by fun_prop) (by fun_prop) (by simp))

-- The derivative in the `w` variables of the gradient map is the Hessian
-- `u0WW`, which is invertible by the quadratic lower bound on `u0`.
lemma u0WW_toLin_isInvertible (x : ℝ^m) (hx : inBounds x) :
    ((Matrix.toLin' (u0WW x 0)).toContinuousLinearMap).IsInvertible := by
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
      = (Matrix.toLin' (u0WW x 0)).toContinuousLinearMap := by
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
    ((fderiv ℝ
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2) (((x, (0 : ℝ)), (0 : ℝ^n)))
      ∘L ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)).IsInvertible) := by
  simpa [gradWParam_partial_eq x hx] using (u0WW_toLin_isInvertible x hx)

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
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (wStarAt x hx) (x, 0) := by
  simpa [wStarAt] using
    (ContDiffAt.contDiffAt_implicitFunction
      (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
        (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt)
      (by simp) (gradWParam_partial_isInvertible x hx))

-- Near the base point, `wStarAt` solves the critical point equation.
lemma wStarAt_eventually_zero (x : ℝ^m) (hx : inBounds x) :
    ∀ᶠ q in 𝓝 (x, (0 : ℝ)), gradW q.1 (wStarAt x hx q) q.2 = 0 := by
  have hz : gradW x 0 0 = 0 := gradW_zero x hx
  have hev := ContDiffAt.eventually_apply_implicitFunction
      (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
        (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt)
      (by simp) (gradWParam_partial_isInvertible x hx)
  filter_upwards [hev] with q hq
  simpa [wStarAt, hz] using hq

-- Differentiating the IFT formula at the base point gives the first-order
-- term of `w*`:  `d/ds w*(x,s)|₀ = \bar w(x)`.
lemma hasDerivAt_wStarAt_s (x : ℝ^m) (hx : inBounds x) :
    HasDerivAt (fun s : ℝ => wStarAt x hx (x, s)) (bud.barw x) 0 := by
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
lemma D_zero_mem : (0 : ℝ^n) ∈ D (d := n) data.r0 :=
  zero_mem_D (d := n) (r := data.r0) (le_of_lt asm.hr0)

/-- The domain ball `D r0` is nonempty. -/
lemma D_nonempty : (BrendleHung.Section2.Multivar.D (d := n) data.r0 : Set ℝ^n).Nonempty :=
  ⟨0, D_zero_mem⟩

-- Existence of a minimizer of `w ↦ u(x,w,s)` on the compact set `D r0`, and
-- the fact that `U(x,s)` is equal to the minimum.
lemma exists_minimizer (x : ℝ^m) (s : ℝ) :
    ∃ w ∈ D (d := n) data.r0,
      IsMinOn (fun w : ℝ^n => data.u x w s) (D (d := n) data.r0) w ∧
      bud.U x s = data.u x w s := by
  have hucont : Continuous (fun w : ℝ^n => data.u x w s) := by
    have hcomp : Continuous (fun w : ℝ^n => (x, w, s)) := by fun_prop
    exact asm.uSmooth.continuous.comp hcomp
  rcases (isCompact_D data.r0).exists_isMinOn D_nonempty hucont.continuousOn with
    ⟨w, hwD, hwmin⟩
  refine ⟨w, hwD, hwmin, ?_⟩
  have hbdd : BddBelow (Set.range (fun wsub : D (d := n) data.r0 => data.u x wsub.1 s)) := by
    refine ⟨data.u x w s, ?_⟩
    rintro _ ⟨wsub, rfl⟩
    exact hwmin wsub.2
  apply le_antisymm
  · simpa [bud] using (ciInf_le hbdd ⟨w, hwD⟩)
  · haveI : Nonempty (D (d := n) data.r0) := ⟨⟨0, D_zero_mem⟩⟩
    simpa [bud] using
      (le_ciInf (c := data.u x w s) (fun wsub : D (d := n) data.r0 => hwmin wsub.2))

-- Local uniqueness of the implicit solution: near the base point, the
-- critical point equation `gradW = 0` is equivalent to `w = wStarAt`.
lemma wStarAt_eventually_eq_iff_critical (x : ℝ^m) (hx : inBounds x) :
    ∀ᶠ z : (ℝ^m × ℝ) × ℝ^n in 𝓝 (((x, (0 : ℝ)), (0 : ℝ^n))),
      gradW z.1.1 z.2 z.1.2 = 0 ↔ wStarAt x hx z.1 = z.2 := by
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
    (hwin : norm w < data.r0)
    (hwmin : IsMinOn (fun w : ℝ^n => data.u x w s) (D (d := n) data.r0) w) :
    gradW x w s = 0 := by
  have hBnhds : B data.r0 ∈ 𝓝 w := B_mem_nhds_of_norm_lt hwin
  have hDnhds : D (d := n) data.r0 ∈ 𝓝 w :=
    mem_of_superset hBnhds (B_subset_D (d := n) (r := data.r0))
  have hlocalOn : IsLocalMinOn (fun w : ℝ^n => data.u x w s) (D (d := n) data.r0) w :=
    hwmin.localize
  have hlocal : IsLocalMin (fun w : ℝ^n => data.u x w s) w :=
    hlocalOn.isLocalMin hDnhds
  have hfderiv : fderiv ℝ (fun w : ℝ^n => data.u x w s) w = 0 :=
    hlocal.fderiv_eq_zero
  ext α
  have h := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) hfderiv
  simpa [gradW] using h

-- The minimizer in the definition of `U` is eventually the implicit function
-- `wStarAt`.  The argument is a compactness contradiction: a minimizing
-- sequence must converge to `0` by the quadratic lower bound for `u0`, and
-- then the local uniqueness of critical points gives the result.
lemma bud_U_eq_u_wStarAt_eventually (x : ℝ^m) (hx : inBounds x) :
    ∀ᶠ s : ℝ in 𝓝 0, bud.U x s = data.u x (wStarAt x hx (x, s)) s := by
  classical
  have hwstar_tendsto : Tendsto (fun s : ℝ => wStarAt x hx (x, s)) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (wStarAt x hx) (x, 0) := wStarAt_contDiffAt x hx |>.continuousAt
    have hline : Tendsto (fun s : ℝ => (x, s)) (𝓝 0) (𝓝 (x, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have ht := hcont.tendsto.comp hline
    simpa [wStarAt_self x hx] using ht
  have hmem : ∀ᶠ s : ℝ in 𝓝 0, norm (wStarAt x hx (x, s)) < data.r0 := by
    have hnorm : Tendsto (fun s : ℝ => norm (wStarAt x hx (x, s))) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (BrendleHung.Section2.Multivar.norm (d := n)) (0 : ℝ^n) :=
        (normCont n).continuousAt
      simpa [BrendleHung.Section2.Multivar.norm] using hc.tendsto.comp hwstar_tendsto
    have hopen : {v : ℝ | v < data.r0} ∈ 𝓝 (0 : ℝ) :=
      IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) asm.hr0
    exact hnorm.eventually hopen
  have hUle : ∀ᶠ s : ℝ in 𝓝 0,
      bud.U x s ≤ data.u x (wStarAt x hx (x, s)) s := by
    filter_upwards [hmem] with s hs
    rcases exists_minimizer x s with ⟨w, hwD, hwmin, hUeq⟩
    rw [hUeq]
    exact hwmin (le_of_lt hs)
  by_contra hnot
  have hneq : ∃ᶠ s : ℝ in 𝓝 0,
      bud.U x s ≠ data.u x (wStarAt x hx (x, s)) s := by
    simpa [not_eventually] using hnot
  have hbad : ∃ᶠ s : ℝ in 𝓝 0,
      bud.U x s < data.u x (wStarAt x hx (x, s)) s := by
    exact (hneq.and_eventually hUle).mono fun s hs =>
      lt_of_le_of_ne hs.2 hs.1
  let bad : Set ℝ := {s | bud.U x s < data.u x (wStarAt x hx (x, s)) s}
  haveI : NeBot (𝓝 (0 : ℝ) ⊓ 𝓟 bad) := by
    rw [← frequently_iff_neBot]
    exact hbad
  rcases exists_seq_tendsto (𝓝 (0 : ℝ) ⊓ 𝓟 bad) with ⟨sseq, hsseq⟩
  have hs_tendsto : Tendsto sseq atTop (𝓝 (0 : ℝ)) := (tendsto_inf.1 hsseq).1
  have hs_bad : ∀ᶠ n in atTop, sseq n ∈ bad := by
    simpa [tendsto_principal] using (tendsto_inf.1 hsseq).2
  have hmin_exists : ∀ k : ℕ, ∃ w ∈ D (d := n) data.r0,
      IsMinOn (fun w : ℝ^n => data.u x w (sseq k)) (D (d := n) data.r0) w ∧
      bud.U x (sseq k) = data.u x w (sseq k) := by
    intro k
    simpa using exists_minimizer x (sseq k)
  choose w hw using hmin_exists
  have hwD : ∀ k, w k ∈ D (d := n) data.r0 := fun k => (hw k).1
  have hwmin : ∀ k, IsMinOn (fun w : ℝ^n => data.u x w (sseq k))
      (D (d := n) data.r0) (w k) := fun k => (hw k).2.1
  have hUeq : ∀ k, bud.U x (sseq k) = data.u x (w k) (sseq k) := fun k => (hw k).2.2
  have hbad_w : ∀ᶠ k in atTop,
      data.u x (w k) (sseq k) < data.u x (wStarAt x hx (x, sseq k)) (sseq k) := by
    filter_upwards [hs_bad] with k hk
    change bud.U x (sseq k) < data.u x (wStarAt x hx (x, sseq k)) (sseq k) at hk
    rw [hUeq k] at hk
    exact hk
  rcases (isCompact_D data.r0).tendsto_subseq hwD with
    ⟨w0, hw0D, φ, hφmono, hwsub⟩
  have hφ : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hs_sub : Tendsto (fun k => sseq (φ k)) atTop (𝓝 (0 : ℝ)) := hs_tendsto.comp hφ
  have hbad_sub : ∀ᶠ k in atTop,
      data.u x (w (φ k)) (sseq (φ k)) <
        data.u x (wStarAt x hx (x, sseq (φ k))) (sseq (φ k)) :=
    hφ.eventually hbad_w
  have hucontAt : ∀ w : ℝ^n, ∀ s : ℝ,
      ContinuousAt (fun q : ℝ^n × ℝ => data.u x q.1 q.2) (w, s) := by
    intro w s
    have hcomp : ContinuousAt (fun q : ℝ^n × ℝ => (x, q.1, q.2)) (w, s) := by fun_prop
    have hu : ContinuousAt (fun y : ℝ^m × ℝ^n × ℝ => data.u y.1 y.2.1 y.2.2)
        (x, w, s) := asm.uSmooth.continuous.continuousAt
    simpa [Function.comp_def] using hu.comp hcomp
  have hR_tendsto : Tendsto
      (fun k => data.u x (wStarAt x hx (x, sseq k)) (sseq k)) atTop (𝓝 0) := by
    have hpair : Tendsto (fun k => (wStarAt x hx (x, sseq k), sseq k)) atTop
        (𝓝 ((0 : ℝ^n), (0 : ℝ))) :=
      (hwstar_tendsto.comp hs_tendsto).prodMk_nhds hs_tendsto
    have ht := (hucontAt 0 0).tendsto.comp hpair
    have h00 : data.u x 0 0 = 0 := by
      have h0 := asm.u0AtZero x hx
      simpa [data_u_zero x hx 0 D_zero_mem] using h0
    simpa [h00] using ht
  have hL_tendsto : Tendsto
      (fun k => data.u x (w (φ k)) (sseq (φ k))) atTop
      (𝓝 (data.u x w0 0)) := by
    have hpair : Tendsto (fun k => (w (φ k), sseq (φ k))) atTop (𝓝 (w0, 0)) :=
      hwsub.prodMk_nhds hs_sub
    exact (hucontAt w0 0).tendsto.comp hpair
  have hu0_le : data.u x w0 0 ≤ 0 :=
    le_of_tendsto_of_tendsto hL_tendsto (hR_tendsto.comp hφ)
      (hbad_sub.mono fun k hk => le_of_lt hk)
  have hu0_nonneg : 0 ≤ data.u x w0 0 := by
    have hquad := asm.u0Quadratic x w0 hx hw0D
    have hnonneg : 0 ≤ asm.σ * (norm w0 ^ 2) :=
      mul_nonneg (le_of_lt asm.hσ) (sq_nonneg _)
    have hEq : data.u x w0 0 = data.u0 x w0 := data_u_zero x hx w0 hw0D
    rw [hEq]
    linarith
  have hu0_eq : data.u x w0 0 = 0 := le_antisymm hu0_le hu0_nonneg
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
  have hwin_ev : ∀ᶠ k in atTop, norm (w (φ k)) < data.r0 := by
    have hopen : {v : ℝ | v < data.r0} ∈ 𝓝 (0 : ℝ) :=
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
    L v = ∑ i : Fin n, v i * L (e i) := by
  have hv : v = ∑ i : Fin n, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  rw [hv]
  simp [e, Finset.sum_apply, Pi.single_apply, Finset.mem_univ, map_sum, map_smul, smul_eq_mul]

/-- Expansion of a bilinear map in the standard basis of `ℝ^n`. -/
lemma bilinear_apply_eq_sum_basis
    (B : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)) (v w : ℝ^n) :
    B v w = ∑ i : Fin n, ∑ j : Fin n, v i * w j * B (e i) (e j) := by
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
      u i * v j * w k * T (e i) (e j) (e k) := by
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
    diff2 (data.u0 x) 0 (bud.barw x) v + diff (data.u1 x) 0 v = 0 := by
  let B : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := diff2 (data.u0 x) 0
  let L : ℝ^n →L[ℝ] ℝ := diff (data.u1 x) 0
  have hsymm : IsSymmSndFDerivAt ℝ (data.u0 x) (0 : ℝ^n) := by
    have hsmooth : ContDiff ℝ (2 : WithTop ℕ∞) (data.u0 x) := by
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
    bud.U2 x = data.u2 x 0 + (1 / 2 : ℝ) * diff (data.u1 x) 0 (bud.barw x) := by
  have hsum := clm_apply_eq_sum_basis (diff (data.u1 x) 0) (bud.barw x)
  change data.u2 x 0 + ((1 : ℝ) / 2) * ∑ α : Fin n, u1W x 0 (e α) * bud.barw x α =
    data.u2 x 0 + (1 / 2 : ℝ) * diff (data.u1 x) 0 (bud.barw x)
  congr 1
  rw [hsum]
  simp [u1W, mul_comm]

/-- The coordinate sums defining `bud.U3` equal their derivative/tensor form. -/
lemma bud_U3_eq (x : ℝ^m) (_ : inBounds x) :
    bud.U3 x =
      data.u3 x 0 + diff (data.u2 x) 0 (bud.barw x)
        + (1 / 2 : ℝ) * diff2 (data.u1 x) 0 (bud.barw x) (bud.barw x)
        + (1 / 6 : ℝ) * diff3 (data.u0 x) 0 (bud.barw x) (bud.barw x) (bud.barw x) := by
  have h1 := clm_apply_eq_sum_basis (diff (data.u2 x) 0) (bud.barw x)
  have h2 := bilinear_apply_eq_sum_basis (diff2 (data.u1 x) 0) (bud.barw x) (bud.barw x)
  have h3 := trilinear_apply_eq_sum_basis (diff3 (data.u0 x) 0)
    (bud.barw x) (bud.barw x) (bud.barw x)
  have h1' : (∑ α : Fin n, u2W x 0 (e α) * bud.barw x α) =
      diff (data.u2 x) 0 (bud.barw x) := by
    simpa [u2W, mul_comm] using h1.symm
  have h2' : (∑ α : Fin n, ∑ β : Fin n,
      u1WW x 0 α β * bud.barw x α * bud.barw x β) =
      diff2 (data.u1 x) 0 (bud.barw x) (bud.barw x) := by
    simpa [u1WW, mul_comm, mul_left_comm, mul_assoc] using h2.symm
  have h3' : (∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
      u0WWW x 0 α β γ * bud.barw x α * bud.barw x β * bud.barw x γ) =
      diff3 (data.u0 x) 0 (bud.barw x) (bud.barw x) (bud.barw x) := by
    simpa [u0WWW, mul_comm, mul_left_comm, mul_assoc] using h3.symm
  change data.u3 x 0
      + ∑ α : Fin n, u2W x 0 (e α) * bud.barw x α
      + ((1 : ℝ) / 2) * ∑ α : Fin n, ∑ β : Fin n,
          u1WW x 0 α β * bud.barw x α * bud.barw x β
      + ((1 : ℝ) / 6) * ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
          u0WWW x 0 α β γ * bud.barw x α * bud.barw x β * bud.barw x γ =
    data.u3 x 0 + diff (data.u2 x) 0 (bud.barw x)
      + (1 / 2 : ℝ) * diff2 (data.u1 x) 0 (bud.barw x) (bud.barw x)
      + (1 / 6 : ℝ) * diff3 (data.u0 x) 0 (bud.barw x) (bud.barw x) (bud.barw x)
  rw [h1', h2', h3']

/-- The reduced function vanishes at `s = 0`. -/
lemma bud_U_zero (x : ℝ^m) (hx : inBounds x) : bud.U x 0 = 0 := by
  rcases exists_minimizer x 0 with ⟨w, hwD, hwmin, hUeq⟩
  have hu00 : data.u x 0 0 = 0 := by
    have h0 := asm.u0AtZero x hx
    simpa [data_u_zero x hx 0 D_zero_mem] using h0
  have hle : bud.U x 0 ≤ 0 := by
    rw [hUeq]
    calc
      data.u x w 0 ≤ data.u x 0 0 := hwmin D_zero_mem
      _ = 0 := hu00
  have hge : 0 ≤ bud.U x 0 := by
    rw [hUeq, data_u_zero x hx w hwD]
    have hquad := asm.u0Quadratic x w hx hwD
    have hnonneg : 0 ≤ asm.σ * (norm w ^ 2) :=
      mul_nonneg (le_of_lt asm.hσ) (sq_nonneg _)
    linarith
  exact le_antisymm hle hge

/-- Smoothness of `u0` after fixing the parameter `x`. -/
lemma u0_x_smooth (x : ℝ^m) : Smooth (data.u0 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- Smoothness of `u1` after fixing the parameter `x`. -/
lemma u1_x_smooth (x : ℝ^m) : Smooth (data.u1 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u1Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- Smoothness of `u2` after fixing the parameter `x`. -/
lemma u2_x_smooth (x : ℝ^m) : Smooth (data.u2 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u2Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- Smoothness of `u3` after fixing the parameter `x`. -/
lemma u3_x_smooth (x : ℝ^m) : Smooth (data.u3 x) := by
  simpa [Function.comp_def, Function.uncurry_def] using
    (asm.u3Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))

/-- The fixed-parameter expansion of `u(x, w*(x,s), s)`.  This is the analytic
core of the paper's Section 2 computation: all unknown second-order terms of
`w*` cancel by the critical-point equation, leaving only the stated
`O(s⁴)` remainder. -/
lemma u_remainder_isBigO (x : ℝ^m) (hx : inBounds x) :
    (fun s : ℝ => data.u x (wStarAt x hx (x, s)) s
        - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
  classical
  rcases asm.uExp with ⟨ρ, hρSmooth, hρeq⟩
  let b : ℝ^n := bud.barw x
  let W : ℝ → ℝ^n := fun s => wStarAt x hx (x, s)
  let R : ℝ → ℝ^n := fun s => W s - s • b
  let B0 : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := diff2 (data.u0 x) 0
  let C0 : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)) := diff3 (data.u0 x) 0
  let L1 : ℝ^n →L[ℝ] ℝ := diff (data.u1 x) 0
  let B1 : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := diff2 (data.u1 x) 0
  let L2 : ℝ^n →L[ℝ] ℝ := diff (data.u2 x) 0

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

  have hWmem : ∀ᶠ s : ℝ in 𝓝 0, W s ∈ D (d := n) data.r0 := by
    have hnorm0 : norm (0 : ℝ^n) = 0 := by
      simp [BrendleHung.Section2.Multivar.norm]
    have hnorm : Tendsto (fun s : ℝ => norm (W s)) (𝓝 0) (𝓝 0) := by
      have ht := (normCont n).continuousAt.tendsto.comp hWtendsto
      simpa [Function.comp_def, hnorm0] using ht
    have hopen : {v : ℝ | v < data.r0} ∈ 𝓝 (0 : ℝ) :=
      IsOpen.mem_nhds (isOpen_lt continuous_id continuous_const) asm.hr0
    filter_upwards [hnorm.eventually hopen] with s hs
    exact le_of_lt hs
  have hseg : ∀ᶠ s : ℝ in 𝓝 0, s ∈ segment data.s0 := by
    refine mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) asm.hs0) ?_
    intro s hs
    change |s| ≤ data.s0
    simpa [Real.dist_eq] using (le_of_lt (by simpa [Real.dist_eq] using hs))
  have hExpEq : (fun s : ℝ => data.u x (W s) s) =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => data.u0 x (W s) + s * data.u1 x (W s)
        + s ^ 2 * data.u2 x (W s) + s ^ 3 * data.u3 x (W s)
        + s ^ 4 * ρ ((x, W s), s)) := by
    filter_upwards [hWmem, hseg] with s hWs hs
    exact hρeq (x, W s) s ⟨hx, hWs⟩ hs

  have hρline : Tendsto (fun s : ℝ => ((x, W s), s)) (𝓝 (0 : ℝ))
      (𝓝 ((x, W 0), (0 : ℝ))) := by
    have hp : Tendsto (fun s : ℝ => (x, W s)) (𝓝 (0 : ℝ)) (𝓝 (x, W 0)) :=
      tendsto_const_nhds.prodMk_nhds (by simpa [hW0] using hWtendsto)
    exact hp.prodMk_nhds tendsto_id
  have hρcont : ContinuousAt (fun s : ℝ => ρ ((x, W s), s)) 0 := by
    exact hρSmooth.continuous.continuousAt.tendsto.comp hρline
  have hρO : (fun s : ℝ => ρ ((x, W s), s)) =O[𝓝 (0 : ℝ)]
      (fun _ : ℝ => (1 : ℝ)) := isBigO_one_of_continuousAt hρcont
  have hρ4 : (fun s : ℝ => s ^ 4 * ρ ((x, W s), s)) =O[𝓝 (0 : ℝ)]
      (fun s : ℝ => s ^ 4) := by
    have hρO0 : (fun s : ℝ => ρ ((x, W s), s)) =O[𝓝 (0 : ℝ)]
        (fun s : ℝ => s ^ 0) := by
      simpa using hρO
    simpa using isBigO_mul_pow_of_isBigO_pow hρO0 4

  have hdu0 : diff (data.u0 x) 0 = 0 := by
    ext v
    have h := congrArg (fun f : ℝ^n → ℝ => f v) (u0WAtZero x hx)
    simpa [u0W] using h
  have hu00 : data.u0 x 0 = 0 := asm.u0AtZero x hx
  have hu10 : data.u1 x 0 = 0 := asm.u1AtZero x hx
  have h0rem : (fun s : ℝ =>
      data.u0 x (W s)
        - (1 / 2 : ℝ) * B0 (W s) (W s)
        - (1 / 6 : ℝ) * C0 (W s) (W s) (W s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa [taylorRemainderThree, B0, C0, hdu0, hu00, smul_eq_mul] using
      hcompose (k := 4) (smooth_taylor_three_isBigO (u0_x_smooth x))
  have h1rem : (fun s : ℝ =>
      data.u1 x (W s) - L1 (W s) - (1 / 2 : ℝ) * B1 (W s) (W s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 3) := by
    simpa [taylorRemainderTwo, L1, B1, hu10, smul_eq_mul] using
      hcompose (k := 3) (smooth_taylor_two_isBigO (u1_x_smooth x))
  have h2rem : (fun s : ℝ =>
      data.u2 x (W s) - data.u2 x 0 - L2 (W s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) := by
    simpa [L2] using hcompose (k := 2) (smooth_taylor_one_isBigO (u2_x_smooth x))
  have h3base : (fun z : ℝ^n => data.u3 x z - data.u3 x 0)
      =O[𝓝 (0 : ℝ^n)] (fun z : ℝ^n => ‖z‖ ^ (1 : ℕ)) := by
    simpa using smooth_taylor_zero_isBigO (u3_x_smooth x)
  have h3rem : (fun s : ℝ => data.u3 x (W s) - data.u3 x 0)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ (1 : ℕ)) := by
    simpa using hcompose (k := 1) h3base
  have h1s : (fun s : ℝ =>
      s * (data.u1 x (W s) - L1 (W s) - (1 / 2 : ℝ) * B1 (W s) (W s)))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow h1rem 1
  have h2s : (fun s : ℝ => s ^ 2 * (data.u2 x (W s) - data.u2 x 0 - L2 (W s)))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow h2rem 2
  have h3s : (fun s : ℝ => s ^ 3 * (data.u3 x (W s) - data.u3 x 0))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow h3rem 3
  have hsmall : (fun s : ℝ =>
      (data.u0 x (W s)
          - (1 / 2 : ℝ) * B0 (W s) (W s)
          - (1 / 6 : ℝ) * C0 (W s) (W s) (W s))
      + s * (data.u1 x (W s) - L1 (W s) - (1 / 2 : ℝ) * B1 (W s) (W s))
      + s ^ 2 * (data.u2 x (W s) - data.u2 x 0 - L2 (W s))
      + s ^ 3 * (data.u3 x (W s) - data.u3 x 0)
      + s ^ 4 * ρ ((x, W s), s))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) :=
    (((h0rem.add h1s).add h2s).add h3s).add hρ4

  have hsymm0 : IsSymmSndFDerivAt ℝ (data.u0 x) (0 : ℝ^n) :=
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
    have hWR : W s = s • b + R s := by simp [R]
    have hsymmRs : B0 (R s) b = B0 b (R s) := hB0symm (R s) b
    have hcross : B0 b (R s) + L1 (R s) = 0 := by
      simpa [b, B0, L1] using barw_cross_cancel x hx (R s)
    calc
      (1 / 2 : ℝ) * B0 (W s) (W s) + s * L1 (W s)
          - s ^ 2 * (1 / 2 : ℝ) * L1 b
          = s ^ 2 * ((1 / 2 : ℝ) * B0 b b + (1 / 2 : ℝ) * L1 b)
              + s * (B0 b (R s) + L1 (R s))
              + (1 / 2 : ℝ) * B0 (R s) (R s) := by
            rw [hWR]
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
      have hWR : W s = s • b + R s := by
        dsimp [R]
        abel
      rw [← hWR])
  have hA1 : (fun s : ℝ =>
      (1 / 6 : ℝ) * (C0 (W s) (W s) (W s) - s ^ 3 * C0 b b b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) :=
    hCdiff.const_mul_left (1 / 6 : ℝ)

  have hB1diff : (fun s : ℝ =>
      B1 (W s) (W s) - s ^ 2 * B1 b b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 3) := by
    exact (bilinear_leading_isBigO B1 b hR).congr_left (fun s => by
      have hWR : W s = s • b + R s := by
        dsimp [R]
        abel
      rw [← hWR])
  have hA2raw : (fun s : ℝ =>
      (1 / 2 : ℝ) * (B1 (W s) (W s) - s ^ 2 * B1 b b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 3) :=
    hB1diff.const_mul_left (1 / 2 : ℝ)
  have hA2s4 : (fun s : ℝ =>
      s ^ 1 * ((1 / 2 : ℝ) * (B1 (W s) (W s) - s ^ 2 * B1 b b)))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hA2raw 1
  have hA2 : (fun s : ℝ =>
      (s / 2) * (B1 (W s) (W s) - s ^ 2 * B1 b b))
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) :=
    hA2s4.congr_left (fun s => by ring)

  have hL2R : (fun s : ℝ => L2 (R s)) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) :=
    isBigO_clm_apply (α := ℝ) (E := ℝ^n) (F := ℝ^n) (G := ℝ)
      (l := 𝓝 (0 : ℝ)) L2 hR
  have hL2diff : (fun s : ℝ => L2 (W s) - s * L2 b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2) := by
    refine hL2R.congr_left ?_
    intro s
    have hWR : W s = s • b + R s := by simp [R]
    rw [hWR]
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
      + s ^ 2 * data.u2 x 0
      + s ^ 2 * L2 (W s)
      + s ^ 3 * data.u3 x 0
      - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    refine hleadSum.congr_left ?_
    intro s
    rw [bud_U2_eq x hx, bud_U3_eq x hx]
    simp [b, B0, C0, L1, B1, L2]
    ring

  have hpoly : (fun s : ℝ =>
      data.u0 x (W s) + s * data.u1 x (W s)
      + s ^ 2 * data.u2 x (W s) + s ^ 3 * data.u3 x (W s)
      + s ^ 4 * ρ ((x, W s), s)
      - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    have htotal := hsmall.add hlead
    refine htotal.congr_left ?_
    intro s
    simp [B0, C0, L1, B1, L2]
    ring
  have htarget : (fun s : ℝ =>
      data.u x (W s) s - s ^ 2 * bud.U2 x - s ^ 3 * bud.U3 x)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
    refine hpoly.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hExpEq] with s hs
    rw [hs]
  simpa [W] using htarget

/-- Main result: `U` has a third-order expansion with locally bounded remainder on `B r0`. -/
theorem expansion_of_U :
  ∃ s0 : ℝ, s0 > 0 ∧
  HasExpansion3 (B data.r0) s0 0 0 bud.U2 bud.U3 bud.U
:= by
  classical
  let ρU : ℝ^m × ℝ → ℝ := fun q =>
    if q.2 = 0 then 0 else
      (bud.U q.1 q.2 - q.2 ^ 2 * bud.U2 q.1 - q.2 ^ 3 * bud.U3 q.1) / q.2 ^ 4
  refine ⟨data.s0, asm.hs0, ρU, ?_, ?_⟩
  · intro p hp
    have hpD : inBounds p := B_subset_D hp
    have hO : (fun s : ℝ =>
        bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p)
        =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
      refine (u_remainder_isBigO p hpD).congr' ?_
        (Filter.Eventually.of_forall fun _ => rfl)
      filter_upwards [bud_U_eq_u_wStarAt_eventually p hpD] with s hs
      rw [hs]
    rcases (Asymptotics.isBigO_iff.mp hO) with ⟨c, hc⟩
    refine ⟨max c 0, ?_⟩
    have hCnonneg : 0 ≤ max c 0 := le_max_right c 0
    filter_upwards [hc] with s hs
    by_cases hs0 : s = 0
    · simp [ρU, hs0, hCnonneg]
    · have hs4_ne : s ^ 4 ≠ 0 := pow_ne_zero 4 hs0
      have hs4_pos : 0 < ‖s ^ 4‖ := norm_pos_iff.mpr hs4_ne
      have hc' : ‖bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p‖
          ≤ (max c 0) * ‖s ^ 4‖ := by
        exact le_trans hs
          (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _))
      have hdiv : ‖bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p‖ / ‖s ^ 4‖
          ≤ max c 0 := by
        exact (div_le_iff₀ hs4_pos).2 hc'
      rw [show ρU (p, s) =
          (bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p) / s ^ 4 by
        simp [ρU, hs0]]
      rw [abs_div]
      simpa [Real.norm_eq_abs] using hdiv
  · intro p s hp hs
    have hpD : inBounds p := B_subset_D hp
    by_cases hs0 : s = 0
    · subst s
      simp [ρU, bud_U_zero p hpD]
    · have hs4_ne : s ^ 4 ≠ 0 := pow_ne_zero 4 hs0
      simp [ρU, hs0]
      field_simp [hs4_ne]
      ring


end Section2
