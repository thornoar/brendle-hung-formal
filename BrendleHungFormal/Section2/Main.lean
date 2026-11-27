import BrendleHungFormal.Section2.Multivar
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open Function (uncurry)
open Filter
open scoped BigOperators Matrix Topology

section BrendleHung.Section2

open BrendleHung.Section2.Multivar

-- Keep the short name `norm` for the coordinate-space norm in this file,
-- without clashing with Mathlib's global `norm`.
local notation "norm" => BrendleHung.Section2.Multivar.norm
local notation "↓" f => uncurry f

structure InitialData where
  r0 : ℝ
  s0 : ℝ
  u : ℝ^m -> ℝ^n -> ℝ -> ℝ
  u0 : ℝ^m -> ℝ^n -> ℝ
  u1 : ℝ^m -> ℝ^n -> ℝ
  u2 : ℝ^m -> ℝ^n -> ℝ
  u3 : ℝ^m -> ℝ^n -> ℝ

axiom data : InitialData

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
  uExp : HasExpansion3 (D r0 ×ˢ D r0) s0
          (↓data.u0) (↓data.u1) (↓data.u2) (↓data.u3)
          (↓data.u)

axiom asm : InitialAssumptions

abbrev inBounds {m : ℕ} (x : ℝ^m) : Prop
:= x ∈ D data.r0

noncomputable section

abbrev u0W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (data.u0 x) w

abbrev u1W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (data.u1 x) w

abbrev u2W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (data.u2 x) w

abbrev u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (data.u0 x) w (e i) (e j)

abbrev u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (data.u1 x) w (e i) (e j)

abbrev u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ
:= diff3 (data.u0 x) w (e i) (e j) (e k)

end

lemma u0WAtZero (x : ℝ^m) (hx : inBounds x) : u0W x 0 = 0
:= by
  have hAtZero : data.u0 x 0 = 0 := asm.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ B data.r0 →
      data.u0 x w ≥ asm.σ * (norm w ^ 2) := by
    intro w hw
    exact asm.u0Quadratic x w hx (by simpa [B, D] using le_of_lt hw)
  have hderiv := ineq_zero_deriv (data.u0 x) data.r0 asm.hr0 asm.σ asm.hσ hAtZero hquad
  ext w
  simpa [u0W] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L w) hderiv

lemma u0WWAtZero (x : ℝ^m) (hx : inBounds x) : Matrix.PosDef (u0WW x 0)
:= by
  have hAtZero : data.u0 x 0 = 0 := asm.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ B data.r0 →
      data.u0 x w ≥ asm.σ * (norm w ^ 2) := by
    intro w hw
    exact asm.u0Quadratic x w hx (by simpa [B, D] using le_of_lt hw)
  have hsmooth : Smooth (data.u0 x) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))
  simpa [u0WW, matrixOf] using
    (ineq_pos_def (data.u0 x) data.r0 asm.hr0 asm.σ asm.hσ
      hsmooth hAtZero hquad)

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
    HasDerivAt (fun s : ℝ => data.u x w s) (data.u1 x w) 0 := by
  rcases asm.uExp with ⟨ρ, hρSmooth, hρ⟩
  have hseg : ∀ᶠ s : ℝ in 𝓝 0, s ∈ segment data.s0 := by
    refine mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) asm.hs0) ?_
    intro s hs
    change |s| ≤ data.s0
    simpa [Real.dist_eq] using (le_of_lt (by simpa [Real.dist_eq] using hs))
  have hEq : (fun s : ℝ => data.u x w s) =ᶠ[𝓝 0]
      (fun s : ℝ => data.u0 x w + s * data.u1 x w + s ^ 2 * data.u2 x w
        + s ^ 3 * data.u3 x w + s ^ 4 * ρ ((x, w), s)) := by
    filter_upwards [hseg] with s hs
    exact hρ (x, w) s ⟨hx, hw⟩ hs
  have hρdiff : HasDerivAt (fun s : ℝ => ρ ((x, w), s))
      (deriv (fun s : ℝ => ρ ((x, w), s)) 0) 0 := by
    have hρat : DifferentiableAt ℝ ρ ((x, w), 0) := hρSmooth.differentiable (by simp) ((x, w), 0)
    have hline : DifferentiableAt ℝ (fun s : ℝ => ((x, w), s)) 0 := by fun_prop
    exact (hρat.comp 0 hline).hasDerivAt
  have hpow2 : HasDerivAt (fun s : ℝ => s ^ 2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have hpow3 : HasDerivAt (fun s : ℝ => s ^ 3) 0 0 := by
    simpa using (hasDerivAt_pow 3 (0 : ℝ))
  have hpow4 : HasDerivAt (fun s : ℝ => s ^ 4) 0 0 := by
    simpa using (hasDerivAt_pow 4 (0 : ℝ))
  have h1 : HasDerivAt (fun s : ℝ => s * data.u1 x w) (data.u1 x w) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (data.u1 x w)
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * data.u2 x w) 0 0 := by
    simpa using hpow2.mul_const (data.u2 x w)
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3 * data.u3 x w) 0 0 := by
    simpa using hpow3.mul_const (data.u3 x w)
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4 * ρ ((x, w), s)) 0 0 := by
    simpa using hpow4.mul hρdiff
  have hpoly : HasDerivAt
      (fun s : ℝ => data.u0 x w + s * data.u1 x w + s ^ 2 * data.u2 x w
        + s ^ 3 * data.u3 x w + s ^ 4 * ρ ((x, w), s)) (data.u1 x w) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (data.u0 x w)).add
      (h1.add (h2.add (h3.add h4)))) using 1
    · ext s
      simp
      ring
    · ring
  exact hpoly.congr_of_eventuallyEq hEq

-- Gradient of `u` in the `w` variables, represented in the standard basis.
noncomputable def gradW (p : ℝ^m) (w : ℝ^n) (s : ℝ) : ℝ^n :=
  fun α => fderiv ℝ (fun w' : ℝ^n => data.u p w' s) w (e α)

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

lemma gradW_zero (p : ℝ^m) (hp : inBounds p) : gradW p 0 0 = 0 := by
  have hB : B data.r0 ∈ 𝓝 (0 : ℝ^n) := by
    refine IsOpen.mem_nhds ?_ ?_
    · simpa [B] using (isOpen_lt (normCont n) continuous_const)
    · simpa [B, BrendleHung.Section2.Multivar.norm] using asm.hr0
  have hEq : (fun w : ℝ^n => data.u p w 0) =ᶠ[𝓝 (0 : ℝ^n)] data.u0 p := by
    filter_upwards [hB] with w hw
    have hwl : BrendleHung.Section2.Multivar.norm w < data.r0 := by simpa [B] using hw
    exact data_u_zero p hp w (by
      change BrendleHung.Section2.Multivar.norm w ≤ data.r0
      exact le_of_lt hwl)
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

lemma hasFDerivAt_gradW_w_comp (p : ℝ^m) (hp : inBounds p) (α : Fin n) :
    HasFDerivAt (fun w : ℝ^n => gradW p w 0 α)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
        ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap)) 0 := by
  have hB : B data.r0 ∈ 𝓝 (0 : ℝ^n) := by
    refine IsOpen.mem_nhds ?_ ?_
    · simpa [B] using (isOpen_lt (normCont n) continuous_const)
    · simpa [B, BrendleHung.Section2.Multivar.norm] using asm.hr0
  have hu0Smooth : Smooth (data.u0 p) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (asm.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) p))
  have hgSmooth : Smooth (fun w : ℝ^n => data.u p w 0) := by
    have hcomp : Smooth (fun w : ℝ^n => (p, w, (0 : ℝ))) := by fun_prop
    simpa [Function.comp_def] using asm.uSmooth.comp hcomp
  have hclm : HasFDerivAt (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w (e α))
      ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w) 0)) 0 := by
    have hc : HasFDerivAt (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w)
        (fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w) 0) 0 :=
      ((hgSmooth.fderiv_right (m := 1) (by simp)).differentiable (by simp) 0).hasFDerivAt
    have hu : HasFDerivAt (fun _ : ℝ^n => e α) (0 : ℝ^n →L[ℝ] ℝ^n) 0 :=
      (hasFDerivAt_const (e α) (0 : ℝ^n))
    simpa using hc.clm_apply hu
  have hdiff2 : fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w) 0
      = diff2 (data.u0 p) 0 := by
    have hEq' : (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w)
        =ᶠ[𝓝 0] (fun w : ℝ^n => fderiv ℝ (data.u0 p) w) := by
      filter_upwards [hB] with w hw
      have hEqw : (fun w' : ℝ^n => data.u p w' 0) =ᶠ[𝓝 w] data.u0 p := by
        filter_upwards [IsOpen.mem_nhds (by simpa [B] using (isOpen_lt (normCont n) continuous_const)) hw] with w' hw'
        have hw'l : BrendleHung.Section2.Multivar.norm w' < data.r0 := by simpa [B] using hw'
        exact data_u_zero p hp w' (by
          change BrendleHung.Section2.Multivar.norm w' ≤ data.r0
          exact le_of_lt hw'l)
      simpa using hEqw.fderiv_eq
    rw [hEq'.fderiv_eq]
  have hsymm : IsSymmSndFDerivAt ℝ (data.u0 p) 0 := by
    have hf2 : ContDiff ℝ (2 : WithTop ℕ∞) (data.u0 p) := hu0Smooth.of_le le_top
    exact hf2.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hL : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp
        ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap))
      = ((ContinuousLinearMap.apply ℝ ℝ (e α)).comp
        (fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w) 0)) := by
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
        (fderiv ℝ (fun w : ℝ^n => fderiv ℝ (fun w' => data.u p w' 0) w) 0)) 0 := by
    simpa [gradW] using hclm
  simpa [hL] using hmain

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

lemma hasDerivAt_gradW_s_comp (x : ℝ^m) (hx : inBounds x) (α : Fin n) :
    HasDerivAt (fun s : ℝ => gradW x 0 s α) (u1W x 0 (e α)) 0 := by
  let F : ℝ × ℝ^n → ℝ := fun z => data.u x z.2 z.1
  have hFsmooth : Smooth F := by
    have hcomp : Smooth (fun z : ℝ × ℝ^n => (x, z.2, z.1)) := by fun_prop
    simpa [F, Function.comp_def] using asm.uSmooth.comp hcomp
  have hF2 : ContDiff ℝ (2 : WithTop ℕ∞) F := hFsmooth.of_le le_top
  let p0 : ℝ × ℝ^n := ((0 : ℝ), (0 : ℝ^n))
  have hfderivSmooth : Smooth (fun z => fderiv ℝ F z) :=
    hFsmooth.fderiv_right (m := ⊤) (by simp)
  have hsecond : HasFDerivAt (fun z => fderiv ℝ F z)
      (fderiv ℝ (fun z => fderiv ℝ F z) p0) p0 :=
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
  have hB : B data.r0 ∈ 𝓝 (0 : ℝ^n) := by
    refine IsOpen.mem_nhds ?_ ?_
    · simpa [B] using (isOpen_lt (normCont n) continuous_const)
    · simpa [B, BrendleHung.Section2.Multivar.norm] using asm.hr0
  have hK_eq : (fun w : ℝ^n => fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n)))
      =ᶠ[𝓝 (0 : ℝ^n)] data.u1 x := by
    filter_upwards [hB] with w hw
    exact hKpoint w (by
      change norm w ≤ data.r0
      exact le_of_lt (by simpa [B] using hw))
  have hKderiv : HasFDerivAt
      (fun z : ℝ × ℝ^n => fderiv ℝ F z ((1 : ℝ), (0 : ℝ^n)))
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ^n))).comp
        (fderiv ℝ (fun z => fderiv ℝ F z) p0)) p0 := by
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
        (fderiv ℝ (fun z => fderiv ℝ F z) p0)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ^n)) := hKcomp.fderiv
  have hK_fd' : fderiv ℝ
      (fun w : ℝ^n => fderiv ℝ F ((0 : ℝ), w) ((1 : ℝ), (0 : ℝ^n))) 0 =
      diff (data.u1 x) 0 := by
    rw [hK_eq.fderiv_eq]
  have hsnd : (fderiv ℝ (fun z => fderiv ℝ F z) p0) ((0 : ℝ), e α) ((1 : ℝ), (0 : ℝ^n))
      = u1W x 0 (e α) := by
    have hval := congrArg (fun L : ℝ^n →L[ℝ] ℝ => L (e α)) (hK_fd.symm.trans hK_fd')
    simpa [ContinuousLinearMap.comp_apply, u1W] using hval
  have hHderiv : HasFDerivAt
      (fun z : ℝ × ℝ^n => fderiv ℝ F z ((0 : ℝ), e α))
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), e α)).comp
        (fderiv ℝ (fun z => fderiv ℝ F z) p0)) p0 := by
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
        (fderiv ℝ (fun z => fderiv ℝ F z) p0)).comp
        (ContinuousLinearMap.inl ℝ ℝ (ℝ^n))) 0 :=
    hHderiv.comp (0 : ℝ) hlineS
  have hsymm : IsSymmSndFDerivAt ℝ F p0 :=
    hF2.contDiffAt.isSymmSndFDerivAt (by simp)
  have hH_L : (((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), e α)).comp
        (fderiv ℝ (fun z => fderiv ℝ F z) p0)).comp
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


lemma hasFDerivAt_gradW_s (x : ℝ^m) (hx : inBounds x) :
    HasFDerivAt (fun s : ℝ => gradW x 0 s)
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
    ext s α
    simp
  simpa [hL, v] using hpi

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

lemma wStarAt_self (x : ℝ^m) (hx : inBounds x) : wStarAt x hx (x, 0) = 0 := by
  simpa [wStarAt] using
    (ContDiffAt.implicitFunction_apply_self
      (show ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun z : (ℝ^m × ℝ) × ℝ^n => gradW z.1.1 z.2 z.1.2)
        (((x, (0 : ℝ)), (0 : ℝ^n))) from gradWParam_smooth.contDiffAt)
      (by simp) (gradWParam_partial_isInvertible x hx))

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
    change fderiv ℝ (fun s : ℝ => gradW x 0 s) 0 t =
      (H ∘L ((ContinuousLinearMap.inr ℝ ℝ^m ℝ).prod (0 : ℝ →L[ℝ] ℝ^n))) t at ht
    have hgrad := congrArg (fun L : ℝ →L[ℝ] ℝ^n => L t)
      (hasFDerivAt_gradW_s x hx).fderiv
    change fderiv ℝ (fun s : ℝ => gradW x 0 s) 0 t =
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

theorem expansion_of_U :
  ∃ s0 : ℝ, s0 > 0 ∧
  HasExpansion3 (B data.r0) s0 0 0 bud.U2 bud.U3 bud.U
:= by
  -- First prove the existence and properties of `w^*`
  sorry

end Section2
