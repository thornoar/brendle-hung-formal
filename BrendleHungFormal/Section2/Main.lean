import BrendleHungFormal.Section2.Multivar
import Mathlib.Analysis.Calculus.ImplicitContDiff

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

theorem expansion_of_U :
  ∃ s0 : ℝ, s0 > 0 ∧
  HasExpansion3 (B data.r0) s0 0 0 bud.U2 bud.U3 bud.U
:= by
  refine ⟨data.s0 / 2, by nlinarith [asm.hs0], ?_⟩
  unfold HasExpansion3
  -- Construct a smooth remainder from the implicit-function solution `w*(p,s)`.
  -- The full Taylor coefficient identification is still pending.
  refine ⟨fun _ => 0, by simpa using (contDiff_const : Smooth (fun _ : ℝ^m × ℝ => (0 : ℝ))), ?_⟩
  intro p s hp hs
  have hplt : norm p < data.r0 := by simpa [B] using hp
  have hpD : inBounds p := by
    change norm p ≤ data.r0
    exact le_of_lt hplt
  have hpos : Matrix.PosDef (u0WW p 0) := u0WWAtZero p hpD
  have hdet : IsUnit (u0WW p 0).det :=
    (Matrix.isUnit_iff_isUnit_det (u0WW p 0)).mp hpos.isUnit
  -- Implicit function theorem setup for F((p,s), w) = gradW p w s.
  let F : (ℝ^m × ℝ) × ℝ^n → ℝ^n := fun z => gradW z.1.1 z.2 z.1.2
  have hF_smooth : Smooth F := gradWParam_smooth
  have hF0 : F ((p, (0 : ℝ)), (0 : ℝ^n)) = 0 := by
    simpa [F] using gradW_zero p hpD
  have hFderiv_w : HasFDerivAt (fun w : ℝ^n => F ((p, (0 : ℝ)), w))
      ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap) 0 := by
    simpa [F] using hasFDerivAt_gradW_w p hpD
  have hInr : fderiv ℝ F ((p, (0 : ℝ)), (0 : ℝ^n)) ∘L
      ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)
      = ((Matrix.toLin' (u0WW p 0)).toContinuousLinearMap) := by
    have hcomp :
        fderiv ℝ (fun w : ℝ^n => F ((p, (0 : ℝ)), w)) 0 =
          fderiv ℝ F ((p, (0 : ℝ)), (0 : ℝ^n)) ∘L
            ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n) := by
      have hlin : HasFDerivAt (fun w : ℝ^n => ((p, (0 : ℝ)), w))
          (ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)) 0 := by
        exact HasFDerivAt.prodMk
          (hasFDerivAt_const ((p, (0 : ℝ)) : ℝ^m × ℝ) (0 : ℝ^n))
          (hasFDerivAt_id (0 : ℝ^n))
      have hFdiff : DifferentiableAt ℝ F ((p, (0 : ℝ)), (0 : ℝ^n)) :=
        (hF_smooth.differentiable (by simp)).differentiableAt
      simpa [Function.comp] using (hFdiff.hasFDerivAt.comp (0 : ℝ^n) hlin).fderiv
    rw [← hcomp]
    exact hFderiv_w.fderiv
  have hInv : (fderiv ℝ F ((p, (0 : ℝ)), (0 : ℝ^n)) ∘L
      ContinuousLinearMap.inr ℝ (ℝ^m × ℝ) (ℝ^n)).IsInvertible := by
    rw [hInr]
    let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
      Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) (u0WW p 0) hdet
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    ext x i
    simp [e, Matrix.toLin_eq_toLin']
  -- Obtain a local implicit function w*(p,s) with gradW p (w*(p,s)) s = 0.
  have hIFT := (hF_smooth.contDiffAt :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) F ((p, (0 : ℝ)), (0 : ℝ^n)))
  let wStar : (ℝ^m × ℝ) → ℝ^n := hIFT.implicitFunction (by simp) hInv
  have hwStar_self : wStar (p, (0 : ℝ)) = 0 := by
    simpa [wStar] using hIFT.implicitFunction_apply_self (by simp) hInv
  have hwStar_eq :
      ∀ᶠ q : ℝ^m × ℝ in 𝓝 (p, (0 : ℝ)),
        F (q, wStar q) = F ((p, (0 : ℝ)), (0 : ℝ^n)) := by
    simpa [wStar] using hIFT.eventually_apply_implicitFunction (by simp) hInv
  have hwStar_iff :
      ∀ᶠ v : (ℝ^m × ℝ) × ℝ^n in 𝓝 ((p, (0 : ℝ)), (0 : ℝ^n)),
        F v = F ((p, (0 : ℝ)), (0 : ℝ^n)) ↔ wStar v.1 = v.2 := by
    simpa [wStar] using hIFT.eventually_apply_eq_iff_implicitFunction (by simp) hInv
  have hwStar_smooth : ContDiffAt ℝ (⊤ : WithTop ℕ∞) wStar (p, (0 : ℝ)) := by
    simpa [wStar] using hIFT.contDiffAt_implicitFunction (by simp) hInv
  have hwStar_cont : ContinuousAt wStar (p, (0 : ℝ)) := hwStar_smooth.continuousAt
  -- wStar stays in the small ball near 0 for small (q,s).
  have hwStar_mem : ∀ᶠ q : ℝ^m × ℝ in 𝓝 (p, (0 : ℝ)), wStar q ∈ B (data.r0 / 2) := by
    have hB0 : B (data.r0 / 2) ∈ 𝓝 (0 : ℝ^n) := by
      refine IsOpen.mem_nhds ?_ ?_
      · simpa [B] using (isOpen_lt (normCont n) continuous_const)
      · simpa [B, BrendleHung.Section2.Multivar.norm] using by linarith [asm.hr0]
    have hB0' : B (data.r0 / 2) ∈ 𝓝 (wStar (p, (0 : ℝ))) := by simpa [hwStar_self] using hB0
    simpa using hwStar_cont.preimage_mem_nhds hB0'
  -- Local minimizer identification: for small (q,s), wStar(q,s) is in D and minimizes u(q,·,s).
  rcases (asm.uExp : HasExpansion3 (D data.r0 ×ˢ D data.r0) data.s0
      (↓data.u0) (↓data.u1) (↓data.u2) (↓data.u3) (↓data.u)) with ⟨ρu, hρuSmooth, hρu⟩
  have hDcompact : IsCompact (D (d := n) data.r0) := by
    have hclosed : IsClosed (D (d := n) data.r0) := by
      simpa [D] using isClosed_le (normCont n) continuous_const
    have hsub : (D (d := n) data.r0) ⊆ Metric.closedBall (0 : ℝ^n) data.r0 := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      refine pi_norm_le_iff_of_nonneg (by linarith [asm.hr0]) |>.2 ?_
      intro i
      have hx' : BrendleHung.Section2.Multivar.norm x ≤ data.r0 := by simpa [D] using hx
      have hsq : (x i) ^ 2 ≤ BrendleHung.Section2.Multivar.norm x ^ 2 := by
        rw [BrendleHung.Section2.Multivar.norm_square]
        exact Finset.single_le_sum (f := fun j => (x j) ^ 2)
          (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have habs : |x i| ≤ BrendleHung.Section2.Multivar.norm x := by
        have hnonneg : 0 ≤ BrendleHung.Section2.Multivar.norm x := by
          unfold BrendleHung.Section2.Multivar.norm
          exact Real.sqrt_nonneg _
        nlinarith [sq_abs (x i), sq_nonneg (BrendleHung.Section2.Multivar.norm x - |x i|)]
      exact habs.trans hx'
    exact (isCompact_closedBall (0 : ℝ^n) data.r0).of_isClosed_subset hclosed hsub
  -- wStar(q) lies in D data.r0 near (p,0).
  have hwStar_memD : ∀ᶠ q : ℝ^m × ℝ in 𝓝 (p, (0 : ℝ)), wStar q ∈ D (d := n) data.r0 := by
    filter_upwards [hwStar_mem] with q hq
    have hlt : BrendleHung.Section2.Multivar.norm (wStar q) < data.r0 / 2 := by
      simpa [B] using hq
    have hle : BrendleHung.Section2.Multivar.norm (wStar q) ≤ data.r0 := by linarith [asm.hr0]
    simpa [D] using hle
  -- wStar(q) is a critical point: gradW = 0.
  have hwStar_crit : ∀ᶠ q : ℝ^m × ℝ in 𝓝 (p, (0 : ℝ)), gradW q.1 (wStar q) q.2 = 0 := by
    filter_upwards [hwStar_eq] with q hq
    have h0 : F ((p, (0 : ℝ)), (0 : ℝ^n)) = 0 := hF0
    simpa [F, h0] using hq
  -- Local uniqueness of critical points near 0 from IFT.
  have hwStar_unique :
      ∀ᶠ v : (ℝ^m × ℝ) × ℝ^n in 𝓝 ((p, (0 : ℝ)), (0 : ℝ^n)),
        gradW v.1.1 v.2 v.1.2 = 0 → wStar v.1 = v.2 := by
    filter_upwards [hwStar_iff] with v hv
    intro hg
    have : F v = F ((p, (0 : ℝ)), (0 : ℝ^n)) := by simpa [F, hF0] using hg
    exact hv.mp this
  -- TODO (task 1 completion): show that for small s, wStar(p,s) is the global minimizer
  -- of w ↦ data.u p w s on D data.r0, hence bud.U p s = data.u p (wStar p s) s.
  -- This uses the quadratic lower bound on u0, bounded perturbation terms from asm.uExp,
  -- and compactness of D to rule out boundary minimizers.
  -- Remaining: Taylor coefficients and smooth remainder ρ for HasExpansion3.
  sorry

end Section2
