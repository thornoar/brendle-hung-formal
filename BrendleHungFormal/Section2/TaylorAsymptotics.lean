import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace BrendleHung.Section2.TaylorAsymptotics

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

/-- If `‖fderiv f y‖ ≤ C‖y-x‖^n` near `x`, then `f y - f x = O(‖y-x‖^(n+1))`. -/
lemma bigO_of_fderiv_bound_pow
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {R C : ℝ} {n : ℕ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hdiff : ∀ y ∈ Metric.ball x R, DifferentiableAt ℝ f y)
    (hbound : ∀ y ∈ Metric.ball x R, ‖fderiv ℝ f y‖ ≤ C * ‖y - x‖ ^ n) :
    (fun y => f y - f x) =O[𝓝 x] (fun y => ‖y - x‖ ^ (n + 1)) := by
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x hR] with y hy
  have hsub : Metric.closedBall x ‖y - x‖ ⊆ Metric.ball x R := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hzx : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact lt_of_le_of_lt hzx (by simpa [Metric.mem_ball, dist_eq_norm] using hy)
  have hdiff' : ∀ z ∈ Metric.closedBall x ‖y - x‖, DifferentiableAt ℝ f z := fun z hz =>
    hdiff z (hsub hz)
  have hbound' : ∀ z ∈ Metric.closedBall x ‖y - x‖,
      ‖fderiv ℝ f z‖ ≤ C * ‖y - x‖ ^ n := by
    intro z hz
    have hzx : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hbound z (hsub hz)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzx n) hC)
  have hmvt := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_fderiv_le
      hdiff' hbound' (x := x) (y := y)
      (by simp [Metric.mem_closedBall]) (by simp [Metric.mem_closedBall, dist_eq_norm])
  have hdist : ‖y - x‖ ^ (n + 1) = ‖y - x‖ ^ n * ‖y - x‖ := by rw [pow_succ]
  calc
    ‖f y - f x‖ ≤ C * ‖y - x‖ ^ n * ‖y - x‖ := hmvt
    _ = C * ‖‖y - x‖ ^ (n + 1)‖ := by
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), hdist]
      ring

/-- A first-order Taylor estimate with remainder `O(‖z‖²)`, assuming only
smoothness at the base point. -/
lemma taylor_one_isBigO_of_contDiffAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} (hφ : ContDiffAt ℝ ⊤ φ (0 : E)) :
    (fun z => φ z - φ 0 - fderiv ℝ φ 0 z) =O[𝓝 (0 : E)] (fun z => ‖z‖ ^ (2 : ℕ)) := by
  let g : E → E →L[ℝ] F := fun z => fderiv ℝ φ z
  have hgcont : ContDiffAt ℝ 1 g (0 : E) := by
    simpa [g] using hφ.fderiv_right (m := (1 : WithTop ℕ∞)) (by simp)
  have hgdiff0 : DifferentiableAt ℝ g 0 := hgcont.differentiableAt_one
  have hgO : (fun z => g z - g 0) =O[𝓝 (0 : E)] (fun z => z - 0) :=
    hgdiff0.hasFDerivAt.isBigO_sub
  rcases isBigO_iff.mp hgO with ⟨C, hCev⟩
  have hCev' : ∀ᶠ z : E in 𝓝 0, ‖g z - g 0‖ ≤ |C| * ‖z‖ :=
    hCev.mono fun z hz => by
      simpa only [sub_zero] using hz.trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (z - 0)))
  rw [eventually_nhds_iff] at hCev'
  rcases hCev' with ⟨t, ht, htopen, h0t⟩
  rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds htopen h0t) with ⟨Rt, hRt, hRtsub⟩
  rcases hφ.contDiffOn (m := (2 : WithTop ℕ∞)) (by simp) (by simp) with
    ⟨u, hu, hucont⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨Rφ, hRφ, hRφsub⟩
  let R : ℝ := min Rt Rφ
  have hR : 0 < R := lt_min hRt hRφ
  have hRtsub' : Metric.ball (0 : E) R ⊆ t :=
    (Metric.ball_subset_ball (min_le_left Rt Rφ)).trans hRtsub
  have hRφsub' : Metric.ball (0 : E) R ⊆ u :=
    (Metric.ball_subset_ball (min_le_right Rt Rφ)).trans hRφsub
  have hφloc : ContDiffOn ℝ 2 φ (Metric.ball (0 : E) R) := hucont.mono hRφsub'
  have hgdiff : ∀ z ∈ Metric.ball (0 : E) R, DifferentiableAt ℝ g z := by
    intro z hz
    have hgOn : ContDiffOn ℝ 1 g (Metric.ball (0 : E) R) :=
      hφloc.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    exact (hgOn.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hdiff' : ∀ z ∈ Metric.ball (0 : E) R,
      DifferentiableAt ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z) z := by
    intro z hz
    have h1 : DifferentiableAt ℝ φ z :=
      (hφloc.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    exact (h1.sub (differentiableAt_const (c := φ 0))).sub (fderiv ℝ φ 0).differentiableAt
  have hbound' : ∀ z ∈ Metric.ball (0 : E) R,
      ‖fderiv ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z) z‖ ≤ |C| * ‖z - 0‖ ^ (1 : ℕ) := by
    intro z hz
    have hzt : z ∈ t := hRtsub' (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hgz : ‖g z - g 0‖ ≤ |C| * ‖z‖ := ht z hzt
    have hderiv : fderiv ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z) z = g z - g 0 := by
      have h1φ : DifferentiableAt ℝ φ z :=
        (hφloc.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
      have h1 : HasFDerivAt φ (g z) z := by simpa [g] using h1φ.hasFDerivAt
      have h2 : HasFDerivAt (fun _ : E => φ 0) (0 : E →L[ℝ] F) z :=
        hasFDerivAt_const (𝕜 := ℝ) (x := z) (c := φ 0)
      have h3 : HasFDerivAt (fun z : E => fderiv ℝ φ 0 z) (fderiv ℝ φ 0) z :=
        (fderiv ℝ φ 0).hasFDerivAt
      simpa [g] using (h1.sub h2 |>.sub h3).fderiv
    rw [hderiv]
    simpa [g] using hgz
  simpa using (bigO_of_fderiv_bound_pow
    (f := fun z => φ z - φ 0 - fderiv ℝ φ 0 z)
    (x := (0 : E)) (R := R) (C := |C|) (n := 1) hR (abs_nonneg C) hdiff' hbound')

/-- First-order Taylor estimate with `O(‖z‖²)` remainder for a globally smooth map. -/
lemma smooth_taylor_one_isBigO
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} (hφ : ContDiff ℝ ⊤ φ) :
    (fun z => φ z - φ 0 - fderiv ℝ φ 0 z) =O[𝓝 (0 : E)] (fun z => ‖z‖ ^ (2 : ℕ)) := by
  exact taylor_one_isBigO_of_contDiffAt (hφ.contDiffAt)

/-- Zeroth-order Taylor estimate `φ z - φ 0 = O(‖z‖)` for a smooth map. -/
lemma smooth_taylor_zero_isBigO
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} (hφ : ContDiff ℝ ⊤ φ) :
    (fun z => φ z - φ 0) =O[𝓝 (0 : E)] (fun z => ‖z‖) := by
  have h := (hφ.differentiable (by simp) (0 : E)).hasFDerivAt.isBigO_sub
  simpa only [sub_zero] using h.norm_right

/-- Second-order Taylor estimate with `O(‖z‖³)` remainder for a smooth map. -/
lemma smooth_taylor_two_isBigO
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → F} (hφ : ContDiff ℝ ⊤ φ) :
    (fun z => φ z - φ 0 - fderiv ℝ φ 0 z - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z)
    =O[𝓝 (0 : E)] (fun z => ‖z‖ ^ (3 : ℕ))
:= by
  let g : E → E →L[ℝ] F := fderiv ℝ φ
  let B : E →L[ℝ] (E →L[ℝ] F) := fderiv ℝ g 0
  have hg : ContDiff ℝ ⊤ g := by
    simpa [g] using hφ.fderiv_right (m := ⊤) (by simp)
  have hremG : (fun z => g z - g 0 - B z) =O[𝓝 (0 : E)] (fun z => ‖z‖ ^ (2 : ℕ)) := by
    simpa [g, B] using smooth_taylor_one_isBigO hg
  rcases isBigO_iff.mp hremG with ⟨C, hCev⟩
  have hCev' : ∀ᶠ z : E in 𝓝 0, ‖g z - g 0 - B z‖ ≤ |C| * ‖z‖ ^ (2 : ℕ) :=
    hCev.mono fun z hz => by
      simpa [Real.norm_of_nonneg (sq_nonneg ‖z‖)] using hz.trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (‖z‖ ^ (2 : ℕ))))
  rw [eventually_nhds_iff] at hCev'
  rcases hCev' with ⟨t, ht, htopen, h0t⟩
  rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds htopen h0t) with ⟨R, hR, hRsub⟩
  have hsymm : IsSymmSndFDerivAt ℝ φ (0 : E) := by
    exact (hφ.contDiffAt).isSymmSndFDerivAt (by simp)
  have hdiff' : ∀ z ∈ Metric.ball (0 : E) R,
      DifferentiableAt ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z) z := by
    intro z hz
    have hquad_diff : DifferentiableAt ℝ (fun z : E => B z z) z :=
      (B.differentiableAt).clm_apply differentiableAt_id
    exact (((hφ.differentiable (by simp) z).sub (differentiableAt_const (c := φ 0))).sub
      (fderiv ℝ φ 0).differentiableAt).sub (hquad_diff.const_smul (1 / 2 : ℝ))
  have hbound' : ∀ z ∈ Metric.ball (0 : E) R,
      ‖fderiv ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z) z‖ ≤ |C| * ‖z - 0‖ ^ (2 : ℕ) := by
    intro z hz
    have hzt : z ∈ t := hRsub (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hgz : ‖g z - g 0 - B z‖ ≤ |C| * ‖z‖ ^ (2 : ℕ) := ht z hzt
    have hflip : B.flip z = B z := by
      ext v
      simpa [B, g, ContinuousLinearMap.flip_apply] using (hsymm.eq z v).symm
    have hquad : HasFDerivAt (fun z : E => B z z) (B z + B.flip z) z := by
      simpa using (B.hasFDerivAt.clm_apply (hasFDerivAt_id (x := z)))
    have hquad' : HasFDerivAt (fun z : E => (1 / 2 : ℝ) • B z z) (B z) z := by
      have hraw := hquad.const_smul (1 / 2 : ℝ)
      convert hraw using 1
      ext v
      simp [hflip]
      rw [← add_smul]
      norm_num
    have hderiv : fderiv ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z) z = g z - g 0 - B z := by
      have h1 : HasFDerivAt φ (g z) z := (hφ.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun _ : E => φ 0) (0 : E →L[ℝ] F) z :=
        hasFDerivAt_const (𝕜 := ℝ) (x := z) (c := φ 0)
      have h3 : HasFDerivAt (fun z : E => fderiv ℝ φ 0 z) (fderiv ℝ φ 0) z :=
        (fderiv ℝ φ 0).hasFDerivAt
      simpa [g, B] using (h1.sub h2 |>.sub h3 |>.sub hquad').fderiv
    rw [hderiv]
    simpa using hgz
  simpa [g, B] using (bigO_of_fderiv_bound_pow
    (f := fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z)
    (x := (0 : E)) (R := R) (C := |C|) (n := 2) hR (abs_nonneg C) hdiff' hbound')

/-- Symmetry of the third derivative in its last two arguments for a smooth real-valued map. -/
lemma third_deriv_symm_last {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ⊤ φ) (u v w : E) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) (0 : E) u v) w =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) (0 : E) u w) v := by
  let A : E → ℝ := fun z => (fderiv ℝ (fderiv ℝ φ) z v) w
  let Bf : E → ℝ := fun z => (fderiv ℝ (fderiv ℝ φ) z w) v
  have hg : ContDiff ℝ ⊤ (fderiv ℝ φ) := hφ.fderiv_right (m := ⊤) (by simp)
  have hsecond : HasFDerivAt (fun z => fderiv ℝ (fderiv ℝ φ) z)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0) 0 :=
    ((hg.fderiv_right (m := 1) (by simp)).differentiable (by simp) 0).hasFDerivAt
  have mkA (q : E) : HasFDerivAt A
      (((ContinuousLinearMap.apply ℝ ℝ w).comp
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0)))) 0 := by
    have hc : HasFDerivAt (fun _ : E => w) 0 0 := hasFDerivAt_const (𝕜 := ℝ) w 0
    have hv : HasFDerivAt (fun _ : E => v) 0 0 := hasFDerivAt_const (𝕜 := ℝ) v 0
    simpa [A] using (hsecond.clm_apply hv).clm_apply hc
  have mkB (q : E) : HasFDerivAt Bf
      (((ContinuousLinearMap.apply ℝ ℝ v).comp
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) w).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0)))) 0 := by
    have hc : HasFDerivAt (fun _ : E => v) 0 0 := hasFDerivAt_const (𝕜 := ℝ) v 0
    have hw : HasFDerivAt (fun _ : E => w) 0 0 := hasFDerivAt_const (𝕜 := ℝ) w 0
    simpa [Bf] using (hsecond.clm_apply hw).clm_apply hc
  have hEq : A = Bf := by
    funext z
    have hsymm : IsSymmSndFDerivAt ℝ φ z := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
    simpa [A, Bf] using hsymm.eq v w
  have hfA := (mkA u).fderiv
  have hfB := (mkB u).fderiv
  rw [hEq] at hfA
  have hlin : ((ContinuousLinearMap.apply ℝ ℝ w).comp
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0))) =
      ((ContinuousLinearMap.apply ℝ ℝ v).comp
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) w).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0))) := hfA.symm.trans hfB
  simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L : E →L[ℝ] ℝ => L u) hlin

/-- Third-order Taylor estimate with `O(‖z‖⁴)` remainder for a smooth real-valued map. -/
lemma smooth_taylor_three_isBigO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ⊤ φ) :
    (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z -
        (1 / 6 : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0 z z z)
      =O[𝓝 (0 : E)] (fun z => ‖z‖ ^ (4 : ℕ)) := by
  let g : E → E →L[ℝ] ℝ := fun z => fderiv ℝ φ z
  let B : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ g 0
  let C : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) := fderiv ℝ (fderiv ℝ g) 0
  have hg : ContDiff ℝ ⊤ g := by
    simpa [g] using hφ.fderiv_right (m := ⊤) (by simp)
  have hremG : (fun z => g z - g 0 - B z - (1 / 2 : ℝ) • C z z)
      =O[𝓝 (0 : E)] (fun z => ‖z‖ ^ (3 : ℕ)) := by
    simpa [g, B, C] using smooth_taylor_two_isBigO hg
  rcases isBigO_iff.mp hremG with ⟨K, hKev⟩
  have hKev' : ∀ᶠ z : E in 𝓝 0,
      ‖g z - g 0 - B z - (1 / 2 : ℝ) • C z z‖ ≤ |K| * ‖z‖ ^ (3 : ℕ) :=
    hKev.mono fun z hz => by
      have hn : 0 ≤ ‖‖z‖ ^ (3 : ℕ)‖ := norm_nonneg _
      simpa [Real.norm_of_nonneg hn] using hz.trans
        (mul_le_mul_of_nonneg_right (le_abs_self K) hn)
  rw [eventually_nhds_iff] at hKev'
  rcases hKev' with ⟨t, ht, htopen, h0t⟩
  rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds htopen h0t) with ⟨R, hR, hRsub⟩
  have hsymmB : IsSymmSndFDerivAt ℝ φ (0 : E) := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  have hsymmC : IsSymmSndFDerivAt ℝ g (0 : E) := hg.contDiffAt.isSymmSndFDerivAt (by simp)
  have hdiff' : ∀ z ∈ Metric.ball (0 : E) R,
      DifferentiableAt ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z -
        (1 / 6 : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0 z z z) z := by
    intro z hz
    have hquad_diff : DifferentiableAt ℝ (fun z : E => B z z) z :=
      (B.differentiableAt).clm_apply differentiableAt_id
    have hcub_diff : DifferentiableAt ℝ (fun z : E => C z z z) z :=
      ((C.differentiableAt).clm_apply differentiableAt_id).clm_apply differentiableAt_id
    exact ((((hφ.differentiable (by simp) z).sub (differentiableAt_const (c := φ 0))).sub
      (fderiv ℝ φ 0).differentiableAt).sub (hquad_diff.const_smul (1 / 2 : ℝ))).sub
      (hcub_diff.const_smul (1 / 6 : ℝ))
  have hbound' : ∀ z ∈ Metric.ball (0 : E) R,
      ‖fderiv ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z -
        (1 / 6 : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0 z z z) z‖
        ≤ |K| * ‖z - 0‖ ^ (3 : ℕ) := by
    intro z hz
    have hzt : z ∈ t := hRsub (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hgz : ‖g z - g 0 - B z - (1 / 2 : ℝ) • C z z‖ ≤ |K| * ‖z‖ ^ (3 : ℕ) := ht z hzt
    have hflipB : B.flip z = B z := by
      ext v
      simpa [B, g, ContinuousLinearMap.flip_apply] using (hsymmB.eq z v).symm
    have hquad : HasFDerivAt (fun z : E => B z z) (B z + B.flip z) z := by
      simpa using (B.hasFDerivAt.clm_apply (hasFDerivAt_id (x := z)))
    have hquad' : HasFDerivAt (fun z : E => (1 / 2 : ℝ) • B z z) (B z) z := by
      have hraw := hquad.const_smul (1 / 2 : ℝ)
      convert hraw using 1
      ext v
      simp [hflipB]
      ring
    have h1clm (C : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (z : E) :=
      (C.hasFDerivAt.clm_apply (hasFDerivAt_id (x := z))).clm_apply (hasFDerivAt_id (x := z))
    have hcub_raw := h1clm C z
    have hcub' : HasFDerivAt (fun z : E => (1 / 6 : ℝ) • C z z z)
        ((1 / 2 : ℝ) • (C z z)) z := by
      have hraw := hcub_raw.const_smul (1 / 6 : ℝ)
      convert hraw using 1
      ext v
      have hCuvw : ∀ a b c : E, C a b c = C a c b := by
        intro a b c
        simpa [C, g] using third_deriv_symm_last hφ a b c
      have hCuv : ∀ a b : E, C a b = C b a := by
        intro a b
        simpa [C, g] using hsymmC.eq a b
      have hCflip : C.flip z = C z := by
        ext a w
        exact congrArg (fun L : E →L[ℝ] ℝ => L w) (hCuv a z)
      have h1 : (C z).flip z = C z z := by
        ext w
        exact hCuvw z w z
      have h2 : (C.flip z).flip z = C z z := by
        rw [hCflip]
        exact h1
      simp [h1, h2]
      ring
    have hderiv : fderiv ℝ (fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z -
        (1 / 6 : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0 z z z) z =
        g z - g 0 - B z - (1 / 2 : ℝ) • C z z := by
      have h1 : HasFDerivAt φ (g z) z := (hφ.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun _ : E => φ 0) (0 : E →L[ℝ] ℝ) z :=
        hasFDerivAt_const (𝕜 := ℝ) (x := z) (c := φ 0)
      have h3 : HasFDerivAt (fun z : E => fderiv ℝ φ 0 z) (fderiv ℝ φ 0) z :=
        (fderiv ℝ φ 0).hasFDerivAt
      simpa [g, B, C] using (h1.sub h2 |>.sub h3 |>.sub hquad' |>.sub hcub').fderiv
    rw [hderiv]
    simpa using hgz
  simpa [g, B, C] using (bigO_of_fderiv_bound_pow
    (f := fun z => φ z - φ 0 - fderiv ℝ φ 0 z -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ φ) 0 z z -
        (1 / 6 : ℝ) • fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0 z z z)
    (x := (0 : E)) (R := R) (C := |K|) (n := 3) hR (abs_nonneg K) hdiff' hbound')

/-- For `n ≤ m`, `s^m = O(s^m)` near zero implies `s^m = O(s^n)`. -/
lemma isBigO_pow_of_le_nhds_zero {m n : ℕ} (hnm : n ≤ m) :
    (fun s : ℝ => s ^ m) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ n) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with s hs
  have hs1 : ‖s‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hs)
  have hp : ‖s‖ ^ m ≤ ‖s‖ ^ n := pow_le_pow_of_le_one (norm_nonneg s) hs1 hnm
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg s) _),
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg s) _)] using hp

/-- Near zero, `‖s‖^k = O(s^k)`. -/
lemma isBigO_norm_pow_eq (k : ℕ) :
    (fun s : ℝ => ‖s‖ ^ k) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ k) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [] with s
  simp [norm_pow]

/-- Applying a fixed continuous linear map preserves a big-O estimate. -/
lemma isBigO_clm_apply {α E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {l : Filter α} (L : F →L[ℝ] G) {f : α → F} {g : α → ℝ}
    (hf : f =O[l] g) : (fun x => L (f x)) =O[l] g := by
  rcases isBigO_iff.mp hf with ⟨C, hC⟩
  rw [isBigO_iff]
  refine ⟨|C| * ‖L‖, hC.mono ?_⟩
  intro x hx
  have hCL : C * ‖L‖ ≤ |C| * ‖L‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg L)
  calc
    ‖L (f x)‖ ≤ ‖L‖ * ‖f x‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * ‖g x‖) := mul_le_mul_of_nonneg_left hx (norm_nonneg L)
    _ = (C * ‖L‖) * ‖g x‖ := by ring
    _ ≤ (|C| * ‖L‖) * ‖g x‖ := mul_le_mul_of_nonneg_right hCL (norm_nonneg _)

/-- Applying a fixed continuous bilinear map multiplies the big-O bounds of its arguments. -/
lemma isBigO_bilinear_apply {α E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {l : Filter α} (B : E →L[ℝ] F →L[ℝ] G) {f : α → E} {g : α → F} {h k : α → ℝ}
    (hf : f =O[l] h) (hg : g =O[l] k) :
    (fun x => B (f x) (g x)) =O[l] (fun x => h x * k x) := by
  rcases isBigO_iff.mp hf with ⟨C1, hC1⟩
  rcases isBigO_iff.mp hg with ⟨C2, hC2⟩
  rw [isBigO_iff]
  refine ⟨|C1| * |C2| * ‖B‖, (hC1.and hC2).mono ?_⟩
  intro x hx
  have hx1 : ‖f x‖ ≤ C1 * ‖h x‖ := hx.1
  have hx2 : ‖g x‖ ≤ C2 * ‖k x‖ := hx.2
  have hx1' : ‖f x‖ ≤ |C1| * ‖h x‖ := hx1.trans
    (mul_le_mul_of_nonneg_right (le_abs_self C1) (norm_nonneg _))
  have hx2' : ‖g x‖ ≤ |C2| * ‖k x‖ := hx2.trans
    (mul_le_mul_of_nonneg_right (le_abs_self C2) (norm_nonneg _))
  calc
    ‖B (f x) (g x)‖ ≤ ‖B (f x)‖ * ‖g x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B‖ * ‖f x‖) * ‖g x‖ := by
      gcongr
      exact B.le_opNorm _
    _ ≤ (‖B‖ * (|C1| * ‖h x‖)) * (|C2| * ‖k x‖) := by
      gcongr
    _ = (|C1| * |C2| * ‖B‖) * ‖h x * k x‖ := by
      rw [norm_mul]
      ring

/-- Applying a fixed continuous trilinear map multiplies the big-O bounds of its arguments. -/
lemma isBigO_trilinear_apply {α E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {l : Filter α} (T : E →L[ℝ] F →L[ℝ] G →L[ℝ] H)
    {f : α → E} {g : α → F} {h : α → G} {h₁ h₂ h₃ : α → ℝ}
    (hf : f =O[l] h₁) (hg : g =O[l] h₂) (hh : h =O[l] h₃) :
    (fun x => T (f x) (g x) (h x)) =O[l] (fun x => h₁ x * h₂ x * h₃ x) := by
  have hfg := isBigO_bilinear_apply (B := T) hf hg
  exact isBigO_bilinear_apply
    (B := ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ H)) hfg hh

/-- Multiplying `f = O(s^m)` by `s^k` gives `s^k * f = O(s^(k+m))`. -/
lemma isBigO_mul_pow_of_isBigO_pow {f : ℝ → ℝ} {m : ℕ}
    (hf : f =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ m)) (k : ℕ) :
    (fun s => s ^ k * f s) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ (k + m)) := by
  have hpow : (fun s : ℝ => s ^ k) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ k) := isBigO_refl _ _
  simpa [pow_add] using hpow.mul hf

/-- If `W(s) = s • b + R(s)` with `R = O(s²)`, the quadratic Taylor term differs
from its leading term by `O(s³)`. -/
lemma bilinear_leading_isBigO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (b : E) {R : ℝ → E}
    (hR : R =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2)) :
    (fun s => B (s • b + R s) (s • b + R s) - s ^ 2 * B b b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 3) := by
  have hbR : (fun s : ℝ => B b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 2) :=
    isBigO_clm_apply (α := ℝ) (E := E) (F := E) (G := ℝ) (l := 𝓝 (0 : ℝ)) (B b) hR
  have hRb : (fun s : ℝ => B (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 2) := by
    simpa [ContinuousLinearMap.flip_apply] using
      (isBigO_clm_apply (α := ℝ) (E := E) (F := E) (G := ℝ) (l := 𝓝 (0 : ℝ)) (B.flip b) hR)
  have hbR3 : (fun s : ℝ => s * B b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 3) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hbR 1
  have hRb3 : (fun s : ℝ => s * B (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 3) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hRb 1
  have hRR4 : (fun s : ℝ => B (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    exact (isBigO_bilinear_apply B hR hR).congr (fun _ => rfl) (fun s => by ring)
  have hRR3 : (fun s : ℝ => B (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 3) :=
    hRR4.trans (isBigO_pow_of_le_nhds_zero (m := 4) (n := 3) (by norm_num))
  have hsum : (fun s : ℝ =>
      s * B b (R s) + s * B (R s) b + B (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 3) :=
    (hbR3.add hRb3).add hRR3
  refine hsum.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [] with s
  simp [map_add, map_smul, smul_eq_mul]
  ring

/-- If `W(s) = s • b + R(s)` with `R = O(s²)`, the cubic Taylor term differs
from its leading term by `O(s⁴)`. -/
lemma trilinear_leading_isBigO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (b : E) {R : ℝ → E}
    (hR : R =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 2)) :
    (fun s => T (s • b + R s) (s • b + R s) (s • b + R s) -
        s ^ 3 * T b b b)
      =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
  let Tthird : E →L[ℝ] (E →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) b).comp
      (↑(ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) :
        (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))).comp T
  have hbbR : (fun s : ℝ => T b b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 2) :=
    isBigO_clm_apply (α := ℝ) (E := E) (F := E) (G := ℝ) (l := 𝓝 (0 : ℝ)) (T b b) hR
  have hbRb : (fun s : ℝ => T b (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 2) := by
    simpa [ContinuousLinearMap.flip_apply] using
      (isBigO_clm_apply (α := ℝ) (E := E) (F := E) (G := ℝ) (l := 𝓝 (0 : ℝ)) ((T b).flip b) hR)
  have hRbb : (fun s : ℝ => T (R s) b b) =O[𝓝 0] (fun s : ℝ => s ^ 2) := by
    simpa [Tthird, ContinuousLinearMap.flip_apply] using
      (isBigO_clm_apply (α := ℝ) (E := E) (F := E) (G := ℝ) (l := 𝓝 (0 : ℝ))
        ((ContinuousLinearMap.apply ℝ ℝ b).comp Tthird) hR)
  have hbbR4 : (fun s : ℝ => s ^ 2 * T b b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hbbR 2
  have hbRb4 : (fun s : ℝ => s ^ 2 * T b (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hbRb 2
  have hRbb4 : (fun s : ℝ => s ^ 2 * T (R s) b b) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hRbb 2
  have hbRR4 : (fun s : ℝ => T b (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    exact (isBigO_bilinear_apply (T b) hR hR).congr (fun _ => rfl) (fun s => by ring)
  have hRbR4 : (fun s : ℝ => T (R s) b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    exact (isBigO_bilinear_apply (T.flip b) hR hR).congr
      (fun s => by simp [ContinuousLinearMap.flip_apply]) (fun s => by ring)
  have hRRb4 : (fun s : ℝ => T (R s) (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 4) := by
    exact (isBigO_bilinear_apply Tthird hR hR).congr
      (fun s => by simp [Tthird, ContinuousLinearMap.flip_apply]) (fun s => by ring)
  have hbRR5 : (fun s : ℝ => s * T b (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 5) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hbRR4 1
  have hRbR5 : (fun s : ℝ => s * T (R s) b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 5) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hRbR4 1
  have hRRb5 : (fun s : ℝ => s * T (R s) (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 5) := by
    simpa using isBigO_mul_pow_of_isBigO_pow hRRb4 1
  have hbRR4' : (fun s : ℝ => s * T b (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) :=
    hbRR5.trans (isBigO_pow_of_le_nhds_zero (m := 5) (n := 4) (by norm_num))
  have hRbR4' : (fun s : ℝ => s * T (R s) b (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) :=
    hRbR5.trans (isBigO_pow_of_le_nhds_zero (m := 5) (n := 4) (by norm_num))
  have hRRb4' : (fun s : ℝ => s * T (R s) (R s) b) =O[𝓝 0] (fun s : ℝ => s ^ 4) :=
    hRRb5.trans (isBigO_pow_of_le_nhds_zero (m := 5) (n := 4) (by norm_num))
  have hRRR6 : (fun s : ℝ => T (R s) (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 6) := by
    exact (isBigO_trilinear_apply T hR hR hR).congr (fun _ => rfl) (fun s => by ring)
  have hRRR4 : (fun s : ℝ => T (R s) (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) :=
    hRRR6.trans (isBigO_pow_of_le_nhds_zero (m := 6) (n := 4) (by norm_num))
  have hsum : (fun s : ℝ =>
      s ^ 2 * T b b (R s) + s ^ 2 * T b (R s) b + s ^ 2 * T (R s) b b
      + s * T b (R s) (R s) + s * T (R s) b (R s) + s * T (R s) (R s) b
      + T (R s) (R s) (R s)) =O[𝓝 0] (fun s : ℝ => s ^ 4) :=
    (((((hbbR4.add hbRb4).add hRbb4).add hbRR4').add hRbR4').add hRRb4').add hRRR4
  refine hsum.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [] with s
  simp [map_add, map_smul, smul_eq_mul]
  ring

/-- A continuous real-valued function is locally `O(1)`. -/
lemma isBigO_one_of_continuousAt {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} {x : α} (hf : ContinuousAt f x) :
    f =O[𝓝 x] (fun _ : α => (1 : ℝ)) := by
  have htend : Tendsto f (𝓝 x) (𝓝 (f x)) := hf.tendsto
  have hevent : ∀ᶠ y in 𝓝 x, dist (f y) (f x) < 1 :=
    (Metric.tendsto_nhds.mp htend) 1 zero_lt_one
  refine IsBigO.of_bound (‖f x‖ + 1) ?_
  filter_upwards [hevent] with y hy
  have hle : ‖f y‖ ≤ ‖f x‖ + 1 := by
    calc
      ‖f y‖ = ‖(f y - f x) + f x‖ := by ring_nf
      _ ≤ ‖f y - f x‖ + ‖f x‖ := norm_add_le _ _
      _ = dist (f y) (f x) + ‖f x‖ := by rw [Real.dist_eq, Real.norm_eq_abs]
      _ ≤ 1 + ‖f x‖ := by linarith [le_of_lt hy]
      _ = ‖f x‖ + 1 := by ring
  simpa using hle

end

end BrendleHung.Section2.TaylorAsymptotics
