import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Real.Sqrt
/- import Mathlib.Analysis.Asymptotics.Defs -/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/- import Mathlib.Analysis.Calculus.ImplicitProdDomain -/
/- import Mathlib.Analysis.InnerProductSpace.PiL2 -/
/- import Mathlib.Analysis.Normed.Module.FiniteDimension -/
import Mathlib.LinearAlgebra.Matrix.PosDef
/- import Mathlib.Topology.MetricSpace.Basic -/

/-!
Starting definitions for Section 2 of Brendle--Hung.

This module uses `Fin m -> ℝ` and `Fin n -> ℝ` for coordinate vectors.
It deliberately separates the coefficient data needed for the abstract
calculation from the analytical hypotheses under which the calculation holds.
-/

namespace BrendleHung.Section2

open scoped BigOperators Topology
open Filter

abbrev Vector (d : ℕ) := Fin d → ℝ
notation:1024 "ℝ" "^" d:1024 => Vector d

-- The Euclidean norm of a coordinate vector.
noncomputable def norm {d : ℕ} (x : ℝ^d) : ℝ
:= √(∑ i : Fin d, x i ^ 2)

lemma norm_sq {d : ℕ} (w : ℝ^d) : norm w ^ 2 = ∑ i : Fin d, w i ^ 2 := by
  unfold norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (w i))]

lemma norm_mul_sq {d : ℕ} (t : ℝ) (w : ℝ^d) :
    norm (t • w) ^ 2 = t ^ 2 * norm w ^ 2 := by
  rw [norm_sq, norm_sq]
  change (∑ i : Fin d, (t * w i) ^ 2) = t ^ 2 * ∑ i : Fin d, w i ^ 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma norm_pos_of_ne_zero {d : ℕ} {w : ℝ^d} (hw : w ≠ 0) : 0 < norm w := by
  unfold norm
  apply Real.sqrt_pos.2
  have hex : ∃ i : Fin d, w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    exact h i
  rcases hex with ⟨i, hi⟩
  exact Finset.sum_pos' (fun j hj => sq_nonneg (w j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

-- The open ball `B_r^d` in coordinate space.
def openBall (d : ℕ) (r : ℝ) : Set ℝ^d
:= {x | norm x < r}

-- The closed ball `\bar B_r^d` in coordinate space.
def closedBall (d : ℕ) (r : ℝ) : Set ℝ^d
:= {x | norm x ≤ r}

def segment (a : ℝ) : Set ℝ
:= {x | |x| ≤ a}

-- A Lean-friendly `O(s^4)` hypothesis for `u(x,w,s) = u0 + s u1 + s^2 u2 + s^3 u3 + O(s^4)`.
def HasExpansion3 (r : ℝ) (a : ℝ) (f0 f1 f2 f3 : ℝ^m -> ℝ^n -> ℝ) (f : ℝ^m → ℝ^n → ℝ → ℝ) : Prop :=
  ∃ ρ : ℝ^m → ℝ^n → ℝ → ℝ,
    ∀ x w s,
      x ∈ closedBall m r ->
      w ∈ closedBall n r ->
      s ∈ segment a ->
      f x w s = f0 x w + s * f1 x w + s ^ 2 * f2 x w + s ^ 3 * f3 x w + s ^ 4 * ρ x w s

open Function (uncurry)
notation "Smooth" => ContDiff ℝ (⊤ : WithTop ℕ∞)

axiom m : ℕ
axiom n : ℕ

structure InitialData where
  r0 : ℝ
  s0 : ℝ
  u : ℝ^m -> ℝ^n -> ℝ -> ℝ
  u0 : ℝ^m -> ℝ^n -> ℝ
  u1 : ℝ^m -> ℝ^n -> ℝ
  u2 : ℝ^m -> ℝ^n -> ℝ
  u3 : ℝ^m -> ℝ^n -> ℝ

structure InitialAssumptions where
  data : InitialData
  hr0 : data.r0 > 0
  hs0 : data.s0 > 0
  σ : ℝ
  hσ : σ > 0
  u0Smooth : Smooth (uncurry data.u0)
  u0AtZero : ∀ x : ℝ^m,
    x ∈ closedBall m r0 →
    data.u0 x 0 = 0
  u0Quadratic : ∀ x : ℝ^m, ∀ w : ℝ^n,
    x ∈ closedBall m r0 →
    w ∈ closedBall n r0 →
    data.u0 x w ≥ σ * (norm w ^ 2)
  u1Smooth : Smooth (uncurry data.u0)
  u1AtZero : ∀ x : ℝ^m, data.u1 x 0 = 0
  u2Smooth : Smooth (uncurry data.u0)
  u3Smooth : Smooth (uncurry data.u0)
  uExp : HasExpansion3 r0 s0 data.u0 data.u1 data.u2 data.u3 data.u
  -- h0PositiveDefinite : ∀ x : ℝ^m,
  --   x ∈ closedBall m r0 →
  --   Matrix.PosDef (data.u0WW x 0)

axiom ua : InitialAssumptions

abbrev inBounds {m : ℕ} (x : ℝ^m) : Prop
:= x ∈ closedBall m ua.data.r0

noncomputable section

-- abbrev Dw (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) : ℝ^n -> ℝ^n →L[ℝ] ℝ
abbrev Dw (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) : ℝ^n -> ℝ^n →L[ℝ] ℝ
:= fderiv ℝ (f x)

abbrev Dww (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n)
: (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ))
:= fderiv ℝ (Dw f x) w

abbrev Dwww (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n)
: (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)))
:= fderiv ℝ (Dww f x) w

def e (i : Fin n) : ℝ^n := Pi.single i 1

abbrev u0W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= Dw ua.data.u0 x w

abbrev u1W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= Dw ua.data.u1 x w

abbrev u2W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= Dw ua.data.u2 x w

abbrev u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => Dww ua.data.u0 x w (e i) (e j)

abbrev u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => Dww ua.data.u1 x w (e i) (e j)

abbrev u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ
:= Dwww ua.data.u0 x w (e i) (e j) (e k)

end

theorem normCont : forall (d : ℕ), Continuous (norm (d := d))
:= by
  intro d
  let g : ℝ^d → ℝ := fun w => ∑ i : Fin d, w i ^ 2
  have hgCont : Continuous g := by
    simpa [g] using
      (continuous_finset_sum (s := Finset.univ)
        (f := fun i : Fin d => fun w : ℝ^d => w i ^ 2)
        (fun i _ => (continuous_apply i).pow 2))
  simpa [norm, g] using Real.continuous_sqrt.comp hgCont

theorem u0WAtZero :
  forall x, inBounds x ->
  u0W x 0 = 0
:= by
  intro x hx
  have hminOn : IsMinOn (ua.data.u0 x) (openBall n ua.data.r0) (0 : ℝ^n) := by
    rewrite [isMinOn_iff]
    intro w hw
    have hw' : w ∈ closedBall n ua.data.r0 := by
      simpa [openBall, closedBall] using (le_of_lt hw)
    have hquadratic : ua.data.u0 x w ≥ ua.σ * norm w ^ 2 := ua.u0Quadratic x w hx hw'
    have hzero : ua.data.u0 x 0 = 0 := ua.u0AtZero x hx
    have hnonneg : 0 ≤ ua.σ * norm w ^ 2 := by
      nlinarith [ua.hσ, sq_nonneg (norm w)]
    nlinarith [hzero, hnonneg, hquadratic]
  have hnormCont : Continuous (norm (d := n)) := normCont n
  have hOpenBallNhds : openBall n ua.data.r0 ∈ nhds (0 : ℝ^n) := by
    refine IsOpen.mem_nhds ?_ ?_
    · simpa [openBall] using (isOpen_lt hnormCont continuous_const)
    · simpa [openBall, norm] using ua.hr0
  have hlocalMin : IsLocalMin (ua.data.u0 x) (0 : ℝ^n) := hminOn.isLocalMin hOpenBallNhds
  have hfderivZero : fderiv ℝ (ua.data.u0 x) 0 = 0 := IsLocalMin.fderiv_eq_zero hlocalMin
  ext i
  simpa [u0W, Dw] using DFunLike.congr_fun hfderivZero i

theorem u0WWAtZero :
  forall x, x ∈ closedBall m ua.data.r0 ->
  Matrix.PosDef (u0WW x 0)
:= by
  intro x hx
  let f : ℝ^n -> ℝ := ua.data.u0 x
  have hfSmooth : Smooth f := ua.u0Smooth.comp (contDiff_const.prodMk contDiff_id)
  have fAtZero : f 0 = 0 := by simpa using ua.u0AtZero x hx
  refine ⟨?_, ?_⟩
  -- Hermitian
  have hf2 : ContDiff ℝ (2 : WithTop ℕ∞) f := by
    refine (hfSmooth.of_le (le_of_lt ?_))
    simpa using (WithTop.coe_lt_top (2 : ℕ∞))
  have hsymm : IsSymmSndFDerivAt ℝ f 0 :=
    hf2.contDiffAt (x := 0) |>.isSymmSndFDerivAt
      (n := (↑(2 : ℕ∞) : WithTop ℕ∞))
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact le_rfl)
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simpa [u0WW, Dww, Dw, f] using (hsymm.eq (e i) (e j)).symm

  -- w^T H w > 0
  intro w wnonzero
  let v : ℝ^n := ⇑w
  have hvne : v ≠ 0 := by
    intro hv
    apply wnonzero
    ext i
    simpa [v] using congrFun hv i
  have hvnormpos : 0 < norm v := norm_pos_of_ne_zero hvne

  -- Slice f along the line t ↦ t v.
  let φ : ℝ → ℝ := fun t => f (t • v)
  have hφSmooth : Smooth φ := by
    have hlin : Smooth (fun t : ℝ => t • v) := by
      change Smooth (fun t : ℝ => t • v)
      exact contDiff_id.smul contDiff_const
    exact hfSmooth.comp hlin
  have hφ0 : φ 0 = 0 := by simp [φ, fAtZero]
  have hφ1 : deriv φ 0 = 0 := by
    have hgrad : fderiv ℝ f 0 = 0 := by
      ext z
      simpa [f, Dw, u0W] using congrFun (u0WAtZero x hx) z
    have hfderiv : HasFDerivAt f (fderiv ℝ f 0) 0 :=
      (hfSmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      change HasDerivAt (fun t : ℝ => t • v) v 0
      simpa only [one_smul] using (hasDerivAt_id (x := (0 : ℝ))).smul_const v
    have hcomp := hfderiv.comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa [φ, Function.comp_def, hgrad] using hcomp.deriv
  have hφ2diag : iteratedDeriv 2 φ 0 = iteratedFDeriv ℝ 2 f 0 (fun _ : Fin 2 => v) := by
    let L : ℝ →L[ℝ] ℝ^n := ContinuousLinearMap.toSpanSingleton ℝ v
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change (iteratedFDeriv ℝ 2 (f ∘ L) (0 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) =
      (iteratedFDeriv ℝ 2 f (0 : ℝ^n)) (fun _ : Fin 2 => v)
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hfSmooth (0 : ℝ) (i := 2) (by simp)]
    simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hφ2 : iteratedDeriv 2 φ 0 = fderiv ℝ (fderiv ℝ f) 0 v v := by
    rw [hφ2diag, iteratedFDeriv_two_apply]

  -- For small t, t v still lies in the ball where the quadratic lower bound holds.
  have hcont_norm_smul : Continuous (fun t : ℝ => norm (t • v)) := by
    have hlin_cont : Continuous (fun t : ℝ => t • v) :=
      continuous_id.smul continuous_const
    exact (normCont n).comp hlin_cont
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t • v ∈ closedBall n ua.data.r0 := by
    have hnhds : {t : ℝ | norm (t • v) < ua.data.r0} ∈ 𝓝 (0 : ℝ) := by
      refine IsOpen.mem_nhds (isOpen_lt hcont_norm_smul continuous_const) ?_
      simpa [norm] using ua.hr0
    filter_upwards [hnhds] with t ht
    exact le_of_lt ht

  -- Taylor expansion of φ to order 2 at 0, using φ 0 = 0 and φ' 0 = 0.
  have hφSmooth2 : ContDiff ℝ (2 : ℕ) φ := hφSmooth.of_le (by simp)
  have ho : (fun t : ℝ => φ t - t ^ 2 / 2 * iteratedDeriv 2 φ 0) =o[𝓝 (0 : ℝ)] (fun t => t ^ 2) := by
    have ht := taylor_isLittleO_univ (f := φ) (x₀ := (0 : ℝ)) (n := (2 : ℕ)) hφSmooth2
    convert ht using 1
    all_goals
      ext t
      simp [taylorWithinEval, taylorWithin, taylorCoeffWithin, Finset.sum_range_succ, hφ0, hφ1] <;> ring

  let A : ℝ := iteratedDeriv 2 φ 0
  let c : ℝ := ua.σ * norm v ^ 2
  have hcpos : 0 < c := by
    exact mul_pos ua.hσ (sq_pos_of_pos hvnormpos)
  have hεpos : 0 < c / 2 := by positivity
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ‖φ t - t ^ 2 / 2 * A‖ ≤ (c / 2) * ‖t ^ 2‖ :=
    ho.bound hεpos
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖φ t - t ^ 2 / 2 * A‖ ≤ (c / 2) * ‖t ^ 2‖ := hev.filter_mono nhdsWithin_le_nhds
  have hsmall' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t • v ∈ closedBall n ua.data.r0 := hsmall.filter_mono nhdsWithin_le_nhds
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  rcases Filter.Eventually.exists ((hpos.and hev').and hsmall') with
    ⟨t, ⟨htpos, htbound⟩, htsmall⟩

  have hlow : c * t ^ 2 ≤ φ t := by
    have hq : f (t • v) ≥ ua.σ * norm (t • v) ^ 2 := by
      simpa [f] using ua.u0Quadratic x (t • v) hx htsmall
    rw [norm_mul_sq] at hq
    dsimp [φ, c]
    nlinarith
  have hupper : φ t ≤ t ^ 2 / 2 * A + (c / 2) * t ^ 2 := by
    have hb := htbound
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at hb
    have hb' := (abs_le.1 hb).2
    nlinarith
  have ht2pos : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hmain : c ≤ A / 2 + c / 2 := by
    nlinarith [hlow, hupper]
  have hApos : 0 < A := by
    nlinarith [hcpos, hmain]

  -- Rewrite the Finsupp quadratic form as vᵀ H v, then use hφ2.
  have hvsum : v = ∑ i : Fin n, w i • e i := by
    ext j
    classical
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [v, e]
    · intro b hb hbj
      simp [e, Ne.symm hbj]
    · intro hj
      simp at hj
  have hsum_eq : (∑ i : Fin n, ∑ j : Fin n, w i * u0WW x 0 i j * w j) = A := by
    let B : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ f) 0
    have hB : B v v =
        ∑ i : Fin n, ∑ j : Fin n, w i * w j * B (e i) (e j) := by
      have h1 : B v v = ∑ i : Fin n, w i * B (e i) v := by
        calc
          B v v = B (∑ i : Fin n, w i • e i) v := by rw [hvsum]
          _ = ∑ i : Fin n, w i * B (e i) v := by simp [map_sum, map_smul]
      rw [h1]
      apply Finset.sum_congr rfl
      intro i hi
      have h2 : B (e i) v = ∑ j : Fin n, w j * B (e i) (e j) := by
        calc
          B (e i) v = B (e i) (∑ j : Fin n, w j • e j) := by rw [hvsum]
          _ = ∑ j : Fin n, w j * B (e i) (e j) := by simp [map_sum, map_smul]
      rw [h2]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change (∑ i : Fin n, ∑ j : Fin n, w i * u0WW x 0 i j * w j) = iteratedDeriv 2 φ 0
    rw [← hφ2] at hB
    rw [hB]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [B, u0WW, Dww, Dw, f]
    ring
  have hfinsupp_eq :
      w.sum (fun i xi => w.sum fun j xj => star xi * u0WW x 0 i j * xj) =
        ∑ i : Fin n, ∑ j : Fin n, w i * u0WW x 0 i j * w j := by
    rw [Finsupp.sum_fintype w
      (fun i xi => w.sum fun j xj => star xi * u0WW x 0 i j * xj) (by simp)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.sum_fintype w
      (fun j xj => star (w i) * u0WW x 0 i j * xj) (by simp)]
    simp [star_trivial, mul_comm, mul_left_comm]
  rw [hfinsupp_eq, hsum_eq]
  exact hApos

end BrendleHung.Section2
