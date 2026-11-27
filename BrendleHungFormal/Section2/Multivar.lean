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

namespace BrendleHung.Section2.Multivar

open scoped BigOperators Topology
open Filter

/-- Coordinate vector type `Fin d → ℝ`. -/
abbrev Vector (d : ℕ) := Fin d → ℝ
notation:1024 "ℝ" "^" d:1024 => Vector d

-- The Euclidean norm of a coordinate vector.
noncomputable def norm {d : ℕ} (x : ℝ^d) : ℝ
:= √(∑ i : Fin d, x i ^ 2)

/-- Continuity of the Euclidean norm on coordinate vectors. -/
lemma normCont : ∀ (d : ℕ), Continuous (norm (d := d))
:= by
  intro d
  let g : ℝ^d → ℝ := fun w => ∑ i : Fin d, w i ^ 2
  have hgCont : Continuous g := by
    simpa [g] using
      (continuous_finset_sum (s := Finset.univ)
        (f := fun i : Fin d => fun w : ℝ^d => w i ^ 2)
        (fun i _ => (continuous_apply i).pow 2))
  simpa [norm, g] using Real.continuous_sqrt.comp hgCont

/-- The square of the Euclidean norm is the sum of squared coordinates. -/
lemma norm_square {d : ℕ} (w : ℝ^d) : norm w ^ 2 = ∑ i : Fin d, w i ^ 2 := by
  unfold norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (w i))]

/-- The Euclidean norm scales quadratically under scalar multiplication. -/
lemma norm_mul_sq {d : ℕ} (t : ℝ) (w : ℝ^d) : norm (t • w) ^ 2 = t ^ 2 * norm w ^ 2
:= by
  rewrite [norm_square, norm_square]
  change (∑ i : Fin d, (t * w i) ^ 2) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A nonzero vector has strictly positive Euclidean norm. -/
lemma ne_zero_norm_pos {d : ℕ} {w : ℝ^d} (hw : w ≠ 0) : 0 < norm w := by
  unfold norm
  apply Real.sqrt_pos.2
  have hex : ∃ i : Fin d, w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    exact h i
  rcases hex with ⟨i, hi⟩
  exact Finset.sum_pos' (fun j hj => sq_nonneg (w j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

-- The open ball `B_r^d` in coordinate space.
def B {d : ℕ} (r : ℝ) : Set ℝ^d
:= {x | norm x < r}

-- The closed ball `\bar B_r^d` in coordinate space.
public def D {d : ℕ} (r : ℝ) : Set ℝ^d
:= {x | norm x ≤ r}

/-- The open coordinate ball `B r` is open. -/
lemma isOpen_B {d : ℕ} (r : ℝ) : IsOpen (B (d := d) r) := by
  simpa [B] using (isOpen_lt (normCont d) continuous_const)

/-- If `0 < r`, the open ball `B r` is a neighborhood of the origin. -/
lemma B_mem_nhds_zero {d : ℕ} {r : ℝ} (hr : 0 < r) : B (d := d) r ∈ 𝓝 (0 : ℝ^d) := by
  refine IsOpen.mem_nhds (isOpen_B r) ?_
  simpa [B, norm] using hr

/-- The open ball `B r` is a neighborhood of each of its points. -/
lemma B_mem_nhds {d : ℕ} {r : ℝ} {x : ℝ^d} (hx : x ∈ B (d := d) r) : B (d := d) r ∈ 𝓝 x :=
  IsOpen.mem_nhds (isOpen_B r) hx

/-- `B r` is a neighborhood of `x` when `norm x < r`. -/
lemma B_mem_nhds_of_norm_lt {d : ℕ} {r : ℝ} {x : ℝ^d} (hx : norm x < r) : B (d := d) r ∈ 𝓝 x :=
  B_mem_nhds (by simpa [B] using hx)

/-- The open ball `B r` is contained in the closed ball `D r`. -/
lemma B_subset_D {d : ℕ} {r : ℝ} : B (d := d) r ⊆ D (d := d) r := by
  intro x hx
  change norm x ≤ r
  exact le_of_lt (by simpa [B] using hx)

/-- The closed coordinate ball `D r` is closed. -/
lemma isClosed_D {d : ℕ} (r : ℝ) : IsClosed (D (d := d) r) := by
  simpa [D] using (isClosed_le (normCont d) continuous_const)

/-- The origin lies in `D r` when `r` is nonnegative. -/
lemma zero_mem_D {d : ℕ} {r : ℝ} (hr : 0 ≤ r) : (0 : ℝ^d) ∈ D (d := d) r := by
  simp [D, norm, hr]

/-- The interval `[-a,a]` used for the auxiliary parameter `s`. -/
def segment (a : ℝ) : Set ℝ
:= {x | |x| ≤ a}

/-- The segment `[-a,a]` is a neighborhood of zero when `a > 0`. -/
lemma segment_mem_nhds_zero {a : ℝ} (ha : 0 < a) : segment a ∈ 𝓝 (0 : ℝ)
:= by
  refine mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) ha) ?_
  intro s hs
  change |s| ≤ a
  simpa [Real.dist_eq] using (le_of_lt (by simpa [Real.dist_eq] using hs))

/-- Fixed dimension of the parameter space `ℝ^m`. -/
axiom m : ℕ
/-- Fixed dimension of the variable space `ℝ^n`. -/
axiom n : ℕ

notation "Smooth" => ContDiff ℝ (⊤ : WithTop ℕ∞)

-- A Lean-friendly `O(s^4)` assertion for
-- `f(p,s) = f0(p) + s f1(p) + s² f2(p) + s³ f3(p) + O(s⁴)`.
--
-- The remainder is required to be locally bounded in `s`, for each fixed
-- parameter `p` in the domain.  This is the content of the asymptotic notation
-- used in the paper.  A stronger variant with a globally smooth remainder is
-- used as an assumption on the original function `u`; it implies this version.
def HasExpansion3 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ball : Set E) (a : ℝ) (f0 f1 f2 f3 : E -> ℝ) (f : E -> ℝ → ℝ) : Prop :=
  ∃ ρ : E × ℝ → ℝ,
    (∀ p ∈ ball, ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝 0, |ρ (p, s)| ≤ C) ∧
    ∀ p s,
      p ∈ ball ->
      s ∈ segment a ->
      f p s = f0 p + s * f1 p + s ^ 2 * f2 p + s ^ 3 * f3 p + s ^ 4 * ρ (p, s)

-- The stronger form of the expansion assumption used for `u` in Section 2.
def HasSmoothExpansion3 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ball : Set E) (a : ℝ) (f0 f1 f2 f3 : E -> ℝ) (f : E -> ℝ → ℝ) : Prop :=
  ∃ ρ : E × ℝ → ℝ,
    Smooth ρ ∧
    ∀ p s,
      p ∈ ball ->
      s ∈ segment a ->
      f p s = f0 p + s * f1 p + s ^ 2 * f2 p + s ^ 3 * f3 p + s ^ 4 * ρ (p, s)

noncomputable section

/-- The `i`-th standard basis vector of `ℝ^n`. -/
def e (i : Fin n) : ℝ^n := Pi.single i 1

/-- First derivative of a function on `ℝ^n`, as a continuous linear map. -/
abbrev diff (f : ℝ^n → ℝ) : ℝ^n -> ℝ^n →L[ℝ] ℝ
:= fderiv ℝ f

/-- Second derivative at `w`, as a continuous bilinear map. -/
abbrev diff2 (f : ℝ^n → ℝ) (w : ℝ^n)
: (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ))
:= fderiv ℝ (diff f) w

/-- Matrix of a bilinear map in the standard basis. -/
abbrev matrixOf (op : ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => op (e i) (e j)

/-- Third derivative at `w`, as a continuous trilinear map. -/
abbrev diff3 (f : ℝ^n → ℝ) (w : ℝ^n)
: (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)))
:= fderiv ℝ (diff2 f) w

end

/-- A function vanishing at zero with a positive quadratic lower bound has zero derivative at zero. -/
theorem ineq_zero_deriv (f : ℝ^n -> ℝ) (r : ℝ) (rh : r > 0) (σ : ℝ) (σh : σ > 0) :
  (f 0 = 0) ->
  (∀ w : ℝ^n, w ∈ B r -> f w ≥ σ * (norm w ^ 2)) ->
  diff f 0 = 0
:= by
  intro fAtZero quad
  have hminOn : IsMinOn f (B r) (0 : ℝ^n) := by
    rewrite [isMinOn_iff]
    intro w hw
    have hquadratic : f w ≥ σ * norm w ^ 2 := quad w hw
    have hnonneg : 0 ≤ σ * norm w ^ 2 := by
      nlinarith [σh, sq_nonneg (norm w)]
    nlinarith [fAtZero, hnonneg, hquadratic]
  have hOpenBallNhds : B r ∈ nhds (0 : ℝ^n) := B_mem_nhds_zero rh
  have hlocalMin : IsLocalMin f (0 : ℝ^n) := hminOn.isLocalMin hOpenBallNhds
  exact IsLocalMin.fderiv_eq_zero hlocalMin

/-- The Hessian at zero of such a function is positive definite. -/
theorem ineq_pos_def (f : ℝ^n → ℝ) (r : ℝ) (rh : r > 0) (σ : ℝ) (σh : σ > 0) :
  Smooth f ->
  f 0 = 0 →
  (∀ w : ℝ^n, w ∈ B r → f w ≥ σ * (norm w ^ 2)) →
  Matrix.PosDef (matrixOf $ diff2 f 0)
:= by
  intro hfSmooth fAtZero hquad
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
  simpa [diff2, diff] using (hsymm.eq (e i) (e j)).symm

  -- w^T H w > 0
  intro w wnonzero
  let v : ℝ^n := ⇑w
  have hvne : v ≠ 0 := by intro hv; apply wnonzero; ext i; simpa using congrFun hv i
  have hvnormpos : 0 < norm v := ne_zero_norm_pos hvne

  -- Slice f along the line t ↦ t v.
  let φ : ℝ → ℝ := fun t => f (t • v)
  have hφSmooth : Smooth φ := by
    have hlin : Smooth (fun t : ℝ => t • v) := by exact contDiff_id.smul contDiff_const
    exact hfSmooth.comp hlin
  have hφ0 : φ 0 = 0 := by simp [φ, fAtZero]
  have hφ1 : deriv φ 0 = 0 := by
    have hgrad : fderiv ℝ f 0 = 0 := by
      simpa [diff] using ineq_zero_deriv f r rh σ σh fAtZero hquad
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
  have hφ2 : iteratedDeriv 2 φ 0 = fderiv ℝ (fderiv ℝ f) 0 v v := by rw [hφ2diag, iteratedFDeriv_two_apply]

  -- For small t, t v still lies in the ball where the quadratic lower bound holds.
  have hcont_norm_smul : Continuous (fun t : ℝ => norm (t • v)) := by exact (normCont n).comp (continuous_id.smul continuous_const)
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t • v ∈ B r := by
    have hnhds : {t : ℝ | norm (t • v) < r} ∈ 𝓝 (0 : ℝ) := by
      refine IsOpen.mem_nhds (isOpen_lt hcont_norm_smul continuous_const) ?_
      simpa [norm] using rh
    filter_upwards [hnhds] with t ht
    exact ht

  -- Taylor expansion of φ to order 2 at 0, using φ 0 = 0 and φ' 0 = 0.
  have hφSmooth2 : ContDiff ℝ (2 : ℕ) φ := hφSmooth.of_le (by simp)
  let A : ℝ := iteratedDeriv 2 φ 0
  let c : ℝ := σ * norm v ^ 2
  have hcpos : 0 < c := by
    exact mul_pos σh (sq_pos_of_pos hvnormpos)
  have hsmall' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t • v ∈ B r := hsmall.filter_mono nhdsWithin_le_nhds

  have ht := Real.taylor_tendsto (f := φ) (x₀ := (0 : ℝ)) (n := (2 : ℕ))
    (s := Set.univ) convex_univ (by simp) hφSmooth2.contDiffOn
  have htIoi : Tendsto
      (fun t : ℝ => (φ t - taylorWithinEval φ 2 Set.univ 0 t) / (t - 0) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    ht.mono_left (nhdsWithin_mono (0 : ℝ) (Set.subset_univ _))
  have htend : Tendsto (fun t : ℝ => φ t / t ^ 2 - A / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ htIoi
    filter_upwards [self_mem_nhdsWithin] with t htpos
    have htne : t ≠ 0 := ne_of_gt htpos
    simp [A, taylorWithinEval, taylorWithin, taylorCoeffWithin,
      iteratedDerivWithin_univ, Finset.sum_range_succ, hφ0, hφ1]
    field_simp [htne]
  have htend_phi : Tendsto (fun t : ℝ => φ t / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (A / 2)) := by
    have hsum := htend.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (A / 2)))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hlowEv : ∀ᶠ t in 𝓝[>] (0 : ℝ), c ≤ φ t / t ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hsmall'] with t htpos htsmall
    have hq : f (t • v) ≥ σ * norm (t • v) ^ 2 := hquad (t • v) htsmall
    rw [norm_mul_sq] at hq
    have ht2pos : 0 < t ^ 2 := sq_pos_of_pos htpos
    rw [le_div_iff₀ ht2pos]
    dsimp [φ, c]
    nlinarith
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  have hc_le : c ≤ A / 2 := ge_of_tendsto htend_phi hlowEv
  have hApos : 0 < A := by
    nlinarith [hcpos, hc_le]

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
  have hsum_eq : (∑ i : Fin n, ∑ j : Fin n, w i * diff2 f 0 (e i) (e j) * w j) = A := by
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
    change (∑ i : Fin n, ∑ j : Fin n, w i * diff2 f 0 (e i) (e j) * w j) = iteratedDeriv 2 φ 0
    rw [← hφ2] at hB
    rw [hB]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [B, diff2, diff]
    ring
  have hfinsupp_eq :
      w.sum (fun i xi => w.sum fun j xj => star xi * diff2 f 0 (e i) (e j) * xj) =
        ∑ i : Fin n, ∑ j : Fin n, w i * diff2 f 0 (e i) (e j) * w j := by
    rw [Finsupp.sum_fintype w
      (fun i xi => w.sum fun j xj => star xi * diff2 f 0 (e i) (e j) * xj) (by simp)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.sum_fintype w
      (fun j xj => star (w i) * diff2 f 0 (e i) (e j) * xj) (by simp)]
    simp [star_trivial, mul_comm, mul_left_comm]
  change 0 < w.sum (fun i xi => w.sum fun j xj =>
    star xi * diff2 f 0 (e i) (e j) * xj)
  rw [hfinsupp_eq, hsum_eq]
  exact hApos

end BrendleHung.Section2.Multivar
