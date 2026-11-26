import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

open scoped BigOperators

abbrev Vector (d : ℕ) := Fin d → ℝ
notation:1024 "ℝ" "^" d:1024 => Vector d

instance {d : ℕ} : HMul ℝ ℝ^d ℝ^d where
  hMul a v i := a * (v i)

-- The Euclidean norm of a coordinate vector.
noncomputable def norm {d : ℕ} (x : ℝ^d) : ℝ
:= √(∑ i : Fin d, x i ^ 2)

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
  let f := ua.data.u0 x
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
  have fWAtZero : ∑ i, fderiv ℝ f 0 (e i) = 0 := by
    have fDAtZero : ⇑(fderiv ℝ f 0) = 0 := by simpa [f, Dw, u0W] using u0WAtZero x hx
    simp [fDAtZero]
  let φ (t : ℝ) : ℝ^n := f (t * w)

end BrendleHung.Section2
