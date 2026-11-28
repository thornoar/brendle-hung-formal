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

/-- The raw functions and radii from the beginning of Section 2. -/
class InitialDefinitions where
  r0 : ℝ
  s0 : ℝ
  σ : ℝ
  u : ℝ^m -> ℝ^n -> ℝ -> ℝ
  u0 : ℝ^m -> ℝ^n -> ℝ
  u1 : ℝ^m -> ℝ^n -> ℝ
  u2 : ℝ^m -> ℝ^n -> ℝ
  u3 : ℝ^m -> ℝ^n -> ℝ

/-- Hypotheses on the initial data: positivity, smoothness, normalization,
a quadratic lower bound, and a smooth third-order expansion. -/
structure InitialAssumptions extends InitialDefinitions where
  hr0 : r0 > 0
  hs0 : s0 > 0
  hσ : σ > 0
  u0Smooth : SmoothGlobal (↓u0)
  uSmooth : SmoothGlobal (fun (x, w, s) => u x w s)
  u0AtZero : ∀ x : ℝ^m, x ∈ D r0 -> u0 x 0 = 0
  u0Quadratic :
    ∀ x : ℝ^m, ∀ w : ℝ^n,
      x ∈ D r0 →
      w ∈ D r0 →
      u0 x w ≥ σ * (norm w ^ 2)
  u1Smooth : SmoothGlobal (↓u1)
  u1AtZero : ∀ x : ℝ^m, x ∈ D r0 -> u1 x 0 = 0
  u2Smooth : SmoothGlobal (↓u2)
  u3Smooth : SmoothGlobal (↓u3)
  uExp : HasSmoothExpansion3 (D r0 ×ˢ D r0) s0
          (↓u0) (↓u1) (↓u2) (↓u3)
          (↓u)

/-- The Section 2 hypotheses are a typeclass so that the Euclidean results can
 later be applied to different local coordinate charts. -/
class InitialAssumptionsInst extends InitialAssumptions

/-- The active choice of the Section 2 hypotheses. -/
abbrev asm [i : InitialAssumptionsInst] : InitialAssumptionsInst := i

variable [InitialAssumptionsInst]

/-- The closed coordinate ball used as the domain for parameters and `w` variables. -/
abbrev inBounds {m : ℕ} (x : ℝ^m) : Prop
:= x ∈ D asm.r0

noncomputable section

/-- Derivative of `u0(x, ·)` at `w`, as a continuous linear functional. -/
abbrev u0W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (asm.u0 x) w

/-- Derivative of `u1(x, ·)` at `w`, as a continuous linear functional. -/
abbrev u1W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (asm.u1 x) w

/-- Derivative of `u2(x, ·)` at `w`, as a continuous linear functional. -/
abbrev u2W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (asm.u2 x) w

/-- Hessian matrix of `u0(x, ·)` at `w` in the standard basis. -/
abbrev u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (asm.u0 x) w (e i) (e j)

/-- Hessian matrix of `u1(x, ·)` at `w` in the standard basis. -/
abbrev u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (asm.u1 x) w (e i) (e j)

/-- Third derivative tensor component of `u0(x, ·)` at `w` in the standard basis. -/
abbrev u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ
:= diff3 (asm.u0 x) w (e i) (e j) (e k)

/-- Bundle holding the reduced function `U`, its direction `barw`, and its second- and third-order coefficients. -/
structure BigUDefinitions where
  U : ℝ^m -> ℝ -> ℝ
  barw : ℝ^m -> ℝ^n
  U2 : ℝ^m -> ℝ
  U3 : ℝ^m -> ℝ

-- The following four definitions correspond to the objects introduced in
-- Section 2 of the paper: U(x,s), \bar w(x), U^{(2)}(x), and U^{(3)}(x).

/-- The reduced function `U`, its minimizing direction `barw`, and the second-
and third-order coefficients `U2` and `U3`. -/
noncomputable def bud : BigUDefinitions :=
  let barw x := (u0WW x 0)⁻¹ *ᵥ (fun α : Fin n => - u1W x 0 (e α))
  {
    U x s := ⨅ w : D (d := n) asm.r0, asm.u x w s
    barw := barw
    U2 x := asm.u2 x 0 + ((1 : ℝ) / 2) * ∑ α : Fin n, u1W x 0 (e α) * barw x α
    U3 x :=
      asm.u3 x 0
       + ∑ α : Fin n, u2W x 0 (e α) * barw x α
       + ((1 : ℝ) / 2) * ∑ α : Fin n, ∑ β : Fin n,
           u1WW x 0 α β * barw x α * barw x β
       + ((1 : ℝ) / 6) * ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
           u0WWW x 0 α β γ * barw x α * barw x β * barw x γ
  }

end

/-- Jacobian matrix of the `z`-variables of a smooth map `F`, at `(y, 0)`. The
`β`-th row and `α`-th column record the derivative of `F^β` in the `z^α`
direction, matching the paper's `(ψ^β_{z^α}(y,0))` convention. -/
noncomputable def zJacobian (F : ℝ^m × ℝ^n → ℝ^n) (y : ℝ^m) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun β α => fderiv ℝ (fun z : ℝ^n => F (y, z) β) 0 (e α : ℝ^n)

/-- Locally smooth coordinate changes and the invertibility hypothesis from Section 2. -/
structure CoordChangeAssumptions where
  Ω : Set ℝ^m
  Ω_open : IsOpen Ω
  Ω_subset_B : Ω ⊆ B asm.r0
  r1 : ℝ
  r1_pos : r1 > 0
  r1_le_r0 : r1 ≤ asm.r0

  Υ : ℝ^m × ℝ^n → ℝ
  Υ_pos : ∀ y, ∀ z,
    y ∈ Ω → z ∈ B r1 → Υ (y, z) > 0
  Υ_smooth : Smooth Υ on (Ω ×ˢ B r1)

  φ : ℝ^m × ℝ^n → ℝ^m
  φ_smooth : Smooth φ on (Ω ×ˢ B r1)
  φ_y_0 : ∀ y, y ∈ Ω → φ (y, 0) = y

  ψ : ℝ^m × ℝ^n → ℝ^n
  ψ_smooth : Smooth ψ on (Ω ×ˢ B r1)
  ψ_y_0 : ∀ y, y ∈ Ω → ψ (y, 0) = 0

  ψ_jacobian_inv : ∀ y, y ∈ Ω → IsUnit (zJacobian ψ y)

/-- The Section 2 coordinate-change hypotheses are a typeclass as well. -/
class CoordChangeAssumptionsInst extends CoordChangeAssumptions

/-- The active choice of the Section 2 coordinate-change hypotheses. -/
abbrev cca [i : CoordChangeAssumptionsInst] : CoordChangeAssumptionsInst := i

variable [CoordChangeAssumptionsInst]

/-- The four rescaled functions `v^(0)`, `v^(1)`, `v^(2)`, and `v^(3)`
introduced in Section 2 after the coordinate change. -/
structure CoordChangeDefinitions where
  v0 : ℝ^m → ℝ^n → ℝ
  v1 : ℝ^m → ℝ^n → ℝ
  v2 : ℝ^m → ℝ^n → ℝ
  v3 : ℝ^m → ℝ^n → ℝ

/-- The coordinate-change definitions associated to the chosen smooth changes
`Υ`, `φ`, and `ψ`: `v^(k)(y,z) = Υ(y,z) u^(k)(φ(y,z), ψ(y,z))`. -/
noncomputable def ccd : CoordChangeDefinitions where
  v0 := fun y z => cca.Υ (y, z) * asm.u0 (cca.φ (y, z)) (cca.ψ (y, z))
  v1 := fun y z => cca.Υ (y, z) * asm.u1 (cca.φ (y, z)) (cca.ψ (y, z))
  v2 := fun y z => cca.Υ (y, z) * asm.u2 (cca.φ (y, z)) (cca.ψ (y, z))
  v3 := fun y z => cca.Υ (y, z) * asm.u3 (cca.φ (y, z)) (cca.ψ (y, z))

end Section2
