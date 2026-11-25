import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/- import Mathlib.Analysis.Asymptotics.Defs -/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
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

-- The cubic truncation used in the Section 2 expansion.
def taylor3From (f0 f1 f2 f3 : ℝ^m -> ℝ^n -> ℝ) (x : ℝ^m) (w : ℝ^n) (s : ℝ) : ℝ :=
  f0 x w + s * f1 x w + s ^ 2 * f2 x w + s ^ 3 * f3 x w

-- A Lean-friendly `O(s^4)` hypothesis for `u(x,w,s) = u0 + s u1 + s^2 u2 + s^3 u3 + O(s^4)`.
def HasExpansion3 (f0 f1 f2 f3 : ℝ^m -> ℝ^n -> ℝ) (f : ℝ^m → ℝ^n → ℝ → ℝ) : Prop :=
  ∃ ρ : ℝ^m → ℝ^n → ℝ → ℝ,
    ∀ x w s,
      f x w s = taylor3From f0 f1 f2 f3 x w s + s ^ 4 * ρ x w s

open Function (uncurry)
notation "Smooth" => ContDiff ℝ (⊤ : ℕ∞)
variable {m n : ℕ}

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
  r0 : ℝ
  hr0 : r0 > 0
  s0 : ℝ
  hs0 : s0 > 0
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
  -- h0PositiveDefinite : ∀ x : ℝ^m,
  --   x ∈ closedBall m r0 →
  --   Matrix.PosDef (data.u0WW x 0)

variable (ua : InitialAssumptions)

noncomputable abbrev Dw (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n) : (ℝ^n →L[ℝ] ℝ) :=
  fderiv ℝ (f x) w

noncomputable abbrev Dww (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n)
: (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ))
:= fderiv ℝ (Dw f x) w

noncomputable abbrev Dwww (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n)
: (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)))
:= fderiv ℝ (Dww f x) w

def e (i : Fin n) : ℝ^n := Pi.single i 1

noncomputable def u0W (x : ℝ^m) (w : ℝ^n) (i : Fin n) : ℝ
:= Dw ua.data.u0 x w (e i)

noncomputable def u1W (x : ℝ^m) (w : ℝ^n) (i : Fin n) : ℝ
:= Dw ua.data.u1 x w (e i)

noncomputable def u2W (x : ℝ^m) (w : ℝ^n) (i : Fin n) : ℝ
:= Dw ua.data.u2 x w (e i)

noncomputable def u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => Dww ua.data.u0 x w (e i) (e j)

noncomputable def u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => Dww ua.data.u1 x w (e i) (e j)

noncomputable def u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ
:= Dwww ua.data.u0 x w (e i) (e j) (e k)



end BrendleHung.Section2
