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

/-- The open ball `B_r^d` in coordinate space. -/
def openBall (d : ℕ) (r : ℝ) : Set (ℝ^d) :=
  {x | norm x < r}

/-- The closed ball `\bar B_r^d` in coordinate space. -/
def closedBall (d : ℕ) (r : ℝ) : Set (ℝ^d) :=
  {x | norm x ≤ r}

open Function (uncurry)

notation "Smooth" => ContDiff ℝ (⊤ : ℕ∞)

variable {m n : ℕ}

variable (u0 : ℝ^m -> ℝ^n -> ℝ)
variable (u1 : ℝ^m -> ℝ^n -> ℝ)
variable (u2 : ℝ^m -> ℝ^n -> ℝ)
variable (u3 : ℝ^m -> ℝ^n -> ℝ)

noncomputable abbrev Dw (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n) : (ℝ^n →L[ℝ] ℝ) :=
  fderiv ℝ (f x) w

-- noncomputable abbrev Dw (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n) : (ℝ^n →L[ℝ] ℝ) :=
--      fderiv ℝ (f x) w

noncomputable abbrev Dww (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n) :
    (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ)) :=
  fderiv ℝ (Dw (m := m) (n := n) f x) w

noncomputable abbrev Dwww (f : ℝ^m → ℝ^n → ℝ) (x : ℝ^m) (w : ℝ^n) :
    (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] (ℝ^n →L[ℝ] ℝ))) :=
  fderiv ℝ (Dww (m := m) (n := n) f x) w

def e (i : Fin n) : ℝ^n := Pi.single i 1

noncomputable def u0W (x : ℝ^m) (w : ℝ^n) (i : Fin n) : ℝ :=
  Dw u0 x w (e i)

noncomputable def u1W (x : ℝ^m) (w : ℝ^n) (i : Fin n) : ℝ :=
  Dw (m := m) (n := n) u1 x w (e i)

noncomputable def u2W (x : ℝ^m) (w : ℝ^n) (i : Fin n) : ℝ :=
  Dw (m := m) (n := n) u2 x w (e i)

noncomputable def u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Dww (m := m) (n := n) u0 x w (e i) (e j)

noncomputable def u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Dww (m := m) (n := n) u1 x w (e i) (e j)

noncomputable def u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ :=
  Dwww (m := m) (n := n) u0 x w (e i) (e j) (e k)



end BrendleHung.Section2
