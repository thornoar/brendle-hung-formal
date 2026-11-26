import BrendleHungFormal.Section2.Multivar

open Function (uncurry)

section BrendleHung.Section2

open BrendleHung.Section2.Multivar

-- Keep the short name `norm` for the coordinate-space norm in this file,
-- without clashing with Mathlib's global `norm`.
local notation "norm" => BrendleHung.Section2.Multivar.norm

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

abbrev u0W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (ua.data.u0 x) w

abbrev u1W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (ua.data.u1 x) w

abbrev u2W (x : ℝ^m) (w : ℝ^n) : ℝ^n -> ℝ
:= diff (ua.data.u2 x) w

abbrev u0WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (ua.data.u0 x) w (e i) (e j)

abbrev u1WW (x : ℝ^m) (w : ℝ^n) : Matrix (Fin n) (Fin n) ℝ
:= Matrix.of fun i j => diff2 (ua.data.u1 x) w (e i) (e j)

abbrev u0WWW (x : ℝ^m) (w : ℝ^n) (i j k : Fin n) : ℝ
:= diff3 (ua.data.u0 x) w (e i) (e j) (e k)

end

lemma u0WAtZero (x : ℝ^m) (hx : inBounds x) : u0W x 0 = 0
:= by
  have hAtZero : ua.data.u0 x 0 = 0 := ua.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ openBall n ua.data.r0 →
      ua.data.u0 x w ≥ ua.σ * (norm w ^ 2) := by
    intro w hw
    exact ua.u0Quadratic x w hx (by simpa [openBall, closedBall] using le_of_lt hw)
  have hderiv := ineq_zero_deriv (ua.data.u0 x) ua.data.r0 ua.hr0 ua.σ ua.hσ hAtZero hquad
  ext w
  simpa [u0W] using congrArg (fun L : ℝ^n →L[ℝ] ℝ => L w) hderiv

lemma u0WWAtZero (x : ℝ^m) (hx : inBounds x) : Matrix.PosDef (u0WW x 0)
:= by
  have hAtZero : ua.data.u0 x 0 = 0 := ua.u0AtZero x hx
  have hquad : ∀ w : ℝ^n, w ∈ openBall n ua.data.r0 →
      ua.data.u0 x w ≥ ua.σ * (norm w ^ 2) := by
    intro w hw
    exact ua.u0Quadratic x w hx (by simpa [openBall, closedBall] using le_of_lt hw)
  have hsmooth : Smooth (ua.data.u0 x) := by
    simpa [Function.comp_def, Function.uncurry_def] using
      (ua.u0Smooth.comp (contDiff_prodMk_right (𝕜 := ℝ) (n := ⊤) x))
  simpa [u0WW, matrixOf] using
    (ineq_pos_def (ua.data.u0 x) ua.data.r0 ua.hr0 ua.σ ua.hσ
      hsmooth hAtZero hquad)

end Section2
