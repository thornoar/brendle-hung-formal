/- structure UData where -/
/-   u0 : ℝ^m → ℝ^n → ℝ -/
/-   u1 : ℝ^m → ℝ^n → ℝ -/
/-   u2 : ℝ^m → ℝ^n → ℝ -/
/-   u3 : ℝ^m → ℝ^n → ℝ -/
/-   u0W : ℝ^m → ℝ^n → Fin n → ℝ -/
/-   u1W : ℝ^m → ℝ^n → Fin n → ℝ -/
/-   u2W : ℝ^m → ℝ^n → Fin n → ℝ -/
/-   u0WW : ℝ^m → ℝ^n → Matrix (Fin n) (Fin n) ℝ -/
/-   u1WW : ℝ^m → ℝ^n → Matrix (Fin n) (Fin n) ℝ -/
/-   u0WWW : ℝ^m → ℝ^n → Fin n → Fin n → Fin n → ℝ -/

/- structure UAssumptions where -/
/-   data : UData m n -/
/-   r0 : ℝ -/
/-   hr0 : r0 > 0 -/
/-   s0 : ℝ -/
/-   hs0 : s0 > 0 -/
/-   σ : ℝ -/
/-   hσ : σ > 0 -/
/-   u0Smooth : Smooth (uncurry data.u0) -/
/-   u0AtZero : ∀ x : ℝ^m, -/
/-     x ∈ closedBall m r0 → -/
/-     data.u0 x 0 = 0 -/
/-   u0Quadratic : ∀ x : ℝ^m, ∀ w : ℝ^n, -/
/-     x ∈ closedBall m r0 → -/
/-     w ∈ closedBall n r0 → -/
/-     data.u0 x w ≥ σ * (norm w ^ 2) -/
/-   u1Smooth : Smooth (uncurry data.u0) -/
/-   u1AtZero : ∀ x : ℝ^m, data.u1 x 0 = 0 -/
/-   u2Smooth : Smooth (uncurry data.u0) -/
/-   u3Smooth : Smooth (uncurry data.u0) -/
/-   h0PositiveDefinite : ∀ x : ℝ^m, -/
/-     x ∈ closedBall m r0 → -/
/-     Matrix.PosDef (data.u0WW x 0) -/
