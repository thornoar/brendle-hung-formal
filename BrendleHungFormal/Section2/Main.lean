import BrendleHungFormal.Section2.Work

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

noncomputable section

/-- Main result: `U` has a third-order expansion with locally bounded remainder on `B r0`. -/
theorem expansion_of_U :
  ∃ s0 : ℝ, s0 > 0 ∧
  HasExpansion3 (B asm.r0) s0 0 0 bud.U2 bud.U3 bud.U
:= by
  classical
  let ρU : ℝ^m × ℝ → ℝ := fun q =>
    if q.2 = 0 then 0 else
      (bud.U q.1 q.2 - q.2 ^ 2 * bud.U2 q.1 - q.2 ^ 3 * bud.U3 q.1) / q.2 ^ 4
  refine ⟨asm.s0, asm.hs0, ρU, ?_, ?_⟩
  · intro p hp
    have hpD : inBounds p := B_subset_D hp
    have hO : (fun s : ℝ =>
        bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p)
        =O[𝓝 (0 : ℝ)] (fun s : ℝ => s ^ 4) := by
      refine (u_remainder_isBigO p hpD).congr' ?_
        (Filter.Eventually.of_forall fun _ => rfl)
      filter_upwards [bud_U_eq_u_wStarAt_eventually p hpD] with s hs
      rw [hs]
    rcases (Asymptotics.isBigO_iff.mp hO) with ⟨c, hc⟩
    refine ⟨max c 0, ?_⟩
    have hCnonneg : 0 ≤ max c 0 := le_max_right c 0
    filter_upwards [hc] with s hs
    by_cases hs0 : s = 0
    · simp [ρU, hs0, hCnonneg]
    · have hs4_ne : s ^ 4 ≠ 0 := pow_ne_zero 4 hs0
      have hs4_pos : 0 < ‖s ^ 4‖ := norm_pos_iff.mpr hs4_ne
      have hc' : ‖bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p‖
          ≤ (max c 0) * ‖s ^ 4‖ := by
        exact le_trans hs
          (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _))
      have hdiv : ‖bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p‖ / ‖s ^ 4‖
          ≤ max c 0 := by
        exact (div_le_iff₀ hs4_pos).2 hc'
      rw [show ρU (p, s) =
          (bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p) / s ^ 4 by
        simp [ρU, hs0]]
      rw [abs_div]
      simpa [Real.norm_eq_abs] using hdiv
  · intro p s hp hs
    have hpD : inBounds p := B_subset_D hp
    by_cases hs0 : s = 0
    · subst s
      simp [ρU, bud_U_zero p hpD]
    · have hs4_ne : s ^ 4 ≠ 0 := pow_ne_zero 4 hs0
      simp [ρU, hs0]
      field_simp [hs4_ne]
      ring

/-- The paper's `derivative.of.U2`: the coordinate derivative of `U^(2)` is the
coordinate derivative of `u^(2)` plus the two critical-point correction terms. -/
lemma derivative_U2 (x : ℝ^m) (hx : inBounds x) (i : Fin m) :
    fderiv ℝ bud.U2 x (e i : ℝ^m)
      = fderiv ℝ (fun y : ℝ^m => asm.u2 y 0) x (e i : ℝ^m)
        + ∑ α : Fin n,
            (fderiv ℝ (fun y : ℝ^m => u1W y 0 (e α)) x (e i : ℝ^m)) * bud.barw x α
        + (1 / 2 : ℝ) * ∑ α : Fin n, ∑ β : Fin n,
            (fderiv ℝ (fun y : ℝ^m => u0WW y 0 α β) x (e i : ℝ^m))
              * bud.barw x α * bud.barw x β
:= by
  classical
  let A : Fin n → ℝ := fun α => u1W x 0 (e α)
  let A' : Fin n → ℝ := fun α =>
    fderiv ℝ (fun y : ℝ^m => u1W y 0 (e α)) x (e i : ℝ^m)
  let B : Fin n → ℝ := bud.barw x
  let B' : Fin n → ℝ := fun β =>
    fderiv ℝ (fun y : ℝ^m => bud.barw y β) x (e i : ℝ^m)
  let C : Matrix (Fin n) (Fin n) ℝ := u0WW x 0
  let C' : Matrix (Fin n) (Fin n) ℝ := fun α β =>
    fderiv ℝ (fun y : ℝ^m => u0WW y 0 α β) x (e i : ℝ^m)

  have hBdiff : DifferentiableAt ℝ bud.barw x :=
    (barw_contDiffAt x hx).differentiableAt (by simp)
  have hBd (β : Fin n) : DifferentiableAt ℝ (fun y : ℝ^m => bud.barw y β) x := by
    fun_prop
  have hAd (α : Fin n) : DifferentiableAt ℝ (fun y : ℝ^m => u1W y 0 (e α)) x :=
    (u1W_smooth_apply α).differentiable (by simp) x
  have hCd (α β : Fin n) : DifferentiableAt ℝ (fun y : ℝ^m => u0WW y 0 α β) x :=
    (u0WW_smooth_apply α β).differentiable (by simp) x
  have hu2Smooth : SmoothGlobal (fun y : ℝ^m => asm.u2 y 0) := by
    have hcomp : SmoothGlobal (fun y : ℝ^m => (y, (0 : ℝ^n))) := by fun_prop
    simpa [Function.comp_def, Function.uncurry_def] using asm.u2Smooth.comp hcomp
  have hu2d : DifferentiableAt ℝ (fun y : ℝ^m => asm.u2 y 0) x :=
    hu2Smooth.differentiable (by simp) x

  have hdetx : (u0WW x 0).det ≠ 0 := by
    have hunitDet : IsUnit (u0WW x 0).det :=
      (Matrix.isUnit_iff_isUnit_det (u0WW x 0)).mp (u0WWAtZero x hx).isUnit
    exact hunitDet.ne_zero
  have hMat : Continuous (fun y : ℝ^m => u0WW y 0) :=
    continuous_matrix (fun α β => (u0WW_smooth_apply α β).continuous)
  have hdetEv : ∀ᶠ y : ℝ^m in 𝓝 x, (u0WW y 0).det ≠ 0 :=
    hMat.matrix_det.continuousAt.eventually_ne hdetx

  have hrowD (α : Fin n) :
      ∑ β : Fin n, (C α β * B' β + C' α β * B β) = -A' α := by
    have hmuld (β : Fin n) : DifferentiableAt ℝ
        (fun y : ℝ^m => u0WW y 0 α β * bud.barw y β) x := (hCd α β).mul (hBd β)
    have hsumd : DifferentiableAt ℝ
        (fun y : ℝ^m => ∑ β : Fin n, u0WW y 0 α β * bud.barw y β) x := by
      fun_prop
    have hEqEv :
        (fun y : ℝ^m => ∑ β : Fin n, u0WW y 0 α β * bud.barw y β + u1W y 0 (e α))
          =ᶠ[𝓝 x] (fun _ : ℝ^m => 0) := by
      filter_upwards [hdetEv] with y hy
      have hspec := congrFun (barw_spec_of_det_ne_zero y hy) α
      have hspec' : ∑ β : Fin n, u0WW y 0 α β * bud.barw y β
          = -u1W y 0 (e α) := by
        simpa [Matrix.mulVec, dotProduct, u1WVec] using hspec
      rw [hspec']
      ring
    have hfd : fderiv ℝ
        (fun y : ℝ^m => ∑ β : Fin n, u0WW y 0 α β * bud.barw y β + u1W y 0 (e α)) x
        = (∑ β : Fin n,
            ((u0WW x 0 α β) • fderiv ℝ (fun y : ℝ^m => bud.barw y β) x
              + (bud.barw x β) • fderiv ℝ (fun y : ℝ^m => u0WW y 0 α β) x))
          + fderiv ℝ (fun y : ℝ^m => u1W y 0 (e α)) x := by
      rw [fderiv_fun_add hsumd (hAd α)]
      rw [fderiv_fun_sum (u := Finset.univ) (fun β _ => hmuld β)]
      have hmul_fd (β : Fin n) :
          fderiv ℝ (fun y : ℝ^m => u0WW y 0 α β * bud.barw y β) x
            = (u0WW x 0 α β) • fderiv ℝ (fun y : ℝ^m => bud.barw y β) x
              + (bud.barw x β) • fderiv ℝ (fun y : ℝ^m => u0WW y 0 α β) x :=
        fderiv_fun_mul (hCd α β) (hBd β)
      simp_rw [hmul_fd]
    have hzero : fderiv ℝ
        (fun y : ℝ^m => ∑ β : Fin n, u0WW y 0 α β * bud.barw y β + u1W y 0 (e α)) x = 0 := by
      rw [hEqEv.fderiv_eq]
      simp
    have h := congrArg (fun L : ℝ^m →L[ℝ] ℝ => L (e i : ℝ^m)) (hfd.symm.trans hzero)
    have h' : (∑ β : Fin n, (C α β * B' β + C' α β * B β)) + A' α = 0 := by
      simpa [A', B', B, C, C', Finset.sum_apply, add_comm, add_left_comm, add_assoc,
        mul_comm] using h
    linarith

  have hcoeff : fderiv ℝ bud.U2 x (e i : ℝ^m)
      = fderiv ℝ (fun y : ℝ^m => asm.u2 y 0) x (e i : ℝ^m)
        + (1 / 2 : ℝ) * ∑ α : Fin n, (A' α * B α + A α * B' α) := by
    have hmuld (α : Fin n) : DifferentiableAt ℝ
        (fun y : ℝ^m => u1W y 0 (e α) * bud.barw y α) x := (hAd α).mul (hBd α)
    have hsumd : DifferentiableAt ℝ
        (fun y : ℝ^m => ∑ α : Fin n, u1W y 0 (e α) * bud.barw y α) x := by
      fun_prop
    have hhalfd : DifferentiableAt ℝ
        (fun y : ℝ^m => (1 / 2 : ℝ) * ∑ α : Fin n, u1W y 0 (e α) * bud.barw y α) x := by
      fun_prop
    change fderiv ℝ (fun y : ℝ^m => asm.u2 y 0 + (1 / 2 : ℝ) *
        ∑ α : Fin n, u1W y 0 (e α) * bud.barw y α) x (e i : ℝ^m) = _
    rw [fderiv_fun_add hu2d hhalfd]
    rw [fderiv_const_mul hsumd (1 / 2 : ℝ)]
    rw [fderiv_fun_sum (u := Finset.univ) (fun α _ => hmuld α)]
    have hmul_fd (α : Fin n) :
        fderiv ℝ (fun y : ℝ^m => u1W y 0 (e α) * bud.barw y α) x
          = (u1W x 0 (e α)) • fderiv ℝ (fun y : ℝ^m => bud.barw y α) x
            + (bud.barw x α) • fderiv ℝ (fun y : ℝ^m => u1W y 0 (e α)) x :=
      fderiv_fun_mul (hAd α) (hBd α)
    simp_rw [hmul_fd]
    simp [A, A', B, B', Finset.sum_apply, add_comm, mul_comm]

  have hCB (α : Fin n) : ∑ β : Fin n, C α β * B β = -A α := by
    have h := congrFun (barw_spec x hx) α
    simpa [C, B, A, Matrix.mulVec, dotProduct] using h
  have hAeq (α : Fin n) : A α = -∑ β : Fin n, C α β * B β := by
    have h := hCB α
    linarith
  have hC_symm (α β : Fin n) : C α β = C β α := by
    simpa [C] using u0WW_symm x α β

  have hS : ∑ α : Fin n, A α * B' α
      = ∑ α : Fin n, A' α * B α
        + ∑ α : Fin n, ∑ β : Fin n, C' α β * B α * B β := by
    calc
      ∑ α : Fin n, A α * B' α
          = -∑ α : Fin n, ∑ β : Fin n, C α β * B β * B' α := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro α _
            rw [hAeq α, neg_mul, Finset.sum_mul]
      _ = -∑ β : Fin n, B β * (∑ α : Fin n, C β α * B' α) := by
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro β _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro α _
            rw [hC_symm α β]
            ring
      _ = -∑ β : Fin n, B β * (-A' β - ∑ α : Fin n, C' β α * B α) := by
            congr 1
            apply Finset.sum_congr rfl
            intro β _
            have hrow : ∑ α : Fin n, C β α * B' α
                = -A' β - ∑ α : Fin n, C' β α * B α := by
              have hsplit : (∑ γ : Fin n, C β γ * B' γ)
                  + (∑ γ : Fin n, C' β γ * B γ) = -A' β := by
                rw [← Finset.sum_add_distrib]
                exact hrowD β
              linarith
            rw [hrow]
      _ = ∑ β : Fin n, (A' β * B β + ∑ α : Fin n, C' β α * B β * B α) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro β _
            calc
              -(B β * (-A' β - ∑ α : Fin n, C' β α * B α))
                  = A' β * B β + B β * (∑ α : Fin n, C' β α * B α) := by
                    ring
              _ = A' β * B β + ∑ α : Fin n, B β * (C' β α * B α) := by
                    rw [Finset.mul_sum]
              _ = A' β * B β + ∑ α : Fin n, C' β α * B β * B α := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro α _
                    ring
      _ = ∑ α : Fin n, A' α * B α
            + ∑ α : Fin n, ∑ β : Fin n, C' α β * B α * B β := by
            rw [Finset.sum_add_distrib]

  have hfinal : fderiv ℝ bud.U2 x (e i : ℝ^m)
      = fderiv ℝ (fun y : ℝ^m => asm.u2 y 0) x (e i : ℝ^m)
        + ∑ α : Fin n, A' α * B α
        + (1 / 2 : ℝ) * ∑ α : Fin n, ∑ β : Fin n, C' α β * B α * B β := by
    rw [hcoeff, Finset.sum_add_distrib, hS]
    ring
  simpa [A, A', B, C'] using hfinal

/-- The cyclic error term in the third `z`-derivative formula for `v0`. -/
abbrev v0T (y : ℝ^m) (α β γ : Fin n) : ℝ :=
  (∑ δ : Fin n, ∑ ζ : Fin n,
    Υc y 0 * u0WW y 0 δ ζ * zD1 (ψc y) γ δ * zD2 (ψc y) α β ζ) +
  (∑ i : Fin m, ∑ δ : Fin n, ∑ ζ : Fin n,
    Υc y 0 * u0XWW y i δ ζ * zD1 (φc y) γ i *
      zD1 (ψc y) α δ * zD1 (ψc y) β ζ) +
  (∑ δ : Fin n, ∑ ζ : Fin n,
    zD1 (Υc y) γ * u0WW y 0 δ ζ *
      zD1 (ψc y) α δ * zD1 (ψc y) β ζ)

/-- The function `v0` vanishes at `z=0`. -/
lemma v0_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : ccd.v0 y 0 = 0
:= by
  change Υc y 0 * v0B y 0 = 0
  rw [v0B_zero y hy]
  simp

/-- The first `z`-derivative of `v0` vanishes at zero. -/
lemma zD1_v0 (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (ccd.v0 y) α = 0
:= by
  change zD1 (fun z : ℝ^n => Υc y z * v0B y z) α = 0
  have h := zD1_mul_at (Υc y) (v0B y) 0
    (upsilon_z_smoothAt y hy) (v0B_smoothAt y hy) α
  simpa [zD1, v0B_zero y hy, zD1_v0B y hy α] using h

/-- The second `z`-derivative formula for `v0` at zero. -/
lemma zD2_v0 (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (ccd.v0 y) α β =
      ∑ γ : Fin n, ∑ δ : Fin n,
        Υc y 0 * u0WW y 0 γ δ *
          zD1 (ψc y) α γ * zD1 (ψc y) β δ
:= by
  rw [zD2_v0_prod y hy α β, zD2_v0B_expanded y hy α β]
  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- The third `z`-derivative formula for `v0` at zero. -/
lemma zD3_v0 (y : ℝ^m) (hy : y ∈ cca.Ω) (α β γ : Fin n) :
    zD3 (ccd.v0 y) α β γ =
      (∑ δ : Fin n, ∑ ζ : Fin n, ∑ η : Fin n,
        Υc y 0 * u0WWW y 0 δ ζ η *
          zD1 (ψc y) α δ * zD1 (ψc y) β ζ * zD1 (ψc y) γ η) +
      v0T y α β γ + v0T y β γ α + v0T y γ α β
:= by
  rw [zD3_v0_prod y hy α β γ, zD3_v0B_expanded y hy α β γ]
  rw [zD2_symm (v0B y) (v0B_smoothAt y hy) α γ]
  rw [zD2_v0B_expanded y hy β γ, zD2_v0B_expanded y hy γ α,
    zD2_v0B_expanded y hy α β]
  simp only [mul_add, Finset.mul_sum, mul_assoc, v0T]
  abel


/-- The term `S_{αβ}` in the second `z`-derivative formula for `v1`. -/
abbrev v1S (y : ℝ^m) (α β : Fin n) : ℝ :=
  (∑ i : Fin m, ∑ γ : Fin n,
    Υc y 0 *
      (u1XW y i γ * zD1 (ψc y) β γ * zD1 (φc y) α i)) +
  (∑ γ : Fin n,
    zD1 (Υc y) α * (u1W y 0 (e γ) * zD1 (ψc y) β γ))

/-- The function `v1` vanishes at `z=0`. -/
lemma v1_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : ccd.v1 y 0 = 0
:= by
  change Υc y 0 * u1B y 0 = 0
  rw [u1B_zero y hy]
  simp

/-- The first `z`-derivative formula for `v1` at zero. -/
lemma zD1_v1 (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (ccd.v1 y) α =
      ∑ γ : Fin n,
        Υc y 0 * u1W y 0 (e γ) * zD1 (ψc y) α γ
:= by
  rw [zD1_v1_prod y hy α, u1B_zero y hy, zD1_u1B_expanded y hy α]
  simp [Finset.mul_sum, mul_assoc]

/-- The second `z`-derivative formula for `v1` at zero. -/
lemma zD2_v1 (y : ℝ^m) (hy : y ∈ cca.Ω) (α β : Fin n) :
    zD2 (ccd.v1 y) α β =
      (∑ γ : Fin n, ∑ δ : Fin n,
        Υc y 0 * (u1WW y 0 γ δ *
          zD1 (ψc y) α γ * zD1 (ψc y) β δ)) +
      (∑ γ : Fin n,
        Υc y 0 * (u1W y 0 (e γ) * zD2 (ψc y) α β γ)) +
      v1S y α β + v1S y β α
:= by
  rw [zD2_v1_prod y hy α β, zD2_u1B_expanded y hy α β,
    zD1_u1B_expanded y hy β, zD1_u1B_expanded y hy α]
  simp only [mul_add, Finset.mul_sum, v1S]
  abel

/-- The value of `v2` at `z=0`. -/
lemma v2_zero (y : ℝ^m) (hy : y ∈ cca.Ω) :
    ccd.v2 y 0 = Υc y 0 * asm.u2 y 0 := by
  change Υc y 0 * u2B y 0 = Υc y 0 * asm.u2 y 0
  rw [u2B_zero y hy]

/-- The first `z`-derivative formula for `v2` at zero. -/
lemma zD1_v2 (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    zD1 (ccd.v2 y) α =
      (∑ β : Fin n,
        Υc y 0 * u2W y 0 (e β) * zD1 (ψc y) α β) +
      (∑ i : Fin m,
        Υc y 0 * u2X y i * zD1 (φc y) α i) +
      zD1 (Υc y) α * asm.u2 y 0
:= by
  rw [zD1_v2_prod y hy α, zD1_u2B_expanded y hy α, u2B_zero y hy]
  simp only [mul_add, Finset.mul_sum, mul_assoc]

/-- The relation between `bar w` and `bar z`: applying the `ψ` Jacobian to `bar z` gives `bar w`. -/
lemma relation_barw_barz (y : ℝ^m) (hy : y ∈ cca.Ω) (α : Fin n) :
    ∑ β : Fin n, zD1 (ψc y) β α * barz y β = bud.barw y α
:= by
  rw [barz_eq_barzViaPsi y hy]
  exact barzViaPsi_spec y hy α

/-- The paper's second-order coefficient after the coordinate change. -/
abbrev V2 (y : ℝ^m) : ℝ :=
  ccd.v2 y 0 + (1 / 2 : ℝ) * ∑ α : Fin n, zD1 (ccd.v1 y) α * barz y α

/-- The paper's `relation.between.U2.and.V2`. -/
lemma relation_U2_V2 (y : ℝ^m) (hy : y ∈ cca.Ω) :
    V2 y = Υc y 0 * bud.U2 y
:= by
  classical
  have hsum :
      (∑ α : Fin n, zD1 (ccd.v1 y) α * barz y α) =
        ∑ β : Fin n, Υc y 0 * u1W y 0 (e β) * bud.barw y β := by
    calc
      ∑ α : Fin n, zD1 (ccd.v1 y) α * barz y α
          = ∑ β : Fin n, Υc y 0 * u1W y 0 (e β) *
              (∑ α : Fin n, zD1 (ψc y) α β * barz y α) := by
            simp_rw [zD1_v1 y hy, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro β _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro α _
            ring
      _ = ∑ β : Fin n, Υc y 0 * u1W y 0 (e β) * bud.barw y β := by
            simp_rw [relation_barw_barz y hy]
  have hsumΥ :
      (∑ β : Fin n, Υc y 0 * u1W y 0 (e β) * bud.barw y β) =
        Υc y 0 * ∑ β : Fin n, u1W y 0 (e β) * bud.barw y β := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    ring
  change ccd.v2 y 0 + (1 / 2 : ℝ) * (∑ α : Fin n, zD1 (ccd.v1 y) α * barz y α) =
    Υc y 0 *
      (asm.u2 y 0 + (1 / 2 : ℝ) *
        ∑ β : Fin n, u1W y 0 (e β) * bud.barw y β)
  rw [v2_zero y hy, hsum, hsumΥ]
  ring

end

end Section2
