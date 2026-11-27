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

/-- The function `v1` vanishes at `z=0`. -/
lemma v1_zero (y : ℝ^m) (hy : y ∈ cca.Ω) : ccd.v1 y 0 = 0
:= by
  change Υc y 0 * u1B y 0 = 0
  rw [u1B_zero y hy]
  simp

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


/-- The paper's third-order coefficient after the coordinate change. -/
abbrev V3 (y : ℝ^m) : ℝ :=
  ccd.v3 y 0
    + ∑ α : Fin n, zD1 (ccd.v2 y) α * barz y α
    + (1 / 2 : ℝ) * ∑ α : Fin n, ∑ β : Fin n,
        zD2 (ccd.v1 y) α β * barz y α * barz y β
    + (1 / 6 : ℝ) * ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
        zD3 (ccd.v0 y) α β γ * barz y α * barz y β * barz y γ

/-- The paper's `relation.between.U3.and.V3`. -/
lemma relation_U3_V3 (y : ℝ^m) (hy : y ∈ cca.Ω) :
    V3 y =
      Υc y 0 * bud.U3 y
        + (∑ i : Fin m, ∑ γ : Fin n,
            Υc y 0 * fderiv ℝ bud.U2 y (e i : ℝ^m) *
              zD1 (φc y) γ i * barz y γ)
        + (∑ γ : Fin n, zD1 (Υc y) γ * bud.U2 y * barz y γ) := by
  classical
  have hyD : inBounds y := B_subset_D (cca.Ω_subset_B hy)
  have h1 :
      (∑ β : Fin n, u2W y 0 (e β) * bud.barw y β) =
        diff (asm.u2 y) 0 (bud.barw y) := by
    simpa [u2W, mul_comm] using
      (clm_apply_eq_sum_basis (diff (asm.u2 y) 0) (bud.barw y)).symm
  have h2 :
      (∑ γ : Fin n, ∑ δ : Fin n,
        u1WW y 0 γ δ * bud.barw y γ * bud.barw y δ) =
        diff2 (asm.u1 y) 0 (bud.barw y) (bud.barw y) := by
    simpa [u1WW, mul_comm, mul_left_comm, mul_assoc] using
      (bilinear_apply_eq_sum_basis (diff2 (asm.u1 y) 0)
        (bud.barw y) (bud.barw y)).symm
  have h3 :
      (∑ δ : Fin n, ∑ ζ : Fin n, ∑ η : Fin n,
        u0WWW y 0 δ ζ η * bud.barw y δ * bud.barw y ζ * bud.barw y η) =
        diff3 (asm.u0 y) 0 (bud.barw y) (bud.barw y) (bud.barw y) := by
    simpa [u0WWW, mul_comm, mul_left_comm, mul_assoc] using
      (trilinear_apply_eq_sum_basis (diff3 (asm.u0 y) 0)
        (bud.barw y) (bud.barw y) (bud.barw y)).symm
  have hBud :
      Υc y 0 * bud.U3 y =
        Υc y 0 * asm.u3 y 0
        + (∑ β : Fin n, Υc y 0 * u2W y 0 (e β) * bud.barw y β)
        + (1 / 2 : ℝ) * (∑ γ : Fin n, ∑ δ : Fin n,
            Υc y 0 * u1WW y 0 γ δ * bud.barw y γ * bud.barw y δ)
        + (1 / 6 : ℝ) * (∑ δ : Fin n, ∑ ζ : Fin n, ∑ η : Fin n,
            Υc y 0 * u0WWW y 0 δ ζ η *
              bud.barw y δ * bud.barw y ζ * bud.barw y η) := by
    rw [bud_U3_eq y hyD, ← h1, ← h2, ← h3]
    simp_rw [mul_add, mul_assoc, Finset.mul_sum]
    ring_nf
  have hAneg :
      (∑ α : Fin n, ∑ β : Fin n, ∑ δ : Fin n, ∑ ζ : Fin n,
        Υc y 0 * u0WW y 0 δ ζ * zD2 (ψc y) α β ζ *
          barz y α * barz y β * bud.barw y δ)
        = - (∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n,
              Υc y 0 * u1W y 0 (e γ) * zD2 (ψc y) α β γ *
                barz y α * barz y β) := by
    linarith [u0WW_psi_cancel y hy]
  have hCneg :
      (∑ γ : Fin n, ∑ δ : Fin n, ∑ ζ : Fin n,
        zD1 (Υc y) γ * u0WW y 0 δ ζ *
          bud.barw y δ * bud.barw y ζ * barz y γ)
        = - (∑ α : Fin n, ∑ γ : Fin n,
              zD1 (Υc y) α * u1W y 0 (e γ) * barz y α * bud.barw y γ) := by
    linarith [u0WW_Upsilon_cancel y hy]
  have hcross := U2_deriv_barz_contract y hy
  have hUpsilon := U2_Upsilon_barz_contract y hy
  have hR :
      (∑ γ : Fin n, zD1 (Υc y) γ * asm.u2 y 0 * barz y γ) =
        ∑ γ : Fin n, asm.u2 y 0 * zD1 (Υc y) γ * barz y γ := by
    apply Finset.sum_congr rfl
    intro γ _
    ring
  have hF :
      (∑ α : Fin n, ∑ γ : Fin n,
        zD1 (Υc y) α * u1W y 0 (e γ) * barz y α * bud.barw y γ) =
        ∑ α : Fin n, ∑ γ : Fin n,
          zD1 (Υc y) γ * u1W y 0 (e α) * bud.barw y α * barz y γ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro γ _
    ring
  unfold V3
  rw [v3_zero y hy, v2_barz_linear y hy, v1_barz_quad y hy, v0_barz_cubic y hy]
  rw [hBud, hcross, hUpsilon]
  rw [hAneg, hCneg]
  ring_nf
  rw [hR, hF]
  abel

/-- The paper's invariance proposition.  On the zero set of `V2` and `dV2`,
the third-order coefficient agrees with `Υ(y,0) * U3(y)`, and the reciprocal
rescaling is the restriction of the smooth function `U3` on `D r0`. -/
theorem invariance (Λ : Set ℝ^m) (hΛΩ : Λ ⊆ cca.Ω)
    (hV2 : ∀ y ∈ Λ, V2 y = 0 ∧ fderiv ℝ V2 y = 0) :
    (∀ y ∈ Λ, V3 y = Υc y 0 * bud.U3 y) ∧
      ∃ F : ℝ^m → ℝ, SmoothOn F (D asm.r0) ∧
        ∀ y ∈ Λ, (Υc y 0)⁻¹ * V3 y = F y
:= by
  classical
  have hzero : (0 : ℝ^n) ∈ B cca.r1 := by
    simpa [B, BrendleHung.Section2.Multivar.norm] using cca.r1_pos
  have hU2_data : ∀ y ∈ Λ, bud.U2 y = 0 ∧ fderiv ℝ bud.U2 y = 0 := by
    intro y hyΛ
    have hyΩ : y ∈ cca.Ω := hΛΩ hyΛ
    have hyD : inBounds y := B_subset_D (cca.Ω_subset_B hyΩ)
    have hΥpos : 0 < Υc y 0 := by
      simpa [Υc] using cca.Υ_pos y 0 hyΩ hzero
    have hΥne : Υc y 0 ≠ 0 := ne_of_gt hΥpos
    have hU2zero : bud.U2 y = 0 := by
      have hrel := relation_U2_V2 y hyΩ
      rw [(hV2 y hyΛ).1] at hrel
      exact (mul_eq_zero.mp hrel.symm).resolve_left hΥne
    have hEqEv : V2 =ᶠ[𝓝 y] fun y' : ℝ^m => Υc y' 0 * bud.U2 y' := by
      filter_upwards [cca.Ω_open.mem_nhds hyΩ] with y' hy'
      exact relation_U2_V2 y' hy'
    have hfderivEq :
        fderiv ℝ V2 y = fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y :=
      hEqEv.fderiv_eq
    have hΥdiff : DifferentiableAt ℝ (fun y' : ℝ^m => Υc y' 0) y :=
      (upsilon_y0_contDiffAt y hyΩ).differentiableAt (by simp)
    have hU2diff : DifferentiableAt ℝ bud.U2 y :=
      (bud_U2_contDiffAt y hyD).differentiableAt (by simp)
    have hprod :
        fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y =
          (Υc y 0) • fderiv ℝ bud.U2 y +
            (bud.U2 y) • fderiv ℝ (fun y' : ℝ^m => Υc y' 0) y := by
      exact (hΥdiff.hasFDerivAt.mul hU2diff.hasFDerivAt).fderiv
    have hprodZero :
        fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y = 0 := by
      simpa [hfderivEq] using (hV2 y hyΛ).2
    have hscale : (Υc y 0) • fderiv ℝ bud.U2 y = 0 := by
      simpa [hprod, hU2zero] using hprodZero
    have hU2deriv : fderiv ℝ bud.U2 y = 0 :=
      (smul_eq_zero.mp hscale).resolve_left hΥne
    exact ⟨hU2zero, hU2deriv⟩
  have hV3_eq : ∀ y ∈ Λ, V3 y = Υc y 0 * bud.U3 y := by
    intro y hyΛ
    have hU2 := hU2_data y hyΛ
    simpa [hU2.1, hU2.2] using relation_U3_V3 y (hΛΩ hyΛ)
  refine ⟨hV3_eq, ?_⟩
  refine ⟨bud.U3, bud_U3_smoothOn_D, ?_⟩
  intro y hyΛ
  have hyΩ : y ∈ cca.Ω := hΛΩ hyΛ
  have hΥpos : 0 < Υc y 0 := by
    simpa [Υc] using cca.Υ_pos y 0 hyΩ hzero
  have hΥne : Υc y 0 ≠ 0 := ne_of_gt hΥpos
  rw [hV3_eq y hyΛ]
  field_simp [hΥne]

end

end Section2
