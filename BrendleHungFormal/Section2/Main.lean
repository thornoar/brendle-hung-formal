import BrendleHungFormal.Section2.Work
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Function (uncurry)
open Filter
open scoped BigOperators Matrix Topology Manifold ContDiff

section BrendleHung.Section2

variable [InitialAssumptionsInst] [CoordChangeAssumptionsInst]

open BrendleHung.Section2.Multivar
open BrendleHung.Section2.TaylorAsymptotics

-- Keep the short name `norm` for the coordinate-space norm in this file,
-- without clashing with Mathlib's global `norm`.
local notation "norm" => BrendleHung.Section2.Multivar.norm
local notation "↓" f => uncurry f

noncomputable section

omit [CoordChangeAssumptionsInst] in
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
  simp [v0B_zero y hy]

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
  simp [u1B_zero y hy]

/-- The paper's second-order coefficient after the coordinate change. -/
abbrev V2 (y : ℝ^m) : ℝ :=
  ccd.v2 y 0 + (1 / 2 : ℝ) * ∑ α : Fin n, zD1 (ccd.v1 y) α * barz y α

/-- The paper's `relation.between.U2.and.V2`. -/
lemma relation_U2_V2 (y : ℝ^m) (hy : y ∈ cca.Ω) :
    V2 y = Υc y 0 * bud.U2 y
:= by
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
  have hR :
      (∑ γ : Fin n, zD1 (Υc y) γ * asm.u2 y 0 * barz y γ) =
        ∑ γ : Fin n, asm.u2 y 0 * zD1 (Υc y) γ * barz y γ := by
    ac_rfl
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
  rw [hBud, U2_deriv_barz_contract y hy, U2_Upsilon_barz_contract y hy]
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
  have hU2_data : ∀ y ∈ Λ, bud.U2 y = 0 ∧ fderiv ℝ bud.U2 y = 0 := by
    intro y hyΛ
    have hyΩ : y ∈ cca.Ω := hΛΩ hyΛ
    have hyD : inBounds y := B_subset_D (cca.Ω_subset_B hyΩ)
    have hΥne : Υc y 0 ≠ 0 := ne_of_gt (upsilon_y0_pos y hyΩ)
    have hU2zero : bud.U2 y = 0 := by
      have hrel := relation_U2_V2 y hyΩ
      rw [(hV2 y hyΛ).1] at hrel
      exact (mul_eq_zero.mp hrel.symm).resolve_left hΥne
    have hEqEv : V2 =ᶠ[𝓝 y] fun y' : ℝ^m => Υc y' 0 * bud.U2 y' := by
      filter_upwards [cca.Ω_open.mem_nhds hyΩ] with y' hy'
      exact relation_U2_V2 y' hy'
    have hprodZero :
        fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y = 0 := by
      rw [← hEqEv.fderiv_eq]
      exact (hV2 y hyΛ).2
    have hscale : (Υc y 0) • fderiv ℝ bud.U2 y = 0 := by
      simpa [fderiv_upsilon0_mul_U2 y hyΩ hyD, hU2zero] using hprodZero
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
  have hΥne : Υc y 0 ≠ 0 := ne_of_gt (upsilon_y0_pos y (hΛΩ hyΛ))
  rw [hV3_eq y hyΛ]
  field_simp [hΥne]


namespace BrendleHung.Section2


/-- The paper's positivity corollary.  The hypothesis `hrem` is the uniform
form on `A` of the remainder bound in `expansion_of_U`. -/
theorem positivity
    (ρ : ℝ^m → ℝ) (hρ_nonneg : ∀ y ∈ D asm.r0, 0 ≤ ρ y)
    (hρ_cont : ContinuousOn ρ (D asm.r0))
    (κ : ℝ) (hκ : 0 < κ)
    (hV2Ω : ∀ y ∈ cca.Ω, κ * Υc y 0 * ρ y ≤ V2 y)
    (hV3Ω : ∀ y ∈ cca.Ω, ρ y = 0 → V2 y = 0 ∧ κ * Υc y 0 ≤ V3 y)
    (A : Set ℝ^m) (hAne : A.Nonempty) (hAcompact : IsCompact A)
    (hAD : A ⊆ D asm.r0) (hAclos : A ⊆ closure cca.Ω)
    (hA0clos : A ∩ {y | ρ y = 0} ⊆ closure (cca.Ω ∩ {y | ρ y = 0}))
    (C : ℝ) (hC : 0 ≤ C)
    (hrem : ∀ y ∈ A, ∀ s ∈ Set.Ioc (0 : ℝ) asm.s0,
      |bud.U y s - s ^ 2 * bud.U2 y - s ^ 3 * bud.U3 y| ≤ C * s ^ 4) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 ≤ asm.s0 ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) s1, 0 < sInf ((fun y => bud.U y s) '' A)) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) s1, ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ A, δ ≤ bud.U y s)
:= by
  classical
  rcases hAne with ⟨y0, hy0A⟩
  have hΩD : cca.Ω ⊆ D asm.r0 := fun y hy => B_subset_D (cca.Ω_subset_B hy)
  have hU2_ge_Ω : ∀ y ∈ cca.Ω, κ * ρ y ≤ bud.U2 y := by
    intro y hy
    have hΥ := upsilon_y0_pos y hy
    have hV := hV2Ω y hy
    rw [relation_U2_V2 y hy] at hV
    have hV' : Υc y 0 * (κ * ρ y) ≤ Υc y 0 * bud.U2 y := by nlinarith
    exact (mul_le_mul_iff_of_pos_left hΥ).mp hV'
  have hU2_ge_A : ∀ y ∈ A, κ * ρ y ≤ bud.U2 y := by
    intro y hyA
    have hyD : inBounds y := hAD hyA
    have hρw : ContinuousWithinAt ρ cca.Ω y :=
      (show ContinuousWithinAt ρ (D asm.r0) y from hρ_cont y hyD).mono hΩD
    have hκρw : ContinuousWithinAt (fun z : ℝ^m => κ * ρ z) cca.Ω y :=
      continuousWithinAt_const.mul hρw
    have hU2w : ContinuousWithinAt bud.U2 cca.Ω y :=
      (bud_U2_contDiffAt y hyD).continuousAt.continuousWithinAt
    exact ContinuousWithinAt.closure_le (hAclos hyA) hκρw hU2w hU2_ge_Ω
  have hV2_nonneg : ∀ y ∈ cca.Ω, 0 ≤ V2 y := by
    intro y hy
    have hρy : 0 ≤ ρ y := hρ_nonneg y (hΩD hy)
    have hcoef : 0 ≤ κ * Υc y 0 :=
      mul_nonneg (le_of_lt hκ) (le_of_lt (upsilon_y0_pos y hy))
    nlinarith [hV2Ω y hy, mul_nonneg hcoef hρy]
  have hU2_nonneg : ∀ y ∈ cca.Ω, 0 ≤ bud.U2 y := by
    intro y hy
    have hρy : 0 ≤ ρ y := hρ_nonneg y (hΩD hy)
    nlinarith [hU2_ge_Ω y hy, mul_nonneg (le_of_lt hκ) hρy]
  let Λ : Set ℝ^m := cca.Ω ∩ {y | ρ y = 0}
  have hΛΩ : Λ ⊆ cca.Ω := fun y hy => hy.1
  have hV2_data : ∀ y ∈ Λ, V2 y = 0 ∧ fderiv ℝ V2 y = 0 := by
    intro y hyΛ
    have hyΩ : y ∈ cca.Ω := hyΛ.1
    have hyD : inBounds y := hΩD hyΩ
    have hΥne : Υc y 0 ≠ 0 := ne_of_gt (upsilon_y0_pos y hyΩ)
    have hV2zero : V2 y = 0 := (hV3Ω y hyΩ hyΛ.2).1
    have hU2zero : bud.U2 y = 0 := by
      have hrel := relation_U2_V2 y hyΩ
      rw [hV2zero] at hrel
      exact (mul_eq_zero.mp hrel.symm).resolve_left hΥne
    have hlocal : IsLocalMin bud.U2 y := by
      filter_upwards [cca.Ω_open.mem_nhds hyΩ] with z hz
      simpa [hU2zero] using hU2_nonneg z hz
    have hdU2 : fderiv ℝ bud.U2 y = 0 := hlocal.fderiv_eq_zero
    have hEqEv : V2 =ᶠ[𝓝 y] fun y' : ℝ^m => Υc y' 0 * bud.U2 y' := by
      filter_upwards [cca.Ω_open.mem_nhds hyΩ] with y' hy'
      exact relation_U2_V2 y' hy'
    refine ⟨hV2zero, ?_⟩
    calc
      fderiv ℝ V2 y = fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y := hEqEv.fderiv_eq
      _ = 0 := by
        simp [fderiv_upsilon0_mul_U2 y hyΩ hyD, hU2zero, hdU2]
  have hV3eqΛ : ∀ y ∈ Λ, V3 y = Υc y 0 * bud.U3 y :=
    (invariance Λ hΛΩ hV2_data).1
  have hU3_ge_Λ : ∀ y ∈ Λ, κ ≤ bud.U3 y := by
    intro y hyΛ
    have hΥ : 0 < Υc y 0 := upsilon_y0_pos y hyΛ.1
    have hV := (hV3Ω y hyΛ.1 hyΛ.2).2
    rw [hV3eqΛ y hyΛ] at hV
    have hV' : Υc y 0 * κ ≤ Υc y 0 * bud.U3 y := by nlinarith
    exact (mul_le_mul_iff_of_pos_left hΥ).mp hV'
  have hU3_ge_A0 : ∀ y ∈ A ∩ {y | ρ y = 0}, κ ≤ bud.U3 y := by
    intro y hy
    have hyD : inBounds y := hAD hy.1
    have hκw : ContinuousWithinAt (fun _ : ℝ^m => κ)
        (cca.Ω ∩ {z | ρ z = 0}) y := continuousWithinAt_const
    have hU3w : ContinuousWithinAt bud.U3 (cca.Ω ∩ {z | ρ z = 0}) y :=
      (bud_U3_contDiffAt y hyD).continuousAt.continuousWithinAt
    exact ContinuousWithinAt.closure_le (hA0clos hy) hκw hU3w hU3_ge_Λ
  have hBadClosed : IsClosed ((D asm.r0) ∩ {y | bud.U3 y ≤ κ / 2}) := by
    exact (isClosed_D asm.r0).isClosed_le bud_U3_smoothOn_D.continuousOn continuousOn_const
  let Bad : Set ℝ^m := A ∩ ((D asm.r0) ∩ {y | bud.U3 y ≤ κ / 2})
  have hBadCompact : IsCompact Bad := hAcompact.inter_right hBadClosed
  have hU3_cont_A : ContinuousOn bud.U3 A :=
    bud_U3_smoothOn_D.continuousOn.mono hAD
  have hε : ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ A, ρ y ≤ ε → κ / 2 ≤ bud.U3 y := by
    by_cases hne : Bad.Nonempty
    · rcases hBadCompact.exists_isMinOn hne (hρ_cont.mono (by
        intro z hz
        exact hz.2.1)) with ⟨yb, hyb, hybmin⟩
      have hybA : yb ∈ A := hyb.1
      have hybD : inBounds yb := hyb.2.1
      have hybU3 : bud.U3 yb ≤ κ / 2 := hyb.2.2
      have hρbpos : 0 < ρ yb := by
        have hρbnonneg : 0 ≤ ρ yb := hρ_nonneg yb hybD
        have hρbne : ρ yb ≠ 0 := by
          intro hρbzero
          have hge := hU3_ge_A0 yb ⟨hybA, hρbzero⟩
          nlinarith
        exact lt_of_le_of_ne hρbnonneg (Ne.symm hρbne)
      refine ⟨ρ yb / 2, by positivity, ?_⟩
      intro y hyA hyρε
      by_contra hnot
      have hyU3 : bud.U3 y ≤ κ / 2 := le_of_not_ge hnot
      have hyBad : y ∈ Bad := ⟨hyA, hAD hyA, hyU3⟩
      have hmin : ρ yb ≤ ρ y := hybmin hyBad
      nlinarith
    · refine ⟨1, by norm_num, ?_⟩
      intro y hyA _
      by_contra hnot
      apply hne
      exact ⟨y, ⟨hyA, hAD hyA, le_of_not_ge hnot⟩⟩
  rcases hε with ⟨ε, hεpos, hU3ε⟩
  rcases hAcompact.exists_bound_of_continuousOn hU3_cont_A with ⟨M, hM⟩
  let M0 : ℝ := max M 0
  have hM0nonneg : 0 ≤ M0 := le_max_right M 0
  have hU3abs : ∀ y ∈ A, |bud.U3 y| ≤ M0 := by
    intro y hyA
    have h := hM y hyA
    have habs : |bud.U3 y| ≤ M := by simpa [Real.norm_eq_abs] using h
    exact habs.trans (le_max_left M 0)
  let K : ℝ := M0 + C
  have hKnonneg : 0 ≤ K := add_nonneg hM0nonneg hC
  let s1 : ℝ := min asm.s0 (min 1 (min (κ / (4 * (C + 1)))
    (κ * ε / (2 * (K + 1)))))
  have hden1 : 0 < 4 * (C + 1) := by positivity
  have hden2 : 0 < 2 * (K + 1) := by positivity
  have hs1pos : 0 < s1 := by
    have hk1pos : 0 < κ / (4 * (C + 1)) := div_pos hκ hden1
    have hk2pos : 0 < κ * ε / (2 * (K + 1)) := div_pos (mul_pos hκ hεpos) hden2
    dsimp [s1]
    exact lt_min asm.hs0 (lt_min zero_lt_one (lt_min hk1pos hk2pos))
  have hs1le_s0 : s1 ≤ asm.s0 := by
    dsimp [s1]
    exact min_le_left _ _
  have hs1le_one : s1 ≤ 1 := by
    dsimp [s1]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hs1le_k1 : s1 ≤ κ / (4 * (C + 1)) := by
    dsimp [s1]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs1le_k2 : s1 ≤ κ * ε / (2 * (K + 1)) := by
    dsimp [s1]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hmain : ∀ s ∈ Set.Ioc (0 : ℝ) s1,
      (0 < sInf ((fun y => bud.U y s) '' A)) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ A, δ ≤ bud.U y s) := by
    intro s hs
    have hspos : 0 < s := hs.1
    have hss1 : s ≤ s1 := hs.2
    have hsasm : s ∈ Set.Ioc (0 : ℝ) asm.s0 := ⟨hspos, hss1.trans hs1le_s0⟩
    have hspow3 : 0 < s ^ 3 := pow_pos hspos 3
    have hspow3nonneg : 0 ≤ s ^ 3 := le_of_lt hspow3
    have hs4le3 : s ^ 4 ≤ s ^ 3 := by
      have hsle1 : s ≤ 1 := hss1.trans hs1le_one
      nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) (le_of_lt hspos)]
    have hCs_le : C * s ≤ κ / 4 := by
      have hsle : s ≤ κ / (4 * (C + 1)) := hss1.trans hs1le_k1
      have hmul : s * (4 * (C + 1)) ≤ κ := by
        calc
          s * (4 * (C + 1)) ≤ (κ / (4 * (C + 1))) * (4 * (C + 1)) :=
            mul_le_mul_of_nonneg_right hsle (le_of_lt hden1)
          _ = κ := by field_simp [ne_of_gt hden1]
      have hCsmall : C * s ≤ (C + 1) * s := by nlinarith [le_of_lt hspos]
      nlinarith
    have hK_le : K * s ≤ κ * ε / 2 := by
      have hsle : s ≤ κ * ε / (2 * (K + 1)) := hss1.trans hs1le_k2
      have hmul : s * (2 * (K + 1)) ≤ κ * ε := by
        calc
          s * (2 * (K + 1)) ≤ (κ * ε / (2 * (K + 1))) * (2 * (K + 1)) :=
            mul_le_mul_of_nonneg_right hsle (le_of_lt hden2)
          _ = κ * ε := by field_simp [ne_of_gt hden2]
      have hKsmall : K * s ≤ (K + 1) * s := by nlinarith [le_of_lt hspos]
      nlinarith
    have hsmall₁ : 0 < (κ / 4) * s ^ 3 := mul_pos (by positivity) hspow3
    have hsmall₂ : 0 < (κ * ε / 2) * s ^ 2 := by positivity
    have hlower : ∀ y ∈ A,
        min ((κ / 4) * s ^ 3) ((κ * ε / 2) * s ^ 2) ≤ bud.U y s := by
      intro y hyA
      have hUy := hrem y hyA s hsasm
      have hUlower : s ^ 2 * bud.U2 y + s ^ 3 * bud.U3 y - C * s ^ 4 ≤ bud.U y s := by
        have hneg := (abs_le.mp hUy).1
        linarith
      by_cases hρε : ρ y ≤ ε
      · have hρy : 0 ≤ ρ y := hρ_nonneg y (hAD hyA)
        have hU2y : 0 ≤ bud.U2 y := by
          have h := hU2_ge_A y hyA
          nlinarith [mul_nonneg (le_of_lt hκ) hρy]
        have hU3y : κ / 2 ≤ bud.U3 y := hU3ε y hyA hρε
        have hU3term : s ^ 3 * (κ / 2) ≤ s ^ 3 * bud.U3 y :=
          mul_le_mul_of_nonneg_left hU3y hspow3nonneg
        have hCterm : C * s ^ 4 ≤ (κ / 4) * s ^ 3 := by
          have hc := mul_le_mul_of_nonneg_right hCs_le hspow3nonneg
          nlinarith
        have hsmall : (κ / 4) * s ^ 3 ≤ bud.U y s := by
          have hU2term : 0 ≤ s ^ 2 * bud.U2 y :=
            mul_nonneg (sq_nonneg s) hU2y
          nlinarith
        exact (min_le_left _ _).trans hsmall
      · have hρε' : ε < ρ y := lt_of_not_ge hρε
        have hU2y : κ * ε ≤ bud.U2 y := by
          have h := hU2_ge_A y hyA
          have hmul := mul_le_mul_of_nonneg_left (le_of_lt hρε') (le_of_lt hκ)
          exact hmul.trans h
        have hU3y : -M0 ≤ bud.U3 y := (abs_le.mp (hU3abs y hyA)).1
        have hU2term : s ^ 2 * (κ * ε) ≤ s ^ 2 * bud.U2 y :=
          mul_le_mul_of_nonneg_left hU2y (sq_nonneg s)
        have hU3term : -(M0 * s ^ 3) ≤ s ^ 3 * bud.U3 y := by
          have h := mul_le_mul_of_nonneg_left hU3y hspow3nonneg
          nlinarith
        have hCterm0 : C * s ^ 4 ≤ C * s ^ 3 :=
          mul_le_mul_of_nonneg_left hs4le3 hC
        have hKterm : M0 * s ^ 3 + C * s ^ 3 ≤ (κ * ε / 2) * s ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hK_le (sq_nonneg s)
          dsimp [K] at h
          nlinarith
        have hsmall : (κ * ε / 2) * s ^ 2 ≤ bud.U y s := by
          nlinarith
        exact (min_le_right _ _).trans hsmall
    have hcpos : 0 < min ((κ / 4) * s ^ 3) ((κ * ε / 2) * s ^ 2) :=
      lt_min hsmall₁ hsmall₂
    have himage_nonempty : ((fun y => bud.U y s) '' A).Nonempty :=
      ⟨bud.U y0 s, ⟨y0, hy0A, rfl⟩⟩
    have hInfge : min ((κ / 4) * s ^ 3) ((κ * ε / 2) * s ^ 2) ≤
        sInf ((fun y => bud.U y s) '' A) := by
      apply le_csInf himage_nonempty
      rintro z ⟨y, hyA, rfl⟩
      exact hlower y hyA
    exact ⟨lt_of_lt_of_le hcpos hInfge,
      min ((κ / 4) * s ^ 3) ((κ * ε / 2) * s ^ 2), hcpos, hlower⟩
  refine ⟨s1, hs1pos, hs1le_s0, ?_, ?_⟩
  · intro s hs
    exact (hmain s hs).1
  · intro s hs
    exact (hmain s hs).2

end BrendleHung.Section2

namespace BrendleHung.Section2.Manifold

open Function Filter
open BrendleHung.Section2
open BrendleHung.Section2.Multivar

variable [InitialAssumptionsInst] [CoordChangeAssumptionsInst]

/-- The coordinate model of the submanifold `𝒵` (dimension `m`). -/
abbrev modelZ := 𝓘(ℝ, Fin m → ℝ)

/-- The coordinate model of the ambient manifold `𝒩` (dimension `m + n`). -/
abbrev modelN := 𝓘(ℝ, (Fin m → ℝ) × (Fin n → ℝ))

/-- The coordinate model of the real line. -/
abbrev modelR := 𝓘(ℝ, ℝ)

/-- Promote Euclidean Section 2 data to the typeclasses used by the
 Euclidean results. -/
@[reducible] def localA (a : InitialAssumptions) : InitialAssumptionsInst :=
  InitialAssumptionsInst.mk a

@[reducible] def localC (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a)) :
    @CoordChangeAssumptionsInst (localA a) :=
  @CoordChangeAssumptionsInst.mk (localA a) c

/-- Explicit projections from chart data with its own Euclidean instance. -/
abbrev Ωof (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a)) : Set (Fin m → ℝ) :=
  @CoordChangeAssumptions.Ω (localA a) c

abbrev r1of (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a)) : ℝ :=
  @CoordChangeAssumptions.r1 (localA a) c

abbrev Υof (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (q : (Fin m → ℝ) × (Fin n → ℝ)) : ℝ :=
  @CoordChangeAssumptions.Υ (localA a) c q

/-- The paper's `V⁽²⁾` and `V⁽³⁾` for a specified pair of Euclidean data. -/
abbrev V2_of (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (y : Fin m → ℝ) : ℝ := @V2 (localA a) (localC a c) y

abbrev V3_of (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (y : Fin m → ℝ) : ℝ := @V3 (localA a) (localC a c) y


omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The scalar factor `Υ(y,0)` with explicit Euclidean data. -/
abbrev Υc_of (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (y : Fin m → ℝ) (z : Fin n → ℝ) : ℝ := @Υc (localA a) (localC a c) y z

/-- The reduced second- and third-order coefficients and the reduced function
with explicit Euclidean data. -/
abbrev budU_of (a : InitialAssumptions) (y : Fin m → ℝ) (s : ℝ) : ℝ := (@bud (localA a)).U y s

abbrev budU2_of (a : InitialAssumptions) (y : Fin m → ℝ) : ℝ := (@bud (localA a)).U2 y

abbrev budU3_of (a : InitialAssumptions) (y : Fin m → ℝ) : ℝ := (@bud (localA a)).U3 y

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
lemma Υc_of_eq (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (y : Fin m → ℝ) (z : Fin n → ℝ) : Υc_of a c y z = Υof a c (y, z) := rfl

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- Smoothness of the local third-order coefficient on its coordinate ball. -/
lemma budU3_of_smoothOn_D (a : InitialAssumptions) :
    ContMDiffOn modelZ modelR (⊤ : WithTop ℕ∞) (budU3_of a) (D (d := m) a.r0) := by
  simpa [modelZ, modelR, budU3_of] using
    (contMDiffOn_iff_contDiffOn.mpr
      (@bud_U3_smoothOn_D (localA a)))

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The Euclidean invariance proposition applied to explicit local data. -/
lemma invariance_local (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (Λe : Set (Fin m → ℝ)) (hΛeΩ : Λe ⊆ Ωof a c)
    (hcrit : ∀ y ∈ Λe, V2_of a c y = 0 ∧ fderiv ℝ (V2_of a c) y = 0) :
    (∀ y ∈ Λe, V3_of a c y = Υc_of a c y 0 * budU3_of a y) ∧
      ∃ F : (Fin m → ℝ) → ℝ, ContDiffOn ℝ (⊤ : WithTop ℕ∞) F (D (d := m) a.r0) ∧
        ∀ y ∈ Λe, (Υc_of a c y 0)⁻¹ * V3_of a c y = F y := by
  simpa [V2_of, V3_of, Υc_of, budU3_of, localC] using
    (@invariance (localA a) (localC a c) Λe hΛeΩ hcrit)

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The origin belongs to the normal-coordinate ball of a chart. -/
lemma zero_mem_B_r1_of (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a)) :
    (0 : Fin n → ℝ) ∈ B (d := n) (r1of a c) := by
  simpa [B, BrendleHung.Section2.Multivar.norm] using
    (@CoordChangeAssumptions.r1_pos (localA a) c)

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- Positivity of `Υ(y,0)` with explicit local data. -/
lemma upsilon_y0_pos_of (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (y : Fin m → ℝ) (hy : y ∈ Ωof a c) : 0 < Υc_of a c y 0 := by
  simpa [Υc_of, localC] using
    (@upsilon_y0_pos (localA a) (localC a c) y hy)

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The reduced function is bounded above by every admissible trial value. -/
lemma budU_of_le_u (a : InitialAssumptions)
    (y : Fin m → ℝ) (s : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ D (d := n) (a.r0)) :
    budU_of a y s ≤ a.u y w s := by
  letI : InitialAssumptionsInst := localA a
  rcases (@exists_minimizer (localA a) y s) with ⟨w0, hw0, hmin, hU⟩
  rw [show budU_of a y s = a.u y w0 s by simpa [budU_of] using hU]
  exact hmin hw

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The Euclidean positivity corollary applied to explicit local data. -/
lemma positivity_local
    (a : InitialAssumptions) (c : @CoordChangeAssumptions (localA a))
    (ρe : (Fin m → ℝ) → ℝ)
    (hρ_nonneg : ∀ y ∈ D (d := m) (a.r0), 0 ≤ ρe y)
    (hρ_cont : ContinuousOn ρe (D (d := m) (a.r0)))
    (κ : ℝ) (hκ : 0 < κ)
    (hV2Ω : ∀ y ∈ Ωof a c, κ * Υc_of a c y 0 * ρe y ≤ V2_of a c y)
    (hV3Ω : ∀ y ∈ Ωof a c, ρe y = 0 →
      V2_of a c y = 0 ∧ κ * Υc_of a c y 0 ≤ V3_of a c y)
    (A : Set (Fin m → ℝ)) (hAne : A.Nonempty) (hAcompact : IsCompact A)
    (hAD : A ⊆ D (d := m) (a.r0)) (hAclos : A ⊆ closure (Ωof a c))
    (hA0clos : A ∩ {y | ρe y = 0} ⊆
      closure (Ωof a c ∩ {y | ρe y = 0}))
    (C : ℝ) (hC : 0 ≤ C)
    (hrem : ∀ y ∈ A, ∀ s ∈ Set.Ioc (0 : ℝ) (a.s0),
      |budU_of a y s - s ^ 2 * budU2_of a y - s ^ 3 * budU3_of a y| ≤
        C * s ^ 4) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 ≤ a.s0 ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) s1, 0 < sInf ((fun y => budU_of a y s) '' A)) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) s1, ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ A, δ ≤ budU_of a y s) := by
  simpa [V2_of, V3_of, Υc_of, budU_of, budU2_of, budU3_of, localC] using
    (@BrendleHung.Section2.positivity (localA a) (localC a c) ρe
      hρ_nonneg hρ_cont κ hκ hV2Ω hV3Ω A hAne hAcompact hAD hAclos
      hA0clos C hC hrem)

/-- The global data of the last two theorems of Section 2.  The metric on
`𝒩` is the Riemannian distance; `ι : 𝒵 ↪ 𝒩` is the inclusion of the
submanifold, and `d(p, 𝒵)` is `Metric.infDist p (Set.range ι)`. -/
structure GlobalData (N Z : Type*) [MetricSpace N] [TopologicalSpace Z] where
  ι : Z → N
  ι_inj : Injective ι

  u : N → ℝ → ℝ
  u0 : N → ℝ
  u1 : N → ℝ
  u2 : N → ℝ
  u3 : N → ℝ

  Υ : Z → (Fin n → ℝ) → ℝ
  V2 : Z → ℝ
  V3 : Z → ℝ
  ρ : Z → ℝ

  /-- The open set `Ω ⊆ 𝒵` and the critical set `Λ ⊆ Ω`. -/
  Ω : Set Z
  Λ : Set Z
  Λ_subset_Ω : Λ ⊆ Ω

  σ : ℝ
  s0 : ℝ
  κ : ℝ
  C : ℝ

  hσ : 0 < σ
  hs0 : 0 < s0
  hκ : 0 < κ
  hC : 0 ≤ C

  hι_cont : Continuous ι
  hρ_cont : Continuous ρ
  hu1_cont : Continuous u1
  hu2_cont : Continuous u2
  hu3_cont : Continuous u3

  hNcompact : IsCompact (Set.univ : Set N)
  hZcompact : IsCompact (Set.univ : Set Z)

  hu_rem :
    ∀ p : N, ∀ s ∈ Set.Ioc (0 : ℝ) s0,
      |u p s - u0 p - s * u1 p - s ^ 2 * u2 p - s ^ 3 * u3 p| ≤ C * s ^ 4
  hu0_zero : ∀ z : Z, u0 (ι z) = 0
  hu1_zero : ∀ z : Z, u1 (ι z) = 0
  hu0_lower : ∀ p : N, σ * (Metric.infDist p (Set.range ι)) ^ 2 ≤ u0 p
  hρ_nonneg : ∀ z : Z, 0 ≤ ρ z

  /-- The Euclidean positivity hypotheses transported to `Ω ⊆ 𝒵`. -/
  hV2_lower : ∀ z ∈ Ω, κ * Υ z 0 * ρ z ≤ V2 z
  hV3_lower : ∀ z ∈ Ω, ρ z = 0 → V2 z = 0 ∧ κ * Υ z 0 ≤ V3 z
  hΩ_dense : ∀ z : Z, z ∈ closure Ω
  hρ0_dense : ∀ z : Z, ρ z = 0 → z ∈ closure (Ω ∩ {z | ρ z = 0})

/-- A chart of `𝒩` adapted to `𝒵`, together with Euclidean Section 2 data
`a` and `c` describing `u` and the change of coordinates `Υ`, `Φ` on the
chart.  Its fields are the local translations of the hypotheses of the paper
`smooth.extension` and `positivity.manifold.version`. -/
structure Chart (N Z : Type*) [MetricSpace N] [TopologicalSpace Z]
    [ChartedSpace (Fin m → ℝ) Z] (S : GlobalData N Z) (z : Z) where
  /-- The open part of `𝒵` covered by this chart. -/
  U : Set Z
  U_open : IsOpen U
  z_mem_U : z ∈ U

  /-- The Euclidean hypotheses on this chart. -/
  a : InitialAssumptions
  c : @CoordChangeAssumptions (localA a)

  /-- The chart coordinate on `U` and its inverse. -/
  coord : Z → Fin m → ℝ
  inverse : (Fin m → ℝ) → Z
  coord_inverse : ∀ y, inverse y ∈ U → coord (inverse y) = y
  inverse_coord : ∀ z' ∈ U, inverse (coord z') = z'
  coord_smooth : ContMDiffOn modelZ modelZ ⊤ coord U
  inverse_smooth : ContMDiffOn modelZ modelZ ⊤ inverse (D (d := m) (a.r0))
  coord_mem_D : ∀ z' ∈ U, coord z' ∈ D (d := m) (a.r0)
  inverse_mem_U : ∀ y ∈ D (d := m) (a.r0), inverse y ∈ U

  /-- The chart coordinates carry the open set `Ω` back and forth. -/
  coord_mem_Ω : ∀ z' ∈ U, z' ∈ S.Ω → coord z' ∈ Ωof a c
  inverse_mem_Ω : ∀ y ∈ Ωof a c, inverse y ∈ S.Ω

  /-- The lift of the chart to `𝒩`; `mapN y w` represents the point with
  coordinates `(y,w)`. -/
  mapN : (Fin m → ℝ) → (Fin n → ℝ) → N
  mapN_zero : ∀ y ∈ D (d := m) (a.r0), mapN y 0 = S.ι (inverse y)

  /-- A compact set of `m`-coordinates containing a neighbourhood of the
  chart centre, used when applying the Euclidean positivity corollary. -/
  A : Set (Fin m → ℝ)
  A_compact : IsCompact A
  A_mem_nhds_zero : A ∈ 𝓝 (0 : Fin m → ℝ)
  A_subset_D : A ⊆ D (d := m) (a.r0)

  /-- An open set of `𝒩`, covered by the chart, containing the part of `𝒵`
  inside `U`. -/
  V : Set N
  V_open : IsOpen V
  V_subset_map : ∀ p ∈ V, ∃ y ∈ A, ∃ w ∈ D (d := n) (a.r0), mapN y w = p
  ι_mem_V : ∀ z' ∈ U, S.ι z' ∈ V

  /-- The local expansion is valid on the same range of `s` as the global one. -/
  hs0_le : a.s0 ≤ S.s0

  /-- Compatibility of the Euclidean data with the global functions. -/
  h_u : ∀ y ∈ D (d := m) (a.r0), ∀ w ∈ D (d := n) (a.r0), ∀ s,
    a.u y w s = S.u (mapN y w) s
  h_u0 : ∀ y ∈ D (d := m) (a.r0), ∀ w ∈ D (d := n) (a.r0),
    a.u0 y w = S.u0 (mapN y w)
  h_u1 : ∀ y ∈ D (d := m) (a.r0), ∀ w ∈ D (d := n) (a.r0),
    a.u1 y w = S.u1 (mapN y w)
  h_u2 : ∀ y ∈ D (d := m) (a.r0), ∀ w ∈ D (d := n) (a.r0),
    a.u2 y w = S.u2 (mapN y w)
  h_u3 : ∀ y ∈ D (d := m) (a.r0), ∀ w ∈ D (d := n) (a.r0),
    a.u3 y w = S.u3 (mapN y w)

  h_Upsilon : ∀ y ∈ Ωof a c, ∀ w ∈ B (d := n) (r1of a c),
    Υof a c (y, w) = S.Υ (inverse y) w
  h_V2 : ∀ y ∈ Ωof a c, V2_of a c y = S.V2 (inverse y)
  h_V3 : ∀ y ∈ Ωof a c, V3_of a c y = S.V3 (inverse y)

  /-- A uniform remainder bound for the local expansion on the compact set
  `A`, as in the Euclidean positivity corollary. -/
  C : ℝ
  hC : 0 ≤ C
  hrem : ∀ y ∈ A, ∀ s ∈ Set.Ioc (0 : ℝ) a.s0,
    |budU_of a y s - s ^ 2 * budU2_of a y - s ^ 3 * budU3_of a y| ≤ C * s ^ 4

  /-- The Euclidean density and critical-set hypotheses.  These are the local
  forms of the density of `Ω` and of `V⁽²⁾ = dV⁽²⁾ = 0` on `Λ`. -/
  A_closure_Ω : A ⊆ closure (Ωof a c)
  A0_closure_Ω0 :
    A ∩ {y | S.ρ (inverse y) = 0} ⊆
      closure (Ωof a c ∩ {y | S.ρ (inverse y) = 0})
  critical_of_mem :
    ∀ y ∈ Ωof a c, inverse y ∈ S.Λ →
      V2_of a c y = 0 ∧ fderiv ℝ (V2_of a c) y = 0

end BrendleHung.Section2.Manifold

namespace BrendleHung.Section2

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The paper's Theorem `smooth.extension`.  On the critical set `Λ`, the
rescaled third-order coefficient `Υ(·,0)⁻¹ V⁽³⁾` is the restriction of a
smooth function on the whole submanifold `𝒵`. -/
theorem smooth_extension
    {N Z : Type*} [MetricSpace N] [TopologicalSpace Z]
    [ChartedSpace (Fin m → ℝ) Z] [IsManifold Manifold.modelZ ⊤ Z]
    [T2Space Z] [CompactSpace Z]
    (S : Manifold.GlobalData N Z)
    (charts : ∀ z : Z, Manifold.Chart (N := N) (Z := Z) S z)
    (hΛV2 : ∀ z ∈ S.Λ, S.V2 z = 0 ∧
      mfderiv Manifold.modelZ Manifold.modelR S.V2 z = 0)
    (hΥpos : ∀ z ∈ S.Λ, 0 < S.Υ z 0) :
    ∃ F : Z → ℝ, ContMDiff Manifold.modelZ Manifold.modelR (⊤ : ℕ∞) F ∧
      ∀ z ∈ S.Λ, (S.Υ z 0)⁻¹ * S.V3 z = F z := by
  classical
  let ratio : Z → ℝ := fun z => (S.Υ z 0)⁻¹ * S.V3 z
  let t : Z → Set ℝ := fun z => if z ∈ S.Λ then {ratio z} else Set.univ
  have ht : ∀ z : Z, Convex ℝ (t z) := by
    intro z
    by_cases hz : z ∈ S.Λ
    · simp [t, hz]
    · simpa [t, hz] using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  have hloc : ∀ z : Z, ∃ U ∈ 𝓝 z, ∃ g : Z → ℝ,
      ContMDiffOn Manifold.modelZ Manifold.modelR (⊤ : ℕ∞) g U ∧
        ∀ y ∈ U, g y ∈ t y := by
    intro z
    let ch : Manifold.Chart (N := N) (Z := Z) S z := charts z
    letI : InitialAssumptionsInst := Manifold.localA ch.a
    letI : CoordChangeAssumptionsInst := Manifold.localC ch.a ch.c
    let Λe : Set (Fin m → ℝ) :=
      {y | ch.inverse y ∈ S.Λ} ∩ Manifold.Ωof ch.a ch.c
    have hΛeΩ : Λe ⊆ Manifold.Ωof ch.a ch.c := fun y hy => hy.2
    have hcrit : ∀ y ∈ Λe,
        Manifold.V2_of ch.a ch.c y = 0 ∧ fderiv ℝ (Manifold.V2_of ch.a ch.c) y = 0 := by
      intro y hy
      refine ⟨?_, (ch.critical_of_mem y hy.2 hy.1).2⟩
      have hglob := (hΛV2 (ch.inverse y) hy.1).1
      rw [ch.h_V2 y hy.2]
      exact hglob
    have hinv := Manifold.invariance_local ch.a ch.c Λe hΛeΩ hcrit
    refine ⟨ch.U, ch.U_open.mem_nhds ch.z_mem_U,
      fun z' => Manifold.budU3_of ch.a (ch.coord z'), ?_, ?_⟩
    · have hsmooth : ContMDiffOn Manifold.modelZ Manifold.modelR (⊤ : ℕ∞)
          (Manifold.budU3_of ch.a) (D (d := m) ch.a.r0) :=
        (Manifold.budU3_of_smoothOn_D ch.a).of_le (by simp)
      have hcoord : ContMDiffOn Manifold.modelZ Manifold.modelZ (⊤ : ℕ∞)
          ch.coord ch.U := ch.coord_smooth.of_le (by simp)
      have hcomp := hsmooth.comp hcoord
        (by intro z' hz'; exact ch.coord_mem_D z' hz')
      simpa [Function.comp_def] using hcomp
    · intro y hyU
      by_cases hyΛ : y ∈ S.Λ
      · have hgmem : Manifold.budU3_of ch.a (ch.coord y) ∈ ({ratio y} : Set ℝ) := by
          have hyΩ : ch.coord y ∈ Manifold.Ωof ch.a ch.c :=
            ch.coord_mem_Ω y hyU (S.Λ_subset_Ω hyΛ)
          have hΛe : ch.coord y ∈ Λe := by
            constructor
            · simpa [ch.inverse_coord y hyU] using hyΛ
            · exact hyΩ
          have hV3eq := (hinv.1 (ch.coord y) hΛe)
          have hΥeq : Manifold.Υof ch.a ch.c (ch.coord y, 0) = S.Υ y 0 := by
            rw [ch.h_Upsilon (ch.coord y) hyΩ (0 : Fin n → ℝ)
              (Manifold.zero_mem_B_r1_of ch.a ch.c)]
            simp [ch.inverse_coord y hyU]
          have hV3global := ch.h_V3 (ch.coord y) hyΩ
          change Manifold.V3_of ch.a ch.c (ch.coord y) = _ at hV3eq
          rw [hV3global] at hV3eq
          simp [ch.inverse_coord y hyU] at hV3eq
          rw [Manifold.Υc_of_eq] at hV3eq
          rw [hΥeq] at hV3eq
          have hΥne : S.Υ y 0 ≠ 0 := ne_of_gt (hΥpos y hyΛ)
          change Manifold.budU3_of ch.a (ch.coord y) = (S.Υ y 0)⁻¹ * S.V3 y
          rw [hV3eq]
          field_simp [hΥne]
        simpa [t, hyΛ] using hgmem
      · simp [t, hyΛ]
  rcases exists_contMDiffMap_forall_mem_convex_of_local (I := Manifold.modelZ)
      (n := (⊤ : ℕ∞)) ht hloc with ⟨F, hF⟩
  refine ⟨F, F.contMDiff, ?_⟩
  intro z hz
  have hzmem : F z ∈ ({ratio z} : Set ℝ) := by simpa [t, hz] using hF z
  exact (Set.mem_singleton_iff.mp hzmem).symm

omit [InitialAssumptionsInst] [CoordChangeAssumptionsInst] in
/-- The paper's Theorem `positivity.manifold.version`.  Covering `𝒵` by
finitely many charts and applying the Euclidean positivity corollary on each
chart yields positivity of `inf u(·,s)` over `𝒩` for small positive `s`. -/
theorem positivity_manifold_version
    {N Z : Type*} [MetricSpace N] [TopologicalSpace Z]
    [ChartedSpace (Fin m → ℝ) Z] [IsManifold Manifold.modelZ ⊤ Z]
    [T2Space Z] [CompactSpace Z] [Nonempty Z] [Nonempty N]
    (S : Manifold.GlobalData N Z)
    (charts : ∀ z : Z, Manifold.Chart (N := N) (Z := Z) S z) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 ≤ S.s0 ∧
      ∀ s ∈ Set.Ioc (0 : ℝ) s1,
        0 < sInf ((fun p => S.u p s) '' (Set.univ : Set N)) := by
  classical
  -- A finite chart cover of `𝒵`.
  let U : Z → Set Z := fun z => (charts z).U
  have hcover : (Set.univ : Set Z) ⊆ ⋃ z, U z := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨z, (charts z).z_mem_U⟩
  rcases S.hZcompact.elim_finite_subcover U
      (fun z => (charts z).U_open) hcover with ⟨t, htcover⟩
  have htne : t.Nonempty := by
    let z0 : Z := Classical.choice (inferInstance : Nonempty Z)
    have hz0 : z0 ∈ ⋃ i ∈ t, U i := htcover trivial
    rcases Set.mem_iUnion₂.mp hz0 with ⟨i, hi, hzi⟩
    exact ⟨i, hi⟩
  -- The Euclidean corollary gives a local radius and a uniform lower bound
  -- over every chart's compact coordinate set.
  have hlocal : ∀ z : Z, ∃ sz : ℝ, 0 < sz ∧ sz ≤ S.s0 ∧
      ∀ s ∈ Set.Ioc (0 : ℝ) sz, ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ (charts z).A, δ ≤ Manifold.budU_of (charts z).a y s := by
    intro z
    let ch : Manifold.Chart (N := N) (Z := Z) S z := charts z
    have hρnonneg_local : ∀ y ∈ D (d := m) ch.a.r0,
        0 ≤ S.ρ (ch.inverse y) := by
      intro y hy
      exact S.hρ_nonneg (ch.inverse y)
    have hρcont_local : ContinuousOn (fun y => S.ρ (ch.inverse y))
        (D (d := m) ch.a.r0) := by
      simpa [Function.comp_def] using
        S.hρ_cont.comp_continuousOn ch.inverse_smooth.continuousOn
    have hV2local : ∀ y ∈ Manifold.Ωof ch.a ch.c,
        S.κ * Manifold.Υc_of ch.a ch.c y 0 * S.ρ (ch.inverse y) ≤
          Manifold.V2_of ch.a ch.c y := by
      intro y hy
      have hΥ0 := ch.h_Upsilon y hy (0 : Fin n → ℝ)
        (Manifold.zero_mem_B_r1_of ch.a ch.c)
      have hglob := S.hV2_lower (ch.inverse y) (ch.inverse_mem_Ω y hy)
      rw [Manifold.Υc_of_eq, hΥ0, ch.h_V2 y hy]
      exact hglob
    have hV3local : ∀ y ∈ Manifold.Ωof ch.a ch.c,
        S.ρ (ch.inverse y) = 0 →
          Manifold.V2_of ch.a ch.c y = 0 ∧
            S.κ * Manifold.Υc_of ch.a ch.c y 0 ≤ Manifold.V3_of ch.a ch.c y := by
      intro y hy hρ0
      have hΥ0 := ch.h_Upsilon y hy (0 : Fin n → ℝ)
        (Manifold.zero_mem_B_r1_of ch.a ch.c)
      have hglob := S.hV3_lower (ch.inverse y) (ch.inverse_mem_Ω y hy) hρ0
      rw [ch.h_V2 y hy, ch.h_V3 y hy, Manifold.Υc_of_eq, hΥ0]
      exact hglob
    have hAne : ch.A.Nonempty := ⟨0, mem_of_mem_nhds ch.A_mem_nhds_zero⟩
    rcases Manifold.positivity_local ch.a ch.c
        (fun y => S.ρ (ch.inverse y)) hρnonneg_local hρcont_local
        S.κ S.hκ hV2local hV3local
        ch.A hAne ch.A_compact ch.A_subset_D ch.A_closure_Ω ch.A0_closure_Ω0
        ch.C ch.hC ch.hrem with
      ⟨sz, hszpos, hszle, _, hszδ⟩
    exact ⟨sz, hszpos, hszle.trans ch.hs0_le, hszδ⟩
  choose sz hszpos hszle hszδ using hlocal
  -- Uniform bounds for the smooth coefficient functions on compact `𝒩`.
  have bound_of_cont : ∀ f : N → ℝ, Continuous f →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : N, |f p| ≤ B := by
    intro f hf
    rcases S.hNcompact.exists_bound_of_continuousOn hf.continuousOn with ⟨B, hB⟩
    refine ⟨max B 0, le_max_right B 0, ?_⟩
    intro p
    have hp : |f p| ≤ B := by simpa [Real.norm_eq_abs] using hB p trivial
    exact hp.trans (le_max_left B 0)
  rcases bound_of_cont S.u1 S.hu1_cont with ⟨B1, hB1nonneg, hB1⟩
  rcases bound_of_cont S.u2 S.hu2_cont with ⟨B2, hB2nonneg, hB2⟩
  rcases bound_of_cont S.u3 S.hu3_cont with ⟨B3, hB3nonneg, hB3⟩
  -- The finite union of chart neighbourhoods is an open set containing `𝒵`.
  let Vfin : Set N := ⋃ i ∈ t, (charts i).V
  have hVfin_open : IsOpen Vfin := by
    dsimp [Vfin]
    exact isOpen_iUnion fun i => isOpen_iUnion fun hi => (charts i).V_open
  have hRange_subset_Vfin : Set.range S.ι ⊆ Vfin := by
    rintro p ⟨z, rfl⟩
    have hzcov : z ∈ ⋃ i ∈ t, U i := htcover trivial
    rcases Set.mem_iUnion₂.mp hzcov with ⟨i, hi, hzi⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, (charts i).ι_mem_V z hzi⟩
  let K : Set N := Vfinᶜ
  have hKcompact : IsCompact K := by
    simpa [K, Set.univ_inter] using
      S.hNcompact.inter_right hVfin_open.isClosed_compl
  have hRangeCompact : IsCompact (Set.range S.ι) := by
    simpa [Set.image_univ] using S.hZcompact.image S.hι_cont
  have hRangeClosed : IsClosed (Set.range S.ι) := hRangeCompact.isClosed
  have hRangeNe : (Set.range S.ι).Nonempty := by
    exact ⟨S.ι (Classical.choice (inferInstance : Nonempty Z)), ⟨_, rfl⟩⟩
  -- Away from the chart union, `u₀` gives a positive quadratic lower bound.
  have hAway : ∃ δaway saway : ℝ, 0 < δaway ∧ 0 < saway ∧
      ∀ s ∈ Set.Ioc (0 : ℝ) saway, ∀ p ∈ K, δaway ≤ S.u p s := by
    by_cases hKne : K.Nonempty
    · have hdist_cont : ContinuousOn
          (fun p : N => Metric.infDist p (Set.range S.ι)) K :=
        (Metric.continuous_infDist_pt (Set.range S.ι)).continuousOn
      rcases hKcompact.exists_isMinOn hKne hdist_cont with ⟨p0, hp0K, hp0min⟩
      have hp0notV : p0 ∉ Vfin := by simpa [K] using hp0K
      have hp0notRange : p0 ∉ Set.range S.ι :=
        fun hp => hp0notV (hRange_subset_Vfin hp)
      have hp0notClosure : p0 ∉ closure (Set.range S.ι) := by
        simpa [hRangeClosed.closure_eq] using hp0notRange
      have hdistpos : 0 < Metric.infDist p0 (Set.range S.ι) :=
        (Metric.infDist_pos_iff_notMem_closure hRangeNe).mp hp0notClosure
      let δdist : ℝ := Metric.infDist p0 (Set.range S.ι)
      have hδdistpos : 0 < δdist := hdistpos
      have hδdist_le : ∀ p ∈ K, δdist ≤ Metric.infDist p (Set.range S.ι) := by
        intro p hpK
        exact hp0min hpK
      let A0 : ℝ := S.σ * δdist ^ 2
      have hA0pos : 0 < A0 := mul_pos S.hσ (sq_pos_of_pos hδdistpos)
      let saway : ℝ := min S.s0 (min 1 (min (A0 / (8 * (B1 + 1)))
        (min (A0 / (8 * (B2 + 1))) (min (A0 / (8 * (B3 + 1)))
          (A0 / (8 * (S.C + 1)))))))
      have hd1 : 0 < 8 * (B1 + 1) := by nlinarith
      have hd2 : 0 < 8 * (B2 + 1) := by nlinarith
      have hd3 : 0 < 8 * (B3 + 1) := by nlinarith
      have hd4 : 0 < 8 * (S.C + 1) := by nlinarith [S.hC]
      have hsawaypos : 0 < saway := by
        dsimp [saway]
        exact lt_min S.hs0 (lt_min zero_lt_one
          (lt_min (div_pos hA0pos hd1) (lt_min (div_pos hA0pos hd2)
            (lt_min (div_pos hA0pos hd3) (div_pos hA0pos hd4)))))
      refine ⟨A0 / 2, saway, div_pos hA0pos (by norm_num), hsawaypos, ?_⟩
      intro s hs p hpK
      have hsleS : s ≤ S.s0 := hs.2.trans (by
        dsimp [saway]
        exact min_le_left _ _)
      have hsle1 : s ≤ 1 := hs.2.trans (by
        dsimp [saway]
        exact (min_le_right _ _).trans (min_le_left _ _))
      have hsle1den : s ≤ A0 / (8 * (B1 + 1)) := hs.2.trans (by
        dsimp [saway]
        exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
      have hsle2den : s ≤ A0 / (8 * (B2 + 1)) := hs.2.trans (by
        dsimp [saway]
        exact (((min_le_right _ _).trans (min_le_right _ _)).trans
          (min_le_right _ _)).trans (min_le_left _ _))
      have hsle3den : s ≤ A0 / (8 * (B3 + 1)) := hs.2.trans (by
        dsimp [saway]
        exact ((((min_le_right _ _).trans (min_le_right _ _)).trans
          (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _))
      have hsleCden : s ≤ A0 / (8 * (S.C + 1)) := hs.2.trans (by
        dsimp [saway]
        exact ((((min_le_right _ _).trans (min_le_right _ _)).trans
          (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _))
      have hterm (B : ℝ) (hB : 0 ≤ B) (hsB : s ≤ A0 / (8 * (B + 1))) :
          s * B ≤ A0 / 8 := by
        have hden : 0 < 8 * (B + 1) := by positivity
        have hmul : s * (8 * (B + 1)) ≤ A0 := by
          calc
            s * (8 * (B + 1)) ≤ (A0 / (8 * (B + 1))) * (8 * (B + 1)) :=
              mul_le_mul_of_nonneg_right hsB (le_of_lt hden)
            _ = A0 := by field_simp [ne_of_gt hden]
        have hsmall : s * B ≤ s * (B + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hs.1)
        nlinarith
      have hB1term : s * B1 ≤ A0 / 8 := hterm B1 hB1nonneg hsle1den
      have hB2term : s * B2 ≤ A0 / 8 := hterm B2 hB2nonneg hsle2den
      have hB3term : s * B3 ≤ A0 / 8 := hterm B3 hB3nonneg hsle3den
      have hCterm : S.C * s ≤ A0 / 8 := by
        simpa [mul_comm] using hterm S.C S.hC hsleCden
      have hs2les : s ^ 2 ≤ s := by
        have hs1nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hsle1
        have hprod : 0 ≤ s * (1 - s) := mul_nonneg (le_of_lt hs.1) hs1nonneg
        nlinarith
      have hs3les : s ^ 3 ≤ s := by
        have h32 : s ^ 3 ≤ s ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hsle1 (sq_nonneg s)
          nlinarith
        exact h32.trans hs2les
      have hs4les : s ^ 4 ≤ s := by
        have h43 : s ^ 4 ≤ s ^ 3 := by
          have h := mul_le_mul_of_nonneg_left hsle1
            (pow_nonneg (le_of_lt hs.1) 3)
          nlinarith
        exact h43.trans hs3les
      have hB2term2 : s ^ 2 * B2 ≤ A0 / 8 :=
        (mul_le_mul_of_nonneg_right hs2les hB2nonneg).trans hB2term
      have hB3term3 : s ^ 3 * B3 ≤ A0 / 8 :=
        (mul_le_mul_of_nonneg_right hs3les hB3nonneg).trans hB3term
      have hCterm4 : S.C * s ^ 4 ≤ A0 / 8 :=
        (mul_le_mul_of_nonneg_left hs4les S.hC).trans hCterm
      have hdnonneg : 0 ≤ Metric.infDist p (Set.range S.ι) := Metric.infDist_nonneg
      have hdsq : δdist ^ 2 ≤ (Metric.infDist p (Set.range S.ι)) ^ 2 := by
        have hdle := hδdist_le p hpK
        nlinarith [sq_nonneg (Metric.infDist p (Set.range S.ι) - δdist)]
      have hu0bound : A0 ≤ S.u0 p := by
        dsimp [A0]
        exact (mul_le_mul_of_nonneg_left hdsq (le_of_lt S.hσ)).trans
          (S.hu0_lower p)
      have hsasm : s ∈ Set.Ioc (0 : ℝ) S.s0 := ⟨hs.1, hsleS⟩
      have hrem := S.hu_rem p s hsasm
      have hUlower : S.u0 p + s * S.u1 p + s ^ 2 * S.u2 p +
          s ^ 3 * S.u3 p - S.C * s ^ 4 ≤ S.u p s := by
        have hneg := (abs_le.mp hrem).1
        linarith
      have hu1lower : -(s * B1) ≤ s * S.u1 p := by
        have h := (abs_le.mp (hB1 p)).1
        simpa [mul_neg] using mul_le_mul_of_nonneg_left h (le_of_lt hs.1)
      have hu2lower : -(s ^ 2 * B2) ≤ s ^ 2 * S.u2 p := by
        have h := (abs_le.mp (hB2 p)).1
        simpa [mul_neg] using mul_le_mul_of_nonneg_left h (sq_nonneg s)
      have hu3lower : -(s ^ 3 * B3) ≤ s ^ 3 * S.u3 p := by
        have h := (abs_le.mp (hB3 p)).1
        simpa [mul_neg] using
          mul_le_mul_of_nonneg_left h (pow_nonneg (le_of_lt hs.1) 3)
      nlinarith
    · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
      intro s hs p hpK
      exfalso
      exact hKne ⟨p, hpK⟩
  rcases hAway with ⟨δaway, saway, hδawaypos, hsawaypos, hAway⟩
  -- Combine the finitely many local radii.
  let sfin : ℝ := t.inf' htne sz
  have hsfinpos : 0 < sfin := by
    dsimp [sfin]
    exact Finset.inf'_mem (Set.Ioi (0 : ℝ))
      (by
      intro x hx y hy
      change 0 < x at hx
      change 0 < y at hy
      change 0 < min x y
      exact lt_min hx hy) t htne sz
      (by intro i hi; exact hszpos i)
  have htne_copy := htne
  rcases htne_copy with ⟨i0, hi0⟩
  have hsfinkleS : sfin ≤ S.s0 := by
    dsimp [sfin]
    exact (Finset.inf'_le sz hi0).trans (hszle i0)
  let sfinal : ℝ := min sfin saway
  have hsfinalpos : 0 < sfinal := by
    dsimp [sfinal]
    exact lt_min hsfinpos hsawaypos
  have hsfinalleS : sfinal ≤ S.s0 :=
    (min_le_left _ _).trans hsfinkleS
  refine ⟨sfinal, hsfinalpos, hsfinalleS, ?_⟩
  intro s hs
  have hspos : 0 < s := hs.1
  have hssfin : s ≤ sfin := hs.2.trans (min_le_left _ _)
  have hssaway : s ≤ saway := hs.2.trans (min_le_right _ _)
  have hδi_exists : ∀ i ∈ t, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ (charts i).A, δ ≤ Manifold.budU_of (charts i).a y s := by
    intro i hi
    have hsi : s ∈ Set.Ioc (0 : ℝ) (sz i) :=
      ⟨hspos, hssfin.trans (by dsimp [sfin]; exact Finset.inf'_le sz hi)⟩
    exact hszδ i s hsi
  let δi : Z → ℝ := fun i =>
    if hi : i ∈ t then Classical.choose (hδi_exists i hi) else 1
  have hδi_pos : ∀ i ∈ t, 0 < δi i := by
    intro i hi
    dsimp [δi]
    simp [hi, (Classical.choose_spec (hδi_exists i hi)).1]
  have hδi_le : ∀ i ∈ t, ∀ y ∈ (charts i).A,
      δi i ≤ Manifold.budU_of (charts i).a y s := by
    intro i hi
    have hspec := Classical.choose_spec (hδi_exists i hi)
    dsimp [δi]
    rw [dif_pos hi]
    exact hspec.2
  let δfin : ℝ := t.inf' htne δi
  have hδfinpos : 0 < δfin := by
    dsimp [δfin]
    exact Finset.inf'_mem (Set.Ioi (0 : ℝ))
      (by
      intro x hx y hy
      change 0 < x at hx
      change 0 < y at hy
      change 0 < min x y
      exact lt_min hx hy) t htne δi hδi_pos
  let δ : ℝ := min δfin δaway
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδfinpos hδawaypos
  have hglobalLower : ∀ p : N, δ ≤ S.u p s := by
    intro p
    by_cases hpV : p ∈ Vfin
    · rcases Set.mem_iUnion₂.mp hpV with ⟨i, hi, hpVi⟩
      rcases (charts i).V_subset_map p hpVi with ⟨y, hyA, w, hwD, hmap⟩
      have hyD : y ∈ D (d := m) (charts i).a.r0 :=
        (charts i).A_subset_D hyA
      have hbudle : Manifold.budU_of (charts i).a y s ≤
          (charts i).a.u y w s :=
        Manifold.budU_of_le_u (charts i).a y s w hwD
      have hcompat : (charts i).a.u y w s = S.u p s := by
        rw [← hmap]
        exact (charts i).h_u y hyD w hwD s
      calc
        δ ≤ δfin := min_le_left _ _
        _ ≤ δi i := by dsimp [δfin]; exact Finset.inf'_le δi hi
        _ ≤ Manifold.budU_of (charts i).a y s := hδi_le i hi y hyA
        _ ≤ (charts i).a.u y w s := hbudle
        _ = S.u p s := hcompat
    · have hpK : p ∈ K := by simpa [K] using hpV
      exact (min_le_right _ _).trans (hAway s ⟨hspos, hssaway⟩ p hpK)
  have himage_nonempty : ((fun p => S.u p s) '' (Set.univ : Set N)).Nonempty := by
    exact ⟨S.u (Classical.choice (inferInstance : Nonempty N)) s,
      ⟨_, trivial, rfl⟩⟩
  have hInfge : δ ≤ sInf ((fun p => S.u p s) '' (Set.univ : Set N)) := by
    apply le_csInf himage_nonempty
    rintro z ⟨p, hp, rfl⟩
    exact hglobalLower p
  exact lt_of_lt_of_le hδpos hInfge

end BrendleHung.Section2

end

end Section2
