import BrendleHungFormal.Section2.Work

open Filter
open scoped BigOperators Topology

section BrendleHung.Section2

variable [InitialAssumptions] [CoordChangeAssumptions]

open BrendleHung.Section2.Multivar
open BrendleHung.Section2.TaylorAsymptotics

noncomputable section

omit [CoordChangeAssumptions] in
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
    rcases Asymptotics.IsBigO.exists_pos hO with ⟨c, hcpos, hcO⟩
    refine ⟨c, ?_⟩
    filter_upwards [Asymptotics.IsBigOWith.bound hcO] with s hs
    by_cases hs0 : s = 0
    · simp [ρU, hs0, hcpos.le]
    · have hs4_ne : s ^ 4 ≠ 0 := pow_ne_zero 4 hs0
      have hs4_pos : 0 < ‖s ^ 4‖ := norm_pos_iff.mpr hs4_ne
      have hc' : ‖bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p‖
          ≤ c * ‖s ^ 4‖ := hs
      have hdiv : ‖bud.U p s - s ^ 2 * bud.U2 p - s ^ 3 * bud.U3 p‖ / ‖s ^ 4‖
          ≤ c := by
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
  simpa [zD1, v0B_zero y hy, zD1_v0B y hy α] using
    (zD1_mul_at (Υc y) (v0B y) 0
      (upsilon_z_smoothAt y hy) (v0B_smoothAt y hy) α)

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

private lemma V2_eventually_eq_upsilon_mul_U2 (y : ℝ^m) (hy : y ∈ cca.Ω) :
    V2 =ᶠ[𝓝 y] fun y' : ℝ^m => Υc y' 0 * bud.U2 y' := by
  filter_upwards [cca.Ω_open.mem_nhds hy] with y' hy'
  exact relation_U2_V2 y' hy'

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
                barz y α * barz y β) :=
    eq_neg_of_add_eq_zero_left (u0WW_psi_cancel y hy)
  have hCneg :
      (∑ γ : Fin n, ∑ δ : Fin n, ∑ ζ : Fin n,
        zD1 (Υc y) γ * u0WW y 0 δ ζ *
          bud.barw y δ * bud.barw y ζ * barz y γ)
        = - (∑ α : Fin n, ∑ γ : Fin n,
              zD1 (Υc y) α * u1W y 0 (e γ) * barz y α * bud.barw y γ) :=
    eq_neg_of_add_eq_zero_left (u0WW_Upsilon_cancel y hy)
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
    have hprodZero :
        fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y = 0 := by
      rw [← (V2_eventually_eq_upsilon_mul_U2 y hyΩ).fderiv_eq]
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
  simp [hΥne]


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
    refine ⟨hV2zero, ?_⟩
    calc
      fderiv ℝ V2 y = fderiv ℝ (fun y' : ℝ^m => Υc y' 0 * bud.U2 y') y :=
        (V2_eventually_eq_upsilon_mul_U2 y hyΩ).fderiv_eq
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
    simp
  have hs1le_one : s1 ≤ 1 := by
    dsimp [s1]
    simp
  have hs1le_k1 : s1 ≤ κ / (4 * (C + 1)) := by
    dsimp [s1]
    simp
  have hs1le_k2 : s1 ≤ κ * ε / (2 * (K + 1)) := by
    dsimp [s1]
    simp
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
      have hmul : s * (4 * (C + 1)) ≤ κ := (le_div_iff₀ hden1).mp hsle
      have hCsmall : C * s ≤ (C + 1) * s := by nlinarith [le_of_lt hspos]
      nlinarith
    have hK_le : K * s ≤ κ * ε / 2 := by
      have hsle : s ≤ κ * ε / (2 * (K + 1)) := hss1.trans hs1le_k2
      have hmul : s * (2 * (K + 1)) ≤ κ * ε := (le_div_iff₀ hden2).mp hsle
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
  exact ⟨s1, hs1pos, hs1le_s0,
    fun s hs => (hmain s hs).1,
    fun s hs => (hmain s hs).2⟩

end BrendleHung.Section2

end

end Section2
