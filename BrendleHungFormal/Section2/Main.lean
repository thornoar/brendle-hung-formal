import BrendleHungFormal.Section2.Euclidean
import BrendleHungFormal.Section2.Manifold
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Function (uncurry)
open Filter
open scoped BigOperators Matrix Topology Manifold ContDiff

section BrendleHung.Section2

variable [InitialAssumptions] [CoordChangeAssumptions]

open BrendleHung.Section2.Multivar
open BrendleHung.Section2.TaylorAsymptotics

-- Keep the short name `norm` for the coordinate-space norm in this file,
-- without clashing with Mathlib's global `norm`.
local notation "norm" => BrendleHung.Section2.Multivar.norm
local notation "↓" f => uncurry f

noncomputable section

namespace BrendleHung.Section2

omit [InitialAssumptions] [CoordChangeAssumptions] in
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
    letI : InitialAssumptions := ch.a
    letI : CoordChangeAssumptions := ch.c
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

omit [InitialAssumptions] [CoordChangeAssumptions] in
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
