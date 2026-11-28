import BrendleHungFormal.Section2.Euclidean
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace BrendleHung.Section2.Manifold

open BrendleHung.Section2.Multivar

/-- The coordinate model of the submanifold `𝒵` (dimension `m`). -/
abbrev modelZ := 𝓘(ℝ, Fin m → ℝ)

/-- The coordinate model of the ambient manifold `𝒩` (dimension `m + n`). -/
abbrev modelN := 𝓘(ℝ, (Fin m → ℝ) × (Fin n → ℝ))

/-- The coordinate model of the real line. -/
abbrev modelR := 𝓘(ℝ, ℝ)

/-- Explicit projections from chart data with its own Euclidean instance. -/
abbrev Ωof (a : InitialAssumptions) (c : @CoordChangeAssumptions a) : Set (Fin m → ℝ) :=
  @CoordChangeAssumptions.Ω a c

abbrev r1of (a : InitialAssumptions) (c : @CoordChangeAssumptions a) : ℝ :=
  @CoordChangeAssumptions.r1 a c

abbrev Υof (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (q : (Fin m → ℝ) × (Fin n → ℝ)) : ℝ :=
  @CoordChangeAssumptions.Υ a c q

/-- The paper's `V⁽²⁾` and `V⁽³⁾` for a specified pair of Euclidean data. -/
abbrev V2_of (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (y : Fin m → ℝ) : ℝ := @V2 a c y

abbrev V3_of (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (y : Fin m → ℝ) : ℝ := @V3 a c y

/-- The scalar factor `Υ(y,0)` with explicit Euclidean data. -/
abbrev Υc_of (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (y : Fin m → ℝ) (z : Fin n → ℝ) : ℝ := @Υc a c y z

/-- The reduced second- and third-order coefficients and the reduced function
with explicit Euclidean data. -/
abbrev budU_of (a : InitialAssumptions) (y : Fin m → ℝ) (s : ℝ) : ℝ := (@bud a).U y s

abbrev budU2_of (a : InitialAssumptions) (y : Fin m → ℝ) : ℝ := (@bud a).U2 y

abbrev budU3_of (a : InitialAssumptions) (y : Fin m → ℝ) : ℝ := (@bud a).U3 y

lemma Υc_of_eq (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (y : Fin m → ℝ) (z : Fin n → ℝ) : Υc_of a c y z = Υof a c (y, z) := rfl

/-- Smoothness of the local third-order coefficient on its coordinate ball. -/
lemma budU3_of_smoothOn_D (a : InitialAssumptions) :
    ContMDiffOn modelZ modelR (⊤ : WithTop ℕ∞) (budU3_of a) (D (d := m) a.r0) := by
  simpa [modelZ, modelR, budU3_of] using
    (contMDiffOn_iff_contDiffOn.mpr
      (@bud_U3_smoothOn_D a))

/-- The Euclidean invariance proposition applied to explicit local data. -/
lemma invariance_local (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (Λe : Set (Fin m → ℝ)) (hΛeΩ : Λe ⊆ Ωof a c)
    (hcrit : ∀ y ∈ Λe, V2_of a c y = 0 ∧ fderiv ℝ (V2_of a c) y = 0) :
    (∀ y ∈ Λe, V3_of a c y = Υc_of a c y 0 * budU3_of a y) ∧
      ∃ F : (Fin m → ℝ) → ℝ, ContDiffOn ℝ (⊤ : WithTop ℕ∞) F (D (d := m) a.r0) ∧
        ∀ y ∈ Λe, (Υc_of a c y 0)⁻¹ * V3_of a c y = F y := by
  simpa [V2_of, V3_of, Υc_of, budU3_of] using
    (@invariance a c Λe hΛeΩ hcrit)

/-- The origin belongs to the normal-coordinate ball of a chart. -/
lemma zero_mem_B_r1_of (a : InitialAssumptions) (c : @CoordChangeAssumptions a) :
    (0 : Fin n → ℝ) ∈ B (d := n) (r1of a c) := by
  simpa [B, BrendleHung.Section2.Multivar.norm] using
    (@CoordChangeAssumptions.r1_pos a c)

/-- Positivity of `Υ(y,0)` with explicit local data. -/
lemma upsilon_y0_pos_of (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
    (y : Fin m → ℝ) (hy : y ∈ Ωof a c) : 0 < Υc_of a c y 0 := by
  simpa [Υc_of] using
    (@upsilon_y0_pos a c y hy)

/-- The reduced function is bounded above by every admissible trial value. -/
lemma budU_of_le_u (a : InitialAssumptions)
    (y : Fin m → ℝ) (s : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ D (d := n) (a.r0)) :
    budU_of a y s ≤ a.u y w s := by
  letI : InitialAssumptions := a
  rcases (@exists_minimizer a y s) with ⟨w0, hw0, hmin, hU⟩
  rw [show budU_of a y s = a.u y w0 s by simpa [budU_of] using hU]
  exact hmin hw

/-- The Euclidean positivity corollary applied to explicit local data. -/
lemma positivity_local
    (a : InitialAssumptions) (c : @CoordChangeAssumptions a)
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
  simpa [V2_of, V3_of, Υc_of, budU_of, budU2_of, budU3_of] using
    (@BrendleHung.Section2.positivity a c ρe
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
  c : @CoordChangeAssumptions a

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

end
