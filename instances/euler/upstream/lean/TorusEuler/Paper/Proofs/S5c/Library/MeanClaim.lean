import TorusEuler.Paper.Proofs.S5c.Library.MeanGlue
import TorusEuler.Paper.Proofs.S5c.Library.Assembly59

/-!
# The Hessian of the mean pressures in Lemma 5.9

`meanHessianClaim` proves `MeanHessianClaim` (`sections/08_exact_wave.tex:233-255`) from
Theorem 4.2 (`h4_2`), Theorem 5.6 (`h5_6`), Lemma 5.7 (`h5_7`) and Lemma B.1 (`hB_1`).
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile LocalizedAmplitude InnerProductSpace Lib.S5a

noncomputable section

set_option maxHeartbeats 3200000 in
/-- **The Hessian of the sum of the mean pressures** (`sections/08_exact_wave.tex:233-255`):
`‖D_x²∑_{p=2}^P q̄_p^♮‖_∞ ≤ K_P 𝖣^C λ^{-5/2}`. Following the text: adding the mean equations (5.11)
of the levels `2 ≤ p ≤ P` (`meanSolution_sum`) gives a solution `(W̄, ∑q̄_p)` of (5.11) with source
`∑ f̄_p`; in Eulerian coordinates it is the linearized Euler equation (4.12) for `W̄^♮` over `U`
with the pressure `(∑q̄_p)^♮` and the source `(∑f̄_p)^♮` (`h4_2`: the smooth-force item of
Theorem 4.2, through `exists_mean_eulerian` and the uniqueness of normalized solutions of (5.11),
`Lib.S5a.meanUnique_of_theorem42`, to identify `(W̄, ∑q̄_p)` with the solution that item
produces); taking the divergence gives the Poisson equation for the pressure with the right side
`div f - 2tr(∇U∇W̄^♮)`, and `D²Δ⁻¹` is bounded on `C^{0,1/2}`
(`meanPressureHessian_closedSlab_bound`). The source and `W̄^♮` are bounded in `C_tC^{1,1/2}` by
(5.45) of `h5_7` (phase-independent clause, `γ = 1`) and (5.37) of `h5_6` (`‖W̄‖_{[2]} + ‖∑f̄_p‖_{[2]}
≤ K𝖣^{C₆}λ^{-5/2}`), and `‖∇U‖_{C^{0,1/2}} ≤ C𝖣²` by (B.1) (`hB_1`, through
`parentGradient_halfHolder_of_B1`) and (5.1). Constants: `a₀ = max (a₀(5.6), a₀(5.7))`,
`C = 2 + 2C₇ + C₆`, `K_P = 48‖Π‖ |K₇(1)| |K₆(2,P)| (1 + C_U)`. -/
theorem meanHessianClaim (h4_2 : Statement.theorem_4_2) (h5_6 : Statement.theorem_5_6)
    (h5_7 : Statement.lemma_5_7) (hB_1 : Statement.lemma_B_1) : MeanHessianClaim := by
  obtain ⟨a6, h6⟩ := h5_6
  obtain ⟨a7, h7⟩ := h5_7
  obtain ⟨Cu, hCu, hUjet⟩ := parentGradient_halfHolder_of_B1 hB_1
  refine ⟨max a6 a7, fun a ha => ?_⟩
  obtain ⟨C6, K6, KP6, h6a⟩ := h6 a (le_trans (le_max_left _ _) ha)
  obtain ⟨C7, K7, h7a⟩ := h7 a (le_trans (le_max_right _ _) ha)
  refine ⟨2 + (2 * C7 + C6),
    fun P => 48 * ‖pressureHessianMultiplier‖ * (|K7 1| * |KP6 2 P|) * (1 + Cu), ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO hsm amp hamp P hP2 R S u hu t ht x
  -- standing facts
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hDp : ∀ m : ℕ, 0 ≤ D ^ m := fun m => pow_nonneg hD0.le m
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hsm6 : D ^ C6 * lam ^ (-1 / 12 : ℝ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hD (by omega : C6 ≤ 2 + (2 * C7 + C6)))
      (Real.rpow_nonneg hlam0.le _)) hsm
  -- the summed mean solution
  let Y : Velocity := fun t => X t 0
  let Bs : HierarchyTwistedProfile T k Vec3 := ∑ p ∈ Finset.Icc 2 P, u.B p
  let Qs : HierarchyTwistedProfile T k ℝ := ∑ p ∈ Finset.Icc 2 P, u.q p
  let fs : HierarchyTwistedProfile T k Vec3 :=
    ∑ p ∈ Finset.Icc 2 P, S5.meanSource (S5.ops d) u (S5.curlCorrection d S) R p
  have hsol : S5.MeanSolution d fs Bs Qs :=
    meanSolution_sum d _ _ _ _ fun p hp => (hu.mean p hp).1
  have hnorm : ∀ r ∈ Icc 0 T, (∫ a in centeredCell, Qs.val.val.val (r, a, 0)) = 0 := by
    intro r hr
    have hcont (p : ℕ) : Continuous fun a => (u.q p).val.val.val (r, a, 0) :=
      (meanInt_slice_spatial (f := fun r a => (u.q p).val.val.val (r, a, 0))
        (slice0_contDiff (u.q p)) hr).continuous
    have hI : (∫ a in centeredCell, Qs.val.val.val (r, a, 0)) =
        ∫ a in centeredCell, ∑ p ∈ Finset.Icc 2 P, (u.q p).val.val.val (r, a, 0) :=
      congrArg (fun F : Vec3 → ℝ => ∫ a in centeredCell, F a)
        (funext fun a => profile_sum_apply _ _ _)
    rw [hI, MeasureTheory.integral_finsetSum _ fun p _ =>
      (hcont p).continuousOn.integrableOn_compact isCompact_centeredCell]
    exact Finset.sum_eq_zero fun p hp => (hu.mean p hp).2 r hr
  have havg : (S5.ops d).average fs = fs := meanSolution_source_phaseIndependent d hsol
  obtain ⟨Bp, qp, hsolp, hnp, hEul⟩ := exists_mean_eulerian h4_2 d hP havg
  obtain ⟨hBe, hqe⟩ := (meanUnique_of_theorem42 h4_2 d hP) fs Bs Bp Qs qp hsol hnorm hsolp hnp
  rw [← hBe, ← hqe] at hEul
  obtain ⟨hbs, hqs, hper, heq⟩ := hEul
  let bE : Velocity := fun t x => Bs.val.val.val (t, X t 0 x, 0)
  let qE : Pressure := fun t x => Qs.val.val.val (t, X t 0 x, 0)
  let fE : Velocity := fun t x => fs.val.val.val (t, X t 0 x, 0)
  -- the Poisson problem for the Eulerian pressure
  have hfper : ∀ r ∈ Icc 0 T, SpatiallyPeriodic (fE r) := by
    intro r hr n y
    change fs.val.val.val (r, X r 0 (y + latticeVector n), 0) = fs.val.val.val (r, X r 0 y, 0)
    rw [parent_flow_lattice hT hP hr h0 n y]
    exact meanProfile_periodic d havg hr 0 0 n _
  have hMom : ∀ r ∈ Icc 0 T, ∀ y, derivWithin (fun s => bE s y) (Icc 0 T) r +
      fderiv ℝ (bE r) y (U r y) + fderiv ℝ (U r) y (bE r y) + gradient (qE r) y = fE r y := by
    intro r hr y
    have h := (heq r hr y).2
    rw [fderivWithin_slab_direction hT hbs hr y (U r y)] at h
    exact h
  -- the sizes of `∇U`, `W̄^♮`, `∑f̄_p^♮`
  obtain ⟨vt, hvt⟩ := hP.velocity_band
  have hUsize : ∀ r ∈ Icc 0 T, SpatialHolderHalf 0 (fderiv ℝ (U r)) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (U r)) ≤ Cu * D ^ 2 := by
    intro r hr
    obtain ⟨hvU, hband⟩ := hvt r hr
    have hUt : (fun y => vt r (toUnitTorus y)) = U r := funext hvU
    have hband4 : RealTorusFourierBand (4 * D) (vt r) := fun j hj =>
      hband j ((show 2 * D ≤ 4 * D by linarith).trans_lt hj)
    have h := hUjet (vt r) hD hband4 (by rw [hUt]; exact meanInt_slice_spatial hP.velocity_smooth hr)
      (by rw [hUt]; exact fun y => hP.gradient_le r hr y)
    rw [hUt] at h
    exact h
  have h6c := h6a hT d χ hP hL hO hsm6 amp hamp P hP2 R S u hu
  dsimp only at h6c
  obtain ⟨-, -, -, -, h537, -⟩ := h6c
  have hu2 := (h537 2).2
  have hN0 : S5.uNorm (S5.radius D a) (S5.width lam) 2 Bs + S5.uNorm (S5.radius D a) (S5.width lam) 2 fs ≤
      |KP6 2 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ) :=
    hu2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (hDp _))
      (Real.rpow_nonneg hlam0.le _))
  have hBu0 := Bridge.uNorm_nonneg (S5.radius D a) (S5.width lam) 2 hT Bs
  have hfu0 := Bridge.uNorm_nonneg (S5.radius D a) (S5.width lam) 2 hT fs
  have hH : ∀ g₀ : HierarchyTwistedProfile T k Vec3,
      (∀ r ∈ Icc 0 T, ∀ y s, g₀.val.val.val (r, y, s) = g₀.val.val.val (r, y, 0)) →
      S5.uNorm (S5.radius D a) (S5.width lam) 2 g₀ ≤ |KP6 2 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ) →
      ∀ r ∈ Icc 0 T, SpatialHolderHalf 1 (fun y => g₀.val.val.val (r, X r 0 y, 0)) ∧
        spatialHolderHalfNorm 1 (fun y => g₀.val.val.val (r, X r 0 y, 0)) ≤
          (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ) := by
    intro g₀ hind hg₀ r hr
    have h7c := h7a hT hP hL hO g₀ fun r' hr' y _ s => hind r' hr' y s
    dsimp only at h7c
    have h1 := (h7c.2.2 hind).2 1 r hr
    have hF : graphRead (fun t => X t 0) g₀ r = fun y => g₀.val.val.val (r, X r 0 y, 0) := by
      funext y
      exact hind r hr _ _
    rw [hF] at h1
    refine ⟨h1.2.1, h1.2.2.trans ?_⟩
    have hu0 := Bridge.uNorm_nonneg (S5.radius D a) (S5.width lam) 2 hT g₀
    rw [mul_one]
    calc K7 1 * (D ^ C7) ^ (1 + 1) * S5.uNorm (S5.radius D a) (S5.width lam) (1 + 1) g₀ ≤
          |K7 1| * (D ^ C7) ^ (1 + 1) * (|KP6 2 P| * D ^ C6 * lam ^ (-5 / 2 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hg₀ hu0
            (by positivity)
      _ = (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ) := by
          rw [pow_add, ← pow_mul]
          ring_nf
  have hCm0 : 0 ≤ |K7 1| * |KP6 2 P| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hMV0 : 0 ≤ (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hCm0 (hDp _)) (Real.rpow_nonneg hlam0.le _)
  have hBsind : ∀ r ∈ Icc 0 T, ∀ y s, Bs.val.val.val (r, y, s) = Bs.val.val.val (r, y, 0) := by
    have hI := Bridge.phaseIndependent_of_average_eq d hsol.phase_independent
    exact fun r hr y s => hI (r, y, 0) ⟨hr, mem_univ _⟩ s
  have hfsind : ∀ r ∈ Icc 0 T, ∀ y s, fs.val.val.val (r, y, s) = fs.val.val.val (r, y, 0) := by
    have hI := Bridge.phaseIndependent_of_average_eq d havg
    exact fun r hr y s => hI (r, y, 0) ⟨hr, mem_univ _⟩ s
  have hVsize := hH Bs hBsind (by linarith)
  have hfsize := hH fs hfsind (by linarith)
  have hbd := meanPressureHessian_closedSlab_bound (T := T) (U := U) (V := bE) (f := fE)
    (q := qE) (MU := Cu * D ^ 2)
    (MV := (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ))
    (Mf := (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ)) hT
    (hP.velocity_smooth.of_le (by simp)) (hbs.of_le (by simp))
    (fun r hr => meanInt_slice_spatial hqs hr) (fun r hr => (hper r hr).2)
    hP.velocity_periodic (fun r hr => (hper r hr).1) hfper hP.divergence_free
    (fun r hr y => (heq r hr y).1) hMom hUsize hVsize hfsize
  dsimp only at hbd
  obtain ⟨hHt, -, -⟩ := hbd
  have hQs : graphRead (fun t => X t 0) Qs t = qE t := by
    funext y
    exact pressure_phase_const d hsol.pressure_phase_independent ht _ _
  have hrate := meanPressureHessian_rate_absorption (D := D) (frequency := lam)
    (MU := Cu * D ^ 2) (MV := (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ))
    (Mf := (|K7 1| * |KP6 2 P|) * D ^ (2 * C7 + C6) * lam ^ (-5 / 2 : ℝ))
    (Cparent := Cu) (Cmean := |K7 1| * |KP6 2 P|) (b := 2 * C7 + C6) hD hlam0 hCu hCm0 hMV0
    le_rfl le_rfl le_rfl
  change ‖fderiv ℝ (gradient (graphRead (fun t => X t 0) Qs t)) x‖ ≤ _
  rw [hQs]
  have hx := norm_apply_le_spatialHolderHalfNorm_zero (hHt t ht).1 x
  refine hx.trans ((hHt t ht).2.trans (hrate.trans (le_of_eq ?_)))
  rw [show 2 * C7 + C6 + 2 = 2 + (2 * C7 + C6) by ring]

end

end TorusEuler.Paper.Lib.S5c
