import Breakdown.CertCell.TailAngularPlane
import Breakdown.CertCell.TailRayModes
import Breakdown.CertCell.TailGradFinite
import Breakdown.CertCell.TailCoefficients
import Breakdown.CertCell.TailPointwise

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open PieceWeights

namespace Internal.ExteriorLinks

theorem dominates_withStretch {a lo : PointCoef} (hD : a.Dominates lo)
    {s c c' g0 g0' g1 g1' len len' cc gc vc : ℝ} (hs : 0 ≤ s) (hc : c ≤ c') (hg0 : g0 ≤ g0')
    (hg1 : g1 ≤ g1') (hll : len = len') (hlen : 0 < len') :
    (a.withStretch s c g0 g1 len cc gc vc).Dominates (lo.withStretch s c' g0' g1' len' cc gc vc) := by
  subst hll
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hD
  simp only [PointCoef.Dominates, PointCoef.withStretch]
  have hs2 : 0 ≤ s / 2 := by positivity
  refine ⟨d1, d2, by linarith, ?_, ?_, ?_⟩
  · have : s / 2 * g1 * len ≤ s / 2 * g1' * len := by gcongr
    linarith
  · have : s / 2 * g1 / len ≤ s / 2 * g1' / len := by gcongr
    linarith
  · have : s * g0 ≤ s * g0' := by gcongr
    linarith

theorem quad_lower (hQ : PointwiseQuadraticTest) {a lo : PointCoef}
    {kLow k r ρ gl vh ch x2 xc x1 xo x0 : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hk : kLow ≤ k)
    (hD : a.Dominates lo) (hcg : 0 ≤ a.curlGrad) (hh : 0 ≤ lo.hess) (hg : gl ≤ lo.gradFloor kLow r)
    (hv : ρ ^ 2 * max (-lo.vel) 0 ≤ vh) (hc : ρ * lo.cross ≤ ch)
    (hang : AngularRelations k r x2 xc x1 xo x0) :
    gl * x1 ^ 2 - vh / ρ ^ 2 * x0 ^ 2 - ch / ρ * x1 * x0 ≤ a.quad x2 xc x1 xo x0 := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hD
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hvel : -lo.vel ≤ vh / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]
    nlinarith [le_max_left (-lo.vel) 0]
  have hcr : lo.cross ≤ ch / ρ := by
    rw [le_div_iff₀ hρ]
    linarith
  have key := hQ
    { hess := lo.hess, curlGrad := lo.curlGrad, curl := lo.curl, grad := lo.grad - gl,
      vel := lo.vel + vh / ρ ^ 2, cross := 0 }
    { hess := a.hess, curlGrad := a.curlGrad, curl := a.curl, grad := a.grad - gl,
      vel := a.vel + vh / ρ ^ 2, cross := a.cross - ch / ρ }
    kLow k r 0 x2 xc x1 xo x0 hr hk hcg
    (by
      simp only [PointCoef.Dominates]
      refine ⟨d1, d2, d3, by linarith, by linarith, by linarith⟩)
    (by
      simp only [PointCoef.PassesTest, PointCoef.gradFloor, PointCoef.curlWithGain,
        PointCoef.velWithShift] at hg ⊢
      refine ⟨hh, le_rfl, by linarith, by simp only [zero_mul, zero_div, add_zero]; linarith, ?_⟩
      have h1 : 0 ≤ lo.grad - gl + 2 * min (lo.curl + lo.curlGrad * max (kLow - 1) 0 ^ 2 / r ^ 2) 0
          + lo.hess * max (kLow - 2) 0 ^ 2 / r ^ 2 - 0 := by linarith
      have h2 : 0 ≤ lo.vel + vh / ρ ^ 2 + 0 * max (kLow - 1) 0 ^ 2 / r ^ 2 := by
        simp only [zero_mul, zero_div, add_zero]
        linarith
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) h1) h2
      simpa using this)
    hang
  simp only [PointCoef.quad] at key ⊢
  nlinarith [key]

theorem cross_le {ch ρ s x1 x0 : ℝ} (hch : 0 ≤ ch) (hρ : 0 < ρ) (hs : 0 < s) :
    ch / ρ * x1 * x0 ≤ ch / (2 * s) * x1 ^ 2 + ch * s / 2 * (x0 ^ 2 / ρ ^ 2) := by
  have e : ch / (2 * s) * x1 ^ 2 + ch * s / 2 * (x0 ^ 2 / ρ ^ 2) - ch / ρ * x1 * x0
      = ch / (2 * s) * (x1 - s * x0 / ρ) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ ch / (2 * s) * (x1 - s * x0 / ρ) ^ 2 := by positivity
  linarith

theorem coeff_facts {c vh ch gl : ℝ} (hc : 0 < c) (hvh : 0 ≤ vh) (hch : 0 ≤ ch)
    (ht : vh / c + ch / Real.sqrt c ≤ gl) :
    0 ≤ vh + ch * Real.sqrt c / 2 ∧ vh + ch * Real.sqrt c / 2 ≤ (gl - ch / (2 * Real.sqrt c)) * c ∧
      0 ≤ gl - ch / (2 * Real.sqrt c) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s * s := ⟨Real.sqrt c, Real.sqrt_pos.2 hc, (Real.mul_self_sqrt hc.le).symm⟩
  rw [Real.sqrt_mul_self hs.le] at ht ⊢
  have h1 : 0 ≤ vh + ch * s / 2 := by positivity
  have e1 : (vh / (s * s) + ch / s) * (s * s) = vh + ch * s := by
    field_simp
  have e2 : (gl - ch / (2 * s)) * (s * s) = gl * (s * s) - ch * s / 2 := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right ht hc.le
  rw [e1] at h3
  have h2 : vh + ch * s / 2 ≤ (gl - ch / (2 * s)) * (s * s) := by
    rw [e2]
    linarith
  refine ⟨h1, h2, ?_⟩
  by_contra hneg
  have : (gl - ch / (2 * s)) * (s * s) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hc
  linarith

theorem ofReal_sub_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (x - y) + ENNReal.ofReal y = ENNReal.ofReal (y - x) + ENNReal.ofReal x := by
  rcases le_total x y with hxy | hxy
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_add, ← ENNReal.ofReal_add (by linarith) hx]
    congr 1
    ring
  · rw [ENNReal.ofReal_of_nonpos (show y - x ≤ 0 by linarith), zero_add, ← ENNReal.ofReal_add (by linarith) hy]
    congr 1
    ring

theorem lintegral_neg_le {μ : Measure (ℝ × ℝ)} {S V D : ℝ × ℝ → ℝ} {α γ c : ℝ} (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hαγ : α ≤ γ * c)
    (hS0 : ∀ᵐ p ∂μ, 0 ≤ S p) (hV0 : ∀ᵐ p ∂μ, 0 ≤ V p) (hD : ∀ᵐ p ∂μ, γ * S p - α * V p ≤ D p)
    (hVm : AEMeasurable (fun p => ENNReal.ofReal (V p)) μ)
    (hinv : ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (S p) ∂μ)
    (hfin : ∫⁻ p, ENNReal.ofReal (S p) ∂μ < ⊤) :
    ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (D p) ∂μ := by
  have hmulS : ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ = ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (S p) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun p => ENNReal.ofReal_mul hγ
  have hmulV : ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ = ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun p => ENNReal.ofReal_mul hα
  have hαV : ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ := by
    rw [hmulS, hmulV]
    calc ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ
        ≤ ENNReal.ofReal γ * ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ := by
          rw [← ENNReal.ofReal_mul hγ]
          gcongr
      _ = ENNReal.ofReal γ * (ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ) := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (S p) ∂μ := by gcongr
  have hfinS : ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ ≠ ⊤ := by
    rw [hmulS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hVm' : AEMeasurable (fun p => ENNReal.ofReal (α * V p)) μ := by
    have := hVm.const_mul (ENNReal.ofReal α)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only
    rw [ENNReal.ofReal_mul hα]
  have hkey : ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ := by
    have hsum : ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ
        ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ := by
      calc ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ
          ≤ ∫⁻ p, (ENNReal.ofReal (α * V p - γ * S p) + ENNReal.ofReal (γ * S p)) ∂μ := le_lintegral_add _ _
        _ = ∫⁻ p, (ENNReal.ofReal (γ * S p - α * V p) + ENNReal.ofReal (α * V p)) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hS0, hV0] with p hs hv
          exact ofReal_sub_add (mul_nonneg hα hv) (mul_nonneg hγ hs)
        _ = ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ + ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ :=
          lintegral_add_right' _ hVm'
        _ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ + ∫⁻ p, ENNReal.ofReal (γ * S p) ∂μ := by
          gcongr
    exact (ENNReal.add_le_add_iff_right hfinS).1 hsum
  calc ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (α * V p - γ * S p) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD] with p hp
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ∫⁻ p, ENNReal.ofReal (γ * S p - α * V p) ∂μ := hkey
    _ ≤ ∫⁻ p, ENNReal.ofReal (D p) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD] with p hp
        exact ENNReal.ofReal_le_ofReal hp

theorem continuous_planeRadius : Continuous planeRadius := by
  unfold planeRadius
  exact Real.continuous_sqrt.comp (by fun_prop)

theorem continuous_cnormSq {β : Type*} [Fintype β] : Continuous (fun x : β → ℂ => cnormSq x) := by
  unfold cnormSq
  fun_prop

theorem cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x := by
  unfold cnormSq
  positivity

end Internal.ExteriorLinks

open Internal.ExteriorLinks in
theorem exteriorConditionSound_of_bounds (hA : AngularModeBounds) (hQ : PointwiseQuadraticTest)
    (hU : UniformCoefficientBounds) (hF : LabelGradFinite) (hR : ModeRayInverseSquare)
    (hS : ModeSquareInverseSquare) : ExteriorConditionSound := by
  intro C nE nM m P h w W HW w₀ epsSup epsGradSup ratio hm mm E mc hE Γ v G H g hv ι hι hflip
  have hP : 0 < P := hm.period_pos
  have hk : E.pieces.azimuthLow ≤ |(labelAzimuth mm ι : ℝ)| := hE.pieces_valid.azimuth_ge ι hι
  have hhalf : MeasurableSet halfPlane := measurableSet_Ioi.prod measurableSet_Ioi
  have hZ : E.region ⊆ halfPlane ∧ MeasurableSet E.region := by
    rcases hE.shape with ⟨R, R₀, R₁, hRd, hreg, -⟩ | ⟨R, -, hreg, -, -⟩
    · rw [hreg]
      exact ⟨fun p hp => hp.1, hhalf.inter (measurableSet_lt hRd.measurable continuous_planeRadius.measurable)⟩
    · rw [hreg]
      exact ⟨fun p hp => hp.1, hhalf.inter ((measurableSet_lt measurable_const measurable_fst).union
        (measurableSet_lt measurable_const measurable_snd))⟩
  have hinv : ENNReal.ofReal E.inverseSquareConst
      * ∫⁻ p in E.region, ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1)
      ≤ ∫⁻ p in E.region, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) := by
    rcases hE.shape with ⟨R, R₀, R₁, hRd, hreg, hcle⟩ | ⟨R, hR0, hreg, hcle, hz⟩
    · have key := hR R R₀ R₁ hRd Γ P v G H g hv hP mm ι
      rw [← hreg] at key
      refine le_trans ?_ key
      gcongr
      refine hcle.trans ?_
      unfold rayInverseSquareConst
      have : max (E.pieces.azimuthLow - 1) 0 ≤ max (|(labelAzimuth mm ι : ℝ)| - 1) 0 :=
        max_le_max (by linarith) le_rfl
      have h0 : 0 ≤ max (E.pieces.azimuthLow - 1) 0 := le_max_right _ _
      nlinarith
    · have hz' := hz ι hι
      have key := hS R hR0 Γ P v G H g hv hP mm ι hz' (hflip R hreg hz')
      rw [← hreg] at key
      refine le_trans ?_ key
      gcongr
  have hfin : ∫⁻ p in E.region, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hZ.1) (hF Γ P v G H g hv hP mm ι)
  have hVm : AEMeasurable (fun p => ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1))
      (volume.restrict E.region) := by
    have h1 := ((aestronglyMeasurable_labelFields hv mm ι).1).mono_measure (Measure.restrict_mono hZ.1 le_rfl)
    have h2 := (continuous_cnormSq.comp_aestronglyMeasurable h1).aemeasurable
    exact ((h2.div (continuous_planeRadius.measurable.pow_const 2).aemeasurable).mul
      measurable_fst.aemeasurable).ennreal_ofReal
  obtain ⟨hα, hαγ, hγ⟩ := coeff_facts hE.inverseSquareConst_pos hE.velHigh_nonneg hE.crossHigh_nonneg hE.test
  have hs : 0 < Real.sqrt E.inverseSquareConst := Real.sqrt_pos.2 hE.inverseSquareConst_pos
  have hang := ae_restrict_of_ae_restrict_of_subset hZ.1 (hA Γ P v G H g hv hP mm ι)
  have hmem := ae_restrict_mem (μ := volume) hZ.2
  refine lintegral_neg_le hα hγ hαγ ?_ ?_ ?_ hVm hinv hfin
  · filter_upwards [hmem] with p hp
    exact mul_nonneg (cnormSq_nonneg _) (Set.mem_prod.mp (hZ.1 hp)).1.le
  · filter_upwards [hmem] with p hp
    exact mul_nonneg (div_nonneg (cnormSq_nonneg _) (sq_nonneg _)) (Set.mem_prod.mp (hZ.1 hp)).1.le
  · filter_upwards [hmem, hang] with p hp hpa
    have hr : 0 < p.1 := (Set.mem_prod.mp (hZ.1 hp)).1
    have hρ : 0 < planeRadius p := Real.sqrt_pos.2 (by positivity)
    obtain ⟨hsc, hcov⟩ := hE.charges_cover
    obtain ⟨h1, h2, h3, h4, h5⟩ := hcov ι hι p hp
    have hD := hU m P h w W HW w₀ epsSup epsGradSup ratio hm E.pieces mm E.modes E.region hE.pieces_valid ι hι p hp
    have hdom := dominates_withStretch (s := E.charges.stretchConst) (cc := E.charges.curlCharge p)
      (gc := E.charges.gradCharge p) (vc := E.charges.velCharge p) hD hsc h1 h2 h3 h4 h5
    have hcg : 0 ≤ (modeCoef m P h w mm ι p).curlGrad := by
      have := hm.conv_le (labelHarmonic mm ι) (planePoint p)
      simp only [modeCoef, PointCoef.ofMode, ModeCoefficients.ofPieces]
      linarith
    have hq := quad_lower hQ hr hρ hk hdom hcg (hE.hess_nonneg p hp) (hE.grad_floor p hp)
      (hE.vel_ceiling p hp) (hE.cross_ceiling p hp) hpa
    have hx := cross_le (x1 := Real.sqrt (cnormSq (labelGrad mm ι G p)))
      (x0 := Real.sqrt (cnormSq (labelVel mm ι v p))) hE.crossHigh_nonneg hρ hs
    rw [Real.sq_sqrt (cnormSq_nonneg _), Real.sq_sqrt (cnormSq_nonneg _)] at hq hx
    have hden : offModeDensity m P h w mc E.charges mm ι v G H p
        = ((modeCoef m P h w mm ι p).withStretch E.charges.stretchConst (mc.curl ι p) (mc.product ι p)
          (mc.gradient ι p) (mc.length ι p) (E.charges.curlCharge p) (E.charges.gradCharge p)
          (E.charges.velCharge p)).quad (Real.sqrt (cnormSq (labelHess mm ι H p)))
          (Real.sqrt (cnormSq (curlGradOfSecondDeriv (labelHess mm ι H p))))
          (Real.sqrt (cnormSq (labelGrad mm ι G p))) (Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))))
          (Real.sqrt (cnormSq (labelVel mm ι v p))) := rfl
    have hpt : (E.gradLow - E.crossHigh / (2 * Real.sqrt E.inverseSquareConst)) * cnormSq (labelGrad mm ι G p)
        - (E.velHigh + E.crossHigh * Real.sqrt E.inverseSquareConst / 2)
          * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2) ≤ offModeDensity m P h w mc E.charges mm ι v G H p := by
      have e : (E.gradLow - E.crossHigh / (2 * Real.sqrt E.inverseSquareConst)) * cnormSq (labelGrad mm ι G p)
          - (E.velHigh + E.crossHigh * Real.sqrt E.inverseSquareConst / 2)
            * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)
          = (E.gradLow * cnormSq (labelGrad mm ι G p) - E.velHigh / planeRadius p ^ 2 * cnormSq (labelVel mm ι v p))
            - (E.crossHigh / (2 * Real.sqrt E.inverseSquareConst) * cnormSq (labelGrad mm ι G p)
              + E.crossHigh * Real.sqrt E.inverseSquareConst / 2
                * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)) := by ring
      rw [e, hden]
      linarith
    have := mul_le_mul_of_nonneg_right hpt hr.le
    calc _ = ((E.gradLow - E.crossHigh / (2 * Real.sqrt E.inverseSquareConst)) * cnormSq (labelGrad mm ι G p)
        - (E.velHigh + E.crossHigh * Real.sqrt E.inverseSquareConst / 2)
          * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)) * p.1 := by ring
      _ ≤ _ := this

theorem exteriorConditionSound_of_square (hS : ModeSquareInverseSquare) : ExteriorConditionSound :=
  exteriorConditionSound_of_bounds angularModeBounds pointwiseQuadraticTest uniformCoefficientBounds
    labelGradFinite modeRayInverseSquare hS

end TailBand

end CertCell

end Breakdown
