import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoercivePieceAbsorbMeasure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothDensity

open PairingSplitInternal (periodMeasure)
open ModeL2Internal (IsSquareField)

namespace BaseBound

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  unfold unitVector
  simp

theorem period_ac : periodMeasure ≪ (volume : Measure (ℝ × Space)) := by
  rw [PairingSplitInternal.periodMeasure_eq]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

theorem lt_top_of_le {f g : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hfg : ∀ σ y, f σ y ≤ c * g σ y) (hg : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ := by
  unfold periodLIntegral at hg ⊢
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (g σ y) := by
        refine lintegral_mono fun σ => lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (hfg σ y)
    _ = ENNReal.ofReal c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg

def scaled (v : ℝ → Space → Space) : ℝ → Space → Space := fun σ y => (1 + ‖y‖)⁻¹ • v σ y

theorem axialRot_smul_apply (φ a : ℝ) (x : Space) (i : Fin 3) :
    axialRot φ (a • x) i = a * axialRot φ x i := by
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem cnormSq_modeVel_scaled (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (scaled v) σ y) = cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 := by
  have hrot : ∀ φ : ℝ, ‖axialRot φ y‖ = ‖y‖ := fun φ => PairingSplitInternal.norm_axialRot φ y
  have e : ∀ i, modeVel ι (scaled v) σ y i = ((1 + ‖y‖)⁻¹ : ℝ) * modeVel ι v σ y i := by
    intro i
    have e1 : ∀ τ φ : ℝ, axialRot (-φ) (scaled v (σ + τ) (axialRot φ y)) i
        = (1 + ‖y‖)⁻¹ * axialRot (-φ) (v (σ + τ) (axialRot φ y)) i := by
      intro τ φ
      unfold scaled
      rw [axialRot_smul_apply, hrot]
    unfold modeVel modeAverage
    simp only [e1]
    push_cast
    have e2 : ∀ τ φ : ℝ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * (((1 + ‖y‖ : ℝ) : ℂ)⁻¹ * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) i : ℝ) : ℂ))
        = ((1 + ‖y‖ : ℝ) : ℂ)⁻¹ * (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
          * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) i : ℝ) : ℂ)) := fun τ φ => by ring
    push_cast at e2
    simp only [e2, intervalIntegral.integral_const_mul]
    ring
  have hpos : 0 < 1 + ‖y‖ := by positivity
  unfold cnormSq
  simp only [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum, inv_pow, div_eq_inv_mul]

end BaseBound

namespace BaseBound

variable {P : ℝ} {v : ℝ → Space → Space}

theorem smooth_two (hv : IsSmoothPerturbation P v) : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) :=
  hv.smooth.of_le (by norm_cast)

theorem norm_secondDerivField (σ : ℝ) (y : Space) :
    ‖secondDerivField v σ y‖ = ‖iteratedFDeriv ℝ 2 (v σ) y‖ := by
  unfold secondDerivField
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem secondDerivSq_le (H : Space →L[ℝ] Space →L[ℝ] Space) : secondDerivSq H ≤ 9 * ‖H‖ ^ 2 := by
  have h : ∀ j l : Fin 3, ‖H (unitVector j) (unitVector l)‖ ^ 2 ≤ ‖H‖ ^ 2 := by
    intro j l
    have h1 : ‖H (unitVector j) (unitVector l)‖ ≤ ‖H‖ := by
      calc ‖H (unitVector j) (unitVector l)‖ ≤ ‖H (unitVector j)‖ * ‖unitVector l‖ :=
            (H (unitVector j)).le_opNorm _
        _ ≤ ‖H‖ * ‖unitVector j‖ * ‖unitVector l‖ := by
            gcongr; exact H.le_opNorm _
        _ = ‖H‖ := by rw [unit_norm, unit_norm, mul_one, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  unfold secondDerivSq
  simp only [Fin.sum_univ_three]
  linarith [h 0 0, h 0 1, h 0 2, h 1 0, h 1 1, h 1 2, h 2 0, h 2 1, h 2 2]

theorem matSq_le (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    intro i
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      calc ‖G (unitVector i)‖ ≤ ‖G‖ * ‖unitVector i‖ := G.le_opNorm _
        _ = ‖G‖ := by rw [unit_norm, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  unfold matSq
  simp only [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem secondDeriv_facts (hv : IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) volume ∧ IsTimePeriodic (secondDerivField v) ∧
      periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ := by
  refine ⟨(Internal.PieceAbsorb.measurable_secondDeriv_slice (smooth_two hv)).aestronglyMeasurable, fun σ y => ?_, ?_⟩
  · unfold secondDerivField
    rw [show v (σ + 1) = v σ from funext (hv.periodic σ)]
  · refine lt_top_of_le (c := 9) (by norm_num) (fun σ y => ?_) (hv.derivatives_finite 2 (by norm_num))
    rw [← norm_secondDerivField]
    exact secondDerivSq_le _

theorem grad_facts (hv : IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume ∧ IsTimePeriodic (gradField v) ∧
      periodLIntegral (fun σ y => matSq (gradField v σ y)) < ⊤ := by
  refine ⟨(Internal.PieceAbsorb.continuous_fderiv_slice (smooth_two hv)).aestronglyMeasurable,
    fun σ y => ?_, ?_⟩
  · unfold gradField
    rw [show v (σ + 1) = v σ from funext (hv.periodic σ)]
  · refine lt_top_of_le (c := 3) (by norm_num) (fun σ y => ?_) (hv.derivatives_finite 1 le_rfl)
    rw [norm_iteratedFDeriv_one]
    exact matSq_le _

theorem scaled_facts (hv : IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => scaled v z.1 z.2) volume ∧ IsTimePeriodic (scaled v) ∧
      periodLIntegral (fun σ y => ‖scaled v σ y‖ ^ 2) < ⊤ := by
  have hc : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖)⁻¹) :=
    Continuous.inv₀ (by fun_prop) fun z => by positivity
  refine ⟨(hc.smul hv.smooth.continuous).aestronglyMeasurable, fun σ y => ?_, ?_⟩
  · unfold scaled
    rw [hv.periodic σ y]
  · have e : (fun σ y => ‖scaled v σ y‖ ^ 2) = fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by
      funext σ y
      have hpos : 0 < 1 + ‖y‖ := by positivity
      unfold scaled
      rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_pow, div_eq_inv_mul]
    rw [e]
    exact hv.weighted_finite

end BaseBound

namespace BaseBound

theorem real_bound {c d z hd hz w BD BZ HD Bw r X2 Xc Xo X1 X0 : ℝ} (hc : 0 < c) (hd0 : 0 ≤ d) (hdB : d ≤ BD)
    (hz0 : |z| ≤ BZ) (hhd : hd ≤ HD) (hw : w ≤ Bw) (hr : 0 < 1 + r) (hhz : (1 + r) ^ 2 * hz ≤ BZ)
    (h2 : 0 ≤ X2) (hcX : 0 ≤ Xc) (ho : 0 ≤ Xo) (h1 : 0 ≤ X1) (h0 : 0 ≤ X0) :
    -((d - c) * X2 + (1 - d) * Xc + (1 / 4 - z) * Xo + (z - hd - c * w) * X1 - hz * X0) ≤
      (c + BD + 1 + BZ + |HD| + c * |Bw|) * (X2 + Xc + Xo + X1) + BZ * (X0 / (1 + r) ^ 2) := by
  have hBZ : 0 ≤ BZ := (abs_nonneg z).trans hz0
  have hzz := abs_le.1 hz0
  have hA : 0 ≤ |HD| + c * |Bw| := add_nonneg (abs_nonneg _) (mul_nonneg hc.le (abs_nonneg _))
  have hcw : c * w ≤ c * |Bw| := mul_le_mul_of_nonneg_left (hw.trans (le_abs_self _)) hc.le
  have e1 : (c - d) * X2 ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * X2 :=
    mul_le_mul_of_nonneg_right (by linarith) h2
  have e2 : (d - 1) * Xc ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * Xc :=
    mul_le_mul_of_nonneg_right (by linarith) hcX
  have e3 : (z - 1 / 4) * Xo ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * Xo :=
    mul_le_mul_of_nonneg_right (by linarith) ho
  have e4 : (-z + hd + c * w) * X1 ≤ (c + BD + 1 + BZ + |HD| + c * |Bw|) * X1 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self HD]) h1
  have hr2 : 0 < (1 + r) ^ 2 := by positivity
  have e5 : hz * X0 ≤ BZ * (X0 / (1 + r) ^ 2) := by
    rw [mul_div_assoc', le_div_iff₀ hr2]
    nlinarith [mul_le_mul_of_nonneg_right hhz h0]
  nlinarith [e1, e2, e3, e4, e5]

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {v : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem secondDerivD_bound (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) :
    ∃ HD, ∀ c y, ModeWeights.secondDerivNorm (m.convD c) y ≤ HD := by
  obtain ⟨BD, hBD⟩ := hm.convD_decay
  have hK : ∀ c, ∃ K, ∀ y ∈ Metric.closedBall (0 : Space) 1, ‖iteratedFDeriv ℝ 2 (m.convD c) y‖ ≤ K :=
    fun c => (isCompact_closedBall 0 1).exists_bound_of_continuousOn
      ((ContDiff.continuous_iteratedFDeriv (m := 2) le_rfl (hm.convD_smooth c)).continuousOn)
  choose K hK using hK
  have := hm.finite_classes
  have := Fintype.ofFinite C
  refine ⟨|BD| + ∑ c, |K c|, fun c y => ?_⟩
  unfold ModeWeights.secondDerivNorm
  have hKc : |K c| ≤ ∑ c, |K c| := Finset.single_le_sum (fun c _ => abs_nonneg (K c)) (Finset.mem_univ c)
  have hs : 0 ≤ ∑ c, |K c| := Finset.sum_nonneg fun c _ => abs_nonneg (K c)
  by_cases hy : ‖y‖ ≤ 1
  · have h := hK c y (by simpa using hy)
    linarith [le_abs_self (K c), abs_nonneg BD]
  · replace hy := not_le.1 hy
    have h2 := hBD c y 2 le_rfl
    have hn := norm_nonneg (iteratedFDeriv ℝ 2 (m.convD c) y)
    have h1 : 1 ≤ ‖y‖ ^ 2 := by nlinarith
    have : ‖iteratedFDeriv ℝ 2 (m.convD c) y‖ ≤ BD := by nlinarith
    linarith [le_abs_self BD]

end BaseBound

namespace BaseBound

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {v : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem pointwise (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hwb : ∃ B, ∀ y, w y ≤ B) :
    ∃ A BZ : ℝ, 0 ≤ A ∧ 0 ≤ BZ ∧ ∀ ι σ y,
      ENNReal.ofReal (-modeValues v ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)) ≤
        ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y))
          + ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y))
          + ENNReal.ofReal BZ * ENNReal.ofReal (cnormSq (modeVel ι (scaled v) σ y)) := by
  obtain ⟨BD, hBD⟩ := hm.convD_decay
  obtain ⟨BZ, hBZ⟩ := hm.convZ_decay
  obtain ⟨Bw, hBw⟩ := hwb
  obtain ⟨HD, hHD⟩ := secondDerivD_bound hm
  have hc := hm.c_pos
  have hBZ0 : 0 ≤ BZ := by
    have := hBZ (m.classOf 0) 0 0 (by norm_num)
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans this
  set A := m.c + BD + 1 + BZ + |HD| + m.c * |Bw| with hAdef
  have hBD0 : 0 ≤ BD := by
    have := hBD (m.classOf 0) 0 0 (by norm_num)
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans this
  have hA : 0 ≤ A := by
    rw [hAdef]
    have := abs_nonneg HD
    have := mul_nonneg hc.le (abs_nonneg Bw)
    linarith
  refine ⟨730 * A, BZ, by positivity, hBZ0, fun ι σ y => ?_⟩
  set h := cnormSq (modeSecondDeriv ι (secondDerivField v) σ y) with hh
  set g := cnormSq (modeGrad ι (gradField v) σ y) with hg
  have hh0 : 0 ≤ h := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg0 : 0 ≤ g := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs := cnormSq_modeVel_scaled v ι σ y
  have hv0 : 0 ≤ cnormSq (modeVel ι v σ y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsn : 0 ≤ cnormSq (modeVel ι (scaled v) σ y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hxc : cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y)) ≤ 729 * h :=
    Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le _
  have hxo : cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y)) ≤ 243 * g :=
    Internal.PieceAbsorb.cnormSq_curlOfGrad_le _
  have hc0 : 0 ≤ cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y)) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ho0 : 0 ≤ cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y)) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd0 := hm.convD_nonneg (m.classOf ι) y
  have hdB : m.convD (m.classOf ι) y ≤ BD := by
    have := hBD (m.classOf ι) y 0 (by norm_num)
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hz : |m.convZ (m.classOf ι) y| ≤ BZ := by
    have := hBZ (m.classOf ι) y 0 (by norm_num)
    rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hhz : (1 + ‖y‖) ^ 2 * ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y ≤ BZ :=
    hBZ (m.classOf ι) y 2 le_rfl
  have key := real_bound (c := m.c) (d := m.convD (m.classOf ι) y) (z := m.convZ (m.classOf ι) y)
    (hd := ModeWeights.secondDerivNorm (m.convD (m.classOf ι)) y) (hz := ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y)
    (w := w y) (r := ‖y‖) (X2 := h) (Xc := cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y)))
    (Xo := cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y))) (X1 := g)
    (X0 := cnormSq (modeVel ι v σ y)) hc hd0 hdB hz (hHD _ y) (hBw y) (by positivity) hhz hh0 hc0 ho0 hg0 hv0
  have hval : modeValues v ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y) =
      (m.convD (m.classOf ι) y - m.c) * h
        + (1 - m.convD (m.classOf ι) y) * cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y))
        + (1 / 4 - m.convZ (m.classOf ι) y) * cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y))
        + (m.convZ (m.classOf ι) y - ModeWeights.secondDerivNorm (m.convD (m.classOf ι)) y - m.c * w y) * g
        - ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * cnormSq (modeVel ι v σ y) := by
    unfold modeValues baseDensity
    rw [Real.sq_sqrt hh0, Real.sq_sqrt hc0, Real.sq_sqrt ho0, Real.sq_sqrt hg0, Real.sq_sqrt hv0]
  have hAin : A * (h + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y))
      + cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y)) + g) ≤ 730 * A * h + 730 * A * g := by
    nlinarith [mul_le_mul_of_nonneg_left hxc hA, mul_le_mul_of_nonneg_left hxo hA,
      mul_nonneg hA hh0, mul_nonneg hA hg0]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hBZ0, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg hBZ0 hsn)]
  apply ENNReal.ofReal_le_ofReal
  rw [hval, hs]
  linarith

end BaseBound

namespace BaseBound

theorem lint3 {μ : Measure (ℝ × Space)} {a b c : ℝ≥0∞} {f g h : ℝ × Space → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) :
    ∫⁻ x, (a * f x + b * g x + c * h x) ∂μ = a * ∫⁻ x, f x ∂μ + b * ∫⁻ x, g x ∂μ + c * ∫⁻ x, h x ∂μ := by
  have h1 : ∫⁻ x, (a * f x + b * g x + c * h x) ∂μ = ∫⁻ x, (a * f x + b * g x) ∂μ + ∫⁻ x, c * h x ∂μ :=
    lintegral_add_left' ((hf.const_mul a).add (hg.const_mul b)) _
  have h2 : ∫⁻ x, (a * f x + b * g x) ∂μ = ∫⁻ x, a * f x ∂μ + ∫⁻ x, b * g x ∂μ :=
    lintegral_add_left' (hf.const_mul a) _
  rw [h1, h2, lintegral_const_mul' _ _ ha, lintegral_const_mul' _ _ hb, lintegral_const_mul' _ _ hc]

end BaseBound

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W v : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem base_neg_finite (hPars : ModeSquareSumHolds) (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι,
      ENNReal.ofReal (-modeValues v ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))) < ⊤ := by
  obtain ⟨A, BZ, _, _, hpt⟩ := BaseBound.pointwise (v := v) hm hwb
  obtain ⟨hH1, hH2, hH3⟩ := BaseBound.secondDeriv_facts hv
  obtain ⟨hG1, hG2, hG3⟩ := BaseBound.grad_facts hv
  obtain ⟨hS1, hS2, hS3⟩ := BaseBound.scaled_facts hv
  have mh : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) periodMeasure := fun ι =>
    Internal.PieceAbsorb.aemeasurable_ofReal_cnormSq (Internal.PieceAbsorb.aemeasurable_modeSecondDeriv hH1 ι)
  have mg : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))) periodMeasure := fun ι =>
    Internal.PieceAbsorb.aemeasurable_ofReal_cnormSq ((aemeasurable_pi_iff.2 fun ij =>
      (Internal.FieldModes.aestronglyMeasurable_modeGrad hG1 ι ij).aemeasurable).mono_ac BaseBound.period_ac)
  have ms : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2))) periodMeasure := fun ι =>
    Internal.PieceAbsorb.aemeasurable_ofReal_cnormSq ((aemeasurable_pi_iff.2 fun i =>
      (Internal.FieldModes.aestronglyMeasurable_modeVel hS1 ι i).aemeasurable).mono_ac BaseBound.period_ac)
  have mF : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))
        + ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))
        + ENNReal.ofReal BZ * ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2))) periodMeasure :=
    fun ι => (((mh ι).const_mul _).add ((mg ι).const_mul _)).add ((ms ι).const_mul _)
  have fh : (∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) ∂periodMeasure) < ⊤ := by
    have e : ∀ ι, (∫⁻ z, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) ∂periodMeasure) =
        ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) :=
      fun ι => lintegral_prod _ (mh ι)
    simp only [e]
    rw [← hPars.2.2.1 _ hH1 hH2 hH3]
    exact hH3
  have fg : (∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2)) ∂periodMeasure) < ⊤ := by
    have e : ∀ ι, (∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2)) ∂periodMeasure) =
        ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)) :=
      fun ι => lintegral_prod _ (mg ι)
    simp only [e]
    rw [← hPars.2.1 _ hG1 hG2 hG3]
    exact hG3
  have fs : (∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2)) ∂periodMeasure)
      < ⊤ := by
    have e : ∀ ι, (∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2)) ∂periodMeasure) =
        ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) σ y)) :=
      fun ι => lintegral_prod _ (ms ι)
    simp only [e]
    rw [← hPars.1 _ hS1 hS2 hS3]
    exact hS3
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι,
        ENNReal.ofReal (-modeValues v ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι,
        (ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y))
          + ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y))
          + ENNReal.ofReal BZ * ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) σ y))) :=
        lintegral_mono fun σ => lintegral_mono fun y => ENNReal.tsum_le_tsum fun ι => hpt ι σ y
    _ = ∫⁻ z, ∑' ι, (ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))
          + ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))
          + ENNReal.ofReal BZ * ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2)))
          ∂periodMeasure := (lintegral_prod _ (AEMeasurable.ennreal_tsum mF)).symm
    _ = ∑' ι, ∫⁻ z, (ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))
          + ENNReal.ofReal A * ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))
          + ENNReal.ofReal BZ * ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2)))
          ∂periodMeasure := lintegral_tsum mF
    _ = ∑' ι, (ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) ∂periodMeasure
          + ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2)) ∂periodMeasure
          + ENNReal.ofReal BZ * ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2))
            ∂periodMeasure) := by
        congr 1
        funext ι
        exact BaseBound.lint3 (mh ι) (mg ι) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * (∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) ∂periodMeasure)
          + ENNReal.ofReal A * (∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))
            ∂periodMeasure)
          + ENNReal.ofReal BZ * (∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (BaseBound.scaled v) z.1 z.2))
            ∂periodMeasure) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top fh,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top fg⟩, ENNReal.mul_lt_top ENNReal.ofReal_lt_top fs⟩

end Internal.SmoothDensity

end Coercive

end Breakdown
