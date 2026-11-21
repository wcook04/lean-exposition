import Breakdown.FracCell.StWeightedInverseSquare
import Breakdown.FracCell.CylIntegral

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace ModeMeasurableInternal

open Breakdown.CellCert.Spectral.Internal.CylIntegral

theorem symm_eq (x : (ℝ × ℝ) × ℝ) :
    cylMap.symm x = ((x.1.1 * Real.cos x.1.2, x.1.1 * Real.sin x.1.2), x.2) := by
  simp [cylMap, polarCoord_symm_apply]

theorem symm_meas : Measurable (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) := by
  have : (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) =
      fun x => ((x.1.1 * Real.cos x.1.2, x.1.1 * Real.sin x.1.2), x.2) := funext symm_eq
  rw [this]
  fun_prop

theorem target_null {s : Set ((ℝ × ℝ) × ℝ)} (hs : MeasurableSet s) (h0 : volume s = 0) :
    volume (cylMap.target ∩ cylMap.symm ⁻¹' s) = 0 := by
  have hT : MeasurableSet cylMap.target := cylMap.open_target.measurableSet
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT
    (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn (s.indicator 1)
  have hle : ∫⁻ x in cylMap.symm '' cylMap.target, s.indicator 1 x ≤ 0 := by
    calc ∫⁻ x in cylMap.symm '' cylMap.target, s.indicator 1 x ≤ ∫⁻ x, s.indicator 1 x :=
          setLIntegral_le_lintegral _ _
      _ = volume s := lintegral_indicator_one hs
      _ = 0 := h0
  have hz : ∫⁻ x in cylMap.target, ENNReal.ofReal x.1.1 * s.indicator 1 (cylMap.symm x) = 0 := by
    have e : ∫⁻ x in cylMap.target, ENNReal.ofReal x.1.1 * s.indicator 1 (cylMap.symm x) =
        ∫⁻ x in cylMap.target, ENNReal.ofReal |(cylDeriv x).det| * s.indicator 1 (cylMap.symm x) := by
      refine setLIntegral_congr_fun hT fun x hx => ?_
      rw [abs_det_eq hx]
    rw [e, ← hc]
    exact nonpos_iff_eq_zero.mp hle
  have hm : Measurable fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * s.indicator 1 (cylMap.symm x) :=
    (measurable_fst.fst.ennreal_ofReal).mul ((measurable_one.indicator hs).comp symm_meas)
  rw [lintegral_eq_zero_iff hm] at hz
  rw [measure_eq_zero_iff_ae_notMem]
  have hz' := (ae_restrict_iff' hT).mp hz
  filter_upwards [hz'] with x hx
  rintro ⟨hxT, hxs⟩
  have h1 := hx hxT
  have hpos : 0 < x.1.1 := hxT.1.1
  simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero, Set.indicator_apply_eq_zero] at h1
  rcases h1 with h1 | h1
  · linarith
  · have := h1 hxs
    simp at this

def ringMap (p : (ℝ × ℝ) × ℝ) : Space := ringPoint p.1.1 p.2 p.1.2

theorem ringMap_eq (p : (ℝ × ℝ) × ℝ) : ringMap p = toSpace (cylMap.symm (swapEquiv p)) := by
  obtain ⟨⟨r, z⟩, θ⟩ := p
  rw [swapEquiv_apply, symm_eq, toSpace_apply]
  rfl

theorem single_cont (i : Fin 3) :
    Continuous fun t : ℝ => (EuclideanSpace.single i t : Space) := by
  have h : (fun t : ℝ => (EuclideanSpace.single i t : Space)) =
      fun t => t • (EuclideanSpace.single i 1 : Space) := by
    funext t
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  exact continuous_id.smul continuous_const

theorem ringMap_cont : Continuous ringMap := by
  unfold ringMap ringPoint
  exact (((single_cont 0).comp (by fun_prop)).add ((single_cont 1).comp (by fun_prop))).add
    ((single_cont 2).comp (by fun_prop))

theorem ringMap_qmp :
    Measure.QuasiMeasurePreserving ringMap
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) volume := by
  refine ⟨ringMap_cont.measurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [Measure.map_apply ringMap_cont.measurable hs, Measure.prod_restrict, ← Measure.volume_eq_prod,
    Measure.restrict_apply (ringMap_cont.measurable hs)]
  have hs' : MeasurableSet (toSpace ⁻¹' s) := toSpace.measurable hs
  have h0' : volume (toSpace ⁻¹' s) = 0 := by rw [toSpace_mp.measure_preimage_equiv]; exact h0
  have e : ringMap ⁻¹' s ∩ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-Real.pi) Real.pi =
      swapEquiv ⁻¹' (cylMap.target ∩ cylMap.symm ⁻¹' (toSpace ⁻¹' s)) := by
    rw [Set.preimage_inter, swapEquiv_preimage, Set.inter_comm]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, ringMap_eq]
  rw [e, swapEquiv_mp.measure_preimage_equiv]
  exact target_null hs' h0'

end ModeMeasurableInternal

open ModeMeasurableInternal in
theorem modeMeasurable : ModeMeasurableStatement := by
  intro u hu k
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hf : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      Complex.exp (-((k : ℂ) * (p.2 : ℂ) * Complex.I)) * u (ringPoint p.1.1 p.2 p.1.2))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
    rw [hν]
    refine AEStronglyMeasurable.mul ?_ (hu.comp_quasiMeasurePreserving ringMap_qmp)
    exact (by fun_prop : Continuous fun p : (ℝ × ℝ) × ℝ =>
      Complex.exp (-((k : ℂ) * (p.2 : ℂ) * Complex.I))).aestronglyMeasurable
  have hi := hf.integral_prod_right'
  have e : (fun q : ℝ × ℝ => angularMode u k q.1 q.2) = fun q =>
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi,
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * u (ringPoint q.1 θ q.2) := by
    funext q
    unfold angularMode
    rw [intervalIntegral.integral_of_le hpi]
  rw [e]
  exact aestronglyMeasurable_const.mul hi

namespace WeightedInverseSquareInternal

theorem mean_le (A B a s t : ℝ) (ha : 0 < a) (hs : 0 < s) (ht : 0 < t) :
    A * B ≤ t / 2 * (a ^ 2 * A ^ 2 / s) + 1 / (2 * t) * (s * (B ^ 2 / a ^ 2)) := by
  have key : t / 2 * (a ^ 2 * A ^ 2 / s) + 1 / (2 * t) * (s * (B ^ 2 / a ^ 2)) - A * B =
      (t * a ^ 2 * A - s * B) ^ 2 / (2 * t * s * a ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (t * a ^ 2 * A - s * B) ^ 2 / (2 * t * s * a ^ 2) := by positivity
  linarith

theorem point_le (A B C D a c ρ s t : ℝ) (ha : 0 < a) (hc : 0 < c) (hρ : 0 < ρ) (hs : 0 < s) (ht : 0 < t) :
    2 * Real.pi * ρ * (A * B + C * D) ≤
      t / 2 * (2 * Real.pi * ρ * (a ^ 2 * A ^ 2 + c ^ 2 * C ^ 2) / s) +
        1 / (2 * t) * (2 * Real.pi * ρ * s * (B ^ 2 / a ^ 2 + D ^ 2 / c ^ 2)) := by
  have h1 := mean_le A B a s t ha hs ht
  have h2 := mean_le C D c s t hc hs ht
  have hp : 0 < 2 * Real.pi * ρ := by positivity
  have e : t / 2 * (2 * Real.pi * ρ * (a ^ 2 * A ^ 2 + c ^ 2 * C ^ 2) / s) +
        1 / (2 * t) * (2 * Real.pi * ρ * s * (B ^ 2 / a ^ 2 + D ^ 2 / c ^ 2)) =
      2 * Real.pi * ρ * ((t / 2 * (a ^ 2 * A ^ 2 / s) + 1 / (2 * t) * (s * (B ^ 2 / a ^ 2))) +
        (t / 2 * (c ^ 2 * C ^ 2 / s) + 1 / (2 * t) * (s * (D ^ 2 / c ^ 2)))) := by
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hp.le

theorem le_sqrt_mul {x g w : ℝ} (hg : 0 ≤ g) (hw : 0 ≤ w)
    (h : ∀ t : ℝ, 0 < t → x ≤ t / 2 * g + 1 / (2 * t) * w) : x ≤ Real.sqrt w * Real.sqrt g := by
  rcases hw.lt_or_eq with hw' | hw'
  · rcases hg.lt_or_eq with hg' | hg'
    · have hsw := Real.sqrt_pos.mpr hw'
      have hsg := Real.sqrt_pos.mpr hg'
      have := h (Real.sqrt w / Real.sqrt g) (div_pos hsw hsg)
      have ew : w = Real.sqrt w ^ 2 := (Real.sq_sqrt hw).symm
      have eg : g = Real.sqrt g ^ 2 := (Real.sq_sqrt hg).symm
      have e : Real.sqrt w / Real.sqrt g / 2 * g + 1 / (2 * (Real.sqrt w / Real.sqrt g)) * w =
          Real.sqrt w * Real.sqrt g := by
        rw [ew, eg, Real.sqrt_sq hsw.le, Real.sqrt_sq hsg.le]
        field_simp
        ring
      linarith
    · subst hg'
      simp only [Real.sqrt_zero, mul_zero]
      by_contra hx
      push Not at hx
      have := h ((w + 1) / x) (div_pos (by linarith) hx)
      have e : (w + 1) / x / 2 * 0 + 1 / (2 * ((w + 1) / x)) * w = x * (w / (2 * (w + 1))) := by
        field_simp
        ring
      have hlt : w / (2 * (w + 1)) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      nlinarith
  · subst hw'
    simp only [Real.sqrt_zero, zero_mul]
    by_contra hx
    push Not at hx
    have := h (x / (g + 1)) (div_pos hx (by linarith))
    have e : x / (g + 1) / 2 * g + 1 / (2 * (x / (g + 1))) * 0 = x * (g / (2 * (g + 1))) := by
      field_simp
      ring
    have hlt : g / (2 * (g + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith

theorem horizontal_meas {F : Space → Space} (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (horizontalPart F) volume := by
  have h0 : AEStronglyMeasurable (fun y => F y 0) volume :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hF
  have h1 : AEStronglyMeasurable (fun y => F y 1) volume :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hF
  unfold horizontalPart
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable h0).add
    (aestronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable h1))

theorem vertical_meas {F : Space → Space} (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (verticalPart F) volume := by
  have h2 : AEStronglyMeasurable (fun y => F y 2) volume :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hF
  unfold verticalPart
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable h2

end WeightedInverseSquareInternal

open WeightedInverseSquareInternal in
theorem weightedInverseSquare_of (hH : ModeInverseSquareStatement) (hP : ModePairingStatement) :
    WeightedInverseSquareStatement := by
  have hM := modeMeasurable
  intro m v G H hv F hF hL hW
  have hS : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hE := hH m v G H hv
  have hPair := hP m v G H hv F hF hL
  set g := ∫ y, entrySq (G y)
  have hg : 0 ≤ g := integral_nonneg fun y => by unfold entrySq; positivity
  set w := (harmonicWeightSq F).toReal
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hWe : harmonicWeightSq F = ENNReal.ofReal w := (ENNReal.ofReal_toReal hW).symm
  apply le_sqrt_mul hg hw0
  intro t ht
  have hmh : ∀ k : ℤ, AEStronglyMeasurable (fun q : ℝ × ℝ => angularMode (horizontalPart v) k q.1 q.2) (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
    fun k => hM _ (horizontal_meas hv.measurable_velocity) k
  have hmv : ∀ k : ℤ, AEStronglyMeasurable (fun q : ℝ × ℝ => angularMode (verticalPart v) k q.1 q.2) (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
    fun k => hM _ (vertical_meas hv.measurable_velocity) k
  have key : ENNReal.ofReal |∫ y, inner ℝ (v y) (F y)| ≤
      ENNReal.ofReal (t / 2) * modeEnergy v + ENNReal.ofReal (1 / (2 * t)) * harmonicWeightSq F := by
    refine hPair.trans ?_
    unfold modePairing modeEnergy harmonicWeightSq
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun k => ?_
    have hmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (t / 2) * ENNReal.ofReal (2 * Real.pi * q.1 *
        ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart v) k q.1 q.2‖ ^ 2
          + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart v) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))) (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) := by
      refine AEMeasurable.const_mul (AEMeasurable.ennreal_ofReal ?_) _
      have hq1 : AEMeasurable (fun q : ℝ × ℝ => q.1) (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
        measurable_fst.aemeasurable
      have hq2 : AEMeasurable (fun q : ℝ × ℝ => q.2) (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
        measurable_snd.aemeasurable
      exact ((aemeasurable_const.mul hq1).mul
        ((aemeasurable_const.mul ((hmh k).aemeasurable.norm.pow_const 2)).add
          (aemeasurable_const.mul ((hmv k).aemeasurable.norm.pow_const 2)))).div
            ((hq1.pow_const 2).add (hq2.pow_const 2))
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left' hmeas]
    refine lintegral_mono_ae ((ae_restrict_mem hS).mono fun q hq => ?_)
    have hρ : 0 < q.1 := hq.1
    have hs : 0 < q.1 ^ 2 + q.2 ^ 2 := by positivity
    have ha : (0 : ℝ) < ((|k| : ℤ) : ℝ) + 1 / 2 := by
      have : (0 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg k
      linarith
    have hc : (0 : ℝ) < ((|k| : ℤ) : ℝ) + 3 / 2 := by linarith
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := point_le ‖angularMode (horizontalPart v) k q.1 q.2‖ ‖angularMode (horizontalPart F) k q.1 q.2‖
      ‖angularMode (verticalPart v) k q.1 q.2‖ ‖angularMode (verticalPart F) k q.1 q.2‖ _ _ q.1 _ t ha hc hρ hs ht
    refine this.trans (le_of_eq ?_)
    ring
  have key2 : ENNReal.ofReal |∫ y, inner ℝ (v y) (F y)| ≤ ENNReal.ofReal (t / 2 * g + 1 / (2 * t) * w) := by
    refine key.trans ?_
    rw [hWe, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    gcongr
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key2
  exact this

theorem modeInverseSquare_of (hB : GradientModeSumStatement) (hF : FrameInverseSquareStatement) : ModeInverseSquareStatement := by
  intro m v G H hv
  exact (ENNReal.tsum_le_tsum fun k => hF m v G H hv k).trans (hB m v G H hv)

theorem weightedInverseSquare_of_parts (hB : GradientModeSumStatement) (hF : FrameInverseSquareStatement)
    (hP : ModePairingStatement) : WeightedInverseSquareStatement :=
  weightedInverseSquare_of (modeInverseSquare_of hB hF) hP

namespace GradientModeSumInternal

open Breakdown.CellCert.Spectral.Internal.CylIntegral ModeMeasurableInternal WeightedInverseSquareInternal


theorem coeff_eq (h : ℝ → ℂ) (k : ℤ) (hab : -Real.pi < Real.pi) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * h θ =
      fourierCoeffOn hab h k := by
  rw [fourierCoeffOn_eq_integral]
  have e2 : Real.pi - -Real.pi = 2 * Real.pi := by ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.real_smul]
  congr 1
  · rw [e2]; push_cast; ring
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [smul_eq_mul]
    congr 1
    rw [fourier_coe_apply]
    congr 1
    rw [e2]
    push_cast
    field_simp

theorem circle_coef_sq (h : ℝ → ℂ) (hh : AEStronglyMeasurable h (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    ∑' k : ℤ, ENNReal.ofReal (2 * Real.pi * ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * h θ‖ ^ 2) ≤
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, ENNReal.ofReal (‖h θ‖ ^ 2) := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  by_cases hL : MemLp h 2 (volume.restrict (Ioc (-Real.pi) Real.pi))
  · have hs := hasSum_sq_fourierCoeffOn hab hL
    simp_rw [coeff_eq h _ hab]
    have hs2 : HasSum (fun k : ℤ => 2 * Real.pi * ‖fourierCoeffOn hab h k‖ ^ 2)
        (2 * Real.pi * ((Real.pi - -Real.pi)⁻¹ • ∫ x in (-Real.pi)..Real.pi, ‖h x‖ ^ 2)) := hs.mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs2.summable, hs2.tsum_eq]
    have hint : Integrable (fun x => ‖h x‖ ^ 2) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      (memLp_two_iff_integrable_sq_norm hh).mp hL
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by simp only [Pi.zero_apply]; positivity),
      intervalIntegral.integral_of_le hab.le, smul_eq_mul]
    apply le_of_eq
    congr 1
    have : Real.pi - -Real.pi = 2 * Real.pi := by ring
    rw [this]
    field_simp
  · have htop : ∫⁻ θ in Ioc (-Real.pi) Real.pi, ENNReal.ofReal (‖h θ‖ ^ 2) = ⊤ := by
      by_contra hne
      apply hL
      rw [memLp_two_iff_integrable_sq_norm hh]
      exact (lintegral_ofReal_ne_top_iff_integrable (f := fun x => ‖h x‖ ^ 2) (hh.norm.pow 2)
        (ae_of_all _ fun x => sq_nonneg ‖h x‖)).mp hne
    rw [htop]
    exact le_top


theorem cyl_le (f : Space → ENNReal) (hf : AEMeasurable f volume) :
    ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal q.1 *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (ringPoint q.1 θ q.2) ≤ ∫⁻ y, f y := by
  have hT : MeasurableSet cylMap.target := cylMap.open_target.measurableSet
  have e1 : ∫⁻ y, f y = ∫⁻ x in cylMap.target, ENNReal.ofReal x.1.1 * f (toSpace (cylMap.symm x)) := by
    rw [← toSpace_mp.lintegral_comp_emb toSpace.measurableEmbedding f, ← setLIntegral_univ,
      ← setLIntegral_congr image_ae,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT (fun x _ => (hasDeriv x).hasFDerivWithinAt)
        cylMap.symm.injOn]
    refine setLIntegral_congr_fun hT fun x hx => ?_
    rw [abs_det_eq hx]
  have e2 : ∫⁻ x in cylMap.target, ENNReal.ofReal x.1.1 * f (toSpace (cylMap.symm x)) =
      ∫⁻ p in (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1.1 * f (ringMap p) := by
    rw [← swapEquiv_mp.setLIntegral_comp_preimage_emb swapEquiv.measurableEmbedding, swapEquiv_preimage]
    refine setLIntegral_congr_fun ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)
      fun p _ => ?_
    rw [ringMap_eq]
    obtain ⟨⟨r, z⟩, θ⟩ := p
    rfl
  have e3 : (volume : Measure ((ℝ × ℝ) × ℝ)).restrict ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-Real.pi) Real.pi) =
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [e1, e2, e3]
  have hm : AEMeasurable (fun p : (ℝ × ℝ) × ℝ => ENNReal.ofReal p.1.1 * f (ringMap p))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) :=
    (measurable_fst.fst.ennreal_ofReal).aemeasurable.mul (hf.comp_quasiMeasurePreserving ringMap_qmp)
  rw [lintegral_prod _ hm]
  refine le_of_eq (lintegral_congr fun q => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

theorem parts_sq (w : Space) : ‖(w 0 : ℂ) + Complex.I * (w 1 : ℂ)‖ ^ 2 + ‖(w 2 : ℂ)‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three, Complex.sq_norm,
    Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Real.norm_eq_abs, sq_abs]
  ring

theorem single_eq (i : Fin 3) (a : ℝ) : (EuclideanSpace.single i a : Space) = a • unitVector i := by
  unfold unitVector
  ext j
  by_cases hj : j = i <;> simp [hj]

theorem frame_sum (M : Space →L[ℝ] Space) (y : Space) (hy : ringRadius y ≠ 0) :
    ∑ c : Fin 3, (‖horizontalPart (fun y => M (ringFrame c y)) y‖ ^ 2 +
      ‖verticalPart (fun y => M (ringFrame c y)) y‖ ^ 2) = entrySq M := by
  simp only [horizontalPart, verticalPart, parts_sq]
  unfold entrySq
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [ringFrame, single_eq, map_add, map_smul]
  set a := y 0 / ringRadius y
  set b := y 1 / ringRadius y
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hR : ringRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
    simp only [a, b, div_pow]
    rw [← add_div, ← hR, div_self (pow_ne_zero 2 hy)]
  have hu := norm_add_sq_real (a • M (unitVector 0)) (b • M (unitVector 1))
  have hv := norm_add_sq_real ((-b) • M (unitVector 0)) (a • M (unitVector 1))
  have h1 : (1 : ℝ) • M (unitVector 2) = M (unitVector 2) := one_smul _ _
  rw [h1, hu, hv]
  simp only [norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
  linear_combination (‖M (unitVector 0)‖ ^ 2 + ‖M (unitVector 1)‖ ^ 2) * hab

theorem ringRadius_ringPoint (ρ θ z : ℝ) (hρ : 0 ≤ ρ) : ringRadius (ringPoint ρ θ z) = ρ := by
  have e0 : ringPoint ρ θ z 0 = ρ * Real.cos θ := by simp [ringPoint]
  have e1 : ringPoint ρ θ z 1 = ρ * Real.sin θ := by simp [ringPoint]
  rw [ringRadius, e0, e1, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hρ]

theorem ringFrame_meas (c : Fin 3) : Measurable (ringFrame c) := by
  have hc : ∀ i : Fin 3, Continuous fun y : Space => y i := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous
  have hRad : Measurable ringRadius := by
    unfold ringRadius
    exact (((hc 0).pow 2).add ((hc 1).pow 2)).sqrt.measurable
  fin_cases c
  · show Measurable fun y : Space =>
      (EuclideanSpace.single 0 (y 0 / ringRadius y) : Space) + EuclideanSpace.single 1 (y 1 / ringRadius y)
    have hf : Measurable fun y : Space => (EuclideanSpace.single 0 (y 0 / ringRadius y) : Space) :=
      (single_cont 0).measurable.comp ((hc 0).measurable.div hRad)
    have hg : Measurable fun y : Space => (EuclideanSpace.single 1 (y 1 / ringRadius y) : Space) :=
      (single_cont 1).measurable.comp ((hc 1).measurable.div hRad)
    exact hf.add hg
  · show Measurable fun y : Space =>
      (EuclideanSpace.single 0 (-(y 1 / ringRadius y)) : Space) + EuclideanSpace.single 1 (y 0 / ringRadius y)
    have hf : Measurable fun y : Space => (EuclideanSpace.single 0 (-(y 1 / ringRadius y)) : Space) :=
      (single_cont 0).measurable.comp ((hc 1).measurable.div hRad).neg
    have hg : Measurable fun y : Space => (EuclideanSpace.single 1 (y 0 / ringRadius y) : Space) :=
      (single_cont 1).measurable.comp ((hc 0).measurable.div hRad)
    exact hf.add hg
  · exact measurable_const

end GradientModeSumInternal

open Breakdown.CellCert.Spectral.Internal.CylIntegral ModeMeasurableInternal WeightedInverseSquareInternal
  GradientModeSumInternal in
theorem gradientModeSum : GradientModeSumStatement := by
  intro m v G H hv
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hGc : ∀ c, AEStronglyMeasurable (fun y => G y (ringFrame c y)) volume := fun c =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hv.measurable_gradient.prodMk (ringFrame_meas c).aestronglyMeasurable)
  have hA : ∀ c, AEStronglyMeasurable (horizontalPart fun y => G y (ringFrame c y)) volume :=
    fun c => horizontal_meas (hGc c)
  have hB : ∀ c, AEStronglyMeasurable (verticalPart fun y => G y (ringFrame c y)) volume :=
    fun c => vertical_meas (hGc c)
  have hslA : ∀ c, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => horizontalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
    ((hA c).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hslB : ∀ c, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => verticalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
    ((hB c).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hmk : ∀ k : ℤ, AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq G k q.1 q.2))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
    intro k
    refine AEMeasurable.ennreal_ofReal ?_
    unfold frameModeSq
    refine (aemeasurable_const.mul measurable_fst.aemeasurable).mul ?_
    have hc : ∀ c : Fin 3, AEMeasurable (fun q : ℝ × ℝ =>
        ‖angularMode (horizontalPart fun y => G y (ringFrame c y)) k q.1 q.2‖ ^ 2 +
          ‖angularMode (verticalPart fun y => G y (ringFrame c y)) k q.1 q.2‖ ^ 2)
        (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := fun c =>
      ((modeMeasurable _ (hA c) k).aemeasurable.norm.pow_const 2).add
        ((modeMeasurable _ (hB c) k).aemeasurable.norm.pow_const 2)
    simp only [Fin.sum_univ_three]
    exact ((hc 0).add (hc 1)).add (hc 2)
  have hE : AEMeasurable (fun y => ENNReal.ofReal (entrySq (G y))) volume :=
    hv.gradient_two.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [← lintegral_tsum hmk]
  calc ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∑' k : ℤ, ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq G k q.1 q.2)
      ≤ ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal q.1 *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (entrySq (G (ringPoint q.1 θ q.2))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS, ae_all_iff.mpr hslA, ae_all_iff.mpr hslB] with q hq h1 h2
        have hρ : 0 < q.1 := hq.1
        have e : ∀ k : ℤ, ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq G k q.1 q.2) =
            ENNReal.ofReal q.1 * ∑ c : Fin 3,
              (ENNReal.ofReal (2 * Real.pi * ‖angularMode (horizontalPart fun y => G y (ringFrame c y)) k q.1 q.2‖ ^ 2)
                + ENNReal.ofReal (2 * Real.pi * ‖angularMode (verticalPart fun y => G y (ringFrame c y)) k q.1 q.2‖ ^ 2)) := by
          intro k
          rw [Finset.sum_congr rfl fun c _ => (ENNReal.ofReal_add (by positivity) (by positivity)).symm,
            ← ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity), ← ENNReal.ofReal_mul hρ.le]
          congr 1
          unfold frameModeSq
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
        simp_rw [e]
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun c _ => ENNReal.summable)]
        gcongr
        have hR : ∀ θ, ringRadius (ringPoint q.1 θ q.2) ≠ 0 := fun θ => by
          rw [ringRadius_ringPoint _ _ _ hρ.le]; exact hρ.ne'
        have hAm : ∀ c, AEMeasurable (fun θ => ENNReal.ofReal
            (‖horizontalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
            (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
          ((h1 c).aemeasurable.norm.pow_const 2).ennreal_ofReal
        have hBm : ∀ c, AEMeasurable (fun θ => ENNReal.ofReal
            (‖verticalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
            (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
          ((h2 c).aemeasurable.norm.pow_const 2).ennreal_ofReal
        have hb1 : ∀ c, _ := fun c => circle_coef_sq
          (fun θ => horizontalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)) (by rw [hν]; exact h1 c)
        have hb2 : ∀ c, _ := fun c => circle_coef_sq
          (fun θ => verticalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)) (by rw [hν]; exact h2 c)
        simp only [hν] at hb1 hb2
        calc _ = ∑ c : Fin 3,
              (∑' k : ℤ, ENNReal.ofReal (2 * Real.pi *
                ‖angularMode (horizontalPart fun y => G y (ringFrame c y)) k q.1 q.2‖ ^ 2)
              + ∑' k : ℤ, ENNReal.ofReal (2 * Real.pi *
                ‖angularMode (verticalPart fun y => G y (ringFrame c y)) k q.1 q.2‖ ^ 2)) :=
              Finset.sum_congr rfl fun c _ => ENNReal.tsum_add
          _ ≤ ∑ c : Fin 3,
              ((∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal
                (‖horizontalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
              + ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal
                (‖verticalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2)) :=
              Finset.sum_le_sum fun c _ => add_le_add (hb1 c) (hb2 c)
          _ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∑ c : Fin 3,
              (ENNReal.ofReal (‖horizontalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2)
              + ENNReal.ofReal (‖verticalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2)) := by
              have hsum := lintegral_finsetSum' (μ := volume.restrict (Ioo (-Real.pi) Real.pi)) Finset.univ
                (f := fun c θ => ENNReal.ofReal
                  (‖horizontalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2) +
                  ENNReal.ofReal (‖verticalPart (fun y => G y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
                (fun c _ => (hAm c).add (hBm c))
              rw [hsum]
              exact Finset.sum_congr rfl fun c _ => (lintegral_add_left' (hAm c) _).symm
          _ = _ := by
              refine lintegral_congr fun θ => ?_
              have hf := frame_sum (G (ringPoint q.1 θ q.2)) (ringPoint q.1 θ q.2) (hR θ)
              rw [← hf, ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)]
              exact Finset.sum_congr rfl fun c _ => (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (entrySq (G y)) := cyl_le _ hE
    _ = ENNReal.ofReal (∫ y, entrySq (G y)) :=
        (ofReal_integral_eq_lintegral_ofReal hv.gradient_two
          (ae_of_all _ fun y => by simp only [Pi.zero_apply]; unfold entrySq; positivity)).symm

theorem weightedInverseSquare_of_frame (hF : FrameInverseSquareStatement) (hP : ModePairingStatement) :
    WeightedInverseSquareStatement :=
  weightedInverseSquare_of_parts gradientModeSum hF hP

namespace ModePairingInternal

open Breakdown.CellCert.Spectral.Internal.CylIntegral ModeMeasurableInternal WeightedInverseSquareInternal
  GradientModeSumInternal


def coef (h : ℝ → ℂ) (k : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * h θ

theorem coef_eq (h : ℝ → ℂ) (k : ℤ) (hab : -Real.pi < Real.pi) : coef h k = fourierCoeffOn hab h k := by
  unfold coef
  rw [fourierCoeffOn_eq_integral]
  have e2 : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [Complex.real_smul]
  congr 1
  · rw [e2]; push_cast; ring
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [smul_eq_mul]
    congr 1
    rw [fourier_coe_apply]
    congr 1
    rw [e2]
    push_cast
    field_simp

theorem int_of (h : ℝ → ℂ) (hh : MemLp h 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (k : ℤ) :
    IntervalIntegrable (fun θ => Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * h θ) volume (-Real.pi) Real.pi := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi : IntegrableOn h (Ioc (-Real.pi) Real.pi) := hh.integrable one_le_two
  have h1 : IntervalIntegrable h volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr hi
  exact h1.continuousOn_mul (by fun_prop : Continuous fun θ : ℝ =>
    Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))).continuousOn

theorem coef_add (a b : ℝ → ℂ) (ha : MemLp a 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hb : MemLp b 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (k : ℤ) :
    coef (fun θ => a θ + b θ) k = coef a k + coef b k := by
  unfold coef
  rw [← mul_add, ← intervalIntegral.integral_add (int_of a ha k) (int_of b hb k)]
  simp only [mul_add]

theorem coef_sub (a b : ℝ → ℂ) (ha : MemLp a 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hb : MemLp b 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (k : ℤ) :
    coef (fun θ => a θ - b θ) k = coef a k - coef b k := by
  unfold coef
  rw [← mul_sub, ← intervalIntegral.integral_sub (int_of a ha k) (int_of b hb k)]
  simp only [mul_sub]

theorem polar (u w : ℂ) : (‖u + w‖ ^ 2 - ‖u - w‖ ^ 2) / 4 = (starRingEnd ℂ u * w).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem circle_pair (a b : ℝ → ℂ) (ha : MemLp a 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hb : MemLp b 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    ENNReal.ofReal |∫ θ in (-Real.pi)..Real.pi, (starRingEnd ℂ (a θ) * b θ).re| ≤
      ∑' k : ℤ, ENNReal.ofReal (2 * Real.pi * (‖coef a k‖ * ‖coef b k‖)) := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hs := hasSum_sq_fourierCoeffOn hab (ha.add hb)
  have hd := hasSum_sq_fourierCoeffOn hab (ha.sub hb)
  have hsa := hasSum_sq_fourierCoeffOn hab ha
  have hsb := hasSum_sq_fourierCoeffOn hab hb
  simp only [← coef_eq _ _ hab] at hs hd hsa hsb
  have e1 : ∀ k, coef (a + b) k = coef a k + coef b k := coef_add a b ha hb
  have e2 : ∀ k, coef (a - b) k = coef a k - coef b k := coef_sub a b ha hb
  simp only [e1, e2] at hs hd
  have hre := (hs.sub hd).div_const 4
  simp only [polar] at hre
  have hL2s : Integrable (fun x => ‖(a + b) x‖ ^ 2) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm (ha.add hb).1).mp (ha.add hb)
  have hL2d : Integrable (fun x => ‖(a - b) x‖ ^ 2) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm (ha.sub hb).1).mp (ha.sub hb)
  have hval : (Real.pi - -Real.pi)⁻¹ • (∫ x in (-Real.pi)..Real.pi, ‖(a + b) x‖ ^ 2) / 4 -
      (Real.pi - -Real.pi)⁻¹ • (∫ x in (-Real.pi)..Real.pi, ‖(a - b) x‖ ^ 2) / 4 =
      (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, (starRingEnd ℂ (a θ) * b θ).re := by
    rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_of_le hab.le, smul_eq_mul, smul_eq_mul]
    have : ∫ θ in Ioc (-Real.pi) Real.pi, (starRingEnd ℂ (a θ) * b θ).re =
        (∫ x in Ioc (-Real.pi) Real.pi, ‖(a + b) x‖ ^ 2) / 4 - (∫ x in Ioc (-Real.pi) Real.pi, ‖(a - b) x‖ ^ 2) / 4 := by
      rw [← integral_div, ← integral_div, ← integral_sub (hL2s.div_const 4) (hL2d.div_const 4)]
      refine integral_congr_ae (ae_of_all _ fun θ => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [← sub_div, polar]
    rw [this]
    have : Real.pi - -Real.pi = 2 * Real.pi := by ring
    rw [this]
    ring
  have hsum : HasSum (fun k => (starRingEnd ℂ (coef a k) * coef b k).re)
      ((2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, (starRingEnd ℂ (a θ) * b θ).re) := by
    rw [← hval, ← sub_div]
    exact hre
  have hbd : ∀ k, |(starRingEnd ℂ (coef a k) * coef b k).re| ≤ ‖coef a k‖ * ‖coef b k‖ := fun k =>
    (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have hprod : Summable (fun k => ‖coef a k‖ * ‖coef b k‖) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hsa.summable.add hsb.summable).div_const 2)
    have := two_mul_le_add_sq ‖coef a k‖ ‖coef b k‖
    linarith
  have habs : Summable (fun k => ‖(starRingEnd ℂ (coef a k) * coef b k).re‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact hbd k) hprod
  have hmain : |∫ θ in (-Real.pi)..Real.pi, (starRingEnd ℂ (a θ) * b θ).re| ≤
      2 * Real.pi * ∑' k : ℤ, ‖coef a k‖ * ‖coef b k‖ := by
    have ht := hsum.tsum_eq
    have e : ∫ θ in (-Real.pi)..Real.pi, (starRingEnd ℂ (a θ) * b θ).re =
        2 * Real.pi * ∑' k, (starRingEnd ℂ (coef a k) * coef b k).re := by
      rw [ht]; field_simp
    rw [e, abs_mul, abs_of_pos hpi2]
    refine mul_le_mul_of_nonneg_left ?_ hpi2.le
    calc |∑' k, (starRingEnd ℂ (coef a k) * coef b k).re|
        = ‖∑' k, (starRingEnd ℂ (coef a k) * coef b k).re‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' k, ‖(starRingEnd ℂ (coef a k) * coef b k).re‖ := norm_tsum_le_tsum_norm habs
      _ ≤ ∑' k, ‖coef a k‖ * ‖coef b k‖ :=
          habs.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hbd k) hprod
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (hprod.mul_left _), tsum_mul_left]
  exact ENNReal.ofReal_le_ofReal hmain


theorem slice_fin (g : Space → ℝ) (hg : Integrable g) :
    ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (g (ringPoint q.1 θ q.2)) < ⊤ := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hgm : AEMeasurable (fun y => ENNReal.ofReal (g y)) volume := hg.1.aemeasurable.ennreal_ofReal
  have hfin := (cyl_le _ hgm).trans_lt hg.lintegral_lt_top
  have hm : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 *
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (g (ringPoint q.1 θ q.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    measurable_fst.ennreal_ofReal.aemeasurable.mul
      (AEMeasurable.lintegral_prod_right' (hgm.comp_quasiMeasurePreserving ringMap_qmp))
  filter_upwards [ae_lt_top' hm hfin.ne, ae_restrict_mem hS] with q hq hqS
  have hρ : ENNReal.ofReal q.1 ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hqS.1
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.mul_top hρ] at hq
  exact lt_irrefl _ hq

theorem ring_norm_sq (ρ θ z : ℝ) : ‖ringPoint ρ θ z‖ ^ 2 = ρ ^ 2 + z ^ 2 := by
  have e0 : ringPoint ρ θ z 0 = ρ * Real.cos θ := by simp [ringPoint]
  have e1 : ringPoint ρ θ z 1 = ρ * Real.sin θ := by simp [ringPoint]
  have e2 : ringPoint ρ θ z 2 = z := by simp [ringPoint]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three, e0, e1, e2]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem hor_le (w : Space) : ‖(w 0 : ℂ) + Complex.I * (w 1 : ℂ)‖ ≤ ‖w‖ := by
  nlinarith [parts_sq w, norm_nonneg ((w 0 : ℂ) + Complex.I * (w 1 : ℂ)), norm_nonneg w,
    sq_nonneg ‖(w 2 : ℂ)‖]

theorem ver_le (w : Space) : ‖(w 2 : ℂ)‖ ≤ ‖w‖ := by
  nlinarith [parts_sq w, norm_nonneg ((w 0 : ℂ) + Complex.I * (w 1 : ℂ)), norm_nonneg w,
    norm_nonneg (w 2 : ℂ)]

theorem inner_parts (x y : Space) : inner ℝ x y =
    (starRingEnd ℂ ((x 0 : ℂ) + Complex.I * (x 1 : ℂ)) * ((y 0 : ℂ) + Complex.I * (y 1 : ℂ))).re +
      (starRingEnd ℂ (x 2 : ℂ) * (y 2 : ℂ)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Fin.sum_univ_three, dotProduct, Complex.mul_re]
  ring

theorem ofReal_abs_add (x y : ℝ) : ENNReal.ofReal |x + y| ≤ ENNReal.ofReal |x| + ENNReal.ofReal |y| := by
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_add_le x y)

theorem coef_ring (u : Space → ℂ) (q : ℝ × ℝ) (k : ℤ) :
    coef (fun θ => u (ringPoint q.1 θ q.2)) k = angularMode u k q.1 q.2 := rfl

theorem pair_int (a b : ℝ → ℂ) (ha : MemLp a 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hb : MemLp b 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    IntervalIntegrable (fun θ => (starRingEnd ℂ (a θ) * b θ).re) volume (-Real.pi) Real.pi := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
  have ha2 := (memLp_two_iff_integrable_sq_norm ha.1).mp ha
  have hb2 := (memLp_two_iff_integrable_sq_norm hb.1).mp hb
  refine Integrable.mono' ((ha2.add hb2).div_const 2) ?_ (ae_of_all _ fun θ => ?_)
  · exact Complex.continuous_re.comp_aestronglyMeasurable
      ((Complex.continuous_conj.comp_aestronglyMeasurable ha.1).mul hb.1)
  · have h1 : |(starRingEnd ℂ (a θ) * b θ).re| ≤ ‖a θ‖ * ‖b θ‖ :=
      (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
    have h2 := two_mul_le_add_sq ‖a θ‖ ‖b θ‖
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    linarith

end ModePairingInternal

open Breakdown.CellCert.Spectral.Internal.CylIntegral ModeMeasurableInternal WeightedInverseSquareInternal
  GradientModeSumInternal ModePairingInternal in
theorem modePairingBound : ModePairingStatement := by
  intro m v G H hv F hF hL
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  by_cases hi : Integrable (fun y => inner ℝ (v y) (F y))
  swap
  · rw [integral_undef hi, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hsl : ∀ u : Space → ℂ, AEStronglyMeasurable u volume →
      ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
        AEStronglyMeasurable (fun θ => u (ringPoint q.1 θ q.2)) (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    intro u hu
    rw [hν]
    exact (hu.comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hF2 : Integrable (fun y => ‖‖y‖ • F y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hL.1).mp hL
  have hv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    have := hv.velocity_six.integrable_norm_rpow (by norm_num) (by norm_num)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only
    norm_num
  have hLF : ∀ u : Space → ℂ, AEStronglyMeasurable u volume → (∀ y, ‖u y‖ ≤ ‖F y‖) →
      ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
        MemLp (fun θ => u (ringPoint q.1 θ q.2)) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    intro u hu hb
    filter_upwards [slice_fin _ hF2, hsl u hu, ae_restrict_mem hS] with q hq hqm hqS
    have hρ : 0 < q.1 := hqS.1
    have hs : 0 < q.1 ^ 2 + q.2 ^ 2 := by positivity
    rw [memLp_two_iff_integrable_sq_norm hqm]
    refine (lintegral_ofReal_ne_top_iff_integrable (f := fun θ => ‖u (ringPoint q.1 θ q.2)‖ ^ 2)
      (hqm.norm.pow 2) (ae_of_all _ fun θ => sq_nonneg _)).mp ?_
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq.ne)
      (?_ : _ ≤ ENNReal.ofReal (1 / (q.1 ^ 2 + q.2 ^ 2)) * _)
    rw [hν, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_smul, norm_norm, mul_pow, ring_norm_sq]
    have h1 : ‖u (ringPoint q.1 θ q.2)‖ ^ 2 ≤ ‖F (ringPoint q.1 θ q.2)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
    have e : 1 / (q.1 ^ 2 + q.2 ^ 2) * ((q.1 ^ 2 + q.2 ^ 2) * ‖F (ringPoint q.1 θ q.2)‖ ^ 2) =
        ‖F (ringPoint q.1 θ q.2)‖ ^ 2 := by field_simp
    rw [e]
    exact h1
  have hLv : ∀ u : Space → ℂ, AEStronglyMeasurable u volume → (∀ y, ‖u y‖ ≤ ‖v y‖) →
      ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
        MemLp (fun θ => u (ringPoint q.1 θ q.2)) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    intro u hu hb
    filter_upwards [slice_fin _ hv6, hsl u hu] with q hq hqm
    rw [memLp_two_iff_integrable_sq_norm hqm]
    refine (lintegral_ofReal_ne_top_iff_integrable (f := fun θ => ‖u (ringPoint q.1 θ q.2)‖ ^ 2)
      (hqm.norm.pow 2) (ae_of_all _ fun θ => sq_nonneg _)).mp ?_
    have hvol : ∫⁻ θ in Ioo (-Real.pi) Real.pi, (1 : ENNReal) ≠ ⊤ := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
      simp
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hvol, hq.ne⟩) ?_
    rw [hν, ← lintegral_add_left measurable_const]
    refine lintegral_mono fun θ => ?_
    have h1 : ‖u (ringPoint q.1 θ q.2)‖ ^ 2 ≤ ‖v (ringPoint q.1 θ q.2)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
    set t := ‖v (ringPoint q.1 θ q.2)‖ ^ 2
    have ht : 0 ≤ t := sq_nonneg _
    have h6 : ‖v (ringPoint q.1 θ q.2)‖ ^ 6 = t ^ 3 := by rw [← pow_mul]
    rw [h6, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg ht (sq_nonneg (t - 1)), sq_nonneg t, sq_nonneg (t - 1)]
  have hvA := horizontal_meas hv.measurable_velocity
  have hvC := vertical_meas hv.measurable_velocity
  have hFA := horizontal_meas hF
  have hFC := vertical_meas hF
  have hcr : ∀ r θ z : ℝ, Spectral.cylPoint r θ z = ringPoint r θ z := fun _ _ _ => rfl
  rw [Breakdown.CellCert.Spectral.cylIntegral _ hi]
  simp only [hcr]
  have hmk : ∀ k : ℤ, AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (2 * Real.pi * q.1 *
      (‖angularMode (horizontalPart v) k q.1 q.2‖ * ‖angularMode (horizontalPart F) k q.1 q.2‖
        + ‖angularMode (verticalPart v) k q.1 q.2‖ * ‖angularMode (verticalPart F) k q.1 q.2‖)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := fun k =>
    ((aemeasurable_const.mul measurable_fst.aemeasurable).mul
      (((modeMeasurable _ hvA k).aemeasurable.norm.mul (modeMeasurable _ hFA k).aemeasurable.norm).add
        ((modeMeasurable _ hvC k).aemeasurable.norm.mul (modeMeasurable _ hFC k).aemeasurable.norm))).ennreal_ofReal
  unfold modePairing
  rw [← lintegral_tsum hmk]
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem hS, hLv _ hvA (fun y => hor_le (v y)), hLv _ hvC (fun y => ver_le (v y)),
    hLF _ hFA (fun y => hor_le (F y)), hLF _ hFC (fun y => ver_le (F y))] with q hqS h1 h2 h3 h4
  have hρ : 0 < q.1 := hqS.1
  have hI : ∫ θ in (-Real.pi)..Real.pi, inner ℝ (v (ringPoint q.1 θ q.2)) (F (ringPoint q.1 θ q.2)) =
      (∫ θ in (-Real.pi)..Real.pi,
        (starRingEnd ℂ (horizontalPart v (ringPoint q.1 θ q.2)) * horizontalPart F (ringPoint q.1 θ q.2)).re) +
      ∫ θ in (-Real.pi)..Real.pi,
        (starRingEnd ℂ (verticalPart v (ringPoint q.1 θ q.2)) * verticalPart F (ringPoint q.1 θ q.2)).re := by
    rw [← intervalIntegral.integral_add (pair_int _ _ h1 h3) (pair_int _ _ h2 h4)]
    exact intervalIntegral.integral_congr fun θ _ => inner_parts _ _
  have c1 := circle_pair _ _ h1 h3
  have c2 := circle_pair _ _ h2 h4
  simp only [coef_ring] at c1 c2
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos hρ, hI, ENNReal.ofReal_mul hρ.le]
  refine (mul_le_mul' le_rfl ((ofReal_abs_add _ _).trans (add_le_add c1 c2))).trans (le_of_eq ?_)
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hρ.le]
  congr 1
  ring

theorem weightedInverseSquare_of_frameBound (hF : FrameInverseSquareStatement) : WeightedInverseSquareStatement :=
  weightedInverseSquare_of_frame hF modePairingBound

end Reduction

end CellCert

end Breakdown
