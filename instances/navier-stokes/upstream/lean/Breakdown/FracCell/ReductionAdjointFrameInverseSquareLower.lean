import Breakdown.FracCell.ReductionAdjointFrameInverseSquareLimit

open scoped ContDiff
open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown

namespace FracInternal

namespace FrameInverseSquareParts

namespace WeightedLowerInternal

open SteadyCert CellCert.Reduction GradientLimitInternal
open Breakdown.CellCert.Spectral.Internal.CylIntegral CellCert.Reduction.ModeMeasurableInternal
  CellCert.Reduction.WeightedInverseSquareInternal CellCert.Reduction.GradientModeSumInternal
  CellCert.Reduction.ModePairingInternal

def wF (v : Space → Space) (k : ℤ) (q : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (2 * Real.pi * q.1 *
    ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart v) k q.1 q.2‖ ^ 2
      + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart v) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))

def bF (f : Space → Space) (k : ℤ) (q : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (2 * Real.pi * q.1 *
    (‖angularMode (horizontalPart f) k q.1 q.2‖ ^ 2 + ‖angularMode (verticalPart f) k q.1 q.2‖ ^ 2))

def tset (j : ℕ) : Set (ℝ × ℝ) :=
  {q | 1 / ((j : ℝ) + 1) < q.1} ∩ {q | q.1 ^ 2 + q.2 ^ 2 < ((j : ℝ) + 1) ^ 2}

theorem side_eq (v : Space → Space) (k : ℤ) : modeWeightedSide v k = ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), wF v k q := rfl

theorem tset_meas (j : ℕ) : MeasurableSet (tset j) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt (by fun_prop) measurable_const)

theorem wF_meas (v : Space → Space) (hv : AEStronglyMeasurable v volume) (k : ℤ) :
    AEMeasurable (wF v k) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  unfold wF
  refine AEMeasurable.ennreal_ofReal ?_
  refine AEMeasurable.div ((aemeasurable_const.mul measurable_fst.aemeasurable).mul ?_) (by fun_prop)
  exact (aemeasurable_const.mul ((modeMeasurable _ (horizontal_meas hv) k).aemeasurable.norm.pow_const 2)).add
    (aemeasurable_const.mul ((modeMeasurable _ (vertical_meas hv) k).aemeasurable.norm.pow_const 2))

theorem bF_meas (f : Space → Space) (hf : AEStronglyMeasurable f volume) (k : ℤ) :
    AEMeasurable (bF f k) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  unfold bF
  refine AEMeasurable.ennreal_ofReal ?_
  refine (aemeasurable_const.mul measurable_fst.aemeasurable).mul ?_
  exact ((modeMeasurable _ (horizontal_meas hf) k).aemeasurable.norm.pow_const 2).add
    ((modeMeasurable _ (vertical_meas hf) k).aemeasurable.norm.pow_const 2)

theorem ring_mem {j : ℕ} {q : ℝ × ℝ} (hq : q ∈ tset j) (θ : ℝ) :
    ringPoint q.1 θ q.2 ∈ Metric.ball (0 : Space) ((j : ℝ) + 1) := by
  rw [mem_ball_zero_iff]
  have h := ring_norm_sq q.1 θ q.2
  have h2 : ‖ringPoint q.1 θ q.2‖ ^ 2 < ((j : ℝ) + 1) ^ 2 := h ▸ hq.2
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2

theorem vcircleCoefBound (f : Space → Space) (hf : AEStronglyMeasurable f volume) (k : ℤ) (j : ℕ) :
    ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (bF f k) q ≤
      ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖f y‖ ^ 2) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  set g : Space → ENNReal := (Metric.ball (0 : Space) ((j : ℝ) + 1)).indicator (fun y => ENNReal.ofReal (‖f y‖ ^ 2))
  have hg : AEMeasurable g volume :=
    (hf.norm.pow 2).aemeasurable.ennreal_ofReal.indicator Metric.isOpen_ball.measurableSet
  have hslA : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => horizontalPart f (ringPoint q.1 θ q.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    ((horizontal_meas hf).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hslB : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => verticalPart f (ringPoint q.1 θ q.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    ((vertical_meas hf).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
  refine le_trans ?_ (cyl_le g hg)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hS, hslA, hslB] with q hqS h1 h2
  by_cases hq : q ∈ tset j
  · rw [indicator_of_mem hq]
    have hρ : 0 < q.1 := hqS.1
    have hb1 := circle_coef_sq (fun θ => horizontalPart f (ringPoint q.1 θ q.2)) (by rw [hν]; exact h1)
    have hb2 := circle_coef_sq (fun θ => verticalPart f (ringPoint q.1 θ q.2)) (by rw [hν]; exact h2)
    simp only [hν] at hb1 hb2
    have e1 : bF f k q = ENNReal.ofReal q.1 *
        (ENNReal.ofReal (2 * Real.pi * ‖angularMode (horizontalPart f) k q.1 q.2‖ ^ 2) +
          ENNReal.ofReal (2 * Real.pi * ‖angularMode (verticalPart f) k q.1 q.2‖ ^ 2)) := by
      unfold bF
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hρ.le]
      congr 1
      ring
    rw [e1]
    gcongr
    have hAm : AEMeasurable (fun θ => ENNReal.ofReal (‖horizontalPart f (ringPoint q.1 θ q.2)‖ ^ 2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := (h1.aemeasurable.norm.pow_const 2).ennreal_ofReal
    calc _ ≤ (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖horizontalPart f (ringPoint q.1 θ q.2)‖ ^ 2)) +
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖verticalPart f (ringPoint q.1 θ q.2)‖ ^ 2) :=
          add_le_add ((ENNReal.le_tsum k).trans hb1) ((ENNReal.le_tsum k).trans hb2)
      _ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, (ENNReal.ofReal (‖horizontalPart f (ringPoint q.1 θ q.2)‖ ^ 2) +
          ENNReal.ofReal (‖verticalPart f (ringPoint q.1 θ q.2)‖ ^ 2)) := (lintegral_add_left' hAm _).symm
      _ = _ := by
          refine lintegral_congr fun θ => ?_
          simp only [g, indicator_of_mem (ring_mem hq θ)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          exact parts_sq (f (ringPoint q.1 θ q.2))
  · rw [indicator_of_notMem hq]
    exact bot_le


theorem real_split (P t wh wv W J ε H V Ha Va Hb Vb : ℝ) (hP : 0 ≤ P) (ht0 : 0 ≤ t) (htJ : t ≤ J)
    (hwh0 : 0 ≤ wh) (hwv0 : 0 ≤ wv) (hwh : wh ≤ W) (hwv : wv ≤ W) (hε : 0 < ε)
    (hH : H ≤ (1 + ε) * Ha + (1 + ε⁻¹) * Hb) (hV : V ≤ (1 + ε) * Va + (1 + ε⁻¹) * Vb)
    (hHb : 0 ≤ Hb) (hVb : 0 ≤ Vb) :
    P * (wh * H + wv * V) * t ≤ (1 + ε) * (P * (wh * Ha + wv * Va) * t) + ((1 + ε⁻¹) * (W * J)) * (P * (Hb + Vb)) := by
  have h1 : wh * H + wv * V ≤ (1 + ε) * (wh * Ha + wv * Va) + (1 + ε⁻¹) * (wh * Hb + wv * Vb) := by
    nlinarith [mul_le_mul_of_nonneg_left hH hwh0, mul_le_mul_of_nonneg_left hV hwv0]
  have h2 : wh * Hb + wv * Vb ≤ W * (Hb + Vb) := by
    nlinarith [mul_le_mul_of_nonneg_right hwh hHb, mul_le_mul_of_nonneg_right hwv hVb]
  have hW : 0 ≤ W := hwh0.trans hwh
  have hPt : 0 ≤ P * t := mul_nonneg hP ht0
  have h3 := mul_le_mul_of_nonneg_left h1 hPt
  have h4 : (wh * Hb + wv * Vb) * t ≤ W * (Hb + Vb) * J :=
    mul_le_mul h2 htJ ht0 (mul_nonneg hW (add_nonneg hHb hVb))
  have hc : 0 ≤ (1 + ε⁻¹) * P := mul_nonneg (by positivity) hP
  have h5 := mul_le_mul_of_nonneg_left h4 hc
  nlinarith [h3, h5]

theorem hor_cont {F : Space → Space} (hF : Continuous F) : Continuous (horizontalPart F) := by
  unfold horizontalPart
  exact (Complex.continuous_ofReal.comp ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp hF)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp hF)))

theorem ver_cont {F : Space → Space} (hF : Continuous F) : Continuous (verticalPart F) := by
  unfold verticalPart
  exact Complex.continuous_ofReal.comp ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp hF)

theorem ring_cont (q : ℝ × ℝ) : Continuous (fun θ => ringPoint q.1 θ q.2) :=
  ringMap_cont.comp (Continuous.prodMk continuous_const continuous_id)

theorem cont_memLp (h : ℝ → ℂ) (hc : Continuous h) : MemLp h 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => hC x (Ioc_subset_Icc_self hx)))

theorem hor_sq_le (w : Space) : ‖(w 0 : ℂ) + Complex.I * (w 1 : ℂ)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have := parts_sq w
  nlinarith [sq_nonneg ‖(w 2 : ℂ)‖]

theorem ver_sq_le (w : Space) : ‖(w 2 : ℂ)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have := parts_sq w
  nlinarith [sq_nonneg ‖(w 0 : ℂ) + Complex.I * (w 1 : ℂ)‖]

theorem diff_slices (f : Space → Space) (hf : AEStronglyMeasurable f volume) (j : ℕ)
    (hfin : ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖f y‖ ^ 2) ≠ ⊤) :
    ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), q ∈ tset j →
      MemLp (fun θ => horizontalPart f (ringPoint q.1 θ q.2)) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
      MemLp (fun θ => verticalPart f (ringPoint q.1 θ q.2)) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hB : MeasurableSet (Metric.ball (0 : Space) ((j : ℝ) + 1)) := Metric.isOpen_ball.measurableSet
  have hon : IntegrableOn (fun y => ‖f y‖ ^ 2) (Metric.ball (0 : Space) ((j : ℝ) + 1)) :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.norm.pow 2).restrict (ae_of_all _ fun y => sq_nonneg _)).mp hfin
  have hint : Integrable ((Metric.ball (0 : Space) ((j : ℝ) + 1)).indicator (fun y => ‖f y‖ ^ 2)) :=
    (integrable_indicator_iff hB).mpr hon
  have hslA : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => horizontalPart f (ringPoint q.1 θ q.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    ((horizontal_meas hf).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hslB : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => verticalPart f (ringPoint q.1 θ q.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    ((vertical_meas hf).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  filter_upwards [slice_fin _ hint, hslA, hslB] with q hq h1 h2
  intro hqT
  have e : ∀ θ, (Metric.ball (0 : Space) ((j : ℝ) + 1)).indicator (fun y => ‖f y‖ ^ 2) (ringPoint q.1 θ q.2) =
      ‖f (ringPoint q.1 θ q.2)‖ ^ 2 := fun θ => indicator_of_mem (ring_mem hqT θ) _
  simp only [e] at hq
  rw [hν]
  constructor
  · refine (memLp_two_iff_integrable_sq_norm h1).mpr ?_
    refine (lintegral_ofReal_ne_top_iff_integrable (h1.norm.pow 2) (ae_of_all _ fun θ => sq_nonneg _)).mp ?_
    refine ne_top_of_le_ne_top hq.ne (lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_)
    exact hor_sq_le _
  · refine (memLp_two_iff_integrable_sq_norm h2).mpr ?_
    refine (lintegral_ofReal_ne_top_iff_integrable (h2.norm.pow 2) (ae_of_all _ fun θ => sq_nonneg _)).mp ?_
    refine ne_top_of_le_ne_top hq.ne (lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_)
    exact ver_sq_le _

theorem point_low (v u : Space → Space) (k : ℤ) (j : ℕ) (q : ℝ × ℝ) (hqT : q ∈ tset j)
    (hu1 : MemLp (fun θ => horizontalPart u (ringPoint q.1 θ q.2)) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hu2 : MemLp (fun θ => verticalPart u (ringPoint q.1 θ q.2)) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hd1 : MemLp (fun θ => horizontalPart (fun y => v y - u y) (ringPoint q.1 θ q.2)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hd2 : MemLp (fun θ => verticalPart (fun y => v y - u y) (ringPoint q.1 θ q.2)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (ε : ℝ) (hε : 0 < ε) :
    wF v k q ≤ ENNReal.ofReal (1 + ε) * wF u k q +
      ENNReal.ofReal ((1 + ε⁻¹) * (((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) * ((j : ℝ) + 1) ^ 2)) *
        bF (fun y => v y - u y) k q := by
  have mh : angularMode (horizontalPart v) k q.1 q.2 = angularMode (horizontalPart u) k q.1 q.2 +
      angularMode (horizontalPart (fun y => v y - u y)) k q.1 q.2 := by
    rw [← coef_ring, ← coef_ring, ← coef_ring, ← coef_add _ _ hu1 hd1]
    congr 1
    funext θ
    simp only [horizontalPart, PiLp.sub_apply, Complex.ofReal_sub]
    ring
  have mv : angularMode (verticalPart v) k q.1 q.2 = angularMode (verticalPart u) k q.1 q.2 +
      angularMode (verticalPart (fun y => v y - u y)) k q.1 q.2 := by
    rw [← coef_ring, ← coef_ring, ← coef_ring, ← coef_add _ _ hu2 hd2]
    congr 1
    funext θ
    simp only [verticalPart, PiLp.sub_apply, Complex.ofReal_sub]
    ring
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hρ : 0 < q.1 := lt_trans (by positivity) hqT.1
  have hr2 : 0 < q.1 ^ 2 + q.2 ^ 2 := by positivity
  have hk : (0 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg k
  have htJ : 1 / (q.1 ^ 2 + q.2 ^ 2) ≤ ((j : ℝ) + 1) ^ 2 := by
    rw [div_le_iff₀ hr2]
    have h1 : 1 < ((j : ℝ) + 1) * q.1 := by
      have h0 : 1 / ((j : ℝ) + 1) < q.1 := hqT.1
      rw [div_lt_iff₀ hj] at h0
      linarith
    nlinarith [sq_nonneg q.2, sq_nonneg ((j : ℝ) + 1)]
  unfold wF bF
  rw [mh, mv]
  have hP : 0 ≤ 2 * Real.pi * q.1 := by positivity
  have hA : 0 ≤ 2 * Real.pi * q.1 * ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart u) k q.1 q.2‖ ^ 2
      + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart u) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2) := by
    positivity
  have hB : 0 ≤ 2 * Real.pi * q.1 * (‖angularMode (horizontalPart (fun y => v y - u y)) k q.1 q.2‖ ^ 2 +
      ‖angularMode (verticalPart (fun y => v y - u y)) k q.1 q.2‖ ^ 2) := by positivity
  have hε' : 0 ≤ ε⁻¹ := by positivity
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) hA) (mul_nonneg (by positivity) hB)]
  refine ENNReal.ofReal_le_ofReal ?_
  set a1 := angularMode (horizontalPart u) k q.1 q.2
  set a2 := angularMode (verticalPart u) k q.1 q.2
  set b1 := angularMode (horizontalPart (fun y => v y - u y)) k q.1 q.2
  set b2 := angularMode (verticalPart (fun y => v y - u y)) k q.1 q.2
  have key := real_split (2 * Real.pi * q.1) (1 / (q.1 ^ 2 + q.2 ^ 2)) ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2)
    ((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) ((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) (((j : ℝ) + 1) ^ 2) ε
    (‖a1 + b1‖ ^ 2) (‖a2 + b2‖ ^ 2) (‖a1‖ ^ 2) (‖a2‖ ^ 2) (‖b1‖ ^ 2) (‖b2‖ ^ 2) hP (by positivity) htJ
    (by positivity) (by positivity) (by nlinarith) le_rfl hε (sq_split _ _ ε hε) (sq_split _ _ ε hε)
    (by positivity) (by positivity)
  exact (le_of_eq (by ring)).trans (key.trans (le_of_eq (by ring)))

theorem trunc_bound (v u : Space → Space) (hv : AEStronglyMeasurable v volume) (hu : Continuous u) (k : ℤ) (j : ℕ)
    (hfin : ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖v y - u y‖ ^ 2) ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (wF v k) q ≤ ENNReal.ofReal (1 + ε) * modeWeightedSide u k +
      ENNReal.ofReal ((1 + ε⁻¹) * (((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) * ((j : ℝ) + 1) ^ 2)) *
        ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖v y - u y‖ ^ 2) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hd : AEStronglyMeasurable (fun y => v y - u y) volume := hv.sub hu.aestronglyMeasurable
  have hsl := diff_slices (fun y => v y - u y) hd j hfin
  calc ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (wF v k) q
      ≤ ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (ENNReal.ofReal (1 + ε) * wF u k q +
          ENNReal.ofReal ((1 + ε⁻¹) * (((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) * ((j : ℝ) + 1) ^ 2)) *
            (tset j).indicator (bF (fun y => v y - u y) k) q) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsl] with q h1
        by_cases hq : q ∈ tset j
        · rw [indicator_of_mem hq, indicator_of_mem hq]
          exact point_low v u k j q hq (cont_memLp _ ((hor_cont hu).comp (ring_cont q)))
            (cont_memLp _ ((ver_cont hu).comp (ring_cont q))) (h1 hq).1 (h1 hq).2 ε hε
        · rw [indicator_of_notMem hq]
          exact bot_le
    _ = ENNReal.ofReal (1 + ε) * modeWeightedSide u k +
          ENNReal.ofReal ((1 + ε⁻¹) * (((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) * ((j : ℝ) + 1) ^ 2)) *
            ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (bF (fun y => v y - u y) k) q := by
        rw [lintegral_add_left' ((wF_meas u hu.aestronglyMeasurable k).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, side_eq]
    _ ≤ _ := by
        gcongr
        exact vcircleCoefBound _ hd k j

theorem trunc_le (v : Space → Space) (u : ℕ → Space → Space) (hv : AEStronglyMeasurable v volume)
    (hu : ∀ n, Continuous (u n))
    (hlim : ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖u n y - v y‖ ^ 2)) atTop (𝓝 0))
    (k : ℤ) (j : ℕ) :
    ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (wF v k) q ≤ liminf (fun n => modeWeightedSide (u n) k) atTop := by
  set X := ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (wF v k) q
  have e : ∀ n, ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖v y - u n y‖ ^ 2) =
      ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖u n y - v y‖ ^ 2) := fun n => by
    simp_rw [norm_sub_rev]
  have he := hlim ((j : ℝ) + 1)
  have hfin : ∀ᶠ n in atTop, ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖v y - u n y‖ ^ 2) ≠ ⊤ :=
    ((tendsto_order.1 he).2 1 one_pos).mono fun n hn => by rw [e n]; exact (hn.trans ENNReal.one_lt_top).ne
  refine le_of_forall_lt_imp_le_of_dense fun l hl => ?_
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  have hlt : l ≠ ⊤ := ne_top_of_lt hl
  obtain ⟨i, hi⟩ := ((tendsto_order.1 (coeff_tend l hlt)).2 _ hl).exists
  have hε : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
  filter_upwards [(tendsto_order.1 (tail_tend _ ((1 + (1 / ((i : ℝ) + 1))⁻¹) *
      (((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) * ((j : ℝ) + 1) ^ 2)) _ he)).2 _ hi, hfin] with n h1 h2
  by_contra hn
  rw [not_le] at hn
  have h3 := trunc_bound v (u n) hv (hu n) k j h2 _ hε
  rw [e n] at h3
  have h4 : X ≤ ENNReal.ofReal (1 + 1 / ((i : ℝ) + 1)) * l +
      ENNReal.ofReal ((1 + (1 / ((i : ℝ) + 1))⁻¹) * (((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2) * ((j : ℝ) + 1) ^ 2)) *
        ∫⁻ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ENNReal.ofReal (‖u n y - v y‖ ^ 2) :=
    h3.trans (by gcongr)
  exact lt_irrefl _ (h4.trans_lt h1)

end WeightedLowerInternal

open SteadyCert CellCert.Reduction WeightedLowerInternal in
theorem modeWeightedLower : ModeWeightedLowerStatement := by
  intro v u hv hu hlim k
  rw [side_eq]
  have hmono : ∀ j j' : ℕ, j ≤ j' → tset j ⊆ tset j' := by
    intro j j' h q hq
    have hjj : (j : ℝ) ≤ j' := by exact_mod_cast h
    have h1 : 1 / ((j : ℝ) + 1) < q.1 := hq.1
    have h2 : q.1 ^ 2 + q.2 ^ 2 < ((j : ℝ) + 1) ^ 2 := hq.2
    exact ⟨show 1 / ((j' : ℝ) + 1) < q.1 from
        lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) h1,
      show q.1 ^ 2 + q.2 ^ 2 < ((j' : ℝ) + 1) ^ 2 from
        lt_of_lt_of_le h2 (pow_le_pow_left₀ (by positivity) (by linarith) 2)⟩
  have hT : Tendsto (fun j : ℕ => ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (tset j).indicator (wF v k) q) atTop
      (𝓝 (∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), wF v k q)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun j => (wF_meas v hv k).indicator (tset_meas j)) ?_ ?_
    · exact ae_of_all _ fun q j j' h => indicator_le_indicator_of_subset (hmono j j' h) (fun _ => bot_le) q
    · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with q hqS
      have hρ : 0 < q.1 := hqS.1
      have h1 : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < q.1 :=
        (tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 _ hρ
      have h2 : ∀ᶠ j : ℕ in atTop, q.1 ^ 2 + q.2 ^ 2 < (j : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually_gt_atTop _
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [h1, h2] with j hj1 hj2
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hmem : q ∈ tset j := ⟨hj1, show q.1 ^ 2 + q.2 ^ 2 < ((j : ℝ) + 1) ^ 2 by nlinarith⟩
      rw [indicator_of_mem hmem]
  exact le_of_tendsto' hT fun j => trunc_le v u hv hu hlim k j

end FrameInverseSquareParts

end FracInternal

end Breakdown
