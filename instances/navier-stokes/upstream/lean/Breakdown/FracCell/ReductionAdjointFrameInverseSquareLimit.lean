import Breakdown.FracCell.ReductionAdjointFrameInverseSquareParts
import Breakdown.FracCell.ReductionAdjointWeightedInverseSquare

open scoped ContDiff
open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown

namespace FracInternal

namespace FrameInverseSquareParts

namespace GradientLimitInternal

open SteadyCert CellCert.Reduction
open Breakdown.CellCert.Spectral.Internal.CylIntegral CellCert.Reduction.ModeMeasurableInternal
  CellCert.Reduction.WeightedInverseSquareInternal CellCert.Reduction.GradientModeSumInternal
  CellCert.Reduction.ModePairingInternal

theorem entrySq_cont : Continuous (fun M : Space →L[ℝ] Space => entrySq M) := by
  unfold entrySq
  exact continuous_finsetSum _ fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm.pow 2)

theorem entrySq_nn (M : Space →L[ℝ] Space) : 0 ≤ entrySq M := by
  unfold entrySq
  positivity

theorem frameModeSq_nn (D : Space → (Space →L[ℝ] Space)) (k : ℤ) (ρ z : ℝ) : 0 ≤ frameModeSq D k ρ z := by
  unfold frameModeSq
  positivity

theorem side_meas (D : Space → (Space →L[ℝ] Space)) (hD : AEStronglyMeasurable D volume) (k : ℤ) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq D k q.1 q.2))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have hGc : ∀ c, AEStronglyMeasurable (fun y => D y (ringFrame c y)) volume := fun c =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hD.prodMk (ringFrame_meas c).aestronglyMeasurable)
  refine AEMeasurable.ennreal_ofReal ?_
  unfold frameModeSq
  refine (aemeasurable_const.mul measurable_fst.aemeasurable).mul ?_
  have hc : ∀ c : Fin 3, AEMeasurable (fun q : ℝ × ℝ =>
      ‖angularMode (horizontalPart fun y => D y (ringFrame c y)) k q.1 q.2‖ ^ 2 +
        ‖angularMode (verticalPart fun y => D y (ringFrame c y)) k q.1 q.2‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := fun c =>
    ((modeMeasurable _ (horizontal_meas (hGc c)) k).aemeasurable.norm.pow_const 2).add
      ((modeMeasurable _ (vertical_meas (hGc c)) k).aemeasurable.norm.pow_const 2)
  simp only [Fin.sum_univ_three]
  exact ((hc 0).add (hc 1)).add (hc 2)

theorem coefEnergy_le (D : Space → (Space →L[ℝ] Space)) (hD : AEStronglyMeasurable D volume) (k : ℤ) :
    modeGradientSide D k ≤ ∫⁻ y, ENNReal.ofReal (entrySq (D y)) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hGc : ∀ c, AEStronglyMeasurable (fun y => D y (ringFrame c y)) volume := fun c =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hD.prodMk (ringFrame_meas c).aestronglyMeasurable)
  have hA : ∀ c, AEStronglyMeasurable (horizontalPart fun y => D y (ringFrame c y)) volume :=
    fun c => horizontal_meas (hGc c)
  have hB : ∀ c, AEStronglyMeasurable (verticalPart fun y => D y (ringFrame c y)) volume :=
    fun c => vertical_meas (hGc c)
  have hslA : ∀ c, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
    ((hA c).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hslB : ∀ c, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
    ((hB c).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hE : AEMeasurable (fun y => ENNReal.ofReal (entrySq (D y))) volume :=
    (entrySq_cont.comp_aestronglyMeasurable hD).aemeasurable.ennreal_ofReal
  calc modeGradientSide D k
      ≤ ∑' j : ℤ, ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq D j q.1 q.2) :=
        ENNReal.le_tsum (f := fun j : ℤ => ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq D j q.1 q.2)) k
    _ = ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∑' j : ℤ, ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq D j q.1 q.2) :=
        (lintegral_tsum fun j => side_meas D hD j).symm
    _ ≤ ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal q.1 *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (entrySq (D (ringPoint q.1 θ q.2))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS, ae_all_iff.mpr hslA, ae_all_iff.mpr hslB] with q hq h1 h2
        have hρ : 0 < q.1 := hq.1
        have e : ∀ k : ℤ, ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq D k q.1 q.2) =
            ENNReal.ofReal q.1 * ∑ c : Fin 3,
              (ENNReal.ofReal (2 * Real.pi * ‖angularMode (horizontalPart fun y => D y (ringFrame c y)) k q.1 q.2‖ ^ 2)
                + ENNReal.ofReal (2 * Real.pi * ‖angularMode (verticalPart fun y => D y (ringFrame c y)) k q.1 q.2‖ ^ 2)) := by
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
            (‖horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
            (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
          ((h1 c).aemeasurable.norm.pow_const 2).ennreal_ofReal
        have hBm : ∀ c, AEMeasurable (fun θ => ENNReal.ofReal
            (‖verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
            (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
          ((h2 c).aemeasurable.norm.pow_const 2).ennreal_ofReal
        have hb1 : ∀ c, _ := fun c => circle_coef_sq
          (fun θ => horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)) (by rw [hν]; exact h1 c)
        have hb2 : ∀ c, _ := fun c => circle_coef_sq
          (fun θ => verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)) (by rw [hν]; exact h2 c)
        simp only [hν] at hb1 hb2
        calc _ = ∑ c : Fin 3,
              (∑' k : ℤ, ENNReal.ofReal (2 * Real.pi *
                ‖angularMode (horizontalPart fun y => D y (ringFrame c y)) k q.1 q.2‖ ^ 2)
              + ∑' k : ℤ, ENNReal.ofReal (2 * Real.pi *
                ‖angularMode (verticalPart fun y => D y (ringFrame c y)) k q.1 q.2‖ ^ 2)) :=
              Finset.sum_congr rfl fun c _ => ENNReal.tsum_add
          _ ≤ ∑ c : Fin 3,
              ((∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal
                (‖horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
              + ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal
                (‖verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2)) :=
              Finset.sum_le_sum fun c _ => add_le_add (hb1 c) (hb2 c)
          _ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∑ c : Fin 3,
              (ENNReal.ofReal (‖horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2)
              + ENNReal.ofReal (‖verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2)) := by
              have hsum := lintegral_finsetSum' (μ := volume.restrict (Ioo (-Real.pi) Real.pi)) Finset.univ
                (f := fun c θ => ENNReal.ofReal
                  (‖horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2) +
                  ENNReal.ofReal (‖verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)‖ ^ 2))
                (fun c _ => (hAm c).add (hBm c))
              rw [hsum]
              exact Finset.sum_congr rfl fun c _ => (lintegral_add_left' (hAm c) _).symm
          _ = _ := by
              refine lintegral_congr fun θ => ?_
              have hf := frame_sum (D (ringPoint q.1 θ q.2)) (ringPoint q.1 θ q.2) (hR θ)
              rw [← hf, ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)]
              exact Finset.sum_congr rfl fun c _ => (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (entrySq (D y)) := cyl_le _ hE


theorem term_le (M : Space →L[ℝ] Space) (y : Space) (hy : ringRadius y ≠ 0) (c : Fin 3) :
    ‖horizontalPart (fun y => M (ringFrame c y)) y‖ ^ 2 ≤ entrySq M ∧
      ‖verticalPart (fun y => M (ringFrame c y)) y‖ ^ 2 ≤ entrySq M := by
  rw [← frame_sum M y hy]
  have hs := Finset.single_le_sum (f := fun c : Fin 3 => ‖horizontalPart (fun y => M (ringFrame c y)) y‖ ^ 2 +
      ‖verticalPart (fun y => M (ringFrame c y)) y‖ ^ 2) (fun c _ => by positivity) (Finset.mem_univ c)
  have h1 := sq_nonneg ‖horizontalPart (fun y => M (ringFrame c y)) y‖
  have h2 := sq_nonneg ‖verticalPart (fun y => M (ringFrame c y)) y‖
  constructor <;> linarith

def SliceL2 (D : Space → (Space →L[ℝ] Space)) (q : ℝ × ℝ) : Prop :=
  ∀ c : Fin 3,
    MemLp (fun θ => horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
    MemLp (fun θ => verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi))

theorem slices (D : Space → (Space →L[ℝ] Space)) (hD : AEStronglyMeasurable D volume)
    (hfin : ∫⁻ y, ENNReal.ofReal (entrySq (D y)) ≠ ⊤) :
    ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), SliceL2 D q := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hEm : AEStronglyMeasurable (fun y => entrySq (D y)) volume := entrySq_cont.comp_aestronglyMeasurable hD
  have hint : Integrable (fun y => entrySq (D y)) :=
    (lintegral_ofReal_ne_top_iff_integrable hEm (ae_of_all _ fun y => entrySq_nn _)).mp hfin
  have hGc : ∀ c, AEStronglyMeasurable (fun y => D y (ringFrame c y)) volume := fun c =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hD.prodMk (ringFrame_meas c).aestronglyMeasurable)
  have hslA : ∀ c, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => horizontalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
    ((horizontal_meas (hGc c)).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  have hslB : ∀ c, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => verticalPart (fun y => D y (ringFrame c y)) (ringPoint q.1 θ q.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := fun c =>
    ((vertical_meas (hGc c)).comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
  filter_upwards [slice_fin _ hint, ae_restrict_mem hS, ae_all_iff.mpr hslA, ae_all_iff.mpr hslB]
    with q hq hqS h1 h2
  have hρ : 0 < q.1 := hqS.1
  have hR : ∀ θ, ringRadius (ringPoint q.1 θ q.2) ≠ 0 := fun θ => by
    rw [ringRadius_ringPoint _ _ _ hρ.le]; exact hρ.ne'
  intro c
  rw [hν]
  constructor
  · refine (memLp_two_iff_integrable_sq_norm (h1 c)).mpr ?_
    refine (lintegral_ofReal_ne_top_iff_integrable ((h1 c).norm.pow 2) (ae_of_all _ fun θ => sq_nonneg _)).mp ?_
    refine ne_top_of_le_ne_top hq.ne (lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_)
    exact (term_le (D (ringPoint q.1 θ q.2)) (ringPoint q.1 θ q.2) (hR θ) c).1
  · refine (memLp_two_iff_integrable_sq_norm (h2 c)).mpr ?_
    refine (lintegral_ofReal_ne_top_iff_integrable ((h2 c).norm.pow 2) (ae_of_all _ fun θ => sq_nonneg _)).mp ?_
    refine ne_top_of_le_ne_top hq.ne (lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_)
    exact (term_le (D (ringPoint q.1 θ q.2)) (ringPoint q.1 θ q.2) (hR θ) c).2

theorem sq_split (a b : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ‖a + b‖ ^ 2 ≤ (1 + ε) * ‖a‖ ^ 2 + (1 + ε⁻¹) * ‖b‖ ^ 2 := by
  set x := ‖a‖
  set y := ‖b‖
  have hinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have h0 : 0 ≤ (ε * x - y) ^ 2 * ε⁻¹ := by positivity
  have e : (ε * x - y) ^ 2 * ε⁻¹ = ε * x ^ 2 - 2 * x * y + ε⁻¹ * y ^ 2 := by
    linear_combination (ε * x ^ 2 - 2 * x * y) * hinv
  have h1 : ‖a + b‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [h0, e, h1]

theorem mode_add_h (A B : Space → (Space →L[ℝ] Space)) (q : ℝ × ℝ) (hB : SliceL2 B q)
    (hD : SliceL2 (fun y => A y - B y) q) (c : Fin 3) (k : ℤ) :
    angularMode (horizontalPart fun y => A y (ringFrame c y)) k q.1 q.2 =
      angularMode (horizontalPart fun y => B y (ringFrame c y)) k q.1 q.2 +
        angularMode (horizontalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2 := by
  rw [← coef_ring, ← coef_ring, ← coef_ring, ← coef_add _ _ (hB c).1 (hD c).1]
  congr 1
  funext θ
  simp only [horizontalPart, ContinuousLinearMap.sub_apply, PiLp.sub_apply, Complex.ofReal_sub]
  ring

theorem mode_add_v (A B : Space → (Space →L[ℝ] Space)) (q : ℝ × ℝ) (hB : SliceL2 B q)
    (hD : SliceL2 (fun y => A y - B y) q) (c : Fin 3) (k : ℤ) :
    angularMode (verticalPart fun y => A y (ringFrame c y)) k q.1 q.2 =
      angularMode (verticalPart fun y => B y (ringFrame c y)) k q.1 q.2 +
        angularMode (verticalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2 := by
  rw [← coef_ring, ← coef_ring, ← coef_ring, ← coef_add _ _ (hB c).2 (hD c).2]
  congr 1
  funext θ
  simp only [verticalPart, ContinuousLinearMap.sub_apply, PiLp.sub_apply, Complex.ofReal_sub]
  ring

theorem point_both (A B : Space → (Space →L[ℝ] Space)) (q : ℝ × ℝ) (hB : SliceL2 B q)
    (hD : SliceL2 (fun y => A y - B y) q) (k : ℤ) (ε : ℝ) (hε : 0 < ε) :
    frameModeSq A k q.1 q.2 ≤ (1 + ε) * frameModeSq B k q.1 q.2 +
        (1 + ε⁻¹) * frameModeSq (fun y => A y - B y) k q.1 q.2 ∧
      frameModeSq B k q.1 q.2 ≤ (1 + ε) * frameModeSq A k q.1 q.2 +
        (1 + ε⁻¹) * frameModeSq (fun y => A y - B y) k q.1 q.2 := by
  unfold frameModeSq
  simp only [mode_add_h A B q hB hD, mode_add_v A B q hB hD]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  constructor
  · refine Finset.sum_le_sum fun c _ => ?_
    have h1 := sq_split (angularMode (horizontalPart fun y => B y (ringFrame c y)) k q.1 q.2)
      (angularMode (horizontalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2) ε hε
    have h2 := sq_split (angularMode (verticalPart fun y => B y (ringFrame c y)) k q.1 q.2)
      (angularMode (verticalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2) ε hε
    linarith
  · refine Finset.sum_le_sum fun c _ => ?_
    have h1 := sq_split (angularMode (horizontalPart fun y => B y (ringFrame c y)) k q.1 q.2 +
        angularMode (horizontalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2)
      (-angularMode (horizontalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2) ε hε
    have h2 := sq_split (angularMode (verticalPart fun y => B y (ringFrame c y)) k q.1 q.2 +
        angularMode (verticalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2)
      (-angularMode (verticalPart fun y => (A y - B y) (ringFrame c y)) k q.1 q.2) ε hε
    simp only [add_neg_cancel_right, norm_neg] at h1 h2
    linarith


theorem side_both (A B : Space → (Space →L[ℝ] Space)) (hB : AEStronglyMeasurable B volume)
    (hBf : ∫⁻ y, ENNReal.ofReal (entrySq (B y)) ≠ ⊤)
    (hD : AEStronglyMeasurable (fun y => A y - B y) volume)
    (hDf : ∫⁻ y, ENNReal.ofReal (entrySq (A y - B y)) ≠ ⊤) (k : ℤ) (ε : ℝ) (hε : 0 < ε) :
    modeGradientSide A k ≤ ENNReal.ofReal (1 + ε) * modeGradientSide B k +
        ENNReal.ofReal (1 + ε⁻¹) * modeGradientSide (fun y => A y - B y) k ∧
      modeGradientSide B k ≤ ENNReal.ofReal (1 + ε) * modeGradientSide A k +
        ENNReal.ofReal (1 + ε⁻¹) * modeGradientSide (fun y => A y - B y) k := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hpt := (slices B hB hBf).and (slices (fun y => A y - B y) hD hDf)
  have key : ∀ (X Y : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable Y volume →
      (∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), frameModeSq X k q.1 q.2 ≤ (1 + ε) * frameModeSq Y k q.1 q.2 +
        (1 + ε⁻¹) * frameModeSq (fun y => A y - B y) k q.1 q.2) →
      modeGradientSide X k ≤ ENNReal.ofReal (1 + ε) * modeGradientSide Y k +
        ENNReal.ofReal (1 + ε⁻¹) * modeGradientSide (fun y => A y - B y) k := by
    intro X Y hY hXY
    unfold modeGradientSide
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left' ((side_meas Y hY k).const_mul _)]
    refine lintegral_mono_ae ?_
    filter_upwards [hXY, ae_restrict_mem hS] with q hq hqS
    have hρ : 0 ≤ 2 * Real.pi * q.1 := by
      have h0 : 0 < q.1 := hqS.1
      positivity
    have h1 := frameModeSq_nn Y k q.1 q.2
    have h2 := frameModeSq_nn (fun y => A y - B y) k q.1 q.2
    have hinv : 0 ≤ ε⁻¹ := by positivity
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) (mul_nonneg hρ h1)) (mul_nonneg (by linarith) (mul_nonneg hρ h2))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_left hq hρ
    nlinarith [this]
  constructor
  · refine key A B hB ?_
    filter_upwards [hpt] with q hq
    exact (point_both A B q hq.1 hq.2 k ε hε).1
  · refine key B A ((hD.add hB).congr (ae_of_all _ fun y => by simp)) ?_
    filter_upwards [hpt] with q hq
    exact (point_both A B q hq.1 hq.2 k ε hε).2

theorem coeff_tend (x : ENNReal) (hx : x ≠ ⊤) :
    Tendsto (fun j : ℕ => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * x) atTop (𝓝 x) := by
  have h0 : Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h0
  have h1 : Tendsto (fun j : ℕ => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal h0
  simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hx)

theorem tail_tend (x : ENNReal) (C : ℝ) (d : ℕ → ENNReal) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => x + ENNReal.ofReal C * d n) atTop (𝓝 x) := by
  have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hd (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at this
  simpa using (tendsto_const_nhds (x := x)).add this

end GradientLimitInternal

open SteadyCert GradientLimitInternal in
theorem modeGradientLimit : ModeGradientLimitStatement := by
  intro G Gn hG hGn hGi hlim k
  have hDm : ∀ n, AEStronglyMeasurable (fun y => Gn n y - G y) volume := fun n => (hGn n).sub hG
  have hGf : ∫⁻ y, ENNReal.ofReal (entrySq (G y)) ≠ ⊤ := hGi.lintegral_lt_top.ne
  have hev : ∀ᶠ n in atTop, ∫⁻ y, ENNReal.ofReal (entrySq (Gn n y - G y)) ≠ ⊤ :=
    ((tendsto_order.1 hlim).2 1 one_pos).mono fun n hn => (hn.trans ENNReal.one_lt_top).ne
  have hd : Tendsto (fun n => modeGradientSide (fun y => Gn n y - G y) k) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le)
      (fun n => coefEnergy_le _ (hDm n) k)
  have hb : modeGradientSide G k ≠ ⊤ := ne_top_of_le_ne_top hGf (coefEnergy_le G hG k)
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      modeGradientSide (Gn n) k ≤ ENNReal.ofReal (1 + ε) * modeGradientSide G k +
          ENNReal.ofReal (1 + ε⁻¹) * modeGradientSide (fun y => Gn n y - G y) k ∧
        modeGradientSide G k ≤ ENNReal.ofReal (1 + ε) * modeGradientSide (Gn n) k +
          ENNReal.ofReal (1 + ε⁻¹) * modeGradientSide (fun y => Gn n y - G y) k :=
    fun ε hε => hev.mono fun n hn => side_both (Gn n) G hG hGf (hDm n) hn k ε hε
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have hlt : l ≠ ⊤ := ne_top_of_lt hl
    obtain ⟨j, hj⟩ := ((tendsto_order.1 (coeff_tend l hlt)).2 _ hl).exists
    have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    filter_upwards [(tendsto_order.1 (tail_tend _ (1 + (1 / ((j : ℝ) + 1))⁻¹) _ hd)).2 _ hj, key _ hε]
      with n h1 h2
    by_contra hn
    rw [not_lt] at hn
    have h3 : modeGradientSide G k ≤ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * l +
        ENNReal.ofReal (1 + (1 / ((j : ℝ) + 1))⁻¹) * modeGradientSide (fun y => Gn n y - G y) k :=
      h2.2.trans (by gcongr)
    exact lt_irrefl _ (h3.trans_lt h1)
  · obtain ⟨j, hj⟩ := ((tendsto_order.1 (coeff_tend _ hb)).2 _ hu).exists
    have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    filter_upwards [(tendsto_order.1 (tail_tend _ (1 + (1 / ((j : ℝ) + 1))⁻¹) _ hd)).2 _ hj, key _ hε]
      with n h1 h2
    exact h2.1.trans_lt h1


end FrameInverseSquareParts

end FracInternal

end Breakdown
