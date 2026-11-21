import Breakdown.CellReduction.AdjointRemainderAzimuthalParts

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

open SteadyCert CellCert.Reduction FracInternal.FrameInverseSquareParts
  Breakdown.CellCert.Spectral.Internal.CylIntegral CellCert.Reduction.ModeMeasurableInternal
  CellCert.Reduction.WeightedInverseSquareInternal CellCert.Reduction.GradientModeSumInternal

namespace GradientTotalInternal

theorem entryNormSq_continuous : Continuous matSq := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem entryNormSq_eq (M : Space →L[ℝ] Space) : matSq M = entrySq M := rfl

end GradientTotalInternal

open GradientTotalInternal in
theorem gradientModeTotal : GradientModeTotalHolds := by
  intro G hD
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hGc : ∀ c, AEStronglyMeasurable (fun y => G y (ringFrame c y)) volume := fun c =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hD.prodMk (ringFrame_meas c).aestronglyMeasurable)
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
    (entryNormSq_continuous.comp_aestronglyMeasurable hD).aemeasurable.ennreal_ofReal
  unfold modeGradientSide
  simp_rw [entryNormSq_eq]
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
              rw [← frame_sum (G (ringPoint q.1 θ q.2)) (ringPoint q.1 θ q.2) (hR θ),
                ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)]
              exact Finset.sum_congr rfl fun c _ => (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (entrySq (G y)) := cyl_le _ hE

end AzimuthalParts

end AdjointDefect

end Breakdown
