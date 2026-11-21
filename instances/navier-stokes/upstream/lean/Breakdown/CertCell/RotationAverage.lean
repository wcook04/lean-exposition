import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.CoerciveModeL2

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace RotationAverageInternal

theorem measurePreserving_axialRot (φ : ℝ) :
    MeasurePreserving (axialRot φ) (volume : Measure Space) volume := by
  obtain ⟨R, hR⟩ := Coercive.axialRotationHolds_proof.1 φ
  have h : axialRot φ = R := funext fun y => (hR y).symm
  rw [h]
  exact R.measurePreserving

theorem measurableEmbedding_axialRot (φ : ℝ) : MeasurableEmbedding (axialRot φ) := by
  obtain ⟨R, hR⟩ := Coercive.axialRotationHolds_proof.1 φ
  have h : axialRot φ = R := funext fun y => (hR y).symm
  rw [h]
  exact R.toHomeomorph.measurableEmbedding

theorem quasiMeasurePreserving_axialRot_pair (ν : Measure ℝ) [SFinite ν] :
    Measure.QuasiMeasurePreserving (fun p : Space × ℝ => axialRot p.2 p.1)
      ((volume : Measure Space).prod ν) volume := by
  have hc : Continuous (fun p : Space × ℝ => axialRot p.2 p.1) := by
    have h := Coercive.ModeL2Internal.continuous_axialRot_pair.comp
      ((continuous_snd : Continuous (fun p : Space × ℝ => p.2)).prodMk continuous_fst)
    exact h
  refine ⟨hc.measurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_
  rw [Measure.map_apply hc.measurable hN, Measure.prod_apply_symm (hc.measurable hN)]
  have hz : ∀ φ : ℝ, (volume : Measure Space)
      ((fun y => (y, φ)) ⁻¹' ((fun p : Space × ℝ => axialRot p.2 p.1) ⁻¹' N)) = 0 := fun φ => by
    change (volume : Measure Space) (axialRot φ ⁻¹' N) = 0
    rw [(measurePreserving_axialRot φ).measure_preimage hN.nullMeasurableSet, h0]
  simp [hz]

end RotationAverageInternal

open RotationAverageInternal in
theorem rotationAverage : RotationAverageHolds := by
  intro f hf
  have hpair : AEMeasurable (Function.uncurry fun (y : Space) (φ : ℝ) => f (axialRot φ y))
      ((volume : Measure Space).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
    hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_axialRot_pair _)
  have hinner : ∀ φ : ℝ, ∫⁻ y, f (axialRot φ y) = ∫⁻ y, f y := fun φ =>
    (measurePreserving_axialRot φ).lintegral_comp_emb (measurableEmbedding_axialRot φ) f
  have hpi : ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : 1 / (2 * Real.pi) * (2 * Real.pi) = 1 := by
      field_simp
    rw [this, ENNReal.ofReal_one]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hpair]
  simp only [hinner, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, sub_zero]
  rw [mul_comm (∫⁻ y, f y), ← mul_assoc, hpi, one_mul]

end Bridge

end CertCell

end Breakdown
