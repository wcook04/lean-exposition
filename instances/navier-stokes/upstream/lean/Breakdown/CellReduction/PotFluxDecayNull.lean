import Breakdown.CellReduction.PotentialShape
import Breakdown.CertCell.ShapeSphericalDivFrame

open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (heightRatio)

namespace FluxDecay.Internal

theorem firstCoord_ne_ae : ∀ᵐ y : Space, y 0 ≠ 0 := by
  set K : Submodule ℝ Space := LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hs : K ≠ ⊤ := by
    intro h
    have hm : unitVector 0 ∈ K := by rw [h]; trivial
    simp [K, unitVector] at hm
  have h0 := Measure.addHaar_submodule (volume : Measure Space) K hs
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with y hy
  intro h
  exact hy (by simp [K, h])

theorem heightSq_ne_ae (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ᵐ y : Space, y 2 ^ 2 ≠ f (y 0 ^ 2 + y 1 ^ 2) := by
  set T : Set (ℝ × (Fin 2 → ℝ)) := {p | p.1 ^ 2 = f (p.2 0 ^ 2 + p.2 1 ^ 2)} with hT
  have hTm : MeasurableSet T := (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
  have hslice : ∀ v : Fin 2 → ℝ, (volume : Measure ℝ) ((fun a => (a, v)) ⁻¹' T) = 0 := by
    intro v
    refine measure_mono_null (t := ({Real.sqrt (f (v 0 ^ 2 + v 1 ^ 2)), -Real.sqrt (f (v 0 ^ 2 + v 1 ^ 2))} : Set ℝ))
      ?_ ((Set.toFinite _).measure_zero _)
    intro a ha
    simp only [Set.mem_preimage, hT, Set.mem_ofPred_eq] at ha
    have h1 : Real.sqrt (f (v 0 ^ 2 + v 1 ^ 2)) = |a| := by rw [← ha, Real.sqrt_sq_eq_abs]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases le_total 0 a with h | h
    · left
      rw [h1, abs_of_nonneg h]
    · right
      rw [h1, abs_of_nonpos h, neg_neg]
  have hT0 : ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) T = 0 := by
    rw [Measure.prod_apply_symm hTm]
    simp [hslice]
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 2).comp
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hpre := hmp.measure_preimage hTm.nullMeasurableSet
  have hz : (volume : Measure Space) {y : Space | y 2 ^ 2 = f (y 0 ^ 2 + y 1 ^ 2)} = 0 := by
    have hT0' : ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))) T = 0 := hT0
    rw [← hT0', ← hpre]
    congr 1
  rw [measure_eq_zero_iff_ae_notMem] at hz
  filter_upwards [hz] with y hy
  exact hy


theorem chartCoord_ne_ae (P : ShapeParams) (hP : IsShapeParams P) (b : ℝ) :
    ∀ᵐ y : Space, chartCoord P y ≠ b := by
  filter_upwards [firstCoord_ne_ae, heightSq_ne_ae (fun s => (b * P.chartLength / (1 - b)) ^ 2 - s)
    (by fun_prop)] with y h0 h2
  intro h
  have hL := hP.chartLength_pos
  have hy : y ≠ 0 := fun e => h0 (by simp [e])
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hne : ‖y‖ + P.chartLength ≠ 0 := by positivity
  unfold chartCoord at h
  rw [div_eq_iff hne] at h
  have hb : b ≠ 1 := by
    rintro rfl
    linarith
  have hR : ‖y‖ = b * P.chartLength / (1 - b) := by
    rw [eq_div_iff (sub_ne_zero.2 (Ne.symm hb))]
    linarith
  apply h2
  have hsq := SphericalDivInternal.coords_sq y
  rw [← hR]
  nlinarith

theorem heightRatio_ne_ae (c : ℝ) : ∀ᵐ y : Space, heightRatio y ≠ c := by
  filter_upwards [firstCoord_ne_ae, heightSq_ne_ae (fun s => c ^ 2 * s / (1 - c ^ 2)) (by fun_prop)]
    with y h0 h2
  intro h
  have hy : y ≠ 0 := fun e => h0 (by simp [e])
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsq := SphericalDivInternal.coords_sq y
  have hz : y 2 = c * ‖y‖ := by
    unfold heightRatio at h
    rw [div_eq_iff hr.ne'] at h
    exact h
  have hq : 0 < y 0 ^ 2 := by positivity
  have hc : 1 - c ^ 2 ≠ 0 := by
    intro hc
    have : y 2 ^ 2 = ‖y‖ ^ 2 := by rw [hz, mul_pow, show c ^ 2 = 1 by linarith, one_mul]
    nlinarith
  apply h2
  rw [eq_div_iff hc]
  have e1 : y 2 ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [hz]; ring
  have e2 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by rw [← hsq]; ring
  linear_combination e1 + c ^ 2 * e2

end FluxDecay.Internal

end PotentialShape

end Breakdown
