import Breakdown.FracCert.HeldExists
import Breakdown.FracCert.HeldLimit

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

open HeldLimitInternal

private theorem defect_at {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ)
    (L : Space →ₗ[ℝ] Space) (hJ : ∀ z, axialTurn (L z) = L (axialTurn z)) (y : Space)
    (h3 : d.profile p (L y) = L (d.profile p y)) (h4 : d.profilePower p (L y) = L (d.profilePower p y))
    (h6 : ∀ w, d.gradProfile p (L y) (L w) = L (d.gradProfile p y w))
    (h7 : ∀ i, d.actuator i (L y) = L (d.actuator i y)) :
    d.defect α p (L y) = L (d.defect α p y) := by
  simp only [FracCertData.defect, driftField, map_add, map_sub, map_smul, map_sum, h3, h4, h6, h7, hJ]

private theorem rhs_at {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ)
    (u : Space → Space) (G : Space → (Space →L[ℝ] Space)) (L : Space →ₗ[ℝ] Space) (y : Space)
    (hD : d.defect α p (L y) = L (d.defect α p y)) (hu : u (L y) = L (u y))
    (hG : ∀ w, G (L y) (L w) = L (G y w)) :
    -d.defect α p (L y) - G (L y) (u (L y)) = L (-d.defect α p y - G y (u y)) := by
  rw [hD, hu, hG, map_sub, map_neg]

private theorem quad_memLp {k N : ℕ} (d : FracCertData k N) {α : ℝ} (hd : IsFracCert α d)
    {p : Fin k → ℝ} (hp : p ∈ box d.radius) :
    MemLp (fun y => d.gradProfile p y (d.profile p y)) 2 volume := by
  obtain ⟨C, hC⟩ := hd.profile_bounds
  have hU : ContDiff ℝ 1 (d.profile p) := hd.profile_smooth p hp
  have hcont : Continuous (fun y => d.gradProfile p y (d.profile p y)) :=
    (hU.continuous_fderiv one_ne_zero).clm_apply hU.continuous
  have hm := hcont.aestronglyMeasurable (μ := volume)
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) volume :=
    integrable_one_add_norm (by simp; norm_num)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ((hint.const_mul (C ^ 4)).mono' (hm.norm.pow 2)
    (ae_of_all _ fun y => ?_))
  obtain ⟨h1, h2, -⟩ := hC p hp y
  have ht : 0 < 1 + ‖y‖ := by positivity
  have hb : ‖d.gradProfile p y (d.profile p y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) * (C * (1 + ‖y‖) ^ (-(1 : ℝ))) :=
    ((d.gradProfile p y).le_opNorm _).trans
      (mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2))
  have he : C * (1 + ‖y‖) ^ (-(2 : ℝ)) * (C * (1 + ‖y‖) ^ (-(1 : ℝ))) = C ^ 2 * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    rw [show (-(3 : ℝ)) = -(2 : ℝ) + -(1 : ℝ) by norm_num, Real.rpow_add ht]
    ring
  have hsq : ((1 + ‖y‖) ^ (-(3 : ℝ))) ^ 2 = (1 + ‖y‖) ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  rw [he] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖d.gradProfile p y (d.profile p y)‖ ^ 2 ≤ (C ^ 2 * (1 + ‖y‖) ^ (-(3 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = C ^ 4 * (1 + ‖y‖) ^ (-(6 : ℝ)) := by rw [mul_pow, hsq]; ring

theorem defectRightSide : DefectRightSideStatement := by
  intro α hα1 hα2 k N d hd p hp
  refine ⟨?_, ?_⟩
  · have hs : MemLp (fun y => ∑ i, d.multiplier p i • d.actuator i y) 2 volume :=
      memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (d.multiplier p i)
    exact (((hd.profile_drift p hp).add (hd.profile_power p hp).1).add (quad_memLp d hd hp)).add hs
  · intro u G H hs
    obtain ⟨m1, m6, mG, iG, wG, -⟩ := profileEmbedData α hα1 hα2 d hd p hp
    have hWc := hd.profile_class p hp
    have hPPc := weakPowerClass_holds α hα1 hα2 d.order _ _ m1 m6 hWc (hd.profile_power p hp)
    obtain ⟨hgt, hgm⟩ := gradientClass_holds d.order _ _ m1 m6 mG iG wG hWc
    obtain ⟨hGt, hGm⟩ := gradientClass_holds d.order u G hs.measurable_velocity hs.velocity_six
      hs.measurable_gradient hs.gradient_two hs.weak_gradient hs.symmetric
    have hAt : ∀ᵐ y ∂volume, ∀ i, d.actuator i (turnStep d.order y) = turnStep d.order (d.actuator i y) :=
      ae_all_iff.2 fun i => (hd.actuator_class i).1
    have hAm : ∀ᵐ y ∂volume, ∀ i, d.actuator i (mirror y) = mirror (d.actuator i y) :=
      ae_all_iff.2 fun i => (hd.actuator_class i).2
    constructor
    · filter_upwards [hWc.1, hPPc.1, hgt, hAt, hs.symmetric.1, hGt] with y h3 h4 h6 h7 hu hG
      exact rhs_at d α p u G (turnLin d.order) y
        (defect_at d α p (turnLin d.order) (axial_turn d.order) y h3 h4 h6 h7) hu hG
    · filter_upwards [hWc.2, hPPc.2, hgm, hAm, hs.symmetric.2, hGm] with y h3 h4 h6 h7 hu hG
      exact rhs_at d α p u G mirrorLin y (defect_at d α p mirrorLin axial_mirror y h3 h4 h6 h7) hu hG

end SteadyCert

end Breakdown
