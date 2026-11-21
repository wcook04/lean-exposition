import Breakdown.Uniqueness.RegIdentifyAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem isMildX_embedX_physField (hH : HeatSemigroup) (hR : FieldOpRealized)
    (hH1 : H1Consistency) (hB : BilinH1Formula) (hBE : BilinExists) {T : ℝ} (hT : 0 < T)
    {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T) (hd : IsVarConstSymbol F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    IsMildX (fun t => embedX (physField (F t))) 0 T := by
  have hm : ∀ t ∈ Icc 0 T, AEStronglyMeasurable (F t) volume := fun t ht => ((hF 0).1 t ht).1
  have hfin : ∀ t ∈ Icc 0 T, ∀ m, hsNormSq m (F t) < ⊤ := fun t ht m => ((hF m).1 t ht).2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine ⟨continuousOn_embedX_physField hR hF hs, fun t ht =>
    ⟨intervalIntegrable_bilinX_physField hR hB hT hF hs ht, ?_⟩⟩
  simp only [sub_zero]
  apply Subtype.ext
  apply Lp.ext
  have e0 := coe_embedX_physField hR (hm 0 h0) (hs 0 h0) (hfin 0 h0)
  have et := coe_embedX_physField hR (hm t ht) (hs t ht) (hfin t ht)
  have eh := coe_heatX_ae hH hR t (embedX (physField (F 0)))
  have ei := coe_integral_bilinX_physField hH hR hB hT hF hd hs ht
  have ea := Lp.coeFn_add ((heatX t (embedX (physField (F 0))) : X) : L2C)
    (((∫ s in (0 : ℝ)..t,
        bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) : X) : L2C)
  filter_upwards [e0, et, eh, ei, ea] with ξ h0' ht' hh' hi' ha'
  have ha2 : (((heatX t (embedX (physField (F 0))) +
      ∫ s in (0 : ℝ)..t, bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s))) : X) :
        L2C) : Space → CSpace) ξ =
      (((heatX t (embedX (physField (F 0)))) : X) : Space → CSpace) ξ +
      (((∫ s in (0 : ℝ)..t, bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) :
        X) : Space → CSpace) ξ := ha'
  refine ht'.trans (ha2.trans ?_).symm
  rw [hh', hi', h0']
  have hfac : ∀ s, ((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • (((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) := by
    intro s
    rw [smul_smul]
    congr 1
    simp only [phiFactor, heatSymbol]
    push_cast
    ring
  simp_rw [hfac]
  rw [intervalIntegral.integral_smul, smul_smul]
  have hheat : heatFactor t ξ = heatSymbol (t - 0) ξ := by
    simp only [heatFactor, heatSymbol, sub_zero, max_eq_left ht.1]
  rw [hheat, mul_comm, ← smul_smul, ← smul_add, ← hd t ht ξ]

end Breakdown.SmoothFlow
