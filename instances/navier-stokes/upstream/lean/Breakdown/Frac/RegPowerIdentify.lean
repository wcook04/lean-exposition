import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegIdentifyAuxCont
import Breakdown.Uniqueness.RegEmbed
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem integral_phi_smul_eq (α t : ℝ) (ξ : Space) (v : ℝ → CSpace) :
    ∫ s in (0 : ℝ)..t, ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • v s =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) •
        ∫ s in (0 : ℝ)..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • v s := by
  have hfac : ∀ s, ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • v s =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • (((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • v s) := by
    intro s
    rw [smul_smul]
    congr 1
    simp only [fracPhiFactor, powerHeatSymbol]
    push_cast
    ring
  simp_rw [hfac]
  rw [intervalIntegral.integral_smul]

theorem powerIdentify_of (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2)
    (h1 : PowerBilinIntegralStatement α) (h2 : PowerHeatXStatement α) :
    PowerIdentifyStatement α := by
  intro T hT F hF hd hs
  have hm : ∀ t ∈ Icc 0 T, AEStronglyMeasurable (F t) volume := fun t ht => ((hF 0).1 t ht).1
  have hfin : ∀ t ∈ Icc 0 T, ∀ m, hsNormSq m (F t) < ⊤ := fun t ht m => ((hF m).1 t ht).2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine ⟨continuousOn_embedX_physField fieldOpRealized_holds hF hs, fun t ht =>
    ⟨(h1 T hT F hF hd hs t ht).1, ?_⟩⟩
  simp only [sub_zero]
  apply Subtype.ext
  apply Lp.ext
  have e0 := coe_embedX_physField fieldOpRealized_holds (hm 0 h0) (hs 0 h0) (hfin 0 h0)
  have et := coe_embedX_physField fieldOpRealized_holds (hm t ht) (hs t ht) (hfin t ht)
  have eh := h2 t (embedX (physField (F 0)))
  have ei := (h1 T hT F hF hd hs t ht).2
  have ea := Lp.coeFn_add ((fracHeatX α t (embedX (physField (F 0))) : X) : L2C)
    (((∫ s in (0 : ℝ)..t,
        fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) : X) : L2C)
  filter_upwards [e0, et, eh, ei, ea] with ξ h0' ht' hh' hi' ha'
  have ha2 : (((fracHeatX α t (embedX (physField (F 0))) +
      ∫ s in (0 : ℝ)..t,
        fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))) : X) :
          L2C) : Space → CSpace) ξ =
      (((fracHeatX α t (embedX (physField (F 0)))) : X) : Space → CSpace) ξ +
      (((∫ s in (0 : ℝ)..t,
        fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) :
        X) : Space → CSpace) ξ := ha'
  refine ht'.trans (ha2.trans ?_).symm
  rw [hh', hi', h0', integral_phi_smul_eq, smul_smul]
  have hheat : fracHeatFactor α t ξ = powerHeatSymbol α (t - 0) ξ := by
    simp only [fracHeatFactor, powerHeatSymbol, sub_zero, max_eq_left ht.1]
  rw [hheat, mul_comm, ← smul_smul, ← smul_add, ← hd t ht ξ]

end Breakdown.SmoothFlow
