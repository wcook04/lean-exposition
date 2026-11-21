import Breakdown.Torus.ShellDefs
import Breakdown.Torus.Basic

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace SourceCont.Internal

theorem forceV_apply (s : ℝ) (F : Space → Space) (k : Lattice) :
    ((forceV s F : V) : Seq) k = forceSeq s F k := rfl

theorem norm_forceSeq_le_of_le (F : Space → Space) {s₁ s : ℝ} (h₁ : 0 < s₁) (h : s₁ ≤ s) (k : Lattice) :
    ‖forceSeq s F k‖ ≤ 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor s₁ k) := by
  have hs : 0 < s := h₁.trans_le h
  have hA : ‖freqTrCoef F k‖ ≤ ∫ x in cell, ‖complexify (F x)‖ := FreqTrSeries.Internal.norm_freqTrCoef_le k
  have hw : 0 ≤ Real.sqrt (weight k) := Real.sqrt_nonneg _
  have hh : heatFactor s k ≤ heatFactor s₁ k := Internal.heatFactor_anti h k
  have hh0 : 0 ≤ heatFactor s k := Internal.heatFactor_nonneg _ _
  have hb : 0 ≤ Real.sqrt (weight k) * heatFactor s₁ k := mul_nonneg hw (Internal.heatFactor_nonneg _ _)
  calc ‖forceSeq s F k‖ ≤ Real.sqrt (weight k) * heatFactor s k * (2 * ‖freqTrCoef F k‖) :=
        Force.Internal.norm_forceSeq_le hs F k
    _ ≤ Real.sqrt (weight k) * heatFactor s₁ k * (2 * ∫ x in cell, ‖complexify (F x)‖) := by
        gcongr
    _ = 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor s₁ k) := by ring

theorem forceV_continuousOn (F : Space → Space) : ContinuousOn (fun s => forceV s F) (Ioi 0) := by
  intro s₀ hs₀
  have hs₀' : (0 : ℝ) < s₀ := hs₀
  rw [ContinuousWithinAt, tendsto_subtype_rng]
  have hev : ∀ᶠ s in 𝓝[Ioi 0] s₀, s₀ / 2 ≤ s :=
    nhdsWithin_le_nhds (Ici_mem_nhds (half_lt_self hs₀'))
  apply Internal.tendsto_seq
    (b := fun k => 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor (s₀ / 2) k))
  · refine ((Internal.summable_weight_heat (half_pos hs₀')).mul_left
      ((2 * ∫ x in cell, ‖complexify (F x)‖) ^ 2)).congr fun k => ?_
    simp only [mul_pow, Real.sq_sqrt (Internal.weight_pos k).le]
  · intro k
    simp only [forceV_apply]
    have e : forceSeq s₀ F k = (Real.sqrt (weight k) * heatFactor s₀ k) • divFree k (freqTrCoef F k) := by
      simp only [forceSeq, if_pos hs₀']
    rw [e]
    have hc : Tendsto (fun s => (Real.sqrt (weight k) * heatFactor s k) • divFree k (freqTrCoef F k))
        (𝓝[Ioi 0] s₀) (𝓝 ((Real.sqrt (weight k) * heatFactor s₀ k) • divFree k (freqTrCoef F k))) :=
      (((continuous_const.mul (Internal.continuous_heatFactor k)).smul continuous_const).tendsto
        s₀).mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    simp only [forceSeq, if_pos hs']
  · filter_upwards [hev] with s hs k
    rw [forceV_apply]
    exact norm_forceSeq_le_of_le F (half_pos hs₀') hs k

end SourceCont.Internal

theorem sourceOp_continuousOn (μ : ℝ) (A : Freq.L2R) (hμ : 0 < μ) :
    ContinuousOn (fun τ => sourceOp μ τ A) (Ioi 0) := by
  have e : (fun τ => sourceOp μ τ A) =
      (fun s => forceV s (fun x => (A : Space → Space) (simCoord μ x))) ∘ (fun τ => μ * τ) := by
    funext τ
    change sourceFun μ τ A = _
    simp only [sourceFun, if_pos hμ, Function.comp_apply]
  rw [e]
  refine (SourceCont.Internal.forceV_continuousOn _).comp (continuous_const.mul continuous_id).continuousOn ?_
  intro τ hτ
  exact mul_pos hμ hτ

end Breakdown.Periodic
