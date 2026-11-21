import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldMetric

open scoped ENNReal Topology NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Internal.HeldMetric in
theorem extendedHeldMetricHolds_of (_h1 : GraphClosedHolds) (_h2 : ReadingEnergyHolds) :
    ExtendedHeldMetricHolds := by
  intro k d hd
  have hw : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hwm : Measurable d.weightFn := hd.weightFn_measurable
  have hC : ∀ y, d.weightFn y ≤ d.weightMax := hd.weightFn_upper
  have hw0 : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hS := continuous_sizeZ (k := k) hwm hC hw0
  have hc0 : 0 ≤ 2 * d.sizeBound / d.supBound :=
    div_nonneg (mul_nonneg zero_le_two hd.sizeBound_nonneg) hd.supBound_pos.le
  refine ⟨?_, ⟨Real.sqrt (min 1 d.weight), Real.sqrt_pos.2 (lt_min one_pos hd.weight_pos),
    fun x _ y _ => (sizeZ_lower hw hC (x.1 - y.1) (x.2 - y.2)).trans (le_max_left _ _)⟩, ?_, ?_⟩
  · have c1 : IsClosed {x : XX × (Fin k → ℝ) | gradCLM x.1 ∈ invariantHH d.symmetries} :=
      (isClosed_invariant d.symmetries).preimage (gradCLM.continuous.comp continuous_fst)
    have c2 : IsClosed {x : XX × (Fin k → ℝ) | sizeZ d.weightFn x.1 x.2 ≤ 2 * d.sizeBound} :=
      isClosed_le hS continuous_const
    have c3 : IsClosed {x : XX × (Fin k → ℝ) | supGrad x.1 ≤ ENNReal.ofReal d.supBound} :=
      (isClosed_supGrad_le _).preimage continuous_fst
    exact c1.inter (c2.inter c3)
  · intro x hx y hy z hz
    have e1 : x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) := (sub_add_sub_cancel x.1 y.1 z.1).symm
    have e2 : x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) := (sub_add_sub_cancel x.2 y.2 z.2).symm
    have hsz : sizeZ d.weightFn (x.1 - z.1) (x.2 - z.2) ≤
        sizeZ d.weightFn (x.1 - y.1) (x.2 - y.2) + sizeZ d.weightFn (y.1 - z.1) (y.2 - z.2) :=
      (congrArg₂ (sizeZ d.weightFn) e1 e2).trans_le (sizeZ_add_le hwm hC hw0 _ _ _ _)
    have hxy := supGrad_sub_ne_top hx.2.2 hy.2.2
    have hyz := supGrad_sub_ne_top hy.2.2 hz.2.2
    have hsup : (supGrad (x.1 - z.1)).toReal ≤
        (supGrad (x.1 - y.1)).toReal + (supGrad (y.1 - z.1)).toReal :=
      (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hxy, hyz⟩)
        ((congrArg supGrad e1).trans_le (supGrad_add_le _ _))).trans_eq
        (ENNReal.toReal_add hxy hyz)
    refine max_le ?_ ?_
    · exact hsz.trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    · calc 2 * d.sizeBound / d.supBound * (supGrad (x.1 - z.1)).toReal
          ≤ 2 * d.sizeBound / d.supBound * ((supGrad (x.1 - y.1)).toReal +
            (supGrad (y.1 - z.1)).toReal) := mul_le_mul_of_nonneg_left hsup hc0
        _ = 2 * d.sizeBound / d.supBound * (supGrad (x.1 - y.1)).toReal +
            2 * d.sizeBound / d.supBound * (supGrad (y.1 - z.1)).toReal := mul_add _ _ _
        _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)
  · intro x hx y hy u hu hlim ε hev
    have hT : Tendsto (fun n => x - u n) atTop (𝓝 (x - y)) := tendsto_const_nhds.sub hlim
    have hε : 0 ≤ ε := by
      obtain ⟨n, hn⟩ := hev.exists
      exact (Real.sqrt_nonneg _).trans ((le_max_left _ _).trans hn)
    refine max_le ?_ ?_
    · exact le_of_tendsto ((hS.tendsto (x - y)).comp hT)
        (hev.mono fun n hn => (le_max_left _ _).trans hn)
    · exact sup_part_le hc0 hε (fun n => x.1 - (u n).1) (x.1 - y.1)
        (tendsto_const_nhds.sub ((continuous_fst.tendsto y).comp hlim))
        (fun n => supGrad_sub_ne_top hx.2.2 (hu n).2.2)
        (hev.mono fun n hn => (le_max_right _ _).trans hn)

end Breakdown.Cert
