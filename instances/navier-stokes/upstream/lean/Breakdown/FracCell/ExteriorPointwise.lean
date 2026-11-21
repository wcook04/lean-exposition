import Breakdown.FracCell.StExterior
import Breakdown.FracCell.ModelFormParts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly ModelFormInternal

theorem exteriorPointwise : ExteriorPointwiseStatement := by
  intro α _ _ k N c hc e he x _ y hy
  unfold CellSplit.localDensity ExteriorData.gradientCoef
  obtain ⟨hS, hGm⟩ := hc.model_outside y hy
  have hA : ∀ i, c.modelActuatorGrad i y = 0 := fun i => (hc.modelActuatorGrad_data i).2.2 y hy
  have hsum : ∑ i, x.2.2.2.1 i * entryInner (x.2.1 y) (c.modelActuatorGrad i y) = 0 := by
    simp [hA, entryInner]
  have hfull : 0 ≤ fullSecondSq (x.2.2.1 y) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcg : 0 ≤ curlGradSq (x.2.2.1 y) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : 0 ≤ (c.innerWeight - c.coercivity) * fullSecondSq (x.2.2.1 y) :=
    mul_nonneg (sub_nonneg.2 he.innerWeight_ge) hfull
  have h2 : 0 ≤ (c.splitVisc - c.innerWeight) * curlGradSq (x.2.2.1 y) :=
    mul_nonneg (sub_nonneg.2 he.innerWeight_le) hcg
  have hj : jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y) =
      -inner ℝ (curlOf (x.2.1 y)) (c.centreStrain y (curlOf (x.2.1 y)))
        + curlGradPart (c.centreCurlGrad y) (x.2.1 y) (x.1 y) := by
    rw [hS, hGm]
    exact jForm_eq _ _ _ _
  have hst : inner ℝ (curlOf (x.2.1 y)) (c.centreStrain y (curlOf (x.2.1 y)))
      ≤ e.strainBound y * ‖curlOf (x.2.1 y)‖ ^ 2 := by
    rw [real_inner_comm]
    exact he.strain_le y hy _
  have hpart := part_bound (c.centreCurlGrad y) (x.2.1 y) (x.1 y) (he.curlGrad_traceFree y hy)
  have hE := he.curlGrad_le y hy
  have hcurl := curl_sq_le (x.2.1 y)
  have hE0 : 0 ≤ entrySq (x.2.1 y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hss : Real.sqrt (entrySq (x.2.1 y)) ^ 2 = entrySq (x.2.1 y) := Real.sq_sqrt hE0
  have hm0 := he.meanCurlGradBound_nonneg y
  have hw0 := he.waveCurlGradBound_nonneg y
  have hℓ := he.splitLength_pos y hy
  have hT0 : 0 ≤ traceFreeConst := Real.sqrt_nonneg _
  have hTd : traceFreeConst = Real.sqrt (7 / 2) := rfl
  rw [← hTd] at hpart
  rw [hsum, hj]
  set v := x.1 y
  set G := x.2.1 y
  set P := curlGradPart (c.centreCurlGrad y) G v
  set E := entrySq G
  set s := Real.sqrt E
  set m := e.meanCurlGradBound y
  set w := e.waveCurlGradBound y
  set ℓ := e.splitLength y
  set T := traceFreeConst
  set t := 1 - 3 / (4 * α) - c.curlWeight - e.strainBound y with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hp : P ≥ -(T * ((m + w) * ‖v‖) * s) := by
    have h := hpart.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE hv0) hT0) hs0)
    exact neg_le_of_abs_le h
  have hmin : 2 * min t 0 * E ≤ t * ‖curlOf G‖ ^ 2 := by
    rcases le_total t 0 with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      have := mul_nonneg h (sq_nonneg ‖curlOf G‖)
      linarith
  have key : 2 * ‖v‖ * s ≤ ℓ * s ^ 2 + ‖v‖ ^ 2 / ℓ := by
    rw [← sub_nonneg]
    have : ℓ * s ^ 2 + ‖v‖ ^ 2 / ℓ - 2 * ‖v‖ * s = (ℓ * s - ‖v‖) ^ 2 / ℓ := by
      field_simp
      ring
    rw [this]
    positivity
  have hamgm := mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ T / 2 * w)
  rw [hss] at hamgm
  have hdiv : T / 2 * w / ℓ * ‖v‖ ^ 2 = T / 2 * w * (‖v‖ ^ 2 / ℓ) := by ring
  have htc : t * ‖curlOf G‖ ^ 2 = (1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf G‖ ^ 2
      - e.strainBound y * ‖curlOf G‖ ^ 2 := by rw [ht]; ring
  nlinarith

end Exterior

end CellCert

end Breakdown
