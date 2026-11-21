import Breakdown.FracCell.GivenChartDefs
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.GivenAuxActuatorOpen
import Breakdown.FracCell.GivenProfileSmoothModes

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open CellCert.GivenFields SteadyCert

private theorem ofComponents_finset_sum (s : Finset ℤ) (w : ℤ → Fin 3 → ℝ) :
    ofComponents (fun i => ∑ n ∈ s, w n i) = ∑ n ∈ s, ofComponents (w n) := by
  ext j
  fin_cases j <;> simp [ofComponents]

private theorem fieldOf_eq_modes (P : ChartParams) (D : FieldData) (β : ℝ) :
    fieldOf P D β = fun y => ∑ n ∈ D.modes, (1 : ℝ) • modeFieldOf P D β n y := by
  funext y
  simp only [one_smul]
  unfold fieldOf modeFieldOf
  rw [← ofComponents_finset_sum]
  congr 1
  funext i
  rw [Finset.mul_sum, Complex.re_sum]

private theorem modeFieldOf_contDiff_all {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : ContDiff ℝ 1 (modeFieldOf P D β n) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases h0 : n = 0
  · subst h0
    by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_mean P hP hD β hn
    · have hph : modePhase P 0 β = fun _ => 1 := by
        funext z
        simp [modePhase]
      refine modeFieldOf_contDiffAt_of P hP D β 0 (reducedField_mean_contDiff P hP hD β hn) y hy ?_
      rw [hph]
      exact contDiffAt_const
  · by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_wave P hP hD β n hn h0
    exact modeFieldOf_contDiffAt_axis_of P hP hD β n hn h0 y hy

theorem fieldOf_contDiff {P : CellCert.GivenFields.ChartParams} {D : CellCert.GivenFields.FieldData}
    (hP : IsChartParams P) (hD : IsFieldData P 1 D) (β : ℝ) : ContDiff ℝ 1 (fieldOf P D β) := by
  rw [fieldOf_eq_modes]
  exact ContDiff.sum fun n hn => (modeFieldOf_contDiff_all hP hD β n hn).const_smul (1 : ℝ)

theorem fieldOf_fderiv_slopeOn {P : CellCert.GivenFields.ChartParams} {D : CellCert.GivenFields.FieldData}
    (hP : IsChartParams P) (hD : IsFieldData P 1 D) (β : ℝ) :
    ∀ R : ℝ, ∃ C : NNReal, LipschitzOnWith C (fderiv ℝ (fieldOf P D β)) (Metric.closedBall 0 R) := by
  have hdiff : ∀ n ∈ D.modes, Differentiable ℝ (modeFieldOf P D β n) := fun n hn =>
    (modeFieldOf_contDiff_all hP hD β n hn).differentiable (by norm_num)
  have hloc : ∀ n ∈ D.modes, LocallyLipschitz (fderiv ℝ (modeFieldOf P D β n)) := by
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      exact modeFieldOf_fderiv_locallySlope_mean hP hD β hn
    · exact modeFieldOf_fderiv_locallySlope_wave hP hD β n hn h0
  have hmode : ∀ n ∈ D.modes, ∀ R : ℝ, ∃ C : NNReal,
      LipschitzOnWith C (fderiv ℝ (modeFieldOf P D β n)) (Metric.closedBall 0 R) := fun n hn R =>
    (hloc n hn).locallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 R)
  have hsum := slopeOn_finset_sum D.modes (fun _ => (1 : ℝ))
    (fun n => fderiv ℝ (modeFieldOf P D β n)) hmode
  have heq : fderiv ℝ (fieldOf P D β) = fun z => ∑ n ∈ D.modes, (1 : ℝ) • fderiv ℝ (modeFieldOf P D β n) z := by
    rw [fieldOf_eq_modes]
    exact fderiv_finset_sum_smul D.modes (fun _ => (1 : ℝ)) (fun n => modeFieldOf P D β n) hdiff
  rw [heq]
  exact hsum

private theorem reducedDivergence_wave_eq_zero (P : ChartParams) (hm : P.m ≠ 0) (D : FieldData) (n : ℤ)
    (h0 : n ≠ 0) (β t x : ℝ) : reducedDivergence P D n β t x = 0 := by
  have hf : (fun t' x' => reducedField P D n β t' x' 0) = fun t' x' =>
      weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x' := by
    funext t' x'
    simp [reducedField, h0]
  have hg : ∀ t' x', reducedField P D n β t' x' 1 =
      weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).polarAmp.eval true t' x' := by
    intro t' x'
    simp [reducedField, h0]
  have hk : ((n * P.m : ℤ) : ℂ) ≠ 0 := by
    have : (n * P.m : ℤ) ≠ 0 := mul_ne_zero h0 (by exact_mod_cast hm)
    exact_mod_cast this
  unfold reducedDivergence
  rw [hf]
  simp only [hg]
  simp only [reducedField, h0, if_false, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp
  rw [Complex.I_sq]
  ring

private theorem divergenceAt_sum_of {s : Finset ℤ} {f : ℤ → Space → Space} {y : Space}
    (hf : ∀ n ∈ s, DifferentiableAt ℝ (f n) y) :
    divergenceAt (fun z => ∑ n ∈ s, f n z) y = ∑ n ∈ s, divergenceAt (f n) y := by
  unfold divergenceAt
  rw [fderiv_fun_sum hf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem fieldOf_divergence_ae {P : CellCert.GivenFields.ChartParams} {D : CellCert.GivenFields.FieldData}
    (hP : IsChartParams P) (hD : IsFieldData P 1 D) (β : ℝ) :
    ∀ᵐ y ∂volume, divergenceAt (fieldOf P D β) y = 0 := by
  have hS : ∀ S : Spline, ∀ᵐ y ∂(volume : Measure Space),
      chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks :=
    fun S => (ae_generic P hP.L0_pos S.mesh.tBreaks S.mesh.xBreaks).mono
      fun y h => ⟨h.2.2.2.1, h.2.2.2.2⟩
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ n ∈ D.modes,
      ∀ S ∈ [(D.amp n).radialAmp, (D.amp n).polarAmp, (D.amp n).streamAmp, (D.amp n).swirlAmp],
        chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks := by
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [hS (D.amp n).radialAmp, hS (D.amp n).polarAmp, hS (D.amp n).streamAmp,
      hS (D.amp n).swirlAmp] with y h1 h2 h3 h4
    intro S hS'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS'
    rcases hS' with rfl | rfl | rfl | rfl <;> assumption
  filter_upwards [ae_generic P hP.L0_pos [] [], hall] with y h0 hg
  have hy1 : y 1 ≠ 0 := h0.2.1
  have hy0 : y ≠ 0 := fun h => hy1 (by simp [h])
  have hx0 : heightRatio y ≠ 0 := div_ne_zero h0.2.2.1 (norm_ne_zero_iff.2 hy0)
  have hR : ∀ n ∈ D.modes, ∀ k : Fin 3, DifferentiableAt ℝ (fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k)
      ((chartT P y, heightRatio y) : ℝ × ℝ) :=
    fun n hn k => reducedField_differentiableAt_generic P hP D n β hx0 (hg n hn) k
  have hmode : ∀ n ∈ D.modes, divergenceAt (modeFieldOf P D β n) y = 0 := by
    intro n hn
    rw [modeFieldOf_divergence_eq hP D β n hy1 (hR n hn)]
    by_cases h0' : n = 0
    · subst h0'
      have hs := hg 0 hn (D.amp 0).streamAmp (by simp)
      rw [reducedDivergence_mean_eq_zero P D β hx0 hs.1 hs.2]
      simp
    · rw [reducedDivergence_wave_eq_zero P hP.m_pos.ne' D n h0']
      simp
  have heq : fieldOf P D β = fun z => ∑ n ∈ D.modes, modeFieldOf P D β n z := by
    rw [fieldOf_eq_modes]
    simp
  rw [heq, divergenceAt_sum_of (fun n hn => modeFieldOf_differentiableAt_of hP D β n hy1 (hR n hn))]
  exact Finset.sum_eq_zero hmode

theorem fieldOf_divergence {P : CellCert.GivenFields.ChartParams} {D : CellCert.GivenFields.FieldData}
    (hP : IsChartParams P) (hD : IsFieldData P 1 D) (β : ℝ) : ∀ y, divergenceAt (fieldOf P D β) y = 0 :=
  divergenceAt_eq_zero_of_ae (fieldOf_contDiff hP hD β) (fieldOf_divergence_ae hP hD β)

theorem fieldOf_turn {P : CellCert.GivenFields.ChartParams} {D : CellCert.GivenFields.FieldData}
    (hP : IsChartParams P) (hD : IsFieldData P 1 D) (β : ℝ) :
    ∀ᵐ y ∂volume, fieldOf P D β (turnStep P.m y) = turnStep P.m (fieldOf P D β y) :=
  fieldOf_turn_ae P D β hP.m_pos.ne'

theorem fieldOf_mirror {P : CellCert.GivenFields.ChartParams} {D : CellCert.GivenFields.FieldData}
    (hP : IsChartParams P) (hD : IsFieldData P 1 D) (β : ℝ) :
    ∀ᵐ y ∂volume, fieldOf P D β (mirror y) = mirror (fieldOf P D β y) :=
  fieldOf_mirror_ae P D β

end FracInternal

end Breakdown
