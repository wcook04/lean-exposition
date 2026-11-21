import Breakdown.FracCell.CellDensityModesWeak

open MeasureTheory Real

noncomputable section

namespace Breakdown.FracInternal.CellDensityModesBound

open SteadyCert CellCert CellCert.CellAnalysis FracInternal.CellDensityModesMirror Assembly

theorem curl_le (M : Space →L[ℝ] Space) : ‖curlOf M‖ ^ 2 ≤ 2 * entrySq M := by
  simp only [vec_sq, curl_apply, entrySq_eq, Fin.sum_univ_three, permSign]
  simp
  nlinarith [sq_nonneg (entry M 2 1 + entry M 1 2), sq_nonneg (entry M 0 2 + entry M 2 0),
    sq_nonneg (entry M 1 0 + entry M 0 1), sq_nonneg (entry M 0 0), sq_nonneg (entry M 1 1), sq_nonneg (entry M 2 2)]

theorem curl_real (x : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * x l j) ^ 2 ≤ 2 * ∑ l : Fin 3, ∑ j : Fin 3, x l j ^ 2 := by
  simp only [Fin.sum_univ_three, permSign]
  simp
  nlinarith [sq_nonneg (x 2 1 + x 1 2), sq_nonneg (x 0 2 + x 2 0), sq_nonneg (x 1 0 + x 0 1),
    sq_nonneg (x 0 0), sq_nonneg (x 1 1), sq_nonneg (x 2 2)]

theorem curlGrad_le (H : Space →L[ℝ] Space →L[ℝ] Space) : curlGradSq H ≤ 2 * CellCert.fullSecondSq H := by
  unfold curlGradSq CellCert.fullSecondSq
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := curl_real (fun l j => H (unitVector a) (unitVector j) l)
  have e : ∀ j, ‖H (unitVector a) (unitVector j)‖ ^ 2 = ∑ l : Fin 3, H (unitVector a) (unitVector j) l ^ 2 :=
    fun j => vec_sq _
  simp only [e]
  rw [Finset.sum_comm] at h
  exact h

theorem entryInner_le (G A : Space →L[ℝ] Space) : |entryInner G A| ≤ entrySq G + entrySq A := by
  unfold entryInner entrySq
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h := abs_real_inner_le_norm (G (unitVector i)) (A (unitVector i))
  nlinarith [sq_nonneg (‖G (unitVector i)‖ - ‖A (unitVector i)‖), norm_nonneg (G (unitVector i)),
    norm_nonneg (A (unitVector i))]

theorem cont_curl : Continuous (fun M : Space →L[ℝ] Space => ‖curlOf M‖ ^ 2) := by
  unfold curlOf entry; fun_prop

theorem cont_curlGrad : Continuous (fun H : Space →L[ℝ] Space →L[ℝ] Space => curlGradSq H) := by
  unfold curlGradSq; fun_prop

theorem cont_entrySq : Continuous (fun M : Space →L[ℝ] Space => entrySq M) := by
  unfold entrySq; fun_prop



theorem nonneg_curlGrad (H : Space →L[ℝ] Space →L[ℝ] Space) : 0 ≤ curlGradSq H :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nonneg_entrySq (M : Space →L[ℝ] Space) : 0 ≤ entrySq M :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pair_integrable {G A : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hA : AEStronglyMeasurable A volume) (hGi : Integrable (fun y => entrySq (G y)))
    (hAi : Integrable (fun y => entrySq (A y))) : Integrable (fun y => entryInner (G y) (A y)) := by
  have hm : AEStronglyMeasurable (fun y => entryInner (G y) (A y)) volume := by
    unfold entryInner
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (hG.apply_continuousLinearMap (unitVector i)).inner (hA.apply_continuousLinearMap (unitVector i))
  refine (hGi.add hAi).mono' hm (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact entryInner_le (G y) (A y)

end Breakdown.FracInternal.CellDensityModesBound

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly FracInternal.CellDensityModesBound

def JFormIntegrableStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox), IsCellBox K → ∀ x : FieldTuple k, IsAdmissible c x →
      IntegrableOn (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y)) K.solid

theorem densityIntegrable_of (hj : JFormIntegrableStatement) : DensityIntegrableStatement := by
  intro α hα₁ hα₂ k N c hc K hK _ _ _ x hx
  have hs := hx.1
  have hE : Integrable (fun y => entrySq (x.2.1 y)) := hs.gradient_two
  have hF : Integrable (fun y => CellCert.fullSecondSq (x.2.2.1 y)) := hs.second_two
  have hC : Integrable (fun y => curlGradSq (x.2.2.1 y)) := by
    refine (hF.const_mul 2).mono' (cont_curlGrad.comp_aestronglyMeasurable hs.measurable_second)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg_curlGrad _)]
    exact curlGrad_le _
  have hV : Integrable (fun y => ‖curlOf (x.2.1 y)‖ ^ 2) := by
    refine (hE.const_mul 2).mono' (cont_curl.comp_aestronglyMeasurable hs.measurable_gradient)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact curl_le _
  have hW : Integrable (fun y => (c.curlWeight - c.coercivity * c.weight y) * entrySq (x.2.1 y)) := by
    refine hE.bdd_mul (c := |c.curlWeight| + |c.coercivity| * (|c.weightMin| + |c.weightMax|))
      ((measurable_const.sub (measurable_const.mul hc.base.weight_measurable)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have h1 := hc.base.weight_lower y
    have h2 := hc.base.weight_upper y
    have h3 : |c.weight y| ≤ |c.weightMin| + |c.weightMax| := by
      rw [abs_le]; constructor <;> cases abs_cases c.weightMin <;> cases abs_cases c.weightMax <;> linarith
    rw [Real.norm_eq_abs]
    calc |c.curlWeight - c.coercivity * c.weight y| ≤ |c.curlWeight| + |c.coercivity * c.weight y| := abs_sub _ _
      _ ≤ _ := by rw [abs_mul]; gcongr
  have hAct : Integrable (fun y => ∑ i, x.2.2.2.1 i * entryInner (x.2.1 y) (c.modelActuatorGrad i y)) :=
    integrable_finsetSum _ fun i _ => (pair_integrable hs.measurable_gradient (hc.modelActuatorGrad_data i).1
      hE (hc.modelActuatorGrad_data i).2.1).const_mul _
  refine ⟨?_, fun i => (pair_integrable hs.measurable_gradient (hc.modelPin_data i).1 hE
    (hc.modelPin_data i).2.1).integrableOn⟩
  have hJ := hj α hα₁ hα₂ c hc K hK x hx
  unfold CellSplit.localDensity
  exact (((((hF.const_mul _).add (hC.const_mul _)).add ((hV.const_mul _).add hW)).integrableOn).add hJ).add
    hAct.integrableOn

end Breakdown.CellCert.CellAnalysis
