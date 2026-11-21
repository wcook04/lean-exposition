import Breakdown.Cert.Nodes
import Breakdown.Cert.SliceFields
import Breakdown.Cert.PeriodIntegral

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ReadingEnergy

open Internal.SliceFields

theorem locallyIntegrable_column {G : Space → (Space →L[ℝ] Space)} (hG : LocallyIntegrable G volume)
    (i : Fin 3) : LocallyIntegrable (fun y => G y (unitVector i)) volume := by
  intro x
  obtain ⟨U, hU, hint⟩ := hG x
  exact ⟨U, hU, (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrable_comp hint⟩

theorem column_ae_of_weakGradient {f f' : Space → Space} {G G' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f G) (h' : IsWeakGradient f' G') (hf : f =ᵐ[volume] f') (i : Fin 3) :
    (fun y => G y (unitVector i)) =ᵐ[volume] fun y => G' y (unitVector i) := by
  refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_column h.2.1 i)
    (locallyIntegrable_column h'.2.1 i) fun φ hφ hφc => ?_
  rw [h.2.2 φ ⟨hφ, hφc⟩ i, h'.2.2 φ ⟨hφ, hφc⟩ i]
  congr 1
  exact integral_congr_ae (hf.mono fun y hy => by simp only [hy])

theorem column_ae (hg : GraphClosedHolds) (q : XBar) {f : Space → Space}
    {G : Space → (Space →L[ℝ] Space)}
    (hf : f =ᵐ[volume] (velocity (gradPart q) : Space → Space)) (hG : IsWeakGradient f G) (j : Fin 3) :
    (fun y => G y (unitVector j)) =ᵐ[volume] (partialX j (gradPart q) : Space → Space) := by
  obtain ⟨G', -, hw, -, -, -, hcol, -⟩ := slice_fields (gradPart q) (secondPart q) (hg q)
  exact (column_ae_of_weakGradient hG hw hf j).trans (hcol j)

theorem matSq_ae (hg : GraphClosedHolds) (q : XBar) {f : Space → Space}
    {G : Space → (Space →L[ℝ] Space)}
    (hf : f =ᵐ[volume] (velocity (gradPart q) : Space → Space)) (hG : IsWeakGradient f G) :
    (fun y => matSq (G y)) =ᵐ[volume]
      fun y => ∑ j : Fin 3, ‖(partialX j (gradPart q) : Space → Space) y‖ ^ 2 := by
  filter_upwards [ae_all_iff.2 (column_ae hg q hf hG)] with y hy
  simp only [matSq, hy]

theorem integrable_sum_partialX (x : Freq.X) :
    Integrable (fun y => ∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2) volume :=
  integrable_finsetSum _ fun j _ => integrable_norm_sq_L2R (partialX j x)

theorem integral_sum_partialX (x : Freq.X) :
    ∫ y, ∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [integral_finsetSum _ fun j _ => integrable_norm_sq_L2R (partialX j x)]
  simp only [integral_norm_sq_L2R]
  exact sum_norm_partialX_sq x

theorem norm_toPhysH (x : HBar) : ‖toPhysH x‖ = ‖x‖ :=
  norm_toPhys_of_mem_sig (x : L2C) x.2

theorem trace_integral {Hs : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (x : HBar)
    (h : (fun y => secondDerivTrace (Hs y)) =ᵐ[volume] fun y => -(toPhysH x : Space → Space) y) :
    Integrable (fun y => ‖secondDerivTrace (Hs y)‖ ^ 2) volume ∧
      ∫ y, ‖secondDerivTrace (Hs y)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h2 : (fun y => ‖secondDerivTrace (Hs y)‖ ^ 2) =ᵐ[volume]
      fun y => ‖(toPhysH x : Space → Space) y‖ ^ 2 := by
    filter_upwards [h] with y hy
    rw [hy, norm_neg]
  refine ⟨(integrable_norm_sq_L2R (toPhysH x)).congr h2.symm, ?_⟩
  rw [integral_congr_ae h2, integral_norm_sq_L2R, norm_toPhysH]

theorem weight_bound {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) :
    ∃ C, 0 ≤ C ∧ ∀ y, 0 ≤ w y ∧ w y ≤ C := by
  obtain ⟨h0, -, hlow, C, hC⟩ := hw
  exact ⟨C, (h0.le.trans (hlow 0)).trans (hC 0), fun y => ⟨h0.le.trans (hlow y), hC y⟩⟩

theorem integrable_weighted {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {s : Space → ℝ}
    (hs : Integrable s volume) : Integrable (fun y => w y * s y) volume := by
  obtain ⟨C, -, hC⟩ := weight_bound hw
  refine hs.bdd_mul (c := C) hw.2.1.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hC y).1]
  exact (hC y).2

theorem sliceWeightedGrad_nonneg {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) (x : Freq.X) :
    0 ≤ sliceWeightedGrad w x := by
  obtain ⟨C, -, hC⟩ := weight_bound hw
  exact integral_nonneg fun y => mul_nonneg (hC y).1 (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem sliceWeightedGrad_le {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) :
    ∃ C, 0 ≤ C ∧ ∀ x : Freq.X, sliceWeightedGrad w x ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := weight_bound hw
  refine ⟨C, hC0, fun x => ?_⟩
  rw [← integral_sum_partialX x, ← integral_const_mul]
  refine integral_mono (integrable_weighted hw (integrable_sum_partialX x))
    ((integrable_sum_partialX x).const_mul C) fun y => ?_
  exact mul_le_mul_of_nonneg_right (hC y).2 (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E]
    (g : Lp (α := TimeCircle) E 2) : ‖g‖ ^ 2 = ∫ t, ‖(g : TimeCircle → E) t‖ ^ 2 := by
  have h := (Lp.memLp g).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  have hI : 0 ≤ ∫ t, ‖(g : TimeCircle → E) t‖ ^ (2 : ℝ) :=
    integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, h, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt hI]
  simp only [Real.rpow_two]

theorem gradSq_ae (u : XX) :
    ∀ᵐ t, ‖(gradCLM u : TimeCircle → HBar) t‖ ^ 2 = ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 := by
  filter_upwards [(ContinuousLinearMap.coeFn_compLpL gradPart u :
    ∀ᵐ t ∂(volume : Measure TimeCircle), (gradCLM u : TimeCircle → HBar) t = gradPart (u t))] with t ht
  exact congrArg (fun x => ‖x‖ ^ 2) ht

theorem norm_sq_gradCLM (u : XX) : ‖gradCLM u‖ ^ 2 = ∫ t, ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 :=
  (norm_sq_eq_integral (E := HBar) (gradCLM u)).trans (integral_congr_ae (gradSq_ae u))

theorem integrable_gradSq (u : XX) :
    Integrable (fun t => ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) volume :=
  ((Lp.memLp (gradCLM u)).integrable_norm_pow two_ne_zero).congr (gradSq_ae u)

theorem secondSq_ae (u : XX) :
    ∀ᵐ t, ‖(secondCLM u : TimeCircle → HBar) t‖ ^ 2 = ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 := by
  filter_upwards [(ContinuousLinearMap.coeFn_compLpL secondPart u :
    ∀ᵐ t ∂(volume : Measure TimeCircle), (secondCLM u : TimeCircle → HBar) t = secondPart (u t))] with t ht
  exact congrArg (fun x => ‖x‖ ^ 2) ht

theorem norm_sq_secondCLM (u : XX) : ‖secondCLM u‖ ^ 2 = ∫ t, ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 :=
  (norm_sq_eq_integral (E := HBar) (secondCLM u)).trans (integral_congr_ae (secondSq_ae u))

theorem integrable_secondSq (u : XX) :
    Integrable (fun t => ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2) volume :=
  ((Lp.memLp (secondCLM u)).integrable_norm_pow two_ne_zero).congr (secondSq_ae u)

theorem toReal_periodLIntegral {f : ℝ → Space → ℝ} (hper : IsTimePeriodic f)
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) {A B : TimeCircle → ℝ}
    (hA : ∀ t, 0 ≤ A t) (hB : Integrable B volume) (hAB : ∀ᵐ t, A t ≤ B t)
    (hae : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (f σ y) = ENNReal.ofReal (A σ)) :
    Integrable A volume ∧ (periodLIntegral f).toReal = ∫ t, A t := by
  obtain ⟨F, hF, hFm⟩ := aestronglyMeasurable_lift_of_periodic f hper hm
  have hΨ : AEMeasurable (fun t => ∫⁻ y, ENNReal.ofReal (F t y)) volume := by
    have h1 := hFm.aemeasurable.ennreal_ofReal
    rw [Measure.volume_eq_prod] at h1
    exact h1.lintegral_prod_right'
  have hPer : periodLIntegral f = ∫⁻ t, ∫⁻ y, ENNReal.ofReal (F t y) := by
    rw [← lintegral_Icc_coe _ hΨ]
    unfold periodLIntegral
    refine lintegral_congr fun σ => lintegral_congr fun y => ?_
    rw [hF]
  have hΨA : ∀ᵐ t : TimeCircle, ∫⁻ y, ENNReal.ofReal (F t y) = ENNReal.ofReal (A t) := by
    refine (ae_coe_iff (fun t => ∫⁻ y, ENNReal.ofReal (F t y) = ENNReal.ofReal (A t))).2 ?_
    filter_upwards [hae] with σ hσ
    simp only [hF]
    exact hσ
  have hAm : AEStronglyMeasurable A volume := by
    refine hΨ.ennreal_toReal.aestronglyMeasurable.congr ?_
    filter_upwards [hΨA] with t ht
    rw [ht, ENNReal.toReal_ofReal (hA t)]
  have hAi : Integrable A volume := by
    refine hB.mono' hAm ?_
    filter_upwards [hAB] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hA t)]
    exact ht
  refine ⟨hAi, ?_⟩
  rw [hPer, lintegral_congr_ae hΨA, ← ofReal_integral_eq_lintegral_ofReal hAi (ae_of_all _ hA),
    ENNReal.toReal_ofReal (integral_nonneg hA)]

theorem slice_energy (hg : GraphClosedHolds) {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀)
    (q : XBar) {f : Space → Space} {Gs : Space → (Space →L[ℝ] Space)}
    {Hs : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hf : f =ᵐ[volume] (velocity (gradPart q) : Space → Space)) (hG : IsWeakGradient f Gs)
    (hH : (fun y => secondDerivTrace (Hs y)) =ᵐ[volume] fun y => -(toPhysH (secondPart q) : Space → Space) y) :
    ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (Hs y)‖ ^ 2 + w y * matSq (Gs y)) =
      ENNReal.ofReal (‖secondPart q‖ ^ 2 + sliceWeightedGrad w (gradPart q)) := by
  obtain ⟨hti, hte⟩ := trace_integral _ hH
  have hwi := integrable_weighted hw (integrable_sum_partialX (gradPart q))
  have hwe : (fun y => w y * matSq (Gs y)) =ᵐ[volume] fun y => w y * ∑ j : Fin 3,
      ‖(partialX j (gradPart q) : Space → Space) y‖ ^ 2 := by
    filter_upwards [matSq_ae hg q hf hG] with y hy
    exact congrArg (fun s => w y * s) hy
  have hwi' : Integrable (fun y => w y * matSq (Gs y)) volume := hwi.congr hwe.symm
  have hnn : 0 ≤ᵐ[volume] fun y => ‖secondDerivTrace (Hs y)‖ ^ 2 + w y * matSq (Gs y) := by
    obtain ⟨C, -, hC⟩ := weight_bound hw
    exact ae_of_all _ fun y => add_nonneg (sq_nonneg _)
      (mul_nonneg (hC y).1 (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hsum : Integrable (fun y => ‖secondDerivTrace (Hs y)‖ ^ 2 + w y * matSq (Gs y)) volume :=
    hti.add hwi'
  have hI : ∫ y, (‖secondDerivTrace (Hs y)‖ ^ 2 + w y * matSq (Gs y)) =
      ‖secondPart q‖ ^ 2 + sliceWeightedGrad w (gradPart q) :=
    calc ∫ y, (‖secondDerivTrace (Hs y)‖ ^ 2 + w y * matSq (Gs y))
        = (∫ y, ‖secondDerivTrace (Hs y)‖ ^ 2) + ∫ y, w y * matSq (Gs y) := integral_add hti hwi'
      _ = ‖secondPart q‖ ^ 2 + ∫ y, w y * ∑ j : Fin 3,
          ‖(partialX j (gradPart q) : Space → Space) y‖ ^ 2 :=
        congrArg₂ (· + ·) hte (integral_congr_ae hwe)
      _ = ‖secondPart q‖ ^ 2 + sliceWeightedGrad w (gradPart q) := rfl
  exact (ofReal_integral_eq_lintegral_ofReal hsum hnn).symm.trans (congrArg ENNReal.ofReal hI)

theorem slice_matNorm (hg : GraphClosedHolds) (q : XBar) {f : Space → Space}
    {Gs : Space → (Space →L[ℝ] Space)}
    (hf : f =ᵐ[volume] (velocity (gradPart q) : Space → Space)) (hG : IsWeakGradient f Gs) :
    ∫⁻ y, ENNReal.ofReal (matSq (Gs y)) = ENNReal.ofReal (‖gradPart q‖ ^ 2) := by
  have h4 := matSq_ae hg q hf hG
  have hi : Integrable (fun y => matSq (Gs y)) volume := (integrable_sum_partialX _).congr h4.symm
  have hnn : 0 ≤ᵐ[volume] fun y => matSq (Gs y) :=
    ae_of_all _ fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have he : ∫ y, matSq (Gs y) = ‖gradPart q‖ ^ 2 :=
    (integral_congr_ae h4).trans (integral_sum_partialX _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn, he]

theorem continuous_matSq : Continuous matSq := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem continuous_secondDerivTrace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem periodic_matSq {G : GradField} (hG : IsTimePeriodic G) :
    IsTimePeriodic (fun σ y => matSq (G σ y)) := fun σ y => by simp only [hG σ y]

theorem energy_part (h : GraphClosedHolds) {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H) :
    weightedEnergy w G H = energyW w u := by
  have hGm : AEStronglyMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
    continuous_matSq.comp_aestronglyMeasurable hr.measurable_gradient
  obtain ⟨C, hC0, hC⟩ := sliceWeightedGrad_le hw
  have hwm : AEStronglyMeasurable (fun z : ℝ × Space => w z.2) volume :=
    (hw.2.1.comp measurable_snd).aestronglyMeasurable
  have hTm : AEStronglyMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (H z.1 z.2)‖ ^ 2) volume :=
    (continuous_secondDerivTrace.comp_aestronglyMeasurable hr.measurable_second).norm.pow 2
  have hBi : Integrable (fun t => ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 +
      C * ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) volume :=
    (integrable_secondSq u).add ((integrable_gradSq u).const_mul C)
  have hper : IsTimePeriodic (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) :=
    fun σ y => by simp only [hr.periodic_second σ y, hr.periodic_gradient σ y]
  have hae : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) =
      ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2 +
        sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) := by
    filter_upwards [hr.velocity_eq, hr.weak_gradient, hr.trace_eq] with σ h1 h2 h3
    exact slice_energy h hw _ h1 h2 h3
  have key := toReal_periodLIntegral
    (A := fun t => ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 +
      sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t))) hper (hTm.add (hwm.mul hGm))
    (fun t => add_nonneg (sq_nonneg _) (sliceWeightedGrad_nonneg hw _)) hBi
    (ae_of_all _ fun t => add_le_add_right (hC _) _) hae
  have hSi : Integrable (fun t => sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t))) volume :=
    (key.1.sub (integrable_secondSq u)).congr (ae_of_all _ fun t => by simp)
  exact key.2.trans ((integral_add (integrable_secondSq u) hSi).trans
    (congrArg (· + ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)))
      (norm_sq_secondCLM u).symm))

theorem matNorm_part (h : GraphClosedHolds)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H) :
    (periodLIntegral (fun σ y => matSq (G σ y))).toReal = ‖gradCLM u‖ ^ 2 := by
  have hGm : AEStronglyMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
    continuous_matSq.comp_aestronglyMeasurable hr.measurable_gradient
  have hae : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) =
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
    filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ h1 h2
    exact slice_matNorm h _ h1 h2
  have key := toReal_periodLIntegral (A := fun t => ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)
    (periodic_matSq hr.periodic_gradient) hGm
    (fun t => sq_nonneg _) (integrable_gradSq u) (ae_of_all _ fun t => le_rfl) hae
  exact key.2.trans (norm_sq_gradCLM u).symm

theorem pin_part (h : GraphClosedHolds)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H)
    (χ : ℝ → Space → (Space →L[ℝ] Space)) :
    pinValue χ G = ∫ t, pinSlice (χ (circleRep t)) (gradPart (sliceOf u t)) := by
  have hcols : ∀ᵐ σ : ℝ, ∀ j : Fin 3, (fun y => G σ y (unitVector j)) =ᵐ[volume]
      (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) := by
    filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ h1 h2
    exact column_ae h _ h1 h2
  unfold pinValue
  rw [← integral_Icc_coe]
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [hcols, Measure.ae_ne volume (1 : ℝ)] with σ h1 h2 hσ
  have hIco : σ ∈ Ico (0 : ℝ) (0 + 1) := ⟨hσ.1, by rw [zero_add]; exact lt_of_le_of_ne hσ.2 h2⟩
  have hrep : circleRep (σ : TimeCircle) = σ := by
    unfold circleRep
    rw [AddCircle.equivIco_coe_eq hIco]
  rw [hrep]
  unfold pinSlice matInner sliceOf
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 h1] with y hy
  simp only [hy]

end Internal.ReadingEnergy

open Internal.ReadingEnergy

theorem readingEnergyHolds_of (h : GraphClosedHolds) : ReadingEnergyHolds :=
  fun _ _ hw _ _ _ _ hr => ⟨energy_part h hw hr, matNorm_part h hr, fun χ _ _ _ => pin_part h hr χ⟩

end Breakdown.Cert
