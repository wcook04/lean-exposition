import Breakdown.Cert.Nodes
import Breakdown.Cert.ReadingEnergy

open scoped ContDiff ENNReal
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldNonzero

theorem isWeakGradient_of_contDiff {W : Space → Space} (hW : ContDiff ℝ 1 W) :
    IsWeakGradient W (fderiv ℝ W) := by
  have hc : Continuous (fderiv ℝ W) := hW.continuous_fderiv one_ne_zero
  refine ⟨hW.continuous.locallyIntegrable, hc.locallyIntegrable, fun φ hφ i => ?_⟩
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hφc : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  refine integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable ?_ ?_ ?_
    (fun x _ => hφd x) (fun x _ => hW.differentiable one_ne_zero x)
  · exact (hφc.smul hW.continuous).integrable_of_hasCompactSupport
      ((hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right)
  · exact (hφ.1.continuous.smul (hc.clm_apply continuous_const)).integrable_of_hasCompactSupport
      hφ.2.smul_right
  · exact (hφ.1.continuous.smul hW.continuous).integrable_of_hasCompactSupport hφ.2.smul_right

theorem periodLIntegral_matSq_eq {W : ℝ → Space → Space} (hW : ∀ σ, ContDiff ℝ 1 (W σ))
    {u : XX} {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H)
    (hz : ∀ᵐ z : ℝ × Space, W z.1 z.2 + v z.1 z.2 = 0) :
    periodLIntegral (fun σ y => matSq (fderiv ℝ (W σ) y)) =
      periodLIntegral (fun σ y => matSq (G σ y)) := by
  have hs : ∀ᵐ σ : ℝ, ∀ᵐ y : Space, W σ y + v σ y = 0 :=
    Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) hz
  have hσ : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (W σ) y)) =
      ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hs, hr.weak_gradient] with σ h0 hg
    have hv : v σ =ᵐ[volume] fun y => -W σ y := by
      filter_upwards [h0] with y hy
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact hy
    have hcol := fun i => Internal.ReadingEnergy.column_ae_of_weakGradient hg
      (isWeakGradient_of_contDiff (hW σ).neg) hv i
    refine lintegral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hcol] with y hy
    simp only [matSq, hy, fderiv_fun_neg, neg_apply, norm_neg]
  unfold periodLIntegral
  exact lintegral_congr_ae (ae_restrict_of_ae hσ)

theorem weighted_lower {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀)
    (G : GradField) (H : SecondField) :
    ENNReal.ofReal w₀ * periodLIntegral (fun σ y => matSq (G σ y)) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) := by
  obtain ⟨hw0, -, hlow, -⟩ := hw
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hf : 0 ≤ matSq (G σ y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← ENNReal.ofReal_mul hw0.le]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_of_le (sq_nonneg _)
    (mul_le_mul_of_nonneg_right (hlow y) hf))

theorem weighted_ne_top {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H)
    (hB : periodLIntegral (fun σ y => matSq (G σ y)) ≠ ⊤) :
    periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≠ ⊤ := by
  obtain ⟨C, -, hC⟩ := Internal.ReadingEnergy.weight_bound hw
  have hslice : ∀ᵐ σ : ℝ,
      ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≤
        ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
          ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hr.trace_eq] with σ h3
    have ht := Internal.ReadingEnergy.trace_integral (Hs := H σ)
      (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))) h3
    have hti := ht.1
    have hte := ht.2
    have hm : AEMeasurable (fun y => ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2)) volume :=
      hti.aemeasurable.ennreal_ofReal
    have hnn : 0 ≤ᵐ[volume] fun y => ‖secondDerivTrace (H σ y)‖ ^ 2 := ae_of_all _ fun y => sq_nonneg _
    have hT : ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2) =
        ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hti hnn).symm.trans (congrArg ENNReal.ofReal hte)
    have hC0 : 0 ≤ C := (hC 0).1.trans (hC 0).2
    calc ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y))
        ≤ ∫⁻ y, (ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2) +
            ENNReal.ofReal C * ENNReal.ofReal (matSq (G σ y))) := by
          refine lintegral_mono fun y => ?_
          have hf : 0 ≤ matSq (G σ y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
          rw [← ENNReal.ofReal_mul hC0]
          refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
          exact (add_le_add_iff_left _).2 (mul_le_mul_of_nonneg_right (hC y).2 hf)
      _ = (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2)) +
            ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (matSq (G σ y)) := lintegral_add_left' hm _
      _ = ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
            ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) :=
        congrArg₂ (· + ·) hT (lintegral_const_mul' (ENNReal.ofReal C)
          (fun y => ENNReal.ofReal (matSq (G σ y))) ENNReal.ofReal_ne_top)
  have hGm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) volume :=
    (Internal.ReadingEnergy.continuous_matSq.comp_aestronglyMeasurable
      hr.measurable_gradient).aemeasurable.ennreal_ofReal
  rw [Measure.volume_eq_prod] at hGm
  have hb : AEMeasurable (fun σ : ℝ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y)))
      ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)) :=
    hGm.lintegral_prod_right'.restrict
  have ha : ∫⁻ σ in Icc (0 : ℝ) 1,
      ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) ≠ ⊤ := by
    rw [lintegral_Icc_coe (fun t => ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2))
      (Internal.ReadingEnergy.integrable_secondSq u).aemeasurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal (Internal.ReadingEnergy.integrable_secondSq u)
        (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hle : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≤
      ∫⁻ σ in Icc (0 : ℝ) 1,
        (ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
          ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) :=
    lintegral_mono_ae (ae_restrict_of_ae hslice)
  have hsplit : ∫⁻ σ in Icc (0 : ℝ) 1,
        (ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) +
          ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) =
      (∫⁻ σ in Icc (0 : ℝ) 1,
        ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) +
        ENNReal.ofReal C * ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) :=
    (lintegral_add_right' (fun σ : ℝ =>
        ENNReal.ofReal (‖secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2))
      (hb.const_mul (ENNReal.ofReal C))).trans
      (congrArg _ (lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top))
  refine ne_top_of_le_ne_top ?_ (hle.trans_eq hsplit)
  exact ENNReal.add_ne_top.2 ⟨ha, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB⟩

theorem arith_contra {w B A E K s : ℝ} (hlow : w * B ≤ A) (he : A = E)
    (h2 : E + K ≤ (2 * s) ^ 2) (hK : 0 ≤ K) (h5 : 4 * s ^ 2 < B * w) : False := by
  nlinarith

end Internal.HeldNonzero

open Internal.HeldNonzero

theorem heldNonzeroHolds_of (h : ReadingEnergyHolds) : HeldNonzeroHolds := by
  intro k d hd p hp f κ hs v G H hr hz
  have hw : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  obtain ⟨he, -, -⟩ := h _ _ hw _ v G H hr
  have hW : ∀ σ, ContDiff ℝ 1 (d.profile p σ) := fun σ =>
    (hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).of_le
      (by norm_num)
  have h5 := hd.nontrivial p hp
  rw [periodLIntegral_matSq_eq hW hr hz] at h5
  have hq : 0 ≤ 4 * d.sizeBound ^ 2 / d.weight := by
    have := hd.weight_pos
    positivity
  have hBt : periodLIntegral (fun σ y => matSq (G σ y)) ≠ ⊤ := by
    intro hB
    rw [hB, ENNReal.toReal_top] at h5
    linarith
  have hAt := weighted_ne_top hw hr hBt
  have hlow := ENNReal.toReal_mono hAt (weighted_lower hw G H)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.weight_pos.le] at hlow
  unfold weightedEnergy at he
  have hκ : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : energyW d.weightFn (freeInv (d.period p) f) + ∑ i, κ i ^ 2 ≤ (2 * d.sizeBound) ^ 2 :=
    (Real.sqrt_le_iff.1 (show Real.sqrt (energyW d.weightFn (freeInv (d.period p) f) + ∑ i, κ i ^ 2)
      ≤ 2 * d.sizeBound from hs.size)).2
  rw [div_lt_iff₀ hd.weight_pos] at h5
  exact arith_contra hlow he h2 hκ h5

end Breakdown.Cert
