import Breakdown.CertCell.AssemblyStatements
import Breakdown.Cert.CoercivePerturbationFactsProof

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCalculus

namespace Internal.RemainderRegular

theorem abs_alternatingSymbol_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem norm_combo_le (c : Fin 3 → ℝ) (M : ℝ) (h : ∀ i, |c i| ≤ M) :
    ‖∑ i : Fin 3, c i • unitVector i‖ ≤ 3 * M := by
  calc ‖∑ i : Fin 3, c i • unitVector i‖ ≤ ∑ i : Fin 3, ‖c i • unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs, norm_unitVector, mul_one]
        exact h i
    _ = 3 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

theorem abs_symbol_sum_le (i : Fin 3) (c : Fin 3 → Fin 3 → ℝ) (M : ℝ) (h : ∀ j l, |c j l| ≤ M) :
    |∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * c j l| ≤ 9 * M := by
  calc |∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * c j l|
      ≤ ∑ j : Fin 3, |∑ l : Fin 3, alternatingSymbol i j l * c j l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, |alternatingSymbol i j l * c j l| :=
        Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, M := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        calc |alternatingSymbol i j l| * |c j l| ≤ 1 * M :=
              mul_le_mul (abs_alternatingSymbol_le i j l) (h j l) (abs_nonneg _) zero_le_one
          _ = M := one_mul _
    _ = 9 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem norm_crossVec_le (u w : Space) : ‖crossVec u w‖ ≤ 27 * (‖u‖ * ‖w‖) := by
  have hc : ∀ j l : Fin 3, |u j * w l| ≤ ‖u‖ * ‖w‖ := fun j l => by
    rw [abs_mul]
    exact mul_le_mul ((Real.norm_eq_abs _).symm.trans_le (PiLp.norm_apply_le u j))
      ((Real.norm_eq_abs _).symm.trans_le (PiLp.norm_apply_le w l)) (abs_nonneg _) (norm_nonneg _)
  have h := norm_combo_le _ _ fun i => abs_symbol_sum_le i (fun j l => u j * w l) _ hc
  unfold crossVec
  simp_rw [mul_assoc]
  refine h.trans (le_of_eq ?_)
  ring

theorem norm_curlVec_le (A : Space →L[ℝ] Space) : ‖curlVec A‖ ≤ 27 * ‖A‖ := by
  have hc : ∀ j l : Fin 3, |A (unitVector j) l| ≤ ‖A‖ := fun j l => by
    refine (Real.norm_eq_abs _).symm.trans_le ((PiLp.norm_apply_le _ l).trans ?_)
    refine (A.le_opNorm _).trans (le_of_eq ?_)
    rw [norm_unitVector, mul_one]
  have h := norm_combo_le _ _ fun i => abs_symbol_sum_le i (fun j l => A (unitVector j) l) _ hc
  unfold curlVec
  refine h.trans (le_of_eq ?_)
  ring

theorem continuous_crossVec : Continuous (fun p : Space × Space => crossVec p.1 p.2) := by
  unfold crossVec
  fun_prop

theorem continuous_curlVec : Continuous (fun A : Space →L[ℝ] Space => curlVec A) := by
  unfold curlVec
  fun_prop

theorem continuous_secondDerivTrace : Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace A) := by
  unfold secondDerivTrace
  fun_prop

theorem fderiv_slice_eq {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (σ : ℝ) (y : Space) :
    fderiv ℝ (W σ) y = (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (σ, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => W z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (σ, y)) (σ, y) :=
    ((hW.differentiable one_ne_zero) (σ, y)).hasFDerivAt
  exact (h1.comp y (hasFDerivAt_prodMk_right σ y)).fderiv

theorem continuous_slice_fderiv {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) =
      fun z => (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    funext fun z => fderiv_slice_eq hW z.1 z.2
  rw [e]
  exact (hW.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem lintegral_slab (f : ℝ × Space → ℝ≥0∞) (hf : AEMeasurable f volume) (R : ℝ) :
    ∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, f z =
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, f (σ, y) := by
  rw [Measure.volume_eq_prod]
  exact setLIntegral_prod f (by rw [← Measure.volume_eq_prod]; exact hf.restrict)

theorem memLp_of_slab {E : Type*} [NormedAddCommGroup E] {f : ℝ × Space → E}
    (hm : AEStronglyMeasurable f volume) (R : ℝ)
    (h : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖f (σ, y)‖ ^ 2) < ⊤) :
    MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) := by
  have hmr : AEStronglyMeasurable f
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) := hm.restrict
  refine (memLp_two_iff_integrable_sq_norm hmr).2 ⟨hmr.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    show (0 : ℝ) ≤ ‖f z‖ ^ 2 by positivity)]
  rw [lintegral_slab (fun z => ENNReal.ofReal (‖f z‖ ^ 2)) (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal R]
  exact h

theorem slab_of_memLp {E : Type*} [NormedAddCommGroup E] {f : ℝ × Space → E}
    (hm : AEStronglyMeasurable f volume) (R : ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R))) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖f (σ, y)‖ ^ 2) < ⊤ := by
  have hI := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have h := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    show (0 : ℝ) ≤ ‖f z‖ ^ 2 by positivity)).1 hI.2
  rwa [lintegral_slab (fun z => ENNReal.ofReal (‖f z‖ ^ 2))
    (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal R] at h

theorem slab_le_period (h : ℝ → Space → ℝ) (R : ℝ) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (h σ y) ≤
      periodLIntegral h := by
  unfold periodLIntegral
  exact lintegral_mono fun σ => setLIntegral_le_lintegral _ _

theorem remainder_regular_of {k : ℕ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {b : Fin k → ℝ → Space → Space}
    (hbm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => b i z.1 z.2) volume)
    (hbp : ∀ i, IsTimePeriodic (b i)) (hb2 : ∀ i, periodLIntegral (fun σ y => ‖b i σ y‖ ^ 2) < ⊤)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (κ : Fin k → ℝ) (F : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    AEStronglyMeasurable (fun z : ℝ × Space => strongRemainder W b κ v G H g F z.1 z.2) volume ∧
      IsTimePeriodic (strongRemainder W b κ v G H g F) ∧
      HasLocalSquare (strongRemainder W b κ v G H g F) := by
  have mH : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have cDW := continuous_slice_fderiv hW.smooth
  have mG1 := continuous_curlVec.comp_aestronglyMeasurable hv.measurable_gradient
  have mP1 := mG1.prodMk cW.aestronglyMeasurable
  have mC1' := continuous_crossVec.comp_aestronglyMeasurable mP1
  have mC1 : AEStronglyMeasurable (fun z : ℝ × Space => crossVec (curlVec (G z.1 z.2)) (W z.1 z.2)) volume :=
    mC1'
  have mG2 := (continuous_curlVec.comp cDW).aestronglyMeasurable (μ := volume)
  have mP2 := mG2.prodMk hv.measurable_velocity
  have mC2' := continuous_crossVec.comp_aestronglyMeasurable mP2
  have mC2 : AEStronglyMeasurable (fun z : ℝ × Space => crossVec (vorticityOf W z.1 z.2) (v z.1 z.2)) volume :=
    mC2'
  have mB : AEStronglyMeasurable (fun z : ℝ × Space => ∑ i, κ i • b i z.1 z.2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hbm i).const_smul (κ i)
  have eR : (fun z : ℝ × Space => strongRemainder W b κ v G H g F z.1 z.2) =
      (fun z : ℝ × Space => F z.1 z.2) - (((fun z : ℝ × Space => g z.1 z.2) -
        (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) +
        ((fun z : ℝ × Space => crossVec (curlVec (G z.1 z.2)) (W z.1 z.2)) +
          (fun z : ℝ × Space => crossVec (vorticityOf W z.1 z.2) (v z.1 z.2)))) +
        (fun z : ℝ × Space => ∑ i, κ i • b i z.1 z.2)) := rfl
  have mR : AEStronglyMeasurable (fun z : ℝ × Space => strongRemainder W b κ v G H g F z.1 z.2) volume := by
    rw [eR]
    exact hFm.sub (((hv.measurable_derivative.sub mH).add (mC1.add mC2)).add mB)
  refine ⟨mR, ?_, ?_⟩
  · intro σ y
    have hWσ : W (σ + 1) = W σ := funext (hW.periodic σ)
    have hb' : ∀ i, b i (σ + 1) y = b i σ y := fun i => hbp i σ y
    simp only [strongRemainder, couplingField, vorticityOf, hFp σ y, hv.periodic_derivative σ y,
      hv.periodic_secondDeriv σ y, hv.periodic_gradient σ y, hv.periodic_velocity σ y, hWσ, hb']
  · intro R
    have hB0 : 0 ≤ B := by
      have h := (hW.decay 0 0).1
      rw [norm_zero, add_zero, div_one] at h
      exact (norm_nonneg _).trans h
    have hWb : ∀ σ y, ‖W σ y‖ ≤ B := fun σ y =>
      (hW.decay σ y).1.trans (div_le_self hB0 (by linarith [norm_nonneg y]))
    have hDWb : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ B := fun σ y =>
      (hW.decay σ y).2.1.trans (div_le_self hB0 (one_le_pow₀ (by linarith [norm_nonneg y])))
    have LF := memLp_of_slab hFm R (lt_of_le_of_lt (slab_le_period (fun σ y => ‖F σ y‖ ^ 2) R) hF2)
    have Lg := memLp_of_slab hv.measurable_derivative R
      (lt_of_le_of_lt (slab_le_period (fun σ y => ‖g σ y‖ ^ 2) R) hv.derivative_finite)
    have LH := memLp_of_slab mH R
      (lt_of_le_of_lt (slab_le_period (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) R) hv.sumSecondPartials_finite)
    have LB : MemLp (fun z : ℝ × Space => ∑ i, κ i • b i z.1 z.2) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) :=
      memLp_finsetSum _ fun i _ => (memLp_of_slab (hbm i) R
        (lt_of_le_of_lt (slab_le_period (fun σ y => ‖b i σ y‖ ^ 2) R) (hb2 i))).const_smul (κ i)
    have Lv := memLp_of_slab hv.measurable_velocity R
      (Coercive.Internal.PerturbationFacts.velocity_localSquare hv R)
    have LG : MemLp (fun z : ℝ × Space => G z.1 z.2) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) := by
      refine memLp_of_slab hv.measurable_gradient R (lt_of_le_of_lt ?_
        (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 3)) hv.gradient_finite))
      calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
            ENNReal.ofReal (‖G σ y‖ ^ 2)
          ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
            ENNReal.ofReal 3 * ENNReal.ofReal (matSq (G σ y)) :=
            lintegral_mono fun σ => lintegral_mono fun y => by
              rw [← ENNReal.ofReal_mul (by norm_num)]
              exact ENNReal.ofReal_le_ofReal
                (Coercive.Internal.PerturbationFacts.sq_norm_le_three_matNorm _)
        _ = ENNReal.ofReal 3 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
            ENNReal.ofReal (matSq (G σ y)) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun σ => ?_
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal 3 * periodLIntegral (fun σ y => matSq (G σ y)) :=
            by gcongr; exact slab_le_period _ R
    have LC1 : MemLp (fun z : ℝ × Space => crossVec (curlVec (G z.1 z.2)) (W z.1 z.2)) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) := by
      refine LG.of_le_mul (c := 27 * 27 * B) mC1.restrict (Filter.Eventually.of_forall fun z => ?_)
      calc ‖crossVec (curlVec (G z.1 z.2)) (W z.1 z.2)‖
          ≤ 27 * (‖curlVec (G z.1 z.2)‖ * ‖W z.1 z.2‖) := norm_crossVec_le _ _
        _ ≤ 27 * ((27 * ‖G z.1 z.2‖) * B) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (norm_curlVec_le _) (hWb _ _) (norm_nonneg _)
              (by positivity)) (by norm_num)
        _ = 27 * 27 * B * ‖G z.1 z.2‖ := by ring
    have LC2 : MemLp (fun z : ℝ × Space => crossVec (vorticityOf W z.1 z.2) (v z.1 z.2)) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) := by
      refine Lv.of_le_mul (c := 27 * 27 * B) mC2.restrict (Filter.Eventually.of_forall fun z => ?_)
      calc ‖crossVec (vorticityOf W z.1 z.2) (v z.1 z.2)‖
          ≤ 27 * (‖curlVec (fderiv ℝ (W z.1) z.2)‖ * ‖v z.1 z.2‖) := norm_crossVec_le _ _
        _ ≤ 27 * ((27 * B) * ‖v z.1 z.2‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((norm_curlVec_le _).trans
              (mul_le_mul_of_nonneg_left (hDWb _ _) (by norm_num))) (norm_nonneg _)) (by norm_num)
        _ = 27 * 27 * B * ‖v z.1 z.2‖ := by ring
    have LR : MemLp (fun z : ℝ × Space => strongRemainder W b κ v G H g F z.1 z.2) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R)) :=
      by rw [eR]; exact LF.sub (((Lg.sub LH).add (LC1.add LC2)).add LB)
    exact slab_of_memLp mR R LR

end Internal.RemainderRegular

theorem remainderRegular_holds : RemainderRegularHolds := by
  intro k C nE nM D hP q _ v G H g hv κ F hFm hFp hF2
  obtain ⟨B, hWs⟩ := hP.model_state
  choose S hS using hP.actuators
  exact Internal.RemainderRegular.remainder_regular_of hWs (fun i => (hS i).measurable)
    (fun i => (hS i).periodic) (fun i => (hS i).square_finite) hv κ F hFm hFp hF2

end Breakdown.CertCell.Assembly
