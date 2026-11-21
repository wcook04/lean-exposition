import Breakdown.CellReduction.AdjointStatements
import Breakdown.CellReduction.AdjointRemainderAzimuthalSliceBound
import Breakdown.CellReduction.AdjointRemainderAzimuthalWeak
import Breakdown.CellReduction.AdjointRemainderAzimuthalSmooth
import Breakdown.CellReduction.AdjointRemainderAzimuthalApprox
import Breakdown.CellReduction.AdjointRemainderAzimuthalGradientTotal
import Breakdown.CellReduction.AdjointRemainderAzimuthalPairing
import Breakdown.CellReduction.AdjointRemainderAzimuthalTime

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace Internal

open CellCert.Reduction

variable {N : ℕ}

def timeCoef (freq : Fin N → ℤ) (σ : ℝ) (p : Fin N) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * (freq p : ℂ) * (σ : ℂ) * Complex.I)

theorem componentWeight_pos (c : Fin 3) : 0 < componentWeight c := by
  unfold componentWeight
  split_ifs <;> norm_num

theorem groupSet_injOn (comp : Fin N → Fin 3) (freq order : Fin N → ℤ)
    (hinj : Function.Injective (fun p : Fin N => (comp p, freq p, order p))) (c : Fin 3) (m : ℤ) :
    Set.InjOn freq (groupSet comp order c m : Set (Fin N)) := by
  intro p hp q hq hpq
  rw [Finset.mem_coe] at hp hq
  simp only [groupSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  apply hinj
  simp only [Prod.mk.injEq]
  exact ⟨hp.1.trans hq.1.symm, hpq, hp.2.trans hq.2.symm⟩

theorem regroup (comp : Fin N → Fin 3) (order : Fin N → ℤ) (I : Fin N → ℝ≥0∞) :
    ∑ c : Fin 3, ∑ m ∈ orderSet comp order c, ENNReal.ofReal (componentWeight c / modeWeight m ^ 2) *
        ∑ p ∈ groupSet comp order c m, I p =
      ∑ p, ENNReal.ofReal (componentWeight (comp p) / modeWeight (order p) ^ 2) * I p := by
  classical
  have h1 : ∀ c, ∑ m ∈ orderSet comp order c, ENNReal.ofReal (componentWeight c / modeWeight m ^ 2) *
      ∑ p ∈ groupSet comp order c m, I p =
      ∑ p ∈ Finset.univ.filter (fun p => comp p = c),
        ENNReal.ofReal (componentWeight (comp p) / modeWeight (order p) ^ 2) * I p := by
    intro c
    rw [← Finset.sum_fiberwise_of_maps_to (g := order) (t := orderSet comp order c)
      (fun _ hp => Finset.mem_image_of_mem order hp)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [hp.1, hp.2]
  simp_rw [h1]
  exact Finset.sum_fiberwise Finset.univ comp _

theorem joint_meas_group (amp : Fin N → Space → ℂ) (comp : Fin N → Fin 3) (freq order : Fin N → ℤ)
    (hampm : ∀ p, AEStronglyMeasurable (amp p) volume) (c : Fin 3) (m : ℤ) :
    AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ ^ 2 *
      ‖groupField amp (timeCoef freq z.1) comp order c m z.2‖ ^ 2)) (volume.prod volume) := by
  have hg : AEStronglyMeasurable (fun z : ℝ × Space => groupField amp (timeCoef freq z.1) comp order c m z.2)
      (volume.prod volume) := by
    unfold groupField
    refine Finset.aestronglyMeasurable_fun_sum _ fun p _ => ?_
    have h1 : Continuous (fun z : ℝ × Space => timeCoef freq z.1 p) := by
      unfold timeCoef
      fun_prop
    exact h1.aestronglyMeasurable.mul (hampm p).comp_snd
  exact (((continuous_norm.comp continuous_snd).pow 2).aestronglyMeasurable.mul
    (hg.norm.pow 2)).aemeasurable.ennreal_ofReal

theorem sqrt_split (x a b : ℝ≥0∞) (h : x ^ 2 ≤ a * b) :
    x ≤ a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have e : x = (x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [e]
  exact ENNReal.rpow_le_rpow h (by norm_num)

theorem weight_le (c : Fin 3) (m : ℤ) :
    componentWeight c / modeWeight m ^ 2 ≤ componentWeight c / (|(m : ℝ)| + 1 / 2) ^ 2 := by
  unfold modeWeight
  exact le_rfl

theorem half_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a := by
  rw [← ENNReal.rpow_mul]
  norm_num

end Internal

open AzimuthalParts.Internal

theorem remainderAzimuthalHolds_of (hM : ModeInverseSquareWeakHolds) (hP : ModePairingHolds)
    (hT : TimeModeSumHolds) : RemainderAzimuthalHolds := by
  classical
  intro R ρ hcert v G hvm hGm hweak h6 hGfin
  obtain ⟨hρ, hRm, N, amp, comp, freq, order, hinj, hampm, hrot, hrep, hsum⟩ := hcert
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  have hfin : ∀ p, ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) < ⊤ := by
    intro p
    have h1 : ENNReal.ofReal (componentWeight (comp p) / (|(order p : ℝ)| + 1 / 2) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) ≤ ENNReal.ofReal (ρ ^ 2) :=
      (Finset.single_le_sum (f := fun p => ENNReal.ofReal (componentWeight (comp p) / (|(order p : ℝ)| + 1 / 2) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2)) (fun _ _ => zero_le) (Finset.mem_univ p)).trans hsum
    have h2 : ENNReal.ofReal (componentWeight (comp p) / (|(order p : ℝ)| + 1 / 2) ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (div_pos (componentWeight_pos _) (by positivity))).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne h2
  set F : ℝ → ℝ := fun σ => ∫ y, inner ℝ (v σ y) (R σ y) with hF
  set Ehat : ℝ → ℝ≥0∞ := fun σ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) with hEhat
  set Shat : ℝ → ℝ≥0∞ := fun σ => ∑ c : Fin 3, ∑ m ∈ orderSet comp order c,
    ENNReal.ofReal (componentWeight c / modeWeight m ^ 2) *
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖groupField amp (timeCoef freq σ) comp order c m y‖ ^ 2) with hShat
  have hvm' := hvm
  have hGm' := hGm
  rw [Measure.volume_eq_prod] at hvm' hGm'
  have hEm : AEMeasurable Ehat volume := by
    have h : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) (volume.prod volume) :=
      (continuous_squareSum.comp_aestronglyMeasurable hGm').aemeasurable.ennreal_ofReal
    exact h.lintegral_prod_right'
  have hSm : AEMeasurable Shat volume := by
    refine Finset.aemeasurable_fun_sum _ fun c _ => Finset.aemeasurable_fun_sum _ fun m _ => ?_
    exact (joint_meas_group amp comp freq order hampm c m).lintegral_prod_right'.const_mul _
  have hEint : ∫⁻ σ, Ehat σ ∂μ < ⊤ := hGfin
  have hEfin : ∀ᵐ σ ∂μ, Ehat σ < ⊤ := ae_lt_top' hEm.restrict hEint.ne
  have hgood : ∀ᵐ σ ∂μ, ENNReal.ofReal |F σ| ≤ Ehat σ ^ (1 / 2 : ℝ) * Shat σ ^ (1 / 2 : ℝ) := by
    filter_upwards [hEfin, ae_restrict_of_ae hweak, ae_restrict_of_ae h6,
      ae_restrict_of_ae hvm'.prodMk_left, ae_restrict_of_ae hGm'.prodMk_left] with σ hE hw h6σ hvσ hGσ
    refine sqrt_split _ _ _ ?_
    exact (slice_bound hM hP amp comp order (timeCoef freq σ) hampm hrot hfin (v σ) (R σ) (G σ)
      hvσ hGσ hw h6σ hE (hrep σ)).2
  have hlin : ∫⁻ σ, ENNReal.ofReal |F σ| ∂μ ≤
      (∫⁻ σ, Ehat σ ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ σ, Shat σ ∂μ) ^ (1 / 2 : ℝ) := by
    refine (lintegral_mono_ae hgood).trans ?_
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (hEm.restrict.pow_const (1 / 2 : ℝ)) (hSm.restrict.pow_const (1 / 2 : ℝ))
    simp only [half_sq] at h
    simpa using h
  have hS : ∫⁻ σ, Shat σ ∂μ ≤ ENNReal.ofReal (ρ ^ 2) := by
    rw [hShat, lintegral_finsetSum' _ fun c _ => (Finset.aemeasurable_fun_sum _ fun m _ =>
      ((joint_meas_group amp comp freq order hampm c m).lintegral_prod_right'.const_mul _).restrict)]
    refine le_trans ?_ (le_of_eq_of_le (regroup comp order _) (le_trans (Finset.sum_le_sum fun p _ =>
      mul_le_mul' (ENNReal.ofReal_le_ofReal (weight_le (comp p) (order p))) le_rfl) hsum))
    refine Finset.sum_le_sum fun c _ => ?_
    rw [lintegral_finsetSum' _ fun m _ =>
      ((joint_meas_group amp comp freq order hampm c m).lintegral_prod_right'.const_mul _).restrict]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl ?_
    exact hT amp freq (groupSet comp order c m) (groupSet_injOn comp freq order hinj c m) hampm
  have hsq : (ENNReal.ofReal (ρ ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal ρ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq hρ]
  have hP2 : (∫⁻ σ, Ehat σ ∂μ) ^ (1 / 2 : ℝ) = ENNReal.ofReal (gradientNorm G) := by
    rw [gradientNorm, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hGfin.ne]
    rfl
  have hbound : ∫⁻ σ, ENNReal.ofReal |F σ| ∂μ ≤ ENNReal.ofReal (ρ * gradientNorm G) := by
    refine hlin.trans ?_
    rw [ENNReal.ofReal_mul hρ, mul_comm (ENNReal.ofReal ρ), hP2, ← hsq]
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hS (by norm_num))
  have hRHS : 0 ≤ ρ * gradientNorm G := mul_nonneg hρ (Real.sqrt_nonneg _)
  have hRm' := hRm
  rw [Measure.volume_eq_prod] at hRm'
  have hFm : AEStronglyMeasurable F volume := by
    have h : AEStronglyMeasurable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (R z.1 z.2)) (volume.prod volume) :=
      hvm'.inner hRm'
    exact h.integral_prod_right'
  have hI : Integrable F μ := by
    refine ⟨hFm.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ρ * gradientNorm G))
    refine le_of_eq_of_le ?_ hbound
    exact lintegral_congr fun σ => by rw [Real.norm_eq_abs]
  have hslices : ∀ᵐ σ ∂μ, Integrable (fun y => inner ℝ (v σ y) (R σ y)) volume := by
    filter_upwards [hEfin, ae_restrict_of_ae hweak, ae_restrict_of_ae h6,
      ae_restrict_of_ae hvm'.prodMk_left, ae_restrict_of_ae hGm'.prodMk_left] with σ hE hw h6σ hvσ hGσ
    exact (slice_bound hM hP amp comp order (timeCoef freq σ) hampm hrot hfin (v σ) (R σ) (G σ)
      hvσ hGσ hw h6σ hE (hrep σ)).1
  refine ⟨hslices, hI, ?_⟩
  show |∫ σ in Set.Icc (0 : ℝ) 1, F σ| ≤ ρ * gradientNorm G
  have h1 : |∫ σ, F σ ∂μ| ≤ ∫ σ, |F σ| ∂μ := abs_integral_le_integral_abs
  have h2 : ENNReal.ofReal (∫ σ, |F σ| ∂μ) = ∫⁻ σ, ENNReal.ofReal |F σ| ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hI.abs (ae_of_all _ fun σ => abs_nonneg _)
  have h3 : ∫ σ, |F σ| ∂μ ≤ ρ * gradientNorm G := by
    rw [← ENNReal.ofReal_le_ofReal_iff hRHS, h2]
    exact hbound
  exact h1.trans h3

end AzimuthalParts

theorem remainderAzimuthalHolds_proof : RemainderAzimuthalHolds :=
  AzimuthalParts.remainderAzimuthalHolds_of
    (AzimuthalParts.modeInverseSquareWeak_of AzimuthalParts.smoothModeInverseSquare
      AzimuthalParts.weakClassApprox AzimuthalParts.gradientModeTotal)
    AzimuthalParts.modePairing AzimuthalParts.timeModeSum

end AdjointDefect

end Breakdown
