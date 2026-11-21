import Breakdown.FracCert.HeldStateLimitAParts
import Breakdown.FracCert.HeldStateLimitAWeak
import Breakdown.FracCert.HeldLimit
import Breakdown.FracCert.ActiveEnclosure
import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCert.InverseSquare
import Breakdown.FracCert.QuadraticSquare

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

def CrossUniformBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ B : ℝ, ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ u G H, IsSecondOrderField d.order u G H → d.energy G H ≤ B →
      MemLp (fun y => d.gradProfile p y (u y) + G y (d.profile p y) + G y (u y)) 2 volume ∧
      ∫ y, ‖d.gradProfile p y (u y) + G y (d.profile p y) + G y (u y)‖ ^ 2 ≤ C

def CrossTestLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Tendsto p atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u₀ : Space → Space)
        (G₀ : Space → (Space →L[ℝ] Space)) (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (B : ℝ),
        (∀ n, IsSecondOrderField d.order (u n) (G n) (H n)) → IsSecondOrderField d.order u₀ G₀ H₀ →
        (∀ n, d.energy (G n) (H n) ≤ B) →
        (∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
          Integrable (fun y => entrySq (E y)) →
          Tendsto (fun n => ∫ y, entryInner (G n y) (E y)) atTop (nhds (∫ y, entryInner (G₀ y) (E y)))) →
        (∀ r : ℝ, Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖u n y - u₀ y‖ ^ 2) atTop (nhds 0)) →
        ∀ ψ : Space → Space, IsTestVectorField ψ →
          Tendsto (fun n => ∫ y, inner ℝ
            (d.gradProfile (p n) y (u n y) + G n y (d.profile (p n) y) + G n y (u n y)) (ψ y))
            atTop
            (nhds (∫ y, inner ℝ (d.gradProfile q y (u₀ y) + G₀ y (d.profile q y) + G₀ y (u₀ y)) (ψ y)))

theorem crossPairingLimit_of (h1 : CrossUniformBoundStatement) (h2 : CrossTestLimitStatement) :
    CrossPairingLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H u₀ G₀ H₀ B hs hs₀ hE hGw hloc ζ hζ
  obtain ⟨C, hC⟩ := h1 α hα1 hα2 d hd (max B (d.energy G₀ H₀))
  have hn := fun n => hC (p n) (hp n) (u n) (G n) (H n) (hs n) ((hE n).trans (le_max_left _ _))
  have h₀ := hC q hq u₀ G₀ H₀ hs₀ (le_max_right _ _)
  exact WeakPairingInternal.tendsto_pair_of_tests (fun n => (hn n).1) (fun n => (hn n).2) h₀.1
    (fun ψ hψ => h2 α hα1 hα2 d hd p q hp hq hpq u G H u₀ G₀ H₀ B hs hs₀ hE hGw hloc ψ hψ) hζ.1

private theorem decay_sq_le {y : Space} (hy : y ≠ 0) : ((1 + ‖y‖)⁻¹) ^ 4 ≤ (‖y‖ ^ 2)⁻¹ := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [inv_pow]
  refine (inv_le_inv₀ (by positivity) (by positivity)).2 ?_
  nlinarith [sq_nonneg ‖y‖, mul_pos hr hr]

private theorem sum3_sq_le (a b c : Space) : ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := (norm_add_le _ _).trans (by linarith [norm_add_le a b])
  have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

theorem crossUniformBound : CrossUniformBoundStatement := by
  intro α hα1 hα2 k N d hd B
  obtain ⟨C, hC⟩ := ActiveEnclosureInternal.profile_bounds_of hd
  refine ⟨3 * ((4 * C ^ 2 + |C| ^ 2) * (d.weightMin⁻¹ * max B 0) + d.productConst ^ 2 * (max B 0) ^ 2),
    fun p hp u G H hs hE => ?_⟩
  have hW : Continuous (d.profile p) := (hd.profile_smooth p hp).continuous
  have hDW : Continuous (d.gradProfile p) := (hd.profile_smooth p hp).continuous_fderiv one_ne_zero
  have hu6 : Integrable (fun y => ‖u y‖ ^ 6) volume :=
    hs.velocity_six.integrable_norm_pow (p := 6) (by norm_num)
  have ma : MemLp (fun y => d.gradProfile p y (u y)) 2 volume :=
    ActiveEnclosureInternal.decay_apply_memLp hDW (fun y => (hC p hp y).2) hs.measurable_velocity hu6
  have mb : MemLp (fun y => G y (d.profile p y)) 2 volume :=
    ActiveEnclosureInternal.bounded_apply_memLp hs.measurable_gradient hs.gradient_two hW
      (ActiveEnclosureInternal.profile_le (fun y => (hC p hp y).1))
  have mc : MemLp (fun y => G y (u y)) 2 volume := quadraticSquareIntegrable d.order u G H hs
  refine ⟨(ma.add mb).add mc, ?_⟩
  have hEn : 0 ≤ d.energy G H := HeldLimitInternal.energy_nonneg d hd G H
  have hEB : d.energy G H ≤ max B 0 := hE.trans (le_max_left _ _)
  have hw0 : 0 ≤ d.weightMin⁻¹ := inv_nonneg.2 hd.weightMin_pos.le
  have hGE : ∫ y, entrySq (G y) ≤ d.weightMin⁻¹ * max B 0 :=
    (LinearStateClosedInternal.entry_le_energy hd.weightMin_pos hd.weight_measurable hd.weight_lower
      hd.weight_upper hs.gradient_two (L := H)).trans (mul_le_mul_of_nonneg_left hEB hw0)
  have ia := ma.integrable_norm_pow (p := 2) (by norm_num)
  have ib := mb.integrable_norm_pow (p := 2) (by norm_num)
  have ic := mc.integrable_norm_pow (p := 2) (by norm_num)
  have hia : ∫ y, ‖d.gradProfile p y (u y)‖ ^ 2 ≤ 4 * C ^ 2 * (d.weightMin⁻¹ * max B 0) := by
    obtain ⟨hI, hIb⟩ := inverseSquareBound u G hs.measurable_velocity hs.velocity_six hs.gradient_two
      hs.weak_gradient
    have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
      have : (volume : Measure Space) {0} = 0 := measure_singleton 0
      filter_upwards [compl_mem_ae_iff.2 this] with y hy
      simpa using hy
    calc ∫ y, ‖d.gradProfile p y (u y)‖ ^ 2 ≤ ∫ y, C ^ 2 * (‖u y‖ ^ 2 / ‖y‖ ^ 2) := by
          refine integral_mono_ae ia (hI.const_mul _) ?_
          filter_upwards [hne] with y hy
          have h1 : ‖d.gradProfile p y (u y)‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖u y‖ :=
            (d.gradProfile p y).le_opNorm (u y) |>.trans
              (mul_le_mul_of_nonneg_right (hC p hp y).2 (norm_nonneg _))
          have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          have h3 := decay_sq_le hy
          have h4 : (C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖u y‖) ^ 2 = C ^ 2 * (((1 + ‖y‖)⁻¹) ^ 4 * ‖u y‖ ^ 2) := by ring
          rw [h4] at h2
          refine h2.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg C))
          rw [div_eq_mul_inv, mul_comm]
          exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = C ^ 2 * ∫ y, ‖u y‖ ^ 2 / ‖y‖ ^ 2 := integral_const_mul _ _
      _ ≤ C ^ 2 * (4 * ∫ y, entrySq (G y)) := mul_le_mul_of_nonneg_left hIb (sq_nonneg _)
      _ ≤ 4 * C ^ 2 * (d.weightMin⁻¹ * max B 0) := by nlinarith [sq_nonneg C]
  have hib : ∫ y, ‖G y (d.profile p y)‖ ^ 2 ≤ |C| ^ 2 * (d.weightMin⁻¹ * max B 0) := by
    calc ∫ y, ‖G y (d.profile p y)‖ ^ 2 ≤ ∫ y, |C| ^ 2 * entrySq (G y) := by
          refine integral_mono ib (hs.gradient_two.const_mul _) fun y => ?_
          have h1 := LinearStateClosedInternal.clm_sq_le (G y) (d.profile p y)
          have h2 : ‖d.profile p y‖ ^ 2 ≤ |C| ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (ActiveEnclosureInternal.profile_le (fun y => (hC p hp y).1) y) 2
          have h3 : 0 ≤ entrySq (G y) := Finset.sum_nonneg fun i _ => sq_nonneg _
          nlinarith
      _ = |C| ^ 2 * ∫ y, entrySq (G y) := integral_const_mul _ _
      _ ≤ |C| ^ 2 * (d.weightMin⁻¹ * max B 0) := mul_le_mul_of_nonneg_left hGE (sq_nonneg _)
  have hic : ∫ y, ‖G y (u y)‖ ^ 2 ≤ d.productConst ^ 2 * (max B 0) ^ 2 := by
    have hsym : symProduct u G u G = fun y => G y (u y) := by
      funext y
      simp only [symProduct]
      rw [← two_smul ℝ (G y (u y)), smul_smul]
      norm_num
    have hb := hd.productConst_bound u G H hs u G H hs
    rw [hsym, mul_assoc, Real.mul_self_sqrt hEn] at hb
    have h0 : 0 ≤ ∫ y, ‖G y (u y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
    have e : l2Norm (fun y => G y (u y)) ^ 2 = ∫ y, ‖G y (u y)‖ ^ 2 := Real.sq_sqrt h0
    have hL := hd.productConst_nonneg
    have h1 : l2Norm (fun y => G y (u y)) ≤ d.productConst * max B 0 :=
      hb.trans (mul_le_mul_of_nonneg_left hEB hL)
    have h2 : 0 ≤ l2Norm (fun y => G y (u y)) := Real.sqrt_nonneg _
    rw [← e]
    nlinarith
  calc ∫ y, ‖d.gradProfile p y (u y) + G y (d.profile p y) + G y (u y)‖ ^ 2
      ≤ ∫ y, 3 * (‖d.gradProfile p y (u y)‖ ^ 2 + ‖G y (d.profile p y)‖ ^ 2 + ‖G y (u y)‖ ^ 2) :=
        integral_mono (((ma.add mb).add mc).integrable_norm_pow (p := 2) (by norm_num))
          (((ia.add ib).add ic).const_mul 3) fun y => sum3_sq_le _ _ _
    _ = 3 * ((∫ y, ‖d.gradProfile p y (u y)‖ ^ 2) + (∫ y, ‖G y (d.profile p y)‖ ^ 2)
          + ∫ y, ‖G y (u y)‖ ^ 2) := by
        have iab : Integrable (fun y => ‖d.gradProfile p y (u y)‖ ^ 2 + ‖G y (d.profile p y)‖ ^ 2) volume :=
          ia.add ib
        rw [integral_const_mul, integral_add iab ic, integral_add ia ib]
    _ ≤ _ := by nlinarith

end SteadyCert

end Breakdown
