import Breakdown.FracCell.VelocityTailSt
import Breakdown.FracCell.LowEntry
import Mathlib

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem lint_sq_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioo (-π) π))) :
    (∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ) ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo (-π) π)) Real.HolderConjugate.two_two
    hf.enorm (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioo, one_mul] at h
  have e2 : ∀ x : ENNReal, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [e2] at h
  have hsq : ∀ x : ENNReal, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ) ^ 2
      ≤ ((∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (ENNReal.ofReal (π - -π)) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
        rw [mul_pow, hsq, hsq, mul_comm]; congr 2; ring

theorem int_sq_le (f : ℝ → ℂ) :
    ‖∫ θ in Ioo (-π) π, f θ‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (Ioo (-π) π))
  · exact (pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2).trans (lint_sq_le hf)
  · rw [integral_non_aestronglyMeasurable hf, enorm_zero]
    simp

theorem hle (K : CellBox) (hK : IsCellBox K) :
    volume.restrict K.rect ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  refine Measure.restrict_mono_ae ?_
  have hsub : K.rect ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨le_trans hK.r_order.1 hp.1.1, trivial⟩
  refine hsub.eventuallyLE.trans ?_
  have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
  exact this.symm.le

theorem meas_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Space → E}
    (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hX.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  exact hf.integral_prod_right'

theorem gm_meas (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {G : Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable G volume) (a b : Fin 3) :
    AEStronglyMeasurable (gradMode m n G a b) (volume.restrict K.rect) := by
  have hF := meas_gen hG (gradKernel m n a b) (gradKernel_cont m n a b)
  have e : gradMode m n G a b = fun p =>
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, gradKernel m n a b θ (G (cylPoint p.1 θ p.2)) :=
    funext fun p => gradMode_eq m n G a b p
  rw [e]
  exact (hF.mono_measure (hle K hK)).const_mul _

theorem gm_sq (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {G : Space → (Space →L[ℝ] Space)}
    (hG1 : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y))) (a b : Fin 3) :
    IntegrableOn (fun p => K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2) K.rect := by
  have h2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hG1).2 ((hG2.const_mul 3).mono'
      ((hG1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact EmbedWeak.Internal.norm_sq_le (G y)
  refine ⟨(((lineWeight_cont K).comp continuous_fst).aestronglyMeasurable).mul
    ((gm_meas K hK m n hG1 a b).norm.pow 2), ?_⟩
  set g : Space → ENNReal := fun y => ‖G y‖ₑ ^ 2 with hg_def
  set C : ℝ := if K.r₁ = 0 then 1 else K.r₁⁻¹ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; split_ifs
    · norm_num
    · exact inv_nonneg.2 hK.r_order.1
  have hw : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 ∧ K.lineWeight p.1 ≤ C * p.1 := by
    intro p hp
    have h1 : K.r₁ ≤ p.1 := hp.1.1
    by_cases h : K.r₁ = 0
    · simp only [CellBox.lineWeight, hC, h, if_true]
      constructor <;> linarith
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
      simp only [CellBox.lineWeight, hC, h, if_false]
      refine ⟨zero_le_one, ?_⟩
      rw [inv_mul_eq_div, le_div_iff₀ hr]
      linarith
  set c0 : ENNReal := ‖(1 / (2 * π) : ℂ)‖ₑ ^ 2 * ENNReal.ofReal (2 * π) with hc0
  have hc0t : ENNReal.ofReal C * c0 ≠ ⊤ := by
    rw [hc0]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) ENNReal.ofReal_ne_top)
  have hpt : ∀ p ∈ K.rect, ‖K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2‖ₑ ≤
      ENNReal.ofReal C * c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
    intro p hp
    obtain ⟨hw0, hw1⟩ := hw p hp
    have hw' : ‖K.lineWeight p.1‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal p.1 := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hw0, ← ENNReal.ofReal_mul hC0]
      exact ENNReal.ofReal_le_ofReal hw1
    have hk : ∫⁻ θ in Ioo (-π) π, ‖gradKernel m n a b θ (G (cylPoint p.1 θ p.2))‖ₑ ^ 2 ≤
        ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      refine lintegral_mono fun θ => pow_le_pow_left₀ (by positivity) ?_ 2
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (gradKernel_bound m n a b θ _)
    have hm : ‖gradMode m n G a b p‖ₑ ^ 2 ≤ c0 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      rw [gradMode_eq, enorm_mul, mul_pow, hc0, mul_assoc]
      exact mul_le_mul' le_rfl ((int_sq_le _).trans (mul_le_mul' le_rfl hk))
    rw [enorm_mul, enorm_pow, enorm_norm]
    calc ‖K.lineWeight p.1‖ₑ * ‖gradMode m n G a b p‖ₑ ^ 2
        ≤ (ENNReal.ofReal C * ENNReal.ofReal p.1) * (c0 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
          mul_le_mul' hw' hm
      _ = ENNReal.ofReal C * c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by ring
  have hgm : AEMeasurable g volume := hG1.enorm.pow_const 2
  have hfin : ∫⁻ y, g y < ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hG1).1 h2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm, hg_def] using hi
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (b := ENNReal.ofReal C * c0 * ∫⁻ y, g y) ?_
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc0t) hfin)
  calc ∫⁻ p in K.rect, ‖K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2‖ₑ
      ≤ ∫⁻ p in K.rect, ENNReal.ofReal C * c0 *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
        setLIntegral_mono' (rect_meas K) hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal C * c0 *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono' (hle K hK) le_rfl
    _ = ENNReal.ofReal C * c0 * ∫⁻ y, g y := by rw [lintegral_const_mul' _ _ hc0t, hint]

end Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

namespace Breakdown.CellCert.CellAnalysis

open ModeGradSquare.Internal in
theorem modeGradSquare : ModeGradSquareStatement := by
  intro K hK m v G H hs n a b
  exact ⟨gm_meas K hK m n hs.measurable_gradient a b, gm_sq K hK m n hs.measurable_gradient hs.gradient_two a b⟩

end Breakdown.CellCert.CellAnalysis
