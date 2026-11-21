import Breakdown.FracCell.SharpYSharpSupremum
import Breakdown.FracCell.LowEntry

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpCircleSquare.Internal

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem coef_summable {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo (-π) π))) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun n : ℤ => ‖(1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * f θ‖ ^ 2) := by
  have hab : -π < π := by linarith [Real.pi_pos]
  have hf' : MemLp f 2 (volume.restrict (Ioc (-π) π)) := by
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hs := (hasSum_sq_fourierCoeffOn hab hf').summable
  have hinj : Function.Injective (fun n : ℤ => n * (m : ℤ)) := by
    intro a b h
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    exact mul_right_cancel₀ hm0 h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : ∀ n : ℤ, fourierCoeffOn hab f (n * (m : ℤ)) = (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * f θ := by
    intro n
    rw [fourierCoeffOn_eq_integral _ _ hab, intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo, Complex.real_smul]
    congr 1
    · push_cast; ring
    · congr 1
      funext θ
      rw [smul_eq_mul, fourier_coe_apply]
      congr 2
      simp only [azimuth]
      push_cast
      field_simp
      ring
  refine (hs.comp_injective hinj).congr (fun n => ?_)
  simp only [Function.comp_apply, e]

theorem slice_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Space → E} {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (hX : MemLp X q volume) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      MemLp (fun θ => X (cylPoint p.1 θ p.2)) q (volume.restrict (Ioo (-π) π)) := by
  set g : Space → ℝ≥0∞ := fun y => ‖X y‖ₑ ^ q.toReal with hg
  have hgm : AEMeasurable g volume := hX.1.enorm.pow_const _
  have hfin : ∫⁻ y, g y < ⊤ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hqt hX.2
  have hF : AEStronglyMeasurable (fun w : (ℝ × ℝ) × ℝ => X (cylArg w)) muU :=
    hX.1.comp_quasiMeasurePreserving qmp
  rw [muU_def] at hF
  have hslice := hF.prodMk_left
  have hH : AEMeasurable (fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal w.1.1 * g (cylArg w))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
      (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal p.1 * g (cylArg (p, θ)) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod _ hH]
  have hae := ae_lt_top' hH.lintegral_prod_right' (by rw [hint]; exact hfin.ne)
  filter_upwards [hslice, hae, ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p h1 h2 h3
  have hr : 0 < p.1 := h3.1
  refine ⟨h1, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  intro htop
  have h5 : ∫⁻ θ in Ioo (-π) π, g (cylArg (p, θ)) = ⊤ := htop
  rw [h5, ENNReal.mul_top (ENNReal.ofReal_pos.2 hr).ne'] at h2
  exact lt_irrefl _ h2

theorem rect_le (K : CellBox) (hK : IsCellBox K) :
    volume.restrict K.rect ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  have h0 : volume.restrict K.rect = volume.restrict (K.rect ∩ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
    refine Measure.restrict_congr_set ?_
    have hnull : (volume : Measure (ℝ × ℝ)) ({0} ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    refine (ae_eq_set).2 ⟨?_, measure_mono_null (fun p hp => absurd hp.1.1 hp.2) measure_empty⟩
    refine measure_mono_null (fun p hp => ?_) hnull
    have h1 : K.r₁ ≤ p.1 := hp.1.1.1
    have h2 : ¬ 0 < p.1 := fun h => hp.2 ⟨hp.1, h, trivial⟩
    exact ⟨le_antisymm (not_lt.1 h2) (le_trans hK.r_order.1 h1), trivial⟩
  rw [h0]
  exact Measure.restrict_mono inter_subset_right le_rfl

theorem frame_memLp {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} {Y : ℝ → E} (hY : MemLp Y 2 μ)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun w : ℝ × E => φ w.1 w.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    MemLp (fun θ => φ θ (Y θ)) 2 μ :=
  hY.of_le (hφc.comp_aestronglyMeasurable (measurable_id.aestronglyMeasurable.prodMk hY.1))
    (ae_of_all _ fun θ => hφb θ (Y θ))

theorem grad_ae (K : CellBox) (hK : IsCellBox K) {m : ℕ} (hm : 1 ≤ m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b : Fin 3, Summable (fun n : ℤ => ‖gradMode m n G a b p‖ ^ 2) := by
  have h2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hs.measurable_gradient).2 ((hs.gradient_two.const_mul 3).mono'
      ((hs.measurable_gradient.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact EmbedWeak.Internal.norm_sq_le (G y)
  filter_upwards [ae_mono (rect_le K hK) (slice_memLp two_ne_zero ENNReal.ofNat_ne_top h2)] with p hp a b
  have hf := frame_memLp hp (fun θ M => (frameMat θ M a b : ℂ))
    (Complex.continuous_ofReal.comp (frameMat_cont a b))
    (fun θ M => by rw [Complex.norm_real, Real.norm_eq_abs]; exact frameMat_bound θ M a b)
  have e : (fun n : ℤ => ‖gradMode m n G a b p‖ ^ 2) = fun n : ℤ => ‖(1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ)‖ ^ 2 := by
    funext n; rw [gradMode_eq]; rfl
  rw [e]
  exact coef_summable hf hm

theorem vel_ae (K : CellBox) (hK : IsCellBox K) {m : ℕ} (hm : 1 ≤ m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ a : Fin 3,
      Summable (fun n : ℤ => ‖modeVec m n v p.1 p.2 a‖ ^ 2) := by
  have : IsFiniteMeasure (volume.restrict (Ioo (-π) π)) := ⟨by simp⟩
  filter_upwards [ae_mono (rect_le K hK) (slice_memLp (by norm_num) ENNReal.ofNat_ne_top hs.velocity_six)]
    with p hp a
  have hp2 := hp.mono_exponent (p := 2) (by norm_num)
  have hf := frame_memLp hp2 (fun θ u => (frameVec θ u a : ℂ))
    (Complex.continuous_ofReal.comp (frameVec_cont a))
    (fun θ u => by rw [Complex.norm_real, Real.norm_eq_abs, frameVec_eq]; exact inner_unit_bound θ u a)
  have e : (fun n : ℤ => ‖modeVec m n v p.1 p.2 a‖ ^ 2) = fun n : ℤ => ‖(1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        (frameVec θ (v (cylPoint p.1 θ p.2)) a : ℂ)‖ ^ 2 := by
    funext n; rw [modeVec_eq]; rfl
  rw [e]
  exact coef_summable hf hm

end Breakdown.CellCert.CellAnalysis.SharpCircleSquare.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpCircleSquare.Internal

theorem sharpCircleSquare_holds : SharpCircleSquareStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  filter_upwards [grad_ae K hd.box hm hx.1, vel_ae K hd.box hm hx.1] with p hg hv
  have hfin : ∀ᶠ n in Filter.cofinite, n ∉ S.resolved := S.resolved.finite_toSet.eventually_cofinite_notMem
  constructor
  · have hsum : Summable (fun n : ℤ => sumSq (fun a b => gradMode c.order n x.2.1 a b p)) := by
      unfold sumSq
      exact summable_sum (fun a _ => summable_sum (fun b _ => hg a b))
    refine hsum.congr_cofinite ?_
    filter_upwards [hfin] with n hn
    have e : sharpGrad c K S x n p = fun a b => gradMode c.order n x.2.1 a b p := by
      funext a b; simp [sharpGrad, lowGrad, hn]
    rw [e]
  · have hsum : Summable (fun n : ℤ => vecSq (fun a => modeVec c.order n x.1 p.1 p.2 a)) := by
      unfold vecSq
      exact summable_sum (fun a _ => hv a)
    refine hsum.congr_cofinite ?_
    filter_upwards [hfin] with n hn
    have e : sharpVel c K S x n p = fun a => modeVec c.order n x.1 p.1 p.2 a := by
      funext a; simp [sharpVel, lowVel, hn]
    rw [e]

end Breakdown.CellCert.CellAnalysis

