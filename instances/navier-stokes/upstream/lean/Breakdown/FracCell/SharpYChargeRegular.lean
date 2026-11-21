import Breakdown.FracCell.SharpYChargeSt
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModeVelSquare
import Mathlib

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpYChargeRegular.Internal

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

def coefAt (m : ℕ) (n : ℤ) (f : ℝ → ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (f θ : ℂ)

theorem neg_pi_lt : -π < π := by linarith [Real.pi_pos]

theorem coefAt_eq (m : ℕ) (n : ℤ) (f : ℝ → ℝ) :
    coefAt m n f = fourierCoeffOn neg_pi_lt (fun θ => (f θ : ℂ)) (n * (m : ℤ)) := by
  rw [fourierCoeffOn_eq_integral _ _ neg_pi_lt, coefAt, Complex.real_smul,
    intervalIntegral.integral_of_le neg_pi_lt.le, integral_Ioc_eq_integral_Ioo]
  congr 1
  · push_cast; ring
  · refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only [smul_eq_mul]
    rw [fourier_coe_apply]
    congr 2
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [azimuth]
    push_cast
    field_simp
    ring

theorem coef_sq_sum (m : ℕ) (hm : 0 < m) (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) :
    Summable (fun n : ℤ => ‖coefAt m n f‖ ^ 2) ∧
      ∑' n : ℤ, ‖coefAt m n f‖ ^ 2 ≤ (2 * π)⁻¹ * ∫ θ in Ioc (-π) π, f θ ^ 2 := by
  have H2 := hasSum_sq_fourierCoeffOn neg_pi_lt hf.ofReal
  replace H2 : HasSum (fun i => ‖fourierCoeffOn neg_pi_lt (fun x => ((f x : ℝ) : ℂ)) i‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in Ioc (-π) π, f θ ^ 2) := by
    convert H2 using 1
    · funext i
      rfl
    · rw [intervalIntegral.integral_of_le neg_pi_lt.le, smul_eq_mul]
      congr 1
      · ring
      · refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
        simp [sq_abs]
  have hinj : Function.Injective (fun n : ℤ => n * (m : ℤ)) := by
    intro a b hab
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    exact mul_right_cancel₀ hm' hab
  have e4 : (fun n : ℤ => ‖coefAt m n f‖ ^ 2) =
      (fun k => ‖fourierCoeffOn neg_pi_lt (fun θ => (f θ : ℂ)) k‖ ^ 2) ∘ (fun n : ℤ => n * (m : ℤ)) := by
    funext n; simp only [Function.comp_apply, coefAt_eq]
  rw [e4]
  refine ⟨H2.summable.comp_injective hinj, ?_⟩
  rw [← H2.tsum_eq]
  exact tsum_comp_le_tsum_of_inj H2.summable (fun k => by positivity) hinj


theorem slice_meas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Space → E}
    (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℝ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => φ θ (X (cylPoint p.1 θ p.2))) (volume.restrict (Ioo (-π) π)) := by
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hX.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  exact hf.prodMk_left

theorem slice_bound (m : ℕ) (hm : 0 < m) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo (-π) π))) :
    ∑' n : ℤ, ENNReal.ofReal (‖coefAt m n f‖ ^ 2) ≤
      ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
  by_cases hL : ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 = ⊤
  · rw [hL, ENNReal.mul_top (by simp [Real.pi_pos])]
    exact le_top
  have e0 : volume.restrict (Ioo (-π) π) = volume.restrict (Ioc (-π) π) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hf2 : MemLp f 2 (volume.restrict (Ioo (-π) π)) := by
    refine (memLp_two_iff_integrable_sq_norm hf).2 ⟨hf.norm.pow 2, ?_⟩
    unfold HasFiniteIntegral
    simpa only [enorm_pow, enorm_norm] using lt_top_iff_ne_top.2 hL
  rw [e0] at hf2
  obtain ⟨hs, hle⟩ := coef_sq_sum m hm f hf2
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
  have hint : Integrable (fun θ => f θ ^ 2) (volume.restrict (Ioc (-π) π)) := hf2.integrable_sq
  calc ENNReal.ofReal (∑' n, ‖coefAt m n f‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * π)⁻¹ * ∫ θ in Ioc (-π) π, f θ ^ 2) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((2 * π)⁻¹) * ENNReal.ofReal (∫ θ in Ioc (-π) π, f θ ^ 2) :=
        ENNReal.ofReal_mul (by positivity)
    _ = _ := by
      congr 1
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun θ => sq_nonneg _), ← e0]
      refine lintegral_congr fun θ => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

def sliceCoef {E : Type*} (m : ℕ) (n : ℤ) (φ : ℝ → E → ℝ) (X : Space → E) (p : ℝ × ℝ) : ℂ :=
  coefAt m n (fun θ => φ θ (X (cylPoint p.1 θ p.2)))

theorem mode_lint (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Space → E} (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℝ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (g : Space → ENNReal) (hg : AEMeasurable g volume)
    (hb : ∀ p ∈ K.rect, ∀ θ, ‖φ θ (X (cylPoint p.1 θ p.2))‖ₑ ^ 2 ≤ g (cylPoint p.1 θ p.2)) :
    ∫⁻ p in K.rect, ∑' n : ℤ, ENNReal.ofReal (p.1 * ‖sliceCoef m n φ X p‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ y, g y := by
  have hsl := ae_mono (hle K hK) (slice_meas hX φ hφc)
  have hpt : ∀ᵐ p ∂(volume.restrict K.rect), ∑' n : ℤ, ENNReal.ofReal (p.1 * ‖sliceCoef m n φ X p‖ ^ 2) ≤
      ENNReal.ofReal ((2 * π)⁻¹) * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
    filter_upwards [hsl, ae_restrict_mem (rect_meas K)] with p hp hpK
    have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hpK.1.1
    have e : ∀ n : ℤ, ENNReal.ofReal (p.1 * ‖sliceCoef m n φ X p‖ ^ 2) =
        ENNReal.ofReal p.1 * ENNReal.ofReal (‖sliceCoef m n φ X p‖ ^ 2) := fun n => ENNReal.ofReal_mul h0
    simp only [e]
    rw [ENNReal.tsum_mul_left]
    calc ENNReal.ofReal p.1 * ∑' n : ℤ, ENNReal.ofReal (‖sliceCoef m n φ X p‖ ^ 2)
        ≤ ENNReal.ofReal p.1 * (ENNReal.ofReal ((2 * π)⁻¹) *
            ∫⁻ θ in Ioo (-π) π, ‖φ θ (X (cylPoint p.1 θ p.2))‖ₑ ^ 2) :=
          by gcongr; exact slice_bound m hm _ hp
      _ ≤ ENNReal.ofReal p.1 * (ENNReal.ofReal ((2 * π)⁻¹) *
            ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
          gcongr with θ
          exact hb p hpK θ
      _ = _ := by ring
  calc _ ≤ ∫⁻ p in K.rect, ENNReal.ofReal ((2 * π)⁻¹) *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono_ae hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal ((2 * π)⁻¹) *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono' (hle K hK) le_rfl
    _ = ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ y, g y := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      rw [← key g, muU_def, lintegral_prod]
      · congr 1; funext p
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
          (hg.comp_quasiMeasurePreserving (muU_def ▸ qmp))

theorem mode_sum (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : Space → E} (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℝ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (g : Space → ENNReal) (hg : AEMeasurable g volume)
    (hgf : ∫⁻ y, g y ≠ ⊤)
    (hb : ∀ p ∈ K.rect, ∀ θ, ‖φ θ (X (cylPoint p.1 θ p.2))‖ₑ ^ 2 ≤ g (cylPoint p.1 θ p.2)) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖sliceCoef m n φ X p‖ ^ 2) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * ‖sliceCoef m n φ X p‖ ^ 2) := by
  have hcm : ∀ n : ℤ, AEStronglyMeasurable (sliceCoef m n φ X) (volume.restrict K.rect) := by
    intro n
    have h := meas_gen hX (fun θ e => Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (φ θ e : ℂ))
      ((phase_cont m n).mul (Complex.continuous_ofReal.comp hφc))
    exact (h.mono_measure (hle K hK)).const_mul _
  have hfm : ∀ n : ℤ, AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * ‖sliceCoef m n φ X p‖ ^ 2)
      (volume.restrict K.rect) :=
    fun n => continuous_fst.aestronglyMeasurable.mul ((hcm n).norm.pow 2)
  have hL := mode_lint K hK m hm hX φ hφc g hg hb
  have hfin : ∫⁻ p in K.rect, ∑' n : ℤ, ENNReal.ofReal (p.1 * ‖sliceCoef m n φ X p‖ ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgf) hL
  have hnorm : ∀ n : ℤ, ∀ᵐ p ∂(volume.restrict K.rect),
      ‖p.1 * ‖sliceCoef m n φ X p‖ ^ 2‖ₑ = ENNReal.ofReal (p.1 * ‖sliceCoef m n φ X p‖ ^ 2) := by
    intro n
    filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
    have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
  have hint : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖sliceCoef m n φ X p‖ ^ 2) K.rect := by
    intro n
    refine ⟨hfm n, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_congr_ae (hnorm n)]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfin)
    exact lintegral_mono fun p => ENNReal.le_tsum n
  refine ⟨hint, ?_⟩
  have e : (fun n : ℤ => ∫ p in K.rect, p.1 * ‖sliceCoef m n φ X p‖ ^ 2) =
      fun n => (∫⁻ p in K.rect, ENNReal.ofReal (p.1 * ‖sliceCoef m n φ X p‖ ^ 2)).toReal := by
    funext n
    refine integral_eq_lintegral_of_nonneg_ae ?_ (hfm n)
    filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
    have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    positivity
  rw [e]
  refine ENNReal.summable_toReal ?_
  rw [← lintegral_tsum fun n => (hfm n).aemeasurable.ennreal_ofReal]
  exact hfin

theorem gm_coef (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    gradMode m n G a b p = sliceCoef m n (fun θ M => frameMat θ M a b) G p := by
  rw [gradMode_eq]; rfl

theorem mv_coef (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    modeVec m n v p.1 p.2 a = sliceCoef m n (fun θ u => frameVec θ u a) v p := by
  rw [modeVec_eq]; rfl

theorem gm_sum (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {G : Space → (Space →L[ℝ] Space)}
    (hG1 : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y))) (a b : Fin 3) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖gradMode m n G a b p‖ ^ 2) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * ‖gradMode m n G a b p‖ ^ 2) := by
  have h2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hG1).2 ((hG2.const_mul 3).mono'
      ((hG1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact EmbedWeak.Internal.norm_sq_le (G y)
  have hfin : ∫⁻ y, ‖G y‖ₑ ^ 2 ≠ ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hG1).1 h2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi.ne
  have H := mode_sum K hK m hm hG1 (fun θ M => frameMat θ M a b) (frameMat_cont a b) (fun y => ‖G y‖ₑ ^ 2)
    (hG1.enorm.pow_const 2) hfin (fun p _ θ => by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (frameMat_bound θ _ a b))
  simp only [gm_coef]
  exact H

theorem mv_sum (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (a : Fin 3) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2) := by
  set R := K.r₂ + K.z₂ with hR
  have hF : Integrable (ModeVelSquareInternal.bump R v) := ModeVelSquareInternal.bump_integrable hs R
  have hfin : ∫⁻ y, ENNReal.ofReal (ModeVelSquareInternal.bump R v y) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hF.hasFiniteIntegral.ne (lintegral_mono fun y => ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have HH := mode_sum K hK m hm hs.measurable_velocity (fun θ u => frameVec θ u a) (frameVec_cont a)
    (fun y => ENNReal.ofReal (ModeVelSquareInternal.bump R v y)) hF.aemeasurable.ennreal_ofReal hfin
    (fun p hp θ => by
      have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
      have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
      have hball : cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) R := by
        rw [mem_closedBall_zero_iff, ModeVelSquareInternal.cylPoint_norm, Real.sqrt_le_iff]
        constructor
        · linarith [hp.1.2, hp.2.2]
        · nlinarith [hp.1.2, hp.2.2]
      simp only [ModeVelSquareInternal.bump]
      rw [Set.indicator_of_mem hball, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      set t := ‖v (cylPoint p.1 θ p.2)‖
      have ht : 0 ≤ t := norm_nonneg _
      have h1 : |frameVec θ (v (cylPoint p.1 θ p.2)) a| ^ 2 ≤ t ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (ModeVelSquareInternal.frameVec_abs _ _ _) 2
      nlinarith [sq_nonneg (t ^ 3 - t), sq_nonneg (t ^ 2 - 1), sq_nonneg t])
  simp only [mv_coef]
  exact HH

theorem tot_sum (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * (sumSq (fun a b => gradMode m n G a b p)
      + vecSq (modeVec m n v p.1 p.2))) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * (sumSq (fun a b => gradMode m n G a b p)
      + vecSq (modeVec m n v p.1 p.2))) := by
  have hG := fun a b => gm_sum K hK m hm hs.measurable_gradient hs.gradient_two a b
  have hV := fun a => mv_sum K hK m hm hs a
  have e : ∀ n : ℤ, (fun p : ℝ × ℝ => p.1 * (sumSq (fun a b => gradMode m n G a b p)
      + vecSq (modeVec m n v p.1 p.2))) = fun p => (∑ a : Fin 3, ∑ b : Fin 3, p.1 * ‖gradMode m n G a b p‖ ^ 2)
        + ∑ a : Fin 3, p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2 := by
    intro n; funext p; simp only [sumSq, vecSq, mul_add, Finset.mul_sum]
  have hi1 : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ‖gradMode m n G a b p‖ ^ 2)
      K.rect := fun n => integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hG a b).1 n
  have hi2 : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => ∑ a : Fin 3, p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2)
      K.rect := fun n => integrable_finsetSum _ fun a _ => (hV a).1 n
  refine ⟨fun n => by rw [e n]; exact (hi1 n).add (hi2 n), ?_⟩
  have e2 : (fun n : ℤ => ∫ p in K.rect, p.1 * (sumSq (fun a b => gradMode m n G a b p)
      + vecSq (modeVec m n v p.1 p.2))) = fun n => (∑ a : Fin 3, ∑ b : Fin 3,
        ∫ p in K.rect, p.1 * ‖gradMode m n G a b p‖ ^ 2) + ∑ a : Fin 3, ∫ p in K.rect, p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2 := by
    funext n
    rw [e n, integral_add (hi1 n) (hi2 n), integral_finsetSum _ fun a _ => (hV a).1 n,
      integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hG a b).1 n]
    congr 1
    exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => (hG a b).1 n
  rw [e2]
  exact (summable_sum fun a _ => summable_sum fun b _ => (hG a b).2).add (summable_sum fun a _ => (hV a).2)

theorem curlSq_le (s : Fin 3 → Fin 3 → ℂ) : curlSq s ≤ 27 * sumSq s := by
  have hs : sumSq s = ∑ q : Fin 3 × Fin 3, ‖s q.2 q.1‖ ^ 2 := by
    rw [sumSq, Finset.sum_comm, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ i, ‖curlComp s i‖ ^ 2 ≤ 9 * sumSq s := by
    intro i
    have hn : ‖curlComp s i‖ ≤ ∑ q : Fin 3 × Fin 3, ‖s q.2 q.1‖ := by
      unfold curlComp
      rw [← Finset.univ_product_univ, Finset.sum_product]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun l _ => ?_))
      rw [norm_mul, Complex.norm_real]
      have hp : ‖CellCert.permSign i j l‖ ≤ 1 := by
        unfold CellCert.permSign; split_ifs <;> simp
      calc ‖CellCert.permSign i j l‖ * ‖s l j‖ ≤ 1 * ‖s l j‖ :=
            mul_le_mul_of_nonneg_right hp (norm_nonneg _)
        _ = ‖s l j‖ := one_mul _
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun q => ‖s q.2 q.1‖)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcs
    rw [hs]
    calc ‖curlComp s i‖ ^ 2 ≤ (∑ q : Fin 3 × Fin 3, ‖s q.2 q.1‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ _ := by exact_mod_cast hcs
  unfold curlSq
  calc ∑ i : Fin 3, ‖curlComp s i‖ ^ 2 ≤ ∑ i : Fin 3, 9 * sumSq s := Finset.sum_le_sum fun i _ => h1 i
    _ = 27 * sumSq s := by simp; ring

theorem bdd_sum {ι : Type*} [Fintype ι] (K : CellBox) (f : ι → ℝ × ℝ → ℝ)
    (h : ∀ i, ∃ C : ℝ, ∀ p ∈ K.rect, |f i p| ≤ C) : ∃ C : ℝ, ∀ p ∈ K.rect, |∑ i, f i p| ≤ C := by
  choose C hC using h
  exact ⟨∑ i, C i, fun p hp => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hC i p hp)⟩

theorem bdd_mul (K : CellBox) (k : ℝ) (f : ℝ × ℝ → ℝ) (h : ∃ C : ℝ, ∀ p ∈ K.rect, |f p| ≤ C) :
    ∃ C : ℝ, ∀ p ∈ K.rect, |k * f p| ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨|k| * C, fun p hp => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg k)⟩

theorem bdd_sq (K : CellBox) (f : ℝ × ℝ → ℝ) (h : ∃ C : ℝ, ∀ p ∈ K.rect, |f p| ≤ C) :
    ∃ C : ℝ, ∀ p ∈ K.rect, |f p ^ 2| ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C ^ 2, fun p hp => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC p hp) 2⟩

theorem dens_reg (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (U : Finset ℤ) (A B Cc : ℝ × ℝ → ℝ)
    (hAm : AEStronglyMeasurable A (volume.restrict K.rect)) (hBm : AEStronglyMeasurable B (volume.restrict K.rect))
    (hCm : AEStronglyMeasurable Cc (volume.restrict K.rect))
    (hA : ∃ C : ℝ, ∀ p ∈ K.rect, |A p| ≤ C) (hB : ∃ C : ℝ, ∀ p ∈ K.rect, |B p| ≤ C)
    (hC : ∃ C : ℝ, ∀ p ∈ K.rect, |Cc p| ≤ C) (D : ℤ → ℝ × ℝ → ℝ)
    (hD : ∀ n p, D n p = if n ∈ U then 0 else A p * curlSq (fun a b => gradMode m n G a b p)
      + B p * sumSq (fun a b => gradMode m n G a b p) + Cc p * vecSq (modeVec m n v p.1 p.2)) :
    (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * D n p) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * D n p) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * D n p‖) := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨CC, hCC⟩ := hC
  set C := |CA| + |CB| + |CC| with hCdef
  have hT := tot_sum K hK m hm hs
  have hgm : ∀ n : ℤ, ∀ a b, AEStronglyMeasurable (gradMode m n G a b) (volume.restrict K.rect) :=
    fun n a b => gm_meas K hK m n hs.measurable_gradient a b
  have hvm : ∀ n : ℤ, ∀ a, AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a)
      (volume.restrict K.rect) := fun n a => (modeVelSquare K hK m v G H hs n a).1
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * D n p) (volume.restrict K.rect) := by
    intro n
    have e : (fun p : ℝ × ℝ => p.1 * D n p) = fun p => p.1 * (if n ∈ U then 0 else A p * curlSq (fun a b => gradMode m n G a b p)
      + B p * sumSq (fun a b => gradMode m n G a b p) + Cc p * vecSq (modeVec m n v p.1 p.2)) := funext fun p => by rw [hD]
    rw [e]
    refine continuous_fst.aestronglyMeasurable.mul ?_
    split_ifs
    · exact aestronglyMeasurable_const
    · have hc : AEStronglyMeasurable (fun p : ℝ × ℝ => curlSq (fun a b => gradMode m n G a b p)) (volume.restrict K.rect) :=
        Finset.univ.aestronglyMeasurable_fun_sum fun i _ => ((Finset.univ.aestronglyMeasurable_fun_sum fun j _ =>
          Finset.univ.aestronglyMeasurable_fun_sum fun l _ => (hgm n l j).const_mul _).norm.pow 2)
      have hq : AEStronglyMeasurable (fun p : ℝ × ℝ => sumSq (fun a b => gradMode m n G a b p)) (volume.restrict K.rect) :=
        Finset.univ.aestronglyMeasurable_fun_sum fun a _ => Finset.univ.aestronglyMeasurable_fun_sum fun b _ =>
          (hgm n a b).norm.pow 2
      have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => vecSq (modeVec m n v p.1 p.2)) (volume.restrict K.rect) :=
        Finset.univ.aestronglyMeasurable_fun_sum fun a _ => (hvm n a).norm.pow 2
      exact ((hAm.mul hc).add (hBm.mul hq)).add (hCm.mul hw)
  have hbd : ∀ n : ℤ, ∀ p ∈ K.rect, ‖p.1 * D n p‖ ≤ 28 * C * (p.1 * (sumSq (fun a b => gradMode m n G a b p)
      + vecSq (modeVec m n v p.1 p.2))) := by
    intro n p hp
    have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have hq0 : 0 ≤ sumSq (fun a b => gradMode m n G a b p) := by unfold sumSq; positivity
    have hw0 : 0 ≤ vecSq (modeVec m n v p.1 p.2) := by unfold vecSq; positivity
    have hc0 : 0 ≤ curlSq (fun a b => gradMode m n G a b p) := by unfold curlSq; positivity
    have hcl := curlSq_le (fun a b => gradMode m n G a b p)
    have hA' : |A p| ≤ C := (hCA p hp).trans (by rw [hCdef]; linarith [le_abs_self CA, abs_nonneg CB, abs_nonneg CC])
    have hB' : |B p| ≤ C := (hCB p hp).trans (by rw [hCdef]; linarith [le_abs_self CB, abs_nonneg CA, abs_nonneg CC])
    have hC' : |Cc p| ≤ C := (hCC p hp).trans (by rw [hCdef]; linarith [le_abs_self CC, abs_nonneg CA, abs_nonneg CB])
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hA'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, hD]
    split_ifs
    · simp only [abs_zero, mul_zero]
      positivity
    · have k1 : |A p * curlSq (fun a b => gradMode m n G a b p)| ≤ C * (27 * sumSq (fun a b => gradMode m n G a b p)) := by
        rw [abs_mul, abs_of_nonneg hc0]
        exact mul_le_mul hA' hcl hc0 hC0
      have k2 : |B p * sumSq (fun a b => gradMode m n G a b p)| ≤ C * sumSq (fun a b => gradMode m n G a b p) := by
        rw [abs_mul, abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_right hB' hq0
      have k3 : |Cc p * vecSq (modeVec m n v p.1 p.2)| ≤ C * vecSq (modeVec m n v p.1 p.2) := by
        rw [abs_mul, abs_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_right hC' hw0
      have k4 := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add k1 k2)) k3)
      have k5 : p.1 * |A p * curlSq (fun a b => gradMode m n G a b p) + B p * sumSq (fun a b => gradMode m n G a b p)
          + Cc p * vecSq (modeVec m n v p.1 p.2)| ≤ p.1 * (C * (27 * sumSq (fun a b => gradMode m n G a b p))
            + C * sumSq (fun a b => gradMode m n G a b p) + C * vecSq (modeVec m n v p.1 p.2)) :=
        mul_le_mul_of_nonneg_left k4 h0
      refine k5.trans ?_
      have : 0 ≤ p.1 * (C * vecSq (modeVec m n v p.1 p.2)) := by positivity
      nlinarith
  have hint : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * D n p) K.rect := by
    intro n
    refine ((hT.1 n).const_mul (28 * C)).mono' (hmeas n) ?_
    filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
    exact hbd n p hp
  have hnb : ∀ n : ℤ, ∫ p in K.rect, ‖p.1 * D n p‖ ≤ 28 * C * ∫ p in K.rect, p.1 * (sumSq (fun a b => gradMode m n G a b p)
      + vecSq (modeVec m n v p.1 p.2)) := by
    intro n
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun p => norm_nonneg _) ((hT.1 n).const_mul _) ?_
    filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
    exact hbd n p hp
  have hsn : Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * D n p‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _) hnb (hT.2.mul_left _)
  refine ⟨hint, Summable.of_norm_bounded hsn fun n => norm_integral_le_integral_norm _, hsn⟩

end Breakdown.CellCert.CellAnalysis.SharpYChargeRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpYChargeRegular.Internal
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem chargeRegular : ChargeRegularStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  have hK : IsCellBox K := hd.box
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hs := hx.1
  have hsd : ∀ n ∉ S.resolved, ∀ p, sharpGrad c K S x n p = fun a b => gradMode c.order n x.2.1 a b p := by
    intro n hn p; funext a b; simp [sharpGrad, lowGrad, hn]
  have hsv : ∀ n ∉ S.resolved, ∀ p, sharpVel c K S x n p = modeVec c.order n x.1 p.1 p.2 := by
    intro n hn p; funext a; simp [sharpVel, lowVel, hn]
  have bS : ∀ i, ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C := fun i => by
    obtain ⟨C, hC⟩ := (hd.class_regular i).2.2.2.2; exact ⟨C, fun p hp => (hC p hp).1⟩
  have bG : ∀ i, ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.gradDev i p| ≤ C := fun i => by
    obtain ⟨C, hC⟩ := (hd.class_regular i).2.2.2.2; exact ⟨C, fun p hp => (hC p hp).2.1⟩
  have bV : ∀ i, ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.velocityDev i p| ≤ C := fun i => by
    obtain ⟨C, hC⟩ := (hd.class_regular i).2.2.2.2; exact ⟨C, fun p hp => (hC p hp).2.2.1⟩
  have bC : ∀ i, ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.curlDev i p| ≤ C := fun i => by
    obtain ⟨C, hC⟩ := (hd.class_regular i).2.2.2.2; exact ⟨C, fun p hp => (hC p hp).2.2.2⟩
  have bK : ∀ k : ℝ, ∃ C : ℝ, ∀ p ∈ K.rect, |(fun _ : ℝ × ℝ => k) p| ≤ C := fun k => ⟨|k|, fun p _ => le_rfl⟩
  have hclass := dens_reg K hK c.order hm hs (S.resolved ∪ S.band)
    (fun p => ∑ i, (Cl.shareWeight i)⁻¹ * Cl.strainDev i p)
    (fun p => ∑ i, ((1 / 2) * Exterior.traceFreeConst * S.splitLength * (Cl.shareWeight i)⁻¹) * Cl.gradDev i p)
    (fun p => ∑ i, ((1 / 2) * Exterior.traceFreeConst * (S.splitLength)⁻¹ * (Cl.shareWeight i)⁻¹) * Cl.gradDev i p)
    (Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
      (hd.class_regular i).1.aestronglyMeasurable.const_mul _)
    (Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
      (hd.class_regular i).2.1.aestronglyMeasurable.const_mul _)
    (Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
      (hd.class_regular i).2.1.aestronglyMeasurable.const_mul _)
    (bdd_sum K _ fun i => bdd_mul K _ _ (bS i)) (bdd_sum K _ fun i => bdd_mul K _ _ (bG i))
    (bdd_sum K _ fun i => bdd_mul K _ _ (bG i))
    (fun n p => classDensity c K S x Cl n p) (fun n p => by
      unfold classDensity
      split_ifs with h
      · rfl
      · have hn : n ∉ S.resolved := fun h' => h (Finset.mem_union_left _ h')
        rw [hsd n hn p, hsv n hn p]
        simp only [CellClasses.classLoss, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)
  have hrow := dens_reg K hK c.order hm hs (S.resolved ∪ S.band)
    (fun p => ∑ i, (2 * Cl.rowWeight i) * Cl.velocityDev i p ^ 2) (fun _ => 0)
    (fun p => ∑ i, (2 * Cl.rowWeight i) * Cl.curlDev i p ^ 2)
    (Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
      ((hd.class_regular i).2.2.1.aestronglyMeasurable.pow 2).const_mul _)
    aestronglyMeasurable_const
    (Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
      ((hd.class_regular i).2.2.2.1.aestronglyMeasurable.pow 2).const_mul _)
    (bdd_sum K _ fun i => bdd_mul K _ _ (bdd_sq K _ (bV i))) (bK 0)
    (bdd_sum K _ fun i => bdd_mul K _ _ (bdd_sq K _ (bC i)))
    (fun n p => rowChargeDensity c S x Cl n p) (fun n p => by
      unfold rowChargeDensity
      split_ifs with h
      · rfl
      · simp only [zero_mul, add_zero, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)
  have hpen := dens_reg K hK c.order hm hs (S.resolved ∪ S.band)
    (fun _ => S.penaltyCurl) (fun _ => S.penaltyStrain) (fun _ => S.penaltyVelocity)
    aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
    (bK _) (bK _) (bK _)
    (fun n p => penaltyDensity c K S x n p) (fun n p => by
      unfold penaltyDensity
      split_ifs with h
      · rfl
      · have hn : n ∉ S.resolved := fun h' => h (Finset.mem_union_left _ h')
        rw [hsd n hn p, hsv n hn p]
        simp only [CellScalars.penalty]
        ring)
  refine ⟨hclass.1, hrow.1, hpen.1, hclass.2.1, hrow.2.1, hpen.2.1, ?_⟩
  have e1 : CellScalars.unresolvedRowCharge c K S Cl x =
      ∫ p in K.rect, ∑' n : ℤ, p.1 * rowChargeDensity c S x Cl n p := by
    unfold CellScalars.unresolvedRowCharge
    refine setIntegral_congr_fun (rect_meas K) fun p _ => ?_
    rw [tsum_mul_left]
    rfl
  rw [e1]
  exact (integral_tsum_of_summable_integral_norm hrow.1 hrow.2.2).symm

end Breakdown.CellCert.CellAnalysis
