import Breakdown.FracCell.SharpYDensityRegular
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.CircleWeak

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpDensityModeSeries.Internal

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal
open Breakdown.CellCert.CellEnergy (angularComb frameTurn)

theorem phase_eq (m : ℕ) (n : ℤ) (θ : ℝ) :
    Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) =
      fourier (-(n * (m : ℤ))) (θ : AddCircle (π - -π)) := by
  rw [fourier_coe_apply]
  congr 1
  unfold azimuth
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

theorem coeff_sq_sum_real {m : ℕ} (hm : 1 ≤ m) (S : Finset ℤ) (h : ℝ → ℂ)
    (hL2 : MemLp h 2 (volume.restrict (Ioc (-π) π))) :
    ∑ n ∈ S, ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
        Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ‖ ^ 2
      ≤ (1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖h θ‖ ^ 2 := by
  have hab : -π < π := by linarith [Real.pi_pos]
  have hsum := hasSum_sq_fourierCoeffOn hab hL2
  have hc : ∀ n : ℤ, (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ = fourierCoeffOn hab h (n * m) := by
    intro n
    rw [fourierCoeffOn_eq_integral _ _ hab, Complex.real_smul,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    congr 1
    · push_cast; ring
    · refine integral_congr_ae (ae_of_all _ fun θ => ?_)
      simp only [smul_eq_mul]
      rw [phase_eq]
  have hinj : Set.InjOn (fun n : ℤ => n * (m : ℤ)) S := by
    intro x _ y _ hxy
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    exact mul_right_cancel₀ hm' hxy
  calc ∑ n ∈ S, ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
        Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ‖ ^ 2
        = ∑ j ∈ S.image (fun n : ℤ => n * (m : ℤ)), ‖fourierCoeffOn hab h j‖ ^ 2 := by
          rw [Finset.sum_image hinj]
          exact Finset.sum_congr rfl fun n _ => by rw [hc]
    _ ≤ (π - -π)⁻¹ • ∫ x in (-π)..π, ‖h x‖ ^ 2 := sum_le_hasSum _ (fun _ _ => by positivity) hsum
    _ = (1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖h θ‖ ^ 2 := by
          rw [smul_eq_mul, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
          congr 1
          ring

theorem sq_enorm (u : ℂ) : ENNReal.ofReal (‖u‖ ^ 2) = ‖u‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem coeff_sq_sum {m : ℕ} (hm : 1 ≤ m) (S : Finset ℤ) (h : ℝ → ℂ) :
    ∑ n ∈ S, ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
        Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ‖ₑ ^ 2
      ≤ ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioo (-π) π, ‖h θ‖ₑ ^ 2 := by
  by_cases hf : AEStronglyMeasurable h (volume.restrict (Ioo (-π) π))
  · by_cases hfin : ∫⁻ θ in Ioo (-π) π, ‖h θ‖ₑ ^ 2 = ⊤
    · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
      exact le_top
    · have hi : Integrable (fun θ => ‖h θ‖ ^ 2) (volume.restrict (Ioo (-π) π)) := by
        refine ⟨(hf.norm.pow 2), ?_⟩
        unfold HasFiniteIntegral
        simpa only [enorm_pow, enorm_norm] using lt_top_iff_ne_top.2 hfin
      have hL : MemLp h 2 (volume.restrict (Ioc (-π) π)) := by
        rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact (memLp_two_iff_integrable_sq_norm hf).2 hi
      have hb := coeff_sq_sum_real hm S h hL
      calc ∑ n ∈ S, ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
            Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ‖ₑ ^ 2
          = ENNReal.ofReal (∑ n ∈ S, ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
            Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ‖ ^ 2) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
            simp only [sq_enorm]
        _ ≤ ENNReal.ofReal ((1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖h θ‖ ^ 2) := ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioo (-π) π, ‖h θ‖ₑ ^ 2 := by
            rw [ENNReal.ofReal_mul (by positivity),
              ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => by positivity)]
            simp only [sq_enorm]
  · have hz : ∀ n : ℤ, ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * h θ = 0 := by
      intro n
      refine integral_non_aestronglyMeasurable fun hm' => hf ?_
      have hc : Continuous (fun θ : ℝ => Complex.exp (((azimuth m n * θ : ℝ) : ℂ) * Complex.I)) := by fun_prop
      refine (hc.aestronglyMeasurable.mul hm').congr (ae_of_all _ fun θ => ?_)
      rw [Pi.mul_apply]
      rw [← mul_assoc, ← Complex.exp_add,
        show ((azimuth m n * θ : ℝ) : ℂ) * Complex.I + -((azimuth m n * θ : ℝ) : ℂ) * Complex.I = 0 by ring,
        Complex.exp_zero, one_mul]
    rw [Finset.sum_eq_zero fun n _ => by rw [hz n, mul_zero, enorm_zero, zero_pow two_ne_zero]]
    exact zero_le

theorem gm_sum {m : ℕ} (hm : 1 ≤ m) (S : Finset ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3)
    (p : ℝ × ℝ) :
    ∑ n ∈ S, ‖gradMode m n G a b p‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ₑ ^ 2 := by
  have e : ∀ n, gradMode m n G a b p = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℝ) : ℂ) :=
    fun n => gradMode_eq m n G a b p
  simp only [e]
  refine (coeff_sq_sum hm S _).trans (mul_le_mul' le_rfl (lintegral_mono fun θ => ?_))
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (frameMat_bound θ _ a b)

theorem mv_sum {m : ℕ} (hm : 1 ≤ m) (S : Finset ℤ) (v : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    ∑ n ∈ S, ‖modeVec m n v p.1 p.2 a‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioo (-π) π, ‖v (cylPoint p.1 θ p.2)‖ₑ ^ 2 := by
  have e : ∀ n, modeVec m n v p.1 p.2 a = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((frameVec θ (v (cylPoint p.1 θ p.2)) a : ℝ) : ℂ) :=
    fun n => modeVec_eq m n v a p
  simp only [e]
  refine (coeff_sq_sum hm S _).trans (mul_le_mul' le_rfl (lintegral_mono fun θ => ?_))
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have hb := velKernel_bound m 0 a θ (v (cylPoint p.1 θ p.2))
  rw [velKernel, norm_mul, phase_norm, one_mul] at hb
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hb

theorem mt_sum {m : ℕ} (hm : 1 ≤ m) (S : Finset ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b c : Fin 3) (p : ℝ × ℝ) :
    ∑ n ∈ S, ‖modeThird m n H a b c p‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioo (-π) π, ‖H (cylPoint p.1 θ p.2)‖ₑ ^ 2 := by
  have e : ∀ n, modeThird m n H a b c p = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℝ) : ℂ) :=
    fun n => ModeSquareIntegrable.Internal.modeThird_eq m n H a b c p
  simp only [e]
  refine (coeff_sq_sum hm S _).trans (mul_le_mul' le_rfl (lintegral_mono fun θ => ?_))
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (ModeSquareIntegrable.Internal.frameThird_bound θ _ a b c)

theorem weight_le (K : CellBox) (hK : IsCellBox K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 ∧ K.lineWeight p.1 ≤ C * p.1 := by
  refine ⟨if K.r₁ = 0 then 1 else K.r₁⁻¹, ?_, fun p hp => ?_⟩
  · split_ifs
    · norm_num
    · exact inv_nonneg.2 hK.r_order.1
  · have h1 : K.r₁ ≤ p.1 := hp.1.1
    by_cases h : K.r₁ = 0
    · simp only [CellBox.lineWeight, h, if_true]
      constructor <;> linarith
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
      simp only [CellBox.lineWeight, h, if_false]
      refine ⟨zero_le_one, ?_⟩
      rw [inv_mul_eq_div, le_div_iff₀ hr]
      linarith

theorem fin_bound (K : CellBox) (hK : IsCellBox K) (g : Space → ENNReal) (hg : AEMeasurable g volume)
    (hfin : ∫⁻ y, g y < ⊤) (D : ENNReal) (hD : D ≠ ⊤) :
    ∫⁻ p in K.rect, ENNReal.ofReal (K.lineWeight p.1) * (D * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2))
      < ⊤ := by
  obtain ⟨C, hC0, hw⟩ := weight_le K hK
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hg.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  have hCD : ENNReal.ofReal C * D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD
  calc ∫⁻ p in K.rect, ENNReal.ofReal (K.lineWeight p.1) * (D * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2))
      ≤ ∫⁻ p in K.rect, ENNReal.ofReal C * D *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
        refine setLIntegral_mono' (rect_meas K) fun p hp => ?_
        have h1 : ENNReal.ofReal (K.lineWeight p.1) ≤ ENNReal.ofReal C * ENNReal.ofReal p.1 := by
          rw [← ENNReal.ofReal_mul hC0]
          exact ENNReal.ofReal_le_ofReal (hw p hp).2
        calc ENNReal.ofReal (K.lineWeight p.1) * (D * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2))
            ≤ ENNReal.ofReal C * ENNReal.ofReal p.1 * (D * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
              mul_le_mul' h1 le_rfl
          _ = ENNReal.ofReal C * D * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
              ring
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal C * D *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono' (hle K hK) le_rfl
    _ = ENNReal.ofReal C * D * ∫⁻ y, g y := by rw [lintegral_const_mul' _ _ hCD, hint]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hCD) hfin

theorem summable_of_bound (K : CellBox) (F : ℤ → ℝ × ℝ → ℝ) (hI : ∀ n, IntegrableOn (F n) K.rect)
    (h0 : ∀ n, ∀ p ∈ K.rect, 0 ≤ F n p) (B : ℝ × ℝ → ENNReal) (hB : ∫⁻ p in K.rect, B p < ⊤)
    (hb : ∀ S : Finset ℤ, ∀ᵐ p ∂(volume.restrict K.rect), ∑ n ∈ S, ENNReal.ofReal (F n p) ≤ B p) :
    Summable (fun n => ∫ p in K.rect, F n p) := by
  have hnn : ∀ n, 0 ≤ ∫ p in K.rect, F n p := fun n => setIntegral_nonneg (rect_meas K) (h0 n)
  refine summable_of_sum_le (c := (∫⁻ p in K.rect, B p).toReal) hnn fun S => ?_
  rw [← ENNReal.ofReal_le_iff_le_toReal hB.ne, ENNReal.ofReal_sum_of_nonneg fun n _ => hnn n]
  have e : ∀ n, ENNReal.ofReal (∫ p in K.rect, F n p) = ∫⁻ p in K.rect, ENNReal.ofReal (F n p) := fun n =>
    ofReal_integral_eq_lintegral_ofReal (hI n) (ae_restrict_of_forall_mem (rect_meas K) (h0 n))
  simp only [e]
  rw [← lintegral_finsetSum' _ fun n _ => (hI n).aemeasurable.ennreal_ofReal]
  exact lintegral_mono_ae (hb S)

theorem cyl_mem_ball (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂) := by
  rw [mem_closedBall_zero_iff]
  have h1 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have h2 : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  refine (cylPoint_norm p.1 θ p.2).trans ?_
  rw [abs_of_nonneg h1, abs_of_nonneg h2]
  linarith [hp.1.2, hp.2.2]

theorem vel_part (K : CellBox) (hK : IsCellBox K) {m : ℕ} (hm : 1 ≤ m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (a : Fin 3) :
    Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2) := by
  obtain ⟨C, hC0, hw⟩ := weight_le K hK
  set R : ℝ := 2 * K.r₂ + K.z₂ with hR
  set g : Space → ENNReal := (Metric.closedBall (0 : Space) R).indicator (fun y => ‖v y‖ₑ ^ 2) with hg_def
  have hg : AEMeasurable g volume :=
    (hs.measurable_velocity.enorm.pow_const 2).indicator measurableSet_closedBall
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_indicator measurableSet_closedBall]
    have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) R)) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have h2 : MemLp v 2 (volume.restrict (Metric.closedBall (0 : Space) R)) :=
      (hs.velocity_six.restrict _).mono_exponent (by norm_num)
    have hi := ((memLp_two_iff_integrable_sq_norm h2.1).1 h2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi
  refine summable_of_bound K (fun n p => K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2)
    (fun n => (modeVelSquare K hK m v G H hs n a).2)
    (fun n p hp => mul_nonneg (hw p hp).1 (by positivity))
    (fun p => ENNReal.ofReal (K.lineWeight p.1) *
      (ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)))
    (fin_bound K hK g hg hfin _ ENNReal.ofReal_ne_top) fun S => ?_
  refine ae_restrict_of_forall_mem (rect_meas K) fun p hp => ?_
  calc ∑ n ∈ S, ENNReal.ofReal (K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2)
      = ENNReal.ofReal (K.lineWeight p.1) * ∑ n ∈ S, ‖modeVec m n v p.1 p.2 a‖ₑ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [ENNReal.ofReal_mul (hw p hp).1, sq_enorm]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl ((mv_sum hm S v a p).trans (mul_le_mul' le_rfl (lintegral_mono fun θ => ?_)))
        rw [hg_def, Set.indicator_of_mem (cyl_mem_ball K hK hp θ)]

def turnCoef (a b a' b' : Fin 3) : ℂ :=
  (if a' = a then (frameTurn b' b : ℂ) else 0) + (if b' = b then (frameTurn a' a : ℂ) else 0)

theorem comb_split (k : ℝ) (a b : Fin 3) (x : Fin 3 → Fin 3 → ℂ) :
    Complex.I * (k : ℂ) * x a b = (∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * x a' b') +
      ∑ a' : Fin 3, ∑ b' : Fin 3, turnCoef a b a' b' * x a' b' := by
  fin_cases a <;> fin_cases b <;> simp [angularComb, turnCoef, Fin.sum_univ_three, frameTurn] <;> ring

theorem frameTurn_norm (c b : Fin 3) : ‖(frameTurn c b : ℂ)‖ ≤ 1 := by
  unfold frameTurn
  split_ifs <;> simp

theorem turnCoef_norm (a b a' b' : Fin 3) : ‖turnCoef a b a' b'‖ ≤ 2 := by
  unfold turnCoef
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(if a' = a then (frameTurn b' b : ℂ) else 0)‖ ≤ 1 := by
    split_ifs
    · exact frameTurn_norm _ _
    · simp
  have h2 : ‖(if b' = b then (frameTurn a' a : ℂ) else 0)‖ ≤ 1 := by
    split_ifs
    · exact frameTurn_norm _ _
    · simp
  linarith

theorem sum_sq_le (x : Fin 3 → Fin 3 → ℂ) :
    (∑ a' : Fin 3, ∑ b' : Fin 3, ‖x a' b'‖) ^ 2 ≤ 9 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖x a' b'‖ ^ 2 := by
  rw [← Fintype.sum_prod_type' (fun i j => ‖x i j‖), ← Fintype.sum_prod_type' (fun i j => ‖x i j‖ ^ 2)]
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3 × Fin 3))) (f := fun q => ‖x q.1 q.2‖)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  norm_num at h
  exact h

theorem add_sq_le (u w : ℂ) : ‖u + w‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_add_le u w
  have h0 := norm_nonneg (u + w)
  nlinarith [mul_le_mul h h h0 (by positivity : (0 : ℝ) ≤ ‖u‖ + ‖w‖), sq_nonneg (‖u‖ - ‖w‖)]

theorem comb_bound (k : ℝ) (a b : Fin 3) (x : Fin 3 → Fin 3 → ℂ) :
    k ^ 2 * ‖x a b‖ ^ 2 ≤ 2 * ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * x a' b'‖ ^ 2 +
      72 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖x a' b'‖ ^ 2 := by
  set T := ∑ a' : Fin 3, ∑ b' : Fin 3, turnCoef a b a' b' * x a' b'
  have hT : ‖T‖ ≤ 2 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖x a' b'‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a' _ => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (turnCoef_norm a b a' b') (norm_nonneg _)
  have hT2 : ‖T‖ ^ 2 ≤ 36 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖x a' b'‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hT 2
    have h2 := sum_sq_le x
    nlinarith
  have hk : ‖Complex.I * (k : ℂ) * x a b‖ ^ 2 = k ^ 2 * ‖x a b‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← hk, comb_split k a b x]
  refine (add_sq_le _ _).trans ?_
  linarith

theorem sum2_enorm (f : Fin 3 → Fin 3 → ℂ) :
    ENNReal.ofReal (∑ a' : Fin 3, ∑ b' : Fin 3, ‖f a' b'‖ ^ 2) = ∑ a' : Fin 3, ∑ b' : Fin 3, ‖f a' b'‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  simp only [sq_enorm]

theorem rect_pos_ae (K : CellBox) (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
  have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
    rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) by ext p; simp,
      Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull), ae_restrict_mem (rect_meas K)]
    with p hp hm
  exact lt_of_le_of_ne (hK.r_order.1.trans hm.1.1) (fun h => hp h.symm)

open Breakdown.CellCert.CellEnergy.Internal.AngularFrame in
theorem angular_ae (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    ∀ᵐ p ∂(volume.restrict K.rect), angularGradMode m n H a b p =
      ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p := by
  have lG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hs.measurable_gradient i) hs.gradient_two fun y => G_sq_le (G y) i
  have lH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hs.measurable_second j i) hs.second_two fun y => H_sq_le (H y) j i
  have lf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hs.measurable_gradient i).inner aestronglyMeasurable_const)
      hs.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have ls : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hs.measurable_second j i).inner aestronglyMeasurable_const)
      hs.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have lg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun C hC => ((ls j i l).integrableOn_isCompact hC).smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hs.weak_second φ hφ i j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have i1 := (lG i).integrable_smul_left_of_hasCompactSupport hd hsupp
    have i2 := (lH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    have e1 : ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
      rw [← L.integral_comp_comm i1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [L, innerSL_apply_apply, real_inner_comm]
    have e2 : ∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) =
        L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by
      rw [← L.integral_comp_comm i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [gv_inner]
      simp [L, innerSL_apply_apply, real_inner_comm]
    rw [e1, e2, hw, map_neg]
  have hC := fun i l => Breakdown.CellCert.CellEnergy.circleWeak (fun y => inner ℝ (G y (unitVector i)) (unitVector l))
    (fun y => gv (H y) i l) (lf i l) (lg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hC i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hC i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  filter_upwards [ae_restrict_of_ae hint, ae_restrict_of_ae hid, rect_pos_ae K hK] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2) (fun i l => h2 i l hr)

theorem grad_part (K : CellBox) (hK : IsCellBox K) {m : ℕ} (hm : 1 ≤ m) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (a b : Fin 3) :
    Summable (fun n : ℤ =>
      (1 + modeNumber m n ^ 2) * ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2) := by
  obtain ⟨C, hC0, hw⟩ := weight_le K hK
  have hG2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hs.measurable_gradient).2 ((hs.gradient_two.const_mul 3).mono'
      ((hs.measurable_gradient.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact EmbedWeak.Internal.norm_sq_le (G y)
  have hH2 : MemLp H 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hs.measurable_second).2 ((hs.second_two.const_mul 9).mono'
      ((hs.measurable_second.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ModeSquareIntegrable.Internal.bil_norm_sq_le (H y)
  have fG : ∫⁻ y, ‖G y‖ₑ ^ 2 < ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hs.measurable_gradient).1 hG2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi
  have fH : ∫⁻ y, ‖H y‖ₑ ^ 2 < ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hs.measurable_second).1 hH2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi
  set g : Space → ENNReal := fun y => ‖G y‖ₑ ^ 2 + ‖H y‖ₑ ^ 2 with hg_def
  have hg : AEMeasurable g volume :=
    (hs.measurable_gradient.enorm.pow_const 2).add (hs.measurable_second.enorm.pow_const 2)
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_add_left' (hs.measurable_gradient.enorm.pow_const 2)]
    exact ENNReal.add_lt_top.2 ⟨fG, fH⟩
  set c : ENNReal := ENNReal.ofReal (1 / (2 * π)) with hc
  set c2 : ENNReal := ENNReal.ofReal (2 * K.r₂ ^ 2) with hc2
  set c72 : ENNReal := ENNReal.ofReal 72 with hc72
  set D : ENNReal := (1 + c2 + c72 * 9) * c with hD_def
  have hD : D ≠ ⊤ := by
    rw [hD_def]
    refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)⟩
  have hid : ∀ᵐ p ∂(volume.restrict K.rect), ∀ n : ℤ, angularGradMode m n H a b p =
      ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p :=
    ae_all_iff.2 fun n => angular_ae K hK hs n a b
  have hsum := summable_of_bound K
    (fun n p => (1 + modeNumber m n ^ 2) * (K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2))
    (fun n => (gm_sq K hK m n hs.measurable_gradient hs.gradient_two a b).const_mul _)
    (fun n p hp => mul_nonneg (by positivity) (mul_nonneg (hw p hp).1 (by positivity)))
    (fun p => ENNReal.ofReal (K.lineWeight p.1) * (D * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)))
    (fin_bound K hK g hg hfin D hD) fun S => ?_
  · exact hsum.congr fun n => integral_const_mul _ _
  filter_upwards [hid, ae_restrict_mem (rect_meas K)] with p hp hmem
  have hw0 := (hw p hmem).1
  have hp1 : 0 ≤ p.1 := hK.r_order.1.trans hmem.1.1
  have hr : p.1 ^ 2 ≤ K.r₂ ^ 2 := pow_le_pow_left₀ hp1 hmem.1.2 2
  have hpt : ∀ n : ℤ, ENNReal.ofReal ((1 + modeNumber m n ^ 2) * (K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2))
      ≤ ENNReal.ofReal (K.lineWeight p.1) * (‖gradMode m n G a b p‖ₑ ^ 2 + c2 * ‖modeThird m n H a b 1 p‖ₑ ^ 2 +
        c72 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖gradMode m n G a' b' p‖ₑ ^ 2) := by
    intro n
    have hb := comb_bound (azimuth m n) a b (fun a' b' => gradMode m n G a' b' p)
    rw [← hp n] at hb
    have hA : ‖angularGradMode m n H a b p‖ ^ 2 ≤ K.r₂ ^ 2 * ‖modeThird m n H a b 1 p‖ ^ 2 := by
      rw [angularGradMode, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hr (by positivity)
    have hk : modeNumber m n ^ 2 = azimuth m n ^ 2 := sq_abs _
    have hreal : (1 + modeNumber m n ^ 2) * ‖gradMode m n G a b p‖ ^ 2 ≤
        ‖gradMode m n G a b p‖ ^ 2 + 2 * K.r₂ ^ 2 * ‖modeThird m n H a b 1 p‖ ^ 2 +
          72 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖gradMode m n G a' b' p‖ ^ 2 := by
      rw [hk]
      nlinarith [hb, hA]
    calc ENNReal.ofReal ((1 + modeNumber m n ^ 2) * (K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2))
        = ENNReal.ofReal (K.lineWeight p.1) *
            ENNReal.ofReal ((1 + modeNumber m n ^ 2) * ‖gradMode m n G a b p‖ ^ 2) := by
          rw [← ENNReal.ofReal_mul hw0]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (K.lineWeight p.1) * ENNReal.ofReal (‖gradMode m n G a b p‖ ^ 2 +
            2 * K.r₂ ^ 2 * ‖modeThird m n H a b 1 p‖ ^ 2 +
            72 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖gradMode m n G a' b' p‖ ^ 2) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hreal)
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := 2 * K.r₂ ^ 2) (by positivity), ENNReal.ofReal_mul (p := 72) (by norm_num),
            sq_enorm, sq_enorm,
            sum2_enorm (fun a' b' => gradMode m n G a' b' p)]
  set EG := ∫⁻ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ₑ ^ 2
  set EH := ∫⁻ θ in Ioo (-π) π, ‖H (cylPoint p.1 θ p.2)‖ₑ ^ 2
  set Eg := ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)
  have hGg : EG ≤ Eg := lintegral_mono fun θ => le_self_add
  have hHg : EH ≤ Eg := lintegral_mono fun θ => le_add_self
  have hW : ∑ n ∈ S, ∑ a' : Fin 3, ∑ b' : Fin 3, ‖gradMode m n G a' b' p‖ₑ ^ 2 =
      ∑ a' : Fin 3, ∑ b' : Fin 3, ∑ n ∈ S, ‖gradMode m n G a' b' p‖ₑ ^ 2 :=
    Finset.sum_comm.trans (Finset.sum_congr rfl fun a' _ => Finset.sum_comm)
  calc ∑ n ∈ S, ENNReal.ofReal ((1 + modeNumber m n ^ 2) * (K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2))
      ≤ ∑ n ∈ S, ENNReal.ofReal (K.lineWeight p.1) * (‖gradMode m n G a b p‖ₑ ^ 2 +
          c2 * ‖modeThird m n H a b 1 p‖ₑ ^ 2 +
          c72 * ∑ a' : Fin 3, ∑ b' : Fin 3, ‖gradMode m n G a' b' p‖ₑ ^ 2) := Finset.sum_le_sum fun n _ => hpt n
    _ = ENNReal.ofReal (K.lineWeight p.1) * (∑ n ∈ S, ‖gradMode m n G a b p‖ₑ ^ 2 +
          c2 * ∑ n ∈ S, ‖modeThird m n H a b 1 p‖ₑ ^ 2 +
          c72 * ∑ a' : Fin 3, ∑ b' : Fin 3, ∑ n ∈ S, ‖gradMode m n G a' b' p‖ₑ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hW]
    _ ≤ ENNReal.ofReal (K.lineWeight p.1) * (c * Eg + c2 * (c * Eg) + c72 * ∑ _a' : Fin 3, ∑ _b' : Fin 3, c * Eg) := by
        gcongr
        · exact (gm_sum hm S G a b p).trans (mul_le_mul' le_rfl hGg)
        · exact (mt_sum hm S H a b 1 p).trans (mul_le_mul' le_rfl hHg)
        · exact (gm_sum hm S G _ _ p).trans (mul_le_mul' le_rfl hGg)
    _ = ENNReal.ofReal (K.lineWeight p.1) * (D * Eg) := by
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hD_def]
        push_cast
        ring

end Breakdown.CellCert.CellAnalysis.SharpDensityModeSeries.Internal

namespace Breakdown.CellCert.CellAnalysis

open SharpDensityModeSeries.Internal in
theorem modeSeries_holds : ModeSeriesStatement := by
  intro K hK m hm v G H hs
  exact ⟨fun a => vel_part K hK hm hs a, fun a b => grad_part K hK hm hs a b⟩

end Breakdown.CellCert.CellAnalysis
