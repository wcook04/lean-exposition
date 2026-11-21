import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.LabelRowProfileSsp
import Breakdown.CertCell.LabelRowProfilePressure
import Breakdown.CertCell.TailAngularPlane
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.LowEntry

open MeasureTheory Set Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.LabelRowProfile

open TailBand.Internal.AngularPlane Coercive.Internal.ModeRotation

theorem vel_meas {f : ℝ → Space → Space} (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (m : ℕ) (ι : ℤ × ℤ) (i : Fin 3) :
    AEStronglyMeasurable (fun p => labelVel m ι f p i) (volume.restrict CertCell.halfPlane) := by
  have hΦ : Continuous (fun q : ℝ × Space => axialRot (-q.1) q.2 i) := by
    unfold axialRot
    fun_prop
  have h := (aestronglyMeasurable_orbitAverage hf (labelHarmonic m ι)
    (fun φ x => axialRot (-φ) x i) hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [labelVel, modeVel, modeAverage_eq, zero_add]

theorem grad_meas {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (m : ℕ) (ι : ℤ × ℤ) (ij : Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun p => labelGrad m ι G p ij) (volume.restrict CertCell.halfPlane) := by
  have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ij.2))) ij.1) := by
    unfold axialRot
    fun_prop
  have h := (aestronglyMeasurable_orbitAverage hG (labelHarmonic m ι)
    (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ij.2))) ij.1) hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [labelGrad, modeGrad, modeAverage_eq, zero_add]

theorem secondDeriv_meas {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (m : ℕ) (ι : ℤ × ℤ)
    (ijl : Fin 3 × Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun p => labelHess m ι H p ijl) (volume.restrict CertCell.halfPlane) := by
  have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
    unfold axialRot
    fun_prop
  have h := (aestronglyMeasurable_orbitAverage hH (labelHarmonic m ι)
    (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1)
    hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [labelHess, modeSecondDeriv, modeAverage_eq, zero_add]

theorem rect_le_half (K : CellBox) (hK : IsCellBox K) :
    volume.restrict K.rect ≤ volume.restrict CertCell.halfPlane := by
  refine Measure.restrict_mono_ae ?_
  have hsub : K.rect ⊆ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := fun p hp =>
    ⟨le_trans hK.r_order.1 hp.1.1, le_trans hK.z_order.1 hp.2.1⟩
  refine hsub.eventuallyLE.trans ?_
  have e : (CertCell.halfPlane : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) :=
    Measure.set_prod_ae_eq Ioi_ae_eq_Ici Ioi_ae_eq_Ici
  exact e.symm.le

theorem coord_two {f : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {μ : Measure (ℝ × ℝ)}
    (h : ∀ a b, AEStronglyMeasurable (fun p => f p a b) μ) : AEStronglyMeasurable f μ :=
  (aemeasurable_pi_iff.2 fun a => aemeasurable_pi_iff.2 fun b => (h a b).aemeasurable).aestronglyMeasurable

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem wsq_le {K : CellBox} (hK : IsCellBox K) {F A B : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hA : IntegrableOn (fun p => p.1 * ‖A p‖ ^ 2) K.rect) (hB : IntegrableOn (fun p => p.1 * ‖B p‖ ^ 2) K.rect)
    (hle : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 → ‖F p‖ ≤ ‖A p‖ + ‖B p‖) :
    IntegrableOn (fun p => p.1 * ‖F p‖ ^ 2) K.rect := by
  refine ((hA.add hB).const_mul 2).mono' (continuous_fst.aestronglyMeasurable.mul (hF.norm.pow 2)) ?_
  filter_upwards [hle, ae_restrict_mem (rect_meas K)] with p hp hm
  have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hm.1.1
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity)]
  rcases h0.eq_or_lt with h | h
  · rw [← h]
    simp
  · have h1 := hp h
    have hA0 := norm_nonneg (A p)
    have hB0 := norm_nonneg (B p)
    have hF0 := norm_nonneg (F p)
    have h2 : ‖F p‖ ^ 2 ≤ 2 * (‖A p‖ ^ 2 + ‖B p‖ ^ 2) := by
      nlinarith [sq_nonneg (‖A p‖ - ‖B p‖)]
    have h3 := mul_le_mul_of_nonneg_left h2 h.le
    linarith

theorem norm_lift (A B : ℂ) : ‖A + Complex.I * B‖ ≤ ‖A‖ + ‖B‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]

theorem wsq_of_lineWeight {K : CellBox} (hK : IsCellBox K) {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict K.rect))
    (h : IntegrableOn (fun p => K.lineWeight p.1 * ‖f p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => p.1 * ‖f p‖ ^ 2) K.rect := by
  refine (h.const_mul (K.r₂ + 1)).mono' (continuous_fst.aestronglyMeasurable.mul (hf.norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have h2 : p.1 ≤ K.r₂ := hp.1.2
  have hr2 : 0 ≤ K.r₂ := by linarith [hK.r_order.1, hK.r_order.2]
  have hs := sq_nonneg ‖f p‖
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hax : K.r₁ = 0
  · rw [CellBox.lineWeight, if_pos hax]
    nlinarith [mul_nonneg hr2 (mul_nonneg h0 hs)]
  · rw [CellBox.lineWeight, if_neg hax, one_mul]
    nlinarith [mul_nonneg (by linarith : 0 ≤ K.r₂ + 1 - p.1) hs]

open CellAnalysis.LowEntry.Internal CellAnalysis.ModeGradSquare.Internal in
theorem wsq_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : CellBox} (hK : IsCellBox K)
    {X : Space → E} (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℂ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖)
    (hloc : IntegrableOn (fun y => ‖X y‖ ^ 2) (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖(1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2))‖ ^ 2) K.rect := by
  set S := Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂) with hS
  set g : Space → ENNReal := S.indicator (fun y => ‖X y‖ₑ ^ 2) with hg_def
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2))) (volume.restrict K.rect) :=
    ((meas_gen hX φ hφc).mono_measure (hle K hK)).const_mul _
  refine ⟨continuous_fst.aestronglyMeasurable.mul (hmeas.norm.pow 2), ?_⟩
  set c0 : ENNReal := ‖(1 / (2 * Real.pi) : ℂ)‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) with hc0
  have hc0t : c0 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) ENNReal.ofReal_ne_top
  have hpt : ∀ p ∈ K.rect, ‖p.1 * ‖(1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2))‖ ^ 2‖ₑ ≤
      c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2)) := by
    intro p hp
    have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
    have hk : ∫⁻ θ in Ioo (-Real.pi) Real.pi, ‖φ θ (X (cylPoint p.1 θ p.2))‖ₑ ^ 2 ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2) := by
      refine lintegral_mono fun θ => ?_
      have hin : cylPoint p.1 θ p.2 ∈ S := by
        rw [hS, mem_closedBall_zero_iff]
        refine (cylPoint_norm p.1 θ p.2).trans ?_
        rw [abs_of_nonneg hr0, abs_of_nonneg hz0]
        linarith [hp.1.2, hp.2.2]
      rw [hg_def, Set.indicator_of_mem hin]
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hφb θ _)
    rw [enorm_mul, enorm_pow, enorm_norm, enorm_mul, mul_pow, Real.enorm_eq_ofReal hr0]
    calc ENNReal.ofReal p.1 * (‖(1 / (2 * Real.pi) : ℂ)‖ₑ ^ 2 *
          ‖∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ^ 2)
        ≤ ENNReal.ofReal p.1 * (‖(1 / (2 * Real.pi) : ℂ)‖ₑ ^ 2 *
          (ENNReal.ofReal (2 * Real.pi) * ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2))) := by
          gcongr
          exact (int_sq_le _).trans (mul_le_mul' le_rfl hk)
      _ = c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2)) := by
          rw [hc0]; ring
  have hgm : AEMeasurable g volume := (hX.enorm.pow_const 2).indicator measurableSet_closedBall
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_indicator measurableSet_closedBall]
    have hi := hloc.2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (b := c0 * ∫⁻ y, g y) ?_ (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc0t) hfin)
  calc ∫⁻ p in K.rect, ‖p.1 * ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2))‖ ^ 2‖ₑ
      ≤ ∫⁻ p in K.rect, c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2)) :=
        setLIntegral_mono' (rect_meas K) hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (cylPoint p.1 θ p.2)) :=
        lintegral_mono' (hle K hK) le_rfl
    _ = c0 * ∫⁻ y, g y := by rw [lintegral_const_mul' _ _ hc0t, hint]

open CellAnalysis.LowEntry.Internal in
theorem vec_sq {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) {f : Space → Space}
    (hm : AEStronglyMeasurable f volume)
    (hloc : ∀ R : ℝ, IntegrableOn (fun y => ‖f y‖ ^ 2) (Metric.closedBall (0 : Space) R)) (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n f p.1 p.2 a‖ ^ 2) K.rect := by
  have h := wsq_circle hK hm (velKernel m n a) (velKernel_cont m n a) (velKernel_bound m n a) (hloc _)
  refine h.congr_fun (fun p _ => ?_) (rect_meas K)
  rw [modeVec_eq]

open CellAnalysis.LowEntry.Internal in
theorem vec_meas {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) {f : Space → Space}
    (hm : AEStronglyMeasurable f volume) (a : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n f p.1 p.2 a) (volume.restrict K.rect) := by
  have h := ((CellAnalysis.ModeGradSquare.Internal.meas_gen hm (velKernel m n a) (velKernel_cont m n a)).mono_measure
    (CellAnalysis.ModeGradSquare.Internal.hle K hK)).const_mul (1 / (2 * Real.pi) : ℂ)
  exact h.congr (Eventually.of_forall fun p => (modeVec_eq m n f a p).symm)

theorem sq_ball_of_six {f : Space → Space} (hf : MemLp f 6 volume) (R : ℝ) :
    IntegrableOn (fun y => ‖f y‖ ^ 2) (Metric.closedBall (0 : Space) R) := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h2 : MemLp f 2 (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    (hf.restrict _).mono_exponent (by norm_num)
  exact (memLp_two_iff_integrable_sq_norm h2.1).1 h2

theorem harmonicMode_label (ι : ℤ × ℤ) : harmonicMode (labelTime ι) ι.1 = ι := by
  refine Prod.ext rfl ?_
  simp only [harmonicMode, labelTime]
  omega

theorem even_label (ι : ℤ × ℤ) : Even (ι.1 + labelTime ι) := ⟨ι.2, by simp only [labelTime]; ring⟩

theorem profile_measurable (K : CellBox) (hK : IsCellBox K) (m : ℕ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ) :
    (∀ a, AEStronglyMeasurable (fun p => velAt m ι v a p) (volume.restrict K.rect)) ∧
    (∀ a b, AEStronglyMeasurable (fun p => gradAt m ι G a b p) (volume.restrict K.rect)) ∧
    (∀ a b c, AEStronglyMeasurable (fun p => slopeAt m ι H a b c p) (volume.restrict K.rect)) ∧
    (∀ a, AEStronglyMeasurable (fun p => velAt m ι Pg a p) (volume.restrict K.rect)) :=
  ⟨fun a => (vel_meas hv.measurable_velocity m ι a).mono_measure (rect_le_half K hK),
    fun a b => (grad_meas hv.measurable_gradient m ι (a, b)).mono_measure (rect_le_half K hK),
    fun a b c => (secondDeriv_meas hv.measurable_secondDeriv m ι (a, c, b)).mono_measure (rect_le_half K hK),
    fun a => (vel_meas hp.measurable m ι a).mono_measure (rect_le_half K hK)⟩

open CellAnalysis.ModeGradSquare.Internal CellAnalysis.ModeSquareIntegrable.Internal in
theorem profile_integrable (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ) :
    IntegrableOn (fun p => p.1 * (cnormSq (velArray m ι v p) + ∑ a : Fin 3, cnormSq (gradArray m ι G p a)
      + cnormSq (fun a => ∑ c : Fin 3, slopeAt m ι H a c c p) + cnormSq (velArray m ι Pg p))) K.rect := by
  obtain ⟨mV, mG, mS, mP⟩ := profile_measurable K hK m v G H Pg hv hp ι
  obtain ⟨hc, hs, hprof⟩ := h1 m v G H hv (labelTime ι)
  have hpr := hprof ι.1 (even_label ι)
  rw [harmonicMode_label] at hpr
  have hpp := h2 m Pg hp (labelTime ι) ι.1 (even_label ι)
  rw [harmonicMode_label] at hpp
  obtain ⟨⟨_, _, hQc, hQcm, _⟩, ⟨_, _, hQs, hQsm, _⟩⟩ := hp.harmonic_gradient (labelTime ι)
  have hV : ∀ a, IntegrableOn (fun p => p.1 * ‖velAt m ι v a p‖ ^ 2) K.rect := fun a =>
    wsq_le hK (mV a) (vec_sq hK m ι.1 hc.measurable_velocity (sq_ball_of_six hc.velocity_six) a)
      (vec_sq hK m ι.1 hs.measurable_velocity (sq_ball_of_six hs.velocity_six) a)
      (by
        filter_upwards [ae_restrict_of_ae hpr] with p hq hpos
        rw [(hq hpos).1 a]
        exact norm_lift _ _)
  have hG : ∀ a b, IntegrableOn (fun p => p.1 * ‖gradAt m ι G a b p‖ ^ 2) K.rect := fun a b =>
    wsq_le hK (mG a b)
      (wsq_of_lineWeight hK (gm_meas K hK m ι.1 hc.measurable_gradient a b)
        (gm_sq K hK m ι.1 hc.measurable_gradient hc.gradient_two a b))
      (wsq_of_lineWeight hK (gm_meas K hK m ι.1 hs.measurable_gradient a b)
        (gm_sq K hK m ι.1 hs.measurable_gradient hs.gradient_two a b))
      (by
        filter_upwards [ae_restrict_of_ae hpr] with p hq hpos
        rw [(hq hpos).2.1 a b]
        exact norm_lift _ _)
  have hS : ∀ a c, IntegrableOn (fun p => p.1 * ‖slopeAt m ι H a c c p‖ ^ 2) K.rect := fun a c =>
    wsq_le hK (mS a c c) (th_sq K hK m ι.1 hc.measurable_second hc.second_two a c c)
      (th_sq K hK m ι.1 hs.measurable_second hs.second_two a c c)
      (by
        filter_upwards [ae_restrict_of_ae hpr] with p hq hpos
        rw [(hq hpos).2.2 a c c]
        exact norm_lift _ _)
  have hL : ∀ a, IntegrableOn (fun p => p.1 * ‖∑ c : Fin 3, slopeAt m ι H a c c p‖ ^ 2) K.rect := by
    intro a
    simp only [Fin.sum_univ_three]
    have h01 := wsq_le hK ((mS a 0 0).add (mS a 1 1)) (hS a 0) (hS a 1)
      (Eventually.of_forall fun p _ => norm_add_le _ _)
    exact wsq_le hK (((mS a 0 0).add (mS a 1 1)).add (mS a 2 2)) h01 (hS a 2)
      (Eventually.of_forall fun p _ => norm_add_le _ _)
  have hP : ∀ a, IntegrableOn (fun p => p.1 * ‖velAt m ι Pg a p‖ ^ 2) K.rect := fun a =>
    wsq_le hK (mP a) (vec_sq hK m ι.1 hQcm (fun R => hQc _ (isCompact_closedBall _ R)) a)
      (vec_sq hK m ι.1 hQsm (fun R => hQs _ (isCompact_closedBall _ R)) a)
      (by
        filter_upwards [ae_restrict_of_ae hpp] with p hq hpos
        rw [hq hpos a]
        exact norm_lift _ _)
  have e : (fun p : ℝ × ℝ => p.1 * (cnormSq (velArray m ι v p) + ∑ a : Fin 3, cnormSq (gradArray m ι G p a)
      + cnormSq (fun a => ∑ c : Fin 3, slopeAt m ι H a c c p) + cnormSq (velArray m ι Pg p))) =
      fun p => ∑ a : Fin 3, p.1 * ‖velAt m ι v a p‖ ^ 2 + ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ‖gradAt m ι G a b p‖ ^ 2
        + ∑ a : Fin 3, p.1 * ‖∑ c : Fin 3, slopeAt m ι H a c c p‖ ^ 2 + ∑ a : Fin 3, p.1 * ‖velAt m ι Pg a p‖ ^ 2 := by
    funext p
    simp only [cnormSq, velArray, gradArray, mul_add, Finset.mul_sum]
  rw [e]
  exact (((integrable_finsetSum _ fun a _ => hV a).add
    (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hG a b)).add
    (integrable_finsetSum _ fun a _ => hL a)).add (integrable_finsetSum _ fun a _ => hP a)

theorem profile_valid_of_parts (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ)
    (hlap : ∀ φ : Fin 3 → CellPoly, IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ →
      rowPairing K (labelRowProfile K m ι v G H Pg).lap φ
        = rowBoundaryGrad K (labelRowProfile K m ι v G H Pg) φ - ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3,
          ∑ b : Fin 3, (labelRowProfile K m ι v G H Pg).grad p a b
            * (starRingEnd ℂ) (testGrad K (labelAzimuth m ι : ℝ) φ p a b))
    (hpres : ∀ φ : Fin 3 → CellPoly, IsTestSolenoidal K (labelAzimuth m ι : ℝ) φ →
      IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ →
      rowPairing K (labelRowProfile K m ι v G H Pg).presGrad φ
        = rowBoundaryPres K (labelRowProfile K m ι v G H Pg) φ) :
    IsRowProfile K (labelAzimuth m ι : ℝ) (labelRowProfile K m ι v G H Pg) := by
  obtain ⟨mV, mG, mS, mP⟩ := profile_measurable K hK m v G H Pg hv hp ι
  refine ⟨⟨aestronglyMeasurable_of_coord fun a => mV a, coord_two fun a b => mG a b,
    aestronglyMeasurable_of_coord fun a => ?_, aestronglyMeasurable_of_coord fun a => mP a⟩,
    profile_integrable h1 h2 K hK m v G H Pg hv hp ι, hlap, hpres⟩
  show AEStronglyMeasurable (fun p => ∑ c : Fin 3, slopeAt m ι H a c c p) (volume.restrict K.rect)
  simp only [Fin.sum_univ_three]
  exact ((mS a 0 0).add (mS a 1 1)).add (mS a 2 2)

end Internal.LabelRowProfile

theorem labelRowProfile_valid (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ) (hax : K.IsAxis → ι.1 = 0) :
    IsRowProfile K (labelAzimuth m ι : ℝ) (labelRowProfile K m ι v G H Pg) :=
  Internal.LabelRowProfile.profile_valid_of_parts h1 h2 K hK m v G H Pg hv hp ι
    (fun φ hφ => labelRowProfile_sumSecondPartials h1 K hK m v G H Pg hv ι hax φ hφ)
    (fun φ hs hφ => labelRowProfile_pressure h2 K hK m v G H Pg hp ι hax φ hs hφ)

theorem labelRowProfile_holds (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement) :
    LabelRowProfileStatement := by
  intro K hK m v G H Pg hv hp ι hax
  exact ⟨labelRowProfile K m ι v G H Pg, labelRowProfile_valid h1 h2 K hK m v G H Pg hv hp ι hax,
    fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

end CellCalculus

end CertCell

end Breakdown
