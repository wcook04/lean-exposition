import Breakdown.FracCell.DensitySlice
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.CellDensityModesTurn

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FracInternal.CircleSliceRegular

open CellCert CellAnalysis SteadyCert Assembly
open CellAnalysis.LowEntry.Internal CellAnalysis.ModeGradSquare.Internal
open CellAnalysis.ModeSquareIntegrable.Internal FracInternal.DensitySlice

theorem per_ae {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π)) (s : ℝ)
    (h : ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)), f (θ + s) = f θ) :
    ∀ᵐ θ ∂volume, f (θ + s) = f θ := by
  have h1 : ∀ᵐ θ ∂volume, θ ∈ Ioo (-π) π → f (θ + s) = f θ :=
    (ae_restrict_iff' measurableSet_Ioo).1 h
  have h2 : ∀ᵐ θ ∂volume, θ ∉ ({π} : Set ℝ) := measure_eq_zero_iff_ae_notMem.1 (measure_singleton π)
  have hQ := h1.and h2
  have h3 : ∀ n : ℤ, ∀ᵐ θ ∂volume, (θ - n • (2 * π) ∈ Ioo (-π) π →
      f (θ - n • (2 * π) + s) = f (θ - n • (2 * π))) ∧ θ - n • (2 * π) ∉ ({π} : Set ℝ) :=
    fun n => (measurePreserving_sub_right volume (n • (2 * π))).quasiMeasurePreserving.ae hQ
  filter_upwards [ae_all_iff.2 h3] with θ hθ
  set n : ℤ := toIocDiv two_pi_pos (-π) θ with hn
  have hm := toIocMod_mem_Ioc two_pi_pos (-π) θ
  rw [← self_sub_toIocDiv_zsmul, ← hn] at hm
  obtain ⟨hq1, hq2⟩ := hθ n
  have hne : θ - n • (2 * π) ≠ π := fun e => hq2 (by rw [e]; rfl)
  have hin : θ - n • (2 * π) ∈ Ioo (-π) π := ⟨hm.1, lt_of_le_of_ne (by linarith [hm.2]) hne⟩
  have e1 := hq1 hin
  have e2 : f (θ + s - n • (2 * π)) = f (θ + s) := hper.sub_zsmul_eq n
  have e3 : f (θ - n • (2 * π)) = f θ := hper.sub_zsmul_eq n
  rw [← e2, ← e3, ← e1]
  congr 1
  ring

theorem per_memLp {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (h : MemLp f 2 (volume.restrict (Ioo (-π) π))) : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))) := by
  have h' : MemLp f 2 (volume.restrict (Ioc (-π) π)) := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
  have hi1 : IntegrableOn f (Ioc (-π) π) := h'.integrable (by norm_num)
  have hi2 : IntegrableOn (fun θ => ‖f θ‖ ^ 2) (Ioc (-π) π) := (memLp_two_iff_integrable_sq_norm h'.1).1 h'
  have hle : -π ≤ -π + 2 * π := by linarith [pi_pos]
  have e : -π + 2 * π = π := by ring
  have j1 : IntervalIntegrable f volume (-π) (-π + 2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 (by rw [e]; exact hi1)
  have j2 : IntervalIntegrable (fun θ => ‖f θ‖ ^ 2) volume (-π) (-π + 2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 (by rw [e]; exact hi2)
  have hper2 : Function.Periodic (fun θ => ‖f θ‖ ^ 2) (2 * π) := fun θ => by simp only [hper θ]
  have k1 := hper.intervalIntegrable two_pi_pos.ne' j1 0 (2 * π)
  have k2 := hper2.intervalIntegrable two_pi_pos.ne' j2 0 (2 * π)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le] at k1 k2
  exact (memLp_two_iff_integrable_sq_norm k1.aestronglyMeasurable).2 k2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slice_meas {K : CellBox} (hK : IsCellBox K) {X : Space → E} (hXm : AEStronglyMeasurable X volume)
    (φ : ℝ → E → ℝ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      AEStronglyMeasurable (fun θ => φ θ (X (cylPoint p.1 θ p.2))) (volume.restrict (Ioo (-π) π)) := by
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hXm.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  exact ae_mono (hle K hK) hf.prodMk_left

theorem cyl_solid {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have hz : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  have hr : cylRadius (cylPoint p.1 θ p.2) = p.1 := by
    unfold cylRadius
    have e : (cylPoint p.1 θ p.2) 0 ^ 2 + (cylPoint p.1 θ p.2) 1 ^ 2 = p.1 ^ 2 := by
      simp [cylPoint]
      linear_combination p.1 ^ 2 * Real.sin_sq_add_cos_sq θ
    rw [e, Real.sqrt_sq h0]
  have hh : cylHeight (cylPoint p.1 θ p.2) = p.2 := by simp [cylHeight, cylPoint]
  simp only [CellBox.solid, Set.mem_ofPred_eq, hr, hh, abs_of_nonneg hz]
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

theorem slice_gen {K : CellBox} (hK : IsCellBox K) {X : Space → E} (hXm : AEStronglyMeasurable X volume)
    (hX : MemLp X 2 (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))))
    (φ : ℝ → E → ℝ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, |φ θ e| ≤ ‖e‖)
    (hφp : ∀ θ e, φ (θ + 2 * π) e = φ θ e) :
    ∀ᵐ p ∂(volume.restrict K.rect), MemLp (fun θ => φ θ (X (cylPoint p.1 θ p.2))) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
  set R : ℝ := 2 * K.r₂ + K.z₂ with hR
  set g : Space → ENNReal := (Metric.closedBall (0 : Space) R).indicator (fun y => ‖X y‖ₑ ^ 2) with hg_def
  have hgm : AEMeasurable g volume := (hXm.enorm.pow_const 2).indicator measurableSet_closedBall
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_indicator measurableSet_closedBall]
    have hi := ((memLp_two_iff_integrable_sq_norm hX.1).1 hX).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi
  have hgq : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => g (cylArg q))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp)
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul hgq
  have hF : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable.mul hgq.lintegral_prod_right'
  have h1 : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) < ⊤ :=
    ae_lt_top' hF (by rw [hint]; exact hfin.ne)
  have h2 : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)
  have h4 : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ K.rect := ae_restrict_mem (rect_meas K)
  filter_upwards [ae_mono (hle K hK) (h1.and h2), h4, slice_meas hK hXm φ hφc] with p hp hp4 hm
  obtain ⟨hp1, hp2⟩ := hp
  have hpos : 0 < p.1 := hp2.1
  have hball : ∀ θ, cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) R := by
    intro θ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (cylPoint_norm _ _ _).trans ?_
    have h1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp4.1.1
    have h2 : 0 ≤ p.2 := le_trans hK.z_order.1 hp4.2.1
    rw [abs_of_nonneg h1, abs_of_nonneg h2, hR]
    linarith [hp4.1.2, hp4.2.2]
  have hI : ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne'] at hp1
    exact lt_irrefl _ hp1
  have hL : MemLp (fun θ => φ θ (X (cylPoint p.1 θ p.2))) 2 (volume.restrict (Ioo (-π) π)) := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (lintegral_mono fun θ => ?_) hI
    rw [hg_def, indicator_of_mem (hball θ), enorm_pow, enorm_norm]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hφb _ _)
  refine per_memLp (fun θ => ?_) hL
  show φ (θ + 2 * π) (X (cylPoint p.1 (θ + 2 * π) p.2)) = φ θ (X (cylPoint p.1 θ p.2))
  rw [cylPoint_per, hφp]

theorem slice_bdd {K : CellBox} (hK : IsCellBox K) {X : Space → E} (hXm : AEStronglyMeasurable X volume)
    (φ : ℝ → E → ℝ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2))
    (hφp : ∀ θ e, φ (θ + 2 * π) e = φ θ e) (C : ℝ)
    (hb : ∀ p ∈ K.rect, ∀ θ, |φ θ (X (cylPoint p.1 θ p.2))| ≤ C) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      AEStronglyMeasurable (fun θ => φ θ (X (cylPoint p.1 θ p.2))) (volume.restrict (Ioc 0 (2 * π))) := by
  filter_upwards [slice_meas hK hXm φ hφc, ae_restrict_mem (rect_meas K)] with p hm hp
  have hL : MemLp (fun θ => φ θ (X (cylPoint p.1 θ p.2))) 2 (volume.restrict (Ioo (-π) π)) :=
    MemLp.of_bound hm C (Filter.Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hb p hp θ)
  refine (per_memLp (fun θ => ?_) hL).1
  show φ (θ + 2 * π) (X (cylPoint p.1 (θ + 2 * π) p.2)) = φ θ (X (cylPoint p.1 θ p.2))
  rw [cylPoint_per, hφp]

theorem clm_memLp {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) : MemLp G 2 volume :=
  (memLp_two_iff_integrable_sq_norm hm).2 ((hi.const_mul 3).mono'
    ((hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact EmbedWeak.Internal.norm_sq_le (G y)))

theorem bil_memLp {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    MemLp H 2 volume :=
  (memLp_two_iff_integrable_sq_norm hm).2 ((hi.const_mul 9).mono'
    ((hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact bil_norm_sq_le (H y)))

end Breakdown.FracInternal.CircleSliceRegular

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly FracInternal.CircleSliceRegular FracInternal.DensitySlice
open LowEntry.Internal ModeSquareIntegrable.Internal

theorem circleSliceRegular_holds : CircleSliceRegularStatement := by
  intro α _ _ k N c hc K hK hw _ hsub x hx
  have hs := hx.1
  have hturn := gradientTurn c.order x.1 x.2.1 x.2.2.1 hs
  have hmem : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ K.rect := ae_restrict_mem (rect_meas K)
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hv2 : MemLp x.1 2 (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :=
    (hs.velocity_six.restrict _).mono_exponent (by norm_num)
  have hG2 := (clm_memLp hs.measurable_gradient hs.gradient_two).restrict
    (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))
  have hH2 := (bil_memLp hs.measurable_second hs.second_two).restrict
    (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))
  have hvL : ∀ a, ∀ᵐ p ∂(volume.restrict K.rect),
      MemLp (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) a) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    fun a => slice_gen hK hs.measurable_velocity hv2 (fun θ u => frameVec θ u a) (frameVec_cont a)
      (fun θ u => by rw [frameVec_eq]; exact inner_unit_bound θ u a) (fun θ u => frameVec_per θ u a)
  have hGL : ∀ a b, ∀ᵐ p ∂(volume.restrict K.rect),
      MemLp (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    fun a b => slice_gen hK hs.measurable_gradient hG2 (fun θ M => frameMat θ M a b) (frameMat_cont a b)
      (fun θ M => frameMat_bound θ M a b) (fun θ M => frameMat_per θ M a b)
  have hHL : ∀ a b d, ∀ᵐ p ∂(volume.restrict K.rect),
      MemLp (fun θ => frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) a b d) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    fun a b d => slice_gen hK hs.measurable_second hH2 (fun θ T => frameThird θ T a b d) (frameThird_cont a b d)
      (fun θ T => frameThird_bound θ T a b d) (fun θ T => frameThird_per θ T a b d)
  have hvP : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a, ∀ᵐ θ ∂volume,
      frameVec (θ + 2 * π / c.order) (x.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) a =
        frameVec θ (x.1 (cylPoint p.1 θ p.2)) a := by
    filter_upwards [slice_ae (P := fun y => x.1 (turnStep c.order y) = turnStep c.order (x.1 y))
      hs.symmetric.1 hK] with p hp a
    refine per_ae (f := fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) a) (fun θ => ?_) _ ?_
    · show frameVec (θ + 2 * π) (x.1 (cylPoint p.1 (θ + 2 * π) p.2)) a = _
      rw [cylPoint_per, frameVec_per]
    · filter_upwards [hp] with θ hθ
      show frameVec (θ + 2 * π / c.order) (x.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) a = _
      rw [← turn_cyl, hθ]
      exact frameVec_turn c.order θ rfl a
  have hGP : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b, ∀ᵐ θ ∂volume,
      frameMat (θ + 2 * π / c.order) (x.2.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) a b =
        frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b := by
    filter_upwards [slice_ae (P := fun y => ∀ u, x.2.1 (turnStep c.order y) (turnStep c.order u) =
      turnStep c.order (x.2.1 y u)) (hturn.mono fun y h => h.1) hK] with p hp a b
    refine per_ae (f := fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b) (fun θ => ?_) _ ?_
    · show frameMat (θ + 2 * π) (x.2.1 (cylPoint p.1 (θ + 2 * π) p.2)) a b = _
      rw [cylPoint_per, frameMat_per]
    · filter_upwards [hp] with θ hθ
      show frameMat (θ + 2 * π / c.order) (x.2.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) a b = _
      rw [← turn_cyl]
      exact frameMat_turn c.order θ hθ a b
  have hHP : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b d, ∀ᵐ θ ∂volume,
      frameThird (θ + 2 * π / c.order) (x.2.2.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) a b d =
        frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) a b d := by
    filter_upwards [slice_ae (P := fun y => ∀ u u', x.2.2.1 (turnStep c.order y) (turnStep c.order u)
      (turnStep c.order u') = turnStep c.order (x.2.2.1 y u u')) (hturn.mono fun y h => h.2) hK] with p hp a b d
    refine per_ae (f := fun θ => frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) a b d) (fun θ => ?_) _ ?_
    · show frameThird (θ + 2 * π) (x.2.2.1 (cylPoint p.1 (θ + 2 * π) p.2)) a b d = _
      rw [cylPoint_per, frameThird_per]
    · filter_upwards [hp] with θ hθ
      show frameThird (θ + 2 * π / c.order) (x.2.2.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) a b d = _
      rw [← turn_cyl]
      exact frameThird_turn c.order θ hθ a b d
  obtain ⟨C, hC⟩ := hc.model_bounded
  have hbS : ∀ p ∈ K.rect, ∀ θ, ‖c.modelStrain (cylPoint p.1 θ p.2)‖ ≤ C :=
    fun p hp θ => (hC _ (hsub (cyl_solid hK hp θ))).2.2.1
  have hbG : ∀ p ∈ K.rect, ∀ θ, ‖c.modelCurlGrad (cylPoint p.1 θ p.2)‖ ≤ C :=
    fun p hp θ => (hC _ (hsub (cyl_solid hK hp θ))).2.2.2
  have hSM : ∀ a b, ∀ᵐ p ∂(volume.restrict K.rect), AEStronglyMeasurable
      (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b) (volume.restrict (Ioc 0 (2 * π))) :=
    fun a b => slice_bdd hK hc.model_measurable.2.2.1 (fun θ M => frameMat θ M a b) (frameMat_cont a b)
      (fun θ M => frameMat_per θ M a b) C (fun p hp θ => (frameMat_bound _ _ a b).trans (hbS p hp θ))
  have hCM : ∀ a b, ∀ᵐ p ∂(volume.restrict K.rect), AEStronglyMeasurable
      (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b) (volume.restrict (Ioc 0 (2 * π))) :=
    fun a b => slice_bdd hK hc.model_measurable.2.2.2 (fun θ M => frameMat θ M a b) (frameMat_cont a b)
      (fun θ M => frameMat_per θ M a b) C (fun p hp θ => (frameMat_bound _ _ a b).trans (hbG p hp θ))
  have hAL : ∀ i a b, ∀ᵐ p ∂(volume.restrict K.rect), MemLp
      (fun θ => frameMat θ (c.modelActuatorGrad i (cylPoint p.1 θ p.2)) a b) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    fun i a b => slice_gen hK (hc.modelActuatorGrad_data i).1
      ((clm_memLp (hc.modelActuatorGrad_data i).1 (hc.modelActuatorGrad_data i).2.1).restrict _)
      (fun θ M => frameMat θ M a b) (frameMat_cont a b)
      (fun θ M => frameMat_bound θ M a b) (fun θ M => frameMat_per θ M a b)
  have hPL : ∀ i a b, ∀ᵐ p ∂(volume.restrict K.rect), MemLp
      (fun θ => frameMat θ (c.modelPinField i (cylPoint p.1 θ p.2)) a b) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    fun i a b => slice_gen hK (hc.modelPin_data i).1
      ((clm_memLp (hc.modelPin_data i).1 (hc.modelPin_data i).2.1).restrict _)
      (fun θ M => frameMat θ M a b) (frameMat_cont a b)
      (fun θ M => frameMat_bound θ M a b) (fun θ M => frameMat_per θ M a b)
  filter_upwards [hmem, ae_all_iff.2 hvL, hvP, ae_all_iff.2 fun a => ae_all_iff.2 (hGL a), hGP,
    ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_all_iff.2 (hHL a b), hHP,
    ae_all_iff.2 fun a => ae_all_iff.2 (hSM a), ae_all_iff.2 fun a => ae_all_iff.2 (hCM a),
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ae_all_iff.2 (hAL i a),
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ae_all_iff.2 (hPL i a)]
    with p hp hvl hvp hgl hgp hhl hhp hsm hcm hal hpl
  exact ⟨fun a => ⟨hvl a, hvp a⟩, fun a b => ⟨hgl a b, hgp a b⟩, fun a b d => ⟨hhl a b d, hhp a b d⟩,
    fun a b => ⟨hsm a b, hcm a b⟩,
    ⟨C, fun θ a b => ⟨(frameMat_bound _ _ a b).trans (hbS p hp θ), (frameMat_bound _ _ a b).trans (hbG p hp θ)⟩⟩,
    fun i a b => ⟨hal i a b, hpl i a b⟩, fun θ => hw p hp θ⟩

end Breakdown.CellCert.CellAnalysis
