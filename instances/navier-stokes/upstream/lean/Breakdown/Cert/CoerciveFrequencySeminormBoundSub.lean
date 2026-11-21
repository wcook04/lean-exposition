import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveSmoothIsPerturbation
import Breakdown.Cert.CoerciveModeL2

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencyBound

namespace Internal

open Breakdown.Coercive.Internal.SmoothIsPerturbation

theorem isWeakGradient_sub {f₁ f₂ : Space → Space} {g₁ g₂ : Space → (Space →L[ℝ] Space)}
    (h₁ : IsWeakGradient f₁ g₁) (h₂ : IsWeakGradient f₂ g₂) :
    IsWeakGradient (fun y => f₁ y - f₂ y) (fun y => g₁ y - g₂ y) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, fun φ hφ i => ?_⟩
  have hI : ∀ {g : Space → (Space →L[ℝ] Space)}, LocallyIntegrable g volume →
      Integrable (fun y => φ y • g y (unitVector i)) volume := fun hg =>
    (hg.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).apply_continuousLinearMap
      (unitVector i)
  have hJ : ∀ {f : Space → Space}, LocallyIntegrable f volume →
      Integrable (fun y => fderiv ℝ φ y (unitVector i) • f y) volume := fun hf =>
    hf.integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have e1 : (fun y => φ y • (g₁ y - g₂ y) (unitVector i)) =
      fun y => φ y • g₁ y (unitVector i) - φ y • g₂ y (unitVector i) := by
    funext y
    rw [ContinuousLinearMap.sub_apply, smul_sub]
  have e2 : (fun y => fderiv ℝ φ y (unitVector i) • (f₁ y - f₂ y)) =
      fun y => fderiv ℝ φ y (unitVector i) • f₁ y - fderiv ℝ φ y (unitVector i) • f₂ y := by
    funext y
    rw [smul_sub]
  show ∫ y, φ y • (g₁ y - g₂ y) (unitVector i) = -∫ y, fderiv ℝ φ y (unitVector i) • (f₁ y - f₂ y)
  rw [e1, e2, integral_sub (hI h₁.2.1) (hI h₂.2.1), integral_sub (hJ h₁.1) (hJ h₂.1), h₁.2.2 φ hφ i,
    h₂.2.2 φ hφ i]
  abel

theorem sixth_sub_le (a b : Space) : ‖a - b‖ ^ 6 ≤ 64 * (‖a‖ ^ 6 + ‖b‖ ^ 6) := by
  have h := norm_sub_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have h1 : ‖a - b‖ ^ 6 ≤ (‖a‖ + ‖b‖) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) h 6
  rcases le_total ‖a‖ ‖b‖ with hab | hab
  · have h2 : (‖a‖ + ‖b‖) ^ 6 ≤ (2 * ‖b‖) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
    have h3 : 0 ≤ ‖a‖ ^ 6 := by positivity
    nlinarith
  · have h2 : (‖a‖ + ‖b‖) ^ 6 ≤ (2 * ‖a‖) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
    have h3 : 0 ≤ ‖b‖ ^ 6 := by positivity
    nlinarith

theorem sq_sub_le (a b : Space) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem matSq_sub_le (A B : Space →L[ℝ] Space) : matSq (A - B) ≤ 2 * matSq A + 2 * matSq B := by
  unfold matSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.sub_apply]
  exact sq_sub_le _ _

theorem matSq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_matSq : Continuous matSq := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem continuous_secondDerivTrace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem secondDerivTrace_sub (A B : Space →L[ℝ] Space →L[ℝ] Space) :
    secondDerivTrace (A - B) = secondDerivTrace A - secondDerivTrace B := by
  unfold secondDerivTrace
  rw [← Finset.sum_sub_distrib]
  rfl

theorem periodLIntegral_mono {f h : ℝ → Space → ℝ} (hfh : ∀ σ y, f σ y ≤ h σ y) :
    periodLIntegral f ≤ periodLIntegral h :=
  lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hfh σ y)

theorem periodLIntegral_const_mul {c : ℝ} (hc : 0 ≤ c) (a : ℝ → Space → ℝ) :
    periodLIntegral (fun σ y => c * a σ y) = ENNReal.ofReal c * periodLIntegral a := by
  unfold periodLIntegral
  simp_rw [ENNReal.ofReal_mul hc]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem periodLIntegral_add {a b : ℝ → Space → ℝ} (ha0 : ∀ σ y, 0 ≤ a σ y) (hb0 : ∀ σ y, 0 ≤ b σ y)
    (ma : AEStronglyMeasurable (fun z : ℝ × Space => a z.1 z.2) volume)
    (mb : AEStronglyMeasurable (fun z : ℝ × Space => b z.1 z.2) volume) :
    periodLIntegral (fun σ y => a σ y + b σ y) = periodLIntegral a + periodLIntegral b := by
  rw [ModeL2Internal.periodLIntegral_eq_slab (fun σ y => a σ y + b σ y)
      ((ma.add mb).mono_ac ModeL2Internal.slab_ac),
    ModeL2Internal.periodLIntegral_eq_slab a (ma.mono_ac ModeL2Internal.slab_ac),
    ModeL2Internal.periodLIntegral_eq_slab b (mb.mono_ac ModeL2Internal.slab_ac)]
  simp_rw [ENNReal.ofReal_add (ha0 _ _) (hb0 _ _)]
  exact lintegral_add_left' (ma.mono_ac ModeL2Internal.slab_ac).aemeasurable.ennreal_ofReal _

theorem periodLIntegral_lt_top_of_two {f a b : ℝ → Space → ℝ} (hf : ∀ σ y, f σ y ≤ 2 * a σ y + 2 * b σ y)
    (ha0 : ∀ σ y, 0 ≤ a σ y) (hb0 : ∀ σ y, 0 ≤ b σ y)
    (ma : AEStronglyMeasurable (fun z : ℝ × Space => a z.1 z.2) volume)
    (mb : AEStronglyMeasurable (fun z : ℝ × Space => b z.1 z.2) volume)
    (ha : periodLIntegral a < ⊤) (hb : periodLIntegral b < ⊤) : periodLIntegral f < ⊤ := by
  refine lt_of_le_of_lt (periodLIntegral_mono hf) ?_
  rw [periodLIntegral_add (fun σ y => mul_nonneg zero_le_two (ha0 σ y))
      (fun σ y => mul_nonneg zero_le_two (hb0 σ y)) (aestronglyMeasurable_const.mul ma)
      (aestronglyMeasurable_const.mul mb),
    periodLIntegral_const_mul zero_le_two, periodLIntegral_const_mul zero_le_two]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb⟩

theorem locallyIntegrable_of_periodic {g : ℝ → Space → Space}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume) (hp : IsTimePeriodic g)
    (hf : periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) < ⊤) :
    LocallyIntegrable (fun z : ℝ × Space => g z.1 z.2) volume := by
  intro x
  set I : Set ℝ := Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) with hI
  set S : Set (ℝ × Space) := Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 1 with hS
  refine ⟨S, prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds _ one_pos), ?_⟩
  refine ⟨hm.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hper : Function.Periodic (fun σ => ∫⁻ y, ENNReal.ofReal (‖g σ y‖ ^ 2)) 1 := fun σ => by
    simp only [hp σ]
  have hΦ : ∫⁻ σ in I, ∫⁻ y, ENNReal.ofReal (‖g σ y‖ ^ 2) < ⊤ := by
    rw [hI, Cert.Internal.CoerciveBordered.lintegral_Ioc_periodic _ hper]
    exact hf
  have hm2 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2)) volume :=
    (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hSf : volume S < ⊤ :=
    ((Metric.isBounded_Ioo _ _).prod Metric.isBounded_ball).measure_lt_top
  calc ∫⁻ z in S, ‖g z.1 z.2‖ₑ ≤ ∫⁻ z in S, (1 + ENNReal.ofReal (‖g z.1 z.2‖ ^ 2)) := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (g z.1 z.2)])
    _ = volume S + ∫⁻ z in S, ENNReal.ofReal (‖g z.1 z.2‖ ^ 2) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ ≤ volume S + ∫⁻ z in I ×ˢ (Set.univ : Set Space), ENNReal.ofReal (‖g z.1 z.2‖ ^ 2) := by
        exact add_le_add le_rfl (lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioc_self (Set.subset_univ _)))
    _ = volume S + ∫⁻ σ in I, ∫⁻ y, ENNReal.ofReal (‖g σ y‖ ^ 2) := by
        rw [Measure.volume_eq_prod, setLIntegral_prod (fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2))
          hm2.restrict, Measure.restrict_univ]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hSf, hΦ⟩

theorem integrable_inner_of_locallyIntegrable {f g : ℝ × Space → Space} (hf : LocallyIntegrable f volume)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Integrable (fun z => inner ℝ (f z) (g z)) volume := by
  have hb : Integrable (fun z => ‖g z‖ • f z) volume :=
    hf.integrable_smul_left_of_hasCompactSupport hg.norm hgc.norm
  refine hb.norm.mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  rw [norm_smul, norm_norm, mul_comm]
  exact norm_inner_le_norm _ _

def testTransport (P : ℝ) (φ : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  -(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2

theorem testTransport_continuous (P : ℝ) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    Continuous (testTransport P φ) := by
  have h1 := (time_contDiff (u := φ) hφ.1).continuous
  have h2 := ((grad_contDiff (u := φ) hφ.1).continuous).clm_apply continuous_snd
  unfold testTransport
  exact ((h1.const_smul (-(1 / P))).sub (hφ.1.continuous)).sub (h2.const_smul (1 / 2 : ℝ))

theorem testTransport_hasCompactSupport (P : ℝ) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    HasCompactSupport (testTransport P φ) := by
  have hJ : HasCompactSupport (joint φ) := hφ.2
  have hD : HasCompactSupport (fderiv ℝ (joint φ)) := hJ.fderiv (𝕜 := ℝ)
  have h1 : ContDiff ℝ 1 (joint φ) := hφ.1.of_le (by simp)
  have hsub : Function.support (testTransport P φ) ⊆
      Function.support (joint φ) ∪ Function.support (fderiv ℝ (joint φ)) := by
    intro z hz
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hz
    unfold testTransport
    rw [deriv_line h1, fderiv_slice h1, hn.2]
    have h0 : φ z.1 z.2 = 0 := hn.1
    simp [h0]
  refine (hJ.union hD).of_isClosed_subset (isClosed_tsupport _) ?_
  exact closure_minimal (hsub.trans (Set.union_subset_union (subset_tsupport _) (subset_tsupport _)))
    ((isClosed_tsupport _).union (isClosed_tsupport _))

end Internal

open Breakdown.Coercive.FrequencyBound.Internal

theorem isPerturbation_sub {Γ₁ Γ₂ : Set Symmetry} {P : ℝ} {u v : ℝ → Space → Space}
    {Gu G : ℝ → Space → (Space →L[ℝ] Space)} {Hu H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {gu g : ℝ → Space → Space} (hu : IsPerturbation Γ₁ P u Gu Hu gu) (hv : IsPerturbation Γ₂ P v G H g) :
    IsPerturbation ∅ P (fun σ y => u σ y - v σ y) (fun σ y => Gu σ y - G σ y)
      (fun σ y => Hu σ y - H σ y) (fun σ y => gu σ y - g σ y) := by
  obtain ⟨hul, -, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ₁ P u Gu Hu gu hu
  obtain ⟨hvl, -, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ₂ P v G H g hv
  have hgul := locallyIntegrable_of_periodic hu.measurable_derivative hu.periodic_derivative
    hu.derivative_finite
  have hgl := locallyIntegrable_of_periodic hv.measurable_derivative hv.periodic_derivative
    hv.derivative_finite
  have mG : ∀ {A : ℝ → Space → (Space →L[ℝ] Space)},
      AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => matSq (A z.1 z.2)) volume := fun h =>
    continuous_matSq.comp_aestronglyMeasurable h
  have mV : ∀ {X : ℝ → Space → Space}, AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2) volume := fun h => h.norm.pow 2
  have mT : ∀ {A : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)},
      AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (A z.1 z.2)‖ ^ 2) volume := fun h =>
    (continuous_secondDerivTrace.comp_aestronglyMeasurable h).norm.pow 2
  refine
    { measurable_velocity := hu.measurable_velocity.sub hv.measurable_velocity
      measurable_gradient := hu.measurable_gradient.sub hv.measurable_gradient
      measurable_secondDeriv := hu.measurable_secondDeriv.sub hv.measurable_secondDeriv
      measurable_derivative := hu.measurable_derivative.sub hv.measurable_derivative
      periodic_velocity := fun σ y => by
        show u (σ + 1) y - v (σ + 1) y = u σ y - v σ y
        rw [hu.periodic_velocity, hv.periodic_velocity]
      periodic_gradient := fun σ y => by
        show Gu (σ + 1) y - G (σ + 1) y = Gu σ y - G σ y
        rw [hu.periodic_gradient, hv.periodic_gradient]
      periodic_secondDeriv := fun σ y => by
        show Hu (σ + 1) y - H (σ + 1) y = Hu σ y - H σ y
        rw [hu.periodic_secondDeriv, hv.periodic_secondDeriv]
      periodic_derivative := fun σ y => by
        show gu (σ + 1) y - g (σ + 1) y = gu σ y - g σ y
        rw [hu.periodic_derivative, hv.periodic_derivative]
      weak_gradient := ?_
      weak_secondDeriv := ?_
      divergence_free := ?_
      sixth_power := ?_
      gradient_finite := ?_
      sumSecondPartials_finite := ?_
      derivative_finite := ?_
      transport := ?_
      invariant := ?_ }
  · filter_upwards [hu.weak_gradient, hv.weak_gradient] with σ h1 h2
    exact isWeakGradient_sub h1 h2
  · filter_upwards [hu.weak_secondDeriv, hv.weak_secondDeriv] with σ h1 h2 j
    have h := isWeakGradient_sub (h1 j) (h2 j)
    have e1 : (fun y => Gu σ y (unitVector j) - G σ y (unitVector j)) =
        fun y => (Gu σ y - G σ y) (unitVector j) := by
      funext y
      rw [ContinuousLinearMap.sub_apply]
    have e2 : (fun y => (Hu σ y).flip (unitVector j) - (H σ y).flip (unitVector j)) =
        fun y => (Hu σ y - H σ y).flip (unitVector j) := by
      funext y
      ext x
      simp
    rw [e1, e2] at h
    exact h
  · filter_upwards [hu.divergence_free, hv.divergence_free] with σ h1 h2
    filter_upwards [h1, h2] with y hy1 hy2
    simp only [ContinuousLinearMap.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib, hy1, hy2, sub_zero]
  · have s1 := AEStronglyMeasurable.prodMk_left (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      hu.measurable_velocity
    have s2 := AEStronglyMeasurable.prodMk_left (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      hv.measurable_velocity
    filter_upwards [hu.sixth_power, hv.sixth_power, s1, s2] with σ h1 h2 m1 m2
    have hpt : ∀ y, ENNReal.ofReal (‖u σ y - v σ y‖ ^ 6) ≤
        ENNReal.ofReal 64 * (ENNReal.ofReal (‖u σ y‖ ^ 6) + ENNReal.ofReal (‖v σ y‖ ^ 6)) := by
      intro y
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (sixth_sub_le _ _)
    calc (∫⁻ y, ENNReal.ofReal (‖u σ y - v σ y‖ ^ 6))
        ≤ ∫⁻ y, ENNReal.ofReal 64 * (ENNReal.ofReal (‖u σ y‖ ^ 6) + ENNReal.ofReal (‖v σ y‖ ^ 6)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal 64 * ((∫⁻ y, ENNReal.ofReal (‖u σ y‖ ^ 6)) + ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left' (m1.norm.aemeasurable.pow_const 6).ennreal_ofReal]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨h1, h2⟩)
  · exact periodLIntegral_lt_top_of_two (a := fun σ y => matSq (Gu σ y)) (b := fun σ y => matSq (G σ y))
      (fun σ y => matSq_sub_le _ _) (fun σ y => matSq_nonneg _)
      (fun σ y => matSq_nonneg _) (mG hu.measurable_gradient) (mG hv.measurable_gradient)
      hu.gradient_finite hv.gradient_finite
  · refine periodLIntegral_lt_top_of_two (a := fun σ y => ‖secondDerivTrace (Hu σ y)‖ ^ 2)
      (b := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) (fun σ y => ?_) (fun σ y => sq_nonneg _)
      (fun σ y => sq_nonneg _) (mT hu.measurable_secondDeriv) (mT hv.measurable_secondDeriv)
      hu.sumSecondPartials_finite hv.sumSecondPartials_finite
    show ‖secondDerivTrace (Hu σ y - H σ y)‖ ^ 2 ≤ _
    rw [secondDerivTrace_sub]
    exact sq_sub_le _ _
  · exact periodLIntegral_lt_top_of_two (a := fun σ y => ‖gu σ y‖ ^ 2) (b := fun σ y => ‖g σ y‖ ^ 2)
      (fun σ y => sq_sub_le _ _) (fun σ y => sq_nonneg _)
      (fun σ y => sq_nonneg _) (mV hu.measurable_derivative) (mV hv.measurable_derivative)
      hu.derivative_finite hv.derivative_finite
  · intro φ hφ
    have hTc := testTransport_continuous P hφ
    have hTs := testTransport_hasCompactSupport P hφ
    have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
    have iu := integrable_inner_of_locallyIntegrable hul hTc hTs
    have iv := integrable_inner_of_locallyIntegrable hvl hTc hTs
    have igu := integrable_inner_of_locallyIntegrable hgul hφc hφ.2
    have ig := integrable_inner_of_locallyIntegrable hgl hφc hφ.2
    have tu := hu.transport φ hφ
    have tv := hv.transport φ hφ
    unfold testTransport at iu iv
    simp only [inner_sub_left]
    rw [integral_sub iu iv, integral_sub igu ig, tu, tv]
  · intro γ hγ
    simp at hγ

end FrequencyBound

end Coercive

end Breakdown
