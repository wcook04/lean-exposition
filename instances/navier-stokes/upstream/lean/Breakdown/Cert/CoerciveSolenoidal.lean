import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.Invariance
import Breakdown.Cert.CoerciveTestDensity

open scoped ContDiff ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.Coercive

namespace Internal.SolenoidalPart

abbrev periodMeasure : Measure (ℝ × Space) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space)

abbrev PeriodL2 := Lp Space 2 periodMeasure

open Classical in
def toL2 (X : ℝ → Space → Space) : PeriodL2 :=
  if h : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure then h.toLp _ else 0

def reprL2 (g : PeriodL2) : ℝ × Space → Space := (Lp.aestronglyMeasurable g).mk g

def ofL2 (g : PeriodL2) (σ : ℝ) (y : Space) : Space := reprL2 g (Int.fract σ, y)

theorem periodMeasure_eq :
    periodMeasure = (volume : Measure (ℝ × Space)).restrict (Icc (0 : ℝ) 1 ×ˢ univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem aestronglyMeasurable_period {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) periodMeasure := by
  rw [periodMeasure_eq]
  exact hX.restrict

theorem lintegral_period (f : ℝ → Space → ℝ)
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) periodMeasure) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂periodMeasure := by
  rw [periodLIntegral, lintegral_prod _ hf]

theorem memLp_of {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (h2 : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤) :
    MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure := by
  have hm := aestronglyMeasurable_period hX
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨(hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
  rw [← lintegral_period (fun σ y => ‖X σ y‖ ^ 2)
    (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal]
  exact h2

theorem lt_top_of_memLp {X : ℝ → Space → Space}
    (h : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm h.1).1 h
  rw [lintegral_period (fun σ y => ‖X σ y‖ ^ 2) hi.1.aemeasurable.ennreal_ofReal]
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).1 hi.2

theorem coeFn_toL2 {X : ℝ → Space → Space}
    (h : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    (toL2 X : ℝ × Space → Space) =ᵐ[periodMeasure] fun z => X z.1 z.2 := by
  rw [toL2, dif_pos h]
  exact h.coeFn_toLp

theorem pairing_eq_inner {X Y : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure)
    (hY : MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure) :
    ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y) = inner ℝ (toL2 X) (toL2 Y) := by
  rw [L2.inner_def]
  have hi := L2.integrable_inner (𝕜 := ℝ) (toL2 X) (toL2 Y)
  have he : (fun z => inner ℝ ((toL2 X : ℝ × Space → Space) z) ((toL2 Y : ℝ × Space → Space) z))
      =ᵐ[periodMeasure] fun z : ℝ × Space => inner ℝ (X z.1 z.2) (Y z.1 z.2) := by
    filter_upwards [coeFn_toL2 hX, coeFn_toL2 hY] with z h1 h2
    rw [h1, h2]
  rw [integral_congr_ae he]
  exact (integral_prod _ (hi.congr he)).symm

theorem periodNorm_eq {X : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    periodNorm X = ‖toL2 X‖ := by
  have hsq : ‖toL2 X‖ ^ 2 = (periodLIntegral (fun σ y => ‖X σ y‖ ^ 2)).toReal := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have he : (fun z => inner ℝ ((toL2 X : ℝ × Space → Space) z) ((toL2 X : ℝ × Space → Space) z))
        =ᵐ[periodMeasure] fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2 := by
      filter_upwards [coeFn_toL2 hX] with z h1
      rw [h1, real_inner_self_eq_norm_sq]
    rw [integral_congr_ae he, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      (hX.1.norm.aemeasurable.pow_const 2).aestronglyMeasurable,
      lintegral_period (fun σ y => ‖X σ y‖ ^ 2)
        ((hX.1.norm.aemeasurable.pow_const 2).ennreal_ofReal)]
  rw [periodNorm, ← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem measurable_fractPair : Measurable (fun z : ℝ × Space => (Int.fract z.1, z.2)) :=
  (measurable_fract.comp measurable_fst).prodMk measurable_snd

theorem aestronglyMeasurable_ofL2 (g : PeriodL2) :
    AEStronglyMeasurable (fun z : ℝ × Space => ofL2 g z.1 z.2) volume :=
  ((Lp.aestronglyMeasurable g).stronglyMeasurable_mk.comp_measurable measurable_fractPair).aestronglyMeasurable

theorem periodic_ofL2 (g : PeriodL2) : IsTimePeriodic (ofL2 g) := by
  intro σ y
  simp only [ofL2, Int.fract_add_one]

theorem ae_mem_Ico : ∀ᵐ z ∂periodMeasure, z.1 ∈ Ico (0 : ℝ) 1 := by
  have h : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), σ ∈ Ico (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ico
  exact Measure.quasiMeasurePreserving_fst.ae h

theorem ofL2_ae (g : PeriodL2) :
    (fun z : ℝ × Space => ofL2 g z.1 z.2) =ᵐ[periodMeasure] (g : ℝ × Space → Space) := by
  filter_upwards [ae_mem_Ico, (Lp.aestronglyMeasurable g).ae_eq_mk] with z hz hmk
  rw [hmk]
  simp only [ofL2, reprL2, Int.fract_eq_self.2 ⟨hz.1, hz.2⟩]

theorem memLp_ofL2 (g : PeriodL2) :
    MemLp (fun z : ℝ × Space => ofL2 g z.1 z.2) 2 periodMeasure :=
  (memLp_congr_ae (ofL2_ae g)).2 (Lp.memLp g)

theorem toL2_ofL2 (g : PeriodL2) : toL2 (ofL2 g) = g :=
  Lp.ext ((coeFn_toL2 (memLp_ofL2 g)).trans (ofL2_ae g))

theorem periodic_int {β : Type*} {X : ℝ → Space → β} (hX : IsTimePeriodic X) (σ : ℝ) (n : ℤ) :
    X (σ + n) = X σ := by
  refine Cert.Internal.Invariance.periodic_eq hX ?_
  have h0 : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by simp⟩
  rw [AddCircle.coe_add, h0, add_zero]

theorem ae_of_period {X Y : ℝ → Space → Space} (hX : IsTimePeriodic X) (hY : IsTimePeriodic Y)
    (h : ∀ᵐ z ∂periodMeasure, X z.1 z.2 = Y z.1 z.2) :
    ∀ᵐ z : ℝ × Space, X z.1 z.2 = Y z.1 z.2 := by
  rw [periodMeasure_eq, ae_restrict_iff' (measurableSet_Icc.prod MeasurableSet.univ)] at h
  have hn : ∀ n : ℤ, ∀ᵐ z : ℝ × Space, (z.1 + n, z.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set Space) →
      X (z.1 + n) z.2 = Y (z.1 + n) z.2 := by
    intro n
    have hmp : MeasurePreserving (fun z : ℝ × Space => (z.1 + n, z.2)) volume volume := by
      rw [Measure.volume_eq_prod]
      exact (measurePreserving_add_right volume (n : ℝ)).prod (MeasurePreserving.id volume)
    filter_upwards [hmp.quasiMeasurePreserving.ae h] with z hz
    simpa using hz
  filter_upwards [ae_all_iff.2 hn] with z hz
  have hmem : (z.1 + ((-⌊z.1⌋ : ℤ) : ℝ), z.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set Space) := by
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · push_cast
      linarith [Int.floor_le z.1]
    · push_cast
      linarith [Int.lt_floor_add_one z.1]
  have e := hz (-⌊z.1⌋) hmem
  rwa [periodic_int hX, periodic_int hY] at e

theorem memLp_of_continuous {X : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => X z.1 z.2)) {r : ℝ} (hs : ∀ σ y, r < ‖y‖ → X σ y = 0) :
    MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure := by
  set K : Set (ℝ × Space) := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) r with hKdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have he : (fun z : ℝ × Space => X z.1 z.2) =ᵐ[periodMeasure] K.indicator (fun z => X z.1 z.2) := by
    rw [periodMeasure_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    by_cases hk : z ∈ K
    · rw [indicator_of_mem hk]
    · rw [indicator_of_notMem hk]
      apply hs
      by_contra hle
      exact hk ⟨hz.1, by simpa using not_lt.1 hle⟩
  rw [memLp_congr_ae he, memLp_indicator_iff_restrict hK.measurableSet]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have : IsFiniteMeasure (periodMeasure.restrict K) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, periodMeasure_eq, Measure.restrict_apply hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ hC)

theorem memLp_testField {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    MemLp (fun z : ℝ × Space => ψ z.1 z.2) 2 periodMeasure := by
  obtain ⟨r, hr⟩ := hψ.2.2.1
  exact memLp_of_continuous hψ.1.continuous hr

def gradOf (q : ℝ → Space → ℝ) (σ : ℝ) (y : Space) : Space := gradientAt (q σ) y

theorem continuous_gradOf {q : ℝ → Space → ℝ} (hq : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradOf q z.1 z.2) := by
  have hc := (Cert.Internal.Invariance.contDiff_fderiv_slice (V := q) (n := 0) hq
    (by simp)).continuous
  simp only [gradOf, gradientAt]
  exact continuous_finsetSum _ fun i _ => (hc.clm_apply continuous_const).smul continuous_const

theorem gradOf_zero {q : ℝ → Space → ℝ} {r : ℝ} (hr : ∀ σ y, r < ‖y‖ → q σ y = 0) (σ : ℝ)
    (y : Space) (hy : r < ‖y‖) : gradOf q σ y = 0 := by
  have hev : q σ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
    exact hr σ x hx
  simp [gradOf, gradientAt, hev.fderiv_eq]

theorem memLp_gradOf {q : ℝ → Space → ℝ} (hq : IsPeriodicTestPotential q) :
    MemLp (fun z : ℝ × Space => gradOf q z.1 z.2) 2 periodMeasure := by
  obtain ⟨r, hr⟩ := hq.2.2
  exact memLp_of_continuous (continuous_gradOf hq.1) (gradOf_zero hr)

theorem slice_contDiff {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] {X : ℝ → Space → β}
    (hX : ContDiff ℝ ∞ (fun z : ℝ × Space => X z.1 z.2)) (σ : ℝ) : ContDiff ℝ ∞ (X σ) :=
  hX.comp (contDiff_const.prodMk contDiff_id)

theorem slice_isTestField {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (σ : ℝ) :
    IsTestField (ψ σ) := by
  obtain ⟨r, hr⟩ := hψ.2.2.1
  refine ⟨slice_contDiff hψ.1 σ, ?_, hψ.2.2.2 σ⟩
  exact HasCompactSupport.intro (isCompact_closedBall (0 : Space) r) fun y hy =>
    hr σ y (not_le.1 (by simpa using hy))

theorem pairing_test_grad {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    {q : ℝ → Space → ℝ} (hq : IsPeriodicTestPotential q) :
    ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (ψ σ y) (gradOf q σ y) = 0 := by
  have h : ∀ σ, ∫ y, inner ℝ (ψ σ y) (gradOf q σ y) = 0 := by
    intro σ
    have h1 := Cert.Internal.Invariance.integral_gradient_test
      ((slice_contDiff hq.1 σ).of_le (by simp)) (slice_isTestField hψ σ)
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ fun y => real_inner_comm _ _)
  simp only [h, integral_zero]

def testSpan : Submodule ℝ PeriodL2 :=
  (Submodule.span ℝ {f | ∃ ψ, IsPeriodicTestField ψ ∧ toL2 ψ = f}).topologicalClosure

instance : CompleteSpace testSpan := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem inner_grad_eq_zero {w : PeriodL2} (hw : w ∈ testSpan) {q : ℝ → Space → ℝ}
    (hq : IsPeriodicTestPotential q) : inner ℝ w (toL2 (gradOf q)) = 0 := by
  have hle : testSpan ≤ LinearMap.ker ((innerSL ℝ (toL2 (gradOf q)) : PeriodL2 →L[ℝ] ℝ) : PeriodL2 →ₗ[ℝ] ℝ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [real_inner_comm, ← pairing_eq_inner (memLp_testField hψ) (memLp_gradOf hq)]
    exact pairing_test_grad hψ hq
  have h := hle hw
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at h
  rw [real_inner_comm, h]

theorem test_mem {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) : toL2 ψ ∈ testSpan :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ψ, hψ, rfl⟩)

theorem isSolenoidalPartOf_ofL2 {F : ℝ → Space → Space}
    (hF : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure) :
    IsSolenoidalPartOf F (ofL2 (testSpan.starProjection (toL2 F))) := by
  set g := testSpan.starProjection (toL2 F)
  refine ⟨aestronglyMeasurable_ofL2 g, periodic_ofL2 g, lt_top_of_memLp (memLp_ofL2 g), ?_, ?_⟩
  · intro q hq
    have e := pairing_eq_inner (memLp_ofL2 g) (memLp_gradOf hq)
    simp only [gradOf] at e
    rw [e, toL2_ofL2]
    exact inner_grad_eq_zero (testSpan.starProjection_apply_mem _) hq
  · intro ψ hψ
    rw [pairing_eq_inner (memLp_ofL2 g) (memLp_testField hψ), pairing_eq_inner hF (memLp_testField hψ),
      toL2_ofL2]
    have h0 := testSpan.starProjection_inner_eq_zero (toL2 F) (toL2 ψ) (test_mem hψ)
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0.symm

theorem toL2_sub {X Y : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure)
    (hY : MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure) :
    toL2 (fun σ y => X σ y - Y σ y) = toL2 X - toL2 Y := by
  have hXY : MemLp (fun z : ℝ × Space => X z.1 z.2 - Y z.1 z.2) 2 periodMeasure := hX.sub hY
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (X := fun σ y => X σ y - Y σ y) hXY, Lp.coeFn_sub (toL2 X) (toL2 Y),
    coeFn_toL2 hX, coeFn_toL2 hY] with z h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4]

theorem eq_zero_of_orthogonal (hH : GradSolenoidalDensityHolds) (g : PeriodL2)
    (hg1 : ∀ q, IsPeriodicTestPotential q → inner ℝ g (toL2 (gradOf q)) = 0)
    (hg2 : ∀ ψ, IsPeriodicTestField ψ → inner ℝ g (toL2 ψ) = 0) : g = 0 := by
  have h := hH (ofL2 g) (aestronglyMeasurable_ofL2 g) (periodic_ofL2 g) (lt_top_of_memLp (memLp_ofL2 g))
    (fun q hq => by
      have e := pairing_eq_inner (memLp_ofL2 g) (memLp_gradOf hq)
      simp only [gradOf] at e
      rw [e, toL2_ofL2]
      exact hg1 q hq)
    (fun ψ hψ => by
      rw [pairing_eq_inner (memLp_ofL2 g) (memLp_testField hψ), toL2_ofL2]
      exact hg2 ψ hψ)
  have hp : ∀ᵐ z ∂periodMeasure, ofL2 g z.1 z.2 = 0 := by
    rw [periodMeasure_eq]
    exact ae_restrict_of_ae h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hp, ofL2_ae g] with z h1 h2
  rw [← h2, h1, Pi.zero_apply]

theorem unique_part (hH : GradSolenoidalDensityHolds) {F Q Q' : ℝ → Space → Space}
    (hQ : IsSolenoidalPartOf F Q) (hQ' : IsSolenoidalPartOf F Q') :
    ∀ᵐ z : ℝ × Space, Q' z.1 z.2 = Q z.1 z.2 := by
  have m : MemLp (fun z : ℝ × Space => Q z.1 z.2) 2 periodMeasure := memLp_of hQ.1 hQ.2.2.1
  have m' : MemLp (fun z : ℝ × Space => Q' z.1 z.2) 2 periodMeasure := memLp_of hQ'.1 hQ'.2.2.1
  have h0 : toL2 Q' - toL2 Q = 0 := by
    refine eq_zero_of_orthogonal hH _ (fun q hq => ?_) (fun ψ hψ => ?_)
    · rw [inner_sub_left, ← pairing_eq_inner m' (memLp_gradOf hq), ← pairing_eq_inner m (memLp_gradOf hq)]
      simp only [gradOf]
      rw [hQ'.2.2.2.1 q hq, hQ.2.2.2.1 q hq, sub_zero]
    · rw [inner_sub_left, ← pairing_eq_inner m' (memLp_testField hψ),
        ← pairing_eq_inner m (memLp_testField hψ), hQ'.2.2.2.2 ψ hψ, hQ.2.2.2.2 ψ hψ, sub_self]
  have he : toL2 Q' = toL2 Q := sub_eq_zero.1 h0
  refine ae_of_period hQ'.2.1 hQ.2.1 ?_
  filter_upwards [coeFn_toL2 m, coeFn_toL2 m'] with z h1 h2
  rw [← h1, ← h2, he]

theorem norms_part {F : ℝ → Space → Space}
    (hF : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure) :
    periodNorm (ofL2 (testSpan.starProjection (toL2 F))) ≤ periodNorm F ∧
      periodNorm (fun σ y => (2 : ℝ) • ofL2 (testSpan.starProjection (toL2 F)) σ y - F σ y) =
        periodNorm F := by
  set g := testSpan.starProjection (toL2 F)
  set f := toL2 F
  have horth : inner ℝ g (f - g) = 0 := by
    rw [real_inner_comm]
    exact testSpan.starProjection_inner_eq_zero f g (testSpan.starProjection_apply_mem f)
  have hpy : ‖f‖ ^ 2 = ‖g‖ ^ 2 + ‖f - g‖ ^ 2 := by
    have := norm_add_sq_real g (f - g)
    rw [horth, mul_zero, add_zero, add_sub_cancel] at this
    exact this
  have hm2 : MemLp (fun z : ℝ × Space => (2 : ℝ) • ofL2 g z.1 z.2 - F z.1 z.2) 2 periodMeasure :=
    ((memLp_ofL2 g).const_smul (2 : ℝ)).sub hF
  have h2 : toL2 (fun σ y => (2 : ℝ) • ofL2 g σ y - F σ y) = g - (f - g) := by
    refine Lp.ext ?_
    filter_upwards [coeFn_toL2 (X := fun σ y => (2 : ℝ) • ofL2 g σ y - F σ y) hm2,
      Lp.coeFn_sub g (f - g), Lp.coeFn_sub f g, ofL2_ae g, coeFn_toL2 hF] with z h1 h3 h4 h5 h6
    rw [h1, h3, Pi.sub_apply, h4, Pi.sub_apply, ← h5, ← h6]
    module
  rw [periodNorm_eq (memLp_ofL2 g), periodNorm_eq hF, periodNorm_eq hm2, toL2_ofL2, h2]
  constructor
  · refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [hpy]
    linarith [sq_nonneg ‖f - g‖]
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sub_sq_real, horth, hpy]
    ring

theorem lintegral_shift (k : ℝ → ℝ≥0∞) (hk : Function.Periodic k 1) (τ : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, k (σ + τ) = ∫⁻ σ in Icc (0 : ℝ) 1, k σ := by
  have e : ∀ f : AddCircle (1 : ℝ) → ℝ≥0∞, ∫⁻ σ in Icc (0 : ℝ) 1, f σ = ∫⁻ t, f t := by
    intro f
    have h := AddCircle.lintegral_preimage 1 0 f
    rw [zero_add] at h
    rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have h1 : (fun σ => k (σ + τ)) = fun σ : ℝ => hk.lift ((σ : AddCircle (1 : ℝ)) + (τ : AddCircle (1 : ℝ))) := by
    funext σ
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
  have h2 : k = fun σ : ℝ => hk.lift (σ : AddCircle (1 : ℝ)) := by
    funext σ
    rw [Function.Periodic.lift_coe]
  rw [h1, e (fun t => hk.lift (t + (τ : AddCircle (1 : ℝ)))), lintegral_add_right_eq_self]
  conv_rhs => rw [h2]
  rw [e hk.lift]

theorem integral_shift (k : ℝ → ℝ) (hk : Function.Periodic k 1) (τ : ℝ) :
    ∫ σ in Icc (0 : ℝ) 1, k (σ + τ) = ∫ σ in Icc (0 : ℝ) 1, k σ := by
  have e : ∀ f : AddCircle (1 : ℝ) → ℝ, ∫ σ in Icc (0 : ℝ) 1, f σ = ∫ t, f t := by
    intro f
    have h := AddCircle.integral_preimage 1 0 f
    rw [zero_add] at h
    rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have h1 : (fun σ => k (σ + τ)) = fun σ : ℝ => hk.lift ((σ : AddCircle (1 : ℝ)) + (τ : AddCircle (1 : ℝ))) := by
    funext σ
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
  have h2 : k = fun σ : ℝ => hk.lift (σ : AddCircle (1 : ℝ)) := by
    funext σ
    rw [Function.Periodic.lift_coe]
  rw [h1, e (fun t => hk.lift (t + (τ : AddCircle (1 : ℝ)))), integral_add_right_eq_self]
  conv_rhs => rw [h2]
  rw [e hk.lift]

theorem diag_sum_eq_trace (L : Space →ₗ[ℝ] Space) :
    ∑ i : Fin 3, (L (unitVector i)) i = LinearMap.trace ℝ Space L := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.trace]
  simp [LinearMap.toMatrix_apply, unitVector]

theorem diag_sum_conj (R : Space ≃ₗᵢ[ℝ] Space) (A : Space →L[ℝ] Space) :
    ∑ i : Fin 3, (R (A (R.symm (unitVector i)))) i = ∑ i : Fin 3, (A (unitVector i)) i := by
  have h := LinearMap.trace_conj' (R := ℝ) (A : Space →ₗ[ℝ] Space) R.toLinearEquiv
  rw [← diag_sum_eq_trace, ← diag_sum_eq_trace] at h
  exact h

theorem divergenceAt_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {W : Space → Space}
    (hW : Differentiable ℝ W) (y : Space) :
    divergenceAt (fun z => R (W (R.symm z))) y = divergenceAt W (R.symm y) := by
  have h := Cert.Internal.Invariance.fderiv_pushForward R hW y
  simp only [divergenceAt]
  have e : ∀ i, (fderiv ℝ (fun z => R (W (R.symm z))) y (unitVector i)) i =
      (R (fderiv ℝ W (R.symm y) (R.symm (unitVector i)))) i := fun i => by
    rw [← h]
    rfl
  simp only [e]
  exact diag_sum_conj R _

def moveField (R : Space ≃ₗᵢ[ℝ] Space) (τ : ℝ) (ψ : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  R (ψ (σ - τ) (R.symm y))

def movePotential (R : Space ≃ₗᵢ[ℝ] Space) (τ : ℝ) (q : ℝ → Space → ℝ) (σ : ℝ) (y : Space) : ℝ :=
  q (σ - τ) (R.symm y)

theorem contDiff_move {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (R : Space ≃ₗᵢ[ℝ] Space)
    (τ : ℝ) {X : ℝ → Space → β} (hX : ContDiff ℝ ∞ (fun z : ℝ × Space => X z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => X (z.1 - τ) (R.symm z.2)) :=
  hX.comp ((contDiff_fst.sub contDiff_const).prodMk
    (((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).contDiff.comp contDiff_snd))

theorem isPeriodicTestField_move (R : Space ≃ₗᵢ[ℝ] Space) (τ : ℝ) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) : IsPeriodicTestField (moveField R τ ψ) := by
  obtain ⟨hs, hp, ⟨r, hr⟩, hd⟩ := hψ
  refine ⟨?_, ?_, ⟨r, fun σ y hy => ?_⟩, fun σ y => ?_⟩
  · exact ((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).contDiff.comp
      (contDiff_move R τ hs)
  · intro σ y
    simp only [moveField]
    rw [show σ + 1 - τ = σ - τ + 1 by ring, hp]
  · simp only [moveField]
    rw [hr _ _ (by rwa [LinearIsometryEquiv.norm_map]), map_zero]
  · have hdiff : Differentiable ℝ (ψ (σ - τ)) :=
      (slice_contDiff hs (σ - τ)).differentiable (by simp)
    rw [show moveField R τ ψ σ = fun z => R (ψ (σ - τ) (R.symm z)) from rfl,
      divergenceAt_pushForward R hdiff, hd]

theorem isPeriodicTestPotential_move (R : Space ≃ₗᵢ[ℝ] Space) (τ : ℝ) {q : ℝ → Space → ℝ}
    (hq : IsPeriodicTestPotential q) : IsPeriodicTestPotential (movePotential R τ q) := by
  obtain ⟨hs, hp, ⟨r, hr⟩⟩ := hq
  refine ⟨contDiff_move R τ hs, ?_, ⟨r, fun σ y hy => ?_⟩⟩
  · intro σ y
    simp only [movePotential]
    rw [show σ + 1 - τ = σ - τ + 1 by ring, hp]
  · simp only [movePotential]
    exact hr _ _ (by rwa [LinearIsometryEquiv.norm_map])

theorem pairing_move (R : Space ≃ₗᵢ[ℝ] Space) (τ : ℝ) {X Z : ℝ → Space → Space}
    (hX : IsTimePeriodic X) (hZ : IsTimePeriodic Z) :
    ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (R.symm (X (σ + τ) (R y))) (Z σ y) =
      ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (moveField R τ Z σ y) := by
  have hin : ∀ σ, ∫ y, inner ℝ (R.symm (X (σ + τ) (R y))) (Z σ y) =
      ∫ y, inner ℝ (X (σ + τ) y) (moveField R τ Z (σ + τ) y) := by
    intro σ
    have h := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
      (fun y => inner ℝ (X (σ + τ) y) (moveField R τ Z (σ + τ) y))
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [moveField, add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply]
    rw [← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  simp only [hin]
  refine integral_shift (fun s => ∫ y, inner ℝ (X s y) (moveField R τ Z s y)) (fun s => ?_) τ
  simp only [moveField, show s + 1 - τ = s - τ + 1 by ring, show ∀ σ y, X (σ + 1) y = X σ y from hX,
    show ∀ σ y, Z (σ + 1) y = Z σ y from hZ]

theorem isSolenoidalPartOf_move (R : Space ≃ₗᵢ[ℝ] Space) (τ : ℝ) {F Q : ℝ → Space → Space}
    (hFp : IsTimePeriodic F) (h : IsSolenoidalPartOf F Q) :
    IsSolenoidalPartOf (fun σ y => R.symm (F (σ + τ) (R y))) (fun σ y => R.symm (Q (σ + τ) (R y))) := by
  obtain ⟨hm, hp, h2, hg, ht⟩ := h
  have hT : MeasurePreserving (fun z : ℝ × Space => (z.1 + τ, R z.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume τ).prod R.measurePreserving
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact R.symm.continuous.comp_aestronglyMeasurable (hm.comp_measurePreserving hT)
  · intro σ y
    simp only
    rw [show σ + 1 + τ = σ + τ + 1 by ring, hp]
  · have e : periodLIntegral (fun σ y => ‖R.symm (Q (σ + τ) (R y))‖ ^ 2) =
        periodLIntegral (fun σ y => ‖Q σ y‖ ^ 2) := by
      simp only [periodLIntegral, LinearIsometryEquiv.norm_map]
      have hin : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖Q (σ + τ) (R y)‖ ^ 2) =
          ∫⁻ y, ENNReal.ofReal (‖Q (σ + τ) y‖ ^ 2) := fun σ =>
        R.measurePreserving.lintegral_comp_emb R.toHomeomorph.measurableEmbedding
          (fun y => ENNReal.ofReal (‖Q (σ + τ) y‖ ^ 2))
      simp only [hin]
      refine lintegral_shift (fun s => ∫⁻ y, ENNReal.ofReal (‖Q s y‖ ^ 2)) (fun s => ?_) τ
      simp only [show ∀ σ y, Q (σ + 1) y = Q σ y from hp]
    rw [e]
    exact h2
  · intro q hq
    have hZ : IsTimePeriodic (fun σ y => gradientAt (q σ) y) := by
      intro σ y
      simp only
      rw [show q (σ + 1) = q σ from funext (hq.2.1 σ)]
    have e1 : moveField R τ (fun σ y => gradientAt (q σ) y) =
        fun σ y => gradientAt (movePotential R τ q σ) y := by
      funext σ y
      show R (gradientAt (q (σ - τ)) (R.symm y)) = gradientAt (fun z => q (σ - τ) (R.symm z)) y
      rw [Cert.Internal.Invariance.gradientAt_pushForward R
        ((slice_contDiff hq.1 (σ - τ)).differentiable (by simp))]
    rw [pairing_move R τ hp hZ, e1]
    exact hg _ (isPeriodicTestPotential_move R τ hq)
  · intro ψ hψ
    rw [pairing_move R τ hp hψ.2.1, pairing_move R τ hFp hψ.2.1]
    exact ht _ (isPeriodicTestField_move R τ hψ)

end Internal.SolenoidalPart

theorem solenoidalModeHolds_of (hRot : AxialRotationHolds) (hH : GradSolenoidalDensityHolds) : SolenoidalModeHolds := by
  intro F hFm hFp hF2
  have hF := Internal.SolenoidalPart.memLp_of hFm hF2
  have hQ := Internal.SolenoidalPart.isSolenoidalPartOf_ofL2 hF
  obtain ⟨n1, n2⟩ := Internal.SolenoidalPart.norms_part hF
  refine ⟨_, hQ, n1, n2, fun Q' hQ' => Internal.SolenoidalPart.unique_part hH hQ hQ', fun τ φ => ?_⟩
  obtain ⟨R, hR⟩ := hRot.1 φ
  have hinv : ∀ x, axialRot (-φ) x = R.symm x := by
    intro x
    conv_lhs => rw [← R.apply_symm_apply x, hR]
    rw [← hRot.2.1, neg_add_cancel, hRot.2.2.1]
  have e : ∀ X : ℝ → Space → Space, (fun σ y => axialRot (-φ) (X (σ + τ) (axialRot φ y))) =
      fun σ y => R.symm (X (σ + τ) (R y)) := by
    intro X
    funext σ y
    rw [hinv, hR]
  rw [e, e]
  exact Internal.SolenoidalPart.isSolenoidalPartOf_move R τ hFp hQ

end Breakdown.Coercive
