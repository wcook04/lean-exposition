import TorusEuler.AmplificationAssembly
import TorusEuler.AmplificationPhysicalBounds

/-! The physical assumptions (2.4) and (2.5) supply a single normalized
amplification window for the wave-vector and amplitude comparisons. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingWaveVector

noncomputable section

/-- The older wave and the two physical strains on the prescribed time window. -/
structure PhysicalAmplification (I : Set ℝ) (t₀ : ℝ) where
  kp : ℝ → Space
  ap : ℝ → Space
  B : ℝ → Space →L[ℝ] Space
  E : ℝ → Space →L[ℝ] Space
  compact : IsCompact I
  activation : t₀ ∈ I
  older_continuous : ContinuousOn B I
  error_continuous : ContinuousOn E I
  trace_zero : ∀ t ∈ I, LinearMap.trace ℝ Space (B t).toLinearMap = 0
  preceding_data : ∀ t ∈ I, kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0
  preceding_vector : ∀ t ∈ I, HasDerivWithinAt kp (-((B t).adjoint (kp t))) I t
  preceding_amplitude : ∀ t ∈ I,
    HasDerivWithinAt ap (affineWaveAmplitudeOperator (B t) (kp t) (ap t)) I t
  first_coupling_positive : 0 < entry (frame kp ap t₀) (B t₀) 0 1
  third_coupling_positive : 0 < entry (frame kp ap t₀) (B t₀) 2 1

namespace PhysicalAmplification

variable {I : Set ℝ} {t₀ T : ℝ} {C₀ : ℕ} (w : PhysicalAmplification I t₀)

abbrev basis : ℝ → Fin 3 → Space := frame w.kp w.ap
def initialStrength : ℝ := ‖w.kp t₀‖ * ‖w.ap t₀‖
def firstCoupling : ℝ := entry (w.basis t₀) (w.B t₀) 0 1
def thirdCoupling : ℝ := entry (w.basis t₀) (w.B t₀) 2 1
def rate : ℝ := amplificationGrowthRate w.initialStrength w.firstCoupling
def ratio : ℝ := w.thirdCoupling / w.firstCoupling
def shear : ℝ := w.initialStrength / w.rate
def errorSize : ℝ :=
  amplificationPhysicalError I w.basis w.B w.E w.firstCoupling w.thirdCoupling w.rate
def clock (τ : ℝ) : ℝ := t₀ + τ / w.rate

def gradient (t : ℝ) : Space →L[ℝ] Space :=
  w.B t + InnerProductSpace.rankOne ℝ (w.ap t) (w.kp t) + w.E t

@[simp] theorem clock_zero : w.clock 0 = t₀ := by simp [clock]

theorem initialStrength_pos : 0 < w.initialStrength := by
  obtain ⟨hk, ha, _⟩ := w.preceding_data t₀ w.activation
  exact mul_pos (norm_pos_iff.mpr hk) (norm_pos_iff.mpr ha)

theorem rate_pos : 0 < w.rate :=
  amplificationGrowthRate_pos w.initialStrength_pos w.first_coupling_positive

theorem ratio_pos : 0 < w.ratio :=
  div_pos w.third_coupling_positive w.first_coupling_positive

theorem continuousOn_basis (i : Fin 3) : ContinuousOn (fun t => w.basis t i) I := by
  intro t ht
  obtain ⟨hk, ha, hp⟩ := w.preceding_data t ht
  have h := hasDerivWithinAt_movingFrame ht (w.B t) (w.trace_zero t ht)
    hk ha hp (w.preceding_vector t ht)
    (by simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht)
  fin_cases i
  · exact h.1.continuousWithinAt
  · exact h.2.1.continuousWithinAt
  · exact h.2.2.1.continuousWithinAt

/-- The physical window, with the inverse clock restricted to the normalized
slab, supplies all the estimates used by the normalized assembly. -/
def toNormalized (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀)
    (hclock : MapsTo w.clock (Icc 0 T) I)
    (hsmallε : (C₀ : ℝ) * w.ratio ≤ 1)
    (hsmallδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio) :
    AmplificationWindow T w.ratio w.shear w.errorSize := by
  have hε := amplification_epsilon_le_half (by omega : 2 ≤ C₀) w.ratio_pos.le hsmallε
  have hp₀ := w.preceding_data t₀ w.activation
  have hnorm := normalized_rates_of_physical_error (t₀ := t₀) (σ := w.initialStrength)
    (e := w.basis) (B := w.B) (E := w.E) w.compact w.activation
    (orthonormal_movingFrame hp₀.1 hp₀.2.1 hp₀.2.2) w.continuousOn_basis
    w.older_continuous w.error_continuous w.initialStrength_pos
    w.first_coupling_positive w.third_coupling_positive (hε.trans (by norm_num))
  have hδ : 0 ≤ w.errorSize := hnorm.1
  have hinv : w.shear⁻¹ ≤ 2 * w.errorSize := hnorm.2.1
  have hshear : 0 < w.shear := div_pos w.initialStrength_pos w.rate_pos
  have hsmall :=
    amplification_normalized_smallness hT hδ w.ratio_pos.le hshear hinv hC₀ hsmallε hsmallδ
  have hclockC : Continuous w.clock := continuous_const.add (continuous_id.div_const _)
  refine
    { kp := fun t => w.kp (w.clock t)
      ap := fun t => w.ap (w.clock t)
      B := fun t => (1 / w.rate) • w.B (w.clock t)
      E := fun t => (1 / w.rate) • w.E (w.clock t)
      timeLower := hT
      ratioPositive := w.ratio_pos
      ratioSmall := hε
      shearLower := (show 1 ≤ T ^ 2 by nlinarith [sq_nonneg (T - 2)]).trans hsmall.2.2.2
      inverseShear := hinv
      errorNonnegative := hδ
      smallness := hsmall.2.1
      older_continuous := (w.older_continuous.comp hclockC.continuousOn hclock).const_smul
        (1 / w.rate : ℝ)
      error_continuous := (w.error_continuous.comp hclockC.continuousOn hclock).const_smul
        (1 / w.rate : ℝ)
      trace_zero := fun t ht => normalized_trace_zero (w.trace_zero _ (hclock ht))
      preceding_data := fun t ht => w.preceding_data _ (hclock ht)
      preceding_vector := ?_
      preceding_amplitude := ?_
      older_bound := fun t ht => (hnorm.2.2 _ (hclock ht)).1
      error_bound := fun t ht => (hnorm.2.2 _ (hclock ht)).2.1
      first_coupling := fun t ht => (hnorm.2.2 _ (hclock ht)).2.2.1
      third_coupling := fun t ht => (hnorm.2.2 _ (hclock ht)).2.2.2 }
  · intro t ht
    exact (normalized_affineWave_derivatives hclock (w.preceding_vector _ (hclock ht))
      (by simpa only [affineWaveAmplitudeOperator_apply, clock] using
        w.preceding_amplitude _ (hclock ht))).1
  · intro t ht
    simpa only [affineWaveAmplitudeOperator_apply, clock] using
      (normalized_affineWave_derivatives hclock (w.preceding_vector _ (hclock ht))
        (by simpa only [affineWaveAmplitudeOperator_apply, clock] using
          w.preceding_amplitude _ (hclock ht))).2

/-- A prescribed wave over the full physical strain obeys the normalized
equation for the same wave after the change of clock. -/
theorem rescale_wave {k a : ℝ → Space} (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀)
    (hclock : MapsTo w.clock (Icc 0 T) I)
    (hsmallε : (C₀ : ℝ) * w.ratio ≤ 1)
    (hsmallδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio)
    (hk : ∀ t ∈ I, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) I t)
    (ha : ∀ t ∈ I,
      HasDerivWithinAt a (affineWaveAmplitudeOperator (w.gradient t) (k t) (a t)) I t) :
    let W := w.toNormalized hT hC₀ hclock hsmallε hsmallδ
    let K := k ∘ w.clock
    let A := a ∘ w.clock
    (∀ t ∈ Icc 0 T, HasDerivWithinAt K (-((W.gradient t).adjoint (K t))) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T,
      HasDerivWithinAt A (affineWaveAmplitudeOperator (W.gradient t) (K t) (A t)) (Icc 0 T) t) := by
  obtain ⟨hkp₀, hap₀, _⟩ := w.preceding_data t₀ w.activation
  have hrescale (t : ℝ) (ht : t ∈ Icc 0 T) :=
    normalized_newWave_derivatives (kp := w.kp) (ap := w.ap) (k := k) (a := a)
      (B := w.B (w.clock t)) (E := w.E (w.clock t)) w.rate_pos.ne' hclock hkp₀ hap₀
      (w.preceding_data _ (hclock ht)).1 (w.preceding_data _ (hclock ht)).2.1
      (hk _ (hclock ht))
      (by simpa only [gradient, affineWaveAmplitudeOperator_apply, clock] using ha _ (hclock ht))
  constructor
  · intro t ht
    simpa only [toNormalized, AmplificationWindow.gradient, AmplificationWindow.basis,
      AmplificationWindow.shearRatio, Function.comp_apply, Function.comp_def, shear,
      initialStrength, clock] using (hrescale t ht).1
  · intro t ht
    simpa only [toNormalized, AmplificationWindow.gradient, AmplificationWindow.basis,
      AmplificationWindow.shearRatio, Function.comp_apply, Function.comp_def, shear,
      initialStrength, clock, affineWaveAmplitudeOperator_apply] using (hrescale t ht).2

end PhysicalAmplification

end

end TorusEuler.MovingWaveVector
