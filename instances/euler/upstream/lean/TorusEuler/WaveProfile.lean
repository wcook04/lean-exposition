import TorusEuler.PhaseCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! The smooth phase profiles in Lemma 3.1 of the frozen torus paper. -/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TorusEuler

noncomputable section

/-- An even smooth bump supported in `[-1/8, 1/8]` with value one at zero. -/
def waveBump (s : ℝ) : ℝ :=
  Real.smoothTransition (1 - 64 * s ^ 2)

private theorem contDiff_waveBump : ContDiff ℝ ∞ waveBump :=
  Real.smoothTransition.contDiff.comp (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => 1 - 64 * s ^ 2))

private theorem waveBump_even (s : ℝ) : waveBump (-s) = waveBump s := by
  simp [waveBump]

@[simp] theorem waveBump_zero : waveBump 0 = 1 := by simp [waveBump]

private theorem waveBump_zero_of_abs_ge {s : ℝ} (hs : 1 / 8 ≤ |s|) : waveBump s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hs' := mul_le_mul hs hs (by norm_num : (0 : ℝ) ≤ 1 / 8) (abs_nonneg s)
  have hs'' : (1 / 8 : ℝ) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs s]
    simpa only [pow_two] using hs'
  linarith

private theorem waveBump_scaled_zero {h s : ℝ} (hh : 0 < h) (hs : h / 8 ≤ |s|) :
    waveBump (s / h) = 0 := by
  apply waveBump_zero_of_abs_ge
  rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
  linarith

/-- The scaled bump extended with period one using the nearest integer. -/
def periodicWaveBump (h s : ℝ) : ℝ :=
  waveBump ((s - (⌊s + 1 / 2⌋ : ℝ)) / h)

theorem periodic_periodicWaveBump (h : ℝ) : Function.Periodic (periodicWaveBump h) 1 := by
  intro s
  unfold periodicWaveBump
  rw [show s + 1 + 1 / 2 = s + 1 / 2 + 1 by ring, Int.floor_add_one,
    Int.cast_add, Int.cast_one]
  congr 2
  ring

private theorem abs_sub_floor_half_le (s : ℝ) : |s - (⌊s + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · linarith [Int.floor_le (s + 1 / 2)]
  · linarith [Int.lt_floor_add_one (s + 1 / 2)]

/-- Each copy agrees with the periodic bump throughout a neighborhood of its closed cell. -/
private theorem periodicWaveBump_eq_translate {h s : ℝ} (hh : 0 < h) (hle : h ≤ 1)
    (z : ℤ) (hs : |s - z| < 3 / 4) :
    periodicWaveBump h s = waveBump ((s - z) / h) := by
  let c : ℤ := ⌊s + 1 / 2⌋
  change waveBump ((s - c) / h) = waveBump ((s - z) / h)
  by_cases hz : c = z
  · rw [hz]
  have hc : |s - c| ≤ 1 / 2 := abs_sub_floor_half_le s
  have hsep : (1 : ℝ) ≤ |(c : ℝ) - z| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hz)
  have htri : |(c : ℝ) - z| ≤ |s - c| + |s - z| := by
    have ht := dist_triangle (c : ℝ) s (z : ℝ)
    rw [dist_comm (c : ℝ) s] at ht
    simpa only [Real.dist_eq] using ht
  rw [waveBump_scaled_zero hh (by linarith : h / 8 ≤ |s - c|),
    waveBump_scaled_zero hh (by linarith : h / 8 ≤ |s - z|)]

private theorem periodicWaveBump_eventuallyEq_translate {h s : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    periodicWaveBump h =ᶠ[𝓝 s] (fun t => waveBump ((t - (⌊s + 1 / 2⌋ : ℝ)) / h)) := by
  let z : ℤ := ⌊s + 1 / 2⌋
  have hs : s ∈ Metric.ball (z : ℝ) (3 / 4) := by
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [abs_sub_floor_half_le s]
  filter_upwards [Metric.isOpen_ball.mem_nhds hs] with t ht
  exact periodicWaveBump_eq_translate hh hle z (by simpa only [Metric.mem_ball, Real.dist_eq] using ht)

theorem contDiff_periodicWaveBump {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    ContDiff ℝ ∞ (periodicWaveBump h) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hs : ContDiff ℝ ∞ (fun t => waveBump ((t - (⌊s + 1 / 2⌋ : ℝ)) / h)) :=
    contDiff_waveBump.comp (by fun_prop)
  exact hs.contDiffAt.congr_of_eventuallyEq (periodicWaveBump_eventuallyEq_translate hh hle)

private theorem periodicWaveBump_even {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    periodicWaveBump h (-s) = periodicWaveBump h s := by
  let z : ℤ := ⌊s + 1 / 2⌋
  have hs : |s - z| ≤ 1 / 2 := abs_sub_floor_half_le s
  have hneg : |(-s) - ((-z : ℤ) : ℝ)| = |s - z| := by
    rw [Int.cast_neg, show -s - -(z : ℝ) = -(s - (z : ℝ)) by ring, abs_neg]
  rw [periodicWaveBump_eq_translate hh hle (-z) (by rw [hneg]; linarith),
    periodicWaveBump_eq_translate hh hle z (by linarith)]
  rw [Int.cast_neg, show -s - -(z : ℝ) = -(s - (z : ℝ)) by ring, neg_div, waveBump_even]

private theorem periodicWaveBump_eq_on_cell {h s : ℝ} (hh : 0 < h) (hle : h ≤ 1)
    (hs : s ∈ Icc (-(1 / 2)) (1 / 2)) :
    periodicWaveBump h s = waveBump (s / h) := by
  have h := periodicWaveBump_eq_translate (s := s) hh hle 0 (by
    simp only [Int.cast_zero, sub_zero, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  simpa only [Int.cast_zero, sub_zero] using h

private theorem periodicWaveBump_nonneg (h s : ℝ) : 0 ≤ periodicWaveBump h s :=
  Real.smoothTransition.nonneg _

private theorem periodicWaveBump_le_one (h s : ℝ) : periodicWaveBump h s ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem phaseMean_periodicWaveBump_le {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    phaseMean (periodicWaveBump h) ≤ h / 4 := by
  have hshift := (periodic_periodicWaveBump h).intervalIntegral_add_eq 0 (-(1 / 2))
  rw [zero_add, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at hshift
  have hshort :
      (∫ s in (-(1 / 2) : ℝ)..(1 / 2), periodicWaveBump h s) =
        ∫ s in (-(h / 8))..(h / 8), periodicWaveBump h s := by
    rw [intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2),
      intervalIntegral.integral_of_le (by linarith : -(h / 8) ≤ h / 8)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    · intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro s hs
      have hcell : s ∈ Icc (-(1 / 2)) (1 / 2) := ⟨hs.1.1.le, hs.1.2⟩
      have ha : h / 8 ≤ |s| := by
        by_contra! ha
        have hb := abs_lt.mp ha
        exact hs.2 ⟨hb.1, hb.2.le⟩
      rw [periodicWaveBump_eq_on_cell hh hle hcell, waveBump_scaled_zero hh ha]
  unfold phaseMean
  rw [hshift, hshort]
  have hc := (contDiff_periodicWaveBump hh hle).continuous
  calc
    (∫ s in (-(h / 8))..(h / 8), periodicWaveBump h s)
        ≤ ∫ _ in (-(h / 8))..(h / 8), (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun s _ => periodicWaveBump_le_one h s)
    _ = h / 4 := by simp; ring

/-- The mean-free slope, divided by its value at phase zero. -/
def waveSlope (h s : ℝ) : ℝ :=
  (periodicWaveBump h s - phaseMean (periodicWaveBump h)) /
    (1 - phaseMean (periodicWaveBump h))

private theorem waveSlope_denom_pos {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    0 < 1 - phaseMean (periodicWaveBump h) := by
  linarith [phaseMean_periodicWaveBump_le hh hle]

private theorem contDiff_waveSlope {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    ContDiff ℝ ∞ (waveSlope h) :=
  ((contDiff_periodicWaveBump hh hle).sub contDiff_const).div_const _

private theorem periodic_waveSlope (h : ℝ) : Function.Periodic (waveSlope h) 1 := by
  intro s
  simp only [waveSlope, periodic_periodicWaveBump h s]

private theorem waveSlope_even {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    waveSlope h (-s) = waveSlope h s := by
  simp only [waveSlope, periodicWaveBump_even hh hle s]

private theorem phaseMean_waveSlope {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    phaseMean (waveSlope h) = 0 := by
  change phaseMean (fun s =>
    (periodicWaveBump h s - phaseMean (periodicWaveBump h)) /
      (1 - phaseMean (periodicWaveBump h))) = 0
  simp only [div_eq_inv_mul]
  change phaseMean (fun s => (1 - phaseMean (periodicWaveBump h))⁻¹ •
    phaseOscillation (periodicWaveBump h) s) = 0
  rw [phaseMean_const_smul]
  rw [phaseMean_phaseOscillation (contDiff_periodicWaveBump hh hle).continuous, smul_zero]

private theorem waveSlope_zero {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    waveSlope h 0 = 1 := by
  unfold waveSlope
  rw [periodicWaveBump_eq_on_cell hh hle (by norm_num : (0 : ℝ) ∈ Icc (-(1 / 2)) (1 / 2)),
    zero_div, waveBump_zero, div_self (waveSlope_denom_pos hh hle).ne']

private theorem waveSlope_bounds {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    -(h / 2) ≤ waveSlope h s ∧ waveSlope h s ≤ 1 := by
  let c := phaseMean (periodicWaveBump h)
  have hc := phaseMean_periodicWaveBump_le hh hle
  have hdenom : (1 / 2 : ℝ) ≤ 1 - c := by linarith
  change -(h / 2) ≤ (periodicWaveBump h s - c) / (1 - c) ∧
    (periodicWaveBump h s - c) / (1 - c) ≤ 1
  constructor
  · rw [le_div_iff₀ (waveSlope_denom_pos hh hle)]
    have hmul := mul_le_mul_of_nonneg_right hdenom (by positivity : 0 ≤ h / 2)
    linarith [periodicWaveBump_nonneg h s]
  · rw [div_le_iff₀ (waveSlope_denom_pos hh hle), one_mul]
    linarith [periodicWaveBump_le_one h s]

/-- The odd phase profile based at phase zero. -/
def waveProfile (h s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, waveSlope h t

/-- The zero-mean pressure primitive of the phase profile. -/
def wavePressurePrimitive (h : ℝ) : ℝ → ℝ :=
  phasePrimitive (waveProfile h)

@[simp] theorem waveProfile_zero (h : ℝ) : waveProfile h 0 = 0 := by simp [waveProfile]

theorem hasDerivAt_waveProfile {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    HasDerivAt (waveProfile h) (waveSlope h s) s := by
  have hc := (contDiff_waveSlope hh hle).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem contDiff_of_smooth_derivative {f df : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (df s) s) (hdf : ContDiff ℝ ∞ df) : ContDiff ℝ ∞ f := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (hf s).differentiableAt, ?_⟩
  rwa [show deriv f = df from funext (fun s => (hf s).deriv)]

theorem contDiff_waveProfile {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) : ContDiff ℝ ∞ (waveProfile h) :=
  contDiff_of_smooth_derivative (hasDerivAt_waveProfile hh hle) (contDiff_waveSlope hh hle)

theorem periodic_waveProfile {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    Function.Periodic (waveProfile h) 1 := by
  intro s
  have hc := (contDiff_waveSlope hh hle).continuous
  have hsum := (periodic_waveSlope h).intervalIntegral_add_eq_add 0 s
    (fun a b => hc.intervalIntegrable a b)
  rw [zero_add, ← phaseMean, phaseMean_waveSlope hh hle, add_zero] at hsum
  exact hsum

theorem odd_waveProfile {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    Function.Odd (waveProfile h) := by
  intro s
  unfold waveProfile
  have hneg := intervalIntegral.integral_comp_neg (f := waveSlope h) (a := 0) (b := s)
  simp only [waveSlope_even hh hle, neg_zero] at hneg
  rw [intervalIntegral.integral_symm, ← hneg]

theorem phaseMean_waveProfile {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    phaseMean (waveProfile h) = 0 := by
  have hshift := (periodic_waveProfile hh hle).intervalIntegral_add_eq 0 (-1)
  rw [zero_add, neg_add_cancel] at hshift
  have hneg := intervalIntegral.integral_comp_neg (f := waveProfile h) (a := 0) (b := 1)
  rw [neg_zero] at hneg
  have ho (s : ℝ) : waveProfile h (-s) = -waveProfile h s := odd_waveProfile hh hle s
  simp only [ho, intervalIntegral.integral_neg] at hneg
  unfold phaseMean
  linarith

theorem hasDerivAt_wavePressurePrimitive {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    HasDerivAt (wavePressurePrimitive h) (waveProfile h s) s :=
  hasDerivAt_phasePrimitive (contDiff_waveProfile hh hle).continuous s

theorem contDiff_wavePressurePrimitive {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    ContDiff ℝ ∞ (wavePressurePrimitive h) :=
  contDiff_of_smooth_derivative (hasDerivAt_wavePressurePrimitive hh hle)
    (contDiff_waveProfile hh hle)

theorem periodic_wavePressurePrimitive {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    Function.Periodic (wavePressurePrimitive h) 1 :=
  periodic_phasePrimitive (contDiff_waveProfile hh hle).continuous
    (periodic_waveProfile hh hle) (phaseMean_waveProfile hh hle)

theorem phaseMean_wavePressurePrimitive {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    phaseMean (wavePressurePrimitive h) = 0 :=
  phaseMean_phasePrimitive (contDiff_waveProfile hh hle).continuous

theorem hasDerivAt_waveProfile_zero {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) :
    HasDerivAt (waveProfile h) 1 0 := by
  simpa only [waveSlope_zero hh hle] using hasDerivAt_waveProfile hh hle 0

theorem deriv_waveProfile_bounds {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    -(h / 2) ≤ deriv (waveProfile h) s ∧ deriv (waveProfile h) s ≤ 1 := by
  rw [(hasDerivAt_waveProfile hh hle s).deriv]
  exact waveSlope_bounds hh hle s

theorem norm_waveProfile_le {h : ℝ} (hh : 0 < h) (hle : h ≤ 1) (s : ℝ) :
    ‖waveProfile h s‖ ≤ h / 2 := by
  have hper := periodic_waveProfile hh hle
  have hreduce : waveProfile h (Int.fract s) = waveProfile h s := by
    simpa only [Int.fract, mul_one] using hper.sub_int_mul_eq (x := s) ⌊s⌋
  rw [← hreduce, Real.norm_eq_abs, abs_le]
  let t := Int.fract s
  have ht0 : 0 ≤ t := Int.fract_nonneg s
  have ht1 : t ≤ 1 := (Int.fract_lt_one s).le
  have hc := (contDiff_waveSlope hh hle).continuous
  have hlower (a b : ℝ) (hab : a ≤ b) :
      (b - a) * (-(h / 2)) ≤ ∫ u in a..b, waveSlope h u := by
    simpa [mul_div_assoc] using intervalIntegral.integral_mono_on (μ := volume) hab
      (continuous_const.intervalIntegrable a b) (hc.intervalIntegrable a b)
      (fun u _ => (waveSlope_bounds hh hle u).1)
  have ht := hlower 0 t ht0
  have hrest := hlower t 1 ht1
  have hsum := intervalIntegral.integral_add_adjacent_intervals (f := waveSlope h) (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t 1)
  rw [← phaseMean, phaseMean_waveSlope hh hle] at hsum
  change -(h / 2) ≤ (∫ u in (0 : ℝ)..t, waveSlope h u) ∧
    (∫ u in (0 : ℝ)..t, waveSlope h u) ≤ h / 2
  constructor
  · nlinarith
  · nlinarith

private theorem exists_iteratedDeriv_waveBump_bound (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ s, ‖iteratedDeriv n waveBump s‖ ≤ M := by
  have hc := (contDiff_waveBump.continuous_iteratedDeriv n (by simp)).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(1 / 4 : ℝ)) (b := 1 / 4)).bddAbove_image
    hc.continuousOn
  refine ⟨max 1 M, zero_lt_one.trans_le (le_max_left _ _), fun s => ?_⟩
  by_cases hs : s ∈ Icc (-(1 / 4)) (1 / 4)
  · exact (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)
  · have hs' : (1 / 8 : ℝ) < |s| := by
      rw [mem_Icc, not_and_or] at hs
      rcases hs with hs | hs
      · linarith [neg_le_abs s]
      · linarith [le_abs_self s]
    have hz : waveBump =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      have hopen : IsOpen {x : ℝ | 1 / 8 < |x|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hs'] with x hx
      exact waveBump_zero_of_abs_ge (show 1 / 8 < |x| from hx).le
    simp only [hz.iteratedDeriv_eq n, iteratedDeriv_const, ite_self, norm_zero]
    exact zero_le_one.trans (le_max_left _ _)

private theorem iteratedDeriv_periodicWaveBump_eq {h : ℝ} (hh : 0 < h) (hle : h ≤ 1)
    (n : ℕ) (s : ℝ) :
    iteratedDeriv n (periodicWaveBump h) s =
      h⁻¹ ^ n * iteratedDeriv n waveBump ((s - (⌊s + 1 / 2⌋ : ℝ)) / h) := by
  calc
    iteratedDeriv n (periodicWaveBump h) s =
        iteratedDeriv n (fun t => waveBump ((t - (⌊s + 1 / 2⌋ : ℝ)) / h)) s :=
      (periodicWaveBump_eventuallyEq_translate hh hle).iteratedDeriv_eq n
    _ = _ := by
      let z : ℝ := ⌊s + 1 / 2⌋
      change iteratedDeriv n (fun t => waveBump ((t - z) / h)) s =
        h⁻¹ ^ n * iteratedDeriv n waveBump ((s - z) / h)
      simp only [div_eq_inv_mul]
      rw [iteratedDeriv_comp_sub_const n (fun t => waveBump (h⁻¹ * t)) z,
        iteratedDeriv_comp_const_mul (contDiff_waveBump.of_le (by simp))]

private theorem iteratedDeriv_waveSlope_eq {h : ℝ} (hh : 0 < h) (hle : h ≤ 1)
    {n : ℕ} (hn : 0 < n) (s : ℝ) :
    iteratedDeriv n (waveSlope h) s =
      iteratedDeriv n (periodicWaveBump h) s / (1 - phaseMean (periodicWaveBump h)) := by
  let c := phaseMean (periodicWaveBump h)
  change iteratedDeriv n ((fun t => periodicWaveBump h t - c) · / (1 - c)) s =
    iteratedDeriv n (periodicWaveBump h) s / (1 - c)
  rw [iteratedDeriv_div_const, iteratedDeriv_fun_sub
    ((contDiff_periodicWaveBump hh hle).of_le (by simp)).contDiffAt contDiffAt_const]
  simp [iteratedDeriv_const, hn.ne']

/-- The order-dependent estimates in Lemma 3.1, uniform in the phase and the scale. -/
theorem exists_iteratedDeriv_waveProfile_bound (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
      ‖iteratedDeriv j (waveProfile h) s‖ ≤ C * h ^ (1 - (j : ℤ)) := by
  let n := j - 1
  have hn : 0 < n := by omega
  have hj' : j = n + 1 := by omega
  have hpower : (1 - (j : ℤ)) = -(n : ℤ) := by omega
  obtain ⟨M, hM, hbound⟩ := exists_iteratedDeriv_waveBump_bound n
  refine ⟨2 * M, by positivity, fun h hh hle s => ?_⟩
  have hdenom : (1 / 2 : ℝ) ≤ 1 - phaseMean (periodicWaveBump h) := by
    linarith [phaseMean_periodicWaveBump_le hh hle]
  have hinv : (1 - phaseMean (periodicWaveBump h))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (waveSlope_denom_pos hh hle)]
    linarith
  have hderiv : deriv (waveProfile h) = waveSlope h :=
    funext fun t => (hasDerivAt_waveProfile hh hle t).deriv
  rw [hpower, zpow_neg, zpow_natCast, ← inv_pow]
  conv_lhs => rw [hj', iteratedDeriv_succ', hderiv, iteratedDeriv_waveSlope_eq hh hle hn,
    iteratedDeriv_periodicWaveBump_eq hh hle]
  rw [norm_div, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ h⁻¹ ^ n),
    Real.norm_of_nonneg (waveSlope_denom_pos hh hle).le, div_eq_mul_inv]
  calc
    _ ≤ h⁻¹ ^ n * M * 2 := by
      gcongr
      exact hbound _
    _ = 2 * M * h⁻¹ ^ n := by ring

/-- The profiles and uniform bounds of Lemma 3.1. -/
theorem lemma31_waveProfile :
    ∃ C : ℝ, 0 < C ∧
    (∀ h, 0 < h → h ≤ 1 →
      ContDiff ℝ ∞ (waveProfile h) ∧ Function.Odd (waveProfile h) ∧
      Function.Periodic (waveProfile h) 1 ∧
      ContDiff ℝ ∞ (wavePressurePrimitive h) ∧ Function.Periodic (wavePressurePrimitive h) 1 ∧
      phaseMean (wavePressurePrimitive h) = 0 ∧
      (∀ s, HasDerivAt (wavePressurePrimitive h) (waveProfile h s) s) ∧
      deriv (waveProfile h) 0 = 1 ∧
      ∀ s, -C * h ≤ deriv (waveProfile h) s ∧ deriv (waveProfile h) s ≤ 1 ∧
        ‖waveProfile h s‖ ≤ C * h) ∧
    (∀ j : ℕ, 2 ≤ j → ∃ Cj : ℝ, 0 < Cj ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
      ‖iteratedDeriv j (waveProfile h) s‖ ≤ Cj * h ^ (1 - (j : ℤ))) := by
  refine ⟨1 / 2, by norm_num, ?_, exists_iteratedDeriv_waveProfile_bound⟩
  intro h hh hle
  refine ⟨contDiff_waveProfile hh hle, odd_waveProfile hh hle, periodic_waveProfile hh hle,
    contDiff_wavePressurePrimitive hh hle, periodic_wavePressurePrimitive hh hle,
    phaseMean_wavePressurePrimitive hh hle, hasDerivAt_wavePressurePrimitive hh hle,
    (hasDerivAt_waveProfile_zero hh hle).deriv, fun s => ?_⟩
  have hb := deriv_waveProfile_bounds hh hle s
  refine ⟨?_, hb.2, ?_⟩
  · linarith [hb.1]
  · linarith [norm_waveProfile_le hh hle s]

end

end TorusEuler
