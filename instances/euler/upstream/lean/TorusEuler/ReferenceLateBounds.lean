import TorusEuler.ReferenceRiccati
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace TorusEuler.ReferenceRiccati

noncomputable section

private theorem intervalIntegrable_of_continuousOn_forward {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable f MeasureTheory.volume a b :=
  (hf.mono (fun _ ht => ha.trans ((uIcc_of_le hab).subset ht).1)).intervalIntegrable

/-- The ratio of canonical amplitudes is the exponential of the integrated rate. -/
theorem referenceV_ratio_eq_exp_integral {Y : ℝ → ℝ}
    (hY : ContinuousOn Y (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    referenceV Y b / referenceV Y a = Real.exp (∫ t in a..b, Y t) := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_continuousOn_forward hY le_rfl ha)
    (intervalIntegrable_of_continuousOn_forward hY ha hab)
  unfold referenceV
  rw [← Real.exp_sub, ← hadd]
  ring_nf

/-- The turning time of the reference rate maximizes the canonical amplitude
on the entire nonnegative time axis. -/
theorem referenceV_le_at_turning_time {Y : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hY : ContinuousOn Y (Ici 0))
    (hbefore : ∀ t ∈ Icc 0 a, 0 ≤ Y t) (hafter : ∀ t ∈ Ici a, Y t ≤ 0) :
    ∀ t ∈ Ici 0, referenceV Y t ≤ referenceV Y a := by
  intro t ht
  rcases le_or_gt t a with hta | hat
  · have hi : 0 ≤ ∫ u in t..a, Y u :=
      intervalIntegral.integral_nonneg hta fun u hu => hbefore u ⟨ht.trans hu.1, hu.2⟩
    have h := Real.one_le_exp hi
    rw [← referenceV_ratio_eq_exp_integral hY ht hta] at h
    exact (le_div_iff₀ (referenceV_pos Y t)).mp h |>.trans_eq' (one_mul _)
  · have hi : (∫ u in a..t, Y u) ≤ 0 := by
      simpa only [intervalIntegral.integral_neg, neg_nonneg] using
        (intervalIntegral.integral_nonneg (f := fun u => -Y u) hat.le
          fun u hu => neg_nonneg.mpr (hafter u hu.1))
    have h := Real.exp_le_one_iff.mpr hi
    rw [← referenceV_ratio_eq_exp_integral hY ha hat.le] at h
    exact (div_le_iff₀ (referenceV_pos Y a)).mp h |>.trans_eq (one_mul _)

/-- The gain in Lemma 2.4 bounds the initial unit of the reference amplitude. -/
theorem referenceV_initial_window {ε τm τ : ℝ} {Y : ℝ → ℝ}
    (hY : ContinuousOn Y (Ici 0)) (hcap : ∀ t ∈ Ici 0, Y t ≤ 1)
    (hgain : (Real.sqrt ε)⁻¹ - 1 ≤ ∫ t in 0..τm, Y t) (hτ : τ ∈ Icc 0 1) :
    referenceV Y τ ≤ Real.exp (2 - (Real.sqrt ε)⁻¹) * referenceV Y τm := by
  have hi := intervalIntegral.integral_mono_on hτ.1
    (intervalIntegrable_of_continuousOn_forward hY le_rfl hτ.1)
    (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (1 : ℝ))) (fun t ht => hcap t ht.1)
  have hi₁ : (∫ t in 0..τ, Y t) ≤ 1 := by simpa using hi.trans (by simpa using hτ.2)
  unfold referenceV
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The early gain bound (2.15), under the amplitude comparison (2.9).
The amplitude at the turning time can be replaced by any larger maximum. -/
theorem amplitude_initial_window_of_reference_comparison {ε T τm τ : ℝ}
    {Y A : ℝ → ℝ} (hε : 2 * ε ≤ 1)
    (hY : ContinuousOn Y (Ici 0)) (hcap : ∀ t ∈ Ici 0, Y t ≤ 1)
    (hgain : (Real.sqrt ε)⁻¹ - 1 ≤ ∫ t in 0..τm, Y t)
    (hτ : τ ∈ Icc 0 1) (hτT : τ ≤ T) (hm : τm ∈ Icc 0 T)
    (hcompare : ∀ t ∈ Icc 0 T,
      Real.exp (-ε) * referenceV Y t ≤ A t ∧ A t ≤ Real.exp ε * referenceV Y t) :
    A τ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * A τm := by
  have hpeak : 0 ≤ A τm := le_trans (by positivity [referenceV_pos Y τm]) (hcompare τm hm).1
  calc
    _ ≤ Real.exp ε * referenceV Y τ := (hcompare τ ⟨hτ.1, hτT⟩).2
    _ ≤ Real.exp ε * (Real.exp (2 - (Real.sqrt ε)⁻¹) * referenceV Y τm) :=
      mul_le_mul_of_nonneg_left (referenceV_initial_window hY hcap hgain hτ) (Real.exp_pos _).le
    _ = Real.exp (2 + 2 * ε - (Real.sqrt ε)⁻¹) * (Real.exp (-ε) * referenceV Y τm) := by
      rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (2 + 2 * ε - (Real.sqrt ε)⁻¹) * A τm :=
      mul_le_mul_of_nonneg_left (hcompare τm hm).1 (Real.exp_pos _).le
    _ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * A τm :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hpeak

private theorem continuous_damping_quarter (ε : ℝ) : Continuous (fun t => damping ε t / 4) :=
  continuous_iff_continuousAt.mpr fun t => by
    have hs := (hasDerivAt_s ε t).continuousAt
    have hx := (hasDerivAt_x ε t).continuousAt
    unfold damping
    fun_prop

private theorem continuousOn_deviation_envelope {ε : ℝ} {Y e : ℝ → ℝ}
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0)) :
    ContinuousOn (fun t => s ε t * (1 + e t)) (Ici 0) := by
  have heq : (fun t => s ε t * (1 + e t)) = fun t => Y t + damping ε t / 4 := by
    funext t
    rw [hform, referenceY]
    ring
  rw [heq]
  exact hY.add ((continuous_damping_quarter ε).continuousOn)

private theorem hasDerivAt_log_damping {ε t : ℝ} :
    HasDerivAt (fun u => -(Real.log (s ε u)) / 2) (damping ε t / 4) t := by
  have hs := (s_pos ε t).ne'
  refine (((hasDerivAt_s ε t).log hs).neg.div_const 2).congr_deriv ?_
  field_simp
  ring

private theorem sqrt_s_div_s_eq_exp {ε a b : ℝ} :
    Real.sqrt (s ε b / s ε a) = Real.exp ((Real.log (s ε b) - Real.log (s ε a)) / 2) := by
  have hpos := div_pos (s_pos ε b) (s_pos ε a)
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos,
    Real.log_div (s_pos ε b).ne' (s_pos ε a).ne']
  congr 1
  ring

/-- The exact tail formula in Proposition 2.6, with its prefactor expressed
as the square root of the ratio of clock factors. -/
theorem referenceV_ratio_decomposition {ε a b : ℝ} {Y e : ℝ → ℝ}
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0)) (ha : 0 ≤ a) (hab : a ≤ b) :
    referenceV Y b / referenceV Y a =
      Real.sqrt (s ε b / s ε a) * Real.exp (∫ t in a..b, s ε t * (1 + e t)) := by
  have hp := intervalIntegrable_of_continuousOn_forward
    (continuousOn_deviation_envelope hform hY) ha hab
  have hD : IntervalIntegrable (fun t => damping ε t / 4) MeasureTheory.volume a b :=
    (continuous_damping_quarter ε).intervalIntegrable a b
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_log_damping (ε := ε) (t := t)) hD
  have hsplit : Y = fun t => s ε t * (1 + e t) - damping ε t / 4 := hform
  rw [referenceV_ratio_eq_exp_integral hY ha hab, hsplit,
    intervalIntegral.integral_sub hp hD, hd, sqrt_s_div_s_eq_exp, ← Real.exp_add]
  congr 1
  ring

theorem s_le_inv_x {ε t : ℝ} (hx : 0 < x ε t) : s ε t ≤ (x ε t)⁻¹ := by
  unfold s
  apply inv_anti₀ hx
  have h := Real.sqrt_le_sqrt (show x ε t ^ 2 ≤ 1 + x ε t ^ 2 by linarith)
  simpa only [Real.sqrt_sq hx.le] using h

theorem inv_two_mul_x_le_s {ε t : ℝ} (hx : 1 ≤ x ε t) : (2 * x ε t)⁻¹ ≤ s ε t := by
  unfold s
  apply inv_anti₀ (by positivity)
  apply (Real.sqrt_le_left (by linarith)).mpr
  nlinarith [sq_nonneg (x ε t - 1)]

private theorem hasDerivAt_inv_square_primitive {ε t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => -(4 / ε) / u) (4 / (ε * t ^ 2)) t := by
  refine ((hasDerivAt_const t (-(4 / ε))).div (hasDerivAt_id t) ht).congr_deriv ?_
  simp only [id, zero_mul, mul_one, zero_sub, neg_neg]
  ring

/-- On the entire ray after the peak, the positive part of the integrated rate
has the uniform bound used in Proposition 2.6. -/
theorem reference_tail_integral_bounds {ε a b : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (ha : 2 / ε ≤ a) (hab : a ≤ b)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8))) :
    0 ≤ (∫ t in a..b, s ε t * (1 + e t)) ∧
      (∫ t in a..b, s ε t * (1 + e t)) ≤ 2 := by
  have ha₀ := lt_of_lt_of_le (show 0 < 2 / ε by positivity) ha
  have hεa : 2 ≤ ε * a := by rw [mul_comm]; exact (div_le_iff₀ hε).mp ha
  have hc := continuousOn_deviation_envelope hform hY
  have hi := intervalIntegrable_of_continuousOn_forward hc ha₀.le hab
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < t := ha₀.trans_le ht.1
  have hmajC : ContinuousOn (fun t => 4 / (ε * t ^ 2)) (Icc a b) := by
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    have ht₀ := hpos t ht
    positivity
  have hmajI : IntervalIntegrable (fun t => 4 / (ε * t ^ 2)) MeasureTheory.volume a b :=
    (hmajC.mono (uIcc_of_le hab).subset).intervalIntegrable
  constructor
  · exact intervalIntegral.integral_nonneg hab fun t ht =>
      mul_nonneg (s_pos ε t).le (by linarith [(he (hpos t ht).le).1])
  · have hcompare := intervalIntegral.integral_mono_on hab hi hmajI (by
      intro t ht
      have ht₀ := hpos t ht
      have hx : 0 < x ε t := by unfold x; positivity
      calc
        _ ≤ s ε t * 2 := mul_le_mul_of_nonneg_left (by linarith [(he ht₀.le).2]) (s_pos ε t).le
        _ ≤ (x ε t)⁻¹ * 2 := mul_le_mul_of_nonneg_right (s_le_inv_x hx) (by norm_num)
        _ = 4 / (ε * t ^ 2) := by unfold x; ring)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_inv_square_primitive (ε := ε)
        (hpos t ((uIcc_of_le hab).subset ht)).ne') hmajI
    have hlast : -(4 / ε) / b - -(4 / ε) / a ≤ 2 := by
      have hupper : (4 / ε) / a ≤ 2 := by
        rw [div_le_iff₀ ha₀, div_le_iff₀ hε]
        nlinarith
      have hdrop : -(4 / ε) / b ≤ 0 := by
        have : 0 < b := ha₀.trans_le hab
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [show 0 < 4 / ε by positivity]) this.le
      have hupper' : -(-(4 / ε) / a) ≤ 2 := by
        simpa only [neg_div, neg_neg] using hupper
      linarith
    exact hcompare.trans (hFTC.trans_le hlast)

theorem x_bounds_of_turning_time {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (2 / ε) (3 / ε)) :
    2 / ε ≤ x ε a ∧ x ε a ≤ 9 / (2 * ε) := by
  have ha₁ : 2 ≤ ε * a := by rw [mul_comm]; exact (div_le_iff₀ hε).mp ha.1
  have ha₂ : ε * a ≤ 3 := by rw [mul_comm]; exact (le_div_iff₀ hε).mp ha.2
  have hx : x ε a * ε = (ε * a) ^ 2 / 2 := by unfold x; ring
  constructor
  · rw [div_le_iff₀ hε, hx]
    nlinarith [sq_nonneg (ε * a - 2)]
  · rw [le_div_iff₀ (by positivity), mul_left_comm, mul_comm (x ε a) ε]
    nlinarith [mul_nonneg (by linarith : 0 ≤ ε * a) (sub_nonneg.mpr ha₂)]

private theorem s_ratio_bounds {ε a b : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (ha : a ∈ Icc (2 / ε) (3 / ε)) (hab : a ≤ b) :
    (ε * x ε b)⁻¹ ≤ s ε b / s ε a ∧ s ε b / s ε a ≤ 9 / (ε * x ε b) := by
  obtain ⟨halow, hahigh⟩ := x_bounds_of_turning_time hε ha
  have ha₀ : 0 ≤ a := (by positivity : 0 ≤ 2 / ε).trans ha.1
  have ha₁ : 1 ≤ x ε a := ((le_div_iff₀ hε).mpr (by linarith)).trans halow
  have habx : x ε a ≤ x ε b := by
    unfold x
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha₀ hab 2) hε.le
    linarith
  have hb₁ := ha₁.trans habx
  have hapos : 0 < x ε a := zero_lt_one.trans_le ha₁
  have hbpos : 0 < x ε b := zero_lt_one.trans_le hb₁
  have hsainv_lo : x ε a ≤ (s ε a)⁻¹ := by
    simpa using inv_anti₀ (s_pos ε a) (s_le_inv_x hapos)
  have hsainv_hi : (s ε a)⁻¹ ≤ 2 * x ε a := by
    simpa using inv_anti₀ (by positivity : 0 < (2 * x ε a)⁻¹) (inv_two_mul_x_le_s ha₁)
  rw [div_eq_mul_inv]
  constructor
  · calc
      _ = ((2 * x ε b)⁻¹) * (2 / ε) := by ring
      _ ≤ _ := mul_le_mul (inv_two_mul_x_le_s hb₁) (halow.trans hsainv_lo)
        (by positivity) (s_pos ε b).le
  · have has : (s ε a)⁻¹ ≤ 9 / ε := by
      apply hsainv_hi.trans
      calc
        2 * x ε a ≤ 2 * (9 / (2 * ε)) := mul_le_mul_of_nonneg_left hahigh (by norm_num)
        _ = 9 / ε := by ring
    calc
      _ ≤ (x ε b)⁻¹ * (9 / ε) :=
        mul_le_mul (s_le_inv_x hbpos) has (inv_nonneg.mpr (s_pos ε a).le)
          (inv_nonneg.mpr hbpos.le)
      _ = 9 / (ε * x ε b) := by ring

/-- The canonical amplitude decays like the inverse square root of the scaled
clock after the turning time, uniformly over the rest of the forward ray. -/
theorem referenceV_late_ratio_bounds {ε τm τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : τm ∈ Icc (2 / ε) (3 / ε)) (hτ : τm ≤ τ)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8))) :
    (Real.sqrt (ε * x ε τ))⁻¹ ≤ referenceV Y τ / referenceV Y τm ∧
      referenceV Y τ / referenceV Y τm ≤ 3 * Real.exp 2 * (Real.sqrt (ε * x ε τ))⁻¹ := by
  have hm₀ : 0 ≤ τm := (by positivity : 0 ≤ 2 / ε).trans hm.1
  rw [referenceV_ratio_decomposition hform hY hm₀ hτ]
  obtain ⟨his₀, his₂⟩ := reference_tail_integral_bounds hε hε₁ hm.1 hτ hform hY he
  obtain ⟨hlo, hhi⟩ := s_ratio_bounds hε hε₁ hm hτ
  have hlo' := Real.sqrt_le_sqrt hlo
  rw [Real.sqrt_inv] at hlo'
  have hhi' := Real.sqrt_le_sqrt hhi
  have hsqrt9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9), hsqrt9] at hhi'
  constructor
  · calc
      _ ≤ Real.sqrt (s ε τ / s ε τm) := hlo'
      _ = Real.sqrt (s ε τ / s ε τm) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp his₀) (Real.sqrt_nonneg _)
  · calc
      _ ≤ (3 / Real.sqrt (ε * x ε τ)) * Real.exp 2 :=
        mul_le_mul hhi' (Real.exp_le_exp.mpr his₂) (Real.exp_pos _).le
          (by positivity)
      _ = _ := by ring

/-- The peak-normalized reference strength has the clock scaling used at a crossing. -/
theorem referenceV_late_strength_bounds {ε τm τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : τm ∈ Icc (2 / ε) (3 / ε)) (hτ : τm ≤ τ)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8))) :
    Real.sqrt (x ε τ / ε) ≤ x ε τ * (referenceV Y τ / referenceV Y τm) ∧
      x ε τ * (referenceV Y τ / referenceV Y τm) ≤ 3 * Real.exp 2 * Real.sqrt (x ε τ / ε) := by
  have hm₀ : 0 < τm := (by positivity : 0 < 2 / ε).trans_le hm.1
  have hτ₀ : 0 < τ := hm₀.trans_le hτ
  have hx : 0 < x ε τ := by unfold x; positivity
  obtain ⟨hlow, hhigh⟩ := referenceV_late_ratio_bounds hε hε₁ hm hτ hform hY he
  have heq : x ε τ * (Real.sqrt (ε * x ε τ))⁻¹ = Real.sqrt (x ε τ / ε) := by
    rw [Real.sqrt_mul hε.le, Real.sqrt_div hx.le]
    field_simp [(Real.sqrt_pos.2 hε).ne', (Real.sqrt_pos.2 hx).ne']
    exact (Real.sq_sqrt hx.le).symm
  constructor
  · rw [← heq]
    exact mul_le_mul_of_nonneg_left hlow hx.le
  · calc
      _ ≤ x ε τ * (3 * Real.exp 2 * (Real.sqrt (ε * x ε τ))⁻¹) :=
        mul_le_mul_of_nonneg_left hhigh hx.le
      _ = 3 * Real.exp 2 * (x ε τ * (Real.sqrt (ε * x ε τ))⁻¹) := by ring
      _ = _ := by rw [heq]

/-- A two-sided comparison to the reference amplitude controls the ratio to the
maximum of the physical amplitude. -/
theorem amplitude_ratio_of_reference_comparison {c C T τm τ M : ℝ} {Y A : ℝ → ℝ}
    (hc : 0 < c) (hC : 0 < C) (hm : τm ∈ Icc 0 T) (hτ : τ ∈ Icc 0 T)
    (hpeak : ∀ t ∈ Icc 0 T, referenceV Y t ≤ referenceV Y τm)
    (hcompare : ∀ t ∈ Icc 0 T,
      c * referenceV Y t ≤ A t ∧ A t ≤ C * referenceV Y t)
    (hmax : IsGreatest (A '' Icc 0 T) M) :
    c / C * (referenceV Y τ / referenceV Y τm) ≤ A τ / M ∧
      A τ / M ≤ C / c * (referenceV Y τ / referenceV Y τm) := by
  have hMlo := (hcompare τm hm).1.trans (hmax.2 (mem_image_of_mem A hm))
  obtain ⟨t, ht, hAt⟩ := hmax.1
  have hMhi : M ≤ C * referenceV Y τm :=
    hAt ▸ (hcompare t ht).2.trans (mul_le_mul_of_nonneg_left (hpeak t ht) hC.le)
  have hM₀ : 0 < M := (mul_pos hc (referenceV_pos Y τm)).trans_le hMlo
  have hA₀ : 0 < A τ := (mul_pos hc (referenceV_pos Y τ)).trans_le (hcompare τ hτ).1
  constructor
  · calc
      _ = (c * referenceV Y τ) / (C * referenceV Y τm) := by ring
      _ ≤ (c * referenceV Y τ) / M :=
        div_le_div_of_nonneg_left (mul_pos hc (referenceV_pos Y τ)).le hM₀ hMhi
      _ ≤ _ := div_le_div_of_nonneg_right (hcompare τ hτ).1 hM₀.le
  · calc
      _ ≤ A τ / (c * referenceV Y τm) :=
        div_le_div_of_nonneg_left hA₀.le (mul_pos hc (referenceV_pos Y τm)) hMlo
      _ ≤ (C * referenceV Y τ) / (c * referenceV Y τm) :=
        div_le_div_of_nonneg_right (hcompare τ hτ).2 (mul_pos hc (referenceV_pos Y τm)).le
      _ = _ := by ring

/-- The late physical strength estimate in Proposition 2.6 before inserting
the bounds on the clock at a crossing. Here the wave number has been divided
by its initial scale. -/
theorem amplitude_late_strength_bounds_of_reference_comparison
    {ε T τm τ M c C kmin kmax k : ℝ} {Y e A : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : τm ∈ Icc (2 / ε) (3 / ε))
    (hτm : τm ≤ τ) (hτT : τ ≤ T)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hc : 0 < c) (hC : 0 < C) (hkmin : 0 ≤ kmin) (hkmax : 0 ≤ kmax)
    (hpeak : ∀ t ∈ Icc 0 T, referenceV Y t ≤ referenceV Y τm)
    (hcompare : ∀ t ∈ Icc 0 T,
      c * referenceV Y t ≤ A t ∧ A t ≤ C * referenceV Y t)
    (hmax : IsGreatest (A '' Icc 0 T) M)
    (hklo : kmin * x ε τ ≤ k) (hkhi : k ≤ kmax * x ε τ) :
    kmin * (c / C) * Real.sqrt (x ε τ / ε) ≤ k * (A τ / M) ∧
      k * (A τ / M) ≤ kmax * (C / c) * (3 * Real.exp 2) * Real.sqrt (x ε τ / ε) := by
  have hm₀ : 0 ≤ τm := (by positivity : 0 ≤ 2 / ε).trans hm.1
  have hτ : τ ∈ Icc 0 T := ⟨hm₀.trans hτm, hτT⟩
  have hx := x_nonneg hε.le τ
  obtain ⟨hrlo, hrhi⟩ := amplitude_ratio_of_reference_comparison hc hC
    ⟨hm₀, hτm.trans hτT⟩ hτ hpeak hcompare hmax
  have hrpos : 0 ≤ A τ / M :=
    (by positivity [referenceV_pos Y τ, referenceV_pos Y τm] :
      0 ≤ c / C * (referenceV Y τ / referenceV Y τm)).trans hrlo
  obtain ⟨hslo, hshi⟩ := referenceV_late_strength_bounds hε hε₁ hm hτm hform hY he
  constructor
  · calc
      _ ≤ kmin * (c / C) * (x ε τ * (referenceV Y τ / referenceV Y τm)) :=
        mul_le_mul_of_nonneg_left hslo (by positivity)
      _ = (kmin * x ε τ) * (c / C * (referenceV Y τ / referenceV Y τm)) := by ring
      _ ≤ (kmin * x ε τ) * (A τ / M) :=
        mul_le_mul_of_nonneg_left hrlo (mul_nonneg hkmin hx)
      _ ≤ _ := mul_le_mul_of_nonneg_right hklo hrpos
  · calc
      _ ≤ (kmax * x ε τ) * (A τ / M) := mul_le_mul_of_nonneg_right hkhi hrpos
      _ ≤ (kmax * x ε τ) * (C / c * (referenceV Y τ / referenceV Y τm)) :=
        mul_le_mul_of_nonneg_left hrhi (mul_nonneg hkmax hx)
      _ = kmax * (C / c) * (x ε τ * (referenceV Y τ / referenceV Y τm)) := by ring
      _ ≤ kmax * (C / c) * (3 * Real.exp 2 * Real.sqrt (x ε τ / ε)) :=
        mul_le_mul_of_nonneg_left hshi (by positivity)
      _ = _ := by ring

end

end TorusEuler.ReferenceRiccati
