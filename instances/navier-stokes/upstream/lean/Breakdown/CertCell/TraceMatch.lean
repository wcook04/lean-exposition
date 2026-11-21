import Breakdown.CertCell.BridgeStatements

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private def rampProfile (x : ℝ) : ℝ := x * Real.smoothTransition x

private lemma rampProfile_contDiff : ContDiff ℝ ∞ rampProfile :=
  contDiff_id.mul Real.smoothTransition.contDiff

private lemma rampProfile_of_nonpos {x : ℝ} (hx : x ≤ 0) : rampProfile x = 0 := by
  simp [rampProfile, Real.smoothTransition.zero_of_nonpos hx]

private lemma rampProfile_of_one_le {x : ℝ} (hx : 1 ≤ x) : rampProfile x = x := by
  simp [rampProfile, Real.smoothTransition.one_of_one_le hx]

private lemma deriv_rampProfile_of_neg {x : ℝ} (hx : x < 0) : deriv rampProfile x = 0 := by
  have h : rampProfile =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => rampProfile_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq]
  simp

private lemma deriv_rampProfile_of_one_lt {x : ℝ} (hx : 1 < x) : deriv rampProfile x = 1 := by
  have h : rampProfile =ᶠ[𝓝 x] fun y => y :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => rampProfile_of_one_le (le_of_lt hy)
  rw [h.deriv_eq]
  simp

private lemma deriv_rampProfile_bound : ∃ M : ℝ, ∀ x, |deriv rampProfile x| ≤ M := by
  have hc : Continuous (deriv rampProfile) := rampProfile_contDiff.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-1 : ℝ) 2
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
  · rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [deriv_rampProfile_of_neg (by linarith)]
      simp
    · rw [deriv_rampProfile_of_one_lt (by linarith)]
      simp

private def rampAt (ε z : ℝ) : ℝ := ε * rampProfile (z / ε)

private lemma rampAt_contDiff (ε : ℝ) : ContDiff ℝ ∞ (rampAt ε) :=
  contDiff_const.mul (rampProfile_contDiff.comp (contDiff_id.div_const ε))

private lemma rampAt_hasDerivAt {ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    HasDerivAt (rampAt ε) (deriv rampProfile (z / ε)) z := by
  have h1 : HasDerivAt rampProfile (deriv rampProfile (z / ε)) (z / ε) :=
    ((rampProfile_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) z := (hasDerivAt_id z).div_const ε
  have h3 := (h1.comp z h2).const_mul ε
  have hne : ε ≠ 0 := hε.ne'
  have h4 : ε * (deriv rampProfile (z / ε) * (1 / ε)) = deriv rampProfile (z / ε) := by
    field_simp
  rw [h4] at h3
  exact h3

private lemma rampAt_of_nonpos {ε z : ℝ} (hε : 0 < ε) (hz : z ≤ 0) : rampAt ε z = 0 := by
  rw [rampAt, rampProfile_of_nonpos (div_nonpos_of_nonpos_of_nonneg hz hε.le), mul_zero]

private lemma rampAt_of_le {ε z : ℝ} (hε : 0 < ε) (hz : ε ≤ z) : rampAt ε z = z := by
  have hne : ε ≠ 0 := hε.ne'
  have he : ε * (z / ε) = z := by field_simp
  rw [rampAt, rampProfile_of_one_le ((one_le_div hε).2 hz), he]

private lemma abs_rampAt_le {ε : ℝ} (hε : 0 < ε) (z : ℝ) : |rampAt ε z| ≤ |z| := by
  have hne : ε ≠ 0 := hε.ne'
  have he : ε * (z / ε) = z := by field_simp
  have h : rampAt ε z = z * Real.smoothTransition (z / ε) := by
    rw [rampAt, rampProfile, ← mul_assoc, he]
  rw [h, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg (z / ε))]
  exact mul_le_of_le_one_right (abs_nonneg z) (Real.smoothTransition.le_one (z / ε))

private def stepFn (z : ℝ) : ℝ := if 0 < z then 1 else 0

private lemma stepFn_monotone : Monotone stepFn := by
  intro a b hab
  unfold stepFn
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 hab) h2
  · exact zero_le_one
  · exact le_rfl

private def hatApprox (h ε z : ℝ) : ℝ :=
  (rampAt ε (z + h) - 2 * rampAt ε z + rampAt ε (z - h)) / h

private def hatFn (h z : ℝ) : ℝ := (max (z + h) 0 - 2 * max z 0 + max (z - h) 0) / h

private def hatSlope (h z : ℝ) : ℝ := (stepFn (z + h) - 2 * stepFn z + stepFn (z - h)) / h

private def hatPairing (f fz : ℝ → ℂ) (h z : ℝ) : ℂ :=
  f z * Complex.ofReal (hatSlope h z) + fz z * Complex.ofReal (hatFn h z)

private lemma hatApprox_contDiff (h ε : ℝ) : ContDiff ℝ ∞ (hatApprox h ε) := by
  have hr := rampAt_contDiff ε
  have h1 : ContDiff ℝ ∞ (fun z => rampAt ε (z + h)) := hr.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun z => rampAt ε (z - h)) := hr.comp (contDiff_id.sub contDiff_const)
  have h3 : ContDiff ℝ ∞ (fun z => 2 * rampAt ε z) := contDiff_const.mul hr
  exact ((h1.sub h3).add h2).div_const h

private lemma hatApprox_hasDerivAt {h ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    HasDerivAt (hatApprox h ε)
      ((deriv rampProfile ((z + h) / ε) - 2 * deriv rampProfile (z / ε)
        + deriv rampProfile ((z - h) / ε)) / h) z := by
  have h1 : HasDerivAt (fun y => rampAt ε (y + h)) (deriv rampProfile ((z + h) / ε)) z := by
    have := (rampAt_hasDerivAt hε (z + h)).comp z ((hasDerivAt_id z).add_const h)
    rw [mul_one] at this
    exact this
  have h2 : HasDerivAt (fun y => rampAt ε (y - h)) (deriv rampProfile ((z - h) / ε)) z := by
    have := (rampAt_hasDerivAt hε (z - h)).comp z ((hasDerivAt_id z).sub_const h)
    rw [mul_one] at this
    exact this
  exact ((h1.sub ((rampAt_hasDerivAt hε z).const_mul 2)).add h2).div_const h

private lemma deriv_hatApprox {h ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    deriv (hatApprox h ε) z = (deriv rampProfile ((z + h) / ε) - 2 * deriv rampProfile (z / ε)
        + deriv rampProfile ((z - h) / ε)) / h :=
  (hatApprox_hasDerivAt hε z).deriv

private lemma hatApprox_eq_zero {h ε z : ℝ} (hh : 0 < h) (hε : 0 < ε) (hz : z ∉ Icc (-h) (h + ε)) :
    hatApprox h ε z = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hz
  rcases hz with hz | hz
  · rw [hatApprox, rampAt_of_nonpos (z := z + h) hε (by linarith),
      rampAt_of_nonpos (z := z) hε (by linarith), rampAt_of_nonpos (z := z - h) hε (by linarith)]
    simp
  · rw [hatApprox, rampAt_of_le (z := z + h) hε (by linarith),
      rampAt_of_le (z := z) hε (by linarith), rampAt_of_le (z := z - h) hε (by linarith)]
    ring

private lemma hatApprox_tsupport {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    tsupport (hatApprox h ε) ⊆ Icc (-h) (h + ε) := by
  refine closure_minimal (fun z hz => ?_) isClosed_Icc
  by_contra hc
  exact hz (hatApprox_eq_zero hh hε hc)

private lemma abs_deriv_hatApprox_le {h ε M : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hM : ∀ x, |deriv rampProfile x| ≤ M) (z : ℝ) : |deriv (hatApprox h ε) z| ≤ 4 * M / h := by
  rw [deriv_hatApprox hε, abs_div, abs_of_pos hh]
  apply div_le_div_of_nonneg_right _ hh.le
  have a1 := abs_le.1 (hM ((z + h) / ε))
  have a2 := abs_le.1 (hM (z / ε))
  have a3 := abs_le.1 (hM ((z - h) / ε))
  exact abs_le.2 ⟨by linarith [a1.1, a2.2, a3.1], by linarith [a1.2, a2.1, a3.2]⟩

private lemma abs_hatApprox_le {h ε z : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hz : z ∈ Ioo (-(2 * h)) (2 * h)) : |hatApprox h ε z| ≤ 10 := by
  obtain ⟨hz1, hz2⟩ := hz
  have b1 : |z + h| ≤ 3 * h := abs_le.2 ⟨by linarith, by linarith⟩
  have b2 : |z| ≤ 2 * h := abs_le.2 ⟨by linarith, by linarith⟩
  have b3 : |z - h| ≤ 3 * h := abs_le.2 ⟨by linarith, by linarith⟩
  have a1 := abs_le.1 (le_trans (abs_rampAt_le hε (z + h)) b1)
  have a2 := abs_le.1 (le_trans (abs_rampAt_le hε z) b2)
  have a3 := abs_le.1 (le_trans (abs_rampAt_le hε (z - h)) b3)
  rw [hatApprox, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  exact abs_le.2 ⟨by linarith [a1.1, a2.2, a3.1], by linarith [a1.2, a2.1, a3.2]⟩

private lemma seq_pos {h : ℝ} (hh : 0 < h) (n : ℕ) : 0 < h / ((n : ℝ) + 2) := by positivity

private lemma seq_lt {h : ℝ} (hh : 0 < h) (n : ℕ) : h / ((n : ℝ) + 2) < h := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

private lemma seq_eventually_lt {h w : ℝ} (hw : 0 < w) :
    ∀ᶠ n : ℕ in atTop, h / ((n : ℝ) + 2) < w := by
  have t : Tendsto (fun n : ℕ => h / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat h).comp (tendsto_add_atTop_nat 2)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  exact (tendsto_order.1 t).2 w hw

private lemma rampAt_eventually {h : ℝ} (hh : 0 < h) (w : ℝ) :
    ∀ᶠ n : ℕ in atTop, rampAt (h / ((n : ℝ) + 2)) w = max w 0 := by
  rcases le_or_gt w 0 with hw | hw
  · exact Eventually.of_forall fun n => by
      rw [rampAt_of_nonpos (seq_pos hh n) hw, max_eq_right hw]
  · filter_upwards [seq_eventually_lt (h := h) hw] with n hn
    rw [rampAt_of_le (seq_pos hh n) hn.le, max_eq_left hw.le]

private lemma rampSlope_eventually {h w : ℝ} (hh : 0 < h) (hw : w ≠ 0) :
    ∀ᶠ n : ℕ in atTop, deriv rampProfile (w / (h / ((n : ℝ) + 2))) = stepFn w := by
  rcases lt_or_gt_of_ne hw with hw | hw
  · exact Eventually.of_forall fun n => by
      rw [deriv_rampProfile_of_neg (div_neg_of_neg_of_pos hw (seq_pos hh n)), stepFn,
        if_neg (not_lt.2 hw.le)]
  · filter_upwards [seq_eventually_lt (h := h) hw] with n hn
    rw [deriv_rampProfile_of_one_lt ((one_lt_div (seq_pos hh n)).2 hn), stepFn, if_pos hw]

private lemma hatApprox_eventually {h : ℝ} (hh : 0 < h) (z : ℝ) :
    ∀ᶠ n : ℕ in atTop, hatApprox h (h / ((n : ℝ) + 2)) z = hatFn h z := by
  filter_upwards [rampAt_eventually hh (z + h), rampAt_eventually hh z,
    rampAt_eventually hh (z - h)] with n h1 h2 h3
  rw [hatApprox, hatFn, h1, h2, h3]

private lemma deriv_hatApprox_eventually {h z : ℝ} (hh : 0 < h) (h1 : z + h ≠ 0) (h2 : z ≠ 0)
    (h3 : z - h ≠ 0) :
    ∀ᶠ n : ℕ in atTop, deriv (hatApprox h (h / ((n : ℝ) + 2))) z = hatSlope h z := by
  filter_upwards [rampSlope_eventually hh h1, rampSlope_eventually hh h2,
    rampSlope_eventually hh h3] with n e1 e2 e3
  rw [deriv_hatApprox (seq_pos hh n), hatSlope, e1, e2, e3]

private lemma hatPairing_outer_left {f fz : ℝ → ℂ} {h z : ℝ} (hh : 0 < h) (hz : z ≤ -h) :
    hatPairing f fz h z = 0 := by
  have s1 : stepFn (z + h) = 0 := if_neg (not_lt.2 (by linarith))
  have s2 : stepFn z = 0 := if_neg (not_lt.2 (by linarith))
  have s3 : stepFn (z - h) = 0 := if_neg (not_lt.2 (by linarith))
  have hS : hatSlope h z = 0 := by rw [hatSlope, s1, s2, s3]; ring
  have hF : hatFn h z = 0 := by
    rw [hatFn, max_eq_right (by linarith : z + h ≤ 0), max_eq_right (by linarith : z ≤ 0),
      max_eq_right (by linarith : z - h ≤ 0)]
    ring
  rw [hatPairing, hS, hF]
  simp

private lemma hatPairing_outer_right {f fz : ℝ → ℂ} {h z : ℝ} (hh : 0 < h) (hz : h < z) :
    hatPairing f fz h z = 0 := by
  have s1 : stepFn (z + h) = 1 := if_pos (by linarith)
  have s2 : stepFn z = 1 := if_pos (by linarith)
  have s3 : stepFn (z - h) = 1 := if_pos (by linarith)
  have hS : hatSlope h z = 0 := by rw [hatSlope, s1, s2, s3]; ring
  have hF : hatFn h z = 0 := by
    rw [hatFn, max_eq_left (by linarith : (0 : ℝ) ≤ z + h), max_eq_left (by linarith : (0 : ℝ) ≤ z),
      max_eq_left (by linarith : (0 : ℝ) ≤ z - h)]
    ring
  rw [hatPairing, hS, hF]
  simp

private lemma hatPairing_lower {f fz : ℝ → ℂ} {h z : ℝ} (hh : 0 < h) (hz1 : -h < z) (hz2 : z ≤ 0) :
    hatPairing f fz h z = fz z * ((1 + z / h : ℝ) : ℂ) + f z / (h : ℂ) := by
  have hne : h ≠ 0 := hh.ne'
  have s1 : stepFn (z + h) = 1 := if_pos (by linarith)
  have s2 : stepFn z = 0 := if_neg (not_lt.2 hz2)
  have s3 : stepFn (z - h) = 0 := if_neg (not_lt.2 (by linarith))
  have hS : hatSlope h z = 1 / h := by rw [hatSlope, s1, s2, s3]; ring
  have hF : hatFn h z = 1 + z / h := by
    rw [hatFn, max_eq_left (by linarith : (0 : ℝ) ≤ z + h), max_eq_right hz2,
      max_eq_right (by linarith : z - h ≤ 0), show z + h - 2 * 0 + 0 = z + h by ring, add_div,
      div_self hne]
    ring
  rw [hatPairing, hS, hF]
  push_cast
  ring

private lemma hatPairing_upper {f fz : ℝ → ℂ} {h z : ℝ} (hh : 0 < h) (hz1 : 0 < z) (hz2 : z ≤ h) :
    hatPairing f fz h z = fz z * ((1 - z / h : ℝ) : ℂ) - f z / (h : ℂ) := by
  have hne : h ≠ 0 := hh.ne'
  have s1 : stepFn (z + h) = 1 := if_pos (by linarith)
  have s2 : stepFn z = 1 := if_pos hz1
  have s3 : stepFn (z - h) = 0 := if_neg (not_lt.2 (by linarith))
  have hS : hatSlope h z = -1 / h := by rw [hatSlope, s1, s2, s3]; ring
  have hF : hatFn h z = 1 - z / h := by
    rw [hatFn, max_eq_left (by linarith : (0 : ℝ) ≤ z + h), max_eq_left hz1.le,
      max_eq_right (by linarith : z - h ≤ 0), show z + h - 2 * z + 0 = h - z by ring, sub_div,
      div_self hne]
  rw [hatPairing, hS, hF]
  push_cast
  ring

private lemma abs_stepFn_le (w : ℝ) : |stepFn w| ≤ 1 := by
  unfold stepFn
  split_ifs <;> simp

private lemma abs_hatSlope_le {h : ℝ} (hh : 0 < h) (z : ℝ) : |hatSlope h z| ≤ 4 / h := by
  rw [hatSlope, abs_div, abs_of_pos hh]
  apply div_le_div_of_nonneg_right _ hh.le
  have a1 := abs_le.1 (abs_stepFn_le (z + h))
  have a2 := abs_le.1 (abs_stepFn_le z)
  have a3 := abs_le.1 (abs_stepFn_le (z - h))
  exact abs_le.2 ⟨by linarith [a1.1, a2.2, a3.1], by linarith [a1.2, a2.1, a3.2]⟩

private lemma abs_hatFn_le {h z : ℝ} (hh : 0 < h) (hz : z ∈ Ioo (-(2 * h)) (2 * h)) :
    |hatFn h z| ≤ 10 := by
  obtain ⟨n, hn⟩ := (hatApprox_eventually hh z).exists
  rw [← hn]
  exact abs_hatApprox_le hh (seq_pos hh n) hz

private lemma hatSlope_measurable (h : ℝ) : Measurable (hatSlope h) := by
  have hm := stepFn_monotone.measurable
  have h1 : Measurable fun z => stepFn (z + h) := hm.comp (measurable_id.add_const h)
  have h2 : Measurable fun z => stepFn (z - h) := hm.comp (measurable_id.sub_const h)
  have h3 : Measurable fun z => 2 * stepFn z := measurable_const.mul hm
  exact ((h1.sub h3).add h2).div_const h

private lemma hatFn_continuous (h : ℝ) : Continuous (hatFn h) := by
  unfold hatFn
  fun_prop

theorem traceMatch : TraceMatchHolds := by
  intro f fz h hh hw
  obtain ⟨hf, hfz, hweak⟩ := hw
  obtain ⟨M, hM⟩ := deriv_rampProfile_bound
  have hf' : Integrable f (volume.restrict (Ioo (-(2 * h)) (2 * h))) := hf
  have hfz' : Integrable fz (volume.restrict (Ioo (-(2 * h)) (2 * h))) := hfz
  have hid : ∀ n : ℕ, ∫ z in Ioo (-(2 * h)) (2 * h),
      f z * Complex.ofReal (deriv (hatApprox h (h / ((n : ℝ) + 2))) z)
      = -∫ z in Ioo (-(2 * h)) (2 * h),
        fz z * Complex.ofReal (hatApprox h (h / ((n : ℝ) + 2)) z) := by
    intro n
    have hε := seq_pos hh n
    have hlt := seq_lt hh n
    refine hweak _ (hatApprox_contDiff _ _)
      (HasCompactSupport.intro isCompact_Icc fun z hz => hatApprox_eq_zero hh hε hz) ?_
    exact (hatApprox_tsupport hh hε).trans (Icc_subset_Ioo (by linarith) (by linarith))
  have hnull : ∀ᵐ z ∂(volume.restrict (Ioo (-(2 * h)) (2 * h))),
      z + h ≠ 0 ∧ z ≠ 0 ∧ z - h ≠ 0 := by
    apply ae_restrict_of_ae
    have hfin : (volume : Measure ℝ) {-h, 0, h} = 0 := (Set.toFinite _).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfin] with z hz
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨fun e => hz.1 (by linarith), hz.2.1, fun e => hz.2.2 (by linarith)⟩
  have hL : Tendsto (fun n : ℕ => ∫ z in Ioo (-(2 * h)) (2 * h),
      f z * Complex.ofReal (deriv (hatApprox h (h / ((n : ℝ) + 2))) z))
      atTop (𝓝 (∫ z in Ioo (-(2 * h)) (2 * h), f z * Complex.ofReal (hatSlope h z))) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖f z‖ * (4 * M / h))
      (fun n => ?_) (hf'.norm.mul_const _) (fun n => ?_) ?_
    · exact hf'.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        ((hatApprox_contDiff _ _).continuous_deriv (by simp))).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_deriv_hatApprox_le hh (seq_pos hh n) hM z)
        (norm_nonneg _)
    · filter_upwards [hnull] with z hz
      exact tendsto_const_nhds.congr'
        ((deriv_hatApprox_eventually hh hz.1 hz.2.1 hz.2.2).mono fun n hn => by simp only [hn])
  have hR : Tendsto (fun n : ℕ => ∫ z in Ioo (-(2 * h)) (2 * h),
      fz z * Complex.ofReal (hatApprox h (h / ((n : ℝ) + 2)) z))
      atTop (𝓝 (∫ z in Ioo (-(2 * h)) (2 * h), fz z * Complex.ofReal (hatFn h z))) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖fz z‖ * 10)
      (fun n => ?_) (hfz'.norm.mul_const _) (fun n => ?_) ?_
    · exact hfz'.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (hatApprox_contDiff _ _).continuous).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_hatApprox_le hh (seq_pos hh n) hz) (norm_nonneg _)
    · exact Eventually.of_forall fun z => tendsto_const_nhds.congr'
        ((hatApprox_eventually hh z).mono fun n hn => by simp only [hn])
  have hlim : ∫ z in Ioo (-(2 * h)) (2 * h), f z * Complex.ofReal (hatSlope h z)
      = -∫ z in Ioo (-(2 * h)) (2 * h), fz z * Complex.ofReal (hatFn h z) :=
    tendsto_nhds_unique hL (hR.neg.congr fun n => (hid n).symm)
  have hI1 : Integrable (fun z => f z * Complex.ofReal (hatSlope h z))
      (volume.restrict (Ioo (-(2 * h)) (2 * h))) := by
    refine Integrable.mono' (hf'.norm.mul_const (4 / h)) (hf'.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp (hatSlope_measurable h)).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_hatSlope_le hh z) (norm_nonneg _)
  have hI2 : Integrable (fun z => fz z * Complex.ofReal (hatFn h z))
      (volume.restrict (Ioo (-(2 * h)) (2 * h))) := by
    refine Integrable.mono' (hfz'.norm.mul_const 10) (hfz'.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (hatFn_continuous h)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_hatFn_le hh hz) (norm_nonneg _)
  have hsum : ∫ z in Ioo (-(2 * h)) (2 * h), hatPairing f fz h z = 0 := by
    simp only [hatPairing]
    rw [integral_add hI1 hI2, hlim]
    ring
  have hGi : IntervalIntegrable (hatPairing f fz h) volume (-(2 * h)) (2 * h) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2 (hI1.add hI2)
  have hG0 : ∫ z in (-(2 * h))..(2 * h), hatPairing f fz h z = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact hsum
  have sub : ∀ a b : ℝ, -(2 * h) ≤ a → a ≤ b → b ≤ 2 * h →
      IntervalIntegrable (hatPairing f fz h) volume a b := fun a b ha hab hb =>
    hGi.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (show -(2 * h) ≤ 2 * h by linarith)]
      exact Icc_subset_Icc ha hb)
  have i1 := sub (-(2 * h)) (-h) le_rfl (by linarith) (by linarith)
  have i2 := sub (-h) 0 (by linarith) (by linarith) (by linarith)
  have i3 := sub 0 h (by linarith) hh.le (by linarith)
  have i4 := sub h (2 * h) (by linarith) (by linarith) le_rfl
  have e1 : ∫ z in (-(2 * h))..(-h), hatPairing f fz h z = 0 := by
    have : ∫ z in (-(2 * h))..(-h), hatPairing f fz h z = ∫ _ in (-(2 * h))..(-h), (0 : ℂ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun z hz => by
        rw [uIoc_of_le (show -(2 * h) ≤ -h by linarith)] at hz
        exact hatPairing_outer_left hh hz.2)
    rw [this, intervalIntegral.integral_zero]
  have e4 : ∫ z in h..(2 * h), hatPairing f fz h z = 0 := by
    have : ∫ z in h..(2 * h), hatPairing f fz h z = ∫ _ in h..(2 * h), (0 : ℂ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun z hz => by
        rw [uIoc_of_le (show h ≤ 2 * h by linarith)] at hz
        exact hatPairing_outer_right hh hz.1)
    rw [this, intervalIntegral.integral_zero]
  have e2 : ∫ z in (-h)..0, hatPairing f fz h z = lowerTrace f fz h := by
    rw [lowerTrace]
    exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun z hz => by
      rw [uIoc_of_le (show -h ≤ 0 by linarith)] at hz
      exact hatPairing_lower hh hz.1 hz.2)
  have e3 : ∫ z in (0 : ℝ)..h, hatPairing f fz h z = -upperTrace f fz h := by
    rw [upperTrace, neg_neg]
    exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun z hz => by
      rw [uIoc_of_le hh.le] at hz
      exact hatPairing_upper hh hz.1 hz.2)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans (i3.trans i4)),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (i3.trans i4),
    ← intervalIntegral.integral_add_adjacent_intervals i3 i4, e1, e2, e3, e4] at hG0
  linear_combination -hG0

end Bridge

end CertCell

end Breakdown
