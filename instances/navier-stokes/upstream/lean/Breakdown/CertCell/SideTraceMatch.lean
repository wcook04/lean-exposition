import Breakdown.CertCell.BridgeTraceStatements

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula CellCert.CellAnalysis Bridge

namespace Internal

def kinkProfile (x : ℝ) : ℝ := x * Real.smoothTransition x

lemma kinkProfile_contDiff : ContDiff ℝ ∞ kinkProfile :=
  contDiff_id.mul Real.smoothTransition.contDiff

lemma kinkProfile_of_nonpos {x : ℝ} (hx : x ≤ 0) : kinkProfile x = 0 := by
  simp [kinkProfile, Real.smoothTransition.zero_of_nonpos hx]

lemma kinkProfile_of_one_le {x : ℝ} (hx : 1 ≤ x) : kinkProfile x = x := by
  simp [kinkProfile, Real.smoothTransition.one_of_one_le hx]

lemma deriv_kinkProfile_of_neg {x : ℝ} (hx : x < 0) : deriv kinkProfile x = 0 := by
  have h : kinkProfile =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => kinkProfile_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq]
  simp

lemma deriv_kinkProfile_of_one_lt {x : ℝ} (hx : 1 < x) : deriv kinkProfile x = 1 := by
  have h : kinkProfile =ᶠ[𝓝 x] fun y => y :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => kinkProfile_of_one_le (le_of_lt hy)
  rw [h.deriv_eq]
  simp

lemma deriv_kinkProfile_bound : ∃ M : ℝ, ∀ x, |deriv kinkProfile x| ≤ M := by
  have hc : Continuous (deriv kinkProfile) := kinkProfile_contDiff.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-1 : ℝ) 2
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
  · rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [deriv_kinkProfile_of_neg (by linarith)]
      simp
    · rw [deriv_kinkProfile_of_one_lt (by linarith)]
      simp

def kinkAt (ε y : ℝ) : ℝ := ε * kinkProfile (y / ε)

lemma kinkAt_contDiff (ε : ℝ) : ContDiff ℝ ∞ (kinkAt ε) :=
  contDiff_const.mul (kinkProfile_contDiff.comp (contDiff_id.div_const ε))

lemma kinkAt_hasDerivAt {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (kinkAt ε) (deriv kinkProfile (y / ε)) y := by
  have h1 : HasDerivAt kinkProfile (deriv kinkProfile (y / ε)) (y / ε) :=
    ((kinkProfile_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt
  have h2 : HasDerivAt (fun w : ℝ => w / ε) (1 / ε) y := (hasDerivAt_id y).div_const ε
  have h3 := (h1.comp y h2).const_mul ε
  have hne : ε ≠ 0 := hε.ne'
  have h4 : ε * (deriv kinkProfile (y / ε) * (1 / ε)) = deriv kinkProfile (y / ε) := by
    field_simp
  rw [h4] at h3
  exact h3

lemma kinkAt_of_nonpos {ε y : ℝ} (hε : 0 < ε) (hy : y ≤ 0) : kinkAt ε y = 0 := by
  rw [kinkAt, kinkProfile_of_nonpos (div_nonpos_of_nonpos_of_nonneg hy hε.le), mul_zero]

lemma kinkAt_of_le {ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) : kinkAt ε y = y := by
  have hne : ε ≠ 0 := hε.ne'
  have he : ε * (y / ε) = y := by field_simp
  rw [kinkAt, kinkProfile_of_one_le ((one_le_div hε).2 hy), he]

lemma abs_kinkAt_le {ε : ℝ} (hε : 0 < ε) (y : ℝ) : |kinkAt ε y| ≤ |y| := by
  have hne : ε ≠ 0 := hε.ne'
  have he : ε * (y / ε) = y := by field_simp
  have h : kinkAt ε y = y * Real.smoothTransition (y / ε) := by
    rw [kinkAt, kinkProfile, ← mul_assoc, he]
  rw [h, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg (y / ε))]
  exact mul_le_of_le_one_right (abs_nonneg y) (Real.smoothTransition.le_one (y / ε))

def unitStep (y : ℝ) : ℝ := if 0 < y then 1 else 0

lemma unitStep_monotone : Monotone unitStep := by
  intro u v huv
  unfold unitStep
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 huv) h2
  · exact zero_le_one
  · exact le_rfl

lemma abs_unitStep_le (y : ℝ) : |unitStep y| ≤ 1 := by
  unfold unitStep
  split_ifs <;> simp

lemma abs_max_zero_le (y : ℝ) : |max y 0| ≤ |y| := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h]
    simp
  · rw [max_eq_left h]

def comb (p m q u v w : ℝ) : ℝ :=
  1 / (m - p) * u - (1 / (m - p) + 1 / (q - m)) * v + 1 / (q - m) * w

lemma abs_comb_le {p m q u v w K : ℝ} (hpm : p < m) (hmq : m < q) (hu : |u| ≤ K) (hv : |v| ≤ K)
    (hw : |w| ≤ K) : |comb p m q u v w| ≤ 2 * (1 / (m - p) + 1 / (q - m)) * K := by
  have hα : 0 ≤ 1 / (m - p) := le_of_lt (one_div_pos.2 (sub_pos.2 hpm))
  have hβ : 0 ≤ 1 / (q - m) := le_of_lt (one_div_pos.2 (sub_pos.2 hmq))
  have hαβ : 0 ≤ 1 / (m - p) + 1 / (q - m) := add_nonneg hα hβ
  have h1 : |1 / (m - p) * u| ≤ 1 / (m - p) * K := by
    rw [abs_mul, abs_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left hu hα
  have h2 : |(1 / (m - p) + 1 / (q - m)) * v| ≤ (1 / (m - p) + 1 / (q - m)) * K := by
    rw [abs_mul, abs_of_nonneg hαβ]
    exact mul_le_mul_of_nonneg_left hv hαβ
  have h3 : |1 / (q - m) * w| ≤ 1 / (q - m) * K := by
    rw [abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left hw hβ
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 h3
  rw [comb]
  exact abs_le.2 ⟨by linarith [a1.1, a2.2, a3.1], by linarith [a1.2, a2.1, a3.2]⟩

def tentApprox (p m q ε x : ℝ) : ℝ :=
  comb p m q (kinkAt ε (x - p)) (kinkAt ε (x - m)) (kinkAt ε (x - q))

def tentFn (p m q x : ℝ) : ℝ := comb p m q (max (x - p) 0) (max (x - m) 0) (max (x - q) 0)

def tentSlope (p m q x : ℝ) : ℝ := comb p m q (unitStep (x - p)) (unitStep (x - m)) (unitStep (x - q))

def pairing (f fd : ℝ → ℂ) (p m q x : ℝ) : ℂ :=
  f x * Complex.ofReal (tentSlope p m q x) + fd x * Complex.ofReal (tentFn p m q x)

lemma tentApprox_contDiff (p m q ε : ℝ) : ContDiff ℝ ∞ (tentApprox p m q ε) := by
  have hs : ∀ s : ℝ, ContDiff ℝ ∞ (fun x => kinkAt ε (x - s)) := fun s =>
    (kinkAt_contDiff ε).comp (contDiff_id.sub contDiff_const)
  show ContDiff ℝ ∞ (fun x => 1 / (m - p) * kinkAt ε (x - p)
    - (1 / (m - p) + 1 / (q - m)) * kinkAt ε (x - m) + 1 / (q - m) * kinkAt ε (x - q))
  exact ((contDiff_const.mul (hs p)).sub (contDiff_const.mul (hs m))).add (contDiff_const.mul (hs q))

lemma tentApprox_hasDerivAt {p m q ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (tentApprox p m q ε)
      (comb p m q (deriv kinkProfile ((x - p) / ε)) (deriv kinkProfile ((x - m) / ε))
        (deriv kinkProfile ((x - q) / ε))) x := by
  have hs : ∀ s : ℝ, HasDerivAt (fun y => kinkAt ε (y - s)) (deriv kinkProfile ((x - s) / ε)) x := by
    intro s
    have h := (kinkAt_hasDerivAt hε (x - s)).comp x ((hasDerivAt_id x).sub_const s)
    rw [mul_one] at h
    exact h
  show HasDerivAt (fun x => 1 / (m - p) * kinkAt ε (x - p)
    - (1 / (m - p) + 1 / (q - m)) * kinkAt ε (x - m) + 1 / (q - m) * kinkAt ε (x - q)) _ x
  exact (((hs p).const_mul (1 / (m - p))).sub ((hs m).const_mul (1 / (m - p) + 1 / (q - m)))).add
    ((hs q).const_mul (1 / (q - m)))

lemma tentApprox_eq_zero {p m q ε x : ℝ} (hpm : p < m) (hmq : m < q) (hε : 0 < ε)
    (hx : x ∉ Icc p (q + ε)) : tentApprox p m q ε x = 0 := by
  have h1 : m - p ≠ 0 := (sub_pos.2 hpm).ne'
  have h2 : q - m ≠ 0 := (sub_pos.2 hmq).ne'
  have hα : 1 / (m - p) * (m - p) = 1 := by field_simp
  have hβ : 1 / (q - m) * (q - m) = 1 := by field_simp
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · rw [tentApprox, comb, kinkAt_of_nonpos hε (by linarith : x - p ≤ 0),
      kinkAt_of_nonpos hε (by linarith : x - m ≤ 0), kinkAt_of_nonpos hε (by linarith : x - q ≤ 0)]
    ring
  · rw [tentApprox, comb, kinkAt_of_le hε (by linarith : ε ≤ x - p),
      kinkAt_of_le hε (by linarith : ε ≤ x - m), kinkAt_of_le hε (by linarith : ε ≤ x - q)]
    linear_combination hα - hβ

lemma tentApprox_tsupport {p m q ε : ℝ} (hpm : p < m) (hmq : m < q) (hε : 0 < ε) :
    tsupport (tentApprox p m q ε) ⊆ Icc p (q + ε) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  exact hx (tentApprox_eq_zero hpm hmq hε hc)

lemma abs_deriv_tentApprox_le {p m q ε M : ℝ} (hpm : p < m) (hmq : m < q) (hε : 0 < ε)
    (hM : ∀ x, |deriv kinkProfile x| ≤ M) (x : ℝ) :
    |deriv (tentApprox p m q ε) x| ≤ 2 * (1 / (m - p) + 1 / (q - m)) * M := by
  rw [(tentApprox_hasDerivAt (p := p) (m := m) (q := q) hε x).deriv]
  exact abs_comb_le hpm hmq (hM _) (hM _) (hM _)

lemma abs_sub_le_width {a b x s : ℝ} (hx : x ∈ Ioo a b) (hs : a < s) (hs' : s < b) :
    |x - s| ≤ b - a := by
  obtain ⟨h1, h2⟩ := hx
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma abs_tentApprox_le {a b p m q ε x : ℝ} (hap : a < p) (hpm : p < m) (hmq : m < q) (hqb : q < b)
    (hε : 0 < ε) (hx : x ∈ Ioo a b) :
    |tentApprox p m q ε x| ≤ 2 * (1 / (m - p) + 1 / (q - m)) * (b - a) :=
  abs_comb_le hpm hmq (le_trans (abs_kinkAt_le hε _) (abs_sub_le_width hx hap (by linarith)))
    (le_trans (abs_kinkAt_le hε _) (abs_sub_le_width hx (by linarith) (by linarith)))
    (le_trans (abs_kinkAt_le hε _) (abs_sub_le_width hx (by linarith) hqb))

lemma abs_tentFn_le {a b p m q x : ℝ} (hap : a < p) (hpm : p < m) (hmq : m < q) (hqb : q < b)
    (hx : x ∈ Ioo a b) :
    |tentFn p m q x| ≤ 2 * (1 / (m - p) + 1 / (q - m)) * (b - a) :=
  abs_comb_le hpm hmq (le_trans (abs_max_zero_le _) (abs_sub_le_width hx hap (by linarith)))
    (le_trans (abs_max_zero_le _) (abs_sub_le_width hx (by linarith) (by linarith)))
    (le_trans (abs_max_zero_le _) (abs_sub_le_width hx (by linarith) hqb))

lemma abs_tentSlope_le {p m q : ℝ} (hpm : p < m) (hmq : m < q) (x : ℝ) :
    |tentSlope p m q x| ≤ 2 * (1 / (m - p) + 1 / (q - m)) * 1 :=
  abs_comb_le hpm hmq (abs_unitStep_le _) (abs_unitStep_le _) (abs_unitStep_le _)

lemma tentSlope_measurable (p m q : ℝ) : Measurable (tentSlope p m q) := by
  have hm := unitStep_monotone.measurable
  have hs : ∀ s : ℝ, Measurable fun x => unitStep (x - s) := fun s =>
    hm.comp (measurable_id.sub_const s)
  show Measurable (fun x => 1 / (m - p) * unitStep (x - p)
    - (1 / (m - p) + 1 / (q - m)) * unitStep (x - m) + 1 / (q - m) * unitStep (x - q))
  exact ((measurable_const.mul (hs p)).sub (measurable_const.mul (hs m))).add
    (measurable_const.mul (hs q))

lemma tentFn_continuous (p m q : ℝ) : Continuous (tentFn p m q) := by
  unfold tentFn comb
  fun_prop

lemma seq_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < δ / ((n : ℝ) + 2) := by positivity

lemma seq_lt {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : δ / ((n : ℝ) + 2) < δ := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

lemma seq_eventually_lt (δ : ℝ) {w : ℝ} (hw : 0 < w) :
    ∀ᶠ n : ℕ in atTop, δ / ((n : ℝ) + 2) < w := by
  have t : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat δ).comp (tendsto_add_atTop_nat 2)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  exact (tendsto_order.1 t).2 w hw

lemma kinkAt_eventually {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    ∀ᶠ n : ℕ in atTop, kinkAt (δ / ((n : ℝ) + 2)) w = max w 0 := by
  rcases le_or_gt w 0 with hw | hw
  · exact Eventually.of_forall fun n => by
      rw [kinkAt_of_nonpos (seq_pos hδ n) hw, max_eq_right hw]
  · filter_upwards [seq_eventually_lt δ hw] with n hn
    rw [kinkAt_of_le (seq_pos hδ n) hn.le, max_eq_left hw.le]

lemma kinkSlope_eventually {δ w : ℝ} (hδ : 0 < δ) (hw : w ≠ 0) :
    ∀ᶠ n : ℕ in atTop, deriv kinkProfile (w / (δ / ((n : ℝ) + 2))) = unitStep w := by
  rcases lt_or_gt_of_ne hw with hw | hw
  · exact Eventually.of_forall fun n => by
      rw [deriv_kinkProfile_of_neg (div_neg_of_neg_of_pos hw (seq_pos hδ n)), unitStep,
        if_neg (not_lt.2 hw.le)]
  · filter_upwards [seq_eventually_lt δ hw] with n hn
    rw [deriv_kinkProfile_of_one_lt ((one_lt_div (seq_pos hδ n)).2 hn), unitStep, if_pos hw]

lemma tentApprox_eventually {p m q δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, tentApprox p m q (δ / ((n : ℝ) + 2)) x = tentFn p m q x := by
  filter_upwards [kinkAt_eventually hδ (x - p), kinkAt_eventually hδ (x - m),
    kinkAt_eventually hδ (x - q)] with n h1 h2 h3
  rw [tentApprox, tentFn, h1, h2, h3]

lemma deriv_tentApprox_eventually {p m q δ x : ℝ} (hδ : 0 < δ) (h1 : x - p ≠ 0) (h2 : x - m ≠ 0)
    (h3 : x - q ≠ 0) :
    ∀ᶠ n : ℕ in atTop, deriv (tentApprox p m q (δ / ((n : ℝ) + 2))) x = tentSlope p m q x := by
  filter_upwards [kinkSlope_eventually hδ h1, kinkSlope_eventually hδ h2,
    kinkSlope_eventually hδ h3] with n e1 e2 e3
  rw [(tentApprox_hasDerivAt (p := p) (m := m) (q := q) (seq_pos hδ n) x).deriv, tentSlope, e1, e2, e3]

lemma pairing_outer_left {f fd : ℝ → ℂ} {p m q x : ℝ} (hpm : p < m) (hmq : m < q) (hx : x ≤ p) :
    pairing f fd p m q x = 0 := by
  have s1 : unitStep (x - p) = 0 := if_neg (not_lt.2 (by linarith))
  have s2 : unitStep (x - m) = 0 := if_neg (not_lt.2 (by linarith))
  have s3 : unitStep (x - q) = 0 := if_neg (not_lt.2 (by linarith))
  have hS : tentSlope p m q x = 0 := by
    rw [tentSlope, comb, s1, s2, s3]
    ring
  have hF : tentFn p m q x = 0 := by
    rw [tentFn, comb, max_eq_right (by linarith : x - p ≤ 0), max_eq_right (by linarith : x - m ≤ 0),
      max_eq_right (by linarith : x - q ≤ 0)]
    ring
  rw [pairing, hS, hF]
  simp

lemma pairing_outer_right {f fd : ℝ → ℂ} {p m q x : ℝ} (hpm : p < m) (hmq : m < q) (hx : q < x) :
    pairing f fd p m q x = 0 := by
  have h1 : m - p ≠ 0 := (sub_pos.2 hpm).ne'
  have h2 : q - m ≠ 0 := (sub_pos.2 hmq).ne'
  have hα : 1 / (m - p) * (m - p) = 1 := by field_simp
  have hβ : 1 / (q - m) * (q - m) = 1 := by field_simp
  have s1 : unitStep (x - p) = 1 := if_pos (by linarith)
  have s2 : unitStep (x - m) = 1 := if_pos (by linarith)
  have s3 : unitStep (x - q) = 1 := if_pos (by linarith)
  have hS : tentSlope p m q x = 0 := by
    rw [tentSlope, comb, s1, s2, s3]
    ring
  have hF : tentFn p m q x = 0 := by
    rw [tentFn, comb, max_eq_left (by linarith : (0 : ℝ) ≤ x - p),
      max_eq_left (by linarith : (0 : ℝ) ≤ x - m), max_eq_left (by linarith : (0 : ℝ) ≤ x - q)]
    linear_combination hα - hβ
  rw [pairing, hS, hF]
  simp

lemma pairing_lower {f fd : ℝ → ℂ} {p m q x : ℝ} (hmq : m < q) (hx1 : p < x)
    (hx2 : x ≤ m) :
    pairing f fd p m q x
      = (((1 / (m - p)) : ℝ) : ℂ) * f x + (((x - p) / (m - p) : ℝ) : ℂ) * fd x := by
  have s1 : unitStep (x - p) = 1 := if_pos (by linarith)
  have s2 : unitStep (x - m) = 0 := if_neg (not_lt.2 (by linarith))
  have s3 : unitStep (x - q) = 0 := if_neg (not_lt.2 (by linarith))
  have hS : tentSlope p m q x = 1 / (m - p) := by
    rw [tentSlope, comb, s1, s2, s3]
    ring
  have hF : tentFn p m q x = (x - p) / (m - p) := by
    rw [tentFn, comb, max_eq_left (by linarith : (0 : ℝ) ≤ x - p),
      max_eq_right (by linarith : x - m ≤ 0), max_eq_right (by linarith : x - q ≤ 0)]
    ring
  rw [pairing, hS, hF]
  ring

lemma pairing_upper {f fd : ℝ → ℂ} {p m q x : ℝ} (hpm : p < m) (hmq : m < q) (hx1 : m < x)
    (hx2 : x ≤ q) :
    pairing f fd p m q x
      = -((((1 / (q - m)) : ℝ) : ℂ) * f x - (((q - x) / (q - m) : ℝ) : ℂ) * fd x) := by
  have h1 : m - p ≠ 0 := (sub_pos.2 hpm).ne'
  have h2 : q - m ≠ 0 := (sub_pos.2 hmq).ne'
  have hα : 1 / (m - p) * (m - p) = 1 := by field_simp
  have hβ : 1 / (q - m) * (q - m) = 1 := by field_simp
  have s1 : unitStep (x - p) = 1 := if_pos (by linarith)
  have s2 : unitStep (x - m) = 1 := if_pos (by linarith)
  have s3 : unitStep (x - q) = 0 := if_neg (not_lt.2 (by linarith))
  have hS : tentSlope p m q x = -(1 / (q - m)) := by
    rw [tentSlope, comb, s1, s2, s3]
    ring
  have hF : tentFn p m q x = (q - x) / (q - m) := by
    rw [tentFn, comb, max_eq_left (by linarith : (0 : ℝ) ≤ x - p),
      max_eq_left (by linarith : (0 : ℝ) ≤ x - m), max_eq_right (by linarith : x - q ≤ 0)]
    linear_combination hα - hβ
  rw [pairing, hS, hF]
  push_cast
  ring

theorem tent_identity {f fd : ℝ → ℂ} {a b p m q : ℝ} (hap : a < p) (hpm : p < m) (hmq : m < q)
    (hqb : q < b) (hw : HasWeakDerivOn f fd a b) :
    ∫ x in p..m, ((((1 / (m - p)) : ℝ) : ℂ) * f x + (((x - p) / (m - p) : ℝ) : ℂ) * fd x)
      = ∫ x in m..q, ((((1 / (q - m)) : ℝ) : ℂ) * f x - (((q - x) / (q - m) : ℝ) : ℂ) * fd x) := by
  obtain ⟨hf, hfd, hweak⟩ := hw
  obtain ⟨M, hM⟩ := deriv_kinkProfile_bound
  have hδ : 0 < b - q := sub_pos.2 hqb
  have hab : a < b := by linarith
  have hf' : Integrable f (volume.restrict (Ioo a b)) := hf
  have hfd' : Integrable fd (volume.restrict (Ioo a b)) := hfd
  have hid : ∀ n : ℕ, ∫ x in Ioo a b,
      f x * Complex.ofReal (deriv (tentApprox p m q ((b - q) / ((n : ℝ) + 2))) x)
      = -∫ x in Ioo a b, fd x * Complex.ofReal (tentApprox p m q ((b - q) / ((n : ℝ) + 2)) x) := by
    intro n
    have hε := seq_pos hδ n
    have hlt := seq_lt hδ n
    refine hweak _ (tentApprox_contDiff _ _ _ _)
      (HasCompactSupport.intro isCompact_Icc fun x hx => tentApprox_eq_zero hpm hmq hε hx) ?_
    exact (tentApprox_tsupport hpm hmq hε).trans (Icc_subset_Ioo hap (by linarith))
  have hnull : ∀ᵐ x ∂(volume.restrict (Ioo a b)), x - p ≠ 0 ∧ x - m ≠ 0 ∧ x - q ≠ 0 := by
    apply ae_restrict_of_ae
    have hfin : (volume : Measure ℝ) {p, m, q} = 0 := (Set.toFinite _).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfin] with x hx
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
    exact ⟨fun e => hx.1 (by linarith), fun e => hx.2.1 (by linarith), fun e => hx.2.2 (by linarith)⟩
  have hL : Tendsto (fun n : ℕ => ∫ x in Ioo a b,
      f x * Complex.ofReal (deriv (tentApprox p m q ((b - q) / ((n : ℝ) + 2))) x))
      atTop (𝓝 (∫ x in Ioo a b, f x * Complex.ofReal (tentSlope p m q x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖f x‖ * (2 * (1 / (m - p) + 1 / (q - m)) * M))
      (fun n => ?_) (hf'.norm.mul_const _) (fun n => ?_) ?_
    · exact hf'.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        ((tentApprox_contDiff _ _ _ _).continuous_deriv (by simp))).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_deriv_tentApprox_le hpm hmq (seq_pos hδ n) hM x)
        (norm_nonneg _)
    · filter_upwards [hnull] with x hx
      exact tendsto_const_nhds.congr'
        ((deriv_tentApprox_eventually hδ hx.1 hx.2.1 hx.2.2).mono fun n hn => by simp only [hn])
  have hR : Tendsto (fun n : ℕ => ∫ x in Ioo a b,
      fd x * Complex.ofReal (tentApprox p m q ((b - q) / ((n : ℝ) + 2)) x))
      atTop (𝓝 (∫ x in Ioo a b, fd x * Complex.ofReal (tentFn p m q x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖fd x‖ * (2 * (1 / (m - p) + 1 / (q - m)) * (b - a)))
      (fun n => ?_) (hfd'.norm.mul_const _) (fun n => ?_) ?_
    · exact hfd'.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (tentApprox_contDiff _ _ _ _).continuous).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_tentApprox_le hap hpm hmq hqb (seq_pos hδ n) hx)
        (norm_nonneg _)
    · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
        ((tentApprox_eventually (p := p) (m := m) (q := q) hδ x).mono fun n hn => by simp only [hn])
  have hlim : ∫ x in Ioo a b, f x * Complex.ofReal (tentSlope p m q x)
      = -∫ x in Ioo a b, fd x * Complex.ofReal (tentFn p m q x) :=
    tendsto_nhds_unique hL (hR.neg.congr fun n => (hid n).symm)
  have hI1 : Integrable (fun x => f x * Complex.ofReal (tentSlope p m q x))
      (volume.restrict (Ioo a b)) := by
    refine Integrable.mono' (hf'.norm.mul_const (2 * (1 / (m - p) + 1 / (q - m)) * 1))
      (hf'.aestronglyMeasurable.mul (Complex.continuous_ofReal.measurable.comp
        (tentSlope_measurable p m q)).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_tentSlope_le hpm hmq x) (norm_nonneg _)
  have hI2 : Integrable (fun x => fd x * Complex.ofReal (tentFn p m q x))
      (volume.restrict (Ioo a b)) := by
    refine Integrable.mono' (hfd'.norm.mul_const (2 * (1 / (m - p) + 1 / (q - m)) * (b - a)))
      (hfd'.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (tentFn_continuous p m q)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_tentFn_le hap hpm hmq hqb hx) (norm_nonneg _)
  have hsum : ∫ x in Ioo a b, pairing f fd p m q x = 0 := by
    simp only [pairing]
    rw [integral_add hI1 hI2, hlim]
    ring
  have hGi : IntervalIntegrable (pairing f fd p m q) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hI1.add hI2)
  have hG0 : ∫ x in a..b, pairing f fd p m q x = 0 := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    exact hsum
  have sub : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable (pairing f fd p m q) volume u v := fun u v hu huv hv =>
    hGi.mono_set (by
      rw [uIcc_of_le huv, uIcc_of_le hab.le]
      exact Icc_subset_Icc hu hv)
  have i1 := sub a p le_rfl hap.le (by linarith)
  have i2 := sub p m hap.le hpm.le (by linarith)
  have i3 := sub m q (by linarith) hmq.le hqb.le
  have i4 := sub q b (by linarith) hqb.le le_rfl
  have e1 : ∫ x in a..p, pairing f fd p m q x = 0 := by
    have : ∫ x in a..p, pairing f fd p m q x = ∫ _ in a..p, (0 : ℂ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => by
        rw [uIoc_of_le hap.le] at hx
        exact pairing_outer_left hpm hmq hx.2)
    rw [this, intervalIntegral.integral_zero]
  have e4 : ∫ x in q..b, pairing f fd p m q x = 0 := by
    have : ∫ x in q..b, pairing f fd p m q x = ∫ _ in q..b, (0 : ℂ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => by
        rw [uIoc_of_le hqb.le] at hx
        exact pairing_outer_right hpm hmq hx.1)
    rw [this, intervalIntegral.integral_zero]
  have e2 : ∫ x in p..m, pairing f fd p m q x
      = ∫ x in p..m, ((((1 / (m - p)) : ℝ) : ℂ) * f x + (((x - p) / (m - p) : ℝ) : ℂ) * fd x) :=
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => by
      rw [uIoc_of_le hpm.le] at hx
      exact pairing_lower hmq hx.1 hx.2)
  have e3 : ∫ x in m..q, pairing f fd p m q x
      = -∫ x in m..q, ((((1 / (q - m)) : ℝ) : ℂ) * f x - (((q - x) / (q - m) : ℝ) : ℂ) * fd x) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => by
      rw [uIoc_of_le hmq.le] at hx
      exact pairing_upper hpm hmq hx.1 hx.2)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans (i3.trans i4)),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (i3.trans i4),
    ← intervalIntegral.integral_add_adjacent_intervals i3 i4, e1, e2, e3, e4] at hG0
  linear_combination hG0

lemma sideTrace_of_lt {f fd : ℝ → ℂ} {c o : ℝ} (h : o < c) :
    sideTrace f fd c o
      = ∫ r in o..c, ((((1 / (c - o)) : ℝ) : ℂ) * f r + (((r - o) / (c - o) : ℝ) : ℂ) * fd r) := by
  rw [sideTrace, edgeSign, if_pos h, one_mul, min_eq_right h.le, max_eq_left h.le,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h.le]

lemma sideTrace_of_gt {f fd : ℝ → ℂ} {c o : ℝ} (h : c < o) :
    sideTrace f fd c o
      = ∫ r in c..o, ((((1 / (o - c)) : ℝ) : ℂ) * f r - (((o - r) / (o - c) : ℝ) : ℂ) * fd r) := by
  rw [sideTrace, edgeSign, if_neg (not_lt.2 h.le), min_eq_left h.le, max_eq_right h.le,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h.le, neg_one_mul,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have n1 : c - o ≠ 0 := (sub_neg.2 h).ne
  have n2 : o - c ≠ 0 := (sub_pos.2 h).ne'
  have e1 : (1 / (c - o) : ℝ) = -(1 / (o - c)) := by
    rw [← neg_div, div_eq_div_iff n1 n2]
    ring
  have e2 : (r - o) / (c - o) = (o - r) / (o - c) := by
    rw [div_eq_div_iff n1 n2]
    ring
  simp only [e1, e2]
  push_cast
  ring

end Internal

open Internal in
theorem sideTraceMatch : SideTraceMatchHolds := by
  intro f fd c o o' a b hco hco' ha hb hw
  have hc : a < c := lt_of_lt_of_le ha (min_le_left _ _)
  have ho : a < o := lt_of_lt_of_le ha (le_trans (min_le_right _ _) (min_le_left _ _))
  have ho' : a < o' := lt_of_lt_of_le ha (le_trans (min_le_right _ _) (min_le_right _ _))
  have bc : c < b := lt_of_le_of_lt (le_max_left _ _) hb
  have bo : o < b := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have bo' : o' < b := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  rcases lt_or_gt_of_ne hco with h1 | h1 <;> rcases lt_or_gt_of_ne hco' with h2 | h2
  · have p1 : a < (a + c) / 2 := by linarith
    have p2 : (a + c) / 2 < c := by linarith
    rw [sideTrace_of_gt h1, sideTrace_of_gt h2]
    exact (tent_identity p1 p2 h1 bo hw).symm.trans (tent_identity p1 p2 h2 bo' hw)
  · rw [sideTrace_of_gt h1, sideTrace_of_lt h2]
    exact (tent_identity ho' h2 h1 bo hw).symm
  · rw [sideTrace_of_lt h1, sideTrace_of_gt h2]
    exact tent_identity ho h1 h2 bo' hw
  · have q1 : c < (c + b) / 2 := by linarith
    have q2 : (c + b) / 2 < b := by linarith
    rw [sideTrace_of_lt h1, sideTrace_of_lt h2]
    exact (tent_identity ho h1 q1 q2 hw).trans (tent_identity ho' h2 q1 q2 hw).symm

end SideTrace

end CertCell

end Breakdown
