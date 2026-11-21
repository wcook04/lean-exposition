import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.ToVLinear
import Breakdown.Torus.ApproxSizes

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ApproxClose.Internal

def simField (W : ℝ → Space → Space) (T t μ : ℝ) : Space → Space :=
  fun y => Real.sqrt μ • approxField W T t (center + Real.sqrt μ • y)

def profSlice (W : ℝ → Space → Space) (T t μ : ℝ) : Space → Space :=
  dilateField (μ / (T - t)) (W (similarityTime T t))

abbrev IsGood (f : Space → Space) : Prop :=
  ContDiff ℝ ∞ f ∧ IsPeriodic f ∧ ∀ x, divergenceAt f x = 0

theorem gradEnergy_sub_comm (f g : Space → Space) : gradEnergy (f - g) = gradEnergy (g - f) := by
  unfold gradEnergy
  have e : g - f = -(f - g) := (neg_sub f g).symm
  rw [e]
  congr 1
  funext y
  rw [fderiv_neg]
  simp only [neg_apply, norm_neg]

theorem cutoffError (hA : ApproxFieldProperties) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C lam : ℝ}
    (hW : IsSimilarityProfile W q C) (hl : 0 < lam) (hl1 : lam < 1) {η : ℝ} (hη : 0 < η) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ T t : ℝ, 0 < μ → μ < μ₀ → 0 < T → t < T → lam * μ ≤ T - t → T - t ≤ μ →
      (∫ y, ∑ i : Fin 3, ‖fderiv ℝ (simField W T t μ - profSlice W T t μ) y (unitVector i)‖ ^ 2) ≤ η ∧
        μ * ∫ y, ‖simField W T t μ y‖ ^ 2 ≤ η := by
  obtain ⟨ℓ₀, hℓ₀, hgc⟩ := cutoffGradientClose hA W q C hW (η * lam) (mul_pos hη hl)
  obtain ⟨K, hK⟩ := cutoffMassBound hA W q C hW
  have hK1 : 0 < |K| + 1 := by positivity
  refine ⟨min (min ℓ₀ 1) ((η / (|K| + 1)) ^ 2), lt_min (lt_min hℓ₀ one_pos) (by positivity),
    fun μ T t hμ hμ₀ hT ht hlo hhi => ?_⟩
  have hμℓ : μ < ℓ₀ := hμ₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hμ1 : μ < 1 := hμ₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hμK : μ < (η / (|K| + 1)) ^ 2 := hμ₀.trans_le (min_le_right _ _)
  have hℓ : 0 < T - t := sub_pos.mpr ht
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsℓ : 0 < Real.sqrt (T - t) := Real.sqrt_pos.mpr hℓ
  have hr : 0 < Real.sqrt μ / Real.sqrt (T - t) := div_pos hsμ hsℓ
  have hdil := ApproxSizes.Internal.cutAt_dil (W := W) (T := T) (t := t) (μ := μ) hℓ
  have hsim : simField W T t μ = cutAt W T t μ := rfl
  have hprof : profSlice W T t μ = fun y => (Real.sqrt μ / Real.sqrt (T - t)) •
      W (similarityTime T t) ((Real.sqrt μ / Real.sqrt (T - t)) • y) := by
    unfold profSlice dilateField
    rw [Real.sqrt_div hμ.le]
  have hcs : ContDiff ℝ ∞ (cutAt W T t (T - t)) :=
    ApproxSizes.Internal.cutAt_contDiff (ApproxSizes.Internal.slice_contDiff hA hW hT ht) _
  have hws : ContDiff ℝ ∞ (W (similarityTime T t)) :=
    hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hdf : Differentiable ℝ (cutAt W T t (T - t) - W (similarityTime T t)) :=
    (hcs.sub hws).differentiable (by simp)
  refine ⟨?_, ?_⟩
  · have hdiff : simField W T t μ - profSlice W T t μ = fun y => (Real.sqrt μ / Real.sqrt (T - t)) •
        (cutAt W T t (T - t) - W (similarityTime T t)) ((Real.sqrt μ / Real.sqrt (T - t)) • y) := by
      rw [hsim, hdil, hprof]
      funext y
      simp [smul_sub]
    show gradEnergy (simField W T t μ - profSlice W T t μ) ≤ η
    rw [hdiff, ApproxSizes.Internal.gradEnergy_dil hdf hr, gradEnergy_sub_comm]
    have hgE := hgc T t hT ht (hhi.trans_lt hμℓ)
    have hsq : Real.sqrt μ * lam ≤ Real.sqrt (T - t) := by
      have e : Real.sqrt μ * lam = Real.sqrt (μ * lam ^ 2) := by
        rw [Real.sqrt_mul hμ.le, Real.sqrt_sq hl.le]
      rw [e]
      apply Real.sqrt_le_sqrt
      nlinarith
    have hrl : Real.sqrt μ / Real.sqrt (T - t) * lam ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hsℓ]
      exact hsq
    calc Real.sqrt μ / Real.sqrt (T - t) * gradEnergy (W (similarityTime T t) - cutAt W T t (T - t))
        ≤ Real.sqrt μ / Real.sqrt (T - t) * (η * lam) := mul_le_mul_of_nonneg_left hgE hr.le
      _ = (Real.sqrt μ / Real.sqrt (T - t) * lam) * η := by ring
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right hrl hη.le
      _ = η := one_mul η
  · have hm := ApproxSizes.Internal.mass_dil (cutAt W T t (T - t)) hr
    have hKb := hK T t hT ht (hhi.trans hμ1.le)
    have hsK : Real.sqrt μ < η / (|K| + 1) := (Real.sqrt_lt' (by positivity)).mpr hμK
    calc μ * ∫ y, ‖simField W T t μ y‖ ^ 2
        = μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2) := by
          rw [← hm, hsim, hdil]
      _ ≤ μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * (K / Real.sqrt (T - t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKb (inv_nonneg.mpr hr.le)) hμ.le
      _ = Real.sqrt μ * K := by
          have e : (Real.sqrt μ / Real.sqrt (T - t))⁻¹ * (K / Real.sqrt (T - t)) = K / Real.sqrt μ := by
            rw [inv_div]
            field_simp
          rw [e, mul_div_assoc', div_eq_iff hsμ.ne']
          linear_combination (-K) * Real.mul_self_sqrt hμ.le
      _ ≤ Real.sqrt μ * (|K| + 1) := by
          apply mul_le_mul_of_nonneg_left _ hsμ.le
          linarith [le_abs_self K]
      _ ≤ η := by
          rw [lt_div_iff₀ hK1] at hsK
          exact hsK.le

theorem fderiv_affine_apply {f : Space → Space} (hf : Differentiable ℝ f) (a : Space) (r : ℝ)
    (y v : Space) :
    fderiv ℝ (fun y : Space => r • f (a + r • y)) y v = (r * r) • fderiv ℝ f (a + r • y) v := by
  have h1 : HasFDerivAt (fun y : Space => a + r • y) (r • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id y).const_smul r).const_add a
  have h2 : HasFDerivAt (fun y : Space => r • f (a + r • y))
      (r • (fderiv ℝ f (a + r • y)).comp (r • ContinuousLinearMap.id ℝ Space)) y :=
    ((hf (a + r • y)).hasFDerivAt.comp y h1).const_smul r
  rw [h2.fderiv]
  simp [smul_smul]

theorem divergence_affine {f : Space → Space} (hf : Differentiable ℝ f) (a : Space) (r : ℝ)
    (y : Space) :
    divergenceAt (fun y : Space => r • f (a + r • y)) y = (r * r) * divergenceAt f (a + r • y) := by
  unfold divergenceAt
  simp_rw [fderiv_affine_apply hf a r y]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

theorem fderiv_affine {f : Space → Space} (hf : Differentiable ℝ f) (a : Space) (r : ℝ) (y : Space) :
    fderiv ℝ (fun y : Space => r • f (a + r • y)) y = (r * r) • fderiv ℝ f (a + r • y) := by
  have h1 : HasFDerivAt (fun y : Space => a + r • y) (r • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id y).const_smul r).const_add a
  have h2 : HasFDerivAt (fun y : Space => r • f (a + r • y))
      (r • (fderiv ℝ f (a + r • y)).comp (r • ContinuousLinearMap.id ℝ Space)) y :=
    ((hf (a + r • y)).hasFDerivAt.comp y h1).const_smul r
  rw [h2.fderiv]
  ext v
  simp [smul_smul]

theorem dilateDecay {f : Space → Space} (hf : IsDecayField f) {m : ℝ} (hm : 0 < m) :
    IsDecayField (dilateField m f) := by
  obtain ⟨h1, h2, C, hC⟩ := hf
  have hr : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  set r := Real.sqrt m with hrdef
  have hd : dilateField m f = fun y : Space => r • f (0 + r • y) := by
    funext y
    simp [dilateField, hrdef]
  have hdf : Differentiable ℝ f := h1.differentiable (by simp)
  have hC0 : 0 ≤ C := by
    have := (hC 0).1
    simp only [norm_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  set κ := 1 + 1 / r with hκ
  have hκ0 : 0 < κ := by positivity
  rw [hd]
  refine ⟨(h1.comp (contDiff_const.add (contDiff_id.const_smul r))).const_smul r, fun y => ?_,
    C * (r * κ + r ^ 2 * κ ^ 2), fun y => ⟨?_, ?_⟩⟩
  · rw [divergence_affine hdf, h2, mul_zero]
  · have hN : ‖r • y‖ = r * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hD : 0 < 1 + r * ‖y‖ := by positivity
    have hND : 1 + ‖y‖ ≤ κ * (1 + r * ‖y‖) := by
      have : κ * (1 + r * ‖y‖) = 1 + ‖y‖ + (r * ‖y‖ + 1 / r) := by
        rw [hκ]; field_simp; ring
      rw [this]; have : 0 ≤ r * ‖y‖ + 1 / r := by positivity
      linarith
    have hb := (hC (0 + r • y)).1
    rw [zero_add, hN] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, zero_add]
    calc r * ‖f (r • y)‖ ≤ r * (C / (1 + r * ‖y‖)) := mul_le_mul_of_nonneg_left hb hr.le
      _ ≤ C * (r * κ + r ^ 2 * κ ^ 2) / (1 + ‖y‖) := by
        rw [mul_div_assoc', div_le_div_iff₀ hD (by positivity)]
        have e1 : r * C * (1 + ‖y‖) ≤ r * C * (κ * (1 + r * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hND (by positivity)
        have e2 : 0 ≤ C * (r ^ 2 * κ ^ 2) * (1 + r * ‖y‖) := by positivity
        nlinarith
  · have hN : ‖r • y‖ = r * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hD : 0 < 1 + r * ‖y‖ := by positivity
    have hND : 1 + ‖y‖ ≤ κ * (1 + r * ‖y‖) := by
      have : κ * (1 + r * ‖y‖) = 1 + ‖y‖ + (r * ‖y‖ + 1 / r) := by
        rw [hκ]; field_simp; ring
      rw [this]; have : 0 ≤ r * ‖y‖ + 1 / r := by positivity
      linarith
    have hND2 : (1 + ‖y‖) ^ 2 ≤ κ ^ 2 * (1 + r * ‖y‖) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hND 2
    have hb := (hC (0 + r • y)).2
    rw [zero_add, hN] at hb
    rw [fderiv_affine hdf, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), zero_add]
    calc r * r * ‖fderiv ℝ f (r • y)‖ ≤ r * r * (C / (1 + r * ‖y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ C * (r * κ + r ^ 2 * κ ^ 2) / (1 + ‖y‖) ^ 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 : r * r * C * (1 + ‖y‖) ^ 2 ≤ r * r * C * (κ ^ 2 * (1 + r * ‖y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hND2 (by positivity)
        have e2 : 0 ≤ C * (r * κ) * (1 + r * ‖y‖) ^ 2 := by positivity
        nlinarith

theorem tsupport_sub_ball {f : Space → Space} {B : ℝ} (h : ∀ y, B < ‖y‖ → f y = 0) :
    tsupport f ⊆ Metric.closedBall 0 B := by
  refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
  by_contra h'
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at h'
  exact hy (h y h')

theorem hasCompactSupport_of_ball {f : Space → Space} {B : ℝ} (h : ∀ y, B < ‖y‖ → f y = 0) :
    HasCompactSupport f :=
  (isCompact_closedBall 0 B).of_isClosed_subset (isClosed_tsupport _) (tsupport_sub_ball h)

theorem zero_decayField : IsDecayField (0 : Space → Space) := by
  refine ⟨contDiff_const, fun y => ?_, 0, fun y => ?_⟩
  · simp [divergenceAt]
  · simp

theorem decay_add {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f + g) := by
  obtain ⟨hf1, hf2, C1, hC1⟩ := hf
  obtain ⟨hg1, hg2, C2, hC2⟩ := hg
  have df : Differentiable ℝ f := hf1.differentiable (by simp)
  have dg : Differentiable ℝ g := hg1.differentiable (by simp)
  refine ⟨hf1.add hg1, fun y => ?_, C1 + C2, fun y => ⟨?_, ?_⟩⟩
  · rw [ToVLinear.Internal.divergenceAt_add (df y) (dg y), hf2 y, hg2 y, add_zero]
  · calc ‖(f + g) y‖ ≤ ‖f y‖ + ‖g y‖ := norm_add_le _ _
      _ ≤ C1 / (1 + ‖y‖) + C2 / (1 + ‖y‖) := add_le_add (hC1 y).1 (hC2 y).1
      _ = (C1 + C2) / (1 + ‖y‖) := by rw [add_div]
  · rw [fderiv_add (df y) (dg y)]
    calc ‖fderiv ℝ f y + fderiv ℝ g y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_add_le _ _
      _ ≤ C1 / (1 + ‖y‖) ^ 2 + C2 / (1 + ‖y‖) ^ 2 := add_le_add (hC1 y).2 (hC2 y).2
      _ = (C1 + C2) / (1 + ‖y‖) ^ 2 := by rw [add_div]

theorem decay_smul (c : ℝ) {f : Space → Space} (hf : IsDecayField f) : IsDecayField (c • f) := by
  obtain ⟨hf1, hf2, C1, hC1⟩ := hf
  refine ⟨hf1.const_smul c, fun y => ?_, |c| * C1, fun y => ⟨?_, ?_⟩⟩
  · rw [ToVLinear.Internal.divergenceAt_smul, hf2 y, mul_zero]
  · rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hC1 y).1 (abs_nonneg c)
  · rw [fderiv_const_smul_field, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hC1 y).2 (abs_nonneg c)

theorem decay_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f - g) := by
  have : f - g = f + (-1 : ℝ) • g := by
    funext y
    simp [sub_eq_add_neg]
  rw [this]
  exact decay_add hf (decay_smul _ hg)

theorem decay_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {f : ι → Space → Space}
    (hf : ∀ i, IsDecayField (f i)) : IsDecayField (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_decayField
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact decay_add (decay_smul _ (hf a)) ih

theorem eventually_zero_fderiv {f : Space → Space} {B : ℝ} (h : ∀ y, B < ‖y‖ → f y = 0) {y : Space}
    (hy : B < ‖y‖) : fderiv ℝ f y = 0 := by
  have hev : f =ᶠ[nhds y] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact h z hz
  rw [hev.fderiv_eq]
  simp

theorem decay_of_ball {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hd : ∀ y, divergenceAt f y = 0)
    {B : ℝ} (h : ∀ y, B < ‖y‖ → f y = 0) : IsDecayField f := by
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : Space) B).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : Space) B).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  refine ⟨hf, hd, (|C0| + |C1|) * (1 + |B|) ^ 2, fun y => ?_⟩
  have hy1 : 0 < 1 + ‖y‖ := by positivity
  by_cases hy : ‖y‖ ≤ B
  · have hyb : y ∈ Metric.closedBall (0 : Space) B := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hB : 1 + ‖y‖ ≤ 1 + |B| := by linarith [le_abs_self B]
    have hB1 : 1 ≤ 1 + |B| := by linarith [abs_nonneg B]
    have hsq : (1 + ‖y‖) ^ 2 ≤ (1 + |B|) ^ 2 := pow_le_pow_left₀ hy1.le hB 2
    have hsq1 : 1 + ‖y‖ ≤ (1 + |B|) ^ 2 := by nlinarith
    have hc0 : ‖f y‖ ≤ |C0| + |C1| := (hC0 y hyb).trans (by linarith [le_abs_self C0, abs_nonneg C1])
    have hc1 : ‖fderiv ℝ f y‖ ≤ |C0| + |C1| :=
      (hC1 y hyb).trans (by linarith [le_abs_self C1, abs_nonneg C0])
    have hn : 0 ≤ |C0| + |C1| := by positivity
    constructor
    · rw [le_div_iff₀ hy1]
      exact mul_le_mul hc0 hsq1 hy1.le hn
    · rw [le_div_iff₀ (by positivity)]
      exact mul_le_mul hc1 hsq (by positivity) hn
  · rw [not_le] at hy
    rw [h y hy, eventually_zero_fderiv h hy]
    simp only [norm_zero]
    constructor <;> positivity

theorem embed_sum (hEL : Freq.EmbedLinear) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {f : ι → Space → Space} (hf : ∀ i, IsDecayField (f i)) :
    Freq.embedX (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Freq.embedX (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hEL.2.2 0 0 zero_decayField
    simp only [zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hEL.1 _ _ (decay_smul _ (hf a)) (decay_sum s c hf),
      hEL.2.2 _ _ (hf a), ih]

theorem good_zero : IsGood (0 : Space → Space) :=
  ⟨contDiff_const, fun _ _ => rfl, fun x => by simp [divergenceAt]⟩

theorem good_add {f g : Space → Space} (hf : IsGood f) (hg : IsGood g) : IsGood (f + g) :=
  ⟨hf.1.add hg.1, ToVLinear.Internal.isPeriodic_add hf.2.1 hg.2.1, fun x => by
    rw [ToVLinear.Internal.divergenceAt_add ((hf.1.differentiable (by simp)) x)
      ((hg.1.differentiable (by simp)) x), hf.2.2 x, hg.2.2 x, add_zero]⟩

theorem good_smul (c : ℝ) {f : Space → Space} (hf : IsGood f) : IsGood (c • f) :=
  ⟨hf.1.const_smul c, ToVLinear.Internal.isPeriodic_smul c hf.2.1, fun x => by
    rw [ToVLinear.Internal.divergenceAt_smul, hf.2.2 x, mul_zero]⟩

theorem toV_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → Space → Space}
    (hg : ∀ i, IsGood (g i)) :
    IsGood (∑ i ∈ s, c i • g i) ∧ toV (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • toV (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using good_zero, ?_⟩
    have h := toV_smul 0 good_zero.1 good_zero.2.1 good_zero.2.2
    simp only [zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha' := good_smul (c a) (hg a)
    refine ⟨good_add ha' ih.1, ?_⟩
    rw [toVAdd _ _ ha'.1 ih.1.1 ha'.2.1 ih.1.2.1 ha'.2.2 ih.1.2.2, ih.2,
      toV_smul _ (hg a).1 (hg a).2.1 (hg a).2.2]

theorem toV_sub_sum {m : ℕ} (c : Fin m → ℝ) {f : Space → Space} {g : Fin m → Space → Space}
    (hf : IsGood f) (hg : ∀ i, IsGood (g i)) :
    toV (f - ∑ i, c i • g i) = toV f - ∑ i, c i • toV (g i) := by
  obtain ⟨h1, h2⟩ := toV_sum Finset.univ c hg
  have hn := good_smul (-1) h1
  have : f - ∑ i, c i • g i = f + (-1 : ℝ) • ∑ i, c i • g i := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [this, toVAdd _ _ hf.1 hn.1 hf.2.1 hn.2.1 hf.2.2 hn.2.2, toV_smul _ h1.1 h1.2.1 h1.2.2, h2,
    neg_one_smul, ← sub_eq_add_neg]

theorem l2_eq {f : Space → Space} (hf : MemLp f 2) :
    Real.sqrt (∫ y, ‖f y‖ ^ 2) = ‖hf.toLp f‖ := by
  have h1 : ‖hf.toLp f‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [real_inner_self_eq_norm_sq, hy]
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

theorem l2_add_le {f g : Space → Space} (hf : MemLp f 2) (hg : MemLp g 2) :
    Real.sqrt (∫ y, ‖(f + g) y‖ ^ 2) ≤ Real.sqrt (∫ y, ‖f y‖ ^ 2) + Real.sqrt (∫ y, ‖g y‖ ^ 2) := by
  rw [l2_eq (hf.add hg), l2_eq hf, l2_eq hg, MemLp.toLp_add hf hg]
  exact norm_add_le _ _

theorem l2_sub_le {f g : Space → Space} (hf : MemLp f 2) (hg : MemLp g 2) :
    Real.sqrt (∫ y, ‖(f - g) y‖ ^ 2) ≤ Real.sqrt (∫ y, ‖f y‖ ^ 2) + Real.sqrt (∫ y, ‖g y‖ ^ 2) := by
  rw [l2_eq (hf.sub hg), l2_eq hf, l2_eq hg, MemLp.toLp_sub hf hg]
  exact norm_sub_le _ _

theorem l2_smul (c : ℝ) (f : Space → Space) :
    Real.sqrt (∫ y, ‖(c • f) y‖ ^ 2) = |c| * Real.sqrt (∫ y, ‖f y‖ ^ 2) := by
  have : (fun y => ‖(c • f) y‖ ^ 2) = fun y => c ^ 2 * ‖f y‖ ^ 2 := by
    funext y
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [this, integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem l2_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) {f : ι → Space → Space}
    (hf : ∀ i, MemLp (f i) 2) :
    MemLp (∑ i ∈ s, c i • f i) 2 ∧
      Real.sqrt (∫ y, ‖(∑ i ∈ s, c i • f i) y‖ ^ 2) ≤ ∑ i ∈ s, |c i| * Real.sqrt (∫ y, ‖f i y‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha' : MemLp (c a • f a) 2 := (hf a).const_smul (c a)
    refine ⟨ha'.add ih.1, ?_⟩
    calc Real.sqrt (∫ y, ‖(c a • f a + ∑ i ∈ s, c i • f i) y‖ ^ 2)
        ≤ Real.sqrt (∫ y, ‖(c a • f a) y‖ ^ 2) + Real.sqrt (∫ y, ‖(∑ i ∈ s, c i • f i) y‖ ^ 2) :=
          l2_add_le ha' ih.1
      _ ≤ |c a| * Real.sqrt (∫ y, ‖f a y‖ ^ 2) + ∑ i ∈ s, |c i| * Real.sqrt (∫ y, ‖f i y‖ ^ 2) := by
          rw [l2_smul]
          exact add_le_add le_rfl ih.2

theorem memLp_of_ball {f : Space → Space} (hf : Continuous f) {B : ℝ} (h : ∀ y, B < ‖y‖ → f y = 0) :
    MemLp f 2 := hf.memLp_of_hasCompactSupport (hasCompactSupport_of_ball h)

theorem l2_le_grad (hG : Freq.GradSixDecay) {b : ℝ} : ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : Space → Space,
    IsTestField φ → tsupport φ ⊆ Metric.closedBall 0 b →
      ∫ y, ‖φ y‖ ^ 2 ≤ K * ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2 := by
  obtain ⟨S, hS⟩ := hG
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ((volume.restrict (Metric.closedBall (0 : Space) b)) univ ^
      (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)).toReal := ⟨_, rfl⟩
  refine ⟨S ^ 2 * c ^ 2, by positivity, fun φ hφ hsup => ?_⟩
  have hvan : ∀ y, b < ‖y‖ → φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (fun h => by
    have := hsup h
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith)
  have hdec := decay_of_ball hφ.1 hφ.2.2 hvan
  obtain ⟨h6, h6b⟩ := hS φ hdec
  have h2 : MemLp φ 2 := memLp_of_ball hφ.1.continuous hvan
  have hI : 0 ≤ ∫ y, ‖φ y‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hJ : 0 ≤ ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2 :=
    integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => by positivity
  have e1 : ∫ y, ‖φ y‖ ^ 2 = ((eLpNorm φ 2 volume).toReal) ^ 2 := by
    rw [← Lp.norm_toLp φ h2, ← l2_eq h2, Real.sq_sqrt hI]
  have hsupp : Function.support φ ⊆ Metric.closedBall 0 b := (subset_tsupport φ).trans hsup
  have hfin : (volume.restrict (Metric.closedBall (0 : Space) b)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall (0 : Space) b).measure_lt_top.ne
  have hexp : (0 : ℝ) ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal := by norm_num
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Metric.closedBall (0 : Space) b))
    (show (2 : ℝ≥0∞) ≤ 6 by norm_num) h2.1.restrict
  rw [eLpNorm_restrict_eq_of_support_subset hsupp, eLpNorm_restrict_eq_of_support_subset hsupp] at hH
  have hne2 := ENNReal.rpow_ne_top_of_nonneg hexp hfin
  have hT : (eLpNorm φ 2 volume).toReal ≤ (eLpNorm φ 6 volume).toReal * c := by
    rw [hcdef, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top h6.2.ne hne2) hH
  have hc : 0 ≤ c := hcdef ▸ ENNReal.toReal_nonneg
  have hT2 : (eLpNorm φ 2 volume).toReal ≤
      S * Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) * c :=
    hT.trans (mul_le_mul_of_nonneg_right h6b hc)
  have h3 := pow_le_pow_left₀ ENNReal.toReal_nonneg hT2 2
  rw [e1]
  calc _ ≤ (S * Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) * c) ^ 2 := h3
    _ = S ^ 2 * c ^ 2 * ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hJ]
      ring

theorem sum_vanish {m : ℕ} (c : Fin m → ℝ) {φ : Fin m → Space → Space} {B : ℝ}
    (h : ∀ l y, B < ‖y‖ → φ l y = 0) : ∀ y, B < ‖y‖ → (∑ l, c l • φ l) y = 0 := by
  intro y hy
  simp [Finset.sum_apply, h _ y hy]

theorem toV_transplant_sub (hTS : TransplantSmooth) {m : ℕ} (c : Fin m → ℝ) {G : Space → Space}
    {φ : Fin m → Space → Space} {μ B : ℝ} (hsh : IsShellScale μ B) (hG : IsDecayField G)
    (hGs : ∀ y, B < ‖y‖ → G y = 0) (hφ : ∀ l, IsDecayField (φ l))
    (hφs : ∀ l y, B < ‖y‖ → φ l y = 0) :
    μ ^ (1 / 4 : ℝ) • toV (transplantField μ G) - ∑ l, c l • (μ ^ (1 / 4 : ℝ) • toV (transplantField μ (φ l))) =
      μ ^ (1 / 4 : ℝ) • toV (transplantField μ (G - ∑ l, c l • φ l)) := by
  have good : ∀ g : Space → Space, IsDecayField g → (∀ y, B < ‖y‖ → g y = 0) →
      IsGood (transplantField μ g) := fun g hg hgs => by
    obtain ⟨h1, h2, h3, _⟩ := hTS g μ B hg.1 hg.2.1 hsh (tsupport_sub_ball hgs)
    exact ⟨h1, h2, h3⟩
  have htr : transplantField μ (G - ∑ l, c l • φ l) = transplantField μ G - ∑ l, c l • transplantField μ (φ l) := by
    funext x
    simp only [transplantField, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_sub, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  rw [htr, toV_sub_sum c (good G hG hGs) (fun l => good (φ l) (hφ l) (hφs l)), smul_sub, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

theorem pieceBound (hTN : TransplantNorm) (hEN : Freq.EmbedNorm) (hEL : Freq.EmbedLinear) {m : ℕ}
    (c : Fin m → ℝ) {G Pf : Space → Space} {φ : Fin m → Space → Space} {μ B ε η M2 : ℝ}
    (hsh : IsShellScale μ B) (hG : IsDecayField G) (hGs : ∀ y, B < ‖y‖ → G y = 0)
    (hφ : ∀ l, IsDecayField (φ l)) (hφs : ∀ l y, B < ‖y‖ → φ l y = 0) (hPf : IsDecayField Pf)
    (hε : ‖Freq.embedX Pf - ∑ l, c l • Freq.embedX (φ l)‖ ≤ ε)
    (hgrad : (∫ y, ∑ i : Fin 3, ‖fderiv ℝ (G - Pf) y (unitVector i)‖ ^ 2) ≤ η)
    (hmass : μ * ∫ y, ‖G y‖ ^ 2 ≤ η) (hM2 : Real.sqrt (∫ y, ‖(∑ l, c l • φ l) y‖ ^ 2) ≤ M2) :
    ‖μ ^ (1 / 4 : ℝ) • toV (transplantField μ (G - ∑ l, c l • φ l))‖ ^ 2 ≤
      (ε + Real.sqrt η) ^ 2 + 2 * η + 2 * μ * M2 ^ 2 := by
  have hS := decay_sum Finset.univ c hφ
  have hSs := sum_vanish c hφs
  have hg := decay_sub hG hS
  have hgs : ∀ y, B < ‖y‖ → (G - ∑ l, c l • φ l) y = 0 := fun y hy => by
    simp [hGs y hy, hSs y hy]
  rw [hTN _ μ B hg.1 hg.2.1 hsh (tsupport_sub_ball hgs), ← hEN _ hg]
  have hemb : Freq.embedX (G - ∑ l, c l • φ l) =
      Freq.embedX (G - Pf) + (Freq.embedX Pf - ∑ l, c l • Freq.embedX (φ l)) := by
    rw [hEL.2.1 _ _ hG hS, hEL.2.1 _ _ hG hPf, embed_sum hEL Finset.univ c hφ]
    abel
  have hη : 0 ≤ η := le_trans (integral_nonneg fun y => by positivity) hgrad
  have h1 : ‖Freq.embedX (G - Pf)‖ ≤ Real.sqrt η := by
    rw [← abs_norm]
    apply Real.abs_le_sqrt
    rw [hEN _ (decay_sub hG hPf)]
    exact hgrad
  have h2 : ‖Freq.embedX (G - ∑ l, c l • φ l)‖ ≤ ε + Real.sqrt η := by
    rw [hemb]
    calc _ ≤ ‖Freq.embedX (G - Pf)‖ + ‖Freq.embedX Pf - ∑ l, c l • Freq.embedX (φ l)‖ := norm_add_le _ _
      _ ≤ Real.sqrt η + ε := add_le_add h1 hε
      _ = ε + Real.sqrt η := add_comm _ _
  have h3 : ‖Freq.embedX (G - ∑ l, c l • φ l)‖ ^ 2 ≤ (ε + Real.sqrt η) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hGm := memLp_of_ball hG.1.continuous hGs
  have hSm := memLp_of_ball hS.1.continuous hSs
  have h4 := l2_sub_le hGm hSm
  have i1 : 0 ≤ ∫ y, ‖(G - ∑ l, c l • φ l) y‖ ^ 2 := integral_nonneg fun y => by positivity
  have i2 : 0 ≤ ∫ y, ‖G y‖ ^ 2 := integral_nonneg fun y => by positivity
  have i3 : 0 ≤ ∫ y, ‖(∑ l, c l • φ l) y‖ ^ 2 := integral_nonneg fun y => by positivity
  have e1 := Real.sq_sqrt i1
  have e2 := Real.sq_sqrt i2
  have e3 := Real.sq_sqrt i3
  have s1 := Real.sqrt_nonneg (∫ y, ‖(G - ∑ l, c l • φ l) y‖ ^ 2)
  have s2 := Real.sqrt_nonneg (∫ y, ‖G y‖ ^ 2)
  have s3 := Real.sqrt_nonneg (∫ y, ‖(∑ l, c l • φ l) y‖ ^ 2)
  have hμ := hsh.1
  have hsq : Real.sqrt (∫ y, ‖(∑ l, c l • φ l) y‖ ^ 2) ^ 2 ≤ M2 ^ 2 := pow_le_pow_left₀ s3 hM2 2
  have ha := pow_le_pow_left₀ s1 h4 2
  have h5 : (∫ y, ‖(G - ∑ l, c l • φ l) y‖ ^ 2) ≤ 2 * (∫ y, ‖G y‖ ^ 2) + 2 * M2 ^ 2 := by
    rw [← e1, ← e2]
    nlinarith [sq_nonneg (Real.sqrt (∫ y, ‖G y‖ ^ 2) - Real.sqrt (∫ y, ‖(∑ l, c l • φ l) y‖ ^ 2))]
  have h6 : μ * (∫ y, ‖(G - ∑ l, c l • φ l) y‖ ^ 2) ≤ 2 * (μ * ∫ y, ‖G y‖ ^ 2) + 2 * μ * M2 ^ 2 :=
    calc _ ≤ μ * (2 * (∫ y, ‖G y‖ ^ 2) + 2 * M2 ^ 2) := mul_le_mul_of_nonneg_left h5 hμ.le
      _ = _ := by ring
  linarith

theorem dil_split (hDA : Freq.DilationAlgebra) {a a₀ : ℝ} (ha : 0 < a) (x x₀ : Freq.X) :
    ‖Freq.dilX a x - Freq.dilX a₀ x₀‖ ≤ a ^ (1 / 4 : ℝ) * ‖x - x₀‖ + ‖Freq.dilX a x₀ - Freq.dilX a₀ x₀‖ := by
  have hsplit : Freq.dilX a x - Freq.dilX a₀ x₀ =
      Freq.dilX a (x - x₀) + (Freq.dilX a x₀ - Freq.dilX a₀ x₀) := by
    rw [map_sub]
    abel
  rw [hsplit, ← hDA.1 a ha]
  exact norm_add_le _ _

theorem embedContinuous (hSG : SliceGradientContinuous) (hSD : SliceDecay) (hEN : Freq.EmbedNorm)
    (hEL : Freq.EmbedLinear) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) : Continuous (fun σ => Freq.embedX (W σ)) := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ σ, Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ (W σ - W σ₀) y (unitVector i)‖ ^ 2) =
      ‖Freq.embedX (W σ) - Freq.embedX (W σ₀)‖ := fun σ => by
    rw [← hEL.2.1 _ _ (hSD W q C hW σ) (hSD W q C hW σ₀),
      ← hEN _ (decay_sub (hSD W q C hW σ) (hSD W q C hW σ₀)), Real.sqrt_sq (norm_nonneg _)]
  have h := (Real.continuous_sqrt.tendsto 0).comp (hSG W q C hW σ₀)
  rw [Real.sqrt_zero] at h
  exact h.congr heq

theorem profileContinuous (hDA : Freq.DilationAlgebra) (hDC : Freq.DilationContinuous)
    (hSG : SliceGradientContinuous) (hSD : SliceDecay) (hEN : Freq.EmbedNorm) (hEL : Freq.EmbedLinear)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) (s₀ L : ℝ)
    (hL : L < 1) :
    Continuous (fun t : Icc (0 : ℝ) L =>
      Freq.dilX (1 - (t : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ)))))) := by
  have hx := embedContinuous hSG hSD hEN hEL hW
  have ha_pos : ∀ t : Icc (0 : ℝ) L, 0 < 1 - (t : ℝ) := fun t => by linarith [t.2.2]
  have hac : Continuous (fun t : Icc (0 : ℝ) L => (1 - (t : ℝ))⁻¹) :=
    (continuous_const.sub continuous_subtype_val).inv₀ (fun t => (ha_pos t).ne')
  have hxc : Continuous (fun t : Icc (0 : ℝ) L => Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ))))) :=
    hx.comp (continuous_const.sub ((continuous_const.sub continuous_subtype_val).log
      (fun t => (ha_pos t).ne')))
  rw [continuous_iff_continuousAt]
  intro t₀
  have ha₀ : 0 < (1 - (t₀ : ℝ))⁻¹ := inv_pos.mpr (ha_pos t₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun t : Icc (0 : ℝ) L => ((1 - (t : ℝ))⁻¹) ^ (1 / 4 : ℝ) *
      ‖Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ)))) - Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ))))‖ +
      ‖Freq.dilX (1 - (t : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ))))) -
        Freq.dilX (1 - (t₀ : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ)))))‖)
    (fun t => norm_nonneg _) (fun t => dil_split hDA (inv_pos.mpr (ha_pos t)) _ _) ?_
  have h1 := (hac.tendsto t₀).rpow_const (p := 1 / 4) (Or.inl ha₀.ne')
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (hxc.tendsto t₀)
  have h3 := tendsto_iff_norm_sub_tendsto_zero.mp
    (((hDC (Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ)))))).continuousAt
      (Ioi_mem_nhds ha₀)).tendsto.comp (hac.tendsto t₀))
  have h4 := (h1.mul h2).add h3
  rw [mul_zero, add_zero] at h4
  exact h4

theorem simField_props (hA : ApproxFieldProperties) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t μ : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T) (hμ : 0 < μ) :
    IsDecayField (simField W T t μ) ∧
      (∀ y, 1 / (8 * Real.sqrt μ) < ‖y‖ → simField W T t μ y = 0) ∧
      approxPeriodic W T t = transplantField μ (simField W T t μ) := by
  have hAW := hA W q C T hW hT
  have h1 := hAW.1
  have h3 := hAW.2.2
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsm : ContDiff ℝ ∞ (approxField W T t) := by
    have hc : ContDiffOn ℝ ∞ ((fun z : ℝ × Space => approxField W T z.1 z.2) ∘ (fun x : Space => (t, x)))
        univ := h1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨ht, mem_univ x⟩)
    exact contDiffOn_univ.mp hc
  have hsf : ContDiff ℝ ∞ (simField W T t μ) := by
    unfold simField
    exact (hsm.comp (contDiff_const.add (contDiff_id.const_smul (Real.sqrt μ)))).const_smul (Real.sqrt μ)
  have hvan : ∀ y, 1 / (8 * Real.sqrt μ) < ‖y‖ → simField W T t μ y = 0 := by
    intro y hy
    have hd : centralRadius / 2 ≤ dist (center + Real.sqrt μ • y) center := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hsμ, centralRadius]
      rw [div_lt_iff₀ (by positivity)] at hy
      nlinarith
    have h0 : approxField W T t (center + Real.sqrt μ • y) = 0 := ((h3 t ht _).2.1 hd).1
    unfold simField
    rw [h0, smul_zero]
  have hdiv : ∀ y, divergenceAt (simField W T t μ) y = 0 := by
    intro y
    unfold simField
    rw [divergence_affine (hsm.differentiable (by simp)), (h3 t ht _).1, mul_zero]
  refine ⟨decay_of_ball hsf hdiv hvan, hvan, ?_⟩
  funext x
  unfold approxPeriodic transplantField simField simCoord
  rw [smul_smul, inv_mul_cancel₀ hsμ.ne', one_smul, smul_smul, mul_inv_cancel₀ hsμ.ne', one_smul,
    add_sub_cancel]

theorem r3_bound {L b : ℝ} (A : Approximant L b) (Q : C(Icc (0 : ℝ) L, Freq.X)) (n : ℕ)
    (x : Icc (0 : ℝ) L) {ε : ℝ} (h : ‖A.r3Piece n - Q‖ ≤ ε) {a : Freq.X} (ha : Q x = a) :
    ‖a - ∑ l, A.weight n l x • Freq.embedX (A.field n l)‖ ≤ ε := by
  have e2 : (A.r3Piece n) x = ∑ l, A.weight n l x • Freq.embedX (A.field n l) := rfl
  have hle := (ContinuousMap.norm_coe_le_norm (A.r3Piece n - Q) x).trans h
  rw [ContinuousMap.sub_apply, e2, ha, norm_sub_rev] at hle
  exact hle

theorem torus_diff {L b : ℝ} (A : Approximant L b) (μ : ℝ) (Q : C(Icc (0 : ℝ) L, V)) (n : ℕ)
    (x : Icc (0 : ℝ) L) {a : V} (ha : Q x = a) :
    (Q - A.torusPiece μ n) x =
      a - ∑ l, A.weight n l x • ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ (A.field n l))) := by
  rw [ContinuousMap.sub_apply, ha]
  rfl

theorem field_vanish {L b : ℝ} (A : Approximant L b) (n : ℕ) (l : Fin A.terms) :
    ∀ y, b < ‖y‖ → A.field n l y = 0 := by
  intro y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hy'
  have := A.support n l hy'
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

end ApproxClose.Internal

open ApproxClose.Internal in
set_option maxHeartbeats 1000000 in
theorem approxClose (hTN : TransplantNorm) (hTS : TransplantSmooth) (hA : ApproxFieldProperties)
    (hL : ApproxLinks) (hEN : Freq.EmbedNorm) (hEL : Freq.EmbedLinear) (hED : Freq.EmbedDilate)
    (_hPP : ProfilePieceStatement) (hDA : Freq.DilationAlgebra)
    (hDC : Freq.DilationContinuous) (hSG : SliceGradientContinuous) (hGradSix : Freq.GradSixDecay) :
    ApproxClose := by
  intro F hF W q C P k b ε δ A hW hP hk hb hδ hAε
  have hSD : SliceDecay := fun _ _ _ hW' s => ApproxSizes.Internal.slice_decay hW' s
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hl : 0 < Real.exp (-(P / k)) := Real.exp_pos _
  have hl1 : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hP hk'))
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hAε 0)
  obtain ⟨Cb, hCb⟩ := A.bound
  obtain ⟨K, hK0, hK⟩ := l2_le_grad hGradSix (b := b)
  set M2 : ℝ := (A.terms : ℝ) * (|Cb| * (Real.sqrt K * |Cb|)) with hM2
  have hM2n : 0 ≤ M2 := by positivity
  obtain ⟨μ₀, hμ₀, hcut⟩ := cutoffError hA hW hl hl1 (η := δ ^ 2 / 16) (by positivity)
  have hb8 : 0 < (1 / (8 * b)) ^ 2 := by positivity
  have hm8 : 0 < δ ^ 2 / (16 * (M2 ^ 2 + 1)) := by positivity
  refine ⟨min (min μ₀ 1) (min ((1 / (8 * b)) ^ 2) (δ ^ 2 / (16 * (M2 ^ 2 + 1)))),
    lt_min (lt_min hμ₀ one_pos) (lt_min hb8 hm8), ?_⟩
  intro T hT hT₀ n
  have hTa : T < μ₀ := hT₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hT1 : T ≤ 1 := (hT₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hTb : T < (1 / (8 * b)) ^ 2 := hT₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hTm : T < δ ^ 2 / (16 * (M2 ^ 2 + 1)) :=
    hT₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Real.exp (-(P / k)) := ⟨_, rfl⟩
  have hl' : 0 < lam := hlam ▸ hl
  have hl1' : lam < 1 := hlam ▸ hl1
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = stepScale T (Real.exp (-(P / k))) n := ⟨_, rfl⟩
  have hμ : 0 < μ := hμdef ▸ stepScale_pos hT hl n
  have hμT : μ ≤ T := by
    rw [hμdef, stepScale]
    exact mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
  rw [← hμdef]
  refine (ContinuousMap.norm_le _ (add_nonneg hε hδ.le)).mpr fun s => ?_
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 - lam := hlam ▸ s.2.2
  have h1s : 0 < 1 - (s : ℝ) := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = stepStart T (Real.exp (-(P / k))) n + μ * s := ⟨_, rfl⟩
  have hTt : T - t = μ * (1 - s) := by
    rw [ht, stepStart, ← hμdef]
    ring
  have htT : t < T := by nlinarith
  have hlo : Real.exp (-(P / k)) * μ ≤ T - t := by
    have h : lam * μ ≤ T - t := by rw [hTt]; nlinarith
    rwa [hlam] at h
  have hhi : T - t ≤ μ := by rw [hTt]; nlinarith
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsqb : Real.sqrt μ < 1 / (8 * b) :=
    (Real.sqrt_lt' (by positivity)).mpr (hμT.trans_lt hTb)
  obtain ⟨B, hB⟩ : ∃ B, B = max b (1 / (8 * Real.sqrt μ)) := ⟨_, rfl⟩
  have hsh : IsShellScale μ B := by
    refine ⟨hμ, hμT.trans hT1, hB ▸ lt_max_of_lt_left hb, ?_⟩
    rw [hB, mul_max_of_nonneg _ _ hsμ.le]
    have e8 : Real.sqrt μ * (1 / (8 * Real.sqrt μ)) = 1 / 8 := by
      field_simp
    refine max_le ?_ e8.le
    rw [lt_div_iff₀ (by positivity)] at hsqb
    have h8 : Real.sqrt μ * (8 * b) = 8 * (Real.sqrt μ * b) := by ring
    linarith
  obtain ⟨hG, hGs, hper⟩ := simField_props hA hW hT htT hμ (μ := μ)
  have hGB : ∀ y, B < ‖y‖ → simField W T t μ y = 0 := fun y hy =>
    hGs y (lt_of_le_of_lt (hB ▸ le_max_right _ _) hy)
  have hφ : ∀ l, IsDecayField (A.field n l) := fun l =>
    decay_of_ball (A.isTest n l).1 (A.isTest n l).2.2 (field_vanish A n l)
  have hφB : ∀ l y, B < ‖y‖ → A.field n l y = 0 := fun l y hy =>
    field_vanish A n l y (lt_of_le_of_lt (hB ▸ le_max_left _ _) hy)
  have hPf : IsDecayField (profSlice W T t μ) :=
    dilateDecay (hSD W q C hW _) (div_pos hμ (sub_pos.mpr htT))
  have hcont := profileContinuous hDA hDC hSG hSD hEN hEL hW (n * (P / k)) (MildFramework.stepLength P k)
    (by show 1 - Real.exp (-(P / k)) < 1; linarith)
  have hc' : Continuous (fun t : Icc (0 : ℝ) (MildFramework.stepLength P k) =>
      F.selfSimilar (fun s => Freq.embedX (W s)) (n * (P / k)) t) := by
    simp only [MildFramework.selfSimilar, hF]
    exact hcont
  have hsim : similarityTime T t = n * (P / k) - Real.log (1 - s) := by
    unfold similarityTime
    rw [hTt]
    have : μ * (1 - s) / T = lam ^ n * (1 - s) := by
      rw [hμdef, stepScale, hlam]
      field_simp
    rw [this, Real.log_mul (pow_ne_zero _ hl'.ne') h1s.ne', Real.log_pow, hlam, Real.log_exp]
    ring
  have hratio : μ / (T - t) = (1 - (s : ℝ))⁻¹ := by
    rw [hTt]
    field_simp
  have hpp : (F.profilePiece (fun s => Freq.embedX (W s)) P k n) s = Freq.embedX (profSlice W T t μ) := by
    unfold MildFramework.profilePiece toPiece
    rw [dif_pos hc']
    show F.selfSimilar (fun s => Freq.embedX (W s)) (n * (P / k)) s = _
    simp only [MildFramework.selfSimilar, hF]
    rw [hED _ _ (inv_pos.mpr h1s) (hSD W q C hW _)]
    unfold profSlice
    rw [hratio, hsim]
  have hε' : ‖Freq.embedX (profSlice W T t μ) - ∑ l, A.weight n l s • Freq.embedX (A.field n l)‖ ≤ ε := by
    exact r3_bound A _ n s (hAε n) hpp
  obtain ⟨hgrad, hmass⟩ := hcut μ T t hμ (hμT.trans_lt hTa) hT htT hlo hhi
  have hM2' : Real.sqrt (∫ y, ‖(∑ l, A.weight n l s • A.field n l) y‖ ^ 2) ≤ M2 := by
    refine (l2_sum_le Finset.univ (fun l => A.weight n l s)
      (fun l => memLp_of_ball (A.isTest n l).1.continuous (field_vanish A n l))).2.trans ?_
    have hterm : ∀ l : Fin A.terms, |A.weight n l s| * Real.sqrt (∫ y, ‖A.field n l y‖ ^ 2) ≤
        |Cb| * (Real.sqrt K * |Cb|) := by
      intro l
      have hw : |A.weight n l s| ≤ |Cb| := by
        rw [← Real.norm_eq_abs]
        exact (ContinuousMap.norm_coe_le_norm _ _).trans ((hCb n l).2.trans (le_abs_self _))
      have hint : ∫ y, ‖A.field n l y‖ ^ 2 ≤ K * Cb ^ 2 := by
        refine (hK _ (A.isTest n l) (A.support n l)).trans ?_
        rw [← hEN _ (hφ l)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hCb n l).1 2) hK0
      have hsq : Real.sqrt (∫ y, ‖A.field n l y‖ ^ 2) ≤ Real.sqrt K * |Cb| := by
        rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hK0]
        exact Real.sqrt_le_sqrt hint
      exact mul_le_mul hw hsq (Real.sqrt_nonneg _) (abs_nonneg _)
    refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbd := pieceBound hTN hEN hEL (fun l => A.weight n l s) hsh hG hGB hφ hφB hPf hε' hgrad hmass hM2'
  rw [torus_diff A μ _ n s ((hL W q C T _ hW hT hT1 hl hl1 n).1 s), ← hμdef, ← ht, hper,
    toV_transplant_sub hTS (fun l => A.weight n l s) hsh hG hGB hφ hφB]
  have hsη : Real.sqrt (δ ^ 2 / 16) = δ / 4 := by
    rw [show δ ^ 2 / 16 = (δ / 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsη] at hbd
  have hμm : μ * (16 * (M2 ^ 2 + 1)) < δ ^ 2 := (lt_div_iff₀ (by positivity)).mp (hμT.trans_lt hTm)
  have hfin : ‖μ ^ (1 / 4 : ℝ) • toV (transplantField μ (simField W T t μ - ∑ l, A.weight n l s • A.field n l))‖ ^ 2
      ≤ (ε + δ) ^ 2 := by
    nlinarith [mul_nonneg hε hδ.le, mul_nonneg hμ.le (sq_nonneg M2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hε hδ.le) two_ne_zero).mp hfin

end Breakdown.Periodic
