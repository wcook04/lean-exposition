import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.Cutoff

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def gradEnergy (f : Space → Space) : ℝ := ∫ y, ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2

def cutAt (W : ℝ → Space → Space) (T t μ : ℝ) (y : Space) : Space :=
  Real.sqrt μ • approxField W T t (center + Real.sqrt μ • y)

namespace ApproxSizes.Internal

variable {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t μ : ℝ}

theorem slice_contDiff (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (ht : t < T) : ContDiff ℝ ∞ (approxField W T t) := by
  have h := (hA W q C T hW hT).1
  rw [contDiff_iff_contDiffAt]
  intro x
  have hm : ((t, x) : ℝ × Space) ∈ Iio T ×ˢ (univ : Set Space) := ⟨ht, trivial⟩
  have h1 := h.contDiffAt ((isOpen_Iio.prod isOpen_univ).mem_nhds hm)
  have h2 : ContDiffAt ℝ ∞ (fun y : Space => ((t, y) : ℝ × Space)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h1.comp x h2

theorem cutAt_contDiff (hf : ContDiff ℝ ∞ (approxField W T t)) (μ : ℝ) :
    ContDiff ℝ ∞ (cutAt W T t μ) :=
  (hf.comp (contDiff_const.add (contDiff_id.const_smul _))).const_smul _

theorem fderiv_cutAt_apply (hf : Differentiable ℝ (approxField W T t)) (μ : ℝ) (y v : Space) :
    fderiv ℝ (cutAt W T t μ) y v =
      (Real.sqrt μ * Real.sqrt μ) • fderiv ℝ (approxField W T t) (center + Real.sqrt μ • y) v := by
  have h1 : HasFDerivAt (fun y : Space => center + Real.sqrt μ • y)
      (Real.sqrt μ • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul (Real.sqrt μ)).const_add center
  have h2 : HasFDerivAt (cutAt W T t μ) (Real.sqrt μ •
      ((fderiv ℝ (approxField W T t) (center + Real.sqrt μ • y)).comp
        (Real.sqrt μ • ContinuousLinearMap.id ℝ Space))) y :=
    ((hf _).hasFDerivAt.comp y h1).const_smul (Real.sqrt μ)
  rw [h2.fderiv]
  simp [smul_smul]

theorem cutAt_div (hf : Differentiable ℝ (approxField W T t))
    (hdiv : ∀ x, divergenceAt (approxField W T t) x = 0) (μ : ℝ) (y : Space) :
    divergenceAt (cutAt W T t μ) y = 0 := by
  have h := hdiv (center + Real.sqrt μ • y)
  simp only [divergenceAt] at h ⊢
  simp only [fderiv_cutAt_apply hf, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h, mul_zero]

theorem cutAt_tsupport (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (ht : t < T) (hμ : 0 < μ) :
    tsupport (cutAt W T t μ) ⊆ Metric.closedBall 0 (1 / (8 * Real.sqrt μ)) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  rw [Function.mem_support] at hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push Not at hlt
  apply hy
  have hs := Real.sqrt_pos.2 hμ
  have hd : centralRadius / 2 ≤ dist (center + Real.sqrt μ • y) center := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs, centralRadius]
    rw [div_lt_iff₀ (by positivity)] at hlt
    nlinarith
  simp [cutAt, (((hA W q C T hW hT).2.2 t ht _).2.1 hd).1]

theorem transplant_cutAt (hμ : 0 < μ) : transplantField μ (cutAt W T t μ) = approxPeriodic W T t := by
  funext x
  have hs : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  simp only [transplantField, simCoord, cutAt, approxPeriodic, smul_smul, inv_mul_cancel₀ hs,
    mul_inv_cancel₀ hs, one_smul, add_sub_cancel]

theorem fderiv_dil_apply {f : Space → Space} (hf : Differentiable ℝ f) (r : ℝ) (y v : Space) :
    fderiv ℝ (fun y => r • f (r • y)) y v = (r * r) • fderiv ℝ f (r • y) v := by
  have h1 : HasFDerivAt (fun y : Space => r • y) (r • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id (𝕜 := ℝ) y).const_smul r
  have h2 : HasFDerivAt (fun y => r • f (r • y))
      (r • ((fderiv ℝ f (r • y)).comp (r • ContinuousLinearMap.id ℝ Space))) y :=
    ((hf _).hasFDerivAt.comp y h1).const_smul r
  rw [h2.fderiv]
  simp [smul_smul]

theorem gradEnergy_dil {f : Space → Space} (hf : Differentiable ℝ f) {r : ℝ} (hr : 0 < r) :
    gradEnergy (fun y => r • f (r • y)) = r * gradEnergy f := by
  unfold gradEnergy
  have e : ∀ y, ∑ i : Fin 3, ‖fderiv ℝ (fun y => r • f (r • y)) y (unitVector i)‖ ^ 2 =
      r ^ 4 * ∑ i : Fin 3, ‖fderiv ℝ f (r • y) (unitVector i)‖ ^ 2 := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_dil_apply hf, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hr hr)]
    ring
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2) r (hR := hr.le),
    finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

theorem mass_dil (f : Space → Space) {r : ℝ} (hr : 0 < r) :
    ∫ y, ‖r • f (r • y)‖ ^ 2 = r⁻¹ * ∫ y, ‖f y‖ ^ 2 := by
  have e : ∀ y, ‖r • f (r • y)‖ ^ 2 = r ^ 2 * ‖f (r • y)‖ ^ 2 := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    ring
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume (fun y => ‖f y‖ ^ 2) r
    (hR := hr.le), finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

theorem cutAt_dil {ℓ : ℝ} (hℓ : 0 < ℓ) :
    cutAt W T t μ = fun y => (Real.sqrt μ / Real.sqrt ℓ) •
      cutAt W T t ℓ ((Real.sqrt μ / Real.sqrt ℓ) • y) := by
  funext y
  have hs : Real.sqrt ℓ ≠ 0 := (Real.sqrt_pos.2 hℓ).ne'
  simp only [cutAt, smul_smul]
  rw [div_mul_cancel₀ _ hs, mul_div_cancel₀ _ hs]

theorem div_sub {f g : Space → Space} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdf : ∀ y, divergenceAt f y = 0) (hdg : ∀ y, divergenceAt g y = 0) (y : Space) :
    divergenceAt (f - g) y = 0 := by
  have h : HasFDerivAt (f - g) (fderiv ℝ f y - fderiv ℝ g y) y :=
    (hf y).hasFDerivAt.sub (hg y).hasFDerivAt
  have h1 := hdf y
  have h2 := hdg y
  simp only [divergenceAt] at h1 h2 ⊢
  rw [h.fderiv]
  simp only [sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib, h1, h2, sub_zero]

theorem decay_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f - g) := by
  obtain ⟨hf1, hf2, Cf, hCf⟩ := hf
  obtain ⟨hg1, hg2, Cg, hCg⟩ := hg
  have df : Differentiable ℝ f := hf1.differentiable (by simp)
  have dg : Differentiable ℝ g := hg1.differentiable (by simp)
  refine ⟨hf1.sub hg1, div_sub df dg hf2 hg2, Cf + Cg, fun y => ⟨?_, ?_⟩⟩
  · calc ‖(f - g) y‖ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ Cf / (1 + ‖y‖) + Cg / (1 + ‖y‖) := add_le_add (hCf y).1 (hCg y).1
      _ = (Cf + Cg) / (1 + ‖y‖) := by rw [add_div]
  · have h : HasFDerivAt (f - g) (fderiv ℝ f y - fderiv ℝ g y) y :=
      (df y).hasFDerivAt.sub (dg y).hasFDerivAt
    rw [h.fderiv]
    calc ‖fderiv ℝ f y - fderiv ℝ g y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_sub_le _ _
      _ ≤ Cf / (1 + ‖y‖) ^ 2 + Cg / (1 + ‖y‖) ^ 2 := add_le_add (hCf y).2 (hCg y).2
      _ = (Cf + Cg) / (1 + ‖y‖) ^ 2 := by rw [add_div]

theorem decay_of_support {f : Space → Space} {R : ℝ} (hf : ContDiff ℝ ∞ f)
    (hdiv : ∀ y, divergenceAt f y = 0) (hR : 0 ≤ R) (hs : tsupport f ⊆ Metric.closedBall 0 R) :
    IsDecayField f := by
  have hc : HasCompactSupport f :=
    (isCompact_closedBall (0 : Space) R).of_isClosed_subset (isClosed_tsupport f) hs
  obtain ⟨A, hA⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (hf.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  refine ⟨hf, hdiv, (|A| + |B|) * (1 + R) ^ 2, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · have hy' : ‖y‖ ≤ R := by simpa using hs hy
    have h1 : 0 < 1 + ‖y‖ := by positivity
    have h2 : 1 + ‖y‖ ≤ 1 + R := by linarith
    have hA' := abs_nonneg A
    have hB' := abs_nonneg B
    constructor
    · rw [le_div_iff₀ h1]
      calc ‖f y‖ * (1 + ‖y‖) ≤ |A| * (1 + R) :=
            mul_le_mul ((hA y).trans (le_abs_self A)) h2 h1.le hA'
        _ ≤ (|A| + |B|) * (1 + R) ^ 2 := by
          nlinarith [mul_nonneg (mul_nonneg hA' (by linarith : (0 : ℝ) ≤ 1 + R)) hR,
            mul_nonneg hB' (sq_nonneg (1 + R))]
    · rw [le_div_iff₀ (by positivity)]
      calc ‖fderiv ℝ f y‖ * (1 + ‖y‖) ^ 2 ≤ |B| * (1 + R) ^ 2 :=
            mul_le_mul ((hB y).trans (le_abs_self B)) (pow_le_pow_left₀ h1.le h2 2)
              (by positivity) hB'
        _ ≤ (|A| + |B|) * (1 + R) ^ 2 := by nlinarith [mul_nonneg hA' (sq_nonneg (1 + R))]
  · have e1 : f y = 0 := image_eq_zero_of_notMem_tsupport hy
    have e2 : fderiv ℝ f y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset (𝕜 := ℝ) h))
    rw [e1, e2, norm_zero, norm_zero]
    exact ⟨by positivity, by positivity⟩

theorem slice_decay (hW : IsSimilarityProfile W q C) (s : ℝ) : IsDecayField (W s) := by
  refine ⟨hW.smooth.comp (contDiff_const.prodMk contDiff_id), hW.div s, C, fun y => ⟨?_, ?_⟩⟩
  · have h := hW.decay s y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero] using h
  · have h := hW.decay s y 1 (by norm_num)
    simpa [norm_iteratedFDeriv_one] using h

theorem gradEnergy_slice_bound (hW : IsSimilarityProfile W q C) : ∃ B : ℝ, ∀ s, gradEnergy (W s) ≤ B := by
  refine ⟨∫ y : Space, 3 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)), fun s => ?_⟩
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  apply integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) (hint.const_mul _)
  refine Eventually.of_forall fun y => ?_
  have h := hW.decay s y 1 (by norm_num)
  rw [norm_iteratedFDeriv_one] at h
  have h1 : 0 < 1 + ‖y‖ := by positivity
  have e : (1 + ‖y‖) ^ (-(4 : ℝ)) = 1 / ((1 + ‖y‖) ^ (1 + 1)) ^ 2 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1.le, Real.rpow_natCast]
    ring
  have hi : ∀ i : Fin 3, ‖fderiv ℝ (W s) y (unitVector i)‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ (1 + 1)) ^ 2 := by
    intro i
    have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
    have := (fderiv ℝ (W s) y).le_opNorm (unitVector i)
    rw [hu, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) (this.trans h) 2
  calc ∑ i : Fin 3, ‖fderiv ℝ (W s) y (unitVector i)‖ ^ 2
      ≤ ∑ _i : Fin 3, (C / (1 + ‖y‖) ^ (1 + 1)) ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
      rw [e]
      simp
      field_simp

theorem norm_sq_piece (hN : TransplantNorm) (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C)
    (hT : 0 < T) (ht : t < T) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ‖(μ ^ (1 / 4 : ℝ)) • toV (approxPeriodic W T t)‖ ^ 2 =
      gradEnergy (cutAt W T t μ) + μ * ∫ y, ‖cutAt W T t μ y‖ ^ 2 := by
  have hf := slice_contDiff hA hW hT ht
  have hs := Real.sqrt_pos.2 hμ
  have hs' := hs.ne'
  rw [← transplant_cutAt hμ]
  exact hN _ μ (1 / (8 * Real.sqrt μ)) (cutAt_contDiff hf μ)
    (cutAt_div (hf.differentiable (by simp)) (fun x => ((hA W q C T hW hT).2.2 t ht x).1) μ)
    ⟨hμ, hμ1, by positivity, le_of_eq (by field_simp)⟩ (cutAt_tsupport hA hW hT ht hμ)

theorem cutAt_decay (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (ht : t < T) (hμ : 0 < μ) : IsDecayField (cutAt W T t μ) := by
  have hf := slice_contDiff hA hW hT ht
  have hs := Real.sqrt_pos.2 hμ
  exact decay_of_support (cutAt_contDiff hf μ)
    (cutAt_div (hf.differentiable (by simp)) (fun x => ((hA W q C T hW hT).2.2 t ht x).1) μ)
    (by positivity) (cutAt_tsupport hA hW hT ht hμ)

theorem norm_embed (hE : Freq.EmbedNorm) {f : Space → Space} (hf : IsDecayField f) :
    ‖Freq.embedX f‖ = Real.sqrt (gradEnergy f) := by
  rw [gradEnergy, ← hE f hf, Real.sqrt_sq (norm_nonneg _)]

theorem norm_embed_sub (hE : Freq.EmbedNorm) (hEL : Freq.EmbedLinear) {f g : Space → Space}
    (hf : IsDecayField f) (hg : IsDecayField g) :
    ‖Freq.embedX f - Freq.embedX g‖ = Real.sqrt (gradEnergy (f - g)) := by
  rw [← hEL.2.1 f g hf hg, norm_embed hE (decay_sub hf hg)]

theorem piece_sq (hN : TransplantNorm) (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C)
    (hT : 0 < T) (ht : t < T) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ‖(μ ^ (1 / 4 : ℝ)) • toV (approxPeriodic W T t)‖ ^ 2 =
      (Real.sqrt μ / Real.sqrt (T - t)) * gradEnergy (cutAt W T t (T - t)) +
        μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2) := by
  have hℓ : 0 < T - t := by linarith
  have hr : 0 < Real.sqrt μ / Real.sqrt (T - t) := div_pos (Real.sqrt_pos.2 hμ) (Real.sqrt_pos.2 hℓ)
  have hd : Differentiable ℝ (cutAt W T t (T - t)) :=
    (cutAt_contDiff (slice_contDiff hA hW hT ht) _).differentiable (by simp)
  rw [norm_sq_piece hN hA hW hT ht hμ hμ1, cutAt_dil (μ := μ) hℓ, gradEnergy_dil hd hr,
    mass_dil _ hr]

theorem embed_cut_bounds (hE : Freq.EmbedNorm) (hEL : Freq.EmbedLinear) (hA : ApproxFieldProperties)
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T) {ε : ℝ}
    (hε : gradEnergy (W (similarityTime T t) - cutAt W T t (T - t)) ≤ ε) :
    ‖Freq.embedX (W (similarityTime T t)) - Freq.embedX (cutAt W T t (T - t))‖ ≤ Real.sqrt ε ∧
    gradEnergy (cutAt W T t (T - t)) = ‖Freq.embedX (cutAt W T t (T - t))‖ ^ 2 := by
  have hℓ : 0 < T - t := by linarith
  have hd := cutAt_decay hA hW hT ht hℓ
  refine ⟨?_, ?_⟩
  · rw [norm_embed_sub hE hEL (slice_decay hW _) hd]
    exact Real.sqrt_le_sqrt hε
  · rw [hE _ hd]
    rfl

theorem sq_norm_sub_le (a b : Space) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_sub_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a - b), norm_nonneg a, norm_nonneg b]

theorem mass_arith {T u m K M δ : ℝ} (hupos : 0 < u) (hTu : u * u = T) (hu1 : u ≤ 1)
    (hM : M ≤ 2 * m + 2 * (K / u)) (huδ : u ≤ (δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) :
    T * M ≤ (δ / 2) ^ 2 := by
  have hLpos : 0 < 2 * |m| + 2 * |K| + 1 := by positivity
  have hT : 0 ≤ T := by rw [← hTu]; positivity
  have e : T * (2 * m + 2 * (K / u)) = 2 * (u * u) * m + 2 * K * u := by
    rw [← hTu]
    field_simp
  have hm1 : u * u * m ≤ u * |m| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self m) (mul_nonneg hupos.le hupos.le)
    have h2 := mul_le_mul_of_nonneg_right hu1 (abs_nonneg m)
    nlinarith [abs_nonneg m]
  have hK1 : K * u ≤ |K| * u := mul_le_mul_of_nonneg_right (le_abs_self K) hupos.le
  calc T * M ≤ T * (2 * m + 2 * (K / u)) := mul_le_mul_of_nonneg_left hM hT
    _ = 2 * (u * u) * m + 2 * K * u := e
    _ ≤ (2 * |m| + 2 * |K| + 1) * u := by linarith [hupos.le]
    _ ≤ (2 * |m| + 2 * |K| + 1) * ((δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) :=
        mul_le_mul_of_nonneg_left huδ hLpos.le
    _ = (δ / 2) ^ 2 := by field_simp

theorem final_arith {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    (A + δ / 2) ^ 2 + (δ / 2) ^ 2 ≤ (A + δ) ^ 2 := by
  nlinarith


theorem cross_smul_smul (a b : ℝ) (u v : Space) : cross (a • u) (b • v) = (a * b) • cross u v := by
  ext i
  fin_cases i <;> simp [cross, crossProduct, WithLp.ofLp_smul] <;> ring

theorem cutAt_formula {W : ℝ → Space → Space} {T t : ℝ} (ht : t < T) (y : Space) :
    cutAt W T t (T - t) y = centralCut (center + Real.sqrt (T - t) • y) • W (similarityTime T t) y +
      Real.sqrt (T - t) • cross (gradientAt centralCut (center + Real.sqrt (T - t) • y))
        (∫ s in (0 : ℝ)..1, s • cross (W (similarityTime T t) (s • y)) y) := by
  have hℓ : 0 < T - t := by linarith
  have hs : Real.sqrt (T - t) ≠ 0 := (Real.sqrt_pos.2 hℓ).ne'
  have e : (T - t) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (T - t))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hℓ.le]
  have hint : ∀ s : ℝ, s • cross ((T - t) ^ (-(1 / 2 : ℝ)) • W (similarityTime T t)
      ((T - t) ^ (-(1 / 2 : ℝ)) • (center + s • (center + Real.sqrt (T - t) • y - center) - center)))
      (center + Real.sqrt (T - t) • y - center) = s • cross (W (similarityTime T t) (s • y)) y := by
    intro s
    rw [e, add_sub_cancel_left, add_sub_cancel_left, smul_smul, smul_smul,
      show (Real.sqrt (T - t))⁻¹ * s * Real.sqrt (T - t) = s by field_simp, cross_smul_smul,
      inv_mul_cancel₀ hs, one_smul]
  simp only [cutAt, approxField, cutoffField, homotopyPotential, selfSimilar]
  simp_rw [hint]
  rw [e, add_sub_cancel_left, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, smul_add,
    smul_smul, show Real.sqrt (T - t) * (centralCut (center + Real.sqrt (T - t) • y) *
      (Real.sqrt (T - t))⁻¹) = centralCut (center + Real.sqrt (T - t) • y) by field_simp]

theorem norm_cross_le (a b : Space) : ‖cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have ha : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [Fin.sum_univ_three]
  have hb : ‖b‖ ^ 2 = b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [Fin.sum_univ_three]
  have hc : ‖cross a b‖ ^ 2 = (a 1 * b 2 - a 2 * b 1) ^ 2 + (a 2 * b 0 - a 0 * b 2) ^ 2 +
      (a 0 * b 1 - a 1 * b 0) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_three, cross, crossProduct]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, hc, ha, hb]
  nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]

theorem profile_const_nonneg {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) : 0 ≤ C := by
  have h := hW.decay 0 0 0 (by norm_num)
  have h' : ‖W 0 0‖ ≤ C := by simpa using h
  exact (norm_nonneg _).trans h'

theorem norm_potential_le {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) (σ : ℝ) (y : Space) :
    ‖∫ s in (0 : ℝ)..1, s • cross (W σ (s • y)) y‖ ≤ C := by
  have hC := profile_const_nonneg hW
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := C)
    (f := fun s => s • cross (W σ (s • y)) y) ?_
  · simpa using h
  intro s hs
  rw [Set.uIoc_of_le zero_le_one] at hs
  have hs0 : 0 ≤ s := hs.1.le
  have hd := hW.decay σ (s • y) 0 (by norm_num)
  simp only [norm_iteratedFDeriv_zero, zero_add, pow_one] at hd
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at hd
  have h1 : 0 < 1 + s * ‖y‖ := by positivity
  rw [le_div_iff₀ h1] at hd
  calc ‖s • cross (W σ (s • y)) y‖ ≤ s * (‖W σ (s • y)‖ * ‖y‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        exact mul_le_mul_of_nonneg_left (norm_cross_le _ _) hs0
    _ ≤ C := by nlinarith [norm_nonneg (W σ (s • y)), norm_nonneg y]

theorem centralCut_bounds : ∃ G : ℝ, 0 ≤ G ∧ ∀ x, |centralCut x| ≤ 1 ∧ ‖gradientAt centralCut x‖ ≤ G := by
  have hc : ContDiff ℝ ∞ centralCut := centralBump.contDiff
  have hs : HasCompactSupport centralCut := centralBump.hasCompactSupport
  obtain ⟨B, hB⟩ := (hc.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hs.fderiv (𝕜 := ℝ))
  refine ⟨3 * |B|, by positivity, fun x => ⟨?_, ?_⟩⟩
  · rw [abs_le]
    have h0 : 0 ≤ centralCut x := centralBump.nonneg
    have h1 : centralCut x ≤ 1 := centralBump.le_one
    exact ⟨by linarith, h1⟩
  · unfold gradientAt
    calc ‖∑ i : Fin 3, fderiv ℝ centralCut x (unitVector i) • unitVector i‖
        ≤ ∑ i : Fin 3, ‖fderiv ℝ centralCut x (unitVector i) • unitVector i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, |B| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
          rw [norm_smul, hu, mul_one]
          have := (fderiv ℝ centralCut x).le_opNorm (unitVector i)
          rw [hu, mul_one] at this
          exact this.trans ((hB x).trans (le_abs_self B))
      _ = 3 * |B| := by simp

theorem cutAt_sq_le {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T) {G : ℝ}
    (hG : ∀ x, |centralCut x| ≤ 1 ∧ ‖gradientAt centralCut x‖ ≤ G) (y : Space) :
    ‖cutAt W T t (T - t) y‖ ^ 2 ≤ (Iic (1 / (8 * Real.sqrt (T - t)))).indicator
      (fun r : ℝ => 2 * (C / (1 + r)) ^ 2 + 2 * (T - t) * G ^ 2 * C ^ 2) ‖y‖ := by
  have hℓ : 0 < T - t := by linarith
  by_cases hy : ‖y‖ ≤ 1 / (8 * Real.sqrt (T - t))
  · rw [indicator_of_mem (show ‖y‖ ∈ Iic (1 / (8 * Real.sqrt (T - t))) from hy), cutAt_formula ht]
    have hC := profile_const_nonneg hW
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0).2
    have hd := hW.decay (similarityTime T t) y 0 (by norm_num)
    simp only [norm_iteratedFDeriv_zero, zero_add, pow_one] at hd
    have h1 : ‖centralCut (center + Real.sqrt (T - t) • y) • W (similarityTime T t) y‖ ≤
        C / (1 + ‖y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |centralCut (center + Real.sqrt (T - t) • y)| * ‖W (similarityTime T t) y‖
          ≤ 1 * (C / (1 + ‖y‖)) :=
            mul_le_mul (hG _).1 hd (norm_nonneg _) zero_le_one
        _ = C / (1 + ‖y‖) := one_mul _
    have h2 : ‖Real.sqrt (T - t) • cross (gradientAt centralCut (center + Real.sqrt (T - t) • y))
        (∫ s in (0 : ℝ)..1, s • cross (W (similarityTime T t) (s • y)) y)‖ ≤
        Real.sqrt (T - t) * (G * C) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine mul_le_mul_of_nonneg_left ((norm_cross_le _ _).trans ?_) (Real.sqrt_nonneg _)
      exact mul_le_mul (hG _).2 (norm_potential_le hW _ y) (norm_nonneg _) hG0
    have h3 := (norm_add_le _ _).trans (add_le_add h1 h2)
    have hsq : Real.sqrt (T - t) ^ 2 = T - t := Real.sq_sqrt hℓ.le
    have h4 : 0 ≤ C / (1 + ‖y‖) := by positivity
    have h5 : 0 ≤ Real.sqrt (T - t) * (G * C) := by positivity
    calc _ ≤ (C / (1 + ‖y‖) + Real.sqrt (T - t) * (G * C)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ ≤ 2 * (C / (1 + ‖y‖)) ^ 2 + 2 * (Real.sqrt (T - t) * (G * C)) ^ 2 := by
          nlinarith [sq_nonneg (C / (1 + ‖y‖) - Real.sqrt (T - t) * (G * C))]
      _ = 2 * (C / (1 + ‖y‖)) ^ 2 + 2 * (T - t) * G ^ 2 * C ^ 2 := by
          rw [mul_pow, hsq]
          ring
  · rw [indicator_of_notMem (show ‖y‖ ∉ Iic (1 / (8 * Real.sqrt (T - t))) from hy)]
    have h0 : cutAt W T t (T - t) y = 0 := by
      by_contra hne
      have := cutAt_tsupport hA hW hT ht hℓ (subset_tsupport _ hne)
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact hy this
    rw [h0, norm_zero]
    norm_num

theorem radial_bound {ρ a b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b) :
    Integrable (fun y : Space => (Iic ρ).indicator (fun r : ℝ => 2 * (a / (1 + r)) ^ 2 + b) ‖y‖) ∧
    ∫ y : Space, (Iic ρ).indicator (fun r : ℝ => 2 * (a / (1 + r)) ^ 2 + b) ‖y‖ ≤
      3 * volume.real (Metric.ball (0 : Space) 1) * ((2 * a ^ 2 + b * ρ ^ 2) * ρ) := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (Iic ρ).indicator (fun r : ℝ => 2 * (a / (1 + r)) ^ 2 + b) :=
    ⟨_, rfl⟩
  rw [← hg]
  have hgm : Measurable g := hg ▸ (Measurable.indicator (by fun_prop) measurableSet_Iic)
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖r ^ 2 * g r‖ ≤
      (Ioc 0 ρ).indicator (fun _ => 2 * a ^ 2 + b * ρ ^ 2) r := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases hrρ : r ≤ ρ
    · rw [hg, indicator_of_mem (show r ∈ Iic ρ from hrρ),
        indicator_of_mem (show r ∈ Ioc 0 ρ from ⟨hr0, hrρ⟩)]
      have h1 : 0 < 1 + r := by linarith
      have h2 : r ^ 2 * (a / (1 + r)) ^ 2 ≤ a ^ 2 := by
        rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ 1 + 2 * r)]
      have h3 : r ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr0.le hrρ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h3 hb]
    · rw [hg, indicator_of_notMem (show r ∉ Iic ρ from hrρ),
        indicator_of_notMem (show r ∉ Ioc 0 ρ from fun h => hrρ h.2)]
      simp
  have hind : Integrable ((Ioc 0 ρ).indicator (fun _ : ℝ => 2 * a ^ 2 + b * ρ ^ 2)) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  have hI : IntegrableOn (fun r => r ^ 2 * g r) (Ioi 0) :=
    hind.integrableOn.mono' (((measurable_id.pow_const 2).mul hgm).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))
  have hform := integral_fun_norm_addHaar (volume : Measure Space) g
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul] at hform
  refine ⟨?_, ?_⟩
  · rw [integrable_fun_norm_addHaar (volume : Measure Space)]
    simpa [finrank_euclideanSpace_fin] using hI
  · rw [hform]
    have hV : 0 ≤ volume.real (Metric.ball (0 : Space) 1) := measureReal_nonneg
    have hle : ∫ r in Ioi (0 : ℝ), r ^ (3 - 1) * g r ≤ (2 * a ^ 2 + b * ρ ^ 2) * ρ := by
      calc ∫ r in Ioi (0 : ℝ), r ^ (3 - 1) * g r
          ≤ ∫ r in Ioi (0 : ℝ), (Ioc 0 ρ).indicator (fun _ => 2 * a ^ 2 + b * ρ ^ 2) r :=
            setIntegral_mono_on hI hind.integrableOn measurableSet_Ioi
              (fun r hr => (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hbound r hr))
        _ = ∫ r, (Ioc 0 ρ).indicator (fun _ => 2 * a ^ 2 + b * ρ ^ 2) r :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr =>
              indicator_of_notMem (fun h => hr h.1) _
        _ = (2 * a ^ 2 + b * ρ ^ 2) * ρ := by
            rw [integral_indicator_const _ measurableSet_Ioc]
            simp [hρ, mul_comm]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hle hV]

theorem massBound (hA : ApproxFieldProperties) (W : ℝ → Space → Space)
    (q : ℝ → Space → ℝ) (C : ℝ) (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, ∀ T t : ℝ, 0 < T → t < T → T - t ≤ 1 →
      ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2 ≤ K / Real.sqrt (T - t) := by
  obtain ⟨G, hG0, hG⟩ := centralCut_bounds
  refine ⟨3 * volume.real (Metric.ball (0 : Space) 1) * ((2 * C ^ 2 + G ^ 2 * C ^ 2 / 32) / 8),
    fun T t hT ht _ => ?_⟩
  have hℓ : 0 < T - t := by linarith
  have hs := Real.sqrt_pos.2 hℓ
  have hsq : Real.sqrt (T - t) ^ 2 = T - t := Real.sq_sqrt hℓ.le
  obtain ⟨hint, hle⟩ := radial_bound (ρ := 1 / (8 * Real.sqrt (T - t))) (a := C)
    (b := 2 * (T - t) * G ^ 2 * C ^ 2) (by positivity) (by positivity)
  calc ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2
      ≤ ∫ y : Space, (Iic (1 / (8 * Real.sqrt (T - t)))).indicator
          (fun r : ℝ => 2 * (C / (1 + r)) ^ 2 + 2 * (T - t) * G ^ 2 * C ^ 2) ‖y‖ :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) hint
          (Eventually.of_forall fun y => cutAt_sq_le hA hW hT ht hG y)
    _ ≤ _ := hle
    _ = _ := by
        field_simp
        rw [hsq]
        ring


theorem potential_arith {s ρ C a b : ℝ} (hs0 : 0 ≤ s) (hρ : 0 < ρ) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (ha : a ≤ C / (1 + s * ρ)) (hb : b ≤ C / (1 + s * ρ) ^ 2) :
    s * (a + b * s * ρ) ≤ 2 * C / ρ := by
  have h1 : 0 < 1 + s * ρ := by positivity
  have hsρ : 0 ≤ s * ρ := by positivity
  rw [le_div_iff₀ h1] at ha
  rw [le_div_iff₀ (by positivity)] at hb
  rw [le_div_iff₀ hρ]
  nlinarith [mul_nonneg hb0 hsρ]

theorem potential_deriv_bound (hW : IsSimilarityProfile W q C) (σ : ℝ) {y v : Space} (hy : 0 < ‖y‖)
    (hv : ‖v‖ ≤ 1) :
    ‖(∫ s in (0 : ℝ)..1, Cutoff.Internal.partialSecond
      (Cutoff.Internal.potentialIntegrand 0 (W σ)) s y) v‖ ≤ 2 * C / ‖y‖ := by
  have hg : ContDiff ℝ ∞ (W σ) := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have h1 : ContDiff ℝ 1 (Cutoff.Internal.potentialIntegrand 0 (W σ)) :=
    (Cutoff.Internal.contDiff_potentialIntegrand hg).of_le (by simp)
  have hint : IntervalIntegrable (fun s => Cutoff.Internal.partialSecond
      (Cutoff.Internal.potentialIntegrand 0 (W σ)) s y) volume 0 1 :=
    ((Cutoff.Internal.continuous_partialSecond _ h1).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 2 * C / ‖y‖) (f := fun s => Cutoff.Internal.partialSecond
      (Cutoff.Internal.potentialIntegrand 0 (W σ)) s y v) ?_
  · simpa using h
  intro s hs
  rw [Set.uIoc_of_le zero_le_one] at hs
  have hs0 : 0 ≤ s := hs.1.le
  show ‖Cutoff.Internal.partialSecond (Cutoff.Internal.potentialIntegrand 0 (W σ)) s y v‖ ≤ _
  rw [Cutoff.Internal.partialSecond_potential_apply hg]
  simp only [zero_add, sub_zero]
  have hd0 := hW.decay σ (s • y) 0 (by norm_num)
  have hd1 := hW.decay σ (s • y) 1 (by norm_num)
  rw [norm_iteratedFDeriv_zero] at hd0
  rw [norm_iteratedFDeriv_one] at hd1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, zero_add, pow_one] at hd0
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at hd1
  have hA1 : ‖cross (W σ (s • y)) v‖ ≤ ‖W σ (s • y)‖ :=
    (norm_cross_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hv)
  have hsv : ‖s • v‖ ≤ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_of_le_one_right hs0 hv
  have hA2 : ‖cross (fderiv ℝ (W σ) (s • y) (s • v)) y‖ ≤ ‖fderiv ℝ (W σ) (s • y)‖ * s * ‖y‖ :=
    (norm_cross_le _ _).trans (mul_le_mul_of_nonneg_right
      (((fderiv ℝ (W σ) (s • y)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hsv (norm_nonneg _))) (norm_nonneg _))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hA1 hA2)) hs0).trans ?_
  exact potential_arith hs0 hy (norm_nonneg _) (norm_nonneg _) hd0 (by simpa using hd1)

theorem fderiv_diff_apply (hW : IsSimilarityProfile W q C) (ht : t < T) (y v : Space) :
    fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y v =
      fderiv ℝ (W (similarityTime T t)) y v -
        ((centralCut (center + Real.sqrt (T - t) • y) • fderiv ℝ (W (similarityTime T t)) y v +
          fderiv ℝ centralCut (center + Real.sqrt (T - t) • y) (Real.sqrt (T - t) • v) •
            W (similarityTime T t) y) +
        Real.sqrt (T - t) • (cross (gradientAt centralCut (center + Real.sqrt (T - t) • y))
          ((∫ s in (0 : ℝ)..1, Cutoff.Internal.partialSecond
            (Cutoff.Internal.potentialIntegrand 0 (W (similarityTime T t))) s y) v) +
          cross (fderiv ℝ (gradientAt centralCut) (center + Real.sqrt (T - t) • y)
            (Real.sqrt (T - t) • v)) (homotopyPotential 0 (W (similarityTime T t)) y))) := by
  have hg : ContDiff ℝ ∞ (W (similarityTime T t)) :=
    hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hgd : Differentiable ℝ (W (similarityTime T t)) := hg.differentiable (by simp)
  have hχ : ContDiff ℝ ∞ centralCut := centralBump.contDiff
  have hΓ : ContDiff ℝ ∞ (gradientAt centralCut) := Cutoff.Internal.contDiff_gradientAt hχ
  have h1 : ContDiff ℝ 1 (Cutoff.Internal.potentialIntegrand 0 (W (similarityTime T t))) :=
    (Cutoff.Internal.contDiff_potentialIntegrand hg).of_le (by simp)
  have hP : HasFDerivAt (homotopyPotential 0 (W (similarityTime T t)))
      (∫ s in (0 : ℝ)..1, Cutoff.Internal.partialSecond
        (Cutoff.Internal.potentialIntegrand 0 (W (similarityTime T t))) s y) y := by
    rw [Cutoff.Internal.homotopyPotential_eq]
    exact Cutoff.Internal.hasFDerivAt_integral_unit _ h1 y
  have hφ : HasFDerivAt (fun y : Space => center + Real.sqrt (T - t) • y)
      (Real.sqrt (T - t) • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul (Real.sqrt (T - t))).const_add center
  have hχc := ((hχ.differentiable (by simp)) (center + Real.sqrt (T - t) • y)).hasFDerivAt.comp y hφ
  have hΓc := ((hΓ.differentiable (by simp)) (center + Real.sqrt (T - t) • y)).hasFDerivAt.comp y hφ
  have hD : HasFDerivAt (fun z => W (similarityTime T t) z -
      (centralCut (center + Real.sqrt (T - t) • z) • W (similarityTime T t) z +
        Real.sqrt (T - t) • cross (gradientAt centralCut (center + Real.sqrt (T - t) • z))
          (homotopyPotential 0 (W (similarityTime T t)) z))) _ y :=
    (hgd y).hasFDerivAt.sub ((hχc.smul (hgd y).hasFDerivAt).add
      ((Cutoff.Internal.hasFDerivAt_cross hΓc hP).const_smul (Real.sqrt (T - t))))
  have he : W (similarityTime T t) - cutAt W T t (T - t) = fun z => W (similarityTime T t) z -
      (centralCut (center + Real.sqrt (T - t) • z) • W (similarityTime T t) z +
        Real.sqrt (T - t) • cross (gradientAt centralCut (center + Real.sqrt (T - t) • z))
          (homotopyPotential 0 (W (similarityTime T t)) z)) := by
    funext z
    rw [Pi.sub_apply, cutAt_formula ht]
    simp [homotopyPotential]
  rw [he, hD.fderiv]
  rfl

theorem norm_combo (g' gy X Y : Space) (χ a r : ℝ) :
    ‖g' - ((χ • g' + a • gy) + r • (X + Y))‖ ≤ |1 - χ| * ‖g'‖ + |a| * ‖gy‖ + |r| * (‖X‖ + ‖Y‖) := by
  have e : g' - ((χ • g' + a • gy) + r • (X + Y)) = (1 - χ) • g' - (a • gy + r • (X + Y)) := by
    module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := norm_add_le (a • gy) (r • (X + Y))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  have h2 := mul_le_mul_of_nonneg_left (norm_add_le X Y) (abs_nonneg r)
  linarith

theorem mid_arith {n e₁ n₁ e₂ n₂ x₁ x₂ r ρ C B₁ B₂ G : ℝ} (hr : 0 < r) (hρ : 1 / (16 * r) ≤ ρ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hn : n ≤ e₁ * n₁ + e₂ * n₂ + r * (x₁ + x₂))
    (he₁1 : e₁ ≤ 1) (hn₁0 : 0 ≤ n₁) (hn₁ : n₁ ≤ C / (1 + ρ) ^ 2) (he₂ : e₂ ≤ r * B₁)
    (hn₂0 : 0 ≤ n₂) (hn₂ : n₂ ≤ C / (1 + ρ)) (hx₁ : x₁ ≤ G * (2 * C / ρ)) (hx₂ : x₂ ≤ r * B₂ * C)
    (hB₁ : 0 ≤ B₁) :
    n ≤ C / (1 + ρ) ^ 2 + r ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C) := by
  have hq : 0 < 1 / (16 * r) := by positivity
  have hρ0 : 0 < ρ := hq.trans_le hρ
  have h16 : 1 ≤ 16 * r * ρ := by
    rw [div_le_iff₀ (by positivity)] at hρ
    linarith
  have k1 : C / (1 + ρ) ≤ 16 * r * C := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr.le hC) hρ0.le]
  have k2 : 2 * C / ρ ≤ 32 * r * C := by
    rw [div_le_iff₀ hρ0]
    nlinarith
  have t1 : e₁ * n₁ ≤ C / (1 + ρ) ^ 2 := by
    rcases le_or_gt 0 e₁ with h | h
    · exact (mul_le_of_le_one_left hn₁0 he₁1).trans hn₁
    · exact (mul_nonpos_of_nonpos_of_nonneg h.le hn₁0).trans (by positivity)
  have t2 : e₂ * n₂ ≤ (r * B₁) * (16 * r * C) := by
    rcases le_or_gt 0 e₂ with h | h
    · exact mul_le_mul he₂ (hn₂.trans k1) hn₂0 (by positivity)
    · exact (mul_nonpos_of_nonpos_of_nonneg h.le hn₂0).trans (by positivity)
  have t3 : x₁ ≤ G * (32 * r * C) := hx₁.trans (mul_le_mul_of_nonneg_left k2 hG)
  have t4 : r * (x₁ + x₂) ≤ r * (G * (32 * r * C) + r * B₂ * C) :=
    mul_le_mul_of_nonneg_left (add_le_add t3 hx₂) hr.le
  linarith

theorem fderiv_diff_inner (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (ht : t < T) {y : Space} (hy : ‖y‖ < 1 / (16 * Real.sqrt (T - t))) :
    fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y = 0 := by
  have hℓ : 0 < T - t := by linarith
  have hs := Real.sqrt_pos.2 hℓ
  have hz : ∀ z ∈ Metric.ball (0 : Space) (1 / (16 * Real.sqrt (T - t))),
      (W (similarityTime T t) - cutAt W T t (T - t)) z = (fun _ => (0 : Space)) z := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hd : dist (center + Real.sqrt (T - t) • z) center ≤ centralRadius / 4 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs, centralRadius]
      rw [lt_div_iff₀ (by positivity)] at hz
      nlinarith
    have h := ((hA W q C T hW hT).2.2 t ht _).2.2 hd
    have e : (T - t) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (T - t))⁻¹ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hℓ.le]
    rw [Pi.sub_apply, cutAt, h, selfSimilar, e, add_sub_cancel_left]
    simp only [smul_smul, mul_inv_cancel₀ hs.ne', inv_mul_cancel₀ hs.ne', one_smul, sub_self]
  have hev : (W (similarityTime T t) - cutAt W T t (T - t)) =ᶠ[𝓝 y] fun _ => (0 : Space) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds
      (by rwa [Metric.mem_ball, dist_zero_right])) hz
  rw [hev.fderiv_eq]
  simp

theorem fderiv_diff_outer (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (ht : t < T) {y : Space} (hy : 1 / (8 * Real.sqrt (T - t)) < ‖y‖) :
    fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y =
      fderiv ℝ (W (similarityTime T t)) y := by
  have hℓ : 0 < T - t := by linarith
  have hg : Differentiable ℝ (W (similarityTime T t)) :=
    (hW.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hc : Differentiable ℝ (cutAt W T t (T - t)) :=
    (cutAt_contDiff (slice_contDiff hA hW hT ht) _).differentiable (by simp)
  have hn : y ∉ tsupport (cutAt W T t (T - t)) := fun h => by
    have := cutAt_tsupport hA hW hT ht hℓ h
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have h0 : fderiv ℝ (cutAt W T t (T - t)) y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_fderiv_subset (𝕜 := ℝ) h))
  have h : HasFDerivAt (W (similarityTime T t) - cutAt W T t (T - t))
      (fderiv ℝ (W (similarityTime T t)) y - fderiv ℝ (cutAt W T t (T - t)) y) y :=
    (hg y).hasFDerivAt.sub (hc y).hasFDerivAt
  rw [h.fderiv, h0, sub_zero]

theorem fderiv_diff_mid (hW : IsSimilarityProfile W q C) (ht : t < T) {B₁ B₂ G : ℝ}
    (hB₁ : ∀ x ∈ Metric.closedBall center 1, ‖fderiv ℝ centralCut x‖ ≤ B₁)
    (hB₂ : ∀ x ∈ Metric.closedBall center 1, ‖fderiv ℝ (gradientAt centralCut) x‖ ≤ B₂)
    (hG : ∀ x, |centralCut x| ≤ 1 ∧ ‖gradientAt centralCut x‖ ≤ G) {y v : Space} (hv : ‖v‖ ≤ 1)
    (hy1 : 1 / (16 * Real.sqrt (T - t)) ≤ ‖y‖) (hy2 : ‖y‖ ≤ 1 / (8 * Real.sqrt (T - t))) :
    ‖fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y v‖ ≤
      C / (1 + ‖y‖) ^ 2 + Real.sqrt (T - t) ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C) := by
  have hℓ : 0 < T - t := by linarith
  have hs := Real.sqrt_pos.2 hℓ
  have hC := profile_const_nonneg hW
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0).2
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ center (Metric.mem_closedBall_self zero_le_one))
  have hy0 : 0 < ‖y‖ := (by positivity : (0 : ℝ) < 1 / (16 * Real.sqrt (T - t))).trans_le hy1
  have hx : center + Real.sqrt (T - t) • y ∈ Metric.closedBall center 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs]
    rw [le_div_iff₀ (by positivity)] at hy2
    nlinarith
  have hrv : ‖Real.sqrt (T - t) • v‖ ≤ Real.sqrt (T - t) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_of_le_one_right hs.le hv
  have hd0 := hW.decay (similarityTime T t) y 0 (by norm_num)
  have hd1 := hW.decay (similarityTime T t) y 1 (by norm_num)
  rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at hd0
  rw [norm_iteratedFDeriv_one] at hd1
  have hn₁ : ‖fderiv ℝ (W (similarityTime T t)) y v‖ ≤ C / (1 + ‖y‖) ^ 2 :=
    (((fderiv ℝ (W (similarityTime T t)) y).le_opNorm v).trans
      (mul_le_of_le_one_right (norm_nonneg _) hv)).trans (by simpa using hd1)
  have he₁ : |1 - centralCut (center + Real.sqrt (T - t) • y)| ≤ 1 := by
    have h0 : 0 ≤ centralCut (center + Real.sqrt (T - t) • y) := centralBump.nonneg
    have h1 : centralCut (center + Real.sqrt (T - t) • y) ≤ 1 := centralBump.le_one
    rw [abs_le]
    constructor <;> linarith
  have he₂ : |fderiv ℝ centralCut (center + Real.sqrt (T - t) • y) (Real.sqrt (T - t) • v)| ≤
      Real.sqrt (T - t) * B₁ := by
    rw [← Real.norm_eq_abs]
    calc _ ≤ ‖fderiv ℝ centralCut (center + Real.sqrt (T - t) • y)‖ * ‖Real.sqrt (T - t) • v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B₁ * Real.sqrt (T - t) := mul_le_mul (hB₁ _ hx) hrv (norm_nonneg _) hB₁0
      _ = _ := mul_comm _ _
  have hx₁ : ‖cross (gradientAt centralCut (center + Real.sqrt (T - t) • y))
      ((∫ s in (0 : ℝ)..1, Cutoff.Internal.partialSecond
        (Cutoff.Internal.potentialIntegrand 0 (W (similarityTime T t))) s y) v)‖ ≤
      G * (2 * C / ‖y‖) :=
    (norm_cross_le _ _).trans (mul_le_mul (hG _).2 (potential_deriv_bound hW _ hy0 hv)
      (norm_nonneg _) hG0)
  have hPy : ‖homotopyPotential 0 (W (similarityTime T t)) y‖ ≤ C := by
    have := norm_potential_le hW (similarityTime T t) y
    simpa [homotopyPotential] using this
  have hx₂ : ‖cross (fderiv ℝ (gradientAt centralCut) (center + Real.sqrt (T - t) • y)
      (Real.sqrt (T - t) • v)) (homotopyPotential 0 (W (similarityTime T t)) y)‖ ≤
      Real.sqrt (T - t) * B₂ * C := by
    have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ _ hx)
    refine (norm_cross_le _ _).trans (mul_le_mul ?_ hPy (norm_nonneg _) (by positivity))
    calc _ ≤ ‖fderiv ℝ (gradientAt centralCut) (center + Real.sqrt (T - t) • y)‖ *
          ‖Real.sqrt (T - t) • v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B₂ * Real.sqrt (T - t) := mul_le_mul (hB₂ _ hx) hrv (norm_nonneg _) hB₂0
      _ = _ := mul_comm _ _
  rw [fderiv_diff_apply hW ht]
  have hc := norm_combo (fderiv ℝ (W (similarityTime T t)) y v) (W (similarityTime T t) y)
    (cross (gradientAt centralCut (center + Real.sqrt (T - t) • y))
      ((∫ s in (0 : ℝ)..1, Cutoff.Internal.partialSecond
        (Cutoff.Internal.potentialIntegrand 0 (W (similarityTime T t))) s y) v))
    (cross (fderiv ℝ (gradientAt centralCut) (center + Real.sqrt (T - t) • y)
      (Real.sqrt (T - t) • v)) (homotopyPotential 0 (W (similarityTime T t)) y))
    (centralCut (center + Real.sqrt (T - t) • y))
    (fderiv ℝ centralCut (center + Real.sqrt (T - t) • y) (Real.sqrt (T - t) • v)) (Real.sqrt (T - t))
  rw [abs_of_pos hs] at hc
  exact mid_arith hs hy1 hC hG0 hc he₁ (norm_nonneg _) hn₁ he₂ (norm_nonneg _) hd0 hx₁ hx₂ hB₁0

theorem tail_arith {r ρ C : ℝ} (hr : 0 < r) (hρ : 1 / (16 * r) ≤ ρ) (hρ0 : 0 ≤ ρ) :
    6 * (C / (1 + ρ) ^ 2) ^ 2 ≤ 24 * C ^ 2 * Real.sqrt r * (1 + ρ) ^ (-(7 / 2 : ℝ)) := by
  have ha : 0 < 1 + ρ := by linarith
  have e1 : (1 + ρ) ^ (-(7 / 2 : ℝ)) = ((1 + ρ) ^ 4)⁻¹ * Real.sqrt (1 + ρ) := by
    rw [show (-(7 / 2 : ℝ)) = -((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add ha,
      Real.rpow_neg ha.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have e2 : (C / (1 + ρ) ^ 2) ^ 2 = C ^ 2 * ((1 + ρ) ^ 4)⁻¹ := by
    field_simp
  have h16 : 1 ≤ 16 * r * ρ := by
    rw [div_le_iff₀ (by positivity)] at hρ
    linarith
  have key : 1 ≤ 4 * (Real.sqrt r * Real.sqrt (1 + ρ)) := by
    rw [← Real.sqrt_mul hr.le]
    have : 1 / 4 ≤ Real.sqrt (r * (1 + ρ)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    linarith
  rw [e1, e2]
  have hX : 0 ≤ C ^ 2 * ((1 + ρ) ^ 4)⁻¹ := by positivity
  calc 6 * (C ^ 2 * ((1 + ρ) ^ 4)⁻¹) = 6 * (C ^ 2 * ((1 + ρ) ^ 4)⁻¹) * 1 := (mul_one _).symm
    _ ≤ 6 * (C ^ 2 * ((1 + ρ) ^ 4)⁻¹) * (4 * (Real.sqrt r * Real.sqrt (1 + ρ))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

theorem sq_three_le {n₀ n₁ n₂ A B : ℝ} (h0 : 0 ≤ n₀) (h1 : 0 ≤ n₁) (h2 : 0 ≤ n₂)
    (k0 : n₀ ≤ A + B) (k1 : n₁ ≤ A + B) (k2 : n₂ ≤ A + B) :
    n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 ≤ 6 * A ^ 2 + 6 * B ^ 2 := by
  have q0 := pow_le_pow_left₀ h0 k0 2
  have q1 := pow_le_pow_left₀ h1 k1 2
  have q2 := pow_le_pow_left₀ h2 k2 2
  nlinarith [sq_nonneg (A - B)]

theorem grad_sum_le (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (ht : t < T) {B₁ B₂ G : ℝ}
    (hB₁ : ∀ x ∈ Metric.closedBall center 1, ‖fderiv ℝ centralCut x‖ ≤ B₁)
    (hB₂ : ∀ x ∈ Metric.closedBall center 1, ‖fderiv ℝ (gradientAt centralCut) x‖ ≤ B₂)
    (hG : ∀ x, |centralCut x| ≤ 1 ∧ ‖gradientAt centralCut x‖ ≤ G) (y : Space) :
    ∑ i : Fin 3, ‖fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y (unitVector i)‖ ^ 2 ≤
      24 * C ^ 2 * Real.sqrt (Real.sqrt (T - t)) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) +
      (Iic (1 / (8 * Real.sqrt (T - t)))).indicator (fun ρ : ℝ => 2 * (0 / (1 + ρ)) ^ 2 +
        6 * (16 * B₁ * C + 32 * G * C + B₂ * C) ^ 2 * Real.sqrt (T - t) ^ 4) ‖y‖ := by
  have hℓ : 0 < T - t := by linarith
  have hs := Real.sqrt_pos.2 hℓ
  have hC := profile_const_nonneg hW
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0).2
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ center (Metric.mem_closedBall_self zero_le_one))
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ center (Metric.mem_closedBall_self zero_le_one))
  have hind : 0 ≤ (Iic (1 / (8 * Real.sqrt (T - t)))).indicator (fun ρ : ℝ => 2 * (0 / (1 + ρ)) ^ 2 +
      6 * (16 * B₁ * C + 32 * G * C + B₂ * C) ^ 2 * Real.sqrt (T - t) ^ 4) ‖y‖ :=
    indicator_nonneg (fun _ _ => by positivity) _
  have hu : ∀ i : Fin 3, ‖unitVector i‖ ≤ 1 := fun i => by simp [unitVector]
  rw [Fin.sum_univ_three]
  by_cases h1 : ‖y‖ < 1 / (16 * Real.sqrt (T - t))
  · rw [fderiv_diff_inner hA hW hT ht h1]
    simp only [show ∀ v : Space, (0 : Space →L[ℝ] Space) v = 0 from fun v => rfl, norm_zero]
    have : (0 : ℝ) ≤ 24 * C ^ 2 * Real.sqrt (Real.sqrt (T - t)) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) := by
      positivity
    rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 0 by norm_num]
    exact add_nonneg this hind
  push Not at h1
  have tail := tail_arith (C := C) hs h1 (norm_nonneg y)
  have hA0 : 0 ≤ C / (1 + ‖y‖) ^ 2 := by positivity
  by_cases h2 : ‖y‖ ≤ 1 / (8 * Real.sqrt (T - t))
  · rw [indicator_of_mem (show ‖y‖ ∈ Iic (1 / (8 * Real.sqrt (T - t))) from h2)]
    have hb := fun i => fderiv_diff_mid hW ht hB₁ hB₂ hG (hu i) h1 h2
    have hsq := sq_three_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hb 0) (hb 1) (hb 2)
    have e : 6 * (Real.sqrt (T - t) ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C)) ^ 2 =
        2 * (0 / (1 + ‖y‖)) ^ 2 + 6 * (16 * B₁ * C + 32 * G * C + B₂ * C) ^ 2 *
          Real.sqrt (T - t) ^ 4 := by ring
    linarith
  · push Not at h2
    rw [fderiv_diff_outer hA hW hT ht h2]
    have hd1 := hW.decay (similarityTime T t) y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at hd1
    have hb : ∀ i : Fin 3, ‖fderiv ℝ (W (similarityTime T t)) y (unitVector i)‖ ≤
        C / (1 + ‖y‖) ^ 2 + 0 := fun i =>
      (((fderiv ℝ (W (similarityTime T t)) y).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hu i))).trans (by simpa using hd1)
    have hsq := sq_three_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hb 0) (hb 1) (hb 2)
    linarith

theorem eps_arith {ℓ a b ε : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) (h1 : ℓ < 1)
    (h2 : ℓ < (ε / (a + b + 1)) ^ 4) : a * Real.sqrt (Real.sqrt ℓ) + b * Real.sqrt ℓ ≤ ε := by
  have hu0 : 0 ≤ Real.sqrt (Real.sqrt ℓ) := Real.sqrt_nonneg _
  have e1 : Real.sqrt (Real.sqrt ℓ) ^ 2 = Real.sqrt ℓ := Real.sq_sqrt (Real.sqrt_nonneg _)
  have e2 : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  have e4 : Real.sqrt (Real.sqrt ℓ) ^ 4 = ℓ := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, e1, e2]
  have hδ : 0 < ε / (a + b + 1) := by positivity
  have hu1 : Real.sqrt (Real.sqrt ℓ) < 1 := by
    rw [← pow_lt_pow_iff_left₀ hu0 zero_le_one (by norm_num : (4 : ℕ) ≠ 0), e4, one_pow]
    exact h1
  have huδ : Real.sqrt (Real.sqrt ℓ) < ε / (a + b + 1) := by
    rw [← pow_lt_pow_iff_left₀ hu0 hδ.le (by norm_num : (4 : ℕ) ≠ 0), e4]
    exact h2
  have hsq : Real.sqrt ℓ ≤ Real.sqrt (Real.sqrt ℓ) := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1.le)]
  have k : (a + b) * (ε / (a + b + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hb, mul_le_mul_of_nonneg_left huδ.le (add_nonneg ha hb)]

theorem gradient_close (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (ε : ℝ)
    (hε : 0 < ε) : ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ T t : ℝ, 0 < T → t < T → T - t < ℓ₀ →
      gradEnergy (W (similarityTime T t) - cutAt W T t (T - t)) ≤ ε := by
  obtain ⟨G, hG0, hG⟩ := centralCut_bounds
  have hχ : ContDiff ℝ ∞ centralCut := centralBump.contDiff
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall center 1).exists_bound_of_continuousOn
    (hχ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨B₂, hB₂⟩ := (isCompact_closedBall center 1).exists_bound_of_continuousOn
    ((Cutoff.Internal.contDiff_gradientAt hχ).continuous_fderiv (by simp)).continuousOn
  have hC := profile_const_nonneg hW
  obtain ⟨Mc, hMc⟩ : ∃ Mc, Mc = 16 * B₁ * C + 32 * G * C + B₂ * C := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ y : Space, (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) := ⟨_, rfl⟩
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hI0 : 0 ≤ I := hI ▸ integral_nonneg (fun y => by positivity)
  have hV : 0 ≤ volume.real (Metric.ball (0 : Space) 1) := measureReal_nonneg
  refine ⟨min 1 ((ε / (24 * C ^ 2 * I + 18 * volume.real (Metric.ball (0 : Space) 1) * Mc ^ 2 / 512
    + 1)) ^ 4), lt_min one_pos (by positivity), fun T t hT ht hℓ₀ => ?_⟩
  have hℓ : 0 < T - t := by linarith
  have hs := Real.sqrt_pos.2 hℓ
  obtain ⟨hrint, hrle⟩ := radial_bound (ρ := 1 / (8 * Real.sqrt (T - t))) (a := 0)
    (b := 6 * Mc ^ 2 * Real.sqrt (T - t) ^ 4) (by positivity) (by positivity)
  have hpt := fun y => grad_sum_le (q := q) hA hW hT ht hB₁ hB₂ hG y
  rw [← hMc] at hpt
  have hmono : gradEnergy (W (similarityTime T t) - cutAt W T t (T - t)) ≤
      ∫ y : Space, (24 * C ^ 2 * Real.sqrt (Real.sqrt (T - t)) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) +
        (Iic (1 / (8 * Real.sqrt (T - t)))).indicator (fun ρ : ℝ => 2 * (0 / (1 + ρ)) ^ 2 +
          6 * Mc ^ 2 * Real.sqrt (T - t) ^ 4) ‖y‖) :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
      ((hint.const_mul _).add hrint) (Eventually.of_forall hpt)
  rw [integral_add (hint.const_mul _) hrint, integral_const_mul, ← hI] at hmono
  have e : 3 * volume.real (Metric.ball (0 : Space) 1) * ((2 * 0 ^ 2 + 6 * Mc ^ 2 *
      Real.sqrt (T - t) ^ 4 * (1 / (8 * Real.sqrt (T - t))) ^ 2) * (1 / (8 * Real.sqrt (T - t)))) =
      18 * volume.real (Metric.ball (0 : Space) 1) * Mc ^ 2 / 512 * Real.sqrt (T - t) := by
    field_simp
    ring
  rw [e] at hrle
  have hfin := eps_arith hℓ (by positivity : 0 ≤ 24 * C ^ 2 * I)
    (by positivity : 0 ≤ 18 * volume.real (Metric.ball (0 : Space) 1) * Mc ^ 2 / 512) hε
    (hℓ₀.trans_le (min_le_left _ _)) (hℓ₀.trans_le (min_le_right _ _))
  nlinarith

end ApproxSizes.Internal

theorem cutoffGradientClose (hA : ApproxFieldProperties) (W : ℝ → Space → Space)
    (q : ℝ → Space → ℝ) (C : ℝ) (hW : IsSimilarityProfile W q C) (ε : ℝ) (hε : 0 < ε) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ T t : ℝ, 0 < T → t < T → T - t < ℓ₀ →
      gradEnergy (W (similarityTime T t) - cutAt W T t (T - t)) ≤ ε :=
  ApproxSizes.Internal.gradient_close hA hW ε hε

theorem cutoffMassBound (hA : ApproxFieldProperties) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (C : ℝ) (hW : IsSimilarityProfile W q C) : ∃ K : ℝ, ∀ T t : ℝ, 0 < T → t < T → T - t ≤ 1 →
      ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2 ≤ K / Real.sqrt (T - t) :=
  ApproxSizes.Internal.massBound hA W q C hW

open ApproxSizes.Internal in
theorem approxSizes (hN : TransplantNorm) (hA : ApproxFieldProperties) (hL : ApproxLinks)
    (hE : Freq.EmbedNorm) (hEL : Freq.EmbedLinear) : ApproxSizes := by
  intro W q C lam c hW hl hl1 hc hcW
  obtain ⟨K, hK⟩ := cutoffMassBound hA W q C hW
  obtain ⟨ℓ₀, hℓ₀, hℓ⟩ := cutoffGradientClose hA W q C hW ((c / 2) ^ 2) (by positivity)
  obtain ⟨B, hB⟩ := gradEnergy_slice_bound hW
  refine ⟨min ℓ₀ 1, Real.sqrt ((Real.sqrt lam)⁻¹ * (Real.sqrt (max B 0) + c / 2) ^ 2 + |K|),
    lt_min hℓ₀ one_pos, fun T hT hT0 n => ?_⟩
  have hT1 : T ≤ 1 := (hT0.trans_le (min_le_right _ _)).le
  have hTℓ : T < ℓ₀ := hT0.trans_le (min_le_left _ _)
  have key : ∀ s : Icc (0 : ℝ) (1 - lam), c / 2 ≤ ‖approxPiece W T lam n s‖ ∧
      ‖approxPiece W T lam n s‖ ≤
        Real.sqrt ((Real.sqrt lam)⁻¹ * (Real.sqrt (max B 0) + c / 2) ^ 2 + |K|) := by
    intro s
    obtain ⟨s, hs0, hs1⟩ := s
    rw [(hL W q C T lam hW hT hT1 hl hl1 n).1 ⟨s, hs0, hs1⟩]
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = stepScale T lam n := ⟨_, rfl⟩
    have hμ : 0 < μ := hμdef ▸ stepScale_pos hT hl n
    have hμ1 : μ ≤ 1 := hμdef ▸ stepScale_le_one hT1 hl hl1.le n
    have hμT : μ ≤ T := by
      rw [hμdef, stepScale]
      exact mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
    have hst : stepStart T lam n = T - μ := by rw [hμdef]; rfl
    simp only [← hμdef, hst]
    obtain ⟨t, htdef⟩ : ∃ t, t = T - μ + μ * s := ⟨_, rfl⟩
    rw [← htdef]
    have hℓe : T - t = μ * (1 - s) := by rw [htdef]; ring
    have hℓpos : 0 < T - t := by rw [hℓe]; exact mul_pos hμ (by linarith)
    have ht : t < T := by linarith
    have hℓμ : T - t ≤ μ := by rw [hℓe]; nlinarith
    have hlamℓ : μ * lam ≤ T - t := by rw [hℓe]; nlinarith
    have hℓ1 : T - t ≤ 1 := hℓμ.trans hμ1
    have hℓ0 : T - t < ℓ₀ := lt_of_le_of_lt (hℓμ.trans hμT) hTℓ
    obtain ⟨h1, h2⟩ := embed_cut_bounds hE hEL hA hW hT ht (hℓ T t hT ht hℓ0)
    rw [Real.sqrt_sq (by positivity)] at h1
    have hm := hK T t hT ht hℓ1
    have hm0 : 0 ≤ ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2 := integral_nonneg fun y => by positivity
    have hWc := hcW (similarityTime T t)
    have hWB : ‖Freq.embedX (W (similarityTime T t))‖ ≤ Real.sqrt (max B 0) := by
      rw [norm_embed hE (slice_decay hW _)]
      exact Real.sqrt_le_sqrt ((hB _).trans (le_max_left _ _))
    have htri := norm_sub_norm_le (Freq.embedX (W (similarityTime T t)))
      (Freq.embedX (cutAt W T t (T - t)))
    have htri' := norm_sub_norm_le (Freq.embedX (cutAt W T t (T - t)))
      (Freq.embedX (W (similarityTime T t)))
    rw [norm_sub_rev] at htri'
    set x := ‖Freq.embedX (cutAt W T t (T - t))‖ with hx
    set m := ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2 with hmdef
    have hsμ := Real.sqrt_pos.2 hμ
    have hsℓ := Real.sqrt_pos.2 hℓpos
    have hr1 : 1 ≤ Real.sqrt μ / Real.sqrt (T - t) := by
      rw [le_div_iff₀ hsℓ, one_mul]
      exact Real.sqrt_le_sqrt hℓμ
    have hr2 : Real.sqrt μ / Real.sqrt (T - t) ≤ (Real.sqrt lam)⁻¹ := by
      rw [div_le_iff₀ hsℓ, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.2 hl.le)]
      refine Real.sqrt_le_sqrt ?_
      rw [inv_mul_eq_div, le_div_iff₀ hl]
      exact hlamℓ
    have hmass : μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * m) ≤ |K| := by
      have hK0 : 0 ≤ K := by
        have := hm0.trans hm
        rwa [le_div_iff₀ hsℓ, zero_mul] at this
      have e : μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * (K / Real.sqrt (T - t))) =
          Real.sqrt μ * K := by
        have hμsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
        field_simp
        linear_combination (-K) * hμsq
      calc μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * m)
          ≤ μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * (K / Real.sqrt (T - t))) := by
            gcongr
        _ = Real.sqrt μ * K := e
        _ ≤ 1 * K := by
            gcongr
            rw [Real.sqrt_le_one]
            exact hμ1
        _ ≤ |K| := by rw [one_mul]; exact le_abs_self K
    have hpos : 0 ≤ μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * m) := by positivity
    have hsq := piece_sq hN hA hW hT ht hμ hμ1
    rw [h2] at hsq
    have hxlo : c / 2 ≤ x := by linarith
    have hxhi : x ≤ Real.sqrt (max B 0) + c / 2 := by linarith
    constructor
    · refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
      rw [hsq]
      have : (c / 2) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hxlo 2
      have := mul_le_mul_of_nonneg_right hr1 (sq_nonneg x)
      linarith
    · refine (Real.le_sqrt (norm_nonneg _) (by positivity)).2 ?_
      rw [hsq]
      have hx2 : x ^ 2 ≤ (Real.sqrt (max B 0) + c / 2) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hxhi 2
      have := mul_le_mul hr2 hx2 (sq_nonneg x) (inv_nonneg.2 (Real.sqrt_nonneg lam))
      linarith
  exact ⟨(ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2 fun s => (key s).2, fun s => (key s).1⟩

open ApproxSizes.Internal in
theorem datumClose (hN : TransplantNorm) (hS : TransplantSmooth) (hA : ApproxFieldProperties)
    (hL : ApproxLinks) (hE : Freq.EmbedNorm) (hEL : Freq.EmbedLinear) (hV : ToVAdd) :
    DatumClose := by
  intro W q C lam b δ ψ₀ hW hl hl1 hψ hsupp hb hδ
  obtain ⟨ℓ₀, hℓ₀, hℓ⟩ := cutoffGradientClose hA W q C hW ((δ / 2) ^ 2) (by positivity)
  obtain ⟨K, hK⟩ := cutoffMassBound hA W q C hW
  obtain ⟨m, hmdef⟩ : ∃ m, m = ∫ y, ‖ψ₀ y‖ ^ 2 := ⟨_, rfl⟩
  have hLpos : 0 < 2 * |m| + 2 * |K| + 1 := by positivity
  refine ⟨min (min ℓ₀ 1) (min (1 / (64 * b ^ 2)) (((δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) ^ 2)),
    by positivity, fun T hT hT0 => ?_⟩
  have hT1 : T ≤ 1 := (hT0.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hTℓ : T < ℓ₀ := hT0.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hTb : T ≤ 1 / (64 * b ^ 2) := (hT0.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hTδ : T ≤ ((δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) ^ 2 :=
    (hT0.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hv : extendPiece (approxPiece W T lam 0) 0 = T ^ (1 / 4 : ℝ) • toV (approxPeriodic W T 0) := by
    have h0 : (0 : ℝ) ≤ 1 - lam := by linarith
    rw [extendPiece, dif_pos h0, Set.IccExtend_left, (hL W q C T lam hW hT hT1 hl hl1 0).1]
    simp [stepScale, stepStart]
  rw [hv]
  obtain ⟨u, hu⟩ : ∃ u, u = Real.sqrt T := ⟨_, rfl⟩
  have hupos : 0 < u := hu ▸ Real.sqrt_pos.2 hT
  have hTu : u * u = T := by rw [hu]; exact Real.mul_self_sqrt hT.le
  have hu1 : u ≤ 1 := by rw [hu]; exact Real.sqrt_le_one.2 hT1
  obtain ⟨R, hR⟩ : ∃ R, R = 1 / (8 * Real.sqrt T) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR, ← hu]; positivity
  have hbR : b ≤ R := by
    rw [hR, ← hu, le_div_iff₀ (by positivity)]
    have h1 : u ≤ 1 / (8 * b) := by
      rw [hu]
      calc Real.sqrt T ≤ Real.sqrt ((1 / (8 * b)) ^ 2) :=
            Real.sqrt_le_sqrt (hTb.trans (le_of_eq (by ring)))
        _ = 1 / (8 * b) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hf := slice_contDiff hA hW hT hT
  obtain ⟨h, hh⟩ : ∃ h, h = cutAt W T 0 T := ⟨_, rfl⟩
  have hhs : ContDiff ℝ ∞ h := hh ▸ cutAt_contDiff hf T
  have hhd : ∀ y, divergenceAt h y = 0 := hh ▸ cutAt_div (hf.differentiable (by simp))
    (fun x => ((hA W q C T hW hT).2.2 0 hT x).1) T
  have hhsupp : tsupport h ⊆ Metric.closedBall 0 R := hR ▸ hh ▸ cutAt_tsupport hA hW hT hT hT
  have hψsupp : tsupport ψ₀ ⊆ Metric.closedBall 0 R :=
    hsupp.trans (Metric.closedBall_subset_closedBall hbR)
  obtain ⟨D, hD⟩ : ∃ D, D = ψ₀ - h := ⟨_, rfl⟩
  have hDs : ContDiff ℝ ∞ D := hD ▸ hψ.1.sub hhs
  have hDd : ∀ y, divergenceAt D y = 0 :=
    hD ▸ div_sub (hψ.1.differentiable (by simp)) (hhs.differentiable (by simp)) hψ.2.2 hhd
  have hDsupp : tsupport D ⊆ Metric.closedBall 0 R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Function.mem_support] at hy
    by_cases h1 : ψ₀ y = 0
    · have h2 : h y ≠ 0 := by
        intro h2
        apply hy
        rw [hD, Pi.sub_apply, h1, h2, sub_zero]
      exact hhsupp (subset_closure h2)
    · exact hψsupp (subset_closure h1)
  have hsh : IsShellScale T R := ⟨hT, hT1, hRpos, le_of_eq (by rw [hR]; field_simp)⟩
  obtain ⟨tD1, tD2, tD3, -⟩ := hS D T R hDs hDd hsh hDsupp
  obtain ⟨th1, th2, th3, -⟩ := hS h T R hhs hhd hsh hhsupp
  have hsplit : transplantField T ψ₀ = transplantField T D + transplantField T h := by
    funext x
    simp only [transplantField, hD, Pi.add_apply, Pi.sub_apply, smul_sub, sub_add_cancel]
  have hdiff : T ^ (1 / 4 : ℝ) • toV (transplantField T ψ₀) -
      T ^ (1 / 4 : ℝ) • toV (approxPeriodic W T 0) = T ^ (1 / 4 : ℝ) • toV (transplantField T D) := by
    rw [hsplit, hV _ _ tD1 th1 tD2 th2 tD3 th3, ← transplant_cutAt hT, ← hh, smul_add,
      add_sub_cancel_right]
  rw [hdiff]
  have hψdec : IsDecayField ψ₀ := decay_of_support hψ.1 hψ.2.2 hb.le hsupp
  have hhdec : IsDecayField h := hh ▸ cutAt_decay hA hW hT hT hT
  have hDdec : IsDecayField D := hD ▸ decay_sub hψdec hhdec
  have hn := hN D T R hDs hDd hsh hDsupp
  rw [← hE D hDdec, hD, hEL.2.1 ψ₀ h hψdec hhdec, ← hD] at hn
  have hc := (embed_cut_bounds hE hEL hA hW hT hT (hℓ T 0 hT hT (by rw [sub_zero]; exact hTℓ))).1
  have e1 : similarityTime T 0 = 0 := by simp [similarityTime, hT.ne']
  rw [e1, sub_zero, Real.sqrt_sq (by positivity), ← hh] at hc
  have hG : ‖Freq.embedX ψ₀ - Freq.embedX h‖ ≤ ‖Freq.embedX ψ₀ - Freq.embedX (W 0)‖ + δ / 2 :=
    (norm_sub_le_norm_sub_add_norm_sub _ (Freq.embedX (W 0)) _).trans (by linarith)
  have hmh := hK T 0 hT hT (by rw [sub_zero]; exact hT1)
  rw [sub_zero, ← hh, ← hu] at hmh
  have hcs : HasCompactSupport h :=
    (isCompact_closedBall (0 : Space) R).of_isClosed_subset (isClosed_tsupport h) hhsupp
  have hi1 : Integrable ((fun v : Space => ‖v‖ ^ 2) ∘ ψ₀) :=
    ((continuous_norm.pow 2).comp hψ.1.continuous).integrable_of_hasCompactSupport
      (hψ.2.1.comp_left (by simp))
  have hi2 : Integrable ((fun v : Space => ‖v‖ ^ 2) ∘ h) :=
    ((continuous_norm.pow 2).comp hhs.continuous).integrable_of_hasCompactSupport
      (hcs.comp_left (by simp))
  replace hi1 : Integrable (fun y => ‖ψ₀ y‖ ^ 2) := hi1
  replace hi2 : Integrable (fun y => ‖h y‖ ^ 2) := hi2
  have hM : ∫ y, ‖D y‖ ^ 2 ≤ 2 * m + 2 * (K / u) := by
    calc ∫ y, ‖D y‖ ^ 2 ≤ ∫ y, (2 * ‖ψ₀ y‖ ^ 2 + 2 * ‖h y‖ ^ 2) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
            ((hi1.const_mul 2).add (hi2.const_mul 2)) (Eventually.of_forall fun y => ?_)
          show ‖D y‖ ^ 2 ≤ 2 * ‖ψ₀ y‖ ^ 2 + 2 * ‖h y‖ ^ 2
          rw [hD, Pi.sub_apply]
          exact sq_norm_sub_le _ _
      _ = 2 * m + 2 * ∫ y, ‖h y‖ ^ 2 := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul, hmdef]
      _ ≤ 2 * m + 2 * (K / u) := by linarith
  have huδ : u ≤ (δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1) := by
    rw [hu]
    calc Real.sqrt T ≤ Real.sqrt (((δ / 2) ^ 2 / (2 * |m| + 2 * |K| + 1)) ^ 2) :=
          Real.sqrt_le_sqrt hTδ
      _ = _ := Real.sqrt_sq (by positivity)
  have hTM : T * ∫ y, ‖D y‖ ^ 2 ≤ (δ / 2) ^ 2 := mass_arith hupos hTu hu1 hM huδ
  have hA0 := norm_nonneg (Freq.embedX ψ₀ - Freq.embedX (W 0))
  have hG2 : ‖Freq.embedX ψ₀ - Freq.embedX h‖ ^ 2 ≤
      (‖Freq.embedX ψ₀ - Freq.embedX (W 0)‖ + δ / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hG 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  calc ‖T ^ (1 / 4 : ℝ) • toV (transplantField T D)‖ ^ 2
      = ‖Freq.embedX ψ₀ - Freq.embedX h‖ ^ 2 + T * ∫ y, ‖D y‖ ^ 2 := hn
    _ ≤ (‖Freq.embedX ψ₀ - Freq.embedX (W 0)‖ + δ / 2) ^ 2 + (δ / 2) ^ 2 := add_le_add hG2 hTM
    _ ≤ (‖Freq.embedX ψ₀ - Freq.embedX (W 0)‖ + δ) ^ 2 := final_arith hA0 hδ

end Breakdown.Periodic
