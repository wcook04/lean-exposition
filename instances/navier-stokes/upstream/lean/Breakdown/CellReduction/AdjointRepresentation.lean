import Breakdown.CellReduction.AdjointStatements
import Breakdown.CellReduction.AdjointRepresentationWindow
import Breakdown.CellReduction.AdjointRepresentationStrip
import Breakdown.CellReduction.AdjointRepresentationSlice

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal.Representation

open RepresentationParts

theorem one_le_smooth : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top

theorem sliceSpace_hasFDerivAt {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (s : ℝ) (y : Space) :
    HasFDerivAt (f s) ((fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space)) y := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => f z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y)) (s, y) :=
    (hf.differentiable one_ne_zero (s, y)).hasFDerivAt
  exact h1.comp y (hasFDerivAt_prodMk_right s y)

theorem slice_hasDerivAt {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (s : ℝ) (y : Space) :
    HasDerivAt (fun t => f t y) (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y) ((1 : ℝ), (0 : Space))) s := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => f z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y)) (s, y) :=
    (hf.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact h1.comp_hasDerivAt s h2

theorem slice_fderiv_eq {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (s : ℝ) (y : Space) :
    fderiv ℝ (f s) y = (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) :=
  (sliceSpace_hasFDerivAt hf s y).fderiv

theorem timeDerivative_eq_joint {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (s : ℝ) (y : Space) :
    timeDerivative f s y = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (s, y) ((1 : ℝ), (0 : Space)) :=
  (slice_hasDerivAt hf s y).deriv

theorem continuous_slice_fderiv {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) := by
  have h : (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) = fun z =>
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact slice_fderiv_eq hf z.1 z.2
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem continuous_timeDerivative {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => timeDerivative f z.1 z.2) := by
  have h : (fun z : ℝ × Space => timeDerivative f z.1 z.2) = fun z =>
      fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z ((1 : ℝ), (0 : Space)) := by
    funext z
    exact timeDerivative_eq_joint hf z.1 z.2
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_slice_fderiv_apply_self {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2 z.2) :=
  (continuous_slice_fderiv hf).clm_apply continuous_snd

theorem cut_contDiff {ζ : ℝ → Space → Space} (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => timeCutoff windowBump ζ z.1 z.2) :=
  ((windowBump_contDiff.of_le one_le_smooth).comp contDiff_fst).smul hζ

theorem windowBump_hasDerivAt (s : ℝ) : HasDerivAt windowBump (deriv windowBump s) s :=
  ((windowBump_contDiff.differentiable (by simp)) s).hasDerivAt

theorem stripCutoff_hasDerivAt (s : ℝ) : HasDerivAt stripCutoff (deriv stripCutoff s) s :=
  ((stripCutoff_contDiff.differentiable (by simp)) s).hasDerivAt

theorem timeDerivative_cut {ζ : ℝ → Space → Space}
    (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (s : ℝ) (y : Space) :
    timeDerivative (timeCutoff windowBump ζ) s y =
      deriv windowBump s • ζ s y + windowBump s • timeDerivative ζ s y := by
  have h := (windowBump_hasDerivAt s).smul (slice_hasDerivAt hζ s y)
  rw [timeDerivative, timeDerivative, (slice_hasDerivAt hζ s y).deriv, add_comm]
  exact h.deriv

theorem fderiv_cut {ζ : ℝ → Space → Space}
    (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (s : ℝ) (y : Space) :
    fderiv ℝ (timeCutoff windowBump ζ s) y = windowBump s • fderiv ℝ (ζ s) y :=
  ((sliceSpace_hasFDerivAt hζ s y).differentiableAt.hasFDerivAt.const_smul (windowBump s)).fderiv

def cutTest (φ : ℝ → Space → Space) : ℝ → Space → Space := fun s y => stripCutoff s • φ s y

theorem cutTest_isTest {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    IsSpaceTimeTestField (cutTest φ) := by
  refine ⟨((stripCutoff_contDiff.comp contDiff_fst).smul hφ.1), ?_, ?_⟩
  · exact hφ.2.1.smul_left (f := fun z : ℝ × Space => stripCutoff z.1)
  · intro s y
    have h : fderiv ℝ (cutTest φ s) y = stripCutoff s • fderiv ℝ (φ s) y := by
      have e : cutTest φ s = stripCutoff s • φ s := rfl
      rw [e, fderiv_const_smul_field]
      rfl
    have h0 := hφ.2.2 s y
    unfold divergenceAt at h0 ⊢
    rw [h]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h0, mul_zero]

theorem cutTest_isTestVector {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    IsSpaceTimeTestVector (cutTest φ) :=
  ⟨(cutTest_isTest hφ).1, (cutTest_isTest hφ).2.1⟩

theorem cut_eq_strip (ζ : ℝ → Space → Space) (s : ℝ) (y : Space) :
    timeCutoff windowBump ζ s y = stripCutoff s • timeCutoff windowBump ζ s y := by
  simp only [timeCutoff, smul_smul, stripCutoff_mul_windowBump]

theorem cutTest_sub (φ ζ : ℝ → Space → Space) (s : ℝ) (y : Space) :
    cutTest φ s y - timeCutoff windowBump ζ s y = stripCutoff s • (φ s y - timeCutoff windowBump ζ s y) := by
  rw [smul_sub, ← cut_eq_strip]
  rfl

theorem cutTest_timeDerivative_sub {φ ζ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (s : ℝ) (y : Space) :
    timeDerivative (cutTest φ) s y - timeDerivative (timeCutoff windowBump ζ) s y =
      deriv stripCutoff s • (φ s y - timeCutoff windowBump ζ s y) +
        stripCutoff s • (timeDerivative φ s y - timeDerivative (timeCutoff windowBump ζ) s y) := by
  have hφ1 : ContDiff ℝ 1 (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.of_le one_le_smooth
  have hZ := cut_contDiff hζ
  have ha := (stripCutoff_hasDerivAt s).smul (slice_hasDerivAt hφ1 s y)
  have hb := (stripCutoff_hasDerivAt s).smul (slice_hasDerivAt hZ s y)
  have e1 : timeDerivative (cutTest φ) s y = stripCutoff s • timeDerivative φ s y +
      deriv stripCutoff s • φ s y := by
    rw [timeDerivative, timeDerivative, (slice_hasDerivAt hφ1 s y).deriv]
    exact ha.deriv
  have e2 : timeDerivative (timeCutoff windowBump ζ) s y =
      stripCutoff s • timeDerivative (timeCutoff windowBump ζ) s y +
        deriv stripCutoff s • timeCutoff windowBump ζ s y := by
    have hf : (fun t => timeCutoff windowBump ζ t y) = fun t => stripCutoff t • timeCutoff windowBump ζ t y := by
      funext t
      exact cut_eq_strip ζ t y
    conv_lhs => rw [timeDerivative, hf]
    rw [timeDerivative, (slice_hasDerivAt hZ s y).deriv]
    exact hb.deriv
  rw [e1, smul_sub, smul_sub]
  nth_rw 1 [e2]
  abel

theorem cutTest_fderiv_sub (φ ζ : ℝ → Space → Space) (s : ℝ) (y : Space) :
    fderiv ℝ (cutTest φ s) y - fderiv ℝ (timeCutoff windowBump ζ s) y =
      stripCutoff s • (fderiv ℝ (φ s) y - fderiv ℝ (timeCutoff windowBump ζ s) y) := by
  have e1 : cutTest φ s = stripCutoff s • φ s := rfl
  have e2 : timeCutoff windowBump ζ s = stripCutoff s • timeCutoff windowBump ζ s := by
    funext y
    exact cut_eq_strip ζ s y
  have h2 : fderiv ℝ (timeCutoff windowBump ζ s) y = stripCutoff s • fderiv ℝ (timeCutoff windowBump ζ s) y := by
    conv_lhs => rw [e2]
    rw [fderiv_const_smul_field]
    rfl
  rw [e1, fderiv_const_smul_field, smul_sub]
  conv_lhs => rw [h2]
  rfl

theorem adjoint_C_nonneg {ζ : ℝ → Space → Space} {C γ : ℝ} (hζ : IsAdjointField ζ C γ) : 0 ≤ C := by
  have h := (hζ.decay 0 0).1
  simp only [norm_zero, add_zero, Real.one_rpow, div_one] at h
  exact (norm_nonneg _).trans h

theorem flow_D_nonneg {W : ℝ → Space → Space} {D : ℝ} (hW : IsFlowPiece W D) : 0 ≤ D :=
  (norm_nonneg _).trans (hW.decay 0 0).1

theorem one_add_norm_pos (y : Space) : 0 < 1 + ‖y‖ := by positivity

theorem decay_nonneg {C : ℝ} (hC : 0 ≤ C) (p : ℝ) (y : Space) : 0 ≤ C / (1 + ‖y‖) ^ p :=
  div_nonneg hC (Real.rpow_nonneg (one_add_norm_pos y).le p)

theorem decay_succ_le {C : ℝ} (hC : 0 ≤ C) (p : ℝ) (hp : 0 ≤ p) (y : Space) :
    C / (1 + ‖y‖) ^ (p + 1) ≤ C / (1 + ‖y‖) ^ p := by
  apply div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos (one_add_norm_pos y) p)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) (by linarith)

theorem apply_self_le {C p : ℝ} (hC : 0 ≤ C) {A : Space →L[ℝ] Space} {y : Space}
    (h : ‖A‖ ≤ C / (1 + ‖y‖) ^ (p + 1)) : ‖A y‖ ≤ C / (1 + ‖y‖) ^ p := by
  have hpos := one_add_norm_pos y
  have e : C / (1 + ‖y‖) ^ (p + 1) * (1 + ‖y‖) = C / (1 + ‖y‖) ^ p := by
    rw [Real.rpow_add_one hpos.ne']
    field_simp
  calc ‖A y‖ ≤ ‖A‖ * ‖y‖ := A.le_opNorm y
    _ ≤ C / (1 + ‖y‖) ^ (p + 1) * (1 + ‖y‖) :=
        mul_le_mul h (by linarith) (norm_nonneg _) (decay_nonneg hC _ y)
    _ = C / (1 + ‖y‖) ^ p := e

theorem cut_norm_le {ζ : ℝ → Space → Space} {C γ : ℝ} (hζ : IsAdjointField ζ C γ) (s : ℝ) (y : Space) :
    ‖timeCutoff windowBump ζ s y‖ ≤ C / (1 + ‖y‖) ^ γ := by
  rw [timeCutoff, norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (abs_windowBump_le s)).trans (hζ.decay s y).1

theorem cut_time_norm_le {ζ : ℝ → Space → Space} {C γ : ℝ} (hζ : IsAdjointField ζ C γ) {M : ℝ}
    (hM : ∀ s, |deriv windowBump s| ≤ M) (s : ℝ) (y : Space) :
    ‖timeDerivative (timeCutoff windowBump ζ) s y‖ ≤ (M + 1) * C / (1 + ‖y‖) ^ γ := by
  rw [timeDerivative_cut hζ.smooth, mul_div_assoc]
  have h1 := (hζ.decay s y).1
  have h2 := (hζ.decay s y).2.1
  have hc := decay_nonneg (adjoint_C_nonneg hζ) γ y
  calc ‖deriv windowBump s • ζ s y + windowBump s • timeDerivative ζ s y‖
      ≤ |deriv windowBump s| * ‖ζ s y‖ + |windowBump s| * ‖timeDerivative ζ s y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ M * (C / (1 + ‖y‖) ^ γ) + 1 * (C / (1 + ‖y‖) ^ γ) := by
        gcongr
        · exact (abs_nonneg _).trans (hM s)
        · exact hM s
        · exact abs_windowBump_le s
    _ = (M + 1) * (C / (1 + ‖y‖) ^ γ) := by ring

theorem cut_fderiv_norm_le {ζ : ℝ → Space → Space} {C γ : ℝ} (hζ : IsAdjointField ζ C γ) (s : ℝ) (y : Space) :
    ‖fderiv ℝ (timeCutoff windowBump ζ s) y‖ ≤ C / (1 + ‖y‖) ^ (γ + 1) := by
  rw [fderiv_cut hζ.smooth, norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (abs_windowBump_le s)).trans (hζ.decay s y).2.2

theorem outside_window {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) : s ∉ Set.Icc (-1 : ℝ) 1 := by
  intro h
  exact hs ⟨by linarith [h.1], by linarith [h.2]⟩

theorem cut_zero_off {ζ : ℝ → Space → Space} {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) (y : Space) :
    timeCutoff windowBump ζ s y = 0 := by
  rw [timeCutoff, windowBump_eq_zero (outside_window hs), zero_smul]

theorem cut_time_zero_off {ζ : ℝ → Space → Space} (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) (y : Space) :
    timeDerivative (timeCutoff windowBump ζ) s y = 0 := by
  rw [timeDerivative_cut hζ, windowBump_eq_zero (outside_window hs),
    deriv_windowBump_eq_zero (outside_window hs), zero_smul, zero_smul, add_zero]

theorem cut_fderiv_zero_off {ζ : ℝ → Space → Space} (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) (y : Space) :
    fderiv ℝ (timeCutoff windowBump ζ s) y = 0 := by
  rw [fderiv_cut hζ, windowBump_eq_zero (outside_window hs), zero_smul]

theorem aesm_apply {A : ℝ × Space → (Space →L[ℝ] Space)} {x : ℝ × Space → Space}
    (hA : AEStronglyMeasurable A volume) (hx : AEStronglyMeasurable x volume) :
    AEStronglyMeasurable (fun z => A z (x z)) volume := by
  have hc : Continuous (fun p : (Space →L[ℝ] Space) × Space => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact hc.comp_aestronglyMeasurable (hA.prodMk hx)

theorem aesm_pairSum {A B : ℝ × Space → (Space →L[ℝ] Space)}
    (hA : AEStronglyMeasurable A volume) (hB : AEStronglyMeasurable B volume) :
    AEStronglyMeasurable (fun z => matInner (A z) (B z)) volume := by
  unfold matInner
  have h := Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
    AEStronglyMeasurable.inner (𝕜 := ℝ) (hA.apply_continuousLinearMap (unitVector i))
      (hB.apply_continuousLinearMap (unitVector i))
  have e : (fun z => ∑ i : Fin 3, inner ℝ (A z (unitVector i)) (B z (unitVector i))) =
      ∑ i : Fin 3, fun z => inner ℝ (A z (unitVector i)) (B z (unitVector i)) := by
    funext z
    simp [Finset.sum_apply]
  rw [e]
  exact h

theorem integrable_of_enorm_le {h : ℝ × Space → ℝ} (hm : AEStronglyMeasurable h volume)
    {b : ℝ × Space → ℝ≥0∞} (hle : ∀ z, ‖h z‖ₑ ≤ b z) (hb : ∫⁻ z, b z < ⊤) : Integrable h :=
  ⟨hm, hasFiniteIntegral_iff_enorm.2 (lt_of_le_of_lt (lintegral_mono hle) hb)⟩

theorem sq_bound_lt_top {a e : ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a) (he : AEMeasurable e)
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e z = 0)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, a (s, y) ^ 2 < ⊤) (hE : ∫⁻ z, e z ^ 2 < ⊤) :
    ∫⁻ z, a z * e z < ⊤ :=
  lt_of_le_of_lt (lintegral_mul_le_strip_sq ha he hz)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE.ne))

theorem mixed_bound_lt_top {a e : ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a) (he : AEMeasurable e)
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e z = 0)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, a (s, y) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) < ⊤)
    (hE : ∫⁻ s, (∫⁻ y, e (s, y) ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) < ⊤) :
    ∫⁻ z, a z * e z < ⊤ :=
  lt_of_le_of_lt (lintegral_mul_le_strip_mixed ha he hz)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE.ne))

theorem tendsto_const_mul_sqrt {X : ℕ → ℝ≥0∞} (hX : Tendsto X atTop (𝓝 0)) {K : ℝ≥0∞} (hK : K ≠ ⊤) :
    Tendsto (fun n => K * X n ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => X n ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hX
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  have := ENNReal.Tendsto.const_mul h1 (Or.inr hK)
  rwa [mul_zero] at this

theorem sq_bound_tendsto {a : ℝ × Space → ℝ≥0∞} {e : ℕ → ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a)
    (he : ∀ n, AEMeasurable (e n)) (hz : ∀ n, ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e n z = 0)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, a (s, y) ^ 2 < ⊤) {X : ℕ → ℝ≥0∞}
    (hX : Tendsto X atTop (𝓝 0)) (hEX : ∀ n, ∫⁻ z, e n z ^ 2 ≤ X n) :
    Tendsto (fun n => ∫⁻ z, a z * e n z) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ≥0∞)) tendsto_const_nhds
    (tendsto_const_mul_sqrt hX (K := (∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, a (s, y) ^ 2) ^ (1 / 2 : ℝ))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne).ne)
    (fun n => by simp) (fun n => ?_)
  refine (lintegral_mul_le_strip_sq ha (he n) (hz n)).trans ?_
  gcongr
  exact hEX n

theorem mixed_bound_tendsto {a : ℝ × Space → ℝ≥0∞} {e : ℕ → ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a)
    (he : ∀ n, AEMeasurable (e n)) (hz : ∀ n, ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → e n z = 0)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, a (s, y) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) < ⊤) {X : ℕ → ℝ≥0∞}
    (hX : Tendsto X atTop (𝓝 0)) (hEX : ∀ n, ∫⁻ s, (∫⁻ y, e n (s, y) ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) ≤ X n) :
    Tendsto (fun n => ∫⁻ z, a z * e n z) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ≥0∞)) tendsto_const_nhds
    (tendsto_const_mul_sqrt hX
      (K := (∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, a (s, y) ^ (6 : ℝ)) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne).ne)
    (fun n => by simp) (fun n => ?_)
  refine (lintegral_mul_le_strip_mixed ha (he n) (hz n)).trans ?_
  gcongr
  exact hEX n

theorem pass_limit {ℓn : ℕ → ℝ × Space → ℝ} {ℓ : ℝ × Space → ℝ} (hℓ : Integrable ℓ)
    (hm : ∀ n, AEStronglyMeasurable (ℓn n) volume) {B : ℕ → ℝ≥0∞} (hB : Tendsto B atTop (𝓝 0))
    (hle : ∀ n, ∫⁻ z, ‖ℓn n z - ℓ z‖ₑ ≤ B n) :
    (∀ᶠ n in atTop, Integrable (ℓn n)) ∧ Tendsto (fun n => ∫ z, ℓn n z) atTop (𝓝 (∫ z, ℓ z)) := by
  have hev : ∀ᶠ n in atTop, Integrable (ℓn n) := by
    filter_upwards [hB.eventually (eventually_lt_nhds ENNReal.zero_lt_top)] with n hn
    have hd : Integrable (fun z => ℓn n z - ℓ z) :=
      ⟨(hm n).sub hℓ.1, hasFiniteIntegral_iff_enorm.2 (lt_of_le_of_lt (hle n) hn)⟩
    have e : (fun z => ℓn n z - ℓ z) + ℓ = ℓn n := by
      funext z
      simp
    have := hd.add hℓ
    rwa [e] at this
  refine ⟨hev, tendsto_integral_of_L1 ℓ hℓ.1 hev ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ≥0∞)) tendsto_const_nhds hB
    (fun n => by simp) hle

theorem sum_unitVector (w : Space) : ∑ i : Fin 3, w i • unitVector i = w := by
  ext j
  simp [unitVector, Pi.single_apply]

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem continuous_entrySq : Continuous matSq := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem entrySq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem norm_apply_le_entrySq_root (A : Space →L[ℝ] Space) (w : Space) : ‖A w‖ ≤ ‖w‖ * Real.sqrt (matSq A) := by
  have hw : A w = ∑ i : Fin 3, w i • A (unitVector i) := by
    conv_lhs => rw [← sum_unitVector w]
    simp [map_sum, map_smul]
  rw [hw]
  calc ‖∑ i : Fin 3, w i • A (unitVector i)‖ ≤ ∑ i : Fin 3, |w i| * ‖A (unitVector i)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_smul]
    _ ≤ Real.sqrt (∑ i : Fin 3, |w i| ^ 2) * Real.sqrt (∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖w‖ * Real.sqrt (matSq A) := by
        rw [EuclideanSpace.norm_eq]
        simp [matSq, sq_abs]

theorem entrySq_root_le_two_norm (A : Space →L[ℝ] Space) : Real.sqrt (matSq A) ≤ 2 * ‖A‖ := by
  rw [show 2 * ‖A‖ = Real.sqrt ((2 * ‖A‖) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  unfold matSq
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i => by
    have := A.le_opNorm (unitVector i)
    rw [norm_unitVector, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖A‖ ^ 2 := by simp
    _ ≤ (2 * ‖A‖) ^ 2 := by nlinarith [sq_nonneg ‖A‖]

theorem abs_pairSum_le (A B : Space →L[ℝ] Space) :
    |matInner A B| ≤ Real.sqrt (matSq A) * Real.sqrt (matSq B) := by
  unfold matInner matSq
  calc |∑ i : Fin 3, inner ℝ (A (unitVector i)) (B (unitVector i))|
      ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ * ‖B (unitVector i)‖ :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm _ _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem pairSum_sub_right (A B B' : Space →L[ℝ] Space) :
    matInner A (B - B') = matInner A B - matInner A B' := by
  simp [matInner, inner_sub_right, Finset.sum_sub_distrib]

theorem entrySq_smul (c : ℝ) (A : Space →L[ℝ] Space) : matSq (c • A) = c ^ 2 * matSq A := by
  simp [matSq, norm_smul, mul_pow, Finset.mul_sum, sq_abs]

def pairF (F φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ := inner ℝ (F z.1 z.2) (φ z.1 z.2)

def pairGW (G : ℝ → Space → (Space →L[ℝ] Space)) (W φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  inner ℝ (G z.1 z.2 (W z.1 z.2)) (φ z.1 z.2)

def pairWv (W v φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  inner ℝ (fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)

def pairG (G : ℝ → Space → (Space →L[ℝ] Space)) (φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)

def pairT (P : ℝ) (v φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  inner ℝ (v z.1 z.2) (-(1 / P) • timeDerivative φ z.1 z.2 - φ z.1 z.2
    - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2)

theorem enorm_le_ofReal {x r : ℝ} (h : |x| ≤ r) : ‖x‖ₑ ≤ ENNReal.ofReal r := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

theorem pairF_sub (F φ ψ : ℝ → Space → Space) (z : ℝ × Space) :
    ‖pairF F φ z - pairF F ψ z‖ₑ ≤
      ENNReal.ofReal ‖F z.1 z.2‖ * ENNReal.ofReal ‖φ z.1 z.2 - ψ z.1 z.2‖ := by
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  apply enorm_le_ofReal
  rw [pairF, pairF, ← inner_sub_right]
  exact abs_real_inner_le_norm _ _

theorem pairGW_sub {G : ℝ → Space → (Space →L[ℝ] Space)} {W : ℝ → Space → Space} {D : ℝ}
    (hW : ∀ σ y, ‖W σ y‖ ≤ D) (φ ψ : ℝ → Space → Space) (z : ℝ × Space) :
    ‖pairGW G W φ z - pairGW G W ψ z‖ₑ ≤
      ENNReal.ofReal (D * Real.sqrt (matSq (G z.1 z.2))) * ENNReal.ofReal ‖φ z.1 z.2 - ψ z.1 z.2‖ := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hW 0 0)
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply enorm_le_ofReal
  rw [pairGW, pairGW, ← inner_sub_right]
  refine (abs_real_inner_le_norm _ _).trans ?_
  gcongr
  refine (norm_apply_le_entrySq_root _ _).trans ?_
  gcongr
  exact hW _ _

theorem pairWv_sub {W v : ℝ → Space → Space} {D : ℝ} (hW : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖))
    (φ ψ : ℝ → Space → Space) (z : ℝ × Space) :
    ‖pairWv W v φ z - pairWv W v ψ z‖ₑ ≤
      ENNReal.ofReal (D * (‖v z.1 z.2‖ / (1 + ‖z.2‖))) * ENNReal.ofReal ‖φ z.1 z.2 - ψ z.1 z.2‖ := by
  have hpos := one_add_norm_pos z.2
  have hD : 0 ≤ D := by
    have := (norm_nonneg _).trans (hW 0 0)
    simpa using this
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply enorm_le_ofReal
  rw [pairWv, pairWv, ← inner_sub_right]
  refine (abs_real_inner_le_norm _ _).trans ?_
  gcongr
  refine ((fderiv ℝ (W z.1) z.2).le_opNorm _).trans ?_
  calc ‖fderiv ℝ (W z.1) z.2‖ * ‖v z.1 z.2‖ ≤ D / (1 + ‖z.2‖) * ‖v z.1 z.2‖ :=
        mul_le_mul_of_nonneg_right (hW _ _) (norm_nonneg _)
    _ = D * (‖v z.1 z.2‖ / (1 + ‖z.2‖)) := by ring

theorem pairG_sub (G : ℝ → Space → (Space →L[ℝ] Space)) (φ ψ : ℝ → Space → Space) (z : ℝ × Space) :
    ‖pairG G φ z - pairG G ψ z‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))) *
        ENNReal.ofReal (Real.sqrt (matSq (fderiv ℝ (φ z.1) z.2 - fderiv ℝ (ψ z.1) z.2))) := by
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply enorm_le_ofReal
  rw [pairG, pairG, ← pairSum_sub_right]
  exact abs_pairSum_le _ _

theorem pairT_sub (P : ℝ) (v φ ψ : ℝ → Space → Space) (z : ℝ × Space) :
    ‖pairT P v φ z - pairT P v ψ z‖ₑ ≤
      ENNReal.ofReal ‖v z.1 z.2‖ * ENNReal.ofReal (|1 / P| *
        ‖timeDerivative φ z.1 z.2 - timeDerivative ψ z.1 z.2‖)
      + ENNReal.ofReal ‖v z.1 z.2‖ * ENNReal.ofReal ‖φ z.1 z.2 - ψ z.1 z.2‖
      + ENNReal.ofReal ‖v z.1 z.2‖ * ENNReal.ofReal ‖fderiv ℝ (φ z.1) z.2 z.2 - fderiv ℝ (ψ z.1) z.2 z.2‖ := by
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply enorm_le_ofReal
  have e : pairT P v φ z - pairT P v ψ z = inner ℝ (v z.1 z.2)
      (-(1 / P) • (timeDerivative φ z.1 z.2 - timeDerivative ψ z.1 z.2) - (φ z.1 z.2 - ψ z.1 z.2)
        - (1 / 2 : ℝ) • (fderiv ℝ (φ z.1) z.2 z.2 - fderiv ℝ (ψ z.1) z.2 z.2)) := by
    rw [pairT, pairT, ← inner_sub_right]
    congr 1
    simp only [smul_sub]
    abel
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have hv := norm_nonneg (v z.1 z.2)
  have h1 : ‖-(1 / P) • (timeDerivative φ z.1 z.2 - timeDerivative ψ z.1 z.2) - (φ z.1 z.2 - ψ z.1 z.2)
        - (1 / 2 : ℝ) • (fderiv ℝ (φ z.1) z.2 z.2 - fderiv ℝ (ψ z.1) z.2 z.2)‖ ≤
      |1 / P| * ‖timeDerivative φ z.1 z.2 - timeDerivative ψ z.1 z.2‖ + ‖φ z.1 z.2 - ψ z.1 z.2‖
        + ‖fderiv ℝ (φ z.1) z.2 z.2 - fderiv ℝ (ψ z.1) z.2 z.2‖ := by
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (le_of_eq ?_)) ?_
    · rw [norm_smul, norm_neg, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  calc ‖v z.1 z.2‖ * ‖_‖ ≤ ‖v z.1 z.2‖ * (|1 / P| * ‖timeDerivative φ z.1 z.2 - timeDerivative ψ z.1 z.2‖
        + ‖φ z.1 z.2 - ψ z.1 z.2‖ + ‖fderiv ℝ (φ z.1) z.2 z.2 - fderiv ℝ (ψ z.1) z.2 z.2‖) :=
        mul_le_mul_of_nonneg_left h1 hv
    _ = _ := by ring

theorem zeroField_fderiv (s : ℝ) (y : Space) :
    fderiv ℝ ((fun _ _ => (0 : Space)) s : Space → Space) y = 0 := by
  simp

theorem pairF_zero (F : ℝ → Space → Space) (z : ℝ × Space) : pairF F (fun _ _ => 0) z = 0 := by
  simp [pairF]

theorem pairGW_zero (G : ℝ → Space → (Space →L[ℝ] Space)) (W : ℝ → Space → Space) (z : ℝ × Space) :
    pairGW G W (fun _ _ => 0) z = 0 := by
  simp [pairGW]

theorem pairWv_zero (W v : ℝ → Space → Space) (z : ℝ × Space) : pairWv W v (fun _ _ => 0) z = 0 := by
  simp [pairWv]

theorem pairG_zero (G : ℝ → Space → (Space →L[ℝ] Space)) (z : ℝ × Space) : pairG G (fun _ _ => 0) z = 0 := by
  simp [pairG, matInner]

theorem pairT_zero (P : ℝ) (v : ℝ → Space → Space) (z : ℝ × Space) : pairT P v (fun _ _ => 0) z = 0 := by
  simp [pairT, timeDerivative]

theorem ofReal_sqrt_sq {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (Real.sqrt x) ^ 2 = ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hx]

theorem strip_const_mul_sq {c : ℝ} {f : ℝ → Space → ℝ} (hf0 : ∀ s y, 0 ≤ f s y)
    (h : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (f s y) ^ 2 < ⊤) :
    ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (c * f s y) ^ 2 < ⊤ := by
  have hle : ∀ s y, ENNReal.ofReal (c * f s y) ^ 2 ≤ ENNReal.ofReal |c| ^ 2 * ENNReal.ofReal (f s y) ^ 2 := by
    intro s y
    rw [← mul_pow, ← ENNReal.ofReal_mul (abs_nonneg c)]
    exact pow_le_pow_left₀ zero_le
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self c) (hf0 s y))) 2
  have hK : ENNReal.ofReal |c| ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (c * f s y) ^ 2
      ≤ ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal |c| ^ 2 * ENNReal.ofReal (f s y) ^ 2 :=
        lintegral_mono fun s => lintegral_mono fun y => hle s y
    _ = ENNReal.ofReal |c| ^ 2 * ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (f s y) ^ 2 := by
        simp_rw [lintegral_const_mul' _ _ hK]
    _ < ⊤ := ENNReal.mul_lt_top hK.lt_top h

theorem mixed_le_scalar {e : ℝ × Space → ℝ≥0∞} {f : ℝ → Space → Space} {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ s y, e (s, y) ≤ ENNReal.ofReal (c * ‖f s y‖)) :
    ∫⁻ s, (∫⁻ y, e (s, y) ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) ≤ ENNReal.ofReal (c ^ 2) * mixedNorm f := by
  have h1 : ∀ s y, e (s, y) ^ (6 / 5 : ℝ) ≤
      ENNReal.ofReal (c ^ (6 / 5 : ℝ)) * ENNReal.ofReal (‖f s y‖ ^ (6 / 5 : ℝ)) := by
    intro s y
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc _), ← Real.mul_rpow hc (norm_nonneg _),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    exact ENNReal.rpow_le_rpow (he s y) (by norm_num)
  have hK : ENNReal.ofReal (c ^ (6 / 5 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : ENNReal.ofReal (c ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) = ENNReal.ofReal (c ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hc _) (by norm_num), ← Real.rpow_mul hc]
    norm_num
  unfold mixedNorm
  calc ∫⁻ s, (∫⁻ y, e (s, y) ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ)
      ≤ ∫⁻ s, (ENNReal.ofReal (c ^ (6 / 5 : ℝ)) * ∫⁻ y, ENNReal.ofReal (‖f s y‖ ^ (6 / 5 : ℝ))) ^ (5 / 3 : ℝ) := by
        refine lintegral_mono fun s => ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← lintegral_const_mul' _ _ hK]
        exact lintegral_mono fun y => h1 s y
    _ = ∫⁻ s, ENNReal.ofReal (c ^ 2) * (∫⁻ y, ENNReal.ofReal (‖f s y‖ ^ (6 / 5 : ℝ))) ^ (5 / 3 : ℝ) := by
        congr 1
        funext s
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), h2]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem sq_le_scalar {e : ℝ × Space → ℝ≥0∞} {f : ℝ → Space → Space} {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ z : ℝ × Space, e z ≤ ENNReal.ofReal (c * ‖f z.1 z.2‖)) :
    ∫⁻ z, e z ^ 2 ≤ ENNReal.ofReal (c ^ 2) * ∫⁻ z : ℝ × Space, ENNReal.ofReal (‖f z.1 z.2‖ ^ 2) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  calc e z ^ 2 ≤ ENNReal.ofReal (c * ‖f z.1 z.2‖) ^ 2 := pow_le_pow_left₀ zero_le (he z) 2
    _ = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (‖f z.1 z.2‖ ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (sq_nonneg c), mul_pow]

theorem tendsto_ofReal_mul {X : ℕ → ℝ≥0∞} (hX : Tendsto X atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n => ENNReal.ofReal c * X n) atTop (𝓝 0) := by
  have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) hX (Or.inr ENNReal.ofReal_ne_top)
  rwa [mul_zero] at this

theorem abs_stripCutoff_mul_zero_off {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) (x : ℝ) :
    |stripCutoff s| * x = 0 := by
  rw [stripCutoff_eq_zero hs, abs_zero, zero_mul]

theorem abs_deriv_stripCutoff_mul_zero_off {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) (x : ℝ) :
    |deriv stripCutoff s| * x = 0 := by
  rw [deriv_stripCutoff_eq_zero hs, abs_zero, zero_mul]

theorem norm_cutTest_sub_le (φ ζ : ℝ → Space → Space) (s : ℝ) (y : Space) :
    ‖cutTest φ s y - timeCutoff windowBump ζ s y‖ = |stripCutoff s| * ‖φ s y - timeCutoff windowBump ζ s y‖ := by
  rw [cutTest_sub, norm_smul, Real.norm_eq_abs]

theorem pass_value {p : (ℝ → Space → Space) → ℝ × Space → ℝ} {a : ℝ × Space → ℝ≥0∞}
    {ζ : ℝ → Space → Space} {C γ : ℝ} (hζ : IsAdjointField ζ C γ) (ha : AEMeasurable a volume)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, a (s, y) ^ 2 < ⊤)
    (hsub : ∀ φ ψ : ℝ → Space → Space, ∀ z : ℝ × Space,
      ‖p φ z - p ψ z‖ₑ ≤ a z * ENNReal.ofReal ‖φ z.1 z.2 - ψ z.1 z.2‖)
    (hzero : ∀ z, p (fun _ _ => 0) z = 0)
    (hm : ∀ φ : ℝ → Space → Space, Continuous (fun z : ℝ × Space => φ z.1 z.2) →
      AEStronglyMeasurable (p φ) volume)
    {φ : ℕ → ℝ → Space → Space} (hφ : ∀ n, IsSpaceTimeTestField (φ n))
    (h0 : Tendsto (fun n => ∫⁻ z : ℝ × Space,
      ENNReal.ofReal (‖φ n z.1 z.2 - timeCutoff windowBump ζ z.1 z.2‖ ^ 2)) atTop (𝓝 0)) :
    Integrable (p (timeCutoff windowBump ζ)) ∧
      (∀ᶠ n in atTop, Integrable (p (cutTest (φ n)))) ∧
      Tendsto (fun n => ∫ z, p (cutTest (φ n)) z) atTop (𝓝 (∫ z, p (timeCutoff windowBump ζ) z)) := by
  have hZc : Continuous (fun z : ℝ × Space => timeCutoff windowBump ζ z.1 z.2) :=
    (cut_contDiff hζ.smooth).continuous
  have hfc : ∀ n, Continuous (fun z : ℝ × Space => cutTest (φ n) z.1 z.2) := fun n =>
    (cutTest_isTest (hφ n)).1.continuous
  have hZint : Integrable (p (timeCutoff windowBump ζ)) := by
    refine integrable_of_enorm_le (hm _ hZc)
      (b := fun z => a z * ENNReal.ofReal ‖timeCutoff windowBump ζ z.1 z.2‖)
      (fun z => ?_) ?_
    · have := hsub (timeCutoff windowBump ζ) (fun _ _ => 0) z
      simp only [hzero, sub_zero] at this
      exact this
    · refine sq_bound_lt_top ha (hZc.norm.aemeasurable.ennreal_ofReal) ?_ hA ?_
      · intro z hz
        rw [cut_zero_off hz, norm_zero, ENNReal.ofReal_zero]
      · refine square_decay_lt_top (c := C) (p := γ) (by linarith [hζ.rate_gt]) (fun z => ?_) ?_
        · exact ENNReal.ofReal_le_ofReal (cut_norm_le hζ z.1 z.2)
        · intro z hz
          rw [cut_zero_off hz, norm_zero, ENNReal.ofReal_zero]
  refine ⟨hZint, pass_limit (ℓn := fun n => p (cutTest (φ n))) hZint (fun n => hm _ (hfc n))
    (B := fun n => ∫⁻ z : ℝ × Space, a z *
      ENNReal.ofReal ‖cutTest (φ n) z.1 z.2 - timeCutoff windowBump ζ z.1 z.2‖) ?_
    (fun n => lintegral_mono fun z => hsub (cutTest (φ n)) (timeCutoff windowBump ζ) z)⟩
  refine sq_bound_tendsto ha (fun n => ((hfc n).sub hZc).norm.aemeasurable.ennreal_ofReal) ?_ hA h0 ?_
  · intro n z hz
    rw [norm_cutTest_sub_le, abs_stripCutoff_mul_zero_off hz, ENNReal.ofReal_zero]
  · intro n
    refine (sq_le_scalar (c := 1) zero_le_one (f := fun s y => φ n s y - timeCutoff windowBump ζ s y)
      (fun z => ?_)).trans (by simp)
    rw [norm_cutTest_sub_le, one_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (norm_nonneg _) (abs_stripCutoff_le _))

theorem fderiv_cutTest_sub_eq (φ ζ : ℝ → Space → Space) (s : ℝ) (y : Space) :
    matSq (fderiv ℝ (cutTest φ s) y - fderiv ℝ (timeCutoff windowBump ζ s) y) =
      stripCutoff s ^ 2 * matSq (fderiv ℝ (φ s) y - fderiv ℝ (timeCutoff windowBump ζ s) y) := by
  rw [cutTest_fderiv_sub, entrySq_smul]

theorem pass_pairG {G : ℝ → Space → (Space →L[ℝ] Space)} {ζ : ℝ → Space → Space} {C γ : ℝ}
    (hζ : IsAdjointField ζ C γ) (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (Real.sqrt (matSq (G s y))) ^ 2 < ⊤)
    {φ : ℕ → ℝ → Space → Space} (hφ : ∀ n, IsSpaceTimeTestField (φ n))
    (hgrad : Tendsto (fun n => ∫⁻ z : ℝ × Space,
      ENNReal.ofReal (matSq (fderiv ℝ (φ n z.1) z.2 - fderiv ℝ (timeCutoff windowBump ζ z.1) z.2)))
        atTop (𝓝 0)) :
    Integrable (pairG G (timeCutoff windowBump ζ)) ∧
      (∀ᶠ n in atTop, Integrable (pairG G (cutTest (φ n)))) ∧
      Tendsto (fun n => ∫ z, pairG G (cutTest (φ n)) z) atTop
        (𝓝 (∫ z, pairG G (timeCutoff windowBump ζ) z)) := by
  have hZ1 := cut_contDiff hζ.smooth
  have hZd : Continuous (fun z : ℝ × Space => fderiv ℝ (timeCutoff windowBump ζ z.1) z.2) :=
    continuous_slice_fderiv hZ1
  have hfd : ∀ n, Continuous (fun z : ℝ × Space => fderiv ℝ (cutTest (φ n) z.1) z.2) := fun n =>
    continuous_slice_fderiv ((cutTest_isTest (hφ n)).1.of_le one_le_smooth)
  have ha : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2)))) volume :=
    ((Real.continuous_sqrt.comp continuous_entrySq).comp_aestronglyMeasurable hGm).aemeasurable.ennreal_ofReal
  have hm : ∀ ψ : ℝ → Space → Space,
      Continuous (fun z : ℝ × Space => fderiv ℝ (ψ z.1) z.2) → AEStronglyMeasurable (pairG G ψ) volume :=
    fun ψ hψ => aesm_pairSum hGm hψ.aestronglyMeasurable
  have hC := adjoint_C_nonneg hζ
  have hZint : Integrable (pairG G (timeCutoff windowBump ζ)) := by
    refine integrable_of_enorm_le (hm _ hZd)
      (b := fun z => ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))) *
        ENNReal.ofReal (Real.sqrt (matSq (fderiv ℝ (timeCutoff windowBump ζ z.1) z.2))))
      (fun z => ?_) ?_
    · have := pairG_sub G (timeCutoff windowBump ζ) (fun _ _ => 0) z
      simp only [pairG_zero, sub_zero] at this
      rw [show fderiv ℝ (fun _ : Space => (0 : Space)) z.2 = 0 from by simp, sub_zero] at this
      exact this
    · refine sq_bound_lt_top ha
        ((Real.continuous_sqrt.comp (continuous_entrySq.comp hZd)).aemeasurable.ennreal_ofReal) ?_ hA ?_
      · intro z hz
        simp only [cut_fderiv_zero_off hζ.smooth hz]
        simp [matSq]
      · refine square_decay_lt_top (c := 2 * C) (p := γ + 1) (by linarith [hζ.rate_gt]) (fun z => ?_) ?_
        · refine ENNReal.ofReal_le_ofReal ((entrySq_root_le_two_norm _).trans ?_)
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (cut_fderiv_norm_le hζ z.1 z.2) (by norm_num)
        · intro z hz
          simp only [cut_fderiv_zero_off hζ.smooth hz]
          simp [matSq]
  refine ⟨hZint, pass_limit (ℓn := fun n => pairG G (cutTest (φ n))) hZint (fun n => hm _ (hfd n))
    (B := fun n => ∫⁻ z : ℝ × Space, ENNReal.ofReal (Real.sqrt (matSq (G z.1 z.2))) *
      ENNReal.ofReal (Real.sqrt (matSq (fderiv ℝ (cutTest (φ n) z.1) z.2 -
        fderiv ℝ (timeCutoff windowBump ζ z.1) z.2)))) ?_
    (fun n => lintegral_mono fun z => pairG_sub G (cutTest (φ n)) (timeCutoff windowBump ζ) z)⟩
  refine sq_bound_tendsto ha
    (fun n => (Real.continuous_sqrt.comp (continuous_entrySq.comp ((hfd n).sub hZd))).aemeasurable.ennreal_ofReal)
    ?_ hA hgrad ?_
  · intro n z hz
    rw [fderiv_cutTest_sub_eq, stripCutoff_eq_zero hz]
    simp
  · intro n
    refine lintegral_mono fun z => ?_
    rw [ofReal_sqrt_sq (entrySq_nonneg _), fderiv_cutTest_sub_eq]
    refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (entrySq_nonneg _) ?_)
    have := abs_stripCutoff_le z.1
    rw [← sq_abs]
    nlinarith [abs_nonneg (stripCutoff z.1)]

theorem timeDerivative_zeroField (s : ℝ) (y : Space) :
    timeDerivative (fun _ _ => (0 : Space)) s y = 0 := by
  simp [timeDerivative]

theorem fderiv_zeroField_apply (s : ℝ) (y : Space) :
    fderiv ℝ ((fun _ _ => (0 : Space)) s : Space → Space) y y = 0 := by
  simp

theorem aesm_pairT {P : ℝ} {v ψ : ℝ → Space → Space}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (h1 : Continuous (fun z : ℝ × Space => timeDerivative ψ z.1 z.2))
    (h0 : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (h3 : Continuous (fun z : ℝ × Space => fderiv ℝ (ψ z.1) z.2 z.2)) :
    AEStronglyMeasurable (pairT P v ψ) volume := by
  have hc : Continuous (fun z : ℝ × Space => -(1 / P) • timeDerivative ψ z.1 z.2 - ψ z.1 z.2
      - (1 / 2 : ℝ) • fderiv ℝ (ψ z.1) z.2 z.2) :=
    ((h1.const_smul (-(1 / P))).sub h0).sub (h3.const_smul (1 / 2 : ℝ))
  unfold pairT
  exact AEStronglyMeasurable.inner (𝕜 := ℝ) hvm (hc.aestronglyMeasurable (μ := volume))

theorem continuous_test_timeDerivative {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun z : ℝ × Space => timeDerivative φ z.1 z.2) :=
  continuous_timeDerivative (hφ.1.of_le one_le_smooth)

theorem continuous_test_fderiv_apply {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 z.2) :=
  continuous_slice_fderiv_apply_self (hφ.1.of_le one_le_smooth)

theorem cutTest_fderiv_apply_sub (φ ζ : ℝ → Space → Space) (s : ℝ) (y : Space) :
    ‖fderiv ℝ (cutTest φ s) y y - fderiv ℝ (timeCutoff windowBump ζ s) y y‖ =
      |stripCutoff s| * ‖fderiv ℝ (φ s) y y - fderiv ℝ (timeCutoff windowBump ζ s) y y‖ := by
  rw [← ContinuousLinearMap.sub_apply, cutTest_fderiv_sub, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, norm_smul, Real.norm_eq_abs]

theorem cutTest_timeDerivative_sub_le {φ ζ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (P : ℝ) (s : ℝ) (y : Space) :
    ENNReal.ofReal (|1 / P| * ‖timeDerivative (cutTest φ) s y - timeDerivative (timeCutoff windowBump ζ) s y‖) ≤
      ENNReal.ofReal (|1 / P| * (|deriv stripCutoff s| * ‖φ s y - timeCutoff windowBump ζ s y‖)) +
      ENNReal.ofReal (|1 / P| * (|stripCutoff s| *
        ‖timeDerivative φ s y - timeDerivative (timeCutoff windowBump ζ) s y‖)) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← mul_add]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  rw [cutTest_timeDerivative_sub hφ hζ]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

theorem pass_pairT {P : ℝ} {v ζ : ℝ → Space → Space} {C γ : ℝ} (hζ : IsAdjointField ζ C γ)
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, ENNReal.ofReal ‖v s y‖ ^ (6 : ℝ)) ^ (1 / 3 : ℝ) < ⊤)
    {φ : ℕ → ℝ → Space → Space} (hφ : ∀ n, IsSpaceTimeTestField (φ n))
    (hm0 : Tendsto (fun n => mixedNorm (fun s y => φ n s y - timeCutoff windowBump ζ s y)) atTop (𝓝 0))
    (hm1 : Tendsto (fun n => mixedNorm (fun s y =>
      timeDerivative (φ n) s y - timeDerivative (timeCutoff windowBump ζ) s y)) atTop (𝓝 0))
    (hm3 : Tendsto (fun n => mixedNorm (fun s y =>
      fderiv ℝ (φ n s) y y - fderiv ℝ (timeCutoff windowBump ζ s) y y)) atTop (𝓝 0)) :
    Integrable (pairT P v (timeCutoff windowBump ζ)) ∧
      (∀ᶠ n in atTop, Integrable (pairT P v (cutTest (φ n)))) ∧
      Tendsto (fun n => ∫ z, pairT P v (cutTest (φ n)) z) atTop
        (𝓝 (∫ z, pairT P v (timeCutoff windowBump ζ) z)) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_deriv_windowBump_le
  obtain ⟨Mc, hMc0, hMc⟩ := exists_abs_deriv_stripCutoff_le
  have hC := adjoint_C_nonneg hζ
  have hγ := hζ.rate_gt
  have hZ1 := cut_contDiff hζ.smooth
  have hZ0 : Continuous (fun z : ℝ × Space => timeCutoff windowBump ζ z.1 z.2) := hZ1.continuous
  have hZt : Continuous (fun z : ℝ × Space => timeDerivative (timeCutoff windowBump ζ) z.1 z.2) :=
    continuous_timeDerivative hZ1
  have hZy : Continuous (fun z : ℝ × Space => fderiv ℝ (timeCutoff windowBump ζ z.1) z.2 z.2) :=
    continuous_slice_fderiv_apply_self hZ1
  have hχ : Continuous stripCutoff := stripCutoff_contDiff.continuous
  have hχ' : Continuous (deriv stripCutoff) := stripCutoff_contDiff.continuous_deriv (by simp)
  have ha : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ‖v z.1 z.2‖) volume :=
    hvm.norm.aemeasurable.ennreal_ofReal
  set a : ℝ × Space → ℝ≥0∞ := fun z => ENNReal.ofReal ‖v z.1 z.2‖ with ha_def
  have hZint : Integrable (pairT P v (timeCutoff windowBump ζ)) := by
    refine integrable_of_enorm_le (aesm_pairT hvm hZt hZ0 hZy)
      (b := fun z => a z * ENNReal.ofReal (|1 / P| * ‖timeDerivative (timeCutoff windowBump ζ) z.1 z.2‖)
        + a z * ENNReal.ofReal ‖timeCutoff windowBump ζ z.1 z.2‖
        + a z * ENNReal.ofReal ‖fderiv ℝ (timeCutoff windowBump ζ z.1) z.2 z.2‖)
      (fun z => ?_) ?_
    · have := pairT_sub P v (timeCutoff windowBump ζ) (fun _ _ => 0) z
      simp only [pairT_zero, sub_zero, timeDerivative_zeroField] at this
      rw [show (fderiv ℝ (fun _ : Space => (0 : Space)) z.2) z.2 = 0 from by simp, sub_zero] at this
      exact this
    · have e1 : ∫⁻ z, a z * ENNReal.ofReal (|1 / P| * ‖timeDerivative (timeCutoff windowBump ζ) z.1 z.2‖) < ⊤ := by
        refine mixed_bound_lt_top ha ((continuous_const.mul hZt.norm).aemeasurable.ennreal_ofReal) ?_ hA ?_
        · intro z hz
          rw [cut_time_zero_off hζ.smooth hz, norm_zero, mul_zero, ENNReal.ofReal_zero]
        · refine mixed_decay_lt_top (e := fun z : ℝ × Space => ENNReal.ofReal (|1 / P| *
            ‖timeDerivative (timeCutoff windowBump ζ) z.1 z.2‖))
            (c := |1 / P| * ((M + 1) * C)) (p := γ) (by linarith) (fun z => ?_) ?_
          · refine ENNReal.ofReal_le_ofReal ?_
            rw [mul_div_assoc, mul_div_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [← mul_div_assoc]
            exact cut_time_norm_le hζ hM z.1 z.2
          · intro z hz
            rw [cut_time_zero_off hζ.smooth hz, norm_zero, mul_zero, ENNReal.ofReal_zero]
      have e2 : ∫⁻ z, a z * ENNReal.ofReal ‖timeCutoff windowBump ζ z.1 z.2‖ < ⊤ := by
        refine mixed_bound_lt_top ha (hZ0.norm.aemeasurable.ennreal_ofReal) ?_ hA ?_
        · intro z hz
          rw [cut_zero_off hz, norm_zero, ENNReal.ofReal_zero]
        · refine mixed_decay_lt_top (e := fun z : ℝ × Space => ENNReal.ofReal ‖timeCutoff windowBump ζ z.1 z.2‖)
            (c := C) (p := γ) (by linarith) (fun z => ?_) ?_
          · exact ENNReal.ofReal_le_ofReal (cut_norm_le hζ z.1 z.2)
          · intro z hz
            rw [cut_zero_off hz, norm_zero, ENNReal.ofReal_zero]
      have e3 : ∫⁻ z, a z * ENNReal.ofReal ‖fderiv ℝ (timeCutoff windowBump ζ z.1) z.2 z.2‖ < ⊤ := by
        refine mixed_bound_lt_top ha (hZy.norm.aemeasurable.ennreal_ofReal) ?_ hA ?_
        · intro z hz
          rw [cut_fderiv_zero_off hζ.smooth hz, ContinuousLinearMap.zero_apply, norm_zero, ENNReal.ofReal_zero]
        · refine mixed_decay_lt_top (e := fun z : ℝ × Space =>
            ENNReal.ofReal ‖fderiv ℝ (timeCutoff windowBump ζ z.1) z.2 z.2‖)
            (c := C) (p := γ) (by linarith) (fun z => ?_) ?_
          · exact ENNReal.ofReal_le_ofReal (apply_self_le hC (cut_fderiv_norm_le hζ z.1 z.2))
          · intro z hz
            rw [cut_fderiv_zero_off hζ.smooth hz, ContinuousLinearMap.zero_apply, norm_zero, ENNReal.ofReal_zero]
      have m1 : AEMeasurable (fun z => a z * ENNReal.ofReal (|1 / P| *
          ‖timeDerivative (timeCutoff windowBump ζ) z.1 z.2‖)) volume :=
        ha.mul (continuous_const.mul hZt.norm).aemeasurable.ennreal_ofReal
      have m2 : AEMeasurable (fun z => a z * ENNReal.ofReal ‖timeCutoff windowBump ζ z.1 z.2‖) volume :=
        ha.mul hZ0.norm.aemeasurable.ennreal_ofReal
      have m12 : AEMeasurable (fun z => a z * ENNReal.ofReal (|1 / P| *
          ‖timeDerivative (timeCutoff windowBump ζ) z.1 z.2‖) +
          a z * ENNReal.ofReal ‖timeCutoff windowBump ζ z.1 z.2‖) volume := m1.add m2
      rw [lintegral_add_left' m12, lintegral_add_left' m1]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨e1, e2⟩, e3⟩
  set Z := timeCutoff windowBump ζ with hZdef
  have hφc : ∀ n, Continuous (fun z : ℝ × Space => φ n z.1 z.2) := fun n => (hφ n).1.continuous
  have hφt : ∀ n, Continuous (fun z : ℝ × Space => timeDerivative (φ n) z.1 z.2) := fun n =>
    continuous_test_timeDerivative (hφ n)
  have hφy : ∀ n, Continuous (fun z : ℝ × Space => fderiv ℝ (φ n z.1) z.2 z.2) := fun n =>
    continuous_test_fderiv_apply (hφ n)
  set e1 : ℕ → ℝ × Space → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (|1 / P| * (|deriv stripCutoff z.1| * ‖φ n z.1 z.2 - Z z.1 z.2‖)) with he1
  set e2 : ℕ → ℝ × Space → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (|1 / P| * (|stripCutoff z.1| * ‖timeDerivative (φ n) z.1 z.2 - timeDerivative Z z.1 z.2‖))
    with he2
  set e3 : ℕ → ℝ × Space → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (|stripCutoff z.1| * ‖φ n z.1 z.2 - Z z.1 z.2‖) with he3
  set e4 : ℕ → ℝ × Space → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (|stripCutoff z.1| * ‖fderiv ℝ (φ n z.1) z.2 z.2 - fderiv ℝ (Z z.1) z.2 z.2‖) with he4
  have m1 : ∀ n, AEMeasurable (e1 n) volume := fun n =>
    (continuous_const.mul ((hχ'.comp continuous_fst).abs.mul ((hφc n).sub hZ0).norm)).aemeasurable.ennreal_ofReal
  have m2 : ∀ n, AEMeasurable (e2 n) volume := fun n =>
    (continuous_const.mul ((hχ.comp continuous_fst).abs.mul ((hφt n).sub hZt).norm)).aemeasurable.ennreal_ofReal
  have m3 : ∀ n, AEMeasurable (e3 n) volume := fun n =>
    ((hχ.comp continuous_fst).abs.mul ((hφc n).sub hZ0).norm).aemeasurable.ennreal_ofReal
  have m4 : ∀ n, AEMeasurable (e4 n) volume := fun n =>
    ((hχ.comp continuous_fst).abs.mul ((hφy n).sub hZy).norm).aemeasurable.ennreal_ofReal
  have hle : ∀ n z, ‖pairT P v (cutTest (φ n)) z - pairT P v Z z‖ₑ ≤
      a z * e1 n z + a z * e2 n z + a z * e3 n z + a z * e4 n z := by
    intro n z
    refine (pairT_sub P v (cutTest (φ n)) Z z).trans ?_
    have k1 := cutTest_timeDerivative_sub_le (hφ n) hζ.smooth P z.1 z.2
    have k3 : ENNReal.ofReal ‖cutTest (φ n) z.1 z.2 - Z z.1 z.2‖ = e3 n z := by
      rw [he3]
      dsimp only
      rw [norm_cutTest_sub_le]
    have k4 : ENNReal.ofReal ‖fderiv ℝ (cutTest (φ n) z.1) z.2 z.2 - fderiv ℝ (Z z.1) z.2 z.2‖ = e4 n z := by
      rw [he4]
      dsimp only
      rw [cutTest_fderiv_apply_sub]
    rw [k3, k4]
    calc a z * ENNReal.ofReal (|1 / P| * ‖timeDerivative (cutTest (φ n)) z.1 z.2 - timeDerivative Z z.1 z.2‖)
          + a z * e3 n z + a z * e4 n z
        ≤ a z * (e1 n z + e2 n z) + a z * e3 n z + a z * e4 n z := by
          gcongr
      _ = a z * e1 n z + a z * e2 n z + a z * e3 n z + a z * e4 n z := by rw [mul_add]
  have hsplit : ∀ n, ∫⁻ z, (a z * e1 n z + a z * e2 n z + a z * e3 n z + a z * e4 n z) =
      (∫⁻ z, a z * e1 n z) + (∫⁻ z, a z * e2 n z) + (∫⁻ z, a z * e3 n z) + (∫⁻ z, a z * e4 n z) := by
    intro n
    have q1 : AEMeasurable (fun z => a z * e1 n z) volume := ha.mul (m1 n)
    have q2 : AEMeasurable (fun z => a z * e2 n z) volume := ha.mul (m2 n)
    have q3 : AEMeasurable (fun z => a z * e3 n z) volume := ha.mul (m3 n)
    have q12 : AEMeasurable (fun z => a z * e1 n z + a z * e2 n z) volume := q1.add q2
    have q123 : AEMeasurable (fun z => a z * e1 n z + a z * e2 n z + a z * e3 n z) volume := q12.add q3
    rw [lintegral_add_left' q123, lintegral_add_left' q12, lintegral_add_left' q1]
  have t1 : Tendsto (fun n => ∫⁻ z, a z * e1 n z) atTop (𝓝 0) := by
    refine mixed_bound_tendsto ha m1 ?_ hA (tendsto_ofReal_mul hm0 ((|1 / P| * Mc) ^ 2)) ?_
    · intro n z hz
      rw [he1]
      dsimp only
      rw [deriv_stripCutoff_eq_zero hz]
      simp
    · intro n
      refine mixed_le_scalar (e := e1 n) (f := fun s y => φ n s y - Z s y) (by positivity) (fun s y => ?_)
      rw [he1]
      dsimp only
      refine ENNReal.ofReal_le_ofReal ?_
      have h := hMc s
      have hx := norm_nonneg (φ n s y - Z s y)
      calc |1 / P| * (|deriv stripCutoff s| * ‖φ n s y - Z s y‖)
          = |1 / P| * |deriv stripCutoff s| * ‖φ n s y - Z s y‖ := by ring
        _ ≤ |1 / P| * Mc * ‖φ n s y - Z s y‖ := by gcongr
  have t2 : Tendsto (fun n => ∫⁻ z, a z * e2 n z) atTop (𝓝 0) := by
    refine mixed_bound_tendsto ha m2 ?_ hA (tendsto_ofReal_mul hm1 (|1 / P| ^ 2)) ?_
    · intro n z hz
      rw [he2]
      dsimp only
      rw [stripCutoff_eq_zero hz]
      simp
    · intro n
      refine mixed_le_scalar (e := e2 n) (f := fun s y => timeDerivative (φ n) s y - timeDerivative Z s y)
        (abs_nonneg _) (fun s y => ?_)
      rw [he2]
      dsimp only
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_stripCutoff_le s)
  have t3 : Tendsto (fun n => ∫⁻ z, a z * e3 n z) atTop (𝓝 0) := by
    refine mixed_bound_tendsto ha m3 ?_ hA (by simpa using tendsto_ofReal_mul hm0 (1 ^ 2)) ?_
    · intro n z hz
      rw [he3]
      dsimp only
      rw [stripCutoff_eq_zero hz]
      simp
    · intro n
      refine (mixed_le_scalar (e := e3 n) (f := fun s y => φ n s y - Z s y) zero_le_one (fun s y => ?_)).trans
        (by simp)
      rw [he3]
      dsimp only
      rw [one_mul]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (norm_nonneg _) (abs_stripCutoff_le s))
  have t4 : Tendsto (fun n => ∫⁻ z, a z * e4 n z) atTop (𝓝 0) := by
    refine mixed_bound_tendsto ha m4 ?_ hA (by simpa using tendsto_ofReal_mul hm3 (1 ^ 2)) ?_
    · intro n z hz
      rw [he4]
      dsimp only
      rw [stripCutoff_eq_zero hz]
      simp
    · intro n
      refine (mixed_le_scalar (e := e4 n) (f := fun s y => fderiv ℝ (φ n s) y y - fderiv ℝ (Z s) y y)
        zero_le_one (fun s y => ?_)).trans (by simp)
      rw [he4]
      dsimp only
      rw [one_mul]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (norm_nonneg _) (abs_stripCutoff_le s))
  refine ⟨hZint, pass_limit (ℓn := fun n => pairT P v (cutTest (φ n))) hZint
    (fun n => aesm_pairT hvm (continuous_test_timeDerivative (cutTest_isTest (hφ n)))
      (cutTest_isTest (hφ n)).1.continuous (continuous_test_fderiv_apply (cutTest_isTest (hφ n))))
    (B := fun n => ∫⁻ z, (a z * e1 n z + a z * e2 n z + a z * e3 n z + a z * e4 n z)) ?_
    (fun n => lintegral_mono fun z => hle n z)⟩
  simp_rw [hsplit]
  simpa using ((t1.add t2).add t3).add t4

theorem rightSide_integrand {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space)
    (v g : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (φ : ℝ → Space → Space)
    (z : ℝ × Space) :
    inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
        + ∑ i, (0 : Fin k → ℝ) i • b i z.1 z.2) (φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) =
      pairF g φ z + pairGW G W φ z + pairWv W v φ z + pairG G φ z := by
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, inner_add_left, pairF, pairGW,
    pairWv, pairG]

theorem limit_eq_of_eventually {u w : ℕ → ℝ} {a c : ℝ} (hu : Tendsto u atTop (𝓝 a))
    (hw : Tendsto w atTop (𝓝 c)) (h : ∀ᶠ n in atTop, u n = w n) : a = c :=
  tendsto_nhds_unique hu (hw.congr' (h.mono fun n hn => hn.symm))

theorem limit_identities {k : ℕ} {Γ : Set Symmetry} {P D C γ : ℝ} {W ζ : ℝ → Space → Space}
    {b : Fin k → ℝ → Space → Space} {v g F : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hW : IsFlowPiece W D) (hζ : IsAdjointField ζ C γ) (hv : IsPerturbation Γ P v G H g)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W b 0 v G g F)
    {φ : ℕ → ℝ → Space → Space} (hφ : ∀ n, IsSpaceTimeTestField (φ n))
    (h0 : Tendsto (fun n => ∫⁻ z : ℝ × Space,
      ENNReal.ofReal (‖φ n z.1 z.2 - timeCutoff windowBump ζ z.1 z.2‖ ^ 2)) atTop (𝓝 0))
    (hgrad : Tendsto (fun n => ∫⁻ z : ℝ × Space,
      ENNReal.ofReal (matSq (fderiv ℝ (φ n z.1) z.2 - fderiv ℝ (timeCutoff windowBump ζ z.1) z.2)))
        atTop (𝓝 0))
    (hm0 : Tendsto (fun n => mixedNorm (fun s y => φ n s y - timeCutoff windowBump ζ s y)) atTop (𝓝 0))
    (hm1 : Tendsto (fun n => mixedNorm (fun s y =>
      timeDerivative (φ n) s y - timeDerivative (timeCutoff windowBump ζ) s y)) atTop (𝓝 0))
    (hm3 : Tendsto (fun n => mixedNorm (fun s y =>
      fderiv ℝ (φ n s) y y - fderiv ℝ (timeCutoff windowBump ζ s) y y)) atTop (𝓝 0)) :
    Integrable (pairF F (timeCutoff windowBump ζ)) ∧ Integrable (pairF g (timeCutoff windowBump ζ)) ∧
    Integrable (pairGW G W (timeCutoff windowBump ζ)) ∧ Integrable (pairWv W v (timeCutoff windowBump ζ)) ∧
    Integrable (pairG G (timeCutoff windowBump ζ)) ∧ Integrable (pairT P v (timeCutoff windowBump ζ)) ∧
    (∫ z, pairF F (timeCutoff windowBump ζ) z) = (∫ z, pairF g (timeCutoff windowBump ζ) z)
      + (∫ z, pairGW G W (timeCutoff windowBump ζ) z) + (∫ z, pairWv W v (timeCutoff windowBump ζ) z)
      + (∫ z, pairG G (timeCutoff windowBump ζ) z) ∧
    (∫ z, pairT P v (timeCutoff windowBump ζ) z) = ∫ z, pairF g (timeCutoff windowBump ζ) z := by
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hD := flow_D_nonneg hW
  have LF := pass_value (p := pairF F) (a := fun z => ENNReal.ofReal ‖F z.1 z.2‖) hζ
    hFm.norm.aemeasurable.ennreal_ofReal (strip_square_lt_top hFp hF2) (pairF_sub F) (pairF_zero F)
    (fun ψ hψ => hFm.inner (𝕜 := ℝ) hψ.aestronglyMeasurable) hφ h0
  have Lg := pass_value (p := pairF g) (a := fun z => ENNReal.ofReal ‖g z.1 z.2‖) hζ
    hv.measurable_derivative.norm.aemeasurable.ennreal_ofReal
    (strip_square_lt_top hv.periodic_derivative hv.derivative_finite) (pairF_sub g) (pairF_zero g)
    (fun ψ hψ => hv.measurable_derivative.inner (𝕜 := ℝ) hψ.aestronglyMeasurable) hφ h0
  have hGs : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (Real.sqrt (matSq (G s y))) ^ 2 < ⊤ := by
    simp_rw [ofReal_sqrt_sq (entrySq_nonneg _)]
    exact strip_entrySq_lt_top hv
  have LGW := pass_value (p := pairGW G W)
    (a := fun z => ENNReal.ofReal (D * Real.sqrt (matSq (G z.1 z.2)))) hζ
    ((continuous_const.mul (Real.continuous_sqrt.comp continuous_entrySq)).comp_aestronglyMeasurable
      hv.measurable_gradient).aemeasurable.ennreal_ofReal
    (strip_const_mul_sq (fun s y => Real.sqrt_nonneg _) hGs)
    (pairGW_sub (fun σ y => (hW.decay σ y).1)) (pairGW_zero G W)
    (fun ψ hψ => (aesm_apply hv.measurable_gradient hWc.aestronglyMeasurable).inner (𝕜 := ℝ)
      hψ.aestronglyMeasurable) hφ h0
  have hWva : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (D * (‖v z.1 z.2‖ / (1 + ‖z.2‖)))) volume := by
    have hq : Continuous (fun p : ℝ × Space => D * (p.1 / (1 + ‖p.2‖))) :=
      continuous_const.mul (continuous_fst.div (continuous_const.add continuous_snd.norm)
        (fun p => (one_add_norm_pos p.2).ne'))
    have hm : AEStronglyMeasurable (fun z : ℝ × Space => D * (‖v z.1 z.2‖ / (1 + ‖z.2‖))) volume :=
      hq.comp_aestronglyMeasurable (hv.measurable_velocity.norm.prodMk continuous_snd.aestronglyMeasurable)
    exact hm.aemeasurable.ennreal_ofReal
  have LWv := pass_value (p := pairWv W v)
    (a := fun z => ENNReal.ofReal (D * (‖v z.1 z.2‖ / (1 + ‖z.2‖)))) hζ
    hWva
    (strip_const_mul_sq (fun s y => by positivity) (strip_inverseSquare_lt_top hv))
    (pairWv_sub (fun σ y => (hW.decay σ y).2)) (pairWv_zero W v)
    (fun ψ hψ => (aesm_apply (continuous_slice_fderiv hW.smooth).aestronglyMeasurable
      hv.measurable_velocity).inner (𝕜 := ℝ) hψ.aestronglyMeasurable) hφ h0
  have LG := pass_pairG hζ hv.measurable_gradient hGs hφ hgrad
  have LT := pass_pairT (P := P) hζ hv.measurable_velocity (strip_sixth_lt_top hv) hφ hm0 hm1 hm3
  refine ⟨LF.1, Lg.1, LGW.1, LWv.1, LG.1, LT.1, ?_, ?_⟩
  · refine limit_eq_of_eventually LF.2.2 (((Lg.2.2.add LGW.2.2).add LWv.2.2).add LG.2.2) ?_
    filter_upwards [Lg.2.1, LGW.2.1, LWv.2.1, LG.2.1] with n h1 h2 h3 h4
    have e := hR (cutTest (φ n)) (cutTest_isTest (hφ n))
    have e2 : ∫ z, pairF F (cutTest (φ n)) z = ∫ z, (pairF g (cutTest (φ n)) z + pairGW G W (cutTest (φ n)) z
        + pairWv W v (cutTest (φ n)) z + pairG G (cutTest (φ n)) z) := by
      refine e.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
      exact rightSide_integrand W b v g G (cutTest (φ n)) z
    have i12 : Integrable (fun z => pairF g (cutTest (φ n)) z + pairGW G W (cutTest (φ n)) z) := h1.add h2
    have i123 : Integrable (fun z => pairF g (cutTest (φ n)) z + pairGW G W (cutTest (φ n)) z
        + pairWv W v (cutTest (φ n)) z) := i12.add h3
    rw [e2, integral_add i123 h4, integral_add i12 h3, integral_add h1 h2]
  · refine limit_eq_of_eventually LT.2.2 Lg.2.2 ?_
    filter_upwards with n
    have e := hv.transport (cutTest (φ n)) (cutTest_isTestVector (hφ n))
    exact e

theorem integrable_mixed_of {v : ℝ → Space → Space} {h ε : ℝ × Space → ℝ}
    (hm : AEStronglyMeasurable h volume)
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, (∫⁻ y, ENNReal.ofReal ‖v s y‖ ^ (6 : ℝ)) ^ (1 / 3 : ℝ) < ⊤)
    (hεm : AEStronglyMeasurable ε volume) (hle : ∀ z, |h z| ≤ ‖v z.1 z.2‖ * ε z)
    {c p : ℝ} (hp : 5 / 2 < p) (hdec : ∀ z : ℝ × Space, ε z ≤ c / (1 + ‖z.2‖) ^ p)
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → ε z = 0) : Integrable h := by
  refine integrable_of_enorm_le hm (b := fun z => ENNReal.ofReal ‖v z.1 z.2‖ * ENNReal.ofReal (ε z))
    (fun z => ?_) ?_
  · rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    exact enorm_le_ofReal (hle z)
  · refine mixed_bound_lt_top hvm.norm.aemeasurable.ennreal_ofReal hεm.aemeasurable.ennreal_ofReal ?_ hA ?_
    · intro z hz'
      rw [hz z hz', ENNReal.ofReal_zero]
    · refine mixed_decay_lt_top (e := fun z : ℝ × Space => ENNReal.ofReal (ε z)) (c := c) (p := p) hp
        (fun z => ENNReal.ofReal_le_ofReal (hdec z)) ?_
      intro z hz'
      rw [hz z hz', ENNReal.ofReal_zero]

theorem integrable_sq_of {h α ε : ℝ × Space → ℝ}
    (hm : AEStronglyMeasurable h volume) (hαm : AEStronglyMeasurable α volume)
    (hA : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (α (s, y)) ^ 2 < ⊤)
    (hεm : AEStronglyMeasurable ε volume) (hα0 : ∀ z, 0 ≤ α z) (hle : ∀ z, |h z| ≤ α z * ε z)
    {c p : ℝ} (hp : 3 / 2 < p) (hdec : ∀ z : ℝ × Space, ε z ≤ c / (1 + ‖z.2‖) ^ p)
    (hz : ∀ z : ℝ × Space, z.1 ∉ Set.Icc (-2 : ℝ) 2 → ε z = 0) : Integrable h := by
  refine integrable_of_enorm_le hm (b := fun z => ENNReal.ofReal (α z) * ENNReal.ofReal (ε z))
    (fun z => ?_) ?_
  · rw [← ENNReal.ofReal_mul (hα0 z)]
    exact enorm_le_ofReal (hle z)
  · refine sq_bound_lt_top hαm.aemeasurable.ennreal_ofReal hεm.aemeasurable.ennreal_ofReal ?_ hA ?_
    · intro z hz'
      rw [hz z hz', ENNReal.ofReal_zero]
    · refine square_decay_lt_top (e := fun z : ℝ × Space => ENNReal.ofReal (ε z)) (c := c) (p := p) hp
        (fun z => ENNReal.ofReal_le_ofReal (hdec z)) ?_
      intro z hz'
      rw [hz z hz', ENNReal.ofReal_zero]

def unitWeight (s : ℝ) : ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s

theorem unitWeight_nonneg (s : ℝ) : 0 ≤ unitWeight s := by
  unfold unitWeight
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) s

theorem unitWeight_le_one (s : ℝ) : unitWeight s ≤ 1 := by
  unfold unitWeight
  exact Set.indicator_le_self' (fun _ _ => zero_le_one) s

theorem unitWeight_zero_off {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) : unitWeight s = 0 := by
  unfold unitWeight
  refine Set.indicator_of_notMem (fun h => hs ⟨by linarith [h.1], by linarith [h.2]⟩) _

theorem measurable_unitWeight : Measurable unitWeight :=
  measurable_const.indicator measurableSet_Icc

theorem slice_integrableOn {f : ℝ × Space → ℝ} (hf : Integrable (fun z => unitWeight z.1 * f z)) :
    IntegrableOn (fun s => ∫ y, f (s, y)) (Set.Icc (0 : ℝ) 1) := by
  have e : (fun z : ℝ × Space => unitWeight z.1 * f z) = Set.indicator (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) f := by
    funext z
    by_cases hz : z.1 ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem (Set.mk_mem_prod hz (Set.mem_univ _)), unitWeight,
        Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem (fun h => hz h.1), unitWeight, Set.indicator_of_notMem hz, zero_mul]
  rw [e, integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)] at hf
  have h2 : Integrable f ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure Space)), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    exact hf
  exact h2.integral_prod_left

theorem integral_weight_prod {f : ℝ × Space → ℝ} (c : ℝ → ℝ) (hf : Integrable (fun z => c z.1 * f z)) :
    ∫ z, c z.1 * f z = ∫ s, c s * ∫ y, f (s, y) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  rw [integral_prod _ hf]
  congr 1
  funext s
  exact integral_const_mul (c s) _

theorem timeDerivative_periodic {f : ℝ → Space → Space} (hf : IsTimePeriodic f) (s : ℝ) (y : Space) :
    timeDerivative f (s + 1) y = timeDerivative f s y := by
  unfold timeDerivative
  rw [← deriv_comp_add_const]
  congr 1
  funext t
  exact hf t y

theorem slice_periodic {f : ℝ → Space → Space} (hf : IsTimePeriodic f) (s : ℝ) : f (s + 1) = f s :=
  funext (hf s)

theorem inner_apply_transpose (K : Space →L[ℝ] Space) (w z : Space) :
    inner ℝ (K w) z = inner ℝ w (transposeApply K z) := by
  unfold transposeApply
  rw [inner_sum]
  conv_lhs => rw [← sum_unitVector w]
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [unitVector, EuclideanSpace.inner_single_right, mul_comm]

theorem pairSum_smul_right (A B : Space →L[ℝ] Space) (c : ℝ) : matInner A (c • B) = c * matInner A B := by
  simp [matInner, inner_smul_right, Finset.mul_sum]

theorem norm_transposeApply_le (K : Space →L[ℝ] Space) (z : Space) : ‖transposeApply K z‖ ≤ 3 * (‖K‖ * ‖z‖) := by
  unfold transposeApply
  calc ‖∑ i : Fin 3, inner ℝ (K (unitVector i)) z • unitVector i‖
      ≤ ∑ i : Fin 3, ‖inner ℝ (K (unitVector i)) z • unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖K‖ * ‖z‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        have := K.le_opNorm (unitVector i)
        rw [norm_unitVector, mul_one] at this
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = 3 * (‖K‖ * ‖z‖) := by simp

theorem combine_pointwise {P : ℝ} {W ζ v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hζ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (z : ℝ × Space) :
    pairT P v (timeCutoff windowBump ζ) z
      - windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))
      + pairWv W v (timeCutoff windowBump ζ) z + pairG G (timeCutoff windowBump ζ) z =
    windowBump z.1 * (inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2))
      - 1 / P * (deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2)) := by
  simp only [pairT, pairWv, pairG]
  rw [timeDerivative_cut hζ1, fderiv_cut hζ1,
    show timeCutoff windowBump ζ z.1 z.2 = windowBump z.1 • ζ z.1 z.2 from rfl]
  rw [inner_smul_right, inner_apply_transpose, pairSum_smul_right]
  simp only [adjointTransport, advectionShift, inner_add_right, inner_sub_right, inner_smul_right,
    inner_neg_right, ContinuousLinearMap.smul_apply, neg_smul]
  ring

theorem entrySq_slice_ae {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ s, s ∈ Set.Icc (-2 : ℝ) 2 → ∫⁻ y, ENNReal.ofReal (matSq (G s y)) < ⊤ := by
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) volume :=
    (continuous_entrySq.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable.ennreal_ofReal
  rw [Measure.volume_eq_prod] at hm
  have hm2 : AEMeasurable (fun s => ∫⁻ y, ENNReal.ofReal (matSq (G s y))) volume :=
    hm.lintegral_prod_right'
  have h := ae_lt_top' hm2.restrict (strip_entrySq_lt_top hv).ne
  exact (ae_restrict_iff' measurableSet_Icc).1 h

theorem convection_integral {Γ : Set Symmetry} {P D C γ : ℝ} {W ζ v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hW : IsFlowPiece W D) (hζ : IsAdjointField ζ C γ) (hv : IsPerturbation Γ P v G H g)
    (hint : Integrable (pairGW G W (timeCutoff windowBump ζ)))
    (hint9 : Integrable (fun z : ℝ × Space =>
      windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2)))) :
    ∫ z, pairGW G W (timeCutoff windowBump ζ) z =
      -∫ z : ℝ × Space, windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2)) := by
  have e : pairGW G W (timeCutoff windowBump ζ) =
      fun z => windowBump z.1 * inner ℝ (G z.1 z.2 (W z.1 z.2)) (ζ z.1 z.2) := by
    funext z
    rw [pairGW, show timeCutoff windowBump ζ z.1 z.2 = windowBump z.1 • ζ z.1 z.2 from rfl,
      inner_smul_right]
  rw [e] at hint ⊢
  rw [integral_weight_prod windowBump hint, integral_weight_prod windowBump hint9, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hv.weak_gradient, hv.sixth_power, entrySq_slice_ae hv] with s h1 h2 h3
  by_cases hs : s ∈ Set.Icc (-2 : ℝ) 2
  · have hWs : ContDiff ℝ 1 (W s) :=
      hW.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hζs : ContDiff ℝ 1 (ζ s) :=
      hζ.smooth.comp (contDiff_const.prodMk contDiff_id)
    have key := RepresentationParts.slice_convection_pairing (v := v s) (W := W s) (ζ := ζ s) (G := G s)
      h1 h2 (h3 hs) hWs (hW.divergence_free s) (fun y => (hW.decay s y).1) hζs hζ.rate_gt
      (fun y => ⟨(hζ.decay s y).1, (hζ.decay s y).2.2⟩)
    rw [key, mul_neg]
  · have h0 : windowBump s = 0 := windowBump_eq_zero (outside_window hs)
    simp [h0]

theorem continuous_adjointTransport {P D C γ : ℝ} {W ζ : ℝ → Space → Space} (hW : IsFlowPiece W D)
    (hζ : IsAdjointField ζ C γ) : Continuous (fun z : ℝ × Space => adjointTransport P W ζ z.1 z.2) := by
  have hζ0 : Continuous (fun z : ℝ × Space => ζ z.1 z.2) := hζ.smooth.continuous
  have hζt := continuous_timeDerivative hζ.smooth
  have hζd := continuous_slice_fderiv hζ.smooth
  have hWd := continuous_slice_fderiv hW.smooth
  have hW0 : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have htr : Continuous (fun z : ℝ × Space => transposeApply (fderiv ℝ (W z.1) z.2) (ζ z.1 z.2)) := by
    unfold transposeApply
    refine continuous_finsetSum _ fun i _ => ?_
    have hci : Continuous (fun z : ℝ × Space => inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector i)) (ζ z.1 z.2)) :=
      (hWd.clm_apply continuous_const).inner hζ0
    exact hci.smul continuous_const
  unfold adjointTransport advectionShift
  exact ((((hζt.const_smul (-(1 / P))).sub hζ0).sub ((hζd.clm_apply continuous_snd).const_smul (1 / 2 : ℝ))).add
    (htr.sub (hζd.clm_apply hW0)))

theorem adjointTransport_norm_le {P D C γ : ℝ} {W ζ : ℝ → Space → Space} (hW : IsFlowPiece W D)
    (hζ : IsAdjointField ζ C γ) (s : ℝ) (y : Space) :
    ‖adjointTransport P W ζ s y‖ ≤ (|1 / P| + 2 + 4 * D) * C / (1 + ‖y‖) ^ γ := by
  have hC := adjoint_C_nonneg hζ
  have hD := flow_D_nonneg hW
  have hγ0 : 0 ≤ γ := by linarith [hζ.rate_gt]
  set c := C / (1 + ‖y‖) ^ γ with hc_def
  have hc : 0 ≤ c := decay_nonneg hC γ y
  have h1 : ‖timeDerivative ζ s y‖ ≤ c := (hζ.decay s y).2.1
  have h0 : ‖ζ s y‖ ≤ c := (hζ.decay s y).1
  have hd : ‖fderiv ℝ (ζ s) y‖ ≤ c := (hζ.decay s y).2.2.trans (decay_succ_le hC γ hγ0 y)
  have hy : ‖fderiv ℝ (ζ s) y y‖ ≤ c := apply_self_le hC (hζ.decay s y).2.2
  have hWd : ‖fderiv ℝ (W s) y‖ ≤ D := by
    refine (hW.decay s y).2.trans ?_
    exact div_le_self hD (by linarith [norm_nonneg y])
  have htr : ‖transposeApply (fderiv ℝ (W s) y) (ζ s y)‖ ≤ 3 * (D * c) :=
    (norm_transposeApply_le _ _).trans (by gcongr)
  have hζW : ‖fderiv ℝ (ζ s) y (W s y)‖ ≤ c * D :=
    ((fderiv ℝ (ζ s) y).le_opNorm _).trans (mul_le_mul hd (hW.decay s y).1 (norm_nonneg _) hc)
  unfold adjointTransport advectionShift
  rw [mul_div_assoc, ← hc_def]
  calc ‖-(1 / P) • timeDerivative ζ s y - ζ s y - (1 / 2 : ℝ) • fderiv ℝ (ζ s) y y
        + (transposeApply (fderiv ℝ (W s) y) (ζ s y) - fderiv ℝ (ζ s) y (W s y))‖
      ≤ |1 / P| * ‖timeDerivative ζ s y‖ + ‖ζ s y‖ + 1 / 2 * ‖fderiv ℝ (ζ s) y y‖
        + (‖transposeApply (fderiv ℝ (W s) y) (ζ s y)‖ + ‖fderiv ℝ (ζ s) y (W s y)‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sub_le _ _))
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (le_of_eq ?_)) (le_of_eq ?_))
        · rw [norm_smul, norm_neg, Real.norm_eq_abs]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ |1 / P| * c + c + 1 / 2 * c + (3 * (D * c) + c * D) := by gcongr
    _ ≤ (|1 / P| + 2 + 4 * D) * c := by nlinarith

theorem weighted_integrabilities {Γ : Set Symmetry} {P D C γ : ℝ} {W ζ : ℝ → Space → Space}
    {v g F : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hW : IsFlowPiece W D) (hζ : IsAdjointField ζ C γ) (hv : IsPerturbation Γ P v G H g)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    Integrable (fun z : ℝ × Space => windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))) ∧
    Integrable (fun z : ℝ × Space => deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2)) ∧
    Integrable (fun z : ℝ × Space => unitWeight z.1 * inner ℝ (F z.1 z.2) (ζ z.1 z.2)) ∧
    Integrable (fun z : ℝ × Space => unitWeight z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2)) ∧
    Integrable (fun z : ℝ × Space => unitWeight z.1 * (inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2))) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_deriv_windowBump_le
  have hC := adjoint_C_nonneg hζ
  have hD := flow_D_nonneg hW
  have hγ := hζ.rate_gt
  have hζ0 : Continuous (fun z : ℝ × Space => ζ z.1 z.2) := hζ.smooth.continuous
  have hζd := continuous_slice_fderiv hζ.smooth
  have hW0 : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hψ : Continuous windowBump := windowBump_contDiff.continuous
  have hψ' : Continuous (deriv windowBump) := windowBump_contDiff.continuous_deriv (by simp)
  have hu : AEStronglyMeasurable (fun z : ℝ × Space => unitWeight z.1) volume :=
    (measurable_unitWeight.comp measurable_fst).aestronglyMeasurable
  have hvm := hv.measurable_velocity
  have hA6 := strip_sixth_lt_top hv
  have hadj := continuous_adjointTransport (P := P) hW hζ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine integrable_mixed_of (v := v) (ε := fun z => |windowBump z.1| * (‖fderiv ℝ (ζ z.1) z.2‖ * D))
      (((hψ.comp continuous_fst).aestronglyMeasurable).mul
        (hvm.inner (𝕜 := ℝ) (hζd.clm_apply hW0).aestronglyMeasurable)) hvm hA6
      ((hψ.comp continuous_fst).abs.mul (hζd.norm.mul continuous_const)).aestronglyMeasurable
      (fun z => ?_) (c := D * C) (p := γ + 1) (by linarith) (fun z => ?_) (fun z hz => ?_)
    · rw [abs_mul]
      calc |windowBump z.1| * |inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))|
          ≤ |windowBump z.1| * (‖v z.1 z.2‖ * (‖fderiv ℝ (ζ z.1) z.2‖ * D)) := by
            gcongr
            refine (abs_real_inner_le_norm _ _).trans ?_
            gcongr
            exact ((fderiv ℝ (ζ z.1) z.2).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hW.decay z.1 z.2).1 (norm_nonneg _))
        _ = ‖v z.1 z.2‖ * (|windowBump z.1| * (‖fderiv ℝ (ζ z.1) z.2‖ * D)) := by ring
    · calc |windowBump z.1| * (‖fderiv ℝ (ζ z.1) z.2‖ * D) ≤ 1 * (C / (1 + ‖z.2‖) ^ (γ + 1) * D) := by
            gcongr
            · exact abs_windowBump_le _
            · exact (hζ.decay z.1 z.2).2.2
        _ = D * C / (1 + ‖z.2‖) ^ (γ + 1) := by ring
    · rw [windowBump_eq_zero (outside_window hz), abs_zero, zero_mul]
  · refine integrable_mixed_of (v := v) (ε := fun z => |deriv windowBump z.1| * ‖ζ z.1 z.2‖)
      (((hψ'.comp continuous_fst).aestronglyMeasurable).mul (hvm.inner (𝕜 := ℝ) hζ0.aestronglyMeasurable))
      hvm hA6 ((hψ'.comp continuous_fst).abs.mul hζ0.norm).aestronglyMeasurable
      (fun z => ?_) (c := M * C) (p := γ) (by linarith) (fun z => ?_) (fun z hz => ?_)
    · rw [abs_mul]
      calc |deriv windowBump z.1| * |inner ℝ (v z.1 z.2) (ζ z.1 z.2)|
          ≤ |deriv windowBump z.1| * (‖v z.1 z.2‖ * ‖ζ z.1 z.2‖) := by
            gcongr
            exact abs_real_inner_le_norm _ _
        _ = ‖v z.1 z.2‖ * (|deriv windowBump z.1| * ‖ζ z.1 z.2‖) := by ring
    · calc |deriv windowBump z.1| * ‖ζ z.1 z.2‖ ≤ M * (C / (1 + ‖z.2‖) ^ γ) := by
            gcongr
            · exact hM _
            · exact (hζ.decay z.1 z.2).1
        _ = M * C / (1 + ‖z.2‖) ^ γ := by ring
    · rw [deriv_windowBump_eq_zero (outside_window hz), abs_zero, zero_mul]
  · refine integrable_sq_of (α := fun z => ‖F z.1 z.2‖) (ε := fun z => unitWeight z.1 * ‖ζ z.1 z.2‖)
      (hu.mul (hFm.inner (𝕜 := ℝ) hζ0.aestronglyMeasurable)) hFm.norm (strip_square_lt_top hFp hF2)
      (hu.mul hζ0.norm.aestronglyMeasurable) (fun z => norm_nonneg _) (fun z => ?_) (c := C) (p := γ)
      (by linarith) (fun z => ?_) (fun z hz => ?_)
    · rw [abs_mul, abs_of_nonneg (unitWeight_nonneg _)]
      calc unitWeight z.1 * |inner ℝ (F z.1 z.2) (ζ z.1 z.2)| ≤ unitWeight z.1 * (‖F z.1 z.2‖ * ‖ζ z.1 z.2‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (unitWeight_nonneg _)
        _ = ‖F z.1 z.2‖ * (unitWeight z.1 * ‖ζ z.1 z.2‖) := by ring
    · exact (mul_le_of_le_one_left (norm_nonneg _) (unitWeight_le_one _)).trans (hζ.decay z.1 z.2).1
    · rw [unitWeight_zero_off hz, zero_mul]
  · refine integrable_mixed_of (v := v) (ε := fun z => unitWeight z.1 * ‖ζ z.1 z.2‖)
      (hu.mul (hvm.inner (𝕜 := ℝ) hζ0.aestronglyMeasurable)) hvm hA6
      (hu.mul hζ0.norm.aestronglyMeasurable) (fun z => ?_) (c := C) (p := γ)
      (by linarith) (fun z => ?_) (fun z hz => ?_)
    · rw [abs_mul, abs_of_nonneg (unitWeight_nonneg _)]
      calc unitWeight z.1 * |inner ℝ (v z.1 z.2) (ζ z.1 z.2)| ≤ unitWeight z.1 * (‖v z.1 z.2‖ * ‖ζ z.1 z.2‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (unitWeight_nonneg _)
        _ = ‖v z.1 z.2‖ * (unitWeight z.1 * ‖ζ z.1 z.2‖) := by ring
    · exact (mul_le_of_le_one_left (norm_nonneg _) (unitWeight_le_one _)).trans (hζ.decay z.1 z.2).1
    · rw [unitWeight_zero_off hz, zero_mul]
  · have i1 : Integrable (fun z : ℝ × Space => unitWeight z.1 * inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)) := by
      refine integrable_mixed_of (v := v) (ε := fun z => unitWeight z.1 * ‖adjointTransport P W ζ z.1 z.2‖)
        (hu.mul (hvm.inner (𝕜 := ℝ) hadj.aestronglyMeasurable)) hvm hA6
        (hu.mul hadj.norm.aestronglyMeasurable) (fun z => ?_) (c := (|1 / P| + 2 + 4 * D) * C) (p := γ)
        (by linarith) (fun z => ?_) (fun z hz => ?_)
      · rw [abs_mul, abs_of_nonneg (unitWeight_nonneg _)]
        calc unitWeight z.1 * |inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)|
            ≤ unitWeight z.1 * (‖v z.1 z.2‖ * ‖adjointTransport P W ζ z.1 z.2‖) :=
              mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (unitWeight_nonneg _)
          _ = ‖v z.1 z.2‖ * (unitWeight z.1 * ‖adjointTransport P W ζ z.1 z.2‖) := by ring
      · exact (mul_le_of_le_one_left (norm_nonneg _) (unitWeight_le_one _)).trans
          (adjointTransport_norm_le hW hζ z.1 z.2)
      · rw [unitWeight_zero_off hz, zero_mul]
    have i2 : Integrable (fun z : ℝ × Space => unitWeight z.1 * matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2)) := by
      have hGs : ∫⁻ s in Set.Icc (-2 : ℝ) 2, ∫⁻ y, ENNReal.ofReal (Real.sqrt (matSq (G s y))) ^ 2 < ⊤ := by
        simp_rw [ofReal_sqrt_sq (entrySq_nonneg _)]
        exact strip_entrySq_lt_top hv
      refine integrable_sq_of (α := fun z => Real.sqrt (matSq (G z.1 z.2)))
        (ε := fun z => unitWeight z.1 * Real.sqrt (matSq (fderiv ℝ (ζ z.1) z.2)))
        (hu.mul (aesm_pairSum hv.measurable_gradient hζd.aestronglyMeasurable))
        ((Real.continuous_sqrt.comp continuous_entrySq).comp_aestronglyMeasurable hv.measurable_gradient)
        hGs (hu.mul (Real.continuous_sqrt.comp (continuous_entrySq.comp hζd)).aestronglyMeasurable)
        (fun z => Real.sqrt_nonneg _) (fun z => ?_) (c := 2 * C) (p := γ + 1) (by linarith)
        (fun z => ?_) (fun z hz => ?_)
      · rw [abs_mul, abs_of_nonneg (unitWeight_nonneg _)]
        calc unitWeight z.1 * |matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2)|
            ≤ unitWeight z.1 * (Real.sqrt (matSq (G z.1 z.2)) * Real.sqrt (matSq (fderiv ℝ (ζ z.1) z.2))) :=
              mul_le_mul_of_nonneg_left (abs_pairSum_le _ _) (unitWeight_nonneg _)
          _ = _ := by ring
      · refine (mul_le_of_le_one_left (Real.sqrt_nonneg _) (unitWeight_le_one _)).trans ?_
        refine (entrySq_root_le_two_norm _).trans ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hζ.decay z.1 z.2).2.2 (by norm_num)
      · rw [unitWeight_zero_off hz, zero_mul]
    exact (i1.add i2).congr (Filter.Eventually.of_forall fun z => by simp only [Pi.add_apply, mul_add])

theorem adjointTransport_periodic {P : ℝ} {W ζ : ℝ → Space → Space} (hW : IsTimePeriodic W)
    (hζ : IsTimePeriodic ζ) (s : ℝ) (y : Space) :
    adjointTransport P W ζ (s + 1) y = adjointTransport P W ζ s y := by
  unfold adjointTransport advectionShift
  rw [timeDerivative_periodic hζ, slice_periodic hζ, slice_periodic hW]

end Internal.Representation

open RepresentationParts

theorem representationHolds_of_density (h : TestFieldDensityHolds) : RepresentationHolds := by
  intro k Γ P D C γ β W ζ A b v g F G H hW hζ hA hv hFm hFp hF2 hR
  obtain ⟨φ, hφ, -, h0, hgrad, hm0, hm1, hm3⟩ :=
    h C γ β ζ A windowBump hζ hA windowBump_contDiff windowBump_hasCompactSupport
  obtain ⟨iF, -, iGW, iWv, iG, iT, I1, I2⟩ :=
    Internal.Representation.limit_identities hW hζ hv hFm hFp hF2 hR hφ h0 hgrad hm0 hm1 hm3
  obtain ⟨i9, iM, ia, im, ib⟩ := Internal.Representation.weighted_integrabilities (P := P) hW hζ hv hFm hFp hF2
  have hIBP := Internal.Representation.convection_integral hW hζ hv iGW i9
  set Z := timeCutoff windowBump ζ with hZ
  have i1 : Integrable (fun z : ℝ × Space => Internal.Representation.pairT P v Z z
      - windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))) := iT.sub i9
  have i2 : Integrable (fun z : ℝ × Space => Internal.Representation.pairT P v Z z
      - windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))
      + Internal.Representation.pairWv W v Z z) := i1.add iWv
  have i3 : Integrable (fun z : ℝ × Space => Internal.Representation.pairT P v Z z
      - windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))
      + Internal.Representation.pairWv W v Z z + Internal.Representation.pairG G Z z) := i2.add iG
  have iM' : Integrable (fun z : ℝ × Space =>
      1 / P * (deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2))) := iM.const_mul (1 / P)
  have iB : Integrable (fun z : ℝ × Space => windowBump z.1 * (inner ℝ (v z.1 z.2)
      (adjointTransport P W ζ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2))) := by
    refine (i3.add iM').congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    rw [Internal.Representation.combine_pointwise hζ.smooth z]
    ring
  have key : ∫ z, Internal.Representation.pairF F Z z =
      (∫ z : ℝ × Space, windowBump z.1 * (inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2)))
      - 1 / P * ∫ z : ℝ × Space, deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2) := by
    rw [I1, ← I2, hIBP]
    have e3 := integral_add i2 iG
    have e2 := integral_add i1 iWv
    have e1 := integral_sub iT i9
    have e4 : ∫ z : ℝ × Space, (Internal.Representation.pairT P v Z z
        - windowBump z.1 * inner ℝ (v z.1 z.2) (fderiv ℝ (ζ z.1) z.2 (W z.1 z.2))
        + Internal.Representation.pairWv W v Z z + Internal.Representation.pairG G Z z) =
        ∫ z : ℝ × Space, (windowBump z.1 * (inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)
          + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2))
          - 1 / P * (deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2))) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => Internal.Representation.combine_pointwise hζ.smooth z)
    have e5 := integral_sub iB iM'
    have e6 : ∫ z : ℝ × Space, 1 / P * (deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2)) =
        1 / P * ∫ z : ℝ × Space, deriv windowBump z.1 * inner ℝ (v z.1 z.2) (ζ z.1 z.2) :=
      integral_const_mul _ _
    rw [e6] at e5
    rw [← e4, e3, e2, e1] at e5
    linarith
  have eF : ∫ z, Internal.Representation.pairF F Z z =
      ∫ s, windowBump s * ∫ y, (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ζ z.1 z.2)) (s, y) := by
    have e : Internal.Representation.pairF F Z = fun z => windowBump z.1 * inner ℝ (F z.1 z.2) (ζ z.1 z.2) := by
      funext z
      rw [Internal.Representation.pairF, hZ, show timeCutoff windowBump ζ z.1 z.2 = windowBump z.1 • ζ z.1 z.2 from rfl,
        inner_smul_right]
    rw [e]
    rw [e] at iF
    exact Internal.Representation.integral_weight_prod windowBump iF
  rw [eF, Internal.Representation.integral_weight_prod windowBump iB, Internal.Representation.integral_weight_prod (deriv windowBump) iM] at key
  have pa : ∀ s, (fun s => ∫ y, (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ζ z.1 z.2)) (s, y)) (s + 1) =
      (fun s => ∫ y, (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ζ z.1 z.2)) (s, y)) s := by
    intro s
    simp only [hFp s, hζ.periodic s]
  have pb : ∀ s, (fun s => ∫ y, (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2)) (s, y)) (s + 1) =
      (fun s => ∫ y, (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (adjointTransport P W ζ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (ζ z.1) z.2)) (s, y)) s := by
    intro s
    simp only [hv.periodic_velocity s, hv.periodic_gradient s,
      Internal.Representation.adjointTransport_periodic hW.periodic hζ.periodic s, Internal.Representation.slice_periodic hζ.periodic s]
  have pm : ∀ s, (fun s => ∫ y, (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (ζ z.1 z.2)) (s, y)) (s + 1) =
      (fun s => ∫ y, (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (ζ z.1 z.2)) (s, y)) s := by
    intro s
    simp only [hv.periodic_velocity s, hζ.periodic s]
  rw [integral_windowBump_mul pa (Internal.Representation.slice_integrableOn ia),
    integral_windowBump_mul pb (Internal.Representation.slice_integrableOn ib),
    integral_deriv_windowBump_mul pm (Internal.Representation.slice_integrableOn im), mul_zero, sub_zero] at key
  exact key

end AdjointDefect

end Breakdown
