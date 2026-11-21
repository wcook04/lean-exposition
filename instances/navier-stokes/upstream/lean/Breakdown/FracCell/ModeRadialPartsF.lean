import Breakdown.FracCell.RelRadialCoef
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.ModeRadialLine
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.ModeGradSquare

open scoped ContDiff
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF

open SteadyCert Assembly CellAnalysis

lemma prim_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a t : ℝ} (hat : a ≤ t) :
    ∫ r in Ico a t, deriv ψ r = ψ t - ψ a := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hat]
  exact intervalIntegral.integral_deriv_eq_sub (fun x _ => (hψ.differentiable one_ne_zero) x)
    ((hψ.continuous_deriv le_rfl).intervalIntegrable _ _)

lemma line_ibp {a b : ℝ} (hab : a < b) (u h : ℝ → ℂ) (L : ℂ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψa : ψ a = 0) (hψb : ψ b = 0)
    (hhw : IntegrableOn (fun t => ((t - a : ℝ) : ℂ) * h t) (Icc a b))
    (hu : ∀ᵐ r ∂(volume.restrict (Icc a b)), u r = L - ∫ t in r..b, h t) :
    ∫ r in Icc a b, ((deriv ψ r : ℝ) : ℂ) * u r = -∫ r in Icc a b, ((ψ r : ℝ) : ℂ) * h r := by
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hdc.continuousOn
  have hhm : AEStronglyMeasurable h (volume.restrict (Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun t => ((t - a : ℝ) : ℂ)⁻¹ * (((t - a : ℝ) : ℂ) * h t))
        (volume.restrict (Icc a b)) :=
      ((Complex.measurable_ofReal.comp (measurable_id.sub_const a)).inv.aestronglyMeasurable).mul hhw.1
    refine h1.congr ?_
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
      rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae hne] with t ht
    have : ((t - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr ht
    field_simp
  set k : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p => ((deriv ψ p.1 : ℝ) : ℂ) * h p.2) with hk
  have hk_slice_t : ∀ t, (fun r => k (r, t)) = Set.indicator (Iio t) (fun r => ((deriv ψ r : ℝ) : ℂ) * h t) := by
    intro t; funext r; simp only [hk, Set.indicator, Set.mem_ofPred_eq, Set.mem_Iio]
  have hk_slice_r : ∀ r, (fun t => k (r, t)) = Set.indicator (Ioi r) (fun t => ((deriv ψ r : ℝ) : ℂ) * h t) := by
    intro r; funext t; simp only [hk, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi]
  have hkm : AEStronglyMeasurable k ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    exact ((Complex.continuous_ofReal.comp (hdc.comp continuous_fst)).aestronglyMeasurable).mul hhm.comp_snd
  have hwn : IntegrableOn (fun t => (t - a) * ‖h t‖) (Icc a b) := by
    refine IntegrableOn.congr_fun hhw.norm (fun t ht => ?_) measurableSet_Icc
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  have hdi : IntegrableOn (fun r => ((deriv ψ r : ℝ) : ℂ)) (Icc a b) :=
    (Complex.continuous_ofReal.comp hdc).integrableOn_Icc
  have hbound : ∀ t ∈ Icc a b, ∫ r, ‖k (r, t)‖ ∂(volume.restrict (Icc a b)) ≤ M * ((t - a) * ‖h t‖) := by
    intro t ht
    have e1 : (fun r => ‖k (r, t)‖) = Set.indicator (Iio t) (fun r => ‖((deriv ψ r : ℝ) : ℂ) * h t‖) := by
      funext r
      rw [show k (r, t) = _ from congrFun (hk_slice_t t) r]
      by_cases hr : r < t <;> simp [Set.indicator, hr]
    rw [e1, integral_indicator measurableSet_Iio]
    have hmem : ∀ᵐ r ∂((volume.restrict (Icc a b)).restrict (Iio t)), r ∈ Icc a b :=
      ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)
    calc ∫ r in Iio t, ‖((deriv ψ r : ℝ) : ℂ) * h t‖ ∂(volume.restrict (Icc a b))
        ≤ ∫ r in Iio t, M * ‖h t‖ ∂(volume.restrict (Icc a b)) := by
          refine integral_mono_ae ?_ (integrable_const _) ?_
          · refine Integrable.mono' (g := fun _ => M * ‖h t‖) (integrable_const _) ?_ ?_
            · exact ((Complex.continuous_ofReal.comp hdc).mul continuous_const).norm.aestronglyMeasurable
            · filter_upwards [hmem] with r hr
              rw [norm_norm, norm_mul, Complex.norm_real]
              exact mul_le_mul_of_nonneg_right (hM r hr) (norm_nonneg _)
          · filter_upwards [hmem] with r hr
            rw [norm_mul, Complex.norm_real]
            exact mul_le_mul_of_nonneg_right (hM r hr) (norm_nonneg _)
      _ = M * ((t - a) * ‖h t‖) := by
          have : Iio t ∩ Icc a b = Ico a t := by
            ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
            constructor
            · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
          rw [setIntegral_const, smul_eq_mul, Measure.real, Measure.restrict_apply measurableSet_Iio, this,
            Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.1)]
          ring
  have hkint : Integrable k ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
    rw [integrable_prod_iff' hkm]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · rw [hk_slice_t]
      exact (hdi.mul_const (h t)).indicator measurableSet_Iio
    · refine Integrable.mono' (hwn.const_mul M) ?_ ?_
      · have := hkm.norm.prod_swap.integral_prod_right'
        exact this
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hbound t ht
  have hswap := integral_integral_swap (μ := volume.restrict (Icc a b)) (ν := volume.restrict (Icc a b))
    (f := fun r t => k (r, t)) hkint
  have hL : ∀ r ∈ Icc a b, ∫ t, k (r, t) ∂(volume.restrict (Icc a b)) =
      ((deriv ψ r : ℝ) : ℂ) * ∫ t in r..b, h t := by
    intro r hr
    have hs : Ioi r ∩ Icc a b = Ioc r b := by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hr.1], h2⟩
    rw [hk_slice_r, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hs,
      integral_const_mul, intervalIntegral.integral_of_le hr.2]
  have hR : ∀ t ∈ Icc a b, ∫ r, k (r, t) ∂(volume.restrict (Icc a b)) = ((ψ t : ℝ) : ℂ) * h t := by
    intro t ht
    rw [hk_slice_t, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      integral_mul_const]
    congr 1
    have : Iio t ∩ Icc a b = Ico a t := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
    rw [this, integral_complex_ofReal, prim_eq hψ ht.1, hψa, sub_zero]
  have h0 : ∫ r in Icc a b, ((deriv ψ r : ℝ) : ℂ) = 0 := by
    rw [integral_complex_ofReal, integral_Icc_eq_integral_Ico, prim_eq hψ hab.le, hψa, hψb]; simp
  have h0L : ∫ r in Icc a b, L * ((deriv ψ r : ℝ) : ℂ) = 0 := by
    rw [integral_const_mul]
    convert mul_zero L using 2
  calc ∫ r in Icc a b, ((deriv ψ r : ℝ) : ℂ) * u r
      = ∫ r in Icc a b, (L * ((deriv ψ r : ℝ) : ℂ) - ∫ t, k (r, t) ∂(volume.restrict (Icc a b))) := by
        refine integral_congr_ae ?_
        filter_upwards [hu, ae_restrict_mem measurableSet_Icc] with r hr hr'
        rw [hr, hL r hr']; ring
    _ = -∫ t, ∫ r, k (r, t) ∂(volume.restrict (Icc a b)) ∂(volume.restrict (Icc a b)) := by
        rw [integral_sub (hdi.const_mul L) hkint.integral_prod_left, h0L, zero_sub, hswap]
    _ = -∫ r in Icc a b, ((ψ r : ℝ) : ℂ) * h r := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc hR

lemma mul_weight {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {f : ℝ × ℝ → ℂ} {w c : ℝ × ℝ → ℝ}
    (hw : Measurable w) (hw0 : ∀ p ∈ S, 0 ≤ w p) (hW : IntegrableOn (fun p => (w p : ℂ) * f p) S)
    (hc : AEStronglyMeasurable c (volume.restrict S)) {C : ℝ} (hC : ∀ p ∈ S, |c p| ≤ C * w p) :
    IntegrableOn (fun p => (c p : ℂ) * f p) S := by
  have hβ : AEStronglyMeasurable (fun p => ((c p / w p : ℝ) : ℂ)) (volume.restrict S) :=
    (Complex.measurable_ofReal.comp_aemeasurable (hc.aemeasurable.div hw.aemeasurable)).aestronglyMeasurable
  have hb : ∀ p ∈ S, ‖((c p / w p : ℝ) : ℂ)‖ ≤ max C 0 := by
    intro p hp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    rcases (hw0 p hp).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [abs_of_pos h, div_le_iff₀ h]
      exact (hC p hp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h.le)
  refine (Integrable.bdd_mul (c := max C 0) hW hβ ((ae_restrict_iff' hS).2 (Eventually.of_forall hb))).congr ?_
  refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
  rcases (hw0 p hp).eq_or_lt with h | h
  · have h0 : c p = 0 := by
      have := hC p hp
      rw [← h, mul_zero] at this
      exact abs_nonpos_iff.mp this
    simp [h0, ← h]
  · have : (w p : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast
    field_simp

lemma cyl_shift (r θ z c : ℝ) :
    CellAnalysis.cylPoint r θ z + EuclideanSpace.single 2 c = CellAnalysis.cylPoint r θ (z + c) := by
  ext i
  fin_cases i <;> simp [CellAnalysis.cylPoint]

lemma gm_shift (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (c r z : ℝ) :
    gradMode m n (fun y => G (y + EuclideanSpace.single 2 c)) a b (r, z) = gradMode m n G a b (r, z + c) := by
  simp only [gradMode, modeMat, cyl_shift]

lemma lw_meas (K : CellBox) : Measurable (fun p : ℝ × ℝ => K.lineWeight p.1) := by
  unfold CellBox.lineWeight
  split_ifs
  · exact measurable_fst
  · exact measurable_const

lemma lw_nonneg {r₁ r₂ z₁ z₂ : ℝ} (h1 : 0 ≤ r₁) {r : ℝ} (hr : r₁ ≤ r) :
    0 ≤ (CellBox.mk r₁ r₂ z₁ z₂).lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · exact h1.trans hr
  · exact zero_le_one

lemma lw_bound {r₁ r₂ z₁ z₂ : ℝ} (h1 : 0 ≤ r₁) {r : ℝ} (hr : r ∈ Icc r₁ r₂) :
    r ≤ max 1 r₂ * (CellBox.mk r₁ r₂ z₁ z₂).lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_mul_of_one_le_left (h1.trans hr.1) (le_max_left _ _)
  · rw [mul_one]; exact hr.2.trans (le_max_right _ _)

lemma wgm_int {m : ℕ} {n : ℤ} {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (a b : Fin 3) {r₁ r₂ z₁ z₂ : ℝ} (h1 : 0 ≤ r₁)
    (h12 : r₁ < r₂) (hz : z₁ < z₂) :
    IntegrableOn (fun p : ℝ × ℝ => ((CellBox.mk r₁ r₂ z₁ z₂).lineWeight p.1 : ℂ) * gradMode m n G a b p)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  have hG1' : AEStronglyMeasurable (fun y => G (y + EuclideanSpace.single 2 z₁)) volume :=
    hG1.comp_measurePreserving (measurePreserving_add_right volume _)
  have hG2' : Integrable (fun y => entrySq ((fun y => G (y + EuclideanSpace.single 2 z₁)) y)) :=
    hG2.comp_add_right _
  have hK' : IsCellBox (CellBox.mk r₁ r₂ 0 (z₂ - z₁)) := ⟨⟨h1, h12⟩, ⟨le_rfl, by simp only; linarith⟩⟩
  have h := LowEntry.Internal.gradMode_int _ hK' m n hG1' hG2' a b
  have e : (fun p : ℝ × ℝ => ((CellBox.mk r₁ r₂ 0 (z₂ - z₁)).lineWeight p.1 : ℂ) *
      gradMode m n (fun y => G (y + EuclideanSpace.single 2 z₁)) a b p) =
      (fun p : ℝ × ℝ => ((CellBox.mk r₁ r₂ z₁ z₂).lineWeight p.1 : ℂ) * gradMode m n G a b p) ∘
        (fun p => p + ((0 : ℝ), z₁)) := by
    funext ⟨r, z⟩
    simp only [Function.comp, Prod.mk_add_mk, add_zero, gm_shift]
    rfl
  have hpre : (fun p : ℝ × ℝ => p + ((0 : ℝ), z₁)) ⁻¹' (Icc r₁ r₂ ×ˢ Icc z₁ z₂) =
      (CellBox.mk r₁ r₂ 0 (z₂ - z₁)).rect := by
    ext ⟨r, z⟩
    simp only [mem_preimage, mem_prod, mem_Icc, Prod.mk_add_mk, add_zero, CellBox.rect]
    constructor <;> intro hh <;> refine ⟨hh.1, ?_, ?_⟩ <;> linarith [hh.2.1, hh.2.2]
  rw [← hpre, e] at h
  exact ((measurePreserving_add_right volume ((0 : ℝ), z₁)).integrableOn_comp_preimage
    (measurableEmbedding_addRight _)).1 h

lemma part_one {m : ℕ} {n : ℤ} {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (a : Fin 3) {r₁ r₂ z₁ z₂ : ℝ} (h1 : 0 ≤ r₁)
    (h12 : r₁ < r₂) (hz : z₁ < z₂) (c : ℝ × ℝ → ℝ) (hc : ContinuousOn c (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (M : ℝ) (hM : ∀ p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂, |c p| ≤ M * p.1) :
    IntegrableOn (fun p : ℝ × ℝ => (c p : ℂ) * gradMode m n G a 0 p) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  have hS : MeasurableSet (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  refine mul_weight hS (lw_meas (CellBox.mk r₁ r₂ z₁ z₂)) (fun p hp => lw_nonneg h1 hp.1.1)
    (wgm_int hG1 hG2 a 0 h1 h12 hz) (hc.aestronglyMeasurable hS) (C := max M 0 * max 1 r₂) ?_
  intro p hp
  have hp0 : 0 ≤ p.1 := h1.trans hp.1.1
  calc |c p| ≤ M * p.1 := hM p hp
    _ ≤ max M 0 * p.1 := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
    _ ≤ max M 0 * (max 1 r₂ * (CellBox.mk r₁ r₂ z₁ z₂).lineWeight p.1) :=
        mul_le_mul_of_nonneg_left (lw_bound h1 hp.1) (le_max_right _ _)
    _ = _ := by ring

lemma slice_of {f : ℝ × ℝ → ℂ} {r₁ r₂ z₁ z₂ : ℝ} (hf : IntegrableOn f (Icc r₁ r₂ ×ˢ Icc z₁ z₂)) :
    ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), IntegrableOn (fun r => f (r, z)) (Icc r₁ r₂) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.prod_left_ae

lemma psi_bound {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {r₁ r₂ : ℝ} (hψ1 : ψ r₁ = 0) :
    ∃ M, ∀ r ∈ Icc r₁ r₂, |ψ r| ≤ M * (r - r₁) := by
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc r₁ r₂) hdc.continuousOn
  refine ⟨M, fun r hr => ?_⟩
  have e : ψ r = ∫ x in r₁..r, deriv ψ x := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => (hψ.differentiable one_ne_zero) x)
      (hdc.intervalIntegrable _ _), hψ1, sub_zero]
  rw [e, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r₁) (b := r) (C := M) (f := deriv ψ)
    (fun x hx => by
      rw [uIoc_of_le hr.1] at hx
      exact hM x ⟨hx.1.le, hx.2.trans hr.2⟩)
  rwa [abs_of_nonneg (sub_nonneg.mpr hr.1)] at this

end Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis Internal.ModeRadialPartsF

def ModeVecRectIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space), AEStronglyMeasurable v volume → MemLp v 6 volume →
    ∀ (n : ℤ) (a : Fin 3) (r₁ r₂ z₁ z₂ : ℝ), 0 ≤ r₁ →
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)

def ModeRadialFormulaStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable v volume → MemLp v 6 volume → AEStronglyMeasurable G volume →
    Integrable (fun y => entrySq (G y)) → IsWeakGradientOf v G →
    ∀ (n : ℤ) (a : Fin 3) (r₁ r₂ z₁ z₂ : ℝ), 0 ≤ r₁ → r₁ < r₂ → z₁ < z₂ →
      ∀ᵐ z ∂(volume.restrict (Set.Icc z₁ z₂)), ∃ L : ℂ, ∀ᵐ r ∂(volume.restrict (Set.Icc r₁ r₂)),
        modeVec m n v r z a = L - ∫ t in r..r₂, gradMode m n G a 0 (t, z)

theorem modeRadialParts_of (hV : ModeVecRectIntegrableStatement) (hF : ModeRadialFormulaStatement) :
    ModeRadialPartsStatement := by
  intro m v G hv1 hv6 hG1 hG2 hweak n a r₁ r₂ z₁ z₂ h1 h12 hz
  have hS : MeasurableSet (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hcr : ContinuousOn (fun p : ℝ × ℝ => p.1) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := continuousOn_fst
  refine ⟨fun g q hg hq => ?_, ?_⟩
  · obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
    obtain ⟨Mq, hMq⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc z₁ z₂) hq.continuousOn
    refine part_one hG1 hG2 a h1 h12 hz (fun p => p.1 * g p.1 * q p.2)
      ((hcr.mul (hg.comp continuousOn_fst (fun p hp => hp.1))).mul (hq.comp continuous_snd).continuousOn)
      (Mg * Mq) (fun p hp => ?_)
    have hp0 : 0 ≤ p.1 := h1.trans hp.1.1
    have hg' := hMg p.1 hp.1
    have hq' := hMq p.2 hp.2
    rw [Real.norm_eq_abs] at hg' hq'
    rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans hg'
    calc p.1 * |g p.1| * |q p.2| ≤ p.1 * Mg * Mq := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hg' hp0) hq' (abs_nonneg _) (mul_nonneg hp0 hMg0)
      _ = Mg * Mq * p.1 := by ring
  intro ψ q hψ hq hψ1 hψ2
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨Mψ, hMψ⟩ := psi_bound (r₂ := r₂) hψ hψ1
  obtain ⟨Mq, hMq⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc z₁ z₂) hq.continuousOn
  obtain ⟨Md, hMd⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc r₁ r₂) hdc.continuousOn
  have hMψ0 : 0 ≤ Mψ := by
    have := hMψ r₂ ⟨h12.le, le_rfl⟩
    by_contra hneg
    push Not at hneg
    have : Mψ * (r₂ - r₁) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
    linarith [abs_nonneg (ψ r₂)]
  have hMq0 : 0 ≤ Mq := (norm_nonneg _).trans (hMq z₁ ⟨le_rfl, hz.le⟩)
  have hMV := hV m v hv1 hv6 n a r₁ r₂ z₁ z₂ h1
  have hT : IntegrableOn (fun p : ℝ × ℝ => ((p.1 - r₁ : ℝ) : ℂ) * gradMode m n G a 0 p)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) :=
    part_one hG1 hG2 a h1 h12 hz (fun p => p.1 - r₁) (hcr.sub continuousOn_const) 1 (fun p hp => by
      rw [abs_of_nonneg (sub_nonneg.mpr hp.1.1)]; linarith)
  have hA0 : IntegrableOn (fun p : ℝ × ℝ => ((ψ p.1 : ℝ) : ℂ) * gradMode m n G a 0 p)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) :=
    part_one hG1 hG2 a h1 h12 hz (fun p => ψ p.1) (hψ.continuous.comp continuous_fst).continuousOn Mψ
      (fun p hp => (hMψ p.1 hp.1).trans (mul_le_mul_of_nonneg_left (by linarith) hMψ0))
  have hA : IntegrableOn (fun p : ℝ × ℝ => ((ψ p.1 * q p.2 : ℝ) : ℂ) * gradMode m n G a 0 p)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
    refine part_one hG1 hG2 a h1 h12 hz (fun p => ψ p.1 * q p.2)
      ((hψ.continuous.comp continuous_fst).mul (hq.comp continuous_snd)).continuousOn (Mψ * Mq) (fun p hp => ?_)
    have hq' := hMq p.2 hp.2
    rw [Real.norm_eq_abs] at hq'
    rw [abs_mul]
    calc |ψ p.1| * |q p.2| ≤ (Mψ * p.1) * Mq := by
          apply mul_le_mul ((hMψ p.1 hp.1).trans (mul_le_mul_of_nonneg_left (by linarith) hMψ0)) hq'
            (abs_nonneg _) (mul_nonneg hMψ0 (h1.trans hp.1.1))
      _ = Mψ * Mq * p.1 := by ring
  have hB0 : IntegrableOn (fun p : ℝ × ℝ => ((deriv ψ p.1 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
    refine Integrable.bdd_mul (c := Md) hMV
      ((Complex.continuous_ofReal.comp (hdc.comp continuous_fst)).aestronglyMeasurable)
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_))
    rw [Complex.norm_real]; exact hMd p.1 hp.1
  have hB : IntegrableOn (fun p : ℝ × ℝ => ((deriv ψ p.1 * q p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
    refine Integrable.bdd_mul (c := Md * Mq) hMV
      ((Complex.continuous_ofReal.comp ((hdc.comp continuous_fst).mul (hq.comp continuous_snd))).aestronglyMeasurable)
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_))
    rw [Complex.norm_real, norm_mul]
    exact mul_le_mul (hMd p.1 hp.1) (hMq p.2 hp.2) (norm_nonneg _) ((norm_nonneg _).trans (hMd p.1 hp.1))
  have hsum : ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, (((deriv ψ p.1 * q p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a +
      ((ψ p.1 * q p.2 : ℝ) : ℂ) * gradMode m n G a 0 p) = 0 := by
    have hI : Integrable (fun p : ℝ × ℝ => ((deriv ψ p.1 * q p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a +
        ((ψ p.1 * q p.2 : ℝ) : ℂ) * gradMode m n G a 0 p)
        ((volume.restrict (Icc r₁ r₂)).prod (volume.restrict (Icc z₁ z₂))) := by
      have h' := hB.add hA
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h'
      exact h'
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hI]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [slice_of hT, slice_of hA0, slice_of hB0, hF m v G hv1 hv6 hG1 hG2 hweak n a r₁ r₂ z₁ z₂ h1 h12 hz]
      with z hTz hAz hBz hLz
    obtain ⟨L, hL⟩ := hLz
    have e : (fun r => ((deriv ψ (r, z).1 * q (r, z).2 : ℝ) : ℂ) * modeVec m n v (r, z).1 (r, z).2 a +
        ((ψ (r, z).1 * q (r, z).2 : ℝ) : ℂ) * gradMode m n G a 0 (r, z)) =
        fun r => (q z : ℂ) * (((deriv ψ r : ℝ) : ℂ) * modeVec m n v r z a +
          ((ψ r : ℝ) : ℂ) * gradMode m n G a 0 (r, z)) := by
      funext r; push_cast; ring
    rw [e, integral_const_mul, integral_add hBz hAz,
      line_ibp h12 (fun r => modeVec m n v r z a) (fun t => gradMode m n G a 0 (t, z)) L ψ hψ hψ1 hψ2 hTz hL]
    simp
  rw [integral_add hB hA] at hsum
  exact (eq_neg_of_add_eq_zero_right hsum)

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF

open SteadyCert Assembly CellAnalysis

def frameForm (a : Fin 3) (p : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  p.1 • ![EuclideanSpace.proj (0 : Fin 3), EuclideanSpace.proj (1 : Fin 3), 0] a +
  p.2 • ![EuclideanSpace.proj (1 : Fin 3), -EuclideanSpace.proj (0 : Fin 3), 0] a +
  ![0, 0, EuclideanSpace.proj (2 : Fin 3)] a

lemma frameForm_smooth (a : Fin 3) : ContDiff ℝ ∞ (frameForm a) := by
  unfold frameForm
  exact ((contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)).add contDiff_const

lemma frameVec_eq_form (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ u a = frameForm a (Real.cos θ, Real.sin θ) u := by
  fin_cases a <;>
    simp [frameVec, frameForm, radialUnit, angularUnit, axialUnit, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

lemma frameMat_eq_form (θ : ℝ) (M : Space →L[ℝ] Space) (a : Fin 3) :
    frameMat θ M a 0 = frameForm a (Real.cos θ, Real.sin θ) (M (radialUnit θ)) := by
  rw [← frameVec_eq_form]
  fin_cases a <;> rfl

lemma col_loc {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hG1
  have h2 : MemLp (fun y => G y (unitVector j)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 (hG2.mono' (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold entrySq
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
  exact h2.locallyIntegrable (by norm_num)

lemma weak_plane {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hv6 : MemLp v 6 volume) (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (hw : IsWeakGradientOf v G) (n : ℤ) (a : Fin 3)
    (Ψ : ℝ × ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ) (hΨp : ∀ p ∈ tsupport Ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
      -∫ p, ((Ψ p : ℝ) : ℂ) * gradMode m n G a 0 p := by
  have h := (cylModeWeak Space v G (hv6.locallyIntegrable (by norm_num)) (col_loc hG1 hG2) hw
    (frameForm a) (frameForm_smooth a) m n Ψ hΨ hΨc hΨp).1
  have e1 : (fun p : ℝ × ℝ => ((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameForm a (Real.cos θ, Real.sin θ) (v (cylPoint p.1 θ p.2)) : ℂ)) := by
    funext p
    simp only [modeVec, frameVec_eq_form]
    ring
  have e2 : (fun p : ℝ × ℝ => ((Ψ p : ℝ) : ℂ) * gradMode m n G a 0 p) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((Ψ p : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameForm a (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ)) := by
    funext p
    simp only [gradMode, modeMat, frameMat_eq_form]
    ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h]
  ring

open ModeRadialLineInternal in
lemma test_smooth (k : ℕ) (x y : ℝ) : ContDiff ℝ ∞ (test k x y) := by
  have hs : ContDiff ℝ ∞ (step k) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun s => (step_hasDeriv k s).differentiableAt, ?_⟩
    rw [show deriv (step k) = kern k from funext fun s => (step_hasDeriv k s).deriv]
    exact ContDiffBump.contDiff_normed _
  exact (hs.comp (contDiff_id.sub contDiff_const)).sub (hs.comp (contDiff_id.sub contDiff_const))

open ModeRadialLineInternal in
lemma test_gm_int {m : ℕ} {n : ℤ} {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (a : Fin 3) {r₁ r₂ Z₁ Z₂ : ℝ} (h1 : 0 ≤ r₁)
    (h12 : r₁ < r₂) (hZ : Z₁ < Z₂) (k : ℕ) (x y x' : ℝ) (hx' : 0 < x')
    (hT0 : ∀ r, r < x' → test k x y r = 0) (χ : ℝ → ℝ) (hχ : Continuous χ) :
    IntegrableOn (fun p : ℝ × ℝ => ((test k x y p.1 * χ p.2 : ℝ) : ℂ) * gradMode m n G a 0 p)
      (Icc r₁ r₂ ×ˢ Icc Z₁ Z₂) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc Z₁ Z₂) hχ.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB Z₁ ⟨le_rfl, hZ.le⟩)
  refine part_one hG1 hG2 a h1 h12 hZ _
    (((test_cont k x y).comp continuous_fst).mul (hχ.comp continuous_snd)).continuousOn (2 * B / x')
    (fun p hp => ?_)
  rcases lt_or_ge p.1 x' with h | h
  · rw [hT0 p.1 h, zero_mul, abs_zero]
    exact mul_nonneg (div_nonneg (by positivity) hx'.le) (h1.trans hp.1.1)
  · rw [abs_mul]
    have hb := hB p.2 hp.2
    rw [Real.norm_eq_abs] at hb
    calc |test k x y p.1| * |χ p.2| ≤ 2 * B := mul_le_mul (abs_test_le k x y p.1) hb (abs_nonneg _) (by norm_num)
      _ ≤ 2 * B / x' * p.1 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hx']
          exact mul_le_mul_of_nonneg_left h (by positivity)

open ModeRadialLineInternal in
lemma dtest_mv_int {m : ℕ} {n : ℤ} {v : Space → Space} (hV : ModeVecRectIntegrableStatement)
    (hv1 : AEStronglyMeasurable v volume) (hv6 : MemLp v 6 volume) (a : Fin 3) {r₁ r₂ Z₁ Z₂ : ℝ}
    (h1 : 0 ≤ r₁) (k : ℕ) (x y : ℝ) (χ : ℝ → ℝ) (hχ : Continuous χ) :
    IntegrableOn (fun p : ℝ × ℝ => ((deriv (test k x y) p.1 * χ p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a)
      (Icc r₁ r₂ ×ˢ Icc Z₁ Z₂) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc Z₁ Z₂) hχ.continuousOn
  obtain ⟨C, hC⟩ := test_deriv_bound k x y
  refine Integrable.bdd_mul (c := C * B) (hV m v hv1 hv6 n a r₁ r₂ Z₁ Z₂ h1)
    ((Complex.continuous_ofReal.comp (((test_deriv_cont k x y).comp continuous_fst).mul
      (hχ.comp continuous_snd))).aestronglyMeasurable)
    ((ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (Eventually.of_forall fun p hp => ?_))
  rw [Complex.norm_real, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hC p.1) (hB p.2 hp.2) (norm_nonneg _) ((abs_nonneg _).trans (hC p.1))

lemma prod_eq {r₁ r₂ Z₁ Z₂ : ℝ} :
    volume.restrict (Icc r₁ r₂ ×ˢ Icc Z₁ Z₂) = (volume.restrict (Icc r₁ r₂)).prod (volume.restrict (Icc Z₁ Z₂)) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

open ModeRadialLineInternal in
lemma test_slice {m : ℕ} {n : ℤ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hV : ModeVecRectIntegrableStatement) (hv1 : AEStronglyMeasurable v volume) (hv6 : MemLp v 6 volume)
    (hG1 : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y)))
    (hw : IsWeakGradientOf v G) (a : Fin 3) {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h12 : r₁ < r₂) (k : ℕ) {x y : ℝ}
    (hx1 : r₁ < x - width k) (hx2 : x + width k < r₂) (hy1 : r₁ < y - width k) (hy2 : y + width k < r₂) :
    ∀ᵐ z ∂(volume : Measure ℝ), ∫ r in Icc r₁ r₂, (((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
      ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z)) = 0 := by
  have hwk := width_pos k
  have hmin : r₁ + width k < min x y := lt_min (by linarith) (by linarith)
  have hx'0 : 0 < min x y - width k := by linarith
  have hT0 : ∀ r, r < min x y - width k → test k x y r = 0 := fun r hr =>
    test_left k (by linarith [min_le_left x y]) (by linarith [min_le_right x y])
  have hT1 : ∀ r, r₂ ≤ r → test k x y r = 0 := fun r hr => test_right k (by linarith) (by linarith)
  have hmx : min x y ≤ x := min_le_left x y
  have hmy : min x y ≤ y := min_le_right x y
  have hdT : ∀ r, (r < min x y - width k ∨ r₂ ≤ r) → deriv (test k x y) r = 0 := by
    intro r hr
    rw [test_deriv]
    rcases hr with hr | hr
    · rw [kern_zero k (t := r - x) ?_, kern_zero k (t := r - y) ?_, sub_zero]
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    · rw [kern_zero k (t := r - x) ?_, kern_zero k (t := r - y) ?_, sub_zero]
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have hFint : ∀ Z₁ Z₂ : ℝ, Z₁ < Z₂ → ∀ χ : ℝ → ℝ, Continuous χ →
      IntegrableOn (fun p : ℝ × ℝ => ((deriv (test k x y) p.1 * χ p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a +
        ((test k x y p.1 * χ p.2 : ℝ) : ℂ) * gradMode m n G a 0 p) (Icc r₁ r₂ ×ˢ Icc Z₁ Z₂) :=
    fun Z₁ Z₂ hZ χ hχ => (dtest_mv_int hV hv1 hv6 a h1 k x y χ hχ).add
      (test_gm_int hG1 hG2 a h1 h12 hZ k x y _ hx'0 hT0 χ hχ)
  have hΦI : ∀ Z₁ Z₂ : ℝ, Z₁ < Z₂ → IntegrableOn (fun z => ∫ r in Icc r₁ r₂,
      (((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z))) (Icc Z₁ Z₂) := by
    intro Z₁ Z₂ hZ
    have h := (hFint Z₁ Z₂ hZ (fun _ => 1) continuous_const)
    rw [IntegrableOn, prod_eq] at h
    have h2 := h.integral_prod_right
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only [mul_one]
  have hloc : LocallyIntegrable (fun z => ∫ r in Icc r₁ r₂,
      (((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z))) volume := fun z0 =>
    ⟨Icc (z0 - 1) (z0 + 1), Icc_mem_nhds (by linarith) (by linarith), hΦI (z0 - 1) (z0 + 1) (by linarith)⟩
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  intro φ hφ hφc
  obtain ⟨Z, hZ⟩ := hφc.isCompact.isBounded.exists_norm_le
  set Z0 := max Z 0 + 1 with hZ0
  have hZ0p : 0 < Z0 := by positivity
  have hφZ : ∀ z, z ∉ Icc (-Z0) Z0 → φ z = 0 := by
    intro z hz
    by_contra hne
    have hzs := hZ z (subset_tsupport _ hne)
    rw [Real.norm_eq_abs] at hzs
    exact hz ⟨by linarith [neg_abs_le z, le_max_left Z 0], by linarith [le_abs_self z, le_max_left Z 0]⟩
  have hTd : Differentiable ℝ (test k x y) := (test_smooth k x y).differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hΨ0 : ∀ p : ℝ × ℝ, p ∉ Icc (min x y - width k) r₂ ×ˢ Icc (-Z0) Z0 → test k x y p.1 * φ p.2 = 0 := by
    intro p hp
    simp only [mem_prod, mem_Icc, not_and_or, not_le] at hp
    rcases hp with (h | h) | (h | h)
    · rw [hT0 _ h, zero_mul]
    · rw [hT1 _ h.le, zero_mul]
    · rw [hφZ p.2 (fun hh => by linarith [hh.1]), mul_zero]
    · rw [hφZ p.2 (fun hh => by linarith [hh.2]), mul_zero]
  have hΨc : HasCompactSupport (fun p : ℝ × ℝ => test k x y p.1 * φ p.2) :=
    HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) hΨ0
  have hΨp : ∀ p ∈ tsupport (fun p : ℝ × ℝ => test k x y p.1 * φ p.2), 0 < p.1 := by
    intro p hp
    have hsub : tsupport (fun p : ℝ × ℝ => test k x y p.1 * φ p.2) ⊆
        Icc (min x y - width k) r₂ ×ˢ Icc (-Z0) Z0 :=
      closure_minimal (fun q hq => by_contra fun h => hq (hΨ0 q h)) (isClosed_Icc.prod isClosed_Icc)
    exact lt_of_lt_of_le hx'0 (hsub hp).1.1
  have hder : ∀ p : ℝ × ℝ, fderiv ℝ (fun p : ℝ × ℝ => test k x y p.1 * φ p.2) p (1, 0) =
      deriv (test k x y) p.1 * φ p.2 := by
    intro p
    have hT' := (hTd p.1).hasFDerivAt.comp p hasFDerivAt_fst
    have hφ' := (hφd p.2).hasFDerivAt.comp p hasFDerivAt_snd
    have hm : HasFDerivAt (fun q : ℝ × ℝ => test k x y q.1 * φ q.2) _ p := hT'.mul hφ'
    rw [hm.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul, mul_zero, zero_add,
      Function.comp]
    rw [fderiv_apply_one_eq_deriv]
    ring
  have weak := weak_plane (m := m) hv6 hG1 hG2 hw n a (fun p : ℝ × ℝ => test k x y p.1 * φ p.2)
    (((test_smooth k x y).comp contDiff_fst).mul (hφ.comp contDiff_snd)) hΨc hΨp
  simp only [hder] at weak
  have hR'm : MeasurableSet (Icc r₁ r₂ ×ˢ Icc (-Z0) Z0) := measurableSet_Icc.prod measurableSet_Icc
  have e1 : ∫ p : ℝ × ℝ, ((deriv (test k x y) p.1 * φ p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
      ∫ p in Icc r₁ r₂ ×ˢ Icc (-Z0) Z0, ((deriv (test k x y) p.1 * φ p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_).symm
    have h0 : deriv (test k x y) p.1 * φ p.2 = 0 := by
      simp only [mem_prod, mem_Icc, not_and_or, not_le] at hp
      rcases hp with (h | h) | (h | h)
      · rw [hdT _ (Or.inl (by linarith)), zero_mul]
      · rw [hdT _ (Or.inr h.le), zero_mul]
      · rw [hφZ p.2 (fun hh => by linarith [hh.1]), mul_zero]
      · rw [hφZ p.2 (fun hh => by linarith [hh.2]), mul_zero]
    rw [h0]; simp
  have e2 : ∫ p : ℝ × ℝ, ((test k x y p.1 * φ p.2 : ℝ) : ℂ) * gradMode m n G a 0 p =
      ∫ p in Icc r₁ r₂ ×ˢ Icc (-Z0) Z0, ((test k x y p.1 * φ p.2 : ℝ) : ℂ) * gradMode m n G a 0 p := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_).symm
    have h0 : test k x y p.1 * φ p.2 = 0 := by
      simp only [mem_prod, mem_Icc, not_and_or, not_le] at hp
      rcases hp with (h | h) | (h | h)
      · rw [hT0 _ (by linarith), zero_mul]
      · rw [hT1 _ h.le, zero_mul]
      · rw [hφZ p.2 (fun hh => by linarith [hh.1]), mul_zero]
      · rw [hφZ p.2 (fun hh => by linarith [hh.2]), mul_zero]
    rw [h0]; simp
  have hZlt : -Z0 < Z0 := by linarith
  have hsum : ∫ p in Icc r₁ r₂ ×ˢ Icc (-Z0) Z0, (((deriv (test k x y) p.1 * φ p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a +
      ((test k x y p.1 * φ p.2 : ℝ) : ℂ) * gradMode m n G a 0 p) = 0 := by
    rw [integral_add (dtest_mv_int hV hv1 hv6 a h1 k x y φ hφ.continuous)
      (test_gm_int hG1 hG2 a h1 h12 hZlt k x y _ hx'0 hT0 φ hφ.continuous), ← e1, ← e2, weak]
    ring
  have hI := hFint (-Z0) Z0 hZlt φ hφ.continuous
  rw [IntegrableOn, prod_eq] at hI
  calc ∫ z, φ z • ∫ r in Icc r₁ r₂, (((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z))
      = ∫ z in Icc (-Z0) Z0, φ z • ∫ r in Icc r₁ r₂, (((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφZ z hz, zero_smul])).symm
    _ = ∫ z in Icc (-Z0) Z0, ∫ r in Icc r₁ r₂, (((deriv (test k x y) r * φ z : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r * φ z : ℝ) : ℂ) * gradMode m n G a 0 (r, z)) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
        rw [← integral_smul]
        congr 1
        funext r
        rw [Complex.real_smul]
        push_cast
        ring
    _ = ∫ p in Icc r₁ r₂ ×ˢ Icc (-Z0) Z0, (((deriv (test k x y) p.1 * φ p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a +
        ((test k x y p.1 * φ p.2 : ℝ) : ℂ) * gradMode m n G a 0 p) := by
        rw [prod_eq, integral_prod_symm _ hI]
    _ = 0 := hsum

end Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis Internal.ModeRadialPartsF ModeRadialLineInternal

theorem modeRadialFormula_of (hV : ModeVecRectIntegrableStatement) : ModeRadialFormulaStatement := by
  intro m v G hv1 hv6 hG1 hG2 hw n a r₁ r₂ z₁ z₂ h1 h12 hz
  have hT : IntegrableOn (fun p : ℝ × ℝ => ((p.1 - r₁ : ℝ) : ℂ) * gradMode m n G a 0 p)
      (Icc r₁ r₂ ×ˢ Icc z₁ z₂) :=
    part_one hG1 hG2 a h1 h12 hz (fun p => p.1 - r₁) (continuousOn_fst.sub continuousOn_const) 1 (fun p hp => by
      rw [abs_of_nonneg (sub_nonneg.mpr hp.1.1)]; linarith)
  have hMV := hV m v hv1 hv6 n a r₁ r₂ z₁ z₂ h1
  have hall : ∀ᵐ z ∂(volume : Measure ℝ), ∀ k : ℕ, ∀ x y : ℚ, r₁ < (x : ℝ) - width k → (x : ℝ) + width k < r₂ →
      r₁ < (y : ℝ) - width k → (y : ℝ) + width k < r₂ →
      ∫ r in Icc r₁ r₂, (((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z)) = 0 := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro x
    rw [ae_all_iff]; intro y
    by_cases hc : r₁ < (x : ℝ) - width k ∧ (x : ℝ) + width k < r₂ ∧ r₁ < (y : ℝ) - width k ∧ (y : ℝ) + width k < r₂
    · filter_upwards [test_slice hV hv1 hv6 hG1 hG2 hw a h1 h12 k hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]
        with z hz' _ _ _ _ using hz'
    · exact Eventually.of_forall fun z c1 c2 c3 c4 => absurd ⟨c1, c2, c3, c4⟩ hc
  filter_upwards [ae_restrict_of_ae hall, slice_of hMV, slice_of hT] with z hzall hzu hzT
  refine line_core r₁ r₂ h12 (fun r => modeVec m n v r z a) (fun t => gradMode m n G a 0 (t, z)) hzu ?_
    (fun k x y c1 c2 c3 c4 => hzall k x y c1 c2 c3 c4)
  intro x' hx'
  have hsub := hzT.mono_set (Icc_subset_Icc_left (le_of_lt hx'))
  have hpos : 0 < x' - r₁ := by linarith
  refine (Integrable.bdd_mul (c := 1 / (x' - r₁)) hsub
    (show AEStronglyMeasurable (fun t : ℝ => ((t - r₁ : ℝ) : ℂ)⁻¹) _ from
      ((Complex.measurable_ofReal.comp (measurable_id.sub_const r₁)).inv).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_))).congr
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_))
  · have htp : 0 < t - r₁ := by linarith [ht.1]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
    exact inv_anti₀ hpos (by linarith [ht.1]) |>.trans (le_of_eq (one_div _).symm)
  · have htp : ((t - r₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show t - r₁ ≠ 0 by linarith [ht.1])
    show ((t - r₁ : ℝ) : ℂ)⁻¹ * (((t - r₁ : ℝ) : ℂ) * gradMode m n G a 0 (t, z)) = gradMode m n G a 0 (t, z)
    rw [← mul_assoc, inv_mul_cancel₀ htp, one_mul]

theorem modeRadialParts_of_vec (hV : ModeVecRectIntegrableStatement) : ModeRadialPartsStatement :=
  modeRadialParts_of hV (modeRadialFormula_of hV)

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF

open SteadyCert Assembly CellAnalysis LowEntry.Internal Real

lemma pow_six_split {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) : x ≤ r * x ^ 6 + r ^ (-(1 / 5 : ℝ)) := by
  have hs : 0 < r ^ (-(1 / 5 : ℝ)) := Real.rpow_pos_of_pos hr _
  have hs5 : r * (r ^ (-(1 / 5 : ℝ))) ^ 5 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']
  rcases le_or_gt x (r ^ (-(1 / 5 : ℝ))) with h | h
  · linarith [mul_nonneg hr.le (pow_nonneg hx 6)]
  · have h1 : 1 < r * x ^ 5 := by
      calc (1 : ℝ) = r * (r ^ (-(1 / 5 : ℝ))) ^ 5 := hs5.symm
        _ < r * x ^ 5 := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ h hs.le (by norm_num)) hr
    have h2 := mul_le_mul_of_nonneg_left h1.le hx
    have h3 : x * (r * x ^ 5) = r * x ^ 6 := by ring
    linarith

lemma enorm_split {r : ℝ} (hr : 0 < r) (u : Space) :
    ‖u‖ₑ ≤ ENNReal.ofReal r * ‖u‖ₑ ^ 6 + ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) := by
  rw [← ofReal_norm u]
  calc ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal (r * ‖u‖ ^ 6 + r ^ (-(1 / 5 : ℝ))) :=
        ENNReal.ofReal_le_ofReal (pow_six_split hr (norm_nonneg _))
    _ = ENNReal.ofReal r * ENNReal.ofReal ‖u‖ ^ 6 + ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) := by
        rw [ENNReal.ofReal_add (mul_nonneg hr.le (pow_nonneg (norm_nonneg _) 6)) (Real.rpow_pos_of_pos hr _).le, ENNReal.ofReal_mul hr.le,
          ENNReal.ofReal_pow (norm_nonneg _)]

lemma modeVec_rect_int {m : ℕ} {v : Space → Space} (hv1 : AEStronglyMeasurable v volume) (hv6 : MemLp v 6 volume)
    (n : ℤ) (a : Fin 3) {r₁ r₂ z₁ z₂ : ℝ} (h1 : 0 ≤ r₁) :
    IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  have hS : MeasurableSet (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    ModeGradSquare.Internal.meas_gen hv1 (velKernel m n a) (velKernel_cont m n a)
  have hle : volume.restrict (Icc r₁ r₂ ×ˢ Icc z₁ z₂) ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    refine Measure.restrict_mono_ae ?_
    have hsub : Icc r₁ r₂ ×ˢ Icc z₁ z₂ ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨le_trans h1 hp.1.1, trivial⟩
    refine hsub.eventuallyLE.trans ?_
    have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
      Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
    exact this.symm.le
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p =>
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2)) :=
    funext fun p => modeVec_eq m n v a p
  rw [e]
  set g : Space → ENNReal := fun y => ‖v y‖ₑ ^ 6 with hg
  have hgm : AEMeasurable g volume := hv1.enorm.pow_const 6
  have hfin : ∫⁻ y, g y < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 6) (by norm_num) (by norm_num) hv6.2
    convert this using 3
    norm_num [hg]
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  have hpow : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ (-(1 / 5 : ℝ))) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
    have h1' : IntegrableOn (fun r : ℝ => r ^ (-(1 / 5 : ℝ))) (Icc r₁ r₂) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      rcases le_or_gt r₁ r₂ with h | h
      · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).1
      · rw [Ioc_eq_empty (not_lt.2 h.le)]; exact integrableOn_empty
    have h2 := h1'.mul_prod (integrableOn_const (μ := (volume : Measure ℝ)) (s := Icc z₁ z₂) (C := (1 : ℝ)) (by simp))
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa using h2
  have hpt : ∀ᵐ p ∂(volume.restrict (Icc r₁ r₂ ×ˢ Icc z₁ z₂)),
      ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2))‖ₑ ≤
        ‖(1 / (2 * π) : ℂ)‖ₑ * (ENNReal.ofReal p.1 * (∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) +
          ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) * ENNReal.ofReal (2 * π)) := by
    filter_upwards [ae_mono hle (ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ))] with p hp
    have hr : 0 < p.1 := hp.1
    rw [enorm_mul]
    refine mul_le_mul' le_rfl ((enorm_integral_le_lintegral_enorm _).trans ?_)
    calc ∫⁻ θ in Ioo (-π) π, ‖velKernel m n a θ (v (cylPoint p.1 θ p.2))‖ₑ
        ≤ ∫⁻ θ in Ioo (-π) π, (ENNReal.ofReal p.1 * g (cylPoint p.1 θ p.2) +
            ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ)))) := by
          refine lintegral_mono fun θ => ?_
          refine le_trans ?_ (enorm_split hr _)
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (velKernel_bound m n a θ _)
      _ = ENNReal.ofReal p.1 * (∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) +
            ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) * ENNReal.ofReal (2 * π) := by
          have hA : ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal p.1 * g (cylPoint p.1 θ p.2) =
              ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          have hB : ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) =
              ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) * ENNReal.ofReal (2 * π) := by
            rw [setLIntegral_const, Real.volume_Ioo, show π - -π = 2 * π by ring]
          rw [lintegral_add_right _ measurable_const, hA, hB]
  refine ⟨(hF.mono_measure hle).const_mul _, ?_⟩
  unfold HasFiniteIntegral
  have hP : ∫⁻ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hpow.2
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hmP : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ)))) :=
    (measurable_fst.pow_const _).ennreal_ofReal
  have hfin' : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) < ⊤ := by
    rw [hint]; exact hfin
  calc ∫⁻ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂,
        ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, ‖(1 / (2 * π) : ℂ)‖ₑ *
          (ENNReal.ofReal p.1 * (∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) +
            ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) * ENNReal.ofReal (2 * π)) := lintegral_mono_ae hpt
    _ = ‖(1 / (2 * π) : ℂ)‖ₑ * ((∫⁻ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, ENNReal.ofReal p.1 *
          (∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2))) +
          (∫⁻ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ)))) * ENNReal.ofReal (2 * π)) := by
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_add_right _ (hmP.mul_const _),
          lintegral_mul_const _ hmP]
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top (ENNReal.add_lt_top.2
        ⟨lt_of_le_of_lt (lintegral_mono' hle le_rfl) hfin', ENNReal.mul_lt_top hP ENNReal.ofReal_lt_top⟩)

end Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF

namespace Breakdown.CellCert.CellFormula

open Internal.ModeRadialPartsF

theorem modeVecRectIntegrable : ModeVecRectIntegrableStatement :=
  fun _ _ hv1 hv6 n a _ _ _ _ h1 => modeVec_rect_int hv1 hv6 n a h1

theorem modeRadialParts : ModeRadialPartsStatement :=
  modeRadialParts_of_vec modeVecRectIntegrable

end Breakdown.CellCert.CellFormula
