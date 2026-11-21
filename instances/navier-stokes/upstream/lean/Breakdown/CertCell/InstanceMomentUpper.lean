import Breakdown.CertCell.InstanceMomentUpperOrbit

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Instance

open Breakdown Breakdown.CertCell
open Breakdown.CellCert.CellAnalysis (CellBox IsCellBox cylRadius cylHeight radialUnit angularUnit axialUnit)

namespace Internal.MomentUpper

theorem integrable_normPlane {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSb : Bornology.IsBounded S) :
    Integrable (fun z : ℝ × Space => ‖F z.1 z.2‖ * {y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ)) z.2)
      periodMeasure := by
  have hmi : Measurable fun z : ℝ × Space => {y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ)) z.2 :=
    (measurable_const.indicator (measurableSet_planeSet hS)).comp measurable_snd
  refine ((integrable_sq hFm hF2).add (integrable_planeSet hS hSb)).mono'
    ((aesm_period hFm).norm.mul hmi.aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z.2 ∈ {y : Space | pointPlane y ∈ S}
  · simp only [Pi.add_apply, indicator_of_mem hz, mul_one, norm_norm]
    nlinarith [sq_nonneg (‖F z.1 z.2‖ - 1), norm_nonneg (F z.1 z.2)]
  · simp only [Pi.add_apply, indicator_of_notMem hz, mul_zero, norm_zero, add_zero]
    positivity

theorem integrable_pairing {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (m : ℕ) (κ : ℤ × ℤ) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) {ψ : ℝ × ℝ → Fin 3 → ℂ}
    (hψ : ∀ c, Measurable fun p => ψ p c) {C : ℝ} (hC : ∀ p ∈ S, ∀ c, ‖ψ p c‖ ≤ C) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (planeField m κ S ψ z.1 z.2)) periodMeasure := by
  refine ((integrable_normPlane hFm hF2 hS hSb).const_mul (3 * C)).mono'
    ((aesm_period hFm).inner (measurable_planeField m κ hS hψ).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  have h := mul_le_mul_of_nonneg_left (norm_planeField_le m κ hC z.1 z.2) (norm_nonneg (F z.1 z.2))
  refine h.trans (le_of_eq ?_)
  ring

theorem planeField_orbit (m : ℕ) (κ : ℤ × ℤ) (S : Set (ℝ × ℝ)) (ψ : ℝ × ℝ → Fin 3 → ℂ) {p : ℝ × ℝ}
    (hp : 0 < p.1) (σ φ : ℝ) :
    planeField m κ S ψ σ (axialRot φ (planePoint p)) =
      S.indicator (fun p => ∑ c : Fin 3, (labelPhase m κ σ φ * ψ p c).re • frameUnit φ c) p := by
  obtain ⟨k, hk⟩ := pointAngle_orbit hp φ
  unfold planeField
  by_cases hpS : p ∈ S
  · have hy : axialRot φ (planePoint p) ∈ {y : Space | pointPlane y ∈ S} := by
      show pointPlane _ ∈ S
      rw [pointPlane_orbit hp.le]; exact hpS
    rw [indicator_of_mem hy, indicator_of_mem hpS, hk, pointPlane_orbit hp.le]
    simp only [labelPhase_sub, frameUnit_sub]
  · have hy : axialRot φ (planePoint p) ∉ {y : Space | pointPlane y ∈ S} := by
      show pointPlane _ ∉ S
      rw [pointPlane_orbit hp.le]; exact hpS
    rw [indicator_of_notMem hy, indicator_of_notMem hpS]

theorem integrable_phase {F : ℝ → Space → Space} {p : ℝ × ℝ}
    (hΦ : Integrable (fun s : ℝ × ℝ => F s.1 (axialRot s.2 (planePoint p))) sliceMeasure)
    (Θ : ℝ × ℝ → ℂ) (hΘ : Continuous Θ) (hΘ1 : ∀ s, ‖Θ s‖ ≤ 1) (c : Fin 3) :
    Integrable (fun s : ℝ × ℝ => Θ s *
      ((inner ℝ (F s.1 (axialRot s.2 (planePoint p))) (frameUnit s.2 c) : ℝ) : ℂ)) sliceMeasure := by
  have hc : Continuous (fun q : (ℝ × ℝ) × Space => Θ q.1 * ((inner ℝ q.2 (frameUnit q.1.2 c) : ℝ) : ℂ)) :=
    (hΘ.comp continuous_fst).mul (Complex.continuous_ofReal.comp
      (continuous_snd.inner ((continuous_frameUnit c).comp (continuous_snd.comp continuous_fst))))
  refine hΦ.norm.mono' (hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hΦ.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Θ s‖ * |inner ℝ (F s.1 (axialRot s.2 (planePoint p))) (frameUnit s.2 c)|
      ≤ 1 * (‖F s.1 (axialRot s.2 (planePoint p))‖ * ‖frameUnit s.2 c‖) :=
        mul_le_mul (hΘ1 s) (abs_real_inner_le_norm _ _) (abs_nonneg _) zero_le_one
    _ = ‖F s.1 (axialRot s.2 (planePoint p))‖ := by rw [norm_frameUnit]; ring

theorem labelVel_eq {F : ℝ → Space → Space} {p : ℝ × ℝ}
    (hΦ : Integrable (fun s : ℝ × ℝ => F s.1 (axialRot s.2 (planePoint p))) sliceMeasure)
    (m : ℕ) (κ : ℤ × ℤ) (c : Fin 3) :
    labelVel m κ F p c = (1 / (2 * Real.pi) : ℂ) * ∫ s, starRingEnd ℂ (labelPhase m κ s.1 s.2) *
      ((inner ℝ (F s.1 (axialRot s.2 (planePoint p))) (frameUnit s.2 c) : ℝ) : ℂ) ∂sliceMeasure := by
  have hI := integrable_phase hΦ (fun s => starRingEnd ℂ (labelPhase m κ s.1 s.2))
    (Complex.continuous_conj.comp (continuous_labelPhase m κ))
    (fun s => by rw [Complex.norm_conj, norm_labelPhase]) c
  unfold labelVel modeVel modeAverage
  congr 1
  rw [intervalIntegral.integral_of_le zero_le_one, sliceMeasure, integral_prod _ hI]
  refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun φ _ => ?_
  beta_reduce
  rw [zero_add, conj_labelPhase, rot_neg_coord]

theorem slice_eq {F : ℝ → Space → Space} {p : ℝ × ℝ}
    (hΦ : Integrable (fun s : ℝ × ℝ => F s.1 (axialRot s.2 (planePoint p))) sliceMeasure)
    (m : ℕ) (κ : ℤ × ℤ) (ψp : Fin 3 → ℂ) :
    ∫ s, ∑ c : Fin 3, (labelPhase m κ s.1 s.2 * ψp c).re *
        inner ℝ (F s.1 (axialRot s.2 (planePoint p))) (frameUnit s.2 c) ∂sliceMeasure =
      2 * Real.pi * (∑ c : Fin 3, starRingEnd ℂ (labelVel m κ F p c) * ψp c).re := by
  set u : Fin 3 → ℝ × ℝ → ℝ := fun c s => inner ℝ (F s.1 (axialRot s.2 (planePoint p))) (frameUnit s.2 c)
    with hu
  have hI : ∀ c, Integrable (fun s : ℝ × ℝ => labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ)) sliceMeasure :=
    integrable_phase hΦ (fun s => labelPhase m κ s.1 s.2) (continuous_labelPhase m κ)
      (fun s => (norm_labelPhase m κ s.1 s.2).le)
  have hv : ∀ c, starRingEnd ℂ (labelVel m κ F p c) =
      (1 / (2 * Real.pi) : ℂ) * ∫ s, labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ) ∂sliceMeasure := by
    intro c
    rw [labelVel_eq hΦ m κ c, map_mul, ← integral_conj]
    congr 1
    · simp [Complex.conj_ofReal, map_ofNat]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hu]
  have hpt : ∀ c s, (labelPhase m κ s.1 s.2 * ψp c).re * u c s =
      (ψp c * (labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ))).re := by
    intro c s
    rw [show ψp c * (labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ)) =
      (labelPhase m κ s.1 s.2 * ψp c) * ((u c s : ℝ) : ℂ) by ring, Complex.re_mul_ofReal]
  have hre : ∀ c, Integrable (fun s => (ψp c * (labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ))).re)
      sliceMeasure := fun c => ((hI c).const_mul (ψp c)).re
  calc ∫ s, ∑ c : Fin 3, (labelPhase m κ s.1 s.2 * ψp c).re * u c s ∂sliceMeasure
      = ∑ c : Fin 3, ∫ s, (ψp c * (labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ))).re ∂sliceMeasure := by
        simp only [hpt]
        exact integral_finsetSum _ fun c _ => hre c
    _ = ∑ c : Fin 3, (ψp c * ∫ s, labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ) ∂sliceMeasure).re := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have h := Complex.reCLM.integral_comp_comm ((hI c).const_mul (ψp c))
        simp only [Complex.reCLM_apply] at h
        rw [h, integral_const_mul]
    _ = 2 * Real.pi * (∑ c : Fin 3, starRingEnd ℂ (labelVel m κ F p c) * ψp c).re := by
        simp only [hv]
        have e : ∑ c : Fin 3, (1 / (2 * Real.pi) : ℂ) *
              (∫ s, labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ) ∂sliceMeasure) * ψp c =
            (((1 / (2 * Real.pi) : ℝ)) : ℂ) * ∑ c : Fin 3,
              ψp c * ∫ s, labelPhase m κ s.1 s.2 * ((u c s : ℝ) : ℂ) ∂sliceMeasure := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          push_cast; ring
        rw [e, Complex.re_ofReal_mul, Complex.re_sum]
        field_simp

end Internal.MomentUpper

open Internal.MomentUpper in
theorem pairing_planeSet_moment (F : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (m : ℕ) (κ : ℤ × ℤ) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) (hS0 : S ⊆ {p | 0 ≤ p.1})
    (ψ : ℝ × ℝ → Fin 3 → ℂ) (hψ : ∀ c, Measurable fun p => ψ p c) (C : ℝ) (hC : ∀ p ∈ S, ∀ c, ‖ψ p c‖ ≤ C) :
    periodPairing F (fun σ y => Set.indicator {y | pointPlane y ∈ S} (fun y => ∑ c : Fin 3,
        (labelPhase m κ σ (pointAngle y) * ψ (pointPlane y) c).re • frameUnit (pointAngle y) c) y) =
      2 * Real.pi * ∫ p in S, p.1 * (∑ c : Fin 3, starRingEnd ℂ (labelVel m κ F p c) * ψ p c).re := by
  change periodPairing F (planeField m κ S ψ) = _
  have hf := integrable_pairing hFm hF2 m κ hS hSb hψ hC
  have hk := integrable_normPlane hFm hF2 hS hSb
  obtain ⟨hfo, hfe⟩ := integral_orbit hf
  obtain ⟨hko, -⟩ := integral_orbit hk
  have hGo := aestronglyMeasurable_orbit (aesm_period hFm)
  have hfo' : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 • inner ℝ (F w.2.1 (axialRot w.2.2 (planePoint w.1)))
      (planeField m κ S ψ w.2.1 (axialRot w.2.2 (planePoint w.1))))
      ((volume.restrict openHalf).prod sliceMeasure) := hfo
  have hko' : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 • (‖F w.2.1 (axialRot w.2.2 (planePoint w.1))‖ *
      {y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ)) (axialRot w.2.2 (planePoint w.1))))
      ((volume.restrict openHalf).prod sliceMeasure) := hko
  have hGo' : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => F w.2.1 (axialRot w.2.2 (planePoint w.1)))
      ((volume.restrict openHalf).prod sliceMeasure) := hGo
  have hL : periodPairing F (planeField m κ S ψ) = ∫ p in openHalf, ∫ s, p.1 •
      inner ℝ (F s.1 (axialRot s.2 (planePoint p))) (planeField m κ S ψ s.1 (axialRot s.2 (planePoint p)))
        ∂sliceMeasure := by
    unfold periodPairing
    rw [← integral_prod (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (planeField m κ S ψ z.1 z.2)) hf]
    rw [show ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space)) = periodMeasure from rfl, hfe]
    exact integral_prod _ hfo'
  have hR : 2 * Real.pi * ∫ p in S, p.1 * (∑ c : Fin 3, starRingEnd ℂ (labelVel m κ F p c) * ψ p c).re =
      ∫ p in openHalf, S.indicator (fun p => 2 * Real.pi *
        (p.1 * (∑ c : Fin 3, starRingEnd ℂ (labelVel m κ F p c) * ψ p c).re)) p := by
    rw [setIntegral_indicator hS, integral_const_mul, inter_comm]
    congr 1
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS inter_subset_left fun x hx => ?_
    have h0 : x.1 = 0 := by
      have h1 : 0 ≤ x.1 := hS0 hx.1
      by_contra hne
      exact hx.2 ⟨hx.1, lt_of_le_of_ne h1 (Ne.symm hne), mem_univ _⟩
    rw [h0, zero_mul]
  rw [hL, hR]
  refine integral_congr_ae ?_
  filter_upwards [hfo'.prod_right_ae, hko'.prod_right_ae, hGo'.prodMk_left,
    ae_restrict_mem measurableSet_openHalf] with p hpf hpk hpG hp
  have hp1 : 0 < p.1 := hp.1
  simp only [planeField_orbit m κ S ψ hp1]
  by_cases hpS : p ∈ S
  · simp only [indicator_of_mem hpS]
    have hn : Integrable (fun s : ℝ × ℝ => ‖F s.1 (axialRot s.2 (planePoint p))‖) sliceMeasure := by
      refine (hpk.const_mul p.1⁻¹).congr (Filter.Eventually.of_forall fun s => ?_)
      have hy : axialRot s.2 (planePoint p) ∈ {y : Space | pointPlane y ∈ S} := by
        show pointPlane _ ∈ S
        rw [pointPlane_orbit hp1.le]; exact hpS
      simp only [indicator_of_mem hy, smul_eq_mul, mul_one]
      field_simp
    have hΦ := (integrable_norm_iff hpG).1 hn
    simp only [inner_sum, real_inner_smul_right, smul_eq_mul]
    rw [integral_const_mul, slice_eq hΦ m κ (ψ p)]
    ring
  · simp only [indicator_of_notMem hpS, inner_zero_right, smul_zero, integral_zero]

open Internal.MomentUpper in
theorem labelVel_integrableOn (F : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (m : ℕ) (κ : ℤ × ℤ) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) (hS0 : S ⊆ {p | 0 ≤ p.1}) (c : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m κ F p c) S := by
  have hk := integrable_normPlane hFm hF2 hS hSb
  obtain ⟨hko, -⟩ := integral_orbit hk
  have hGo := aestronglyMeasurable_orbit (aesm_period hFm)
  have hko' : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 • (‖F w.2.1 (axialRot w.2.2 (planePoint w.1))‖ *
      {y : Space | pointPlane y ∈ S}.indicator (fun _ => (1 : ℝ)) (axialRot w.2.2 (planePoint w.1))))
      ((volume.restrict openHalf).prod sliceMeasure) := hko
  have hGo' : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => F w.2.1 (axialRot w.2.2 (planePoint w.1)))
      ((volume.restrict openHalf).prod sliceMeasure) := hGo
  have hpos : ∀ᵐ w ∂((volume.restrict openHalf).prod sliceMeasure), 0 < w.1.1 := ae_orbit_pos
  obtain ⟨W, hWdef⟩ : ∃ W : (ℝ × ℝ) × (ℝ × ℝ) → ℂ, W = fun w => ((w.1.1 * S.indicator (fun _ => (1 : ℝ)) w.1 : ℝ) : ℂ) *
    (starRingEnd ℂ (labelPhase m κ w.2.1 w.2.2) *
      ((inner ℝ (F w.2.1 (axialRot w.2.2 (planePoint w.1))) (frameUnit w.2.2 c) : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hWm : AEStronglyMeasurable W ((volume.restrict openHalf).prod sliceMeasure) := by
    have h1 : Measurable fun w : (ℝ × ℝ) × (ℝ × ℝ) => ((w.1.1 * S.indicator (fun _ => (1 : ℝ)) w.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_fst.fst.mul ((measurable_const.indicator hS).comp measurable_fst))
    have h2 : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => starRingEnd ℂ (labelPhase m κ w.2.1 w.2.2) *
        ((inner ℝ (F w.2.1 (axialRot w.2.2 (planePoint w.1))) (frameUnit w.2.2 c) : ℝ) : ℂ))
        ((volume.restrict openHalf).prod sliceMeasure) :=
      by
        have h3 : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
            inner ℝ (F w.2.1 (axialRot w.2.2 (planePoint w.1))) (frameUnit w.2.2 c))
            ((volume.restrict openHalf).prod sliceMeasure) :=
          hGo'.inner ((continuous_frameUnit c).comp (continuous_snd.comp continuous_snd)).aestronglyMeasurable
        have h5 : Continuous fun w : (ℝ × ℝ) × (ℝ × ℝ) => starRingEnd ℂ (labelPhase m κ w.2.1 w.2.2) :=
          Complex.continuous_conj.comp ((continuous_labelPhase m κ).comp continuous_snd)
        exact h5.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable h3)
    rw [hWdef]
    exact h1.aestronglyMeasurable.mul h2
  have hW : Integrable W ((volume.restrict openHalf).prod sliceMeasure) := by
    refine hko'.mono' hWm ?_
    filter_upwards [hpos] with w hw
    rw [hWdef, norm_mul, norm_mul, Complex.norm_conj, norm_labelPhase, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
    by_cases hwS : w.1 ∈ S
    · have hy : axialRot w.2.2 (planePoint w.1) ∈ {y : Space | pointPlane y ∈ S} := by
        show pointPlane _ ∈ S
        rw [pointPlane_orbit hw.le]; exact hwS
      rw [indicator_of_mem hwS, indicator_of_mem hy, mul_one, mul_one, abs_of_pos hw]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans (le_of_eq ?_)) hw.le
      rw [norm_frameUnit, mul_one]
    · rw [indicator_of_notMem hwS, mul_zero, abs_zero, zero_mul]
      exact mul_nonneg hw.le (mul_nonneg (norm_nonneg _) (indicator_nonneg (fun _ _ => zero_le_one) _))
  have hae : ∀ᵐ p ∂(volume.restrict openHalf), ∫ s, W (p, s) ∂sliceMeasure =
      ((2 * Real.pi : ℝ) : ℂ) * S.indicator (fun p => (p.1 : ℂ) * labelVel m κ F p c) p := by
    filter_upwards [hko'.prod_right_ae, hGo'.prodMk_left, ae_restrict_mem measurableSet_openHalf]
      with p hpk hpG hp
    have hp1 : 0 < p.1 := hp.1
    by_cases hpS : p ∈ S
    · have hn : Integrable (fun s : ℝ × ℝ => ‖F s.1 (axialRot s.2 (planePoint p))‖) sliceMeasure := by
        refine (hpk.const_mul p.1⁻¹).congr (Filter.Eventually.of_forall fun s => ?_)
        have hy : axialRot s.2 (planePoint p) ∈ {y : Space | pointPlane y ∈ S} := by
          show pointPlane _ ∈ S
          rw [pointPlane_orbit hp1.le]; exact hpS
        simp only [indicator_of_mem hy, smul_eq_mul, mul_one]
        field_simp
      have hΦ := (integrable_norm_iff hpG).1 hn
      simp only [hWdef, indicator_of_mem hpS, mul_one]
      rw [integral_const_mul, labelVel_eq hΦ m κ c]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    · simp only [hWdef, indicator_of_notMem hpS, mul_zero, Complex.ofReal_zero, zero_mul, integral_zero]
  have h2 : IntegrableOn (S.indicator (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m κ F p c)) openHalf := by
    refine ((hW.integral_prod_left.congr hae).const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    simp only
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ Real.two_pi_pos.ne', Complex.ofReal_one, one_mul]
  rw [← integrable_indicator_iff hS]
  have e : S.indicator (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m κ F p c) =
      openHalf.indicator (S.indicator (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m κ F p c)) := by
    funext p
    by_cases hp : p ∈ openHalf
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp]
      by_cases hpS : p ∈ S
      · have h0 : p.1 = 0 := by
          have h1 : 0 ≤ p.1 := hS0 hpS
          by_contra hne
          exact hp ⟨lt_of_le_of_ne h1 (Ne.symm hne), mem_univ _⟩
        rw [indicator_of_mem hpS, h0, Complex.ofReal_zero, zero_mul]
      · rw [indicator_of_notMem hpS]
  rw [e, integrable_indicator_iff measurableSet_openHalf]
  exact h2

namespace Internal.MomentUpper

theorem continuous_testValue' {count rowCount : ℕ} (R : RowValues count rowCount) (box : Fin count → CellBox)
    (a : Fin rowCount) (c : Fin 3) : Continuous (R.testValue box a c) := by
  unfold RowValues.testValue CellPoly.eval CellBox.refR CellBox.refZ; fun_prop

theorem upper_generator_shape {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ)
    (a : Fin rowCount) (hK : IsCellBox (M.box (R.cellOf a))) (σ : ℝ) (y : Space) :
    Set.indicator {y : Space | 0 ≤ y 2} (R.generatorField M.box m a σ) y =
      Set.indicator {y | pointPlane y ∈ (M.box (R.cellOf a)).rect} (fun y => ∑ c : Fin 3,
        (labelPhase m (R.labelOf a) σ (pointAngle y) *
          (rowPartFactor (R.realPart a) * R.testValue M.box a c (pointPlane y))).re • frameUnit (pointAngle y) c) y := by
  by_cases h2 : 0 ≤ y 2
  · have hy : y ∈ {y : Space | 0 ≤ y 2} := h2
    rw [indicator_of_mem hy, generatorField_eq]
    have hiff : y ∈ (M.box (R.cellOf a)).solid ↔ y ∈ {y | pointPlane y ∈ (M.box (R.cellOf a)).rect} := by
      simp only [CellBox.solid, CellBox.rect, mem_ofPred_eq, mem_prod, mem_Icc, pointPlane,
        cylHeight, abs_of_nonneg h2]
      tauto
    by_cases hs : y ∈ (M.box (R.cellOf a)).solid
    · rw [indicator_of_mem hs, indicator_of_mem (hiff.1 hs)]
      simp only [if_pos h2]
    · rw [indicator_of_notMem hs, indicator_of_notMem (fun h => hs (hiff.2 h))]
  · have hy : y ∉ {y : Space | 0 ≤ y 2} := h2
    rw [indicator_of_notMem hy]
    have hn : y ∉ {y | pointPlane y ∈ (M.box (R.cellOf a)).rect} := by
      intro h
      have h' : (M.box (R.cellOf a)).z₁ ≤ (pointPlane y).2 := h.2.1
      exact h2 (hK.z_order.1.trans h')
    rw [indicator_of_notMem hn]

end Internal.MomentUpper

open Internal.MomentUpper in
theorem generator_upper_pairing {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ)
    (hR : IsRowValues M R m tauMax) (F : ℝ → Space → Space) (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (a : Fin rowCount) :
    periodPairing F (fun σ y => Set.indicator {y : Space | 0 ≤ y 2} (R.generatorField M.box m a σ) y) =
      R.upperMoment M.box m a F := by
  have hK : IsCellBox (M.box (R.cellOf a)) := hR.mesh_valid.box_valid _
  set ψ : ℝ × ℝ → Fin 3 → ℂ := fun p c => rowPartFactor (R.realPart a) * R.testValue M.box a c p with hψdef
  have hψc : ∀ c, Continuous fun p => ψ p c := fun c => continuous_const.mul (continuous_testValue' R M.box a c)
  have hcomp : IsCompact (M.box (R.cellOf a)).rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (continuous_finsetSum Finset.univ fun c _ => (hψc c).norm).continuousOn
  have hC' : ∀ p ∈ (M.box (R.cellOf a)).rect, ∀ c, ‖ψ p c‖ ≤ C := by
    intro p hp c
    refine le_trans ?_ (hC p hp)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun c _ => norm_nonneg _)]
    exact Finset.single_le_sum (f := fun c => ‖ψ p c‖) (fun c _ => norm_nonneg _) (Finset.mem_univ c)
  have hS0 : (M.box (R.cellOf a)).rect ⊆ {p | 0 ≤ p.1} := fun p hp => hK.r_order.1.trans hp.1.1
  have e : (fun σ y => Set.indicator {y : Space | 0 ≤ y 2} (R.generatorField M.box m a σ) y) =
      fun σ y => Set.indicator {y | pointPlane y ∈ (M.box (R.cellOf a)).rect} (fun y => ∑ c : Fin 3,
        (labelPhase m (R.labelOf a) σ (pointAngle y) * ψ (pointPlane y) c).re • frameUnit (pointAngle y) c) y := by
    funext σ y
    exact upper_generator_shape M R m a hK σ y
  have hSm : MeasurableSet (M.box (R.cellOf a)).rect := measurableSet_Icc.prod measurableSet_Icc
  rw [e, pairing_planeSet_moment F hFm hF2 m (R.labelOf a) (M.box (R.cellOf a)).rect hSm
    hcomp.isBounded hS0 ψ (fun c => (hψc c).measurable) C hC']
  unfold RowValues.upperMoment
  congr 1
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun p _ => ?_
  simp only [hψdef, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Breakdown.CertCell.Instance
