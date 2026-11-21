import Breakdown.CertTorus.RegularStatements
import Breakdown.CertTorus.SymbolCurve

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.OrbitTail

open Internal.SymbolCurve

theorem weightL1Measure_zero : weightL1Measure 0 = volume := by
  have h : (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ 0)) = 1 := by
    funext ξ
    simp
  rw [weightL1Measure, h, withDensity_one]

theorem integrable_orbit_velSymbol (hW : HomWiener) {w : ℝ → X}
    (hc : ∀ k, IsHomSobolevCurve k w univ) (s : ℝ) : Integrable (velSymbol (w s)) volume := by
  have h := memLp_curve hW hc 0 (mem_univ s)
  rw [weightL1Measure_zero] at h
  exact memLp_one_iff_integrable.1 h

theorem integrable_char_smul {f : Space → CSpace} (hf : Integrable f volume) (y : Space) :
    Integrable (fun v : Space => 𝐞 (inner ℝ v y) • f v) volume := by
  have h := (Real.fourierIntegral_convergent_iff (μ := volume) (-y)).2 hf
  simpa [inner_neg_right] using h

theorem norm_physField_sub_le {f g : Space → CSpace} (hf : Integrable f volume)
    (hg : Integrable g volume) (y : Space) :
    ‖physField f y - physField g y‖ ≤
      ‖(realVec : CSpace →L[ℝ] Space)‖ * (∫⁻ ξ, ‖f ξ - g ξ‖ₑ).toReal := by
  have h1 : 𝓕⁻ f y - 𝓕⁻ g y = ∫ v, 𝐞 (inner ℝ v y) • (f v - g v) := by
    rw [Real.fourierInv_eq, Real.fourierInv_eq,
      ← integral_sub (integrable_char_smul hf y) (integrable_char_smul hg y)]
    simp_rw [smul_sub]
  have h2 : ‖𝓕⁻ f y - 𝓕⁻ g y‖ ≤ (∫⁻ ξ, ‖f ξ - g ξ‖ₑ).toReal := by
    rw [h1]
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun v => ?_
    rw [Circle.norm_smul, ofReal_norm]
  unfold physField
  rw [← map_sub]
  exact (realVec.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

theorem exists_radius_physField (f : Space → CSpace) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R₀ : ℝ, ∀ y, R₀ ≤ ‖y‖ → ‖physField f y‖ ≤ δ := by
  have h : Tendsto (𝓕⁻ f) (cocompact Space) (𝓝 0) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact tendsto_integral_exp_inner_smul_cocompact (fun x => f (-x))
  have h' : Tendsto (fun y => ‖physField f y‖) (comap norm atTop) (𝓝 0) := by
    rw [comap_norm_atTop, Metric.cobounded_eq_cocompact]
    have := ((realVec.continuous.tendsto 0).comp h).norm
    simpa [physField, Function.comp_def] using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_comap.1 (h'.eventually (eventually_le_nhds hδ)))
  exact ⟨N, fun y hy => hN ‖y‖ hy y rfl⟩

theorem orbitField_add_period (hR : RotateSymbol) {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (hw : realization.F.IsOrbit (realization.rot R) w P) (s : ℝ) (y : Space) :
    orbitField w (s + P) y = R (orbitField w s (R.symm y)) := by
  unfold orbitField
  rw [hw.periodic s, realization_rot_eq]
  exact (hR R (w s)).2.2 y

end Internal.OrbitTail

open Internal.OrbitTail Internal.SymbolCurve

theorem orbitTailOfSymbolCurve_holds : OrbitTailOfSymbolCurve := by
  intro hOH hW hR w P R hw ε hε
  have hc : ∀ k, IsHomSobolevCurve k w univ := hOH w P R hw
  set c : ℝ := ‖(realVec : CSpace →L[ℝ] Space)‖ + 1 with hcdef
  have hc0 : 0 < c := by positivity
  set η : ℝ := ε / (2 * c) with hη
  have hη0 : 0 < η := by positivity
  let U : ℝ → Set ℝ := fun t => {s | ∫⁻ ξ, ‖velSymbol (w s) ξ - velSymbol (w t) ξ‖ₑ
    ∂weightL1Measure 0 < ENNReal.ofReal η}
  have hU : ∀ t ∈ Icc 0 P, U t ∈ 𝓝 t := by
    intro t _
    have h := tendsto_lintegral_vel_sub hW hc 0 (mem_univ t)
    rw [nhdsWithin_univ] at h
    exact h (Iio_mem_nhds (ENNReal.ofReal_pos.2 hη0))
  obtain ⟨T, -, hcover⟩ := isCompact_Icc.elim_nhds_subcover U hU
  choose Rt hRt using fun t : ℝ => exists_radius_physField (velSymbol (w t)) (half_pos hε)
  set R₀ : ℝ := ∑ t ∈ T, |Rt t| with hR₀
  have hbase : ∀ s ∈ Icc 0 P, ∀ y, R₀ ≤ ‖y‖ → ‖orbitField w s y‖ ≤ ε := by
    intro s hs y hy
    obtain ⟨t, htT, hst⟩ := mem_iUnion₂.1 (hcover hs)
    have hRy : Rt t ≤ ‖y‖ := (le_abs_self _).trans
      ((Finset.single_le_sum (fun i _ => abs_nonneg (Rt i)) htT).trans hy)
    have h1 := hRt t y hRy
    have h2 := norm_physField_sub_le (integrable_orbit_velSymbol hW hc s)
      (integrable_orbit_velSymbol hW hc t) y
    have h3 : ∫⁻ ξ, ‖velSymbol (w s) ξ - velSymbol (w t) ξ‖ₑ < ENNReal.ofReal η := by
      have h : ∫⁻ ξ, ‖velSymbol (w s) ξ - velSymbol (w t) ξ‖ₑ ∂weightL1Measure 0 <
          ENNReal.ofReal η := hst
      rwa [weightL1Measure_zero] at h
    have hlt : (∫⁻ ξ, ‖velSymbol (w s) ξ - velSymbol (w t) ξ‖ₑ).toReal < η := by
      have := (ENNReal.toReal_lt_toReal h3.ne_top ENNReal.ofReal_ne_top).2 h3
      rwa [ENNReal.toReal_ofReal hη0.le] at this
    have h4 : ‖(realVec : CSpace →L[ℝ] Space)‖ *
        (∫⁻ ξ, ‖velSymbol (w s) ξ - velSymbol (w t) ξ‖ₑ).toReal ≤ ε / 2 := by
      calc _ ≤ c * η := mul_le_mul (by linarith) hlt.le ENNReal.toReal_nonneg hc0.le
        _ = ε / 2 := by
          rw [hη]
          field_simp
    calc ‖orbitField w s y‖
        = ‖(physField (velSymbol (w s)) y - physField (velSymbol (w t)) y) +
            physField (velSymbol (w t)) y‖ := by
          rw [sub_add_cancel]
          rfl
      _ ≤ ‖physField (velSymbol (w s)) y - physField (velSymbol (w t)) y‖ +
            ‖physField (velSymbol (w t)) y‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (h2.trans h4) h1
      _ = ε := add_halves ε
  have hper : Function.Periodic (fun s => ∀ y, R₀ ≤ ‖y‖ → ‖orbitField w s y‖ ≤ ε) P := by
    intro s
    refine propext ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · have := h (R y) (by rwa [LinearIsometryEquiv.norm_map])
      rwa [orbitField_add_period hR hw, LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.norm_map] at this
    · rw [orbitField_add_period hR hw, LinearIsometryEquiv.norm_map]
      exact h _ (by rwa [LinearIsometryEquiv.norm_map])
  refine ⟨R₀, fun s y hy => ?_⟩
  obtain ⟨s', hs', hss'⟩ := hper.exists_mem_Ico₀ hw.pos s
  have key : ∀ y, R₀ ≤ ‖y‖ → ‖orbitField w s' y‖ ≤ ε := hbase s' (Ico_subset_Icc_self hs')
  have key' : ∀ y, R₀ ≤ ‖y‖ → ‖orbitField w s y‖ ≤ ε := Eq.mpr hss' key
  exact key' y hy

end Breakdown.FarField
