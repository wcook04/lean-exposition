import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.FracCell.RadialTrace

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.CertCell.LocalField.Internal

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.Assembly Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellFormula Breakdown.CellCert.CellEnergy
open Breakdown.CellCert.CellEnergy.RadialTraceInternal

theorem localSecondLocallyIntegrable {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    LocallyIntegrable H volume :=
  locInt_cols hs.measurable_second fun j =>
    locInt_cols ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hs.measurable_second)
      fun i => (Breakdown.FracInternal.ModeHeightAxis.second_memLp hs.measurable_second hs.second_two j i).locallyIntegrable
        (by norm_num)

theorem localRadialWeakMode {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (a b : Fin 3) (n : ℤ) :
    IsRadialWeak (gradMode m n G a b) (radialGradMode m n H a b) := by
  have hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (Breakdown.FracInternal.ModeHeightAxis.col_memLp hs.measurable_gradient hs.gradient_two j).locallyIntegrable
      (by norm_num)
  have hG : LocallyIntegrable G volume := locInt_cols hs.measurable_gradient hGc
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    locInt_cols ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hs.measurable_second)
      fun i => (Breakdown.FracInternal.ModeHeightAxis.second_memLp hs.measurable_second hs.second_two j i).locallyIntegrable
        (by norm_num)
  have hweakG : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
    intro φ hφ j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
      hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
      (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
        (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
      intro i
      rw [neg_apply, ContinuousLinearMap.integral_apply i1,
        ContinuousLinearMap.integral_apply i2]
      simpa using hs.weak_second φ hφ i j
    refine ContinuousLinearMap.ext fun u => ?_
    rw [vec_sum u]
    simp only [map_sum, map_smul, key]
  intro Ψ hΨ hc hpos
  have h := (cylModeWeak (Space →L[ℝ] Space) G H hG hHc hweakG (entryForm a b) (entryForm_smooth a b) m n Ψ
    hΨ hc hpos).1
  have e1 : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, entryForm_circle]
    rfl
  have e2 : ∀ p : ℝ × ℝ, radialGradMode m n H a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ) := by
    intro p
    simp only [radialGradMode, modeThird, entryForm_circle]
    rfl
  simp only [e1, e2]
  have f1 : (fun p : ℝ × ℝ => ((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ))) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ)) := funext fun p => by ring
  have f2 : (fun p : ℝ × ℝ => ((Ψ p : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ))) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((Ψ p : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ)) :=
    funext fun p => by ring
  rw [f1, f2, integral_const_mul, integral_const_mul, h, mul_neg]

theorem localThirdLineIntegrable {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (a b : Fin 3) (n : ℤ) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * radialGradMode m n H a b p) K.rect := by
  have h := (LowEntry.Internal.mode_int K hK (localSecondLocallyIntegrable hs) (thirdKernel m n a b)
    (thirdKernel_cont m n a b) (thirdKernel_bound m n a b)).const_mul (1 / (2 * Real.pi) : ℂ)
  refine IntegrableOn.congr_fun h (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [radialGradMode_eq]
  ring

theorem localGradRectIntegrable {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (a b : Fin 3) (n : ℤ) :
    IntegrableOn (gradMode m n G a b) K.rect :=
  ((localModeStripIntegrable m v G H hs n K.r₂ K.z₁ K.z₂).2 a b).mono_set
    (Set.prod_mono (Set.Icc_subset_Icc_left hK.r_order.1) subset_rfl)

end Breakdown.CertCell.LocalField.Internal

namespace Breakdown.CertCell.LocalField

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.Assembly Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellFormula Breakdown.CellCert.CellEnergy
open Breakdown.CellCert.CellEnergy.RadialTraceInternal

theorem localRadialTrace : LocalRadialTraceStatement := by
  intro K hK m v G H hs n a b
  have hF := Internal.localGradRectIntegrable (m := m) hs K hK a b n
  have hDw := Internal.localThirdLineIntegrable (m := m) hs K hK a b n
  have hab : K.r₁ < K.r₂ := hK.r_order.2
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  refine ⟨hF, ?_, ?_, ?_⟩
  · have hK' : IsCellBox ⟨0, K.r₂, K.z₁, K.z₂⟩ := ⟨⟨le_rfl, lt_of_le_of_lt hK.r_order.1 hab⟩, hK.z_order⟩
    have h := (Internal.localThirdLineIntegrable (m := m) hs ⟨0, K.r₂, K.z₁, K.z₂⟩ hK' a b n).mono_set
      (Set.prod_mono (Set.Icc_subset_Icc_left hK.r_order.1) subset_rfl)
    refine IntegrableOn.congr_fun h (fun p _ => ?_) hKm
    simp [CellBox.lineWeight]
  · intro h0
    refine IntegrableOn.congr_fun hDw (fun p _ => ?_) hKm
    simp [CellBox.lineWeight, h0]
  · intro ψ t hψ ht hcase
    set F := gradMode m n G a b with hFdef
    set D := radialGradMode m n H a b with hDdef
    have hc : 0 < K.r₂ - K.r₁ := sub_pos.2 hab
    set α := ψ K.r₂ with hα
    set β := ψ K.r₁ with hβ
    set χ : ℝ → ℝ := fun r => ψ r - α / (K.r₂ - K.r₁) * (r - K.r₁) - β / (K.r₂ - K.r₁) * (K.r₂ - r) with hχdef
    have hχ : ContDiff ℝ 1 χ :=
      (hψ.sub (contDiff_const.mul (contDiff_id.sub contDiff_const))).sub
        (contDiff_const.mul (contDiff_const.sub contDiff_id))
    have hχd : ∀ r, deriv χ r = deriv ψ r - α / (K.r₂ - K.r₁) + β / (K.r₂ - K.r₁) := by
      intro r
      have hd : HasDerivAt χ (deriv ψ r - α / (K.r₂ - K.r₁) * 1 - β / (K.r₂ - K.r₁) * (-1)) r :=
        (((hψ.differentiable one_ne_zero) r).hasDerivAt.sub (((hasDerivAt_id' r).sub_const K.r₁).const_mul _)).sub
          (((hasDerivAt_id' r).const_sub K.r₂).const_mul _)
      rw [hd.deriv]
      ring
    have hχ1 : χ K.r₁ = 0 := by
      simp only [hχdef]
      rw [sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hc.ne', hβ, sub_self]
    have hχ2 : χ K.r₂ = 0 := by
      simp only [hχdef]
      rw [sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hc.ne', hα, sub_self]
    obtain ⟨hI, hcore⟩ := rect_core K hK (Internal.localRadialWeakMode hs a b n) hF hDw hχ hχ1 hχ2 ht
    obtain ⟨T, hT⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.z₁ K.z₂) ht.continuousOn
    have hDs := shifted_int K hK hDw
    set X₁ : ℝ × ℝ → ℂ := fun p => ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p +
      (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * D p) * ((t p.2 : ℝ) : ℂ) with hX₁
    set Y₀ : ℝ × ℝ → ℂ := fun p => ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p +
      (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * D p) * ((t p.2 : ℝ) : ℂ) with hY₀
    have htc : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (ht.comp continuous_snd)
    have hbd : ∀ (f : ℝ × ℝ → ℂ) (C : ℂ), IntegrableOn f K.rect →
        IntegrableOn (fun p => C * ((t p.2 : ℝ) : ℂ) * f p) K.rect := by
      intro f C hf
      refine Integrable.bdd_mul (c := ‖C‖ * T) hf ((continuous_const.mul htc).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem hKm] with p hp
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hT p.2 hp.2) (norm_nonneg _)
    have hX₁i : IntegrableOn X₁ K.rect := by
      refine IntegrableOn.congr_fun ((hbd F (((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) hF).add
        (hbd _ (((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) hDs)) (fun p _ => ?_) hKm
      simp only [hX₁, Pi.add_apply]
      push_cast
      ring
    have hY₀i : IntegrableOn (fun p => (β : ℂ) * Y₀ p) K.rect := by
      by_cases hb0 : β = 0
      · simp only [hb0, Complex.ofReal_zero, zero_mul]
        exact integrableOn_zero
      · have hr : K.r₁ ≠ 0 := by
          rcases hcase with h | h
          · exact h
          · intro h0
            exact hb0 (by rw [hβ, h0, h])
        have hD : IntegrableOn D K.rect :=
          IntegrableOn.congr_fun hDw (fun p _ => by simp [CellBox.lineWeight, hr]) hKm
        have hD2 : IntegrableOn (fun p => ((p.1 - K.r₂ : ℝ) : ℂ) * D p) K.rect := by
          refine Integrable.bdd_mul (c := K.r₂ - K.r₁) hD ?_ ?_
          · exact (Complex.continuous_ofReal.comp (continuous_fst.sub continuous_const)).aestronglyMeasurable
          · filter_upwards [ae_restrict_mem hKm] with p hp
            obtain ⟨⟨h1, h2⟩, _⟩ := hp
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
            linarith
        refine IntegrableOn.congr_fun (((hbd F (((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) hF).add
          (hbd _ (((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) hD2)).const_mul (β : ℂ)) (fun p _ => ?_) hKm
        simp only [hY₀, Pi.add_apply]
        push_cast
        ring
    have hpt : ∀ p : ℝ × ℝ, D p * ((ψ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) =
        (D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) + (α : ℂ) * X₁ p +
          (β : ℂ) * Y₀ p := by
      intro p
      have hne1 : ((K.r₂ : ℂ) - K.r₁) ≠ 0 := by
        rw [← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.2 hc.ne'
      have hne2 : ((K.r₁ : ℂ) - K.r₂) ≠ 0 := by
        rw [← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.2 (by linarith)
      rw [hχd]
      simp only [hχdef, hX₁, hY₀]
      push_cast
      field_simp
      ring
    have hR1 : radialFaceMoment K F D 1 t = ∫ p in K.rect, X₁ p := by
      unfold radialFaceMoment radialStripMoment edgeSign
      rw [if_pos rfl, if_pos hab, min_eq_right hab.le, max_eq_left hab.le, one_mul]
      rfl
    have hR0 : radialFaceMoment K F D 0 t = -∫ p in K.rect, Y₀ p := by
      unfold radialFaceMoment radialStripMoment edgeSign
      rw [if_neg (by decide), if_neg (not_lt.2 hab.le), min_eq_left hab.le, max_eq_right hab.le, neg_one_mul]
      rfl
    have hI' : IntegrableOn (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ))
        K.rect := hI
    have hcore' : ∫ p in K.rect, (D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) = 0 :=
      hcore
    have hX' : IntegrableOn (fun p => (α : ℂ) * X₁ p) K.rect := hX₁i.const_mul _
    have hI2 : IntegrableOn (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ) +
        (α : ℂ) * X₁ p) K.rect := hI'.add hX'
    rw [hR1, hR0, setIntegral_congr_fun hKm (fun p _ => hpt p), integral_add hI2 hY₀i, integral_add hI' hX',
      hcore', integral_const_mul, integral_const_mul]
    ring

end Breakdown.CertCell.LocalField
