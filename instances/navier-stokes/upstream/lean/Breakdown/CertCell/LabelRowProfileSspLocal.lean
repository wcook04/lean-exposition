import Breakdown.CertCell.RowProfileDefs
import Breakdown.FracCell.RadialTrace
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.CircleWeak
import Breakdown.CertCell.LocalResolvedEnergy
import Breakdown.CertCell.LocalModeIntegrable

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

namespace Internal.ModeParts

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem gradMode_integrableOn {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a b : Fin 3) :
    IntegrableOn (gradMode m n G a b) K.rect := by
  have h := (localModeStripIntegrable m v G H hs n K.r₂ K.z₁ K.z₂).2 a b
  exact h.mono_set (Set.prod_mono (Set.Icc_subset_Icc_left hK.r_order.1) subset_rfl)

private theorem combo_oneHot (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) :
    comboThird (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m n H c p = modeThird m n H a b c p := by
  fin_cases a <;> fin_cases b <;> simp [comboThird, Fin.sum_univ_three]

theorem weighted_modeThird_integrableOn {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (fun p => (p.1 : ℂ) * modeThird m n H a b c p) K.rect := by
  obtain ⟨-, -, hc⟩ := localModeSquareIntegrable K hK m v G H hs n
    (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0)
  obtain ⟨hm, hi⟩ := hc c
  have e : comboThird (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m n H c = modeThird m n H a b c :=
    funext (combo_oneHot m n H a b c)
  rw [e] at hm hi
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hr : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect :=
    continuous_fst.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine Integrable.mono' ((hr.add hi).div_const 2)
    ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hm) ?_
  filter_upwards [ae_restrict_mem hKm] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have hsq : ‖modeThird m n H a b c p‖ ≤ (1 + ‖modeThird m n H a b c p‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖modeThird m n H a b c p‖ - 1)]
  calc p.1 * ‖modeThird m n H a b c p‖ ≤ p.1 * ((1 + ‖modeThird m n H a b c p‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hsq h0
    _ = (p.1 + p.1 * ‖modeThird m n H a b c p‖ ^ 2) / 2 := by ring

private theorem third_sq {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    AEStronglyMeasurable (modeThird m n H a b c) (volume.restrict K.rect) := by
  obtain ⟨-, -, hc⟩ := localModeSquareIntegrable K hK m v G H hs n
    (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0)
  have e : comboThird (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m n H c = modeThird m n H a b c :=
    funext (combo_oneHot m n H a b c)
  rw [← e]
  exact (hc c).1

private theorem lineWeight_third_integrableOn {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b c p) K.rect := by
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hw := weighted_modeThird_integrableOn hs K hK m n a b c
  by_cases h0 : K.r₁ = 0
  · refine IntegrableOn.congr_fun hw (fun p _ => ?_) hKm
    simp [CellBox.lineWeight, h0]
  · have hpos : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    have ht : IntegrableOn (modeThird m n H a b c) K.rect := by
      refine Integrable.mono' (hw.norm.div_const K.r₁) (third_sq hs K hK m n a b c) ?_
      filter_upwards [ae_restrict_mem hKm] with p hp
      have h1 : K.r₁ ≤ p.1 := hp.1.1
      rw [le_div_iff₀ hpos, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hpos.le.trans h1)]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    refine IntegrableOn.congr_fun ht (fun p _ => ?_) hKm
    simp [CellBox.lineWeight, h0]

open RadialTraceInternal in
private theorem radialWeak_local {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (m : ℕ) (a b : Fin 3)
    (n : ℤ) : IsRadialWeak (gradMode m n G a b) (radialGradMode m n H a b) := by
  have hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (FracInternal.ModeHeightAxis.col_memLp hs.measurable_gradient hs.gradient_two j).locallyIntegrable
      (by norm_num)
  have hG : LocallyIntegrable G volume := locInt_cols hs.measurable_gradient hGc
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    locInt_cols ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hs.measurable_second)
      fun i => (FracInternal.ModeHeightAxis.second_memLp hs.measurable_second hs.second_two j i).locallyIntegrable
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
      rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
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
  have f1 : ∀ X : ℝ × ℝ → ℂ, (fun p : ℝ × ℝ => ((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * X p)) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * X p) := fun X => funext fun p => by ring
  have f2 : ∀ X : ℝ × ℝ → ℂ, (fun p : ℝ × ℝ => ((Ψ p : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * X p)) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((Ψ p : ℝ) : ℂ) * X p) := fun X => funext fun p => by ring
  rw [f1, f2, integral_const_mul, integral_const_mul, h, mul_neg]

theorem radial_parts {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a : Fin 3) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (h1 : χ K.r₁ = 0)
    (h2 : χ K.r₂ = 0) {τ : ℝ → ℝ} (hτ : Continuous τ) :
    IntegrableOn (fun p => modeThird m n H a 0 0 p * ((χ p.1 * τ p.2 : ℝ) : ℂ)
      + gradMode m n G a 0 p * ((deriv χ p.1 * τ p.2 : ℝ) : ℂ)) K.rect ∧
    ∫ p in K.rect, (modeThird m n H a 0 0 p * ((χ p.1 * τ p.2 : ℝ) : ℂ)
      + gradMode m n G a 0 p * ((deriv χ p.1 * τ p.2 : ℝ) : ℂ)) = 0 :=
  RadialTraceInternal.rect_core K hK (radialWeak_local hs m a 0 n) (gradMode_integrableOn hs K hK m n a 0)
    (lineWeight_third_integrableOn hs K hK m n a 0 0) hχ h1 h2 hτ

private theorem comboGrad_oneHot (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    comboGrad (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m n G p = gradMode m n G a b p := by
  fin_cases a <;> fin_cases b <;> simp [comboGrad, Fin.sum_univ_three]

private theorem height_deriv_eq {f A χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (p : ℝ × ℝ) :
    CellBox.heightDeriv (fun q : ℝ × ℝ => ((f q.1 * A q.1 * χ q.2 : ℝ) : ℂ)) p
      = ((f p.1 * A p.1 * deriv χ p.2 : ℝ) : ℂ) := by
  unfold CellBox.heightDeriv
  have hd : HasDerivAt (fun z => f p.1 * A p.1 * χ z) (f p.1 * A p.1 * deriv χ p.2) p.2 :=
    ((hχ.differentiable one_ne_zero) p.2).hasDerivAt.const_mul _
  exact hd.ofReal_comp.deriv

theorem height_parts {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (K : CellBox)
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a : Fin 3) {A χ : ℝ → ℝ} (hA : ContDiff ℝ 1 A)
    (hχ : ContDiff ℝ 1 χ) (h1 : χ K.z₁ = 0) (h2 : χ K.z₂ = 0) :
    IntegrableOn (fun p => (p.1 : ℂ) * (modeThird m n H a 2 2 p * ((A p.1 * χ p.2 : ℝ) : ℂ)
      + gradMode m n G a 2 p * ((A p.1 * deriv χ p.2 : ℝ) : ℂ))) K.rect ∧
    ∫ p in K.rect, (p.1 : ℂ) * (modeThird m n H a 2 2 p * ((A p.1 * χ p.2 : ℝ) : ℂ)
      + gradMode m n G a 2 p * ((A p.1 * deriv χ p.2 : ℝ) : ℂ)) = 0 := by
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hKc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hAc : Continuous A := hA.continuous
  have hχc : Continuous χ := hχ.continuous
  have hχ'c : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  have hT := weighted_modeThird_integrableOn hs K hK m n a 2 2
  have hS := gradMode_integrableOn hs K hK m n a 2
  have iT : IntegrableOn (fun p => ((A p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a 2 2 p)) K.rect :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hAc.comp continuous_fst).mul (hχc.comp continuous_snd))).continuousOn hT hKc
  have iS : IntegrableOn (fun p => ((p.1 * A p.1 * deriv χ p.2 : ℝ) : ℂ) * gradMode m n G a 2 p) K.rect :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp
      ((continuous_fst.mul (hAc.comp continuous_fst)).mul (hχ'c.comp continuous_snd))).continuousOn hS hKc
  have hsum : IntegrableOn (fun p => (p.1 : ℂ) * (modeThird m n H a 2 2 p * ((A p.1 * χ p.2 : ℝ) : ℂ)
      + gradMode m n G a 2 p * ((A p.1 * deriv χ p.2 : ℝ) : ℂ))) K.rect := by
    refine IntegrableOn.congr_fun (iT.add iS) (fun p _ => ?_) hKm
    simp only [Pi.add_apply]
    push_cast
    ring
  refine ⟨hsum, ?_⟩
  set κ : Fin 3 → Fin 3 → ℂ := fun a' b' => if a' = a ∧ b' = 2 then (1 : ℂ) else 0 with hκ
  have eT : ∀ p, comboThird κ m n H 2 p = modeThird m n H a 2 2 p := fun p => combo_oneHot m n H a 2 2 p
  have eS : ∀ p, comboGrad κ m n G p = gradMode m n G a 2 p := fun p => comboGrad_oneHot m n G a 2 p
  set f : ℝ → ℝ := fun r => if K.r₁ = 0 then 1 else r with hf
  have hfc : ContDiff ℝ 1 f := by
    by_cases h0 : K.r₁ = 0
    · simp only [hf, h0, if_true]; exact contDiff_const
    · simp only [hf, h0, if_false]; exact contDiff_id
  have hwf : ∀ r, K.lineWeight r * f r = r := by
    intro r
    by_cases h0 : K.r₁ = 0 <;> simp [CellBox.lineWeight, hf, h0]
  set ψ : ℝ × ℝ → ℂ := fun q => ((f q.1 * A q.1 * χ q.2 : ℝ) : ℂ) with hψ
  have hψc : ContDiff ℝ 1 ψ :=
    Complex.ofRealCLM.contDiff.comp (((hfc.comp contDiff_fst).mul (hA.comp contDiff_fst)).mul
      (hχ.comp contDiff_snd))
  have hP := localModeHeightParts K hK m v G H hs n κ ψ hψc (fun r => by simp [hψ, h1])
    (fun r => by simp [hψ, h2])
  have hd : ∀ p, CellBox.heightDeriv ψ p = ((f p.1 * A p.1 * deriv χ p.2 : ℝ) : ℂ) := fun p => height_deriv_eq hχ p
  simp only [eT, eS, hd] at hP
  have e1 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * modeThird m n H a 2 2 p * ψ p
      = ((A p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a 2 2 p) := by
    intro p
    have hc : (K.lineWeight p.1 : ℂ) * (f p.1 : ℂ) = (p.1 : ℂ) := by exact_mod_cast hwf p.1
    simp only [hψ]
    push_cast
    linear_combination (A p.1 : ℂ) * (χ p.2 : ℂ) * modeThird m n H a 2 2 p * hc
  have e2 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((f p.1 * A p.1 * deriv χ p.2 : ℝ) : ℂ)
      = ((p.1 * A p.1 * deriv χ p.2 : ℝ) : ℂ) * gradMode m n G a 2 p := by
    intro p
    have hc : (K.lineWeight p.1 : ℂ) * (f p.1 : ℂ) = (p.1 : ℂ) := by exact_mod_cast hwf p.1
    push_cast
    linear_combination (A p.1 : ℂ) * ((deriv χ p.2 : ℝ) : ℂ) * gradMode m n G a 2 p * hc
  simp only [e1, e2] at hP
  calc ∫ p in K.rect, (p.1 : ℂ) * (modeThird m n H a 2 2 p * ((A p.1 * χ p.2 : ℝ) : ℂ)
        + gradMode m n G a 2 p * ((A p.1 * deriv χ p.2 : ℝ) : ℂ))
      = ∫ p in K.rect, (((A p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a 2 2 p)
          + ((p.1 * A p.1 * deriv χ p.2 : ℝ) : ℂ) * gradMode m n G a 2 p) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        push_cast
        ring
    _ = 0 := by
        rw [integral_add iT iS, hP, neg_add_cancel]

open Internal.AngularFrame in
theorem angular_column {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * modeThird m n H a 1 1 p
      = turnVector (azimuth m n) (fun b => gradMode m n G b 1 p) a + gradMode m n G a 0 p := by
  have locs : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hs.measurable_second j i).inner aestronglyMeasurable_const)
      hs.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have locf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hs.measurable_gradient i).inner aestronglyMeasurable_const)
      hs.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have locG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hs.measurable_gradient i) hs.gradient_two fun y => G_sq_le (G y) i
  have locH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hs.measurable_second j i) hs.second_two fun y => H_sq_le (H y) j i
  have locg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun K hK => ((locs j i l).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hs.weak_second φ hφ i j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := (locG i).integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • H y (unitVector j) (unitVector i)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [L, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => circleWeak (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) (fun y => gv (H y) i l)
    (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a 1 i l) (wgt_smooth _ a 1 i l) (hk ▸ wgt_periodic _ a 1 i l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  have key := point m n G H a 1 r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2) (fun i l => h2 i l hr)
  have e : (r : ℂ) * modeThird m n H a 1 1 (r, z) = angularGradMode m n H a 1 (r, z) := rfl
  rw [e, key]
  fin_cases a <;> simp [angularComb, frameTurn, turnVector, Fin.sum_univ_three] <;> ring

end Internal.ModeParts

end CellCalculus

end CertCell

end Breakdown
