import Breakdown.CertCell.TailAngular
import Breakdown.CertCell.ModeRotationNorms
import Breakdown.FracCell.CylIntegral

open scoped ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace Internal.AngularPlane

open CellCert.Spectral.Internal.CylIntegral

theorem planePoint_eq (p : ℝ × ℝ) : planePoint p = p.1 • unitVector 0 + p.2 • unitVector 2 := by
  ext i
  fin_cases i <;> simp [planePoint, CellCert.CellAnalysis.cylPoint, unitVector]

theorem continuous_planePoint : Continuous planePoint := by
  have e : planePoint = fun p : ℝ × ℝ => p.1 • unitVector 0 + p.2 • unitVector 2 := funext planePoint_eq
  rw [e]
  fun_prop

theorem axialRot_planePoint (θ : ℝ) (p : ℝ × ℝ) :
    axialRot θ (planePoint p) = CellCert.Spectral.cylPoint p.1 θ p.2 := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, CellCert.Spectral.cylPoint,
    unitVector] <;> ring

theorem continuous_orbitPlane : Continuous (fun x : (ℝ × ℝ) × ℝ => axialRot x.2 (planePoint x.1)) := by
  have e : (fun x : (ℝ × ℝ) × ℝ => axialRot x.2 (planePoint x.1)) =
      fun x => axialRot x.2 (x.1.1 • unitVector 0 + x.1.2 • unitVector 2) := by
    funext x
    rw [planePoint_eq]
  rw [e]
  unfold axialRot
  fun_prop

end Internal.AngularPlane

open Internal.AngularPlane CellCert.Spectral.Internal.CylIntegral in
theorem lintegral_eq_cylindrical (F : Space → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.univ, ENNReal.ofReal p.1 *
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, F (axialRot θ (planePoint p)) := by
  set g : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun w => F (toSpace w) with hg
  set Hf : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal x.1.1 * g (cylMap.symm x) with hHf
  have hsw : (fun x => Hf (swapEquiv x)) =
      fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * F (axialRot x.2 (planePoint x.1)) := by
    funext x
    obtain ⟨⟨r, z⟩, θ⟩ := x
    simp only [hHf, hg, swapEquiv_apply, axialRot_planePoint]
    rw [← toSpace_apply]
    rfl
  have hmeas : Measurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * F (axialRot x.2 (planePoint x.1))) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (hF.comp continuous_orbitPlane.measurable)
  calc ∫⁻ y, F y = ∫⁻ w, g w := (toSpace_mp.lintegral_comp_emb toSpace.measurableEmbedding F).symm
    _ = ∫⁻ w in cylMap.symm '' cylMap.target, g w := by
        rw [setLIntegral_congr image_ae, Measure.restrict_univ]
    _ = ∫⁻ x in cylMap.target, ENNReal.ofReal |(cylDeriv x).det| * g (cylMap.symm x) :=
        lintegral_image_eq_lintegral_abs_det_fderiv_mul volume cylMap.open_target.measurableSet
          (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g
    _ = ∫⁻ x in cylMap.target, Hf x := by
        refine setLIntegral_congr_fun cylMap.open_target.measurableSet fun x hx => ?_
        rw [abs_det_eq hx]
    _ = ∫⁻ x in swapEquiv ⁻¹' cylMap.target, Hf (swapEquiv x) :=
        (swapEquiv_mp.setLIntegral_comp_preimage_emb swapEquiv.measurableEmbedding Hf _).symm
    _ = ∫⁻ x in (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal x.1.1 * F (axialRot x.2 (planePoint x.1)) := by
        rw [swapEquiv_preimage, hsw]
    _ = _ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
        refine lintegral_congr fun p => ?_
        show ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * F (axialRot θ (planePoint p)) = _
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem ae_exists_rotation_planePoint_of_ae {Q : Space → Prop} (hQ : ∀ᵐ y, Q y) :
    ∀ᵐ p ∂(volume.restrict halfPlane), ∃ θ : ℝ, Q (axialRot θ (planePoint p)) := by
  set N := toMeasurable volume {y | ¬ Q y} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hQ
  have hsub : {y | ¬ Q y} ⊆ N := subset_toMeasurable _ _
  have hmθ : Measurable (fun x : (ℝ × ℝ) × ℝ => N.indicator (1 : Space → ℝ≥0∞) (axialRot x.2 (planePoint x.1))) :=
    (measurable_one.indicator hNm).comp Internal.AngularPlane.continuous_orbitPlane.measurable
  have hmI : Measurable (fun p : ℝ × ℝ => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      N.indicator (1 : Space → ℝ≥0∞) (axialRot θ (planePoint p))) := hmθ.lintegral_prod_right'
  have h0 := lintegral_eq_cylindrical (N.indicator 1) (measurable_one.indicator hNm)
  rw [lintegral_indicator_one hNm, hN0] at h0
  have hae := (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp measurable_fst).mul hmI)).1 h0.symm
  have hS : ∀ᵐ p ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.univ)), ∃ θ : ℝ, Q (axialRot θ (planePoint p)) := by
    filter_upwards [hae, ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp hpS
    have hp1 : 0 < p.1 := hpS.1
    have hI : ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, N.indicator (1 : Space → ℝ≥0∞) (axialRot θ (planePoint p)) = 0 := by
      have hp' := hp
      simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at hp'
      rcases hp' with h | h
      · simp only [Function.comp_apply, ENNReal.ofReal_eq_zero] at h
        linarith
      · exact h
    have hθ := (lintegral_eq_zero_iff (hmθ.comp (measurable_const.prodMk measurable_id))).1 hI
    have hne : volume.restrict (Set.Ioo (-Real.pi) Real.pi) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
      linarith [Real.pi_pos]
    have : (ae (volume.restrict (Set.Ioo (-Real.pi) Real.pi))).NeBot := ae_neBot.2 hne
    obtain ⟨θ, hθ⟩ := hθ.exists
    refine ⟨θ, ?_⟩
    by_contra hq
    have hmem : axialRot θ (planePoint p) ∈ N := hsub hq
    simp [Set.indicator_of_mem hmem] at hθ
  exact ae_restrict_of_ae_restrict_of_subset (Set.prod_mono le_rfl (Set.subset_univ _)) hS

namespace Internal.AngularPlane

theorem cylRadius_planePoint {p : ℝ × ℝ} (hp : 0 < p.1) : cylRadius (planePoint p) = p.1 := by
  unfold cylRadius
  rw [planePoint_eq]
  simp [unitVector, Real.sqrt_sq hp.le]

end Internal.AngularPlane

open Internal.AngularPlane Coercive.Internal.ModeRotation Coercive.FrequencySeminorm.Internal in
theorem angularModeBounds_of (hA : AngularModePointwise) : AngularModeBounds := by
  intro Γ P v G H g hv hP mm ι
  have hRot := Coercive.axialRotationHolds_proof
  obtain ⟨hlv, hlG, hlH⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  set ξ := labelHarmonic mm ι with hξ
  have hgood := ((hA Γ P v G H g hv hP ξ).and (ae_integrable_orbit hRot hlv)).and
    ((ae_integrable_orbit hRot hlG).and (ae_integrable_orbit hRot hlH))
  rw [Measure.volume_eq_prod] at hgood
  obtain ⟨σ₀, hσ₀⟩ := (Measure.ae_ae_of_ae_prod hgood).exists
  have hhp : MeasurableSet halfPlane := measurableSet_Ioi.prod measurableSet_Ioi
  filter_upwards [ae_exists_rotation_planePoint_of_ae hσ₀, ae_restrict_mem hhp] with p hq hp
  obtain ⟨θ, ⟨hrel, hiv⟩, hiG, hiH⟩ := hq
  set y' := axialRot θ (planePoint p) with hy'
  have hy : axialRot (-θ) y' = planePoint p := by
    rw [hy', ← hRot.2.1, neg_add_cancel, hRot.2.2.1]
  have rv := modeVel_rotation_of hRot ξ (-θ) (z := (σ₀, y')) hiv
  have rG := modeGrad_rotation_of hRot ξ (-θ) (z := (σ₀, y')) hiG
  have rH := modeSecondDeriv_rotation_of hRot ξ (-θ) (z := (σ₀, y')) hiH
  simp only [hy] at rv rG rH
  have tv := modeVel_shift ξ hv.periodic_velocity σ₀ (planePoint p)
  have tG := modeGrad_shift ξ hv.periodic_gradient σ₀ (planePoint p)
  have tH := modeSecondDeriv_shift ξ hv.periodic_secondDeriv σ₀ (planePoint p)
  have n1 : cnormSq (labelVel mm ι v p) = cnormSq (modeVel ξ v σ₀ y') := by
    rw [← cnormSq_phase _ (norm_phase _) (labelVel mm ι v p), labelVel, ← tv, rv,
      cnormSq_phase _ (norm_phase _), cnormSq_rotC]
  have n2 : cnormSq (labelGrad mm ι G p) = cnormSq (modeGrad ξ G σ₀ y') := by
    rw [← cnormSq_phase _ (norm_phase _) (labelGrad mm ι G p), labelGrad, ← tG, rG,
      cnormSq_phase _ (norm_phase _), cnormSq_rotCMat]
  have n3 : cnormSq (labelHess mm ι H p) = cnormSq (modeSecondDeriv ξ H σ₀ y') := by
    rw [← cnormSq_phase _ (norm_phase _) (labelHess mm ι H p), labelHess, ← tH, rH,
      cnormSq_phase _ (norm_phase _), cnormSq_rotTensor]
  have n4 : cnormSq (curlOfGrad (labelGrad mm ι G p)) = cnormSq (curlOfGrad (modeGrad ξ G σ₀ y')) := by
    rw [← cnormSq_phase _ (norm_phase _) (curlOfGrad (labelGrad mm ι G p)), labelGrad, ← curlOfGrad_phase,
      ← tG, rG, curlOfGrad_phase, cnormSq_phase _ (norm_phase _), curlOfGrad_rotCMat, cnormSq_rotC]
  have n5 : cnormSq (curlGradOfSecondDeriv (labelHess mm ι H p)) = cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ξ H σ₀ y')) := by
    rw [← cnormSq_phase _ (norm_phase _) (curlGradOfSecondDeriv (labelHess mm ι H p)), labelHess,
      ← curlGradOfSecondDeriv_phase, ← tH, rH, curlGradOfSecondDeriv_phase, cnormSq_phase _ (norm_phase _),
      curlGradOfSecondDeriv_rotTensor, cnormSq_rotCMat]
  have hr : p.1 = cylRadius y' := by
    rw [hy', (hRot.2.2.2.2 θ (planePoint p)).1, cylRadius_planePoint hp.1]
  rw [n1, n2, n3, n4, n5, hr]
  exact hrel

theorem angularModeBounds : AngularModeBounds := angularModeBounds_of angularModePointwise

namespace Internal.AngularPlane

theorem axialRot_add_int_mul (n : ℤ) (φ : ℝ) (y : Space) :
    axialRot (φ + n * (2 * Real.pi)) y = axialRot φ y := by
  unfold axialRot
  rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem volume_eq_zero_of_periodic {E : Set ℝ}
    (hper : ∀ (n : ℤ) (φ : ℝ), φ + n * (2 * Real.pi) ∈ E ↔ φ ∈ E)
    (h0 : volume (E ∩ Set.Ioo (-Real.pi) Real.pi) = 0) : volume E = 0 := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hIoc : volume (E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) = 0 := by
    refine le_antisymm ?_ zero_le
    have hsub : E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) ⊆ (E ∩ Set.Ioo (-Real.pi) Real.pi) ∪ {Real.pi} := by
      rintro x ⟨hx, hx1, hx2⟩
      rcases lt_or_eq_of_le hx2 with h | h
      · exact Or.inl ⟨hx, hx1, by linarith⟩
      · exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)
    calc volume (E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))
        ≤ volume ((E ∩ Set.Ioo (-Real.pi) Real.pi) ∪ {Real.pi}) := measure_mono hsub
      _ ≤ volume (E ∩ Set.Ioo (-Real.pi) Real.pi) + volume ({Real.pi} : Set ℝ) := measure_union_le _ _
      _ = 0 := by rw [h0, Real.volume_singleton, add_zero]
  have hn : ∀ n : ℤ, volume (E ∩ Set.Ioc (-Real.pi + n • (2 * Real.pi)) (-Real.pi + (n + 1) • (2 * Real.pi))) = 0 := by
    intro n
    have e : E ∩ Set.Ioc (-Real.pi + n • (2 * Real.pi)) (-Real.pi + (n + 1) • (2 * Real.pi)) =
        (fun x => x + -(n * (2 * Real.pi))) ⁻¹' (E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, zsmul_eq_mul]
      have hx := hper (-n) x
      push_cast at hx
      rw [show x + -(n * (2 * Real.pi)) = x + -(n : ℝ) * (2 * Real.pi) by ring, hx]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by linarith, by push_cast at h3; linarith⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by linarith, by push_cast; linarith⟩
    rw [e, measure_preimage_add_right, hIoc]
  have hU : E = ⋃ n : ℤ, E ∩ Set.Ioc (-Real.pi + n • (2 * Real.pi)) (-Real.pi + (n + 1) • (2 * Real.pi)) := by
    rw [← Set.inter_iUnion, iUnion_Ioc_add_zsmul hp, Set.inter_univ]
  rw [hU]
  exact measure_iUnion_null hn

end Internal.AngularPlane

open Internal.AngularPlane in
theorem ae_volume_rotation_planePoint_eq_zero {N : Set Space} (hN : MeasurableSet N) (h0 : volume N = 0) :
    ∀ᵐ p ∂(volume.restrict halfPlane), volume {φ : ℝ | axialRot φ (planePoint p) ∈ N} = 0 := by
  have hmθ : Measurable (fun x : (ℝ × ℝ) × ℝ => N.indicator (1 : Space → ℝ≥0∞) (axialRot x.2 (planePoint x.1))) :=
    (measurable_one.indicator hN).comp continuous_orbitPlane.measurable
  have hmI : Measurable (fun p : ℝ × ℝ => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
      N.indicator (1 : Space → ℝ≥0∞) (axialRot θ (planePoint p))) := hmθ.lintegral_prod_right'
  have h1 := lintegral_eq_cylindrical (N.indicator 1) (measurable_one.indicator hN)
  rw [lintegral_indicator_one hN, h0] at h1
  have hae := (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp measurable_fst).mul hmI)).1 h1.symm
  have hS : ∀ᵐ p ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.univ)),
      volume {φ : ℝ | axialRot φ (planePoint p) ∈ N} = 0 := by
    filter_upwards [hae, ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp hpS
    have hp1 : 0 < p.1 := hpS.1
    have hEm : MeasurableSet {φ : ℝ | axialRot φ (planePoint p) ∈ N} :=
      hN.preimage (continuous_orbitPlane.comp (continuous_const.prodMk continuous_id)).measurable
    have hI : ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, N.indicator (1 : Space → ℝ≥0∞) (axialRot θ (planePoint p)) = 0 := by
      have hp' := hp
      simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at hp'
      rcases hp' with h | h
      · simp only [Function.comp_apply, ENNReal.ofReal_eq_zero] at h
        linarith
      · exact h
    have hI' : volume ({φ : ℝ | axialRot φ (planePoint p) ∈ N} ∩ Set.Ioo (-Real.pi) Real.pi) = 0 := by
      rw [← Measure.restrict_apply hEm, ← lintegral_indicator_one hEm, ← hI]
      rfl
    refine volume_eq_zero_of_periodic (fun n φ => ?_) hI'
    simp only [Set.mem_ofPred_eq, axialRot_add_int_mul]
  exact ae_restrict_of_ae_restrict_of_subset (Set.prod_mono le_rfl (Set.subset_univ _)) hS

open Internal.AngularPlane in
theorem Internal.AngularPlane.quasiMeasurePreserving_of_eq (f : ((ℝ × ℝ) × ℝ) × ℝ → ℝ × Space)
    (hf : f = fun w => (w.1.2, axialRot w.2 (planePoint w.1.1))) :
    Measure.QuasiMeasurePreserving f
      (((volume.restrict halfPlane).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) volume := by
  have hfc : Continuous f := by
    have e : (fun w : ((ℝ × ℝ) × ℝ) × ℝ => (w.1.2, axialRot w.2 (planePoint w.1.1))) =
        fun w => (w.1.2, axialRot w.2 (w.1.1.1 • unitVector 0 + w.1.1.2 • unitVector 2)) := by
      funext w
      rw [planePoint_eq]
    rw [hf, e]
    unfold axialRot
    fun_prop
  refine ⟨hfc.measurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hfc.measurable hs]
  rw [Measure.volume_eq_prod] at hs0
  have hτ := (Measure.measure_prod_null hs).1 hs0
  have hpre : MeasurableSet (f ⁻¹' s) := hfc.measurable hs
  have hg : Measurable (fun x : (ℝ × ℝ) × ℝ => volume (Prod.mk x ⁻¹' (f ⁻¹' s))) :=
    measurable_measure_prodMk_left hpre
  rw [Measure.prod_apply hpre, lintegral_eq_zero_iff hg]
  have hset : MeasurableSet {x : (ℝ × ℝ) × ℝ | volume (Prod.mk x ⁻¹' (f ⁻¹' s)) = 0} :=
    hg (measurableSet_singleton 0)
  have key : ∀ᵐ τ : ℝ, ∀ᵐ p ∂(volume.restrict halfPlane), volume (Prod.mk (p, τ) ⁻¹' (f ⁻¹' s)) = 0 := by
    filter_upwards [hτ] with τ hτ0
    have hsl : MeasurableSet (Prod.mk τ ⁻¹' s) := measurable_prodMk_left hs
    filter_upwards [ae_volume_rotation_planePoint_eq_zero hsl hτ0] with p hp
    rw [hf]
    exact hp
  have key2 : ∀ᵐ x ∂((volume.restrict halfPlane).prod (volume : Measure ℝ)),
      volume (Prod.mk x ⁻¹' (f ⁻¹' s)) = 0 := by
    rw [Measure.ae_prod_iff_ae_ae hset]
    exact (Measure.ae_ae_comm (p := fun (p : ℝ × ℝ) (τ : ℝ) => volume (Prod.mk (p, τ) ⁻¹' (f ⁻¹' s)) = 0)
      hset).2 key
  exact key2

theorem quasiMeasurePreserving_orbitPlane :
    Measure.QuasiMeasurePreserving (fun w : ((ℝ × ℝ) × ℝ) × ℝ => (w.1.2, axialRot w.2 (planePoint w.1.1)))
      (((volume.restrict halfPlane).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) volume :=
  Internal.AngularPlane.quasiMeasurePreserving_of_eq _ rfl

namespace Internal.AngularPlane

open Coercive.Internal.ModeRotation

theorem aestronglyMeasurable_orbitAverage {X : Type*} [NormedAddCommGroup X] {u : ℝ × Space → X}
    (hu : AEStronglyMeasurable u volume) (ι : ℤ × ℤ) (Φ : ℝ → X → ℝ)
    (hΦ : Continuous (fun q : ℝ × X => Φ q.1 q.2)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor ι τ φ * ((Φ φ (u (τ, axialRot φ (planePoint p))) : ℝ) : ℂ)) (volume.restrict halfPlane) := by
  obtain ⟨K, hKdef⟩ : ∃ K : ((ℝ × ℝ) × ℝ) × ℝ → ℂ, K = fun w =>
    expFactor ι w.1.2 w.2 * ((Φ w.2 (u (w.1.2, axialRot w.2 (planePoint w.1.1))) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hK : AEStronglyMeasurable K (((volume.restrict halfPlane : Measure (ℝ × ℝ)).prod volume).prod volume) := by
    rw [hKdef]
    have h1 : AEStronglyMeasurable (fun w : ((ℝ × ℝ) × ℝ) × ℝ => u (w.1.2, axialRot w.2 (planePoint w.1.1)))
        (((volume.restrict halfPlane : Measure (ℝ × ℝ)).prod volume).prod volume) := hu.comp_quasiMeasurePreserving quasiMeasurePreserving_orbitPlane
    have h2 : AEStronglyMeasurable (fun w : ((ℝ × ℝ) × ℝ) × ℝ => (w, u (w.1.2, axialRot w.2 (planePoint w.1.1))))
        (((volume.restrict halfPlane : Measure (ℝ × ℝ)).prod volume).prod volume) := aestronglyMeasurable_id.prodMk h1
    have hc : Continuous (fun q : (((ℝ × ℝ) × ℝ) × ℝ) × X =>
        expFactor ι q.1.1.2 q.1.2 * ((Φ q.1.2 q.2 : ℝ) : ℂ)) :=
      ((continuous_expFactor ι).comp ((continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_fst))).mul
        (Complex.continuous_ofReal.comp (hΦ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    have h3 := hc.comp_aestronglyMeasurable h2
    exact h3
  have hmu : ((volume.restrict halfPlane : Measure (ℝ × ℝ)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      = (((volume.restrict halfPlane : Measure (ℝ × ℝ)).prod volume).prod volume).restrict
          ((Set.univ ×ˢ Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ]
  have hK' : AEStronglyMeasurable K (((volume.restrict halfPlane : Measure (ℝ × ℝ)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [hmu]
    exact hK.restrict
  have h3 := hK'.integral_prod_right'.integral_prod_right'
  have e : (fun p : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor ι τ φ * ((Φ φ (u (τ, axialRot φ (planePoint p))) : ℝ) : ℂ)) =
      fun p => ∫ τ in Set.Ioc (0 : ℝ) 1, ∫ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), K ((p, τ), φ) := by
    funext p
    rw [intervalIntegral.integral_of_le zero_le_one]
    congr 1
    funext τ
    rw [intervalIntegral.integral_of_le (by positivity), hKdef]
  rw [e]
  exact h3

theorem aestronglyMeasurable_of_coord {β : Type*} [Fintype β] {f : ℝ × ℝ → β → ℂ} {μ : Measure (ℝ × ℝ)}
    (h : ∀ b, AEStronglyMeasurable (fun p => f p b) μ) : AEStronglyMeasurable f μ :=
  (aemeasurable_pi_iff.2 fun b => (h b).aemeasurable).aestronglyMeasurable

end Internal.AngularPlane

open Internal.AngularPlane Coercive.Internal.ModeRotation in
theorem aestronglyMeasurable_labelFields {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (mm : ℕ) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (labelVel mm ι v) (volume.restrict halfPlane) ∧
      AEStronglyMeasurable (labelGrad mm ι G) (volume.restrict halfPlane) ∧
      AEStronglyMeasurable (labelHess mm ι H) (volume.restrict halfPlane) := by
  refine ⟨aestronglyMeasurable_of_coord fun i => ?_, aestronglyMeasurable_of_coord fun ij => ?_,
    aestronglyMeasurable_of_coord fun ijl => ?_⟩
  · have hΦ : Continuous (fun q : ℝ × Space => axialRot (-q.1) q.2 i) := by
      unfold axialRot
      fun_prop
    have h := (aestronglyMeasurable_orbitAverage hv.measurable_velocity (labelHarmonic mm ι)
      (fun φ x => axialRot (-φ) x i) hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [labelVel, modeVel, modeAverage_eq, zero_add]
  · have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
        axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ij.2))) ij.1) := by
      unfold axialRot
      fun_prop
    have h := (aestronglyMeasurable_orbitAverage hv.measurable_gradient (labelHarmonic mm ι)
      (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ij.2))) ij.1) hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [labelGrad, modeGrad, modeAverage_eq, zero_add]
  · have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
      unfold axialRot
      fun_prop
    have h := (aestronglyMeasurable_orbitAverage hv.measurable_secondDeriv (labelHarmonic mm ι)
      (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1)
      hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [labelHess, modeSecondDeriv, modeAverage_eq, zero_add]

end TailBand

end CertCell

end Breakdown
