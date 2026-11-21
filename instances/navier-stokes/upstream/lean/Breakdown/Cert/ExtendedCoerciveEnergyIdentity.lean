import Breakdown.Cert.ExtendedCoerciveEnergyIdentityStretch
import Breakdown.Cert.ExtendedCoerciveNodes
import Breakdown.Cert.CoerciveSmoothEnergyIdentity

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace EnergyIdentityWeakInternal

open Coercive Coercive.EnergyIdentityInternal Coercive.SmoothEnergyIdentityInternal
open Coercive.SmoothEnergyIdentityInternal.SliceIntegrable

theorem slice_decay {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) :
    0 ≤ D ∧ (∀ y, ‖W σ y‖ ≤ D) ∧ (∀ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖)) ∧
      (∀ y, ‖HW σ y‖ ≤ D / (1 + ‖y‖)) := by
  have r1 : ∀ y : Space, (1 : ℝ) ≤ 1 + ‖y‖ := fun y => by linarith [norm_nonneg y]
  have r0 : ∀ y : Space, (0 : ℝ) < 1 + ‖y‖ := fun y => by linarith [norm_nonneg y]
  have hD0 : 0 ≤ D := by
    have := (norm_nonneg _).trans (hW.decay σ 0).1
    simpa using this
  refine ⟨hD0, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · exact (hW.decay σ y).1.trans (div_le_self hD0 (r1 y))
  · exact (hW.decay σ y).2.1.trans
      (div_le_div_of_nonneg_left hD0 (r0 y) (le_self_pow₀ (r1 y) (by norm_num)))
  · exact (hW.decay σ y).2.2.trans
      (div_le_div_of_nonneg_left hD0 (r0 y) (le_self_pow₀ (r1 y) (by norm_num)))

theorem slice_data (P : ℝ) {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} {v : ℝ → Space → Space} (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v)
    (σ : ℝ) (hs : SliceBounds P v σ) (hm : AEStronglyMeasurable (HW σ))
    (hsym : ∀ᵐ y, ∀ a b, HW σ y a b = HW σ y b a) :
    WeakSliceData (v σ) (W σ) (HW σ) D := by
  obtain ⟨D0, n0, n1, n2⟩ := slice_decay hW σ
  exact
    { hu := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
      hd := hv.divergence_free σ
      i0 := hs.weighted
      i1 := hs.first
      i2 := hs.second
      hW := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
      hWd := hW.divergence_free σ
      D0 := D0
      W0 := n0
      W1 := n1
      W2 := n2
      hHm := hm
      hweak := hW.secondDeriv_weak σ
      hsym := hsym }

theorem zero_flow_decay :
    ∃ D, ∀ (σ : ℝ) (y : Space), ∀ j ≤ 2,
      ‖iteratedFDeriv ℝ j ((fun _ _ => (0 : Space)) σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1) :=
  ⟨0, fun σ y j _ => by simp⟩

theorem advection_integrable (P : ℝ) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ) :
    Integrable (fun y => inner ℝ (advectionPart W v σ y) (-secondDerivTrace (secondDerivField v σ y))) := by
  obtain ⟨hsm, c1, c2, c3, ct, cdt⟩ := slice_cont P v hv σ
  obtain ⟨hD0, nW, nA', -⟩ := slice_decay hW σ
  have hWs : ContDiff ℝ 1 (W σ) := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have w0 : Continuous (W σ) := hWs.continuous
  have w1 : Continuous (fun y => fderiv ℝ (W σ) y) := hWs.continuous_fderiv (by norm_num)
  have c0 : Continuous (v σ) := hsm.continuous
  have cr : Continuous (fun y : Space => ‖v σ y‖ / (1 + ‖y‖)) :=
    c0.norm.div (continuous_const.add continuous_norm) (fun y => by positivity)
  have mH : AEStronglyMeasurable (fun y => ‖secondDerivField v σ y‖) := c2.norm.aestronglyMeasurable
  have mG : AEStronglyMeasurable (fun y => ‖fderiv ℝ (v σ) y‖) := c1.norm.aestronglyMeasurable
  have mr : AEStronglyMeasurable (fun y : Space => ‖v σ y‖ / (1 + ‖y‖)) := cr.aestronglyMeasurable
  have hwr : Integrable (fun y : Space => (‖v σ y‖ / (1 + ‖y‖)) ^ 2) := by
    simpa only [div_pow] using hs.weighted
  have iHG := int_mul mH mG hs.second hs.first
  have iHr := int_mul mH mr hs.second hwr
  refine ((iHG.const_mul (3 * D)).add (iHr.const_mul (3 * D))).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · simp only [secondDerivTrace, secondDerivField, advectionPart]
    exact (Continuous.inner (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_neg]
    have ht := trace_le (secondDerivField v σ y)
    have ha : ‖advectionPart W v σ y‖ ≤ ‖fderiv ℝ (v σ) y‖ * D + D * (‖v σ y‖ / (1 + ‖y‖)) := by
      unfold advectionPart
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact ((fderiv ℝ (v σ) y).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (nW y) (norm_nonneg _))
      · refine ((fderiv ℝ (W σ) y).le_opNorm _).trans ?_
        calc ‖fderiv ℝ (W σ) y‖ * ‖v σ y‖ ≤ D / (1 + ‖y‖) * ‖v σ y‖ :=
              mul_le_mul_of_nonneg_right (nA' y) (norm_nonneg _)
          _ = D * (‖v σ y‖ / (1 + ‖y‖)) := by ring
    have h1 := norm_nonneg (secondDerivTrace (secondDerivField v σ y))
    have h3 : 0 ≤ ‖v σ y‖ / (1 + ‖y‖) := by positivity
    have h4 := norm_nonneg (fderiv ℝ (v σ) y)
    calc ‖advectionPart W v σ y‖ * ‖secondDerivTrace (secondDerivField v σ y)‖
        ≤ (‖fderiv ℝ (v σ) y‖ * D + D * (‖v σ y‖ / (1 + ‖y‖))) * (3 * ‖secondDerivField v σ y‖) :=
          mul_le_mul ha ht h1 (by positivity)
      _ = 3 * D * (‖secondDerivField v σ y‖ * ‖fderiv ℝ (v σ) y‖)
          + 3 * D * (‖secondDerivField v σ y‖ * (‖v σ y‖ / (1 + ‖y‖))) := by ring

theorem stretch_measurable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {v : ℝ → Space → Space} (σ : ℝ) (cv : Continuous (v σ)) (cdv : Continuous (fun y => fderiv ℝ (v σ) y))
    (cdW : Continuous (fun y => fderiv ℝ (W σ) y)) (hm : AEStronglyMeasurable (HW σ)) :
    AEStronglyMeasurable (fun y => stretchFormWith W HW v (gradField v) σ y) := by
  have key : Continuous (fun p : Space × (Space →L[ℝ] Space →L[ℝ] Space) =>
      -(∑ i : Fin 3, ∑ j : Fin 3, curlCLM (fderiv ℝ (v σ) p.1) i
          * ((fderiv ℝ (W σ) p.1 (unitVector j) i + fderiv ℝ (W σ) p.1 (unitVector i) j) / 2)
          * curlCLM (fderiv ℝ (v σ) p.1) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, v σ p.1 m * ∑ a : Fin 3, ∑ b : Fin 3,
            alternatingSymbol j a b * p.2 (unitVector m) (unitVector a) b) * curlCLM (fderiv ℝ (v σ) p.1) j
        + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
            alternatingSymbol i m l * (∑ a : Fin 3, ∑ b : Fin 3,
              alternatingSymbol j a b * p.2 (unitVector m) (unitVector a) b)
              * fderiv ℝ (v σ) p.1 (unitVector j) i * v σ p.1 l) := by
    fun_prop
  have h := key.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hm)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [stretchFormWith, vortGrad, gradField, curlCLM_apply, id]

theorem stretch_integrable (P : ℝ) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ)
    (hm : AEStronglyMeasurable (HW σ)) :
    Integrable (fun y => stretchFormWith W HW v (gradField v) σ y) := by
  obtain ⟨hsm, c1, c2, c3, ct, cdt⟩ := slice_cont P v hv σ
  obtain ⟨hD0, nW, nA', nB⟩ := slice_decay hW σ
  have hWs : ContDiff ℝ 1 (W σ) := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have w1 : Continuous (fun y => fderiv ℝ (W σ) y) := hWs.continuous_fderiv (by norm_num)
  have c0 : Continuous (v σ) := hsm.continuous
  have nA : ∀ y, ‖fderiv ℝ (W σ) y‖ ≤ D := fun y =>
    (nA' y).trans (div_le_self hD0 (by linarith [norm_nonneg y]))
  have cr : Continuous (fun y : Space => ‖v σ y‖ / (1 + ‖y‖)) :=
    c0.norm.div (continuous_const.add continuous_norm) (fun y => by positivity)
  have mG : AEStronglyMeasurable (fun y => ‖fderiv ℝ (v σ) y‖) := c1.norm.aestronglyMeasurable
  have mr : AEStronglyMeasurable (fun y : Space => ‖v σ y‖ / (1 + ‖y‖)) := cr.aestronglyMeasurable
  have hwr : Integrable (fun y : Space => (‖v σ y‖ / (1 + ‖y‖)) ^ 2) := by
    simpa only [div_pow] using hs.weighted
  have iGr := int_mul mG mr hs.first hwr
  set K := ‖curlCLM‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ((hs.first.const_mul (9 * (K * K) * D)).add
    (iGr.const_mul (81 * K * D + 729 / 2 * D))).mono' (stretch_measurable σ c0 c1 w1 hm)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  set G := fderiv ℝ (v σ) y with hG
  set A := fderiv ℝ (W σ) y with hA
  set B := HW σ y with hB
  have hGc : ∀ i, |curlVec G i| ≤ K * ‖G‖ := fun i => (comp_le _ i).trans (curl_le G)
  have hAs : ∀ i j : Fin 3, |(A (unitVector j) i + A (unitVector i) j) / 2| ≤ ‖A‖ := by
    intro i j
    rw [abs_div, abs_two]
    have := abs_add_le (A (unitVector j) i) (A (unitVector i) j)
    have := entry_le A i j
    have := entry_le A j i
    linarith
  have T1 : |∑ i : Fin 3, ∑ j : Fin 3, curlVec G i * ((A (unitVector j) i + A (unitVector i) j) / 2)
      * curlVec G j| ≤ 3 * (3 * (K * ‖G‖ * ‖A‖ * (K * ‖G‖))) :=
    sum3 _ _ fun i => sum3 _ _ fun j => prod3 (hGc i) (hAs i j) (hGc j)
  have T2 : |∑ j : Fin 3, (∑ m : Fin 3, v σ y m * vortGrad B j m) * curlVec G j|
      ≤ 3 * (3 * (‖v σ y‖ * (3 * (3 * ‖B‖))) * (K * ‖G‖)) :=
    sum3 _ _ fun j => prod2 (sum3 _ _ fun m => prod2 (comp_le _ m) (vort_le B j m)) (hGc j)
  have T3 : |∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
      alternatingSymbol i m l * vortGrad B j m * G (unitVector j) i * v σ y l|
      ≤ 3 * (3 * (3 * (3 * (1 * (3 * (3 * ‖B‖)) * ‖G‖ * ‖v σ y‖)))) :=
    sum3 _ _ fun i => sum3 _ _ fun m => sum3 _ _ fun l => sum3 _ _ fun j =>
      prod4 (eps_le i m l) (vort_le B j m) (entry_le G i j) (comp_le _ l)
  have hs3 : |stretchFormWith W HW v (gradField v) σ y| ≤
      3 * (3 * (K * ‖G‖ * ‖A‖ * (K * ‖G‖)))
      + 3 * (3 * (‖v σ y‖ * (3 * (3 * ‖B‖))) * (K * ‖G‖))
      + 1 / 2 * (3 * (3 * (3 * (3 * (1 * (3 * (3 * ‖B‖)) * ‖G‖ * ‖v σ y‖))))) := by
    unfold stretchFormWith
    simp only [gradField]
    rw [← hG, ← hA, ← hB]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ T2)) ?_)
    · rw [abs_neg]
      exact T1
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left T3 (by norm_num)
  refine hs3.trans ?_
  have g0 := norm_nonneg G
  have u0 := norm_nonneg (v σ y)
  have hAD := nA y
  have hBD := nB y
  rw [← hA] at hAD
  rw [← hB] at hBD
  have r0 : (0 : ℝ) < 1 + ‖y‖ := by positivity
  calc 3 * (3 * (K * ‖G‖ * ‖A‖ * (K * ‖G‖)))
      + 3 * (3 * (‖v σ y‖ * (3 * (3 * ‖B‖))) * (K * ‖G‖))
      + 1 / 2 * (3 * (3 * (3 * (3 * (1 * (3 * (3 * ‖B‖)) * ‖G‖ * ‖v σ y‖)))))
      ≤ 3 * (3 * (K * ‖G‖ * D * (K * ‖G‖)))
      + 3 * (3 * (‖v σ y‖ * (3 * (3 * (D / (1 + ‖y‖))))) * (K * ‖G‖))
      + 1 / 2 * (3 * (3 * (3 * (3 * (1 * (3 * (3 * (D / (1 + ‖y‖)))) * ‖G‖ * ‖v σ y‖))))) := by
        gcongr
    _ = 9 * (K * K) * D * ‖G‖ ^ 2 + (81 * K * D + 729 / 2 * D) * (‖G‖ * (‖v σ y‖ / (1 + ‖y‖))) := by
        field_simp
        ring

theorem stretch_slice_weak (P : ℝ) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ)
    (hm : AEStronglyMeasurable (HW σ)) (hsym : ∀ᵐ y, ∀ a b, HW σ y a b = HW σ y b a) :
    ∫ y, inner ℝ (advectionPart W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ y, stretchFormWith W HW v (gradField v) σ y :=
  stretch_weak (slice_data P hW hv σ hs hm hsym)

theorem slice_identity_weak (P : ℝ) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ)
    (hm : AEStronglyMeasurable (HW σ)) (hsym : ∀ᵐ y, ∀ a b, HW σ y a b = HW σ y b a) :
    ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      (1 / P) * (∫ y, timePair v σ y)
      + ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y) := by
  obtain ⟨i1, i2, -, -, i5, i6, -⟩ :=
    slice_integrable P (fun _ _ => (0 : Space)) v contDiff_const zero_flow_decay hv σ hs
  have i3 := advection_integrable P hW hv σ hs
  have i7 := stretch_integrable P hW hv σ hs hm
  simp_rw [smoothRight_split]
  rw [integral_add _ i3, integral_add i1 i2, integral_add _ i7, integral_add i5 i6,
    transport_slice P v hv σ hs, sumSecondPartials_slice P v hv σ hs, stretch_slice_weak P hW hv σ hs hm hsym]
  all_goals first | exact i5.add i6 | exact i1.add i2 | ring

end EnergyIdentityWeakInternal

open EnergyIdentityWeakInternal Coercive Coercive.SmoothEnergyIdentityInternal in
theorem energyIdentitySmoothWeak_of_symmetric (hH : WeakSecondDerivSymmetricHolds) :
    EnergyIdentitySmoothWeakHolds := by
  intro P W HW D v _ hW hv
  have hm : ∀ᵐ σ, AEStronglyMeasurable (HW σ) :=
    AEStronglyMeasurable.prodMk_left (f := fun z : ℝ × Space => HW z.1 z.2) hW.secondDeriv_measurable
  have hae : (fun σ => ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun σ => (1 / P) * (∫ y, timePair v σ y)
        + ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
          + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y) := by
    filter_upwards [slice_bounds_ae P v hv, ae_restrict_of_ae hm] with σ hs hmσ
    exact slice_identity_weak P hW hv σ hs hmσ (hH hW σ)
  rw [integral_congr_ae hae]
  have hT : Integrable (fun σ => (1 / P) * ∫ y, timePair v σ y) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (time_integrable P v hv).const_mul _
  by_cases hR : Integrable (fun σ => ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
      + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y))
      (volume.restrict (Set.Icc (0 : ℝ) 1))
  · rw [integral_add hT hR, integral_const_mul, time_term_zero P v hv, mul_zero, zero_add]
  · have hS : ¬ Integrable (fun σ => (1 / P) * (∫ y, timePair v σ y)
        + ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
          + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y))
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      intro h
      refine hR ((h.sub hT).congr (Eventually.of_forall fun σ => ?_))
      simp only [Pi.sub_apply]
      ring
    rw [integral_undef hS, integral_undef hR]

end CoerciveWeak

end Breakdown
