import Breakdown.Cert.CoerciveSmoothBase
import Breakdown.Cert.CoercivePieceFieldCurlWeightSumSecondPartials
import Breakdown.Cert.CoerciveStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsSumSecondPartials

open SmoothBaseInternal BaseDensityInternal

private theorem field_fderiv_smooth {U : ℝ → Space → Space} (hU : ContDiff ℝ ∞ (fun z : ℝ × Space => U z.1 z.2))
    (s : ℝ) : ContDiff ℝ ∞ (fderiv ℝ (U s)) := by
  have hf : ContDiff ℝ ∞ (U s) := hU.comp (contDiff_const.prodMk contDiff_id)
  exact hf.fderiv_right (m := ∞) (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])

private theorem field_mode_derivatives {U : ℝ → Space → Space}
    (hU : ContDiff ℝ ∞ (fun z : ℝ × Space => U z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ) :
    (ContDiff ℝ 2 fun y => reVec (modeVel ι U σ y)) ∧ (ContDiff ℝ 2 fun y => imVec (modeVel ι U σ y)) ∧
      (∀ y, fderiv ℝ (fun y => reVec (modeVel ι U σ y)) y = reMat (modeGrad ι (gradField U) σ y)) ∧
      (∀ y, fderiv ℝ (fun y => imVec (modeVel ι U σ y)) y = imMat (modeGrad ι (gradField U) σ y)) ∧
      (∀ l : Fin 3,
        (∀ y, fderiv ℝ (fun y => reVec (fun i => modeGrad ι (gradField U) σ y (i, l))) y =
          reMat (fun mj => modeSecondDeriv ι (secondDerivField U) σ y (mj.1, mj.2, l))) ∧
        (∀ y, fderiv ℝ (fun y => imVec (fun i => modeGrad ι (gradField U) σ y (i, l))) y =
          imMat (fun mj => modeSecondDeriv ι (secondDerivField U) σ y (mj.1, mj.2, l)))) := by
  have hfv : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => U (σ + p.1) p.2.2 :=
    hU.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd.snd)
  obtain ⟨a1, a2, a3, a4⟩ := mode_field ι (f := fun τ _ => U (σ + τ)) hfv
  refine ⟨a1, a2, a3, a4, fun l => ?_⟩
  have hDv : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => fderiv ℝ (U (σ + p.1)) p.2.2 :=
    ContDiff.fderiv (f := fun (p : ℝ × ℝ × Space) (z : Space) => U (σ + p.1) z) (g := fun p => p.2.2)
      (hU.comp ((contDiff_const.add contDiff_fst.fst).prodMk contDiff_snd)) contDiff_snd.snd
      (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  have hfl : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space =>
      (fun (τ φ : ℝ) (z : Space) => fderiv ℝ (U (σ + τ)) z (axialRot φ (unitVector l))) p.1 p.2.1 p.2.2 := by
    have e : (fun p : ℝ × ℝ × Space => fderiv ℝ (U (σ + p.1)) p.2.2 (axialRot p.2.1 (unitVector l))) =
        fun p => fderiv ℝ (U (σ + p.1)) p.2.2 (rotMap p.2.1 (unitVector l)) := by
      funext p; rw [rotMap_apply]
    show ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => fderiv ℝ (U (σ + p.1)) p.2.2 (axialRot p.2.1 (unitVector l))
    rw [e]
    exact hDv.clm_apply ((rotMap_contDiff.comp contDiff_snd.fst).clm_apply contDiff_const)
  obtain ⟨-, -, b3, b4⟩ := mode_field ι
    (f := fun (τ φ : ℝ) (z : Space) => fderiv ℝ (U (σ + τ)) z (axialRot φ (unitVector l))) hfl
  have hcol' : ∀ s z a b, fderiv ℝ (fun x => fderiv ℝ (U s) x b) z a = fderiv ℝ (fderiv ℝ (U s)) z a b := by
    intro s z a b
    rw [fderiv_clm_apply (((field_fderiv_smooth hU s).differentiable (by simp)) z) (differentiableAt_const _)]
    simp
  have hg : ∀ y, (fun ij : Fin 3 × Fin 3 => modeAverage ι (fun τ φ (ij : Fin 3 × Fin 3) =>
      axialRot (-φ) (fderiv ℝ (fun z => fderiv ℝ (U (σ + τ)) z (axialRot φ (unitVector l))) (axialRot φ y)
        (axialRot φ (unitVector ij.2))) ij.1) ij) =
      fun mj => modeSecondDeriv ι (secondDerivField U) σ y (mj.1, mj.2, l) := by
    intro y
    funext mj
    unfold modeSecondDeriv modeAverage
    congr 1
    refine intervalIntegral.integral_congr fun τ _ => intervalIntegral.integral_congr fun φ _ => ?_
    simp only [secondDerivField]
    rw [hcol']
  exact ⟨fun y => by rw [← hg y]; exact b3 y, fun y => by rw [← hg y]; exact b4 y⟩

private theorem field_secondDeriv_continuous {U : ℝ → Space → Space}
    (hU : ContDiff ℝ ∞ (fun z : ℝ × Space => U z.1 z.2)) :
    Continuous (fun z : ℝ × Space => secondDerivField U z.1 z.2) := by
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (U z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => U z.1 y) (g := fun z => z.2)
      (hU.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have h2 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (U z.1) x) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => fderiv ℝ (U z.1) y) (g := fun z => z.2)
      (h1.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  exact h2.continuous

private theorem trace_of_columns {P : Space → Space} (hP : ContDiff ℝ 2 P) {M : Space → (Space →L[ℝ] Space)}
    (hM : ∀ y, fderiv ℝ P y = M y) {c : Fin 3 → Space → Space} (hc : ∀ j y, M y (unitVector j) = c j y)
    {D : Fin 3 → Space → (Space →L[ℝ] Space)} (hD : ∀ j y, fderiv ℝ (c j) y = D j y) (y : Space) :
    secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ P x) y) = ∑ j : Fin 3, D j y (unitVector j) := by
  have hPM : (fun x => fderiv ℝ P x) = M := funext hM
  have hMd : Differentiable ℝ M := by
    rw [← hPM]
    exact (hP.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold secondDerivTrace
  rw [hPM]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcj : c j = fun x => M x (unitVector j) := funext fun x => (hc j x).symm
  rw [← hD j y, hcj, fderiv_clm_apply (hMd y) (differentiableAt_const _)]
  simp

private theorem reMat_unit (g : Fin 3 × Fin 3 → ℂ) (j : Fin 3) :
    reMat g (unitVector j) = reVec (fun i => g (i, j)) := by
  ext l
  rw [reMat_apply, reVec_apply]

private theorem imMat_unit (g : Fin 3 × Fin 3 → ℂ) (j : Fin 3) :
    imMat g (unitVector j) = imVec (fun i => g (i, j)) := by
  ext l
  rw [imMat_apply, imVec_apply]

private theorem reVec_sum (x : Fin 3 → Fin 3 → ℂ) :
    ∑ j : Fin 3, reVec (x j) = reVec (fun i => ∑ j : Fin 3, x j i) := by
  unfold reVec
  simp only [Complex.re_sum, Finset.sum_smul]
  exact Finset.sum_comm

private theorem imVec_sum (x : Fin 3 → Fin 3 → ℂ) :
    ∑ j : Fin 3, imVec (x j) = imVec (fun i => ∑ j : Fin 3, x j i) := by
  unfold imVec
  simp only [Complex.im_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem field_mode_sumSecondPartials {U : ℝ → Space → Space} (hU : ContDiff ℝ ∞ (fun z : ℝ × Space => U z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) :
    (ContDiff ℝ 2 fun y => reVec (modeVel ι U σ y)) ∧ (ContDiff ℝ 2 fun y => imVec (modeVel ι U σ y)) ∧
      (∀ y, secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (fun y => reVec (modeVel ι U σ y)) x) y)
        = reVec (modeVel ι (fun s x => secondDerivTrace (secondDerivField U s x)) σ y)) ∧
      (∀ y, secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (fun y => imVec (modeVel ι U σ y)) x) y)
        = imVec (modeVel ι (fun s x => secondDerivTrace (secondDerivField U s x)) σ y)) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := field_mode_derivatives hU ι σ
  have hc := field_secondDeriv_continuous hU
  have htr : ∀ y, (fun i => ∑ j : Fin 3, modeSecondDeriv ι (secondDerivField U) σ y (i, j, j)) =
      modeVel ι (fun s x => secondDerivTrace (secondDerivField U s x)) σ y := by
    intro y
    funext i
    have hrot : Continuous (fun p : ℝ × ℝ => axialRot p.2 y) := by
      have e : (fun p : ℝ × ℝ => axialRot p.2 y) = fun p => rotMap p.2 y := funext fun p => (rotMap_apply _ _).symm
      rw [e]
      exact (rotMap_contDiff.continuous.comp continuous_snd).clm_apply continuous_const
    have hz : Integrable (fun p : ℝ × ℝ => secondDerivField U (σ + p.1) (axialRot p.2 y))
        Internal.ModeRotation.boxMeasure :=
      StretchInternal.integrable_box_of_continuous
        (hc.comp ((continuous_const.add continuous_fst).prodMk hrot))
    exact CurlWeight.Internal.SumSecondPartialsModes.modeSecondDeriv_trace_eq (z := (σ, y)) ι hz i
  refine ⟨a1, a2, fun y => ?_, fun y => ?_⟩
  · rw [trace_of_columns a1 a3 (fun j x => reMat_unit _ j) (fun j x => (a5 j).1 x) y]
    simp only [reMat_unit]
    rw [reVec_sum, htr]
  · rw [trace_of_columns a2 a4 (fun j x => imMat_unit _ j) (fun j x => (a5 j).2 x) y]
    simp only [imMat_unit]
    rw [imVec_sum, htr]

end Internal.SmoothPieceEpsSumSecondPartials

end Coercive

end Breakdown
