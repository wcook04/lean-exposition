import Breakdown.Cert.CoerciveSmoothBase
import Breakdown.Cert.CoerciveSmoothEnergyIdentitySumSecondPartials
import Breakdown.Cert.CoerciveStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsSumSecondPartials

theorem vort_smooth {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => curlVec (fderiv ℝ (v z.1) z.2)) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (hv.smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
      (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  have e : (fun z : ℝ × Space => curlVec (fderiv ℝ (v z.1) z.2))
      = fun z => StretchInternal.curlCLM (fderiv ℝ (v z.1) z.2) := by
    funext z
    rw [StretchInternal.curlCLM_apply]
  rw [e]
  exact StretchInternal.curlCLM.contDiff.comp h1

private theorem curl_fun_eq {u : Space → Space} (hu : ContDiff ℝ 3 u) (hd : ∀ y, divergenceAt u y = 0) :
    (fun x => -secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) x))
      = fun x => curlVec (fderiv ℝ (fun x => curlVec (fderiv ℝ u x)) x) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hω : ContDiff ℝ 2 (fun x => curlVec (fderiv ℝ u x)) := by
    have e : (fun x => curlVec (fderiv ℝ u x)) = fun x => StretchInternal.curlCLM (fderiv ℝ u x) := by
      funext x
      rw [StretchInternal.curlCLM_apply]
    rw [e]
    exact StretchInternal.curlCLM.contDiff.comp (hu.fderiv_right (m := 2) (by norm_num))
  have hdω : Differentiable ℝ (fun x => curlVec (fderiv ℝ u x)) := hω.differentiable (by norm_num)
  funext x
  ext i
  rw [EnergyIdentityInternal.ssp_curl u hu2 hd x i, EnergyIdentityInternal.curlVec_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [EnergyIdentityInternal.fderiv_component _ (hdω x)]

theorem vort_negSumSecondPartials {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (s : ℝ) (x : Space) :
    curlVec (fderiv ℝ (fun x => -secondDerivTrace (secondDerivField v s x)) x)
      = -secondDerivTrace (secondDerivField (fun s x => curlVec (fderiv ℝ (v s) x)) s x) := by
  have hsm : ContDiff ℝ ∞ (v s) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hu3 : ContDiff ℝ 3 (v s) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu4 : ContDiff ℝ 4 (v s) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hω3 : ContDiff ℝ 3 (fun x => curlVec (fderiv ℝ (v s) x)) := by
    have e : (fun x => curlVec (fderiv ℝ (v s) x)) = fun x => StretchInternal.curlCLM (fderiv ℝ (v s) x) := by
      funext x
      rw [StretchInternal.curlCLM_apply]
    rw [e]
    exact StretchInternal.curlCLM.contDiff.comp (hu4.fderiv_right (m := 3) (by norm_num))
  have hdω : ∀ y, divergenceAt (fun x => curlVec (fderiv ℝ (v s) x)) y = 0 :=
    fun y => SmoothEnergyIdentityInternal.curl_field_div (v s) hu3 y
  have e1 : (fun x => -secondDerivTrace (secondDerivField v s x))
      = fun x => curlVec (fderiv ℝ (fun x => curlVec (fderiv ℝ (v s) x)) x) :=
    curl_fun_eq hu3 (hv.divergence_free s)
  rw [e1]
  have e2 := congrFun (curl_fun_eq hω3 hdω) x
  exact e2.symm

theorem modeVel_neg (ι : ℤ × ℤ) (F : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    modeVel ι (fun s x => -F s x) σ y = -modeVel ι F σ y := by
  funext i
  have e : ∀ τ φ : ℝ, axialRot (-φ) (-F (σ + τ) (axialRot φ y)) i
      = -(axialRot (-φ) (F (σ + τ) (axialRot φ y)) i) := by
    intro τ φ
    rw [← SmoothBaseInternal.rotMap_apply, map_neg, SmoothBaseInternal.rotMap_apply]
    rfl
  unfold modeVel modeAverage
  simp only [e, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg, Pi.neg_apply]

end Internal.SmoothPieceEpsSumSecondPartials

end Coercive

end Breakdown
