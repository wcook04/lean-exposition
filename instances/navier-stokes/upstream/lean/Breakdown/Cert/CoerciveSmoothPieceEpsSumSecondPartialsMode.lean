import Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsField
import Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsCurl
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoerciveSmoothEnergyIdentitySumSecondPartials
import Breakdown.Cert.CoerciveStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsSumSecondPartials

private def crossMap (j : Fin 3) : Space →L[ℝ] Space :=
  ∑ k : Fin 3, ∑ l : Fin 3, alternatingSymbol k j l • (EuclideanSpace.proj l : Space →L[ℝ] ℝ).smulRight (unitVector k)

private theorem crossMap_coord (j : Fin 3) (x : Space) (k : Fin 3) :
    crossMap j x k = ∑ l : Fin 3, alternatingSymbol k j l * x l := by
  simp [crossMap, unitVector, Pi.single_apply, mul_ite, Finset.sum_ite_eq]

private theorem reVec_curl (g : Fin 3 × Fin 3 → ℂ) :
    reVec (curlOfGrad g) = ∑ j : Fin 3, crossMap j (reVec (fun i => g (i, j))) := by
  ext k
  rw [CurlWeight.Internal.SumSecondPartialsModes.reVec_coord]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, crossMap_coord, CurlWeight.Internal.SumSecondPartialsModes.reVec_coord, curlOfGrad,
    Complex.re_sum, Complex.re_ofReal_mul]

private theorem imVec_curl (g : Fin 3 × Fin 3 → ℂ) :
    imVec (curlOfGrad g) = ∑ j : Fin 3, crossMap j (imVec (fun i => g (i, j))) := by
  ext k
  rw [CurlWeight.Internal.SumSecondPartialsModes.imVec_coord]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, crossMap_coord, CurlWeight.Internal.SumSecondPartialsModes.imVec_coord, curlOfGrad,
    Complex.im_sum, Complex.im_ofReal_mul]

private theorem vortRe_eq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) :
    (fun y => reVec (curlOfGrad (modeGrad ι (gradField v) σ y)))
      = fun y => ∑ j : Fin 3, crossMap j (reVec (fun i => modeGrad ι (gradField v) σ y (i, j))) :=
  funext fun _ => reVec_curl _

private theorem vortIm_eq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) :
    (fun y => imVec (curlOfGrad (modeGrad ι (gradField v) σ y)))
      = fun y => ∑ j : Fin 3, crossMap j (imVec (fun i => modeGrad ι (gradField v) σ y (i, j))) :=
  funext fun _ => imVec_curl _

theorem vortRe_contDiff {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) :
    ContDiff ℝ 2 (fun y => reVec (curlOfGrad (modeGrad ι (gradField v) σ y))) := by
  rw [vortRe_eq]
  exact ContDiff.sum fun j _ => (crossMap j).contDiff.comp ((SmoothBaseInternal.smooth_mode_derivatives hv ι σ).2.2.2.2 j).1

theorem vortIm_contDiff {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) :
    ContDiff ℝ 2 (fun y => imVec (curlOfGrad (modeGrad ι (gradField v) σ y))) := by
  rw [vortIm_eq]
  exact ContDiff.sum fun j _ => (crossMap j).contDiff.comp ((SmoothBaseInternal.smooth_mode_derivatives hv ι σ).2.2.2.2 j).2.1

theorem fderiv_vortRe_apply {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) (l : Fin 3) :
    fderiv ℝ (fun y => reVec (curlOfGrad (modeGrad ι (gradField v) σ y))) y (unitVector l)
      = ∑ i : Fin 3, (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l)).re • unitVector i := by
  obtain ⟨-, -, -, -, h5⟩ := SmoothBaseInternal.smooth_mode_derivatives hv ι σ
  have hd : HasFDerivAt (fun y => ∑ j : Fin 3, crossMap j (reVec (fun i => modeGrad ι (gradField v) σ y (i, j))))
      (∑ j : Fin 3, (crossMap j).comp (fderiv ℝ (fun y => reVec (fun i => modeGrad ι (gradField v) σ y (i, j))) y)) y :=
    HasFDerivAt.fun_sum fun j _ => (crossMap j).hasFDerivAt.comp y (((h5 j).1.differentiable (by norm_num)) y).hasFDerivAt
  rw [vortRe_eq, hd.fderiv]
  change _ = reVec (fun i => curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l))
  ext k
  rw [CurlWeight.Internal.SumSecondPartialsModes.reVec_coord]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    WithLp.ofLp_sum, crossMap_coord, (h5 _).2.2.1 y, CurlWeight.Internal.SumSecondPartialsModes.reMat_coord, curlGradOfSecondDeriv,
    Complex.re_sum, Complex.re_ofReal_mul]

theorem fderiv_vortIm_apply {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) (l : Fin 3) :
    fderiv ℝ (fun y => imVec (curlOfGrad (modeGrad ι (gradField v) σ y))) y (unitVector l)
      = ∑ i : Fin 3, (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l)).im • unitVector i := by
  obtain ⟨-, -, -, -, h5⟩ := SmoothBaseInternal.smooth_mode_derivatives hv ι σ
  have hd : HasFDerivAt (fun y => ∑ j : Fin 3, crossMap j (imVec (fun i => modeGrad ι (gradField v) σ y (i, j))))
      (∑ j : Fin 3, (crossMap j).comp (fderiv ℝ (fun y => imVec (fun i => modeGrad ι (gradField v) σ y (i, j))) y)) y :=
    HasFDerivAt.fun_sum fun j _ => (crossMap j).hasFDerivAt.comp y (((h5 j).2.1.differentiable (by norm_num)) y).hasFDerivAt
  rw [vortIm_eq, hd.fderiv]
  change _ = imVec (fun i => curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) (i, l))
  ext k
  rw [CurlWeight.Internal.SumSecondPartialsModes.imVec_coord]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    WithLp.ofLp_sum, crossMap_coord, (h5 _).2.2.2 y, CurlWeight.Internal.SumSecondPartialsModes.imMat_coord, curlGradOfSecondDeriv,
    Complex.im_sum, Complex.im_ofReal_mul]

private theorem joint_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : ContDiff ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
  ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => F z.1 y) (g := fun z => z.2)
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])

private theorem negSumSecondPartials_smooth {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => -secondDerivTrace (secondDerivField v z.1 z.2)) := by
  have hH : ContDiff ℝ ∞ (fun z : ℝ × Space => secondDerivField v z.1 z.2) :=
    joint_fderiv (F := fun s x => fderiv ℝ (v s) x) (joint_fderiv hv.smooth)
  unfold secondDerivTrace
  exact (ContDiff.sum fun j _ => (hH.clm_apply contDiff_const).clm_apply contDiff_const).neg

private theorem rot_continuous (y : Space) : Continuous (fun p : ℝ × ℝ => axialRot p.2 y) := by
  unfold axialRot
  fun_prop

theorem curl_sumSecondPartials_mode {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) (i : Fin 3) :
    curlOfGrad (modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y) i
      = -(((secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ
            (fun y => reVec (curlOfGrad (modeGrad ι (gradField v) σ y))) x) y) i : ℝ) : ℂ)
        + ((secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ
            (fun y => imVec (curlOfGrad (modeGrad ι (gradField v) σ y))) x) y) i : ℝ) : ℂ) * Complex.I) := by
  have hU : ContDiff ℝ ∞ (fun z : ℝ × Space => curlVec (fderiv ℝ (v z.1) z.2)) := vort_smooth hv
  have hGc := (SmoothBaseInternal.smooth_fields_continuous hv).2.1
  have hmode : ∀ y, curlOfGrad (modeGrad ι (gradField v) σ y)
      = modeVel ι (fun s x => curlVec (fderiv ℝ (v s) x)) σ y := fun y =>
    Internal.CurlEnergy.curlOfGrad_modeGrad_eq (z := (σ, y)) ι
      (StretchInternal.integrable_box_of_continuous
        (hGc.comp ((continuous_const.add continuous_fst).prodMk (rot_continuous y))))
  have eRe : (fun y => reVec (curlOfGrad (modeGrad ι (gradField v) σ y)))
      = fun y => reVec (modeVel ι (fun s x => curlVec (fderiv ℝ (v s) x)) σ y) :=
    funext fun y => by rw [hmode y]
  have eIm : (fun y => imVec (curlOfGrad (modeGrad ι (gradField v) σ y)))
      = fun y => imVec (modeVel ι (fun s x => curlVec (fderiv ℝ (v s) x)) σ y) :=
    funext fun y => by rw [hmode y]
  obtain ⟨-, -, h3, h4⟩ := field_mode_sumSecondPartials (U := fun s x => curlVec (fderiv ℝ (v s) x)) hU ι σ
  rw [eRe, eIm, h3 y, h4 y, CurlWeight.Internal.SumSecondPartialsModes.reVec_coord,
    CurlWeight.Internal.SumSecondPartialsModes.imVec_coord, Complex.re_add_im]
  have hNc : Continuous (fun z : ℝ × Space =>
      gradField (fun s x => -secondDerivTrace (secondDerivField v s x)) z.1 z.2) :=
    (joint_fderiv (F := fun s x => -secondDerivTrace (secondDerivField v s x)) (negSumSecondPartials_smooth hv)).continuous
  rw [Internal.CurlEnergy.curlOfGrad_modeGrad_eq (z := (σ, y)) ι
    (StretchInternal.integrable_box_of_continuous
      (hNc.comp ((continuous_const.add continuous_fst).prodMk (rot_continuous y))))]
  have e : (fun s x => curlVec (gradField (fun s x => -secondDerivTrace (secondDerivField v s x)) s x))
      = fun s x => -secondDerivTrace (secondDerivField (fun s x => curlVec (fderiv ℝ (v s) x)) s x) :=
    funext fun s => funext fun x => vort_negSumSecondPartials hv s x
  rw [e, modeVel_neg]
  rfl

end Internal.SmoothPieceEpsSumSecondPartials

end Coercive

end Breakdown
