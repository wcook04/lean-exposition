import Breakdown.Torus.StatementsApprox

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace SelfSimilar.Internal

theorem slice_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : ℝ → Space → F}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Space => G z.1 z.2)) (s : ℝ) : ContDiff ℝ ∞ (G s) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem hasFDerivAt_scaled {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F)
    (a : ℝ) (c x : Space) (hf : DifferentiableAt ℝ f (a • (x - c))) :
    HasFDerivAt (fun z : Space => f (a • (z - c)))
      ((fderiv ℝ f (a • (x - c))).comp (a • ContinuousLinearMap.id ℝ Space)) x := by
  have h1 : HasFDerivAt (fun z : Space => a • (z - c)) (a • ContinuousLinearMap.id ℝ Space) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul a
  exact hf.hasFDerivAt.comp x h1

theorem fderiv_scaledField_apply (f : Space → Space) (r : ℝ) (x v : Space)
    (hf : Differentiable ℝ f) :
    fderiv ℝ (fun z : Space => r • f (r • (z - center))) x v
      = (r * r) • fderiv ℝ f (r • (x - center)) v := by
  have h : HasFDerivAt (fun z : Space => r • f (r • (z - center)))
      (r • (fderiv ℝ f (r • (x - center))).comp (r • ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_scaled f r center x (hf _)).const_smul r
  rw [h.fderiv]
  simp [smul_smul]

theorem fderiv_scaledPressure_apply (f : Space → ℝ) (a r : ℝ) (x v : Space)
    (hf : Differentiable ℝ f) :
    fderiv ℝ (fun z : Space => a * f (r • (z - center))) x v
      = (a * r) * fderiv ℝ f (r • (x - center)) v := by
  have h : HasFDerivAt (fun z : Space => a * f (r • (z - center)))
      (a • (fderiv ℝ f (r • (x - center))).comp (r • ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_scaled f r center x (hf _)).const_mul a
  rw [h.fderiv, smul_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul,
    smul_eq_mul, mul_assoc]

theorem iteratedFDeriv_two_scaledField (f : Space → Space) (r : ℝ) (x : Space) (m : Fin 2 → Space)
    (hf : ContDiff ℝ ∞ f) :
    iteratedFDeriv ℝ 2 (fun z : Space => r • f (r • (z - center))) x (fun i => m i)
      = (r * r ^ 2) • iteratedFDeriv ℝ 2 f (r • (x - center)) m := by
  have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) f := contDiff_infty.1 hf 2
  set L : Space →L[ℝ] Space := r • ContinuousLinearMap.id ℝ Space with hL
  have hcomp : (fun z : Space => f (r • (z - center))) = fun z => (f ∘ L) (z - center) := by
    funext z
    simp [hL]
  have hinner : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun z : Space => f (r • (z - center))) x := by
    rw [hcomp]
    exact ((h2.comp L.contDiff).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hinner, hcomp, iteratedFDeriv_comp_sub,
    L.iteratedFDeriv_comp_right h2 _ le_rfl, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hm : (fun i : Fin 2 => L (m i)) = fun i => r • m i := by
    funext i
    simp [hL]
  rw [hm, ContinuousMultilinearMap.map_smul_univ, Fin.prod_const, smul_smul]
  simp [hL]

theorem divergence_scaledField (f : Space → Space) (r : ℝ) (x : Space)
    (hf : Differentiable ℝ f) :
    divergenceAt (fun z : Space => r • f (r • (z - center))) x
      = (r * r) * divergenceAt f (r • (x - center)) := by
  unfold divergenceAt
  simp_rw [fderiv_scaledField_apply f r x _ hf]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

theorem advection_scaledField (f : Space → Space) (r : ℝ) (x : Space)
    (hf : Differentiable ℝ f) :
    advectionAt (fun z : Space => r • f (r • (z - center))) x
      = (r * r * r) • advectionAt f (r • (x - center)) := by
  unfold advectionAt
  rw [fderiv_scaledField_apply f r x _ hf, map_smul, smul_smul]

theorem sumSecondPartials_scaledField (f : Space → Space) (r : ℝ) (x : Space)
    (hf : ContDiff ℝ ∞ f) :
    sumSecondPartialsAt (fun z : Space => r • f (r • (z - center))) x
      = (r * r ^ 2) • sumSecondPartialsAt f (r • (x - center)) := by
  unfold sumSecondPartialsAt
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := iteratedFDeriv_two_scaledField f r x ![unitVector i, unitVector i] hf
  simpa using this

theorem gradient_scaledPressure (f : Space → ℝ) (a r : ℝ) (x : Space)
    (hf : Differentiable ℝ f) :
    gradientAt (fun z : Space => a * f (r • (z - center))) x
      = (a * r) • gradientAt f (r • (x - center)) := by
  unfold gradientAt
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_scaledPressure_apply f a r x _ hf, smul_smul]

theorem differentiable_of_smooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (h : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  (contDiff_infty.1 h 1).differentiable (by norm_num)

theorem scaleFactor_mul_self (T t : ℝ) (ht : t < T) :
    (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) = (T - t)⁻¹ := by
  rw [← rpow_add (sub_pos.2 ht), show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, rpow_neg_one]

theorem hasDerivAt_similarityTime (T t : ℝ) (hT : 0 < T) (ht : t < T) :
    HasDerivAt (fun τ => similarityTime T τ) (T - t)⁻¹ t := by
  have hp : 0 < T - t := sub_pos.2 ht
  have h1 : HasDerivAt (fun τ : ℝ => (T - τ) / T) ((0 - 1) / T) t :=
    ((hasDerivAt_const t T).sub (hasDerivAt_id' t)).div_const T
  have h2 : HasDerivAt (fun τ => similarityTime T τ) (-(((0 - 1) / T) / ((T - t) / T))) t :=
    (h1.log (div_pos hp hT).ne').neg
  convert h2 using 1
  field_simp
  ring

theorem hasDerivAt_scaleFactor (T t : ℝ) (ht : t < T) :
    HasDerivAt (fun τ : ℝ => (T - τ) ^ (-(1 / 2 : ℝ)))
      ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) t := by
  have hp : 0 < T - t := sub_pos.2 ht
  have h1 : HasDerivAt (fun τ : ℝ => T - τ) (0 - 1) t :=
    (hasDerivAt_const t T).sub (hasDerivAt_id' t)
  have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hp.ne')
  convert h2 using 1
  rw [show (-(1 / 2 : ℝ)) - 1 = -(1 / 2) + -(1 / 2) + -(1 / 2) by norm_num, rpow_add hp,
    rpow_add hp]
  ring

theorem deriv_time_slice (W : ℝ → Space → Space)
    (hF : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) (y : Space) :
    deriv (fun σ => W σ y) s = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) (1, 0) := by
  have h : HasDerivAt (fun σ : ℝ => (σ, y)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s y)
  exact ((hF (s, y)).hasFDerivAt.comp_hasDerivAt s h).deriv

theorem fderiv_space_slice (W : ℝ → Space → Space)
    (hF : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) (y v : Space) :
    fderiv ℝ (W s) y v = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) (0, v) := by
  have h := (hF (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  have h' : HasFDerivAt (W s)
      ((fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) y := h
  rw [h'.fderiv]
  simp

theorem deriv_selfSimilar (W : ℝ → Space → Space)
    (hF : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2)) (T t : ℝ) (hT : 0 < T) (ht : t < T)
    (x : Space) :
    deriv (fun τ => selfSimilar W T τ x) t =
      (T - t) ^ (-(1 / 2 : ℝ)) • ((T - t)⁻¹ • deriv (fun σ => W σ ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))) (similarityTime T t)
        + ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) •
          fderiv ℝ (W (similarityTime T t)) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center)) (x - center))
      + ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) •
          W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center)) := by
  have hγ : HasDerivAt
      (fun τ => (similarityTime T τ, (T - τ) ^ (-(1 / 2 : ℝ)) • (x - center)))
      ((T - t)⁻¹, ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) • (x - center)) t :=
    (hasDerivAt_similarityTime T t hT ht).prodMk
      ((hasDerivAt_scaleFactor T t ht).smul_const (x - center))
  have hW := (hF _).hasFDerivAt.comp_hasDerivAt t hγ
  have h := (hasDerivAt_scaleFactor T t ht).smul hW
  have h' : HasDerivAt (fun τ => selfSimilar W T τ x)
      ((T - t) ^ (-(1 / 2 : ℝ)) • fderiv ℝ (fun z : ℝ × Space => W z.1 z.2)
          (similarityTime T t, (T - t) ^ (-(1 / 2 : ℝ)) • (x - center))
          ((T - t)⁻¹, ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) • (x - center))
        + ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) •
          W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))) t := h
  rw [h'.deriv]
  have hsplit : (((T - t)⁻¹ : ℝ), ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) • (x - center))
      = (T - t)⁻¹ • ((1 : ℝ), (0 : Space))
        + ((0 : ℝ), ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) • (x - center)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, ← deriv_time_slice W hF, ← fderiv_space_slice W hF, map_smul]

theorem contDiffAt_scaleFactor (T : ℝ) (z : ℝ × Space) (hz : z.1 < T) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => (T - z.1) ^ (-(1 / 2 : ℝ))) z :=
  (contDiffAt_const.sub contDiffAt_fst).rpow_const_of_ne (sub_pos.2 hz).ne'

theorem contDiffAt_similarityTime (T : ℝ) (hT : 0 < T) (z : ℝ × Space) (hz : z.1 < T) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => similarityTime T z.1) z := by
  have h : ContDiffAt ℝ ∞ (fun z : ℝ × Space => (T - z.1) / T) z :=
    (contDiffAt_const.sub contDiffAt_fst).div_const T
  exact (h.log (div_pos (sub_pos.2 hz) hT).ne').neg

theorem contDiffAt_scaledPoint (T : ℝ) (z : ℝ × Space) (hz : z.1 < T) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => (T - z.1) ^ (-(1 / 2 : ℝ)) • (z.2 - center)) z :=
  (contDiffAt_scaleFactor T z hz).smul (contDiffAt_snd.sub contDiffAt_const)

theorem contDiffOn_selfSimilar (W : ℝ → Space → Space) (T : ℝ) (hT : 0 < T)
    (h : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilar W T z.1 z.2) (Iio T ×ˢ univ) := by
  intro z hz
  have hz1 : z.1 < T := hz.1
  have hW : ContDiffAt ℝ ∞ (fun z : ℝ × Space =>
      W (similarityTime T z.1) ((T - z.1) ^ (-(1 / 2 : ℝ)) • (z.2 - center))) z :=
    h.contDiffAt.comp z ((contDiffAt_similarityTime T hT z hz1).prodMk
      (contDiffAt_scaledPoint T z hz1))
  exact ((contDiffAt_scaleFactor T z hz1).smul hW).contDiffWithinAt

theorem contDiffOn_selfSimilarPressure (q : ℝ → Space → ℝ) (T : ℝ) (hT : 0 < T)
    (h : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilarPressure q T z.1 z.2) (Iio T ×ˢ univ) := by
  intro z hz
  have hz1 : z.1 < T := hz.1
  have hq : ContDiffAt ℝ ∞ (fun z : ℝ × Space =>
      q (similarityTime T z.1) ((T - z.1) ^ (-(1 / 2 : ℝ)) • (z.2 - center))) z :=
    h.contDiffAt.comp z ((contDiffAt_similarityTime T hT z hz1).prodMk
      (contDiffAt_scaledPoint T z hz1))
  have hinv : ContDiffAt ℝ ∞ (fun z : ℝ × Space => (T - z.1)⁻¹) z :=
    (contDiffAt_const.sub contDiffAt_fst).inv (sub_pos.2 hz1).ne'
  exact (hinv.mul hq).contDiffWithinAt

end SelfSimilar.Internal

open SelfSimilar.Internal in
theorem selfSimilarSolves : SelfSimilarSolves := by
  intro W q C T hP hT
  have hF : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) :=
    differentiable_of_smooth hP.smooth
  have hWs : ∀ s, ContDiff ℝ ∞ (W s) := slice_contDiff hP.smooth
  have hWd : ∀ s, Differentiable ℝ (W s) := fun s => differentiable_of_smooth (hWs s)
  have hqd : ∀ s, Differentiable ℝ (q s) := fun s =>
    differentiable_of_smooth (slice_contDiff hP.smooth_pressure s)
  refine ⟨contDiffOn_selfSimilar W T hT hP.smooth,
    contDiffOn_selfSimilarPressure q T hT hP.smooth_pressure, fun t ht x => ⟨?_, ?_⟩⟩
  · have h := divergence_scaledField (W (similarityTime T t)) ((T - t) ^ (-(1 / 2 : ℝ))) x (hWd _)
    rw [hP.div, mul_zero] at h
    exact h
  · have hA := advection_scaledField (W (similarityTime T t)) ((T - t) ^ (-(1 / 2 : ℝ))) x (hWd _)
    have hL := sumSecondPartials_scaledField (W (similarityTime T t)) ((T - t) ^ (-(1 / 2 : ℝ))) x (hWs _)
    have hG := gradient_scaledPressure (q (similarityTime T t)) (T - t)⁻¹ ((T - t) ^ (-(1 / 2 : ℝ))) x (hqd _)
    have hres := hP.residual (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))
    unfold SimilarityResidual at hres
    rw [map_smul] at hres
    change deriv (fun τ => selfSimilar W T τ x) t
        + advectionAt (fun z : Space => (T - t) ^ (-(1 / 2 : ℝ)) • W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (z - center))) x
        - sumSecondPartialsAt (fun z : Space => (T - t) ^ (-(1 / 2 : ℝ)) • W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (z - center))) x
        + gradientAt (fun z : Space => (T - t)⁻¹ * q (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (z - center))) x
        = 0
    rw [deriv_selfSimilar W hF T t hT ht x, hA, hL, hG, ← scaleFactor_mul_self T t ht]
    linear_combination (norm := module) ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ))) • hres

end Breakdown.Periodic
