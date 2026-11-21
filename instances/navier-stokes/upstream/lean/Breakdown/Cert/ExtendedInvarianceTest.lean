import Breakdown.Cert.ExtendedInvarianceTrace
import Breakdown.Cert.TestPairing

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedInvarianceTest

open Internal.Invariance Internal.ExtendedInvarianceTrace

theorem isSpaceTimeTestField_shift {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) (b : ℝ) :
    IsSpaceTimeTestField (fun σ y => φ (σ + b) y) := by
  obtain ⟨hs, hc, hdiv⟩ := hφ
  refine ⟨hs.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd), ?_,
    fun s y => hdiv (s + b) y⟩
  exact hc.comp_homeomorph ((Homeomorph.addRight b).prodCongr (Homeomorph.refl Space))

theorem coord_symm_eq (R : Space ≃ₗᵢ[ℝ] Space) (w : Space) (i : Fin 3) :
    (R.symm w) i = inner ℝ (R (unitVector i)) w := by
  have e1 : (R.symm w) i = inner ℝ (unitVector i) (R.symm w) := by
    simp [unitVector, EuclideanSpace.inner_single_left]
  rw [e1, ← R.inner_map_map (unitVector i) (R.symm w), LinearIsometryEquiv.apply_symm_apply]

theorem isSpaceTimeTestField_rot {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    (R : Space ≃ₗᵢ[ℝ] Space) : IsSpaceTimeTestField (fun σ y => R.symm (φ σ (R y))) := by
  obtain ⟨hs, hc, hdiv⟩ := hφ
  refine ⟨R.symm.contDiff.comp (hs.comp (contDiff_fst.prodMk (R.contDiff.comp contDiff_snd))), ?_,
    fun s y => ?_⟩
  · have h1 := hc.comp_homeomorph ((Homeomorph.refl ℝ).prodCongr R.toHomeomorph)
    exact h1.comp_left (g := R.symm) (map_zero _)
  · have hd : Differentiable ℝ (φ s) :=
      (hs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have e : (fun y => R.symm (φ s (R y))) = pushForward R.symm (φ s) := by
      funext y
      simp [pushForward]
    show divergenceAt (fun y => R.symm (φ s (R y))) y = 0
    rw [e]
    simp only [divergenceAt]
    simp only [fderiv_pushForward R.symm hd, LinearIsometryEquiv.symm_symm, coord_symm_eq]
    let B : Space →L[ℝ] Space →L[ℝ] ℝ :=
      (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).bilinearComp (ContinuousLinearMap.id ℝ Space)
        (fderiv ℝ (φ s) (R y))
    have hB : ∀ x x', B x x' = inner ℝ x (fderiv ℝ (φ s) (R y) x') := fun x x' => by
      simp [B]
    have h := bilin_trace_rot B R
    simp only [hB] at h
    rw [h]
    have h2 := hdiv s (R y)
    simp only [divergenceAt] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [unitVector, EuclideanSpace.inner_single_left]

theorem circleLpOrZero_comp_add (u : TimeCircle → HBar) (b : ℝ) :
    circleLpOrZero (fun t => u (t + (b : TimeCircle))) =
      (shiftLp b : HH →L[ℝ] HH) (circleLpOrZero u) := by
  have hmp := measurePreserving_add_right (volume : Measure TimeCircle) (b : TimeCircle)
  by_cases hm : MemLp u 2 volume
  · have hm' : MemLp (fun t => u (t + (b : TimeCircle))) 2 volume := hm.comp_measurePreserving hmp
    have e0 : circleLpOrZero u = hm.toLp u := dif_pos hm
    have e1 : circleLpOrZero (fun t => u (t + (b : TimeCircle))) = hm'.toLp _ := dif_pos hm'
    have k0 : ((circleLpOrZero u : HH) : TimeCircle → HBar) =ᵐ[volume] u :=
      (EventuallyEq.of_eq (congrArg (fun w : HH => (w : TimeCircle → HBar)) e0)).trans hm.coeFn_toLp
    have k1 : ((circleLpOrZero (fun t => u (t + (b : TimeCircle))) : HH) : TimeCircle → HBar) =ᵐ[volume]
        fun t => u (t + (b : TimeCircle)) :=
      (EventuallyEq.of_eq (congrArg (fun w : HH => (w : TimeCircle → HBar)) e1)).trans hm'.coeFn_toLp
    refine Lp.ext ?_
    filter_upwards [k1, shift_coe b (circleLpOrZero u), ae_shift b k0] with t h1 h2 h3
    exact h1.trans (h3.symm.trans h2.symm)
  · have hm' : ¬ MemLp (fun t => u (t + (b : TimeCircle))) 2 volume := fun h => hm (by
      have h' := h.comp_measurePreserving
        (measurePreserving_add_right (volume : Measure TimeCircle) ((-b : ℝ) : TimeCircle))
      have e : ((fun t => u (t + (b : TimeCircle))) ∘ fun t => t + ((-b : ℝ) : TimeCircle)) = u := by
        funext t
        simp [add_assoc]
      rwa [e] at h')
    have e0 : circleLpOrZero u = 0 := dif_neg hm
    have e1 : circleLpOrZero (fun t => u (t + (b : TimeCircle))) = 0 := dif_neg hm'
    calc circleLpOrZero (fun t => u (t + (b : TimeCircle))) = (0 : HH) := e1
      _ = (shiftLp b : HH →L[ℝ] HH) 0 := (map_zero _).symm
      _ = (shiftLp b : HH →L[ℝ] HH) (circleLpOrZero u) := congrArg _ e0.symm

theorem physToHH_comp_add {F : ℝ → Space → Space} (hF : IsTimePeriodic F) (b : ℝ) :
    physToHH (fun σ => F (σ + b)) = (shiftLp b : HH →L[ℝ] HH) (physToHH F) := by
  unfold physToHH
  rw [← circleLpOrZero_comp_add]
  congr 1
  funext t
  simp only [onCircle]
  rw [periodic_shift hF t b]

theorem periodize_comp_add (φ : ℝ → Space → Space) (b : ℝ) :
    periodize (fun σ y => φ (σ + b) y) = fun σ => periodize φ (σ + b) := by
  funext σ y
  simp only [periodize]
  refine tsum_congr fun n => ?_
  rw [add_right_comm]

theorem shiftLp_testInHH (φ : ℝ → Space → Space) (b : ℝ) :
    (shiftLp b : HH →L[ℝ] HH) (testInHH φ) = testInHH (fun σ y => φ (σ + b) y) := by
  exact (physToHH_comp_add Internal.TestPairing.periodize_periodic b).symm.trans
    (congrArg physToHH (periodize_comp_add φ b).symm)

theorem shiftLp_shiftLp_neg (a : ℝ) (g : HH) :
    (shiftLp a : HH →L[ℝ] HH) ((shiftLp (-a) : HH →L[ℝ] HH) g) = g := by
  refine Lp.ext ?_
  filter_upwards [shift_coe a ((shiftLp (-a) : HH →L[ℝ] HH) g), ae_shift a (shift_coe (-a) g)]
    with t h1 h2
  rw [h1, h2]
  simp [add_assoc]

theorem inner_shiftLp (a : ℝ) (f g : HH) :
    inner ℝ ((shiftLp a : HH →L[ℝ] HH) f) g = inner ℝ f ((shiftLp (-a) : HH →L[ℝ] HH) g) := by
  conv_lhs => rw [← shiftLp_shiftLp_neg a g]
  exact (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (a : TimeCircle))
    (measurePreserving_add_right volume (a : TimeCircle))).inner_map_map f _

theorem inner_rotX (R : Space ≃ₗᵢ[ℝ] Space) (v w : HBar) :
    inner ℝ (rotX R v) w = inner ℝ v (rotX R.symm w) :=
  calc inner ℝ (rotX R v) w = inner ℝ (rotX R v) (rotX R (rotX R.symm w)) := by rw [rotX_rotX_symm]
    _ = inner ℝ v (rotX R.symm w) := (rotX R).inner_map_map _ _

theorem inner_rotHH (R : Space ≃ₗᵢ[ℝ] Space) (f g : HH) :
    inner ℝ (rotHH R f) g = inner ℝ f (rotHH R.symm g) := by
  refine (L2.inner_def (rotHH R f) g).trans ((integral_congr_ae ?_).trans
    (L2.inner_def f (rotHH R.symm g)).symm)
  filter_upwards [rot_coe R f, rot_coe R.symm g] with t h1 h2
  exact (congrArg (fun v => inner ℝ v ((g : TimeCircle → HBar) t)) h1).trans
    ((inner_rotX R _ _).trans (congrArg (fun v => inner ℝ ((f : TimeCircle → HBar) t) v) h2.symm))

theorem circleLpOrZero_comp_rot (R : Space ≃ₗᵢ[ℝ] Space) (u : TimeCircle → HBar) :
    circleLpOrZero (fun t => rotX R (u t)) = rotHH R (circleLpOrZero u) := by
  by_cases hm : MemLp u 2 volume
  · have hm' : MemLp (fun t => rotX R (u t)) 2 volume :=
      ((rotX R).toContinuousLinearEquiv : Freq.X →L[ℝ] Freq.X).comp_memLp' hm
    have e0 : circleLpOrZero u = hm.toLp u := dif_pos hm
    have e1 : circleLpOrZero (fun t => rotX R (u t)) = hm'.toLp _ := dif_pos hm'
    have k0 : ((circleLpOrZero u : HH) : TimeCircle → HBar) =ᵐ[volume] u :=
      (EventuallyEq.of_eq (congrArg (fun w : HH => (w : TimeCircle → HBar)) e0)).trans hm.coeFn_toLp
    have k1 : ((circleLpOrZero (fun t => rotX R (u t)) : HH) : TimeCircle → HBar) =ᵐ[volume]
        fun t => rotX R (u t) :=
      (EventuallyEq.of_eq (congrArg (fun w : HH => (w : TimeCircle → HBar)) e1)).trans hm'.coeFn_toLp
    refine Lp.ext ?_
    filter_upwards [k1, rot_coe R (circleLpOrZero u), k0] with t h1 h2 h3
    exact h1.trans ((congrArg (rotX R) h3.symm).trans h2.symm)
  · have hm' : ¬ MemLp (fun t => rotX R (u t)) 2 volume := fun h => hm (by
      have h' := ((rotX R.symm).toContinuousLinearEquiv : Freq.X →L[ℝ] Freq.X).comp_memLp' h
      have e : (((rotX R.symm).toContinuousLinearEquiv : Freq.X →L[ℝ] Freq.X) ∘
          fun t => rotX R (u t)) = u := by
        funext t
        have := rotX_rotX_symm R.symm (u t)
        simpa using this
      rwa [e] at h')
    have e0 : circleLpOrZero u = 0 := dif_neg hm
    have e1 : circleLpOrZero (fun t => rotX R (u t)) = 0 := dif_neg hm'
    calc circleLpOrZero (fun t => rotX R (u t)) = (0 : HH) := e1
      _ = rotHH R 0 := (map_zero _).symm
      _ = rotHH R (circleLpOrZero u) := congrArg _ e0.symm

theorem physToHH_comp_pushForward (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    (R : Space ≃ₗᵢ[ℝ] Space) (F : ℝ → Space → Space) :
    physToHH (fun σ => pushForward R (F σ)) = rotHH R (physToHH F) := by
  unfold physToHH
  rw [← circleLpOrZero_comp_rot]
  congr 1
  funext t
  simp only [onCircle]
  exact solField_pushForward hP R _

theorem periodize_rot (R : Space ≃ₗᵢ[ℝ] Space) (φ : ℝ → Space → Space) :
    periodize (fun σ y => R.symm (φ σ (R y))) = fun σ => pushForward R.symm (periodize φ σ) := by
  funext σ y
  simp only [periodize, pushForward, LinearIsometryEquiv.symm_symm]
  exact (R.symm.toContinuousLinearEquiv.map_tsum (f := fun n : ℤ => φ (σ + n) (R y))).symm

theorem rotHH_testInHH (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    (R : Space ≃ₗᵢ[ℝ] Space) (φ : ℝ → Space → Space) :
    rotHH R.symm (testInHH φ) = testInHH (fun σ y => R.symm (φ σ (R y))) := by
  exact (physToHH_comp_pushForward hP R.symm (periodize φ)).symm.trans
    (congrArg physToHH (periodize_rot R φ).symm)

end Internal.ExtendedInvarianceTest

end Breakdown.Cert
