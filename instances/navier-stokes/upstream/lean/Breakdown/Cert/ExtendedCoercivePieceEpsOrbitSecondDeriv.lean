import Breakdown.Cert.ExtendedCoercivePieceEpsModeIdentity
import Breakdown.Cert.ExtendedCoercivePieceEpsExpansion
import Breakdown.Cert.CoerciveSmoothEpsPointwiseSecondDeriv
import Breakdown.Cert.ExtendedCoercivePairingSplitAeDiff

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.OrbitSecondDeriv

open Filter Coercive Coercive.Internal.SmoothPieceEpsCore Coercive.Internal.MuSmooth Coercive.Internal.ModeRotation
  Coercive.Internal.SmoothEpsPointwise

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}

def secondDerivIntegrand (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3)
    (y : Space) (p : ℝ × ℝ) : Space →L[ℝ] ℂ :=
  expFactor κ p.1 p.2 • (Complex.ofRealCLM.comp ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp
    ((StretchInternal.rotCLM (-p.2)).comp ((ContinuousLinearMap.apply ℝ Space (axialRot p.2 (unitVector a))).comp
      ((HW (σ + p.1) (axialRot p.2 y)).comp (StretchInternal.rotCLM p.2))))))

theorem secondDerivIntegrand_apply (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (y : Space) (p : ℝ × ℝ) (u : Space) :
    secondDerivIntegrand HW κ σ b a y p u = expFactor κ p.1 p.2
      * ((axialRot (-p.2) (HW (σ + p.1) (axialRot p.2 y) (axialRot p.2 u) (axialRot p.2 (unitVector a))) b
        : ℝ) : ℂ) := rfl

theorem hasFDerivAt_gradModeIntegrand_weak (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (y : Space) (p : ℝ × ℝ)
    (hp : HasFDerivAt (fderiv ℝ (W (σ + p.1))) (HW (σ + p.1) (axialRot p.2 y)) (axialRot p.2 y)) :
    HasFDerivAt (fun x => gradModeIntegrand W κ σ b a x p) (secondDerivIntegrand HW κ σ b a y p) y := by
  have h1 : HasFDerivAt (fun x => axialRot p.2 x) (StretchInternal.rotCLM p.2) y :=
    (StretchInternal.rotCLM p.2).hasFDerivAt
  have h3 := hp.comp y h1
  have h4 := (ContinuousLinearMap.apply ℝ Space (axialRot p.2 (unitVector a))).hasFDerivAt.comp y h3
  have h5 := (StretchInternal.rotCLM (-p.2)).hasFDerivAt.comp y h4
  have h6 := (EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp y h5
  have h7 := Complex.ofRealCLM.hasFDerivAt.comp y h6
  exact h7.const_mul (expFactor κ p.1 p.2)

theorem increment_gradModeIntegrand (hW : IsWeakSecondDerivState W HW D) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3)
    (p : ℝ × ℝ) : LipschitzWith (Real.nnabs D) (fun x => gradModeIntegrand W κ σ b a x p) := by
  have hRot := axialRotationHolds_proof
  have hD := WeakAeDiff.decay_nonneg hW
  have hL := WeakAeDiff.fderiv_increment hW (σ + p.1)
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_nnabs, abs_of_nonneg hD]
  simp only [gradModeIntegrand]
  rw [← mul_sub, norm_mul, norm_expFactor, one_mul, ← Complex.ofReal_sub, Complex.norm_real]
  set F := fderiv ℝ (W (σ + p.1))
  set w := axialRot p.2 (unitVector a)
  have e := (StretchInternal.rotCLM (-p.2)).map_sub (F (axialRot p.2 x) w) (F (axialRot p.2 x') w)
  simp only [StretchInternal.rotCLM_apply] at e
  have e2 : axialRot p.2 x - axialRot p.2 x' = axialRot p.2 (x - x') := by
    have := (StretchInternal.rotCLM p.2).map_sub x x'
    simp only [StretchInternal.rotCLM_apply] at this
    exact this.symm
  have hLd := hL.dist_le_mul (axialRot p.2 x) (axialRot p.2 x')
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hD, e2, norm_axialRot hRot] at hLd
  calc ‖axialRot (-p.2) (F (axialRot p.2 x) w) b - axialRot (-p.2) (F (axialRot p.2 x') w) b‖
      = ‖axialRot (-p.2) (F (axialRot p.2 x) w - F (axialRot p.2 x') w) b‖ := by
        rw [e, PiLp.sub_apply]
    _ ≤ ‖axialRot (-p.2) (F (axialRot p.2 x) w - F (axialRot p.2 x') w)‖ := by
        simpa using PiLp.norm_apply_le (axialRot (-p.2) (F (axialRot p.2 x) w - F (axialRot p.2 x') w)) b
    _ = ‖(F (axialRot p.2 x) - F (axialRot p.2 x')) w‖ := by
        rw [norm_axialRot hRot, sub_apply]
    _ ≤ ‖F (axialRot p.2 x) - F (axialRot p.2 x')‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖F (axialRot p.2 x) - F (axialRot p.2 x')‖ := by
        rw [norm_axialRot hRot, ModeDerivative.Internal.norm_unitVector_one, mul_one]
    _ ≤ D * ‖x - x'‖ := hLd

theorem continuous_gradModeIntegrand_once (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (κ : ℤ × ℤ)
    (σ : ℝ) (b a : Fin 3) (x : Space) : Continuous (fun p => gradModeIntegrand W κ σ b a x p) := by
  have h0 : Continuous fun p : ℝ × ℝ => fderiv ℝ (W (σ + p.1)) (axialRot p.2 x) :=
    (OnceExpansion.continuous_slice_fderiv_of_once hW).comp ((continuous_const.add continuous_fst).prodMk
      (ModeDerivative.Internal.continuous_axialRot_comp continuous_snd continuous_const))
  have h1 := h0.clm_apply (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ : ℝ × ℝ => unitVector a)
    continuous_snd continuous_const)
  have h2 := ModeDerivative.Internal.continuous_axialRot_comp continuous_snd.neg h1
  exact (continuous_expFactor κ).mul (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ b).comp h2))

theorem modeGrad_eq_box_once (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (x : Space) :
    modeGrad κ (gradField W) σ x (b, a)
      = (1 / (2 * Real.pi) : ℂ) * ∫ p, gradModeIntegrand W κ σ b a x p ∂boxMeasure := by
  unfold modeGrad
  rw [modeAverage_eq]
  congr 1
  exact iter_eq_prod (fun τ φ => expFactor κ τ φ * ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ x)
    (axialRot φ (unitVector a))) b : ℝ) : ℂ))
    (StretchInternal.integrable_box_of_continuous (continuous_gradModeIntegrand_once hW κ σ b a x))

theorem aestronglyMeasurable_secondDerivIntegrand (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3) (y : Space)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => HW (σ + p.1) (axialRot p.2 y)) boxMeasure) :
    AEStronglyMeasurable (fun p => secondDerivIntegrand HW κ σ b a y p) boxMeasure := by
  set G : ℝ × ℝ → (Space →L[ℝ] Space →L[ℝ] Space) → (Space →L[ℝ] ℂ) := fun p A =>
    expFactor κ p.1 p.2 • (Complex.ofRealCLM.comp ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp
      ((StretchInternal.rotCLM (-p.2)).comp ((ContinuousLinearMap.apply ℝ Space (axialRot p.2 (unitVector a))).comp
        (A.comp (StretchInternal.rotCLM p.2)))))) with hG
  have hc : Continuous (Function.uncurry G) := by
    refine continuous_clm_apply.2 fun u => ?_
    have hA : Continuous fun q : (ℝ × ℝ) × (Space →L[ℝ] Space →L[ℝ] Space) =>
        q.2 (axialRot q.1.2 u) (axialRot q.1.2 (unitVector a)) :=
      (continuous_snd.clm_apply (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ => u)
        continuous_fst.snd continuous_const)).clm_apply
        (ModeDerivative.Internal.continuous_axialRot_comp (w := fun _ => unitVector a) continuous_fst.snd
          continuous_const)
    have h2 := ModeDerivative.Internal.continuous_axialRot_comp continuous_fst.snd.neg hA
    have h3 := ((continuous_expFactor κ).comp continuous_fst).mul
      (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ b).comp h2))
    exact h3
  exact hc.comp_aestronglyMeasurable₂ aestronglyMeasurable_id hmeas

theorem modeGrad_hasFDerivAt_weak (hW : IsWeakSecondDerivState W HW D) (κ : ℤ × ℤ) (σ : ℝ) (b a : Fin 3)
    (y : Space) (hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => HW (σ + p.1) (axialRot p.2 y)) boxMeasure)
    (hgood : ∀ᵐ p ∂boxMeasure,
      HasFDerivAt (fderiv ℝ (W (σ + p.1))) (HW (σ + p.1) (axialRot p.2 y)) (axialRot p.2 y)) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun x => modeGrad κ (gradField W) σ x (b, a)) L y ∧
      ∀ j, L (unitVector j) = modeSecondDeriv κ HW σ y (b, j, a) := by
  have hI := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := boxMeasure) (x₀ := y)
    (F := fun x p => gradModeIntegrand W κ σ b a x p) (F' := fun p => secondDerivIntegrand HW κ σ b a y p)
    (bound := fun _ => D) Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      (continuous_gradModeIntegrand_once hW.smooth κ σ b a x).aestronglyMeasurable)
    (StretchInternal.integrable_box_of_continuous (continuous_gradModeIntegrand_once hW.smooth κ σ b a y))
    (aestronglyMeasurable_secondDerivIntegrand κ σ b a y hmeas)
    (Filter.Eventually.of_forall fun p => (increment_gradModeIntegrand hW κ σ b a p).lipschitzOnWith)
    (StretchInternal.integrable_box_of_continuous continuous_const)
    (hgood.mono fun p hp => hasFDerivAt_gradModeIntegrand_weak κ σ b a y p hp)
  refine ⟨(1 / (2 * Real.pi) : ℂ) • ∫ p, secondDerivIntegrand HW κ σ b a y p ∂boxMeasure, ?_, ?_⟩
  · have hfun : (fun x => modeGrad κ (gradField W) σ x (b, a)) =
        fun x => (1 / (2 * Real.pi) : ℂ) * ∫ p, gradModeIntegrand W κ σ b a x p ∂boxMeasure := by
      funext x
      exact modeGrad_eq_box_once hW.smooth κ σ b a x
    rw [hfun]
    exact hI.2.const_mul _
  · intro j
    have hint := hI.1
    rw [smul_apply, ContinuousLinearMap.integral_apply hint, smul_eq_mul]
    unfold modeSecondDeriv
    rw [modeAverage_eq]
    congr 1
    rw [iter_eq_prod (fun τ φ => expFactor κ τ φ * ((axialRot (-φ) (HW (σ + τ) (axialRot φ y)
      (axialRot φ (unitVector j)) (axialRot φ (unitVector a))) b : ℝ) : ℂ))]
    · rfl
    · exact (hint.apply_continuousLinearMap (unitVector j)).congr (Filter.Eventually.of_forall fun p => rfl)

theorem fderiv_bound (hW : IsWeakSecondDerivState W HW D) : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ D := fun s y =>
  ((hW.decay s y).2.1).trans (div_le_self (WeakAeDiff.decay_nonneg hW)
    (one_le_pow₀ (by linarith [norm_nonneg y])))

theorem secondDeriv_expansion_weak (hW : IsWeakSecondDerivState W HW D) (s : Finset (ℤ × ℤ))
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => HW (σ + p.1) (axialRot p.2 y)) boxMeasure)
    (hgood : ∀ᵐ p ∂boxMeasure,
      HasFDerivAt (fderiv ℝ (W (σ + p.1))) (HW (σ + p.1) (axialRot p.2 y)) (axialRot p.2 y))
    (hpt : HasFDerivAt (fderiv ℝ (W (σ + τ))) (HW (σ + τ) (axialRot φ y)) (axialRot φ y)) (b j a : Fin 3) :
    axialRot (-φ) (HW (σ + τ) (axialRot φ y) (axialRot φ (unitVector j)) (axialRot φ (unitVector a))) b
      = (modeSecondDeriv (0, 0) HW σ y (b, j, a)).re
        + ∑ α ∈ s, (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeSecondDeriv α HW σ y (b, j, a)).re := by
  set c : ℤ × ℤ → ℂ := fun α => Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
  have hf : HasFDerivAt (fun x => axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ x) (axialRot φ (unitVector a))) b)
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp ((StretchInternal.rotCLM (-φ)).comp
        ((ContinuousLinearMap.apply ℝ Space (axialRot φ (unitVector a))).comp
          ((HW (σ + τ) (axialRot φ y)).comp (StretchInternal.rotCLM φ))))) y := by
    have h1 : HasFDerivAt (fun x => axialRot φ x) (StretchInternal.rotCLM φ) y :=
      (StretchInternal.rotCLM φ).hasFDerivAt
    have h3 := hpt.comp y h1
    have h4 := (ContinuousLinearMap.apply ℝ Space (axialRot φ (unitVector a))).hasFDerivAt.comp y h3
    have h5 := (StretchInternal.rotCLM (-φ)).hasFDerivAt.comp y h4
    exact (EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp y h5
  choose L hL hLe using fun α => modeGrad_hasFDerivAt_weak hW α σ b a y hmeas hgood
  have hg : HasFDerivAt (fun x => (modeGrad (0, 0) (gradField W) σ x (b, a)).re
        + ∑ α ∈ s, (c α * modeGrad α (gradField W) σ x (b, a)).re)
      (Complex.reCLM.comp (L (0, 0)) + ∑ α ∈ s, Complex.reCLM.comp (c α • L α)) y := by
    refine (Complex.reCLM.hasFDerivAt.comp y (hL (0, 0))).add ?_
    refine HasFDerivAt.fun_sum fun α _ => ?_
    exact Complex.reCLM.hasFDerivAt.comp y ((hL α).const_mul (c α))
  have heq : (fun x => axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ x) (axialRot φ (unitVector a))) b)
      = fun x => (modeGrad (0, 0) (gradField W) σ x (b, a)).re
        + ∑ α ∈ s, (c α * modeGrad α (gradField W) σ x (b, a)).re :=
    funext fun x => OnceExpansion.grad_expansion_once hW.smooth (fderiv_bound hW) hW.periodic s hh σ τ φ x b a
  rw [heq] at hf
  have hu := congrArg (fun T : Space →L[ℝ] ℝ => T (unitVector j)) (hf.unique hg)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.smul_apply, Complex.reCLM_apply, smul_eq_mul, hLe] at hu
  rw [← hu]
  rfl

theorem modeSecondDeriv_zero_real (σ : ℝ) (y : Space) (ijl : Fin 3 × Fin 3 × Fin 3) :
    (((modeSecondDeriv (0, 0) HW σ y ijl).re : ℝ) : ℂ) = modeSecondDeriv (0, 0) HW σ y ijl := by
  have h0 := modeSecondDeriv_neg (0, 0) HW σ y ijl
  simp only [Prod.neg_mk, neg_zero] at h0
  exact Complex.conj_eq_iff_re.mp h0.symm

theorem secondDerivC_expansion_weak (hW : IsWeakSecondDerivState W HW D) (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => HW (σ + p.1) (axialRot p.2 y)) boxMeasure)
    (hgood : ∀ᵐ p ∂boxMeasure,
      HasFDerivAt (fderiv ℝ (W (σ + p.1))) (HW (σ + p.1) (axialRot p.2 y)) (axialRot p.2 y))
    (hpt : HasFDerivAt (fderiv ℝ (W (σ + τ))) (HW (σ + τ) (axialRot φ y)) (axialRot φ y)) (b j a : Fin 3) :
    ((axialRot (-φ) (HW (σ + τ) (axialRot φ y) (axialRot φ (unitVector j)) (axialRot φ (unitVector a))) b
        : ℝ) : ℂ)
      = modeSecondDeriv (0, 0) HW σ y (b, j, a)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeSecondDeriv α HW σ y (b, j, a) := by
  rw [secondDeriv_expansion_weak hW s hh σ τ φ y hmeas hgood hpt b j a, Complex.ofReal_add]
  congr 1
  · exact modeSecondDeriv_zero_real σ y (b, j, a)
  · exact re_sum_sym s hs _ fun α => by rw [phase_neg, modeSecondDeriv_neg, map_mul]

theorem vortGrad_expansion_at (hW : IsWeakSecondDerivState W HW D) (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => HW (σ + p.1) (axialRot p.2 y)) boxMeasure)
    (hgood : ∀ᵐ p ∂boxMeasure,
      HasFDerivAt (fderiv ℝ (W (σ + p.1))) (HW (σ + p.1) (axialRot p.2 y)) (axialRot p.2 y))
    (hpt : HasFDerivAt (fderiv ℝ (W (σ + τ))) (HW (σ + τ) (axialRot φ y)) (axialRot φ y)) (i j : Fin 3) :
    ((axialRot (-φ) (vortGradMap (HW (σ + τ) (axialRot φ y)) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
      = curlGradOfSecondDeriv (modeSecondDeriv (0, 0) HW σ y) (i, j)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * curlGradOfSecondDeriv (modeSecondDeriv α HW σ y) (i, j) := by
  rw [VortGradMap.vortGradMap_apply, ← Coercive.Internal.CurlEnergy.curlVec_axialRot φ _ i]
  push_cast
  simp_rw [secondDerivC_expansion_weak hW s hs hh σ τ φ y hmeas hgood hpt]
  unfold curlGradOfSecondDeriv
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ => ?_
  push_cast
  ring

theorem orbit_expansion_ae (hW : IsWeakSecondDerivState W HW D) (H : Finset (ℤ × ℤ))
    (hspan : ∀ σ y i, W σ y i = ∑ β ∈ H, (modeVel β W σ y i).re) (hzero : (0, 0) ∈ H)
    (hneg : ∀ β ∈ H, -β ∈ H) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Space)), ∀ᵐ q ∂boxMeasure, ∀ i j : Fin 3,
      ((axialRot (-q.2) (vortGradMap (HW (z.1 + q.1) (axialRot q.2 z.2)) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
        = curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
          + ∑ α ∈ H.erase 0, Complex.exp (((2 * Real.pi * α.1 * q.1 + α.2 * q.2 : ℝ) : ℂ) * Complex.I)
            * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j) := by
  have hs : ∀ α ∈ H.erase (0, 0), -α ∈ H.erase (0, 0) := by
    intro α hα
    rw [Finset.mem_erase] at hα ⊢
    exact ⟨fun h0 => hα.1 (by simpa using congrArg Neg.neg h0), hneg α hα.2⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ H.erase (0, 0), (modeVel α W σ y i).re := by
    intro σ y i
    rw [hspan σ y i, Finset.add_sum_erase H (fun β => (modeVel β W σ y i).re) hzero]
  have hq := hW.secondDeriv_measurable.comp_quasiMeasurePreserving
    (Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot WeakModeIdentity.orbitBox)
  filter_upwards [hq.prodMk_left, WeakModeIdentity.ae_orbit_of_ae (WeakModeIdentity.ae_good_point hW)]
    with z hz hg
  filter_upwards [hg] with q hq' i j
  exact vortGrad_expansion_at hW (H.erase (0, 0)) hs hh z.1 q.1 q.2 z.2 hz (hg.mono fun p hp => hp.1) hq'.1 i j

end Internal.OrbitSecondDeriv

end CoerciveWeak

end Breakdown
