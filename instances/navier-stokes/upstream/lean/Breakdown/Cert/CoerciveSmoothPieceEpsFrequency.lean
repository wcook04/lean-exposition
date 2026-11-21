import Breakdown.Cert.CoerciveSmoothPieceEpsSeries
import Breakdown.Cert.CoerciveFrequencySeminormAngular

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsFrequency

theorem gradField_eq_of_smooth {U : ℝ × Space → Space} (hU : ContDiff ℝ 1 U) (t : ℝ) (x : Space) :
    gradField (fun s y => U (s, y)) t x = (fderiv ℝ U (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : Differentiable ℝ U := hU.differentiable (by simp)
  exact ((hd (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem continuous_gradField_of_smooth {U : ℝ × Space → Space} (hU : ContDiff ℝ 1 U) :
    Continuous (fun z : ℝ × Space => gradField (fun s y => U (s, y)) z.1 z.2) := by
  have e : (fun z : ℝ × Space => gradField (fun s y => U (s, y)) z.1 z.2) =
      fun z => (fderiv ℝ U z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact gradField_eq_of_smooth hU z.1 z.2
  rw [e]
  exact (hU.continuous_fderiv (by simp)).clm_comp continuous_const

theorem deriv_time_eq {U : ℝ × Space → Space} (hU : ContDiff ℝ 1 U) (t : ℝ) (x : Space) :
    deriv (fun s => U (s, x)) t = fderiv ℝ U (t, x) ((1 : ℝ), (0 : Space)) := by
  have hd : Differentiable ℝ U := hU.differentiable (by simp)
  have hc : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Space)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((hd (t, x)).hasFDerivAt.comp_hasDerivAt t hc).deriv

theorem timeDeriv_smooth {v : ℝ → Space → Space} (hv : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) := by
  have e : (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) =
      fun z => fderiv ℝ (fun w : ℝ × Space => v w.1 w.2) z ((1 : ℝ), (0 : Space)) := by
    funext z
    exact deriv_time_eq (U := fun w : ℝ × Space => v w.1 w.2) (hv.of_le (by simp)) z.1 z.2
  rw [e]
  exact (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_gradField_time {v : ℝ → Space → Space}
    (hv : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) (s : ℝ) (x u : Space) :
    HasDerivAt (fun t => gradField v t x u)
      (gradField (fun t y => deriv (fun r => v r y) t) s x u) s := by
  set V : ℝ × Space → Space := fun z => v z.1 z.2 with hVdef
  have hV1 : ContDiff ℝ 1 V := hv.of_le (by simp)
  have hD : ContDiff ℝ ∞ (fderiv ℝ V) := hv.fderiv_right (m := ∞) (by simp)
  have hDd : Differentiable ℝ (fderiv ℝ V) := hD.differentiable (by simp)
  have hsymm := (hv.contDiffAt (x := (s, x))).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have e1 : ∀ t, gradField v t x u = fderiv ℝ V (t, x) ((0 : ℝ), u) := by
    intro t
    have := gradField_eq_of_smooth hV1 t x
    have h2 : gradField v t x = gradField (fun s y => V (s, y)) t x := rfl
    rw [h2, this]
    rfl
  set U : ℝ × Space → Space := fun z => deriv (fun r => v r z.2) z.1 with hUdef
  have hU : ContDiff ℝ ∞ U := timeDeriv_smooth hv
  have hUe : ∀ z, U z = fderiv ℝ V z ((1 : ℝ), (0 : Space)) := fun z => deriv_time_eq hV1 z.1 z.2
  have e2 : gradField (fun t y => deriv (fun r => v r y) t) s x u = fderiv ℝ U (s, x) ((0 : ℝ), u) := by
    have := gradField_eq_of_smooth (hU.of_le (by simp)) s x
    have h2 : gradField (fun t y => deriv (fun r => v r y) t) s x = gradField (fun s y => U (s, y)) s x := rfl
    rw [h2, this]
    rfl
  have hUf : HasFDerivAt U ((ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space))).comp
      (fderiv ℝ (fderiv ℝ V) (s, x))) (s, x) := by
    have h := (ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space))).hasFDerivAt.comp (s, x)
      (hDd (s, x)).hasFDerivAt
    have hfun : U = (ContinuousLinearMap.apply ℝ Space ((1 : ℝ), (0 : Space))) ∘ fderiv ℝ V := by
      funext z; exact hUe z
    rw [hfun]
    exact h
  rw [e2, hUf.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [← hsymm]
  have hc : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : Space)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h3 := (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), u)).hasFDerivAt.comp_hasDerivAt s
    ((hDd (s, x)).hasFDerivAt.comp_hasDerivAt s hc)
  simp only [ContinuousLinearMap.apply_apply] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
  exact e1 t


theorem hasDerivAt_phase (n : ℝ) (c : ℝ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(((2 * Real.pi * n * t + c : ℝ) : ℂ) * Complex.I)))
      (Complex.exp (-(((2 * Real.pi * n * τ + c : ℝ) : ℂ) * Complex.I)) * (-(((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)))
      τ := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * Real.pi * n * t + c : ℝ) : ℂ)) ((2 * Real.pi * n : ℝ) : ℂ) τ := by
    have := (((hasDerivAt_id τ).const_mul (2 * Real.pi * n)).add_const c).ofReal_comp
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => -(((2 * Real.pi * n * t + c : ℝ) : ℂ) * Complex.I))
      (-(((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)) τ := (h1.mul_const Complex.I).neg
  exact h3.cexp

theorem phase_one (n : ℤ) (c : ℝ) :
    Complex.exp (-(((2 * Real.pi * n * 1 + c : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * n * 0 + c : ℝ) : ℂ) * Complex.I)) := by
  have : (-(((2 * Real.pi * n * 1 + c : ℝ) : ℂ) * Complex.I)) =
      (-(((2 * Real.pi * n * 0 + c : ℝ) : ℂ) * Complex.I)) + ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem modeAverage_time_deriv {β : Type*} (ι : ℤ × ℤ) (F F' : ℝ → ℝ → β → ℝ) (b : β)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2 b)) (hF' : Continuous (fun p : ℝ × ℝ => F' p.1 p.2 b))
    (hd : ∀ τ φ, HasDerivAt (fun t => F t φ b) (F' τ φ b) τ) (hp : ∀ φ, F 1 φ b = F 0 φ b) :
    modeAverage ι F' b = (((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I) * modeAverage ι F b := by
  set E : ℝ → ℝ → ℂ := fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
    with hE
  have hEc : Continuous (fun p : ℝ × ℝ => E p.1 p.2) := by
    simp only [hE]
    fun_prop
  have hint : ∀ K : ℝ → ℝ → β → ℝ, Continuous (fun p : ℝ × ℝ => K p.1 p.2 b) →
      IntegrableOn (Function.uncurry (fun τ φ => E τ φ * ((K τ φ b : ℝ) : ℂ)))
        (Set.uIoc 0 1 ×ˢ Set.uIoc 0 (2 * Real.pi)) := by
    intro K hK
    have hc : Continuous (Function.uncurry (fun τ φ => E τ φ * ((K τ φ b : ℝ) : ℂ))) :=
      hEc.mul (Complex.continuous_ofReal.comp hK)
    exact (hc.continuousOn.integrableOn_compact ((isCompact_uIcc (a := (0 : ℝ)) (b := 1)).prod
      (isCompact_uIcc (a := (0 : ℝ)) (b := 2 * Real.pi)))).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  unfold modeAverage
  rw [intervalIntegral_intervalIntegral_swap (hint F' hF'), intervalIntegral_intervalIntegral_swap (hint F hF)]
  have key : ∀ φ, (∫ τ in (0 : ℝ)..1, E τ φ * ((F' τ φ b : ℝ) : ℂ)) =
      (((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I) * ∫ τ in (0 : ℝ)..1, E τ φ * ((F τ φ b : ℝ) : ℂ) := by
    intro φ
    have hu : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => E t φ)
        (E τ φ * (-(((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I))) τ := fun τ _ =>
      hasDerivAt_phase (ι.1 : ℝ) (ι.2 * φ) τ
    have hv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => ((F t φ b : ℝ) : ℂ)) ((F' τ φ b : ℝ) : ℂ) τ :=
      fun τ _ => (hd τ φ).ofReal_comp
    have cu : Continuous (fun τ => E τ φ * (-(((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I))) :=
      (hEc.comp (Continuous.prodMk_left φ)).mul continuous_const
    have cv : Continuous (fun τ => ((F' τ φ b : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hF'.comp (Continuous.prodMk_left φ))
    have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv (cu.intervalIntegrable _ _)
      (cv.intervalIntegrable _ _)
    rw [ibp]
    have e1 : E 1 φ = E 0 φ := by simp only [hE]; exact phase_one ι.1 (ι.2 * φ)
    rw [e1, hp φ, sub_self, zero_sub, ← intervalIntegral.integral_neg]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    ring
  simp_rw [key, intervalIntegral.integral_const_mul]
  ring

theorem continuous_cnormSq' {β : Type*} [Fintype β] : Continuous (cnormSq : (β → ℂ) → ℝ) := by
  unfold cnormSq
  fun_prop

theorem cnormSq_const_mul {β : Type*} [Fintype β] (c : ℂ) (x : β → ℂ) :
    cnormSq (fun b => c * x b) = ‖c‖ ^ 2 * cnormSq x := by
  unfold cnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [norm_mul, mul_pow]

theorem iter_tsum_eq {f : ℤ × ℤ → ℝ → Space → ℝ}
    (hfm : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f ι z.1 z.2)) volume) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (f ι σ y)) =
      ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f ι σ y) := by
  rw [← Internal.SmoothPieceEps.slab_tsum_eq hfm]
  exact (lintegral_prod _ (Internal.SmoothPieceEps.slab_aem (AEMeasurable.tsum hfm))).symm

theorem matSq_le_three (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    intro i
    have := G.le_opNorm (unitVector i)
    rw [Internal.SmoothPieceEps.norm_unit, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  simp only [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem hasDerivAt_rot_coord {f : ℝ → Space} {f' : Space} {τ : ℝ} (φ : ℝ) (i : Fin 3)
    (hf : HasDerivAt f f' τ) : HasDerivAt (fun t => axialRot φ (f t) i) (axialRot φ f' i) τ := by
  have h := ((EuclideanSpace.proj i).comp
    (LinearMap.toContinuousLinearMap (RotationInternal.axialRotLinear φ))).hasFDerivAt.comp_hasDerivAt τ hf
  exact h

theorem continuous_rot_family {K : ℝ → Space → (Space →L[ℝ] Space)} (hK : Continuous (fun z : ℝ × Space => K z.1 z.2))
    (σ : ℝ) (y : Space) (ij : Fin 3 × Fin 3) :
    Continuous (fun p : ℝ × ℝ =>
      axialRot (-p.2) (K (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector ij.2))) ij.1) := by
  have h1 : Continuous (fun p : ℝ × ℝ => K (σ + p.1) (axialRot p.2 y)) :=
    hK.comp ((continuous_const.add continuous_fst).prodMk
      (GainInternal.continuous_axialRot_comp continuous_snd continuous_const))
  have h2 := h1.clm_apply (GainInternal.continuous_axialRot_comp continuous_snd
    (continuous_const : Continuous fun _ : ℝ × ℝ => unitVector ij.2))
  exact GainInternal.continuous_coord (GainInternal.continuous_axialRot_comp continuous_snd.neg h2) ij.1

theorem modeGrad_time {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) (ij : Fin 3 × Fin 3) :
    modeGrad ι (gradField (fun t x => deriv (fun r => v r x) t)) σ y ij =
      (((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I) * modeGrad ι (gradField v) σ y ij := by
  have hV1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  have hU1 : ContDiff ℝ 1 (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) :=
    (timeDeriv_smooth hv.smooth).of_le (by simp)
  have cG : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) := continuous_gradField_of_smooth hV1
  have cGt : Continuous (fun z : ℝ × Space => gradField (fun t x => deriv (fun r => v r x) t) z.1 z.2) :=
    continuous_gradField_of_smooth hU1
  have hF := continuous_rot_family cG σ y ij
  have hF' := continuous_rot_family cGt σ y ij
  have hd : ∀ τ φ : ℝ, HasDerivAt
      (fun t => axialRot (-φ) (gradField v (σ + t) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1)
      (axialRot (-φ) (gradField (fun t x => deriv (fun r => v r x) t) (σ + τ) (axialRot φ y)
        (axialRot φ (unitVector ij.2))) ij.1) τ := by
    intro τ φ
    have h0 := hasDerivAt_gradField_time hv.smooth (σ + τ) (axialRot φ y) (axialRot φ (unitVector ij.2))
    have h1 := h0.scomp τ ((hasDerivAt_id' τ).const_add σ)
    rw [one_smul] at h1
    exact hasDerivAt_rot_coord (-φ) ij.1 h1
  have hp : ∀ φ : ℝ,
      axialRot (-φ) (gradField v (σ + 1) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1 =
        axialRot (-φ) (gradField v (σ + 0) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1 := by
    intro φ
    have e : v (σ + 1) = v (σ + 0) := by
      funext x
      rw [add_zero, hv.periodic σ x]
    simp only [gradField, e]
  exact modeAverage_time_deriv (β := Fin 3 × Fin 3) ι
    (fun τ φ (ab : Fin 3 × Fin 3) =>
      axialRot (-φ) (gradField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector ab.2))) ab.1)
    (fun τ φ (ab : Fin 3 × Fin 3) => axialRot (-φ) (gradField (fun t x => deriv (fun r => v r x) t) (σ + τ)
      (axialRot φ y) (axialRot φ (unitVector ab.2))) ab.1) ij hF hF' hd hp

theorem time_series_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2)) < ⊤ := by
  set Gt : ℝ → Space → (Space →L[ℝ] Space) := gradField (fun t x => deriv (fun r => v r x) t) with hGt
  have hV1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  have hU1 : ContDiff ℝ 1 (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) :=
    (timeDeriv_smooth hv.smooth).of_le (by simp)
  have cG : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) := continuous_gradField_of_smooth hV1
  have cGt : Continuous (fun z : ℝ × Space => Gt z.1 z.2) := continuous_gradField_of_smooth hU1
  have hGtp : IsTimePeriodic Gt := by
    intro σ y
    have e : (fun x => deriv (fun r => v r x) (σ + 1)) = fun x => deriv (fun r => v r x) σ := by
      funext x
      rw [← deriv_comp_add_const (fun r => v r x) 1 σ]
      congr 1
      funext r
      exact hv.periodic r x
    simp only [hGt, gradField, e]
  have hfin : periodLIntegral (fun σ y => matSq (Gt σ y)) < ⊤ := by
    have h1 := hv.time_derivatives_finite 1 le_rfl
    simp only [norm_iteratedFDeriv_one] at h1
    have hle : periodLIntegral (fun σ y => matSq (Gt σ y)) ≤
        ENNReal.ofReal 3 * periodLIntegral (fun σ y => ‖fderiv ℝ (fun x => deriv (fun s => v s x) σ) y‖ ^ 2) := by
      unfold periodLIntegral
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun σ => ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun y => ?_
      rw [← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (matSq_le_three _)
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1)
  have hpar := hPars.2.1 Gt cGt.aestronglyMeasurable hGtp hfin
  have hg : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι Gt σ y)) < ⊤ := by
    rw [← hpar]; exact hfin
  have hm : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume := fun ι =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Internal.PieceAbsorb.aem_vortAmp cG.aestronglyMeasurable ι).pow_const 2).const_mul _)
  rw [iter_tsum_eq hm]
  refine Internal.SmoothPieceEps.series_finite_of_le (c := ENNReal.ofReal (243 / (4 * Real.pi ^ 2)))
    ENNReal.ofReal_ne_top (g := fun ι σ y => cnormSq (modeGrad ι Gt σ y)) (fun ι σ y => ?_) hg
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : modeGrad ι Gt σ y = fun ij => (((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I) *
      modeGrad ι (gradField v) σ y ij := funext fun ij => modeGrad_time hv ι σ y ij
  rw [e1, cnormSq_const_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    vortAmp, Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _)]
  have hc := Internal.PieceAbsorb.cnormSq_curlOfGrad_le (modeGrad ι (gradField v) σ y)
  have hpi : 0 < Real.pi := Real.pi_pos
  have e2 : 243 / (4 * Real.pi ^ 2) * ((2 * Real.pi * ι.1) ^ 2 * cnormSq (modeGrad ι (gradField v) σ y)) =
      (ι.1 : ℝ) ^ 2 * (243 * cnormSq (modeGrad ι (gradField v) σ y)) := by
    field_simp
    ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)

open GainInternal in
theorem contracted_le {β : Type*} [Fintype β] (M : β → Fin 3 → ℂ) (y : Space) :
    cnormSq (fun b => ∑ j, M b j * (azimuthalField y j : ℂ)) ≤ ‖y‖ ^ 2 * ∑ b, ∑ j, ‖M b j‖ ^ 2 := by
  have hrow : ∀ b, ‖∑ j, M b j * (azimuthalField y j : ℂ)‖ ^ 2 ≤ (∑ j, ‖M b j‖ ^ 2) * cylRadius y ^ 2 := by
    intro b
    have h1 : ‖∑ j, M b j * (azimuthalField y j : ℂ)‖ ≤ ∑ j, ‖M b j‖ * |azimuthalField y j| := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M b j‖) (fun j => |azimuthalField y j|)
    simp only [sq_abs] at h2
    rw [azimuthalField_sq y] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hS : 0 ≤ ∑ b, ∑ j, ‖M b j‖ ^ 2 := by positivity
  calc cnormSq (fun b => ∑ j, M b j * (azimuthalField y j : ℂ))
      ≤ ∑ b, (∑ j, ‖M b j‖ ^ 2) * cylRadius y ^ 2 := Finset.sum_le_sum fun b _ => hrow b
    _ = cylRadius y ^ 2 * ∑ b, ∑ j, ‖M b j‖ ^ 2 := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ ‖y‖ ^ 2 * ∑ b, ∑ j, ‖M b j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (FrequencySeminorm.Internal.cylRadius_sq_le_norm_sq y) hS

open GainInternal in
theorem angular_pointwise_general {β : Type*} [Fintype β] (w : β → ℂ) (M : β → Fin 3 → ℂ) (Bw : β → ℂ)
    (y : Space) (k : ℝ) (hB : cnormSq Bw ≤ (2 : ℝ) ^ 2 * cnormSq w)
    (hid : ∀ b, ∑ j, M b j * (azimuthalField y j : ℂ) = (k : ℂ) * Complex.I * w b + Bw b) :
    k ^ 2 * cnormSq w ≤ 8 * cnormSq w + 2 * ‖y‖ ^ 2 * ∑ b, ∑ j, ‖M b j‖ ^ 2 := by
  set u : β → ℂ := fun b => ∑ j, M b j * (azimuthalField y j : ℂ) with hu
  have hkw : (fun b => (k : ℂ) * Complex.I * w b) = u + -Bw := by
    funext b
    simp only [Pi.add_apply, Pi.neg_apply, hu, hid b]
    ring
  have hsq : cnormSq (fun b => (k : ℂ) * Complex.I * w b) = k ^ 2 * cnormSq w := by
    simp only [cnormSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h1 := cnormSq_add_le u (-Bw)
  rw [← hkw, hsq, FrequencySeminorm.Internal.cnormSq_neg'] at h1
  have h2 := contracted_le M y
  rw [← hu] at h2
  nlinarith

open GainInternal in
theorem angular_grad_mode_bound (hD : ModeDerivativeHolds) (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) :
    ∀ᵐ z : ℝ × Space, ((ι.2 : ℝ)) ^ 2 * cnormSq (modeGrad ι G z.1 z.2) ≤
      8 * cnormSq (modeGrad ι G z.1 z.2) + 2 * ‖z.2‖ ^ 2 * cnormSq (modeSecondDeriv ι H z.1 z.2) := by
  have hRot := axialRotationHolds_proof
  obtain ⟨-, hD2, -⟩ := hD Γ P v G H g hv ι
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => by positivity
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hR2 := Measure.ae_ae_of_ae_prod (ae_all_iff.2 (fun n => (hR Γ P v G H g hv ι (s n)).2))
  have hslice : ∀ᵐ σ, ∀ᵐ y, ((ι.2 : ℝ)) ^ 2 * cnormSq (modeGrad ι G σ y) ≤
      8 * cnormSq (modeGrad ι G σ y) + 2 * ‖y‖ ^ 2 * cnormSq (modeSecondDeriv ι H σ y) := by
    filter_upwards [hD2, hR2] with σ h2 h4
    have hc2 := fun l => weak_components (fun y i => modeGrad ι G σ y (i, l))
      (fun y ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l)) (h2 l).1 (h2 l).2
    have hid2 := angular_identity hRot (β := Fin 3 × Fin 3) (fun y => modeGrad ι G σ y)
      (fun y b j => modeSecondDeriv ι H σ y (b.1, j, b.2)) (ι.2 : ℝ)
      (fun ψ b c => ((axialRot ψ (unitVector c.1) b.1 : ℝ) : ℂ) * ((axialRot (-ψ) (unitVector b.2) c.2 : ℝ) : ℂ))
      (fun b c => ((azimuthalField (unitVector c.1) b.1 : ℝ) : ℂ) * (if b.2 = c.2 then 1 else 0)
        + (if b.1 = c.1 then 1 else 0) * ((-azimuthalField (unitVector b.2) c.2 : ℝ) : ℂ))
      (fun b => (hc2 b.2).1 b.1) (fun b j => (hc2 b.2).2.1 b.1 j)
      (fun φ hφ b j => (hc2 b.2).2.2 φ hφ b.1 j)
      (fun b c => by
        have e2 : axialRot (-0) (unitVector b.2) c.2 = if b.2 = c.2 then 1 else 0 := by
          rw [neg_zero, unit_apply hRot]; exact if_congr eq_comm rfl rfl
        rw [unit_apply hRot, e2]
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        by_cases h1 : b1 = c1 <;> by_cases h2 : b2 = c2 <;> simp [h1, h2, Prod.ext_iff])
      (fun b c => by
        have d1 := (hasDerivAt_axialRot (unitVector c.1) b.1).ofReal_comp
        have d2 := (hasDerivAt_axialRot_neg (unitVector b.2) c.2).ofReal_comp
        have e1 : ((axialRot 0 (unitVector c.1) b.1 : ℝ) : ℂ) = if b.1 = c.1 then 1 else 0 := by
          rw [unit_apply hRot]; split_ifs <;> simp
        have e2 : ((axialRot (-0) (unitVector b.2) c.2 : ℝ) : ℂ) = if b.2 = c.2 then 1 else 0 := by
          rw [neg_zero, unit_apply hRot, if_congr eq_comm rfl rfl]; split_ifs <;> simp
        have := d1.mul d2
        rw [e1, e2] at this
        exact this)
      s hs0 hs
      (fun n => by
        filter_upwards [h4] with y hy b
        have := congrFun (hy n) b
        rw [this]
        simp only [rotCMat, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        ring)
    filter_upwards [hid2] with y hy2
    have := angular_pointwise_general (β := Fin 3 × Fin 3) (modeGrad ι G σ y)
      (fun b j => modeSecondDeriv ι H σ y (b.1, j, b.2)) _ y (ι.2 : ℝ) (grad_bound _) hy2
    refine this.trans (le_of_eq ?_)
    congr 2
    simp only [cnormSq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  refine ae_of_ae_ae ?_ hslice
  have hcn : ∀ {β : Type} [Fintype β], Continuous (cnormSq : (β → ℂ) → ℝ) := by
    intro β _
    unfold cnormSq
    fun_prop
  have mG := hcn.comp_aestronglyMeasurable (modeGrad_aesm hRot ι G hv.measurable_gradient)
  have mH := hcn.comp_aestronglyMeasurable (modeSecondDeriv_aesm hRot ι H hv.measurable_secondDeriv)
  have hy : AEStronglyMeasurable (fun z : ℝ × Space => 2 * ‖z.2‖ ^ 2) volume :=
    (continuous_const.mul ((continuous_norm.comp continuous_snd).pow 2)).aestronglyMeasurable
  exact AEStronglyMeasurable.nullMeasurableSet_le (aestronglyMeasurable_const.mul mG)
    ((aestronglyMeasurable_const.mul mG).add (hy.mul mH))

theorem abs_mul_le_of_sq (k a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : k ^ 2 * a ≤ 8 * a + 2 * r ^ 2 * b) : |k| * a ≤ 3 * a + r * (a + b) := by
  have h0 : 0 ≤ |k| * a := mul_nonneg (abs_nonneg k) ha
  have h1 : 0 ≤ 3 * a + r * (a + b) := by positivity
  have hk : |k| ^ 2 = k ^ 2 := sq_abs k
  have hsq : (|k| * a) ^ 2 ≤ (3 * a + r * (a + b)) ^ 2 := by
    have e : (|k| * a) ^ 2 = a * (k ^ 2 * a) := by rw [mul_pow, hk]; ring
    rw [e]
    have h3 : a * (k ^ 2 * a) ≤ a * (8 * a + 2 * r ^ 2 * b) := mul_le_mul_of_nonneg_left h ha
    nlinarith [sq_nonneg (a - b), mul_nonneg hr ha, mul_nonneg hr hb, mul_nonneg ha hb,
      mul_nonneg (mul_nonneg hr hr) (mul_nonneg ha hb), sq_nonneg (r * (a - b))]
  exact (pow_le_pow_iff_left₀ h0 h1 (by norm_num)).1 hsq

theorem slab_mono_ae {f g : ℝ → Space → ℝ≥0∞} (h : ∀ᵐ z : ℝ × Space, f z.1 z.2 ≤ g z.1 z.2) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  have h2 : ∀ᵐ σ, ∀ᵐ y, f σ y ≤ g σ y := Measure.ae_ae_of_ae_prod h
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae h2] with σ hσ
  exact lintegral_mono_ae hσ

open GainInternal in
theorem angular_series_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) (P : ℝ) (v : ℝ → Space → Space)
    (hv : IsSmoothPerturbation P v) (wt : Space → ℝ) (hwt0 : ∀ y, 0 ≤ wt y) (hwtc : Continuous wt)
    (hwd : ∃ B, ∀ y, ‖y‖ * wt y ≤ B) (hwb : ∃ B, ∀ y, wt y ≤ B) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2)) < ⊤ := by
  have hRot := axialRotationHolds_proof
  have hp := hSP P v hv
  have hG := hp.measurable_gradient
  have hH := hp.measurable_secondDeriv
  obtain ⟨Bd, hBd⟩ := hwd
  obtain ⟨Bw, hBw⟩ := hwb
  have hBw0 : 0 ≤ Bw := (hwt0 0).trans (hBw 0)
  have hBd0 : 0 ≤ Bd := by simpa using hBd 0
  have hcn : ∀ {β : Type} [Fintype β], Continuous (cnormSq : (β → ℂ) → ℝ) := by
    intro β _
    unfold cnormSq
    fun_prop
  set c : ℝ := 243 * (3 * Bw + Bd) with hc
  have mA : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))) volume := fun ι =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hcn.comp_aestronglyMeasurable (modeGrad_aesm hRot ι _ hG)).aemeasurable
  have mB : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) volume := fun ι =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hcn.comp_aestronglyMeasurable (modeSecondDeriv_aesm hRot ι _ hH)).aemeasurable
  have hm : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume := fun ι =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((hwtc.comp continuous_snd).aemeasurable).mul_const _).mul
        ((Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2))
  have hpt : ∀ ι, ∀ᵐ z : ℝ × Space,
      ENNReal.ofReal (wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2) ≤
        ENNReal.ofReal c * ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2)
          + cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) := by
    intro ι
    filter_upwards [angular_grad_mode_bound hDer hRotM hp ι] with z hz
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set a := cnormSq (modeGrad ι (gradField v) z.1 z.2) with ha
    set b := cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2) with hb
    have ha0 : 0 ≤ a := Internal.PieceAbsorb.cnormSq_nonneg' _
    have hb0 : 0 ≤ b := Internal.PieceAbsorb.cnormSq_nonneg' _
    have hV : vortAmp (gradField v) ι z.1 z.2 ^ 2 ≤ 243 * a := by
      rw [vortAmp, Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _)]
      exact Internal.PieceAbsorb.cnormSq_curlOfGrad_le _
    have hk := abs_mul_le_of_sq (ι.2 : ℝ) a b ‖z.2‖ ha0 hb0 (norm_nonneg _) hz
    have hw0 := hwt0 z.2
    have hw1 := hBw z.2
    have hw2 := hBd z.2
    calc wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2
        ≤ wt z.2 * |(ι.2 : ℝ)| * (243 * a) :=
          mul_le_mul_of_nonneg_left hV (mul_nonneg hw0 (abs_nonneg _))
      _ = 243 * (wt z.2 * (|(ι.2 : ℝ)| * a)) := by ring
      _ ≤ 243 * (wt z.2 * (3 * a + ‖z.2‖ * (a + b))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hw0) (by norm_num)
      _ = 243 * (3 * wt z.2 * a + (‖z.2‖ * wt z.2) * (a + b)) := by ring
      _ ≤ 243 * (3 * Bw * a + Bd * (a + b)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have e1 : 3 * wt z.2 * a ≤ 3 * Bw * a := by nlinarith
          have e2 : (‖z.2‖ * wt z.2) * (a + b) ≤ Bd * (a + b) :=
            mul_le_mul_of_nonneg_right hw2 (add_nonneg ha0 hb0)
          linarith
      _ ≤ c * (a + b) := by
          rw [hc]
          nlinarith [mul_nonneg hBw0 hb0]
  have hGpar := hPars.2.1 (gradField v) hG hp.periodic_gradient hp.gradient_finite
  have hHfin : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ :=
    lt_of_le_of_lt (perturbationSecondDerivBoundHolds_proof ∅ P v _ _ _ hp) hp.sumSecondPartials_finite
  have hHpar := hPars.2.2.1 (secondDerivField v) hH hp.periodic_secondDeriv hHfin
  have fA : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)) < ⊤ := by
    rw [← hGpar]; exact hp.gradient_finite
  have fB : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) < ⊤ := by
    rw [← hHpar]; exact hHfin
  have hsum : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y) + cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) < ⊤ := by
    have mAB : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
        ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2)
          + cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) volume := fun ι =>
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hcn.comp_aestronglyMeasurable (modeGrad_aesm hRot ι _ hG)).aemeasurable.add
          (hcn.comp_aestronglyMeasurable (modeSecondDeriv_aesm hRot ι _ hH)).aemeasurable)
    rw [← Internal.SmoothPieceEps.slab_tsum_eq mAB]
    have e : ∀ z : ℝ × Space, ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2)
          + cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) =
        ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))
          + ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2)) := by
      intro z
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun ι => ?_
      exact ENNReal.ofReal_add (Internal.PieceAbsorb.cnormSq_nonneg' _) (Internal.PieceAbsorb.cnormSq_nonneg' _)
    simp_rw [e]
    rw [lintegral_add_left' (Internal.SmoothPieceEps.slab_aem (AEMeasurable.tsum mA)),
      Internal.SmoothPieceEps.slab_tsum_eq (f := fun ι σ y => cnormSq (modeGrad ι (gradField v) σ y)) mA,
      Internal.SmoothPieceEps.slab_tsum_eq (f := fun ι σ y => cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) mB]
    exact ENNReal.add_lt_top.2 ⟨fA, fB⟩
  rw [iter_tsum_eq hm]
  calc ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2)
      ≤ ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal c *
          ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y) + cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) :=
        ENNReal.tsum_le_tsum fun ι => slab_mono_ae (hpt ι)
    _ = ENNReal.ofReal c * ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y) + cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [ENNReal.tsum_mul_left]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum

end Internal.SmoothPieceEpsFrequency

end Coercive

end Breakdown
