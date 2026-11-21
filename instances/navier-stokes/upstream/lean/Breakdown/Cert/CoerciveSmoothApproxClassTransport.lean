import Breakdown.Cert.CoerciveSmoothApproxGeneral
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.Cert.CoercivePieceField
import Breakdown.Cert.CoerciveSmoothApproxPeriodBound
import Breakdown.Cert.CoerciveSmoothApproxIterated

open scoped ContDiff ENNReal Topology Convolution InnerProductSpace
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem mollify_time_deriv (n : ℕ) {v : ℝ → Space → Space} (hv : LocallyIntegrable (joint v) volume)
    (σ : ℝ) (y : Space) :
    deriv (fun s => mollify n v s y) σ =
      ∫ t, fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t) := by
  have hdiff : DifferentiableAt ℝ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v) (σ, y) :=
    (mollify_smooth n hv).differentiable (by simp) (σ, y)
  have hin : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : Space)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt σ hin
  rw [show (fun s => mollify n v s y) =
    (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v) ∘ (fun s : ℝ => (s, y)) from rfl,
    h1.deriv, convolution_fderiv_apply n hv, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply]

theorem gradient_sq_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖G σ y‖ ^ 2) < ⊤ := by
  calc periodLIntegral (fun σ y => ‖G σ y‖ ^ 2)
      ≤ periodLIntegral (fun σ y => 3 * matSq (G σ y)) :=
        lintegral_mono fun σ => lintegral_mono fun y =>
          ENNReal.ofReal_le_ofReal (PerturbationFacts.sq_norm_le_three_matNorm _)
    _ = ENNReal.ofReal 3 * periodLIntegral (fun σ y => matSq (G σ y)) := by
        unfold periodLIntegral
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite

theorem scalar_convolution_integrable {φ : ℝ × Space → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × Space → E}
    (hf : LocallyIntegrable f volume) (x : ℝ × Space) :
    Integrable (fun t => φ t • f (x - t)) volume := by
  have := volume_prod_invariantClass
  have h := (hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ hf) x
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using h

theorem kernel_fderiv_continuous (n : ℕ) (w : ℝ × Space → ℝ × Space) (hw : Continuous w) :
    Continuous (fun t => fderiv ℝ (kernel n) t (w t)) :=
  ((kernel_contDiff n).continuous_fderiv (by simp)).clm_apply hw

theorem kernel_fderiv_hasCompactSupport (n : ℕ) (w : ℝ × Space → ℝ × Space) :
    HasCompactSupport (fun t => fderiv ℝ (kernel n) t (w t)) := by
  refine ((kernel_hasCompactSupport n).fderiv (𝕜 := ℝ)).mono ?_
  intro t ht h0
  exact ht (by simp [h0])

theorem coordinate_kernel_contDiff (n : ℕ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun t : ℝ × Space => t.2 k * kernel n t) := by
  set ℓ : ℝ × Space →L[ℝ] ℝ :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space) with hℓ
  have e : (fun t : ℝ × Space => t.2 k * kernel n t) = fun t => ℓ t * kernel n t := by
    funext t
    simp [hℓ]
  rw [e]
  exact (ContinuousLinearMap.contDiff ℓ).mul (kernel_contDiff n)

theorem coordinate_kernel_hasCompactSupport (n : ℕ) (k : Fin 3) :
    HasCompactSupport (fun t : ℝ × Space => t.2 k * kernel n t) :=
  (kernel_hasCompactSupport n).mul_left

theorem coordinate_kernel_fderiv (n : ℕ) (k : Fin 3) (t : ℝ × Space) :
    fderiv ℝ (fun t : ℝ × Space => t.2 k * kernel n t) t (0, unitVector k) =
      kernel n t + t.2 k * fderiv ℝ (kernel n) t (0, unitVector k) := by
  set ℓ : ℝ × Space →L[ℝ] ℝ :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space) with hℓ
  have e : (fun t : ℝ × Space => t.2 k * kernel n t) = fun t => ℓ t * kernel n t := by
    funext t
    simp [hℓ]
  have hK : HasFDerivAt (kernel n) (fderiv ℝ (kernel n) t) t :=
    ((kernel_contDiff n).differentiable (by simp) t).hasFDerivAt
  have h : HasFDerivAt (fun t => ℓ t * kernel n t) (ℓ t • fderiv ℝ (kernel n) t + kernel n t • ℓ) t :=
    (ℓ.hasFDerivAt (x := t)).mul hK
  rw [e, h.fderiv]
  simp [hℓ, unitVector]
  ring

theorem fderiv_apply_snd_eq_sum (L : ℝ × Space →L[ℝ] ℝ) (z : Space) :
    L (0, z) = ∑ k : Fin 3, z k * L (0, unitVector k) := by
  have hz : z = ∑ k, z k • unitVector k := by
    ext j
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  have h := congrArg (L.comp (ContinuousLinearMap.inr ℝ ℝ Space)) hz
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simpa using h

theorem coordinate_kernel_sum (n : ℕ) (t : ℝ × Space) :
    ∑ k : Fin 3, fderiv ℝ (fun t : ℝ × Space => t.2 k * kernel n t) t (0, unitVector k) =
      3 * kernel n t + fderiv ℝ (kernel n) t (0, t.2) := by
  simp_rw [coordinate_kernel_fderiv]
  rw [Finset.sum_add_distrib, fderiv_apply_snd_eq_sum (fderiv ℝ (kernel n) t) t.2]
  simp

theorem coordinate_convolution_sum {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) (σ : ℝ) (y : Space) :
    ∑ k : Fin 3, ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        joint (fun s x => G s x (unitVector k))) (σ, y) =
      (3 : ℝ) • (∫ t, kernel n t • joint v ((σ, y) - t)) +
        ∫ t, fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t) := by
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  have hk : ∀ k : Fin 3, ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      joint (fun s x => G s x (unitVector k))) (σ, y) =
      ∫ t, fderiv ℝ (fun t : ℝ × Space => t.2 k * kernel n t) t (0, unitVector k) • joint v ((σ, y) - t) := by
    intro k
    rw [← partial_eq_of (coordinate_kernel_contDiff n k) (coordinate_kernel_hasCompactSupport n k) hvl
      (joint_apply_locallyIntegrable hGl (unitVector k)) k
      (hv.weak_gradient.mono fun s hs φ hφ => hs.2.2 φ hφ k) σ y, convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
  have hint : ∀ k : Fin 3, Integrable (fun t => fderiv ℝ (fun t : ℝ × Space => t.2 k * kernel n t) t
      (0, unitVector k) • joint v ((σ, y) - t)) volume := fun k =>
    scalar_convolution_integrable
      (((coordinate_kernel_contDiff n k).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((coordinate_kernel_hasCompactSupport n k).fderiv_apply (𝕜 := ℝ) _) hvl _
  simp_rw [hk]
  rw [← integral_finsetSum _ fun k _ => hint k]
  simp_rw [← Finset.sum_smul, coordinate_kernel_sum, add_smul, mul_smul]
  have iB : Integrable (fun t => kernel n t • joint v ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_contDiff n).continuous (kernel_hasCompactSupport n) hvl _
  have iD : Integrable (fun t => fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_fderiv_continuous n _ (continuous_const.prodMk continuous_snd))
      (kernel_fderiv_hasCompactSupport n _) hvl _
  have iB3 : Integrable (fun t => (3 : ℝ) • (kernel n t • joint v ((σ, y) - t))) volume := iB.smul (3 : ℝ)
  rw [integral_add iB3 iD, integral_smul]

theorem mollify_transportPart_eq {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) (σ : ℝ) (y : Space) :
    transportPart P (mollify n v) σ y =
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) +
        (1 / 2 : ℝ) • ∑ k : Fin 3, ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          joint (fun s x => G s x (unitVector k))) (σ, y) := by
  have hH := volume_prod_invariantClass
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hgl : LocallyIntegrable (joint g) volume := FrequencySeminorm.Internal.derivative_locallyIntegrable hv
  have iA : Integrable (fun t => fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_fderiv_continuous n _ continuous_const)
      (kernel_fderiv_hasCompactSupport n _) hvl _
  have iB : Integrable (fun t => kernel n t • joint v ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_contDiff n).continuous (kernel_hasCompactSupport n) hvl _
  have iC : Integrable (fun t => fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_fderiv_continuous n _ continuous_const)
      (kernel_fderiv_hasCompactSupport n _) hvl _
  have iD : Integrable (fun t => fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_fderiv_continuous n _ (continuous_const.prodMk continuous_snd))
      (kernel_fderiv_hasCompactSupport n _) hvl _
  have iK : Integrable (fun t => kernel n t • joint g ((σ, y) - t)) volume :=
    scalar_convolution_integrable (kernel_contDiff n).continuous (kernel_hasCompactSupport n) hgl _
  have jA : Integrable (fun t => (1 / P) • (fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t))) volume :=
    iA.smul (1 / P)
  have jC : Integrable (fun t => (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t))) volume :=
    iC.smul (1 / 2 : ℝ)
  have jD : Integrable (fun t => (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t))) volume :=
    iD.smul (1 / 2 : ℝ)
  have jAB : Integrable (fun t => (1 / P) • (fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
      kernel n t • joint v ((σ, y) - t)) volume := jA.sub iB
  have jABC : Integrable (fun t => (1 / P) • (fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
      kernel n t • joint v ((σ, y) - t) +
      (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t))) volume := jAB.add jC
  have iF : Integrable (fun t => (1 / P) • (fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
      kernel n t • joint v ((σ, y) - t) +
      (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t)) -
      (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t))) volume := jABC.sub jD
  have hT : (1 / P) • (∫ t, fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
      (∫ t, kernel n t • joint v ((σ, y) - t)) +
      (1 / 2 : ℝ) • (∫ t, fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t)) -
      (1 / 2 : ℝ) • (∫ t, fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t)) =
      ∫ t, kernel n t • joint g ((σ, y) - t) := by
    refine ext_inner_left ℝ fun e => ?_
    set φ : ℝ → Space → Space := fun s z => kernel n ((σ, y) - (s, z)) • e with hφ
    have hφt : IsSpaceTimeTestVector φ := by
      have e0 : (fun z : ℝ × Space => φ z.1 z.2) = fun z => kernel n ((σ, y) - z) • e := by
        funext z
        simp only [hφ, Prod.mk.eta]
      rw [IsSpaceTimeTestVector, e0]
      exact ⟨((kernel_contDiff n).comp (contDiff_const.sub contDiff_id)).smul contDiff_const,
        ((kernel_hasCompactSupport n).comp_homeomorph (Homeomorph.subLeft ((σ, y) : ℝ × Space))).smul_right⟩
    have hds : ∀ s z, deriv (fun s' => φ s' z) s = -(fderiv ℝ (kernel n) ((σ, y) - (s, z)) (1, 0)) • e := by
      intro s z
      have hin : HasDerivAt (fun s' : ℝ => ((σ, y) : ℝ × Space) - (s', z)) (-((1 : ℝ), (0 : Space))) s :=
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s z)).const_sub _
      have hK := ((kernel_contDiff n).differentiable (by simp) ((σ, y) - (s, z))).hasFDerivAt
      have h2 := (hK.comp_hasDerivAt s hin).smul_const e
      have e1 : (fun s' => φ s' z) = fun s' => (kernel n ∘ fun s' : ℝ => ((σ, y) : ℝ × Space) - (s', z)) s' • e := by
        funext s'
        simp [hφ]
      rw [e1, h2.deriv, map_neg, neg_smul]
    have hdz : ∀ s z, fderiv ℝ (φ s) z z = -(fderiv ℝ (kernel n) ((σ, y) - (s, z)) (0, z)) • e := by
      intro s z
      have hc : DifferentiableAt ℝ (fun z' : Space => kernel n ((σ, y) - (s, z'))) z :=
        (kernel_shift_testFunction n σ s y).1.differentiable (by simp) z
      have e1 : φ s = fun z' => kernel n ((σ, y) - (s, z')) • e := by
        funext z'
        simp [hφ]
      rw [e1, fderiv_smul_const hc]
      simp only [ContinuousLinearMap.smulRight_apply]
      rw [kernel_shift_fderiv n σ s y z z]
    have h := hv.transport φ hφt
    have hsplit : ∫ t, ((1 / P) • (fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
        kernel n t • joint v ((σ, y) - t) +
        (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t)) -
        (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t))) =
        (1 / P) • (∫ t, fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
        (∫ t, kernel n t • joint v ((σ, y) - t)) +
        (1 / 2 : ℝ) • (∫ t, fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t)) -
        (1 / 2 : ℝ) • (∫ t, fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t)) := by
      rw [integral_sub jABC jD, integral_add jAB jC, integral_sub jA iB, integral_smul, integral_smul,
        integral_smul]
    rw [← hsplit, ← integral_inner iF e, ← integral_inner iK e]
    calc ∫ t, ⟪e, (1 / P) • (fderiv ℝ (kernel n) t (1, 0) • joint v ((σ, y) - t)) -
          kernel n t • joint v ((σ, y) - t) +
          (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, y) • joint v ((σ, y) - t)) -
          (1 / 2 : ℝ) • (fderiv ℝ (kernel n) t (0, t.2) • joint v ((σ, y) - t))⟫_ℝ
        = ∫ t, ⟪v ((σ, y) - t).1 ((σ, y) - t).2, -(1 / P) • deriv (fun s => φ s ((σ, y) - t).2) ((σ, y) - t).1
            - φ ((σ, y) - t).1 ((σ, y) - t).2
            - (1 / 2 : ℝ) • fderiv ℝ (φ ((σ, y) - t).1) ((σ, y) - t).2 ((σ, y) - t).2⟫_ℝ := by
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          simp only [hds, hdz, Prod.mk.eta, sub_sub_cancel]
          have e2 : (((0 : ℝ), (((σ, y) : ℝ × Space) - t).2) : ℝ × Space) = ((0 : ℝ), y) - ((0 : ℝ), t.2) := by
            simp
          rw [e2, map_sub]
          have e3 : φ ((σ, y) - t).1 ((σ, y) - t).2 = kernel n t • e := by
            simp [hφ]
          rw [e3]
          simp only [joint, inner_sub_right, inner_add_right, real_inner_smul_right, inner_neg_right,
            neg_smul, sub_smul]
          rw [real_inner_comm e]
          ring
      _ = ∫ z : ℝ × Space, ⟪v z.1 z.2, -(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2
            - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2⟫_ℝ :=
          integral_sub_left_eq_self (fun z : ℝ × Space => ⟪v z.1 z.2, -(1 / P) • deriv (fun s => φ s z.2) z.1
            - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2⟫_ℝ) volume ((σ, y) : ℝ × Space)
      _ = ∫ z : ℝ × Space, ⟪g z.1 z.2, φ z.1 z.2⟫_ℝ := h
      _ = ∫ t, ⟪g ((σ, y) - t).1 ((σ, y) - t).2, φ ((σ, y) - t).1 ((σ, y) - t).2⟫_ℝ :=
          (integral_sub_left_eq_self (fun z : ℝ × Space => ⟪g z.1 z.2, φ z.1 z.2⟫_ℝ) volume
            ((σ, y) : ℝ × Space)).symm
      _ = ∫ t, ⟪e, kernel n t • joint g ((σ, y) - t)⟫_ℝ := by
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          simp only [hφ, Prod.mk.eta, sub_sub_cancel, real_inner_smul_right, joint]
          rw [real_inner_comm e]
  have hsum := coordinate_convolution_sum hv n σ y
  rw [transportPart, mollify_time_deriv n hvl, mollify_fderiv_eq n hvl σ y y, convolution_def,
    convolution_def, hsum]
  simp only [ContinuousLinearMap.lsmul_apply]
  have hB : mollify n v σ y = ∫ t, kernel n t • joint v ((σ, y) - t) := by
    simp only [mollify, convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [hB, ← hT]
  module

theorem locallyIntegrable_norm {E : Type*} [NormedAddCommGroup E] {f : ℝ × Space → E}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun z => ‖f z‖) volume :=
  hf.mono hf.aestronglyMeasurable.norm (Eventually.of_forall fun _ => le_of_eq (norm_norm _))

theorem transport_finite_bound {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ j : ℕ, periodLIntegral (fun σ y =>
      ‖iteratedFDeriv ℝ j (transportPart P (mollify n v) σ) y‖ ^ 2) < ⊤ := by
  intro j
  have hH := volume_prod_invariantClass
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  have hgl : LocallyIntegrable (joint g) volume := FrequencySeminorm.Internal.derivative_locallyIntegrable hv
  have hGkl : ∀ k : Fin 3, LocallyIntegrable (joint (fun s x => G s x (unitVector k))) volume :=
    fun k => joint_apply_locallyIntegrable hGl _
  have c1 : ContDiff ℝ ∞ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) :=
    (kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hgl
  have c2 : ∀ k : Fin 3, ContDiff ℝ ∞ ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      joint (fun s x => G s x (unitVector k))) := fun k =>
    (coordinate_kernel_hasCompactSupport n k).contDiff_convolution_left _ (coordinate_kernel_contDiff n k) (hGkl k)
  have hle : ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  set S : ℝ × Space → Space := fun z => ∑ k : Fin 3, ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      joint (fun s x => G s x (unitVector k))) z with hS
  have cs : ContDiff ℝ ∞ S := ContDiff.sum fun k _ => c2 k
  have cs2 : ContDiff ℝ ∞ ((1 / 2 : ℝ) • S) := cs.const_smul (1 / 2 : ℝ)
  set Φ : ℝ × Space → Space := (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) +
    (1 / 2 : ℝ) • S with hΦ
  have cΦ : ContDiff ℝ ∞ Φ := c1.add cs2
  have hslice : ∀ σ, transportPart P (mollify n v) σ = fun y => Φ (σ, y) := by
    intro σ
    funext y
    rw [mollify_transportPart_eq hv n σ y]
    rfl
  set Θ : ℝ × Space → ℝ := fun t => ‖iteratedFDeriv ℝ j (kernel n) t‖ +
    ∑ k : Fin 3, ‖iteratedFDeriv ℝ j (fun t : ℝ × Space => t.2 k * kernel n t) t‖ with hΘ
  have hΘc : Continuous Θ :=
    ((kernel_contDiff n).continuous_iteratedFDeriv hle).norm.add
      (continuous_finsetSum _ fun k _ => ((coordinate_kernel_contDiff n k).continuous_iteratedFDeriv hle).norm)
  have hΘs : HasCompactSupport Θ := by
    refine (kernel_hasCompactSupport n).mono' ?_
    intro t ht
    by_contra hn
    apply ht
    have h1 : iteratedFDeriv ℝ j (kernel n) t = 0 :=
      Function.notMem_support.mp fun h => hn (support_iteratedFDeriv_subset j h)
    have h2 : ∀ k : Fin 3, iteratedFDeriv ℝ j (fun t : ℝ × Space => t.2 k * kernel n t) t = 0 := fun k =>
      Function.notMem_support.mp fun h => hn (tsupport_mul_subset_right (support_iteratedFDeriv_subset j h))
    simp [hΘ, h1, h2]
  set w : ℝ → Space → ℝ := fun s x => ‖g s x‖ + ‖G s x‖ with hw
  have hwl : LocallyIntegrable (joint w) volume := (locallyIntegrable_norm hgl).add (locallyIntegrable_norm hGl)
  have hpt : ∀ σ y, ‖iteratedFDeriv ℝ j (transportPart P (mollify n v) σ) y‖ ^ 2 ≤
      ‖∫ t, Θ t • joint w ((σ, y) - t)‖ ^ 2 := by
    intro σ y
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [hslice σ]
    refine (norm_iteratedFDeriv_slice_le cΦ j σ y).trans ?_
    have eD : iteratedFDeriv ℝ j Φ (σ, y) = iteratedFDeriv ℝ j (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) +
        (1 / 2 : ℝ) • ∑ k : Fin 3, iteratedFDeriv ℝ j ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          joint (fun s x => G s x (unitVector k))) (σ, y) := by
      rw [hΦ, iteratedFDeriv_add_apply (c1.of_le hle).contDiffAt (cs2.of_le hle).contDiffAt,
        iteratedFDeriv_const_smul_apply (cs.of_le hle).contDiffAt, hS, iteratedFDeriv_sum fun k _ => (c2 k).of_le hle,
        Finset.sum_apply]
    have b1 := norm_iteratedFDeriv_convolution_le hgl j (kernel n) (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernel_contDiff n) (kernel_hasCompactSupport n) ContinuousLinearMap.opNorm_lsmul_le (σ, y)
    have b2 := fun k : Fin 3 => norm_iteratedFDeriv_convolution_le (hGkl k) j
      (fun t : ℝ × Space => t.2 k * kernel n t) (ContinuousLinearMap.lsmul ℝ ℝ)
      (coordinate_kernel_contDiff n k) (coordinate_kernel_hasCompactSupport n k)
      ContinuousLinearMap.opNorm_lsmul_le (σ, y)
    have ia1 : Integrable (fun t => ‖iteratedFDeriv ℝ j (kernel n) t‖ * ‖joint g ((σ, y) - t)‖) volume := by
      simpa only [smul_eq_mul] using scalar_convolution_integrable
        ((kernel_contDiff n).continuous_iteratedFDeriv hle).norm
        ((kernel_hasCompactSupport n).iteratedFDeriv j).norm (locallyIntegrable_norm hgl) (σ, y)
    have ia2 : ∀ k : Fin 3, Integrable (fun t => ‖iteratedFDeriv ℝ j (fun t : ℝ × Space => t.2 k * kernel n t) t‖ *
        ‖joint (fun s x => G s x (unitVector k)) ((σ, y) - t)‖) volume := fun k => by
      simpa only [smul_eq_mul] using scalar_convolution_integrable
        ((coordinate_kernel_contDiff n k).continuous_iteratedFDeriv hle).norm
        ((coordinate_kernel_hasCompactSupport n k).iteratedFDeriv j).norm (locallyIntegrable_norm (hGkl k)) (σ, y)
    have iΘ : Integrable (fun t => Θ t * joint w ((σ, y) - t)) volume := by
      simpa only [smul_eq_mul] using scalar_convolution_integrable hΘc hΘs hwl (σ, y)
    have hsum : (∫ t, ‖iteratedFDeriv ℝ j (kernel n) t‖ * ‖joint g ((σ, y) - t)‖) +
        ∑ k : Fin 3, ∫ t, ‖iteratedFDeriv ℝ j (fun t : ℝ × Space => t.2 k * kernel n t) t‖ *
          ‖joint (fun s x => G s x (unitVector k)) ((σ, y) - t)‖ ≤ ∫ t, Θ t * joint w ((σ, y) - t) := by
      rw [← integral_finsetSum _ fun k _ => ia2 k, ← integral_add ia1 (integrable_finsetSum _ fun k _ => ia2 k)]
      refine integral_mono (ia1.add (integrable_finsetSum _ fun k _ => ia2 k)) iΘ fun t => ?_
      simp only [hΘ, hw, joint, add_mul, Finset.sum_mul]
      refine add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _))
        (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine ((G ((σ, y) - t).1 ((σ, y) - t).2).le_opNorm _).trans ?_
      rw [PerturbationFacts.norm_unitVector_eq, mul_one]
      exact le_add_of_nonneg_left (norm_nonneg _)
    have hfin : ∫ t, Θ t * joint w ((σ, y) - t) = ‖∫ t, Θ t • joint w ((σ, y) - t)‖ := by
      have h0 : ∀ t, 0 ≤ Θ t * joint w ((σ, y) - t) := fun t => by
        simp only [hΘ, hw, joint]
        positivity
      rw [Real.norm_of_nonneg (integral_nonneg fun t => by simp only [Pi.zero_apply, smul_eq_mul]; exact h0 t)]
      simp only [smul_eq_mul]
    rw [eD, ← hfin]
    refine (norm_add_le _ _).trans ?_
    refine le_trans (add_le_add b1 ?_) hsum
    rw [norm_smul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [Real.norm_eq_abs])) ?_
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => b2 k)
  have hper : IsTimePeriodic w := fun σ y => by
    simp only [hw, hv.periodic_derivative σ y, hv.periodic_gradient σ y]
  have hwm : AEStronglyMeasurable (joint w) volume :=
    hv.measurable_derivative.norm.add hv.measurable_gradient.norm
  have hw2 : periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) < ⊤ := by
    have m1 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (2 * ‖g z.1 z.2‖ ^ 2)) volume :=
      ((hv.measurable_derivative.norm.aemeasurable.pow_const 2).const_mul 2).ennreal_ofReal
    have m2 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (2 * ‖G z.1 z.2‖ ^ 2)) volume :=
      ((hv.measurable_gradient.norm.aemeasurable.pow_const 2).const_mul 2).ennreal_ofReal
    have m12 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (2 * ‖g z.1 z.2‖ ^ 2 + 2 * ‖G z.1 z.2‖ ^ 2)) volume :=
      (((hv.measurable_derivative.norm.aemeasurable.pow_const 2).const_mul 2).add
        ((hv.measurable_gradient.norm.aemeasurable.pow_const 2).const_mul 2)).ennreal_ofReal
    refine lt_of_le_of_lt (PieceField.Internal.periodLIntegral_mono
      (g := fun σ y => 2 * ‖g σ y‖ ^ 2 + 2 * ‖G σ y‖ ^ 2) fun σ y => ?_) ?_
    · simp only [hw]
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (‖g σ y‖ - ‖G σ y‖)]
    · refine lt_of_le_of_lt (PieceField.Internal.periodLIntegral_add_le m1 m2 m12) ?_
      rw [PieceField.Internal.periodLIntegral_const_mul (by norm_num) (fun σ y => ‖g σ y‖ ^ 2),
        PieceField.Internal.periodLIntegral_const_mul (by norm_num) (fun σ y => ‖G σ y‖ ^ 2)]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.derivative_finite,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (gradient_sq_lt_top hv)⟩
  refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y =>
    ENNReal.ofReal_le_ofReal (hpt σ y)) ?_
  refine lt_of_le_of_lt (period_convolution_sq_le hΘc hΘs hwm hper) ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (hΘc.integrable_of_hasCompactSupport hΘs).2) hw2

end Internal.SmoothApprox

end Coercive

end Breakdown
