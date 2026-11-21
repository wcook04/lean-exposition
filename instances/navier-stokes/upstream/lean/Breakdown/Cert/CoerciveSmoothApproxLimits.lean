import Breakdown.Cert.CoerciveSmoothApproxClass
import Breakdown.Cert.CoerciveSmoothApproxLimitsWhole
import Breakdown.Cert.CoerciveSmoothApproxLimitsTransport

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem convolution_sq_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → Space → E} (hw : AEStronglyMeasurable (joint w) volume) (hper : IsTimePeriodic w)
    (hfin : periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) < ⊤) :
    Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint w) (σ, y) - w σ y‖ ^ 2))
      atTop (𝓝 0) :=
  period_convolution_sq_tendsto hw hper hfin

theorem matSq_le_three_sq (A : Space →L[ℝ] Space) : matSq A ≤ 3 * ‖A‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i => by
    have := A.le_opNorm (unitVector i)
    rw [PerturbationFacts.norm_unitVector_eq, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖A‖ ^ 2 := by simp

theorem mollify_gradient_tendsto {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    Tendsto (fun n => periodLIntegral (fun σ y => matSq (gradField (mollify n v) σ y - G σ y)))
      atTop (𝓝 0) := by
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 3)
    (convolution_sq_tendsto (w := G) hv.measurable_gradient hv.periodic_gradient
      (gradient_sq_lt_top hv)) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    (fun n => ?_)
  have e : ∀ σ y, gradField (mollify n v) σ y =
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, y) := fun σ y => by
    simp only [gradField, mollify_fderiv_clm n hvl hGl hv.weak_gradient σ]
  unfold periodLIntegral
  simp_rw [e]
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal
        (matSq ((kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, y) - G σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal 3 * ENNReal.ofReal
        (‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, y) - G σ y‖ ^ 2) :=
        lintegral_mono fun σ => lintegral_mono fun y => by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (matSq_le_three_sq _)
    _ = _ := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem joint_apply_locallyIntegrable_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → Space → (Space →L[ℝ] E)} (hG : LocallyIntegrable (joint G) volume) (e : Space) :
    LocallyIntegrable (joint (fun s x => G s x e)) volume :=
  (hG.smul ‖e‖).mono ((ContinuousLinearMap.apply ℝ E e).continuous.comp_aestronglyMeasurable
    hG.aestronglyMeasurable) (Eventually.of_forall fun z => by
      rw [Pi.smul_apply, norm_smul, norm_norm]
      simpa [joint, mul_comm] using (G z.1 z.2).le_opNorm e)

theorem convolution_apply_eq (n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : ℝ → Space → (Space →L[ℝ] E)}
    (hF : LocallyIntegrable (joint F) volume) (x : ℝ × Space) (e : Space) :
    (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint F) x e =
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (fun s z => F s z e)) x := by
  have := volume_prod_invariantClass
  have hex := ((kernel_hasCompactSupport n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernel_contDiff n).continuous hF) x
  rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp [joint]

theorem mollify_secondDerivField_eq {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) (σ : ℝ) (y : Space) :
    secondDerivField (mollify n v) σ y =
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint H) (σ, y) := by
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  have hHl : LocallyIntegrable (joint H) volume := PerturbationFacts.secondDeriv_locallyIntegrable hv
  have hH := volume_prod_invariantClass
  have hconv : ContDiff ℝ ∞ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) :=
    (kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hGl
  have hdF : DifferentiableAt ℝ
      (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, x)) y :=
    ((hconv.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) y
  unfold secondDerivField
  rw [mollify_fderiv_clm n hvl hGl hv.weak_gradient σ]
  refine ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_)
  refine ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun j => ?_)
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe]
  have hGj : LocallyIntegrable (joint (fun s x => G s x (EuclideanSpace.single j 1))) volume :=
    joint_apply_locallyIntegrable hGl _
  have hHj : LocallyIntegrable (joint (fun s x => (H s x).flip (EuclideanSpace.single j 1))) volume := by
    exact (hHl.smul ‖EuclideanSpace.single j (1 : ℝ)‖).mono
      ((ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).continuous.clm_apply continuous_const
        |>.comp_aestronglyMeasurable hHl.aestronglyMeasurable) (Eventually.of_forall fun z => by
          rw [Pi.smul_apply, norm_smul, norm_norm, mul_comm]
          simpa [joint] using ((H z.1 z.2).flip).le_opNorm (EuclideanSpace.single j 1))
  have e1 : (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, x)
      (EuclideanSpace.single j 1)) = fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        joint (fun s z => G s z (EuclideanSpace.single j 1))) (σ, x) := by
    funext x
    exact convolution_apply_eq n hGl (σ, x) _
  have e2 := fderiv_clm_apply (c := fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    joint G) (σ, x)) (u := fun _ => (EuclideanSpace.single j (1 : ℝ) : Space)) hdF
    (differentiableAt_const _)
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at e2
  have e3 : fderiv ℝ (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, x)) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint G) (σ, x)
        (EuclideanSpace.single j 1)) y (EuclideanSpace.single i 1) := by
    rw [e2]
    rfl
  rw [e3, e1, slice_fderiv_clm_of (kernel_contDiff n) (kernel_hasCompactSupport n) hGj hHj
    (hv.weak_secondDeriv.mono fun s hs => hs j) σ, convolution_apply_eq n hHj,
    convolution_apply_eq n hHl, convolution_apply_eq n (joint_apply_locallyIntegrable_of hHl _)]
  simp only [ContinuousLinearMap.flip_apply]

theorem sq_add_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem secondDerivSq_le_sq (A : Space →L[ℝ] Space →L[ℝ] Space) : secondDerivSq A ≤ 9 * ‖A‖ ^ 2 := by
  have h : ∀ j l : Fin 3, ‖A (unitVector j) (unitVector l)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun j l => by
    have h1 := (A (unitVector j)).le_opNorm (unitVector l)
    have h2 := A.le_opNorm (unitVector j)
    rw [PerturbationFacts.norm_unitVector_eq, mul_one] at h1 h2
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  unfold secondDerivSq
  simp only [Fin.sum_univ_three]
  linarith [h 0 0, h 0 1, h 0 2, h 1 0, h 1 1, h 1 2, h 2 0, h 2 1, h 2 2]

theorem sq_le_secondDerivSq (A : Space →L[ℝ] Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 9 * secondDerivSq A := by
  have h1 : ‖A‖ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖A (unitVector j) (unitVector l)‖ :=
    (PerturbationFacts.opNorm_le_sum_apply A).trans
      (Finset.sum_le_sum fun j _ => PerturbationFacts.opNorm_le_sum_apply _)
  have h0 := norm_nonneg A
  have h2 := pow_le_pow_left₀ h0 h1 2
  unfold secondDerivSq
  simp only [Fin.sum_univ_three] at h2 ⊢
  have := sq_add_three_le
    (‖A (unitVector 0) (unitVector 0)‖ + ‖A (unitVector 0) (unitVector 1)‖ + ‖A (unitVector 0) (unitVector 2)‖)
    (‖A (unitVector 1) (unitVector 0)‖ + ‖A (unitVector 1) (unitVector 1)‖ + ‖A (unitVector 1) (unitVector 2)‖)
    (‖A (unitVector 2) (unitVector 0)‖ + ‖A (unitVector 2) (unitVector 1)‖ + ‖A (unitVector 2) (unitVector 2)‖)
  have e0 := sq_add_three_le ‖A (unitVector 0) (unitVector 0)‖ ‖A (unitVector 0) (unitVector 1)‖
    ‖A (unitVector 0) (unitVector 2)‖
  have e1 := sq_add_three_le ‖A (unitVector 1) (unitVector 0)‖ ‖A (unitVector 1) (unitVector 1)‖
    ‖A (unitVector 1) (unitVector 2)‖
  have e2 := sq_add_three_le ‖A (unitVector 2) (unitVector 0)‖ ‖A (unitVector 2) (unitVector 1)‖
    ‖A (unitVector 2) (unitVector 2)‖
  linarith

theorem secondDeriv_sq_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖H σ y‖ ^ 2) < ⊤ := by
  calc periodLIntegral (fun σ y => ‖H σ y‖ ^ 2)
      ≤ periodLIntegral (fun σ y => 9 * secondDerivSq (H σ y)) :=
        lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (sq_le_secondDerivSq _)
    _ = ENNReal.ofReal 9 * periodLIntegral (fun σ y => secondDerivSq (H σ y)) := by
        unfold periodLIntegral
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((PerturbationFacts.secondDeriv_bound hv).trans_lt hv.sumSecondPartials_finite)

theorem mollify_secondDeriv_tendsto {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    Tendsto (fun n => periodLIntegral (fun σ y => secondDerivSq (secondDerivField (mollify n v) σ y - H σ y)))
      atTop (𝓝 0) := by
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 9)
    (convolution_sq_tendsto (w := H) hv.measurable_secondDeriv hv.periodic_secondDeriv
      (secondDeriv_sq_lt_top hv)) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    (fun n => ?_)
  unfold periodLIntegral
  simp_rw [mollify_secondDerivField_eq hv n]
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal
        (secondDerivSq ((kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint H) (σ, y) - H σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal 9 * ENNReal.ofReal
        (‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint H) (σ, y) - H σ y‖ ^ 2) :=
        lintegral_mono fun σ => lintegral_mono fun y => by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (secondDerivSq_le_sq _)
    _ = _ := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem kernel_snd_le (n : ℕ) (t : ℝ × Space) (ht : kernel n t ≠ 0) : ‖t.2‖ ≤ 2 / ((n : ℝ) + 1) := by
  have h2 : (spaceBump n).normed volume t.2 ≠ 0 := by
    intro h0
    exact ht (by simp [kernel, h0])
  have hm : t.2 ∈ Function.support ((spaceBump n).normed volume) := h2
  rw [(spaceBump n).support_normed_eq, Metric.mem_ball, dist_zero_right] at hm
  exact hm.le

theorem weight_diff_le (y z : Space) :
    |1 / (1 + ‖y‖) - 1 / (1 + ‖y - z‖)| ≤ ‖z‖ * (1 / (1 + ‖y - z‖)) := by
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hq : 0 < 1 + ‖y - z‖ := by positivity
  have hd : |‖y - z‖ - ‖y‖| ≤ ‖z‖ := by
    have := abs_norm_sub_norm_le (y - z) y
    simpa [abs_sub_comm, norm_neg] using this
  rw [div_sub_div _ _ hp.ne' hq.ne', abs_div, abs_of_pos (mul_pos hp hq), mul_one_div]
  rw [div_le_div_iff₀ (mul_pos hp hq) hq]
  have : |1 * (1 + ‖y - z‖) - (1 + ‖y‖) * 1| = |‖y - z‖ - ‖y‖| := by ring_nf
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_right hd hq.le, mul_nonneg (norm_nonneg z) (mul_nonneg (norm_nonneg y) hq.le)]

def weightedField (v : ℝ → Space → Space) (s : ℝ) (x : Space) : Space := (1 / (1 + ‖x‖)) • v s x

theorem weightedField_locallyIntegrable {v : ℝ → Space → Space}
    (hvl : LocallyIntegrable (joint v) volume) : LocallyIntegrable (joint (weightedField v)) volume :=
  hvl.mono ((((measurable_const.div (measurable_const.add measurable_norm)).comp
      measurable_snd).aestronglyMeasurable.smul hvl.aestronglyMeasurable).congr
      (Eventually.of_forall fun z => rfl))
    (Eventually.of_forall fun z => by
      simp only [weightedField, joint, norm_smul]
      have h0 : 0 ≤ 1 / (1 + ‖z.2‖) := by positivity
      have h1 : 1 / (1 + ‖z.2‖) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [norm_nonneg z.2]
      rw [Real.norm_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1)

theorem weighted_pointwise (n : ℕ) {v : ℝ → Space → Space} (hvl : LocallyIntegrable (joint v) volume)
    (σ : ℝ) (y : Space) :
    ‖mollify n v σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 ≤
      2 * ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (weightedField v)) (σ, y)
        - weightedField v σ y‖ ^ 2 +
      2 * (2 / ((n : ℝ) + 1)) ^ 2 *
        ‖∫ t, kernel n t • joint (fun s x => ‖weightedField v s x‖) ((σ, y) - t)‖ ^ 2 := by
  have hH := volume_prod_invariantClass
  have hwl := weightedField_locallyIntegrable hvl
  set x : ℝ × Space := (σ, y) with hx
  set c : ℝ := 1 / (1 + ‖y‖) with hc
  have hc0 : 0 < c := by positivity
  have I1 : Integrable (fun t => kernel n t • joint v (x - t)) volume :=
    (kernel_hasCompactSupport n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernel_contDiff n).continuous hvl x
  have I2 : Integrable (fun t => kernel n t • joint (weightedField v) (x - t)) volume :=
    (kernel_hasCompactSupport n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernel_contDiff n).continuous hwl x
  have I3 : Integrable (fun t => c • (kernel n t • joint v (x - t))) volume := I1.smul c
  set A := (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (weightedField v)) x
    - weightedField v σ y with hA
  set D := c • mollify n v σ y - (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    joint (weightedField v)) x with hD
  have hsplit : c • (mollify n v σ y - v σ y) = A + D := by
    simp only [hA, hD, weightedField, smul_sub, ← hc]
    abel
  have hDint : D = ∫ t, (c • (kernel n t • joint v (x - t)) - kernel n t • joint (weightedField v) (x - t)) := by
    rw [integral_sub I3 I2, integral_smul, hD]
    simp only [mollify, convolution_def, ContinuousLinearMap.lsmul_apply, hx]
  set B := ∫ t, kernel n t • joint (fun s x => ‖weightedField v s x‖) (x - t) with hB
  have hbound : ‖D‖ ≤ 2 / ((n : ℝ) + 1) * B := by
    have hBint : B = ∫ t, kernel n t * ‖joint (weightedField v) (x - t)‖ := by
      simp only [hB, joint, smul_eq_mul]
    rw [hDint, hBint, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((I2.norm.const_mul (2 / ((n : ℝ) + 1))).congr
      (Eventually.of_forall fun t => by
        simp only [norm_smul, Real.norm_of_nonneg (kernel_nonneg n t)])) (Eventually.of_forall fun t => ?_)
    by_cases hk : kernel n t = 0
    · simp [hk]
    have hz := kernel_snd_le n t hk
    have hw := weight_diff_le y t.2
    have e : c • (kernel n t • joint v (x - t)) - kernel n t • joint (weightedField v) (x - t) =
        kernel n t • ((c - 1 / (1 + ‖y - t.2‖)) • joint v (x - t)) := by
      simp only [weightedField, joint, hx, Prod.fst_sub, Prod.snd_sub, sub_smul, smul_sub]
      rw [smul_comm c (kernel n t)]
    rw [e, norm_smul, norm_smul, Real.norm_of_nonneg (kernel_nonneg n t), Real.norm_eq_abs]
    have hwn : ‖joint (weightedField v) (x - t)‖ = 1 / (1 + ‖y - t.2‖) * ‖joint v (x - t)‖ := by
      simp only [weightedField, joint, hx, Prod.fst_sub, Prod.snd_sub, norm_smul]
      rw [Real.norm_of_nonneg (by positivity)]
    rw [hwn]
    have hk0 := kernel_nonneg n t
    have hv0 := norm_nonneg (joint v (x - t))
    have hq : 0 ≤ 1 / (1 + ‖y - t.2‖) := by positivity
    calc kernel n t * (|c - 1 / (1 + ‖y - t.2‖)| * ‖joint v (x - t)‖)
        ≤ kernel n t * ((‖t.2‖ * (1 / (1 + ‖y - t.2‖))) * ‖joint v (x - t)‖) := by gcongr
      _ ≤ kernel n t * ((2 / ((n : ℝ) + 1) * (1 / (1 + ‖y - t.2‖))) * ‖joint v (x - t)‖) := by gcongr
      _ = 2 / ((n : ℝ) + 1) * (kernel n t * (1 / (1 + ‖y - t.2‖) * ‖joint v (x - t)‖)) := by ring
  have hB0 : 0 ≤ B := integral_nonneg fun t => by
    simp only [joint, smul_eq_mul]
    exact mul_nonneg (kernel_nonneg n t) (norm_nonneg _)
  have hlhs : ‖mollify n v σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 = ‖A + D‖ ^ 2 := by
    rw [← hsplit, norm_smul, Real.norm_of_nonneg hc0.le, mul_pow, hc]
    field_simp
  rw [hlhs, Real.norm_of_nonneg hB0]
  have h1 := norm_add_le A D
  have hD0 := norm_nonneg D
  have hA0 := norm_nonneg A
  have hr : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  have h2 : ‖D‖ ^ 2 ≤ (2 / ((n : ℝ) + 1)) ^ 2 * B ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hD0 hbound 2
  nlinarith [sq_nonneg (‖A‖ - ‖D‖), pow_le_pow_left₀ (norm_nonneg _) h1 2]

theorem weightedField_sq_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖weightedField v σ y‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt (le_of_eq ?_) (velocity_weight_lt_top hv)
  unfold periodLIntegral
  refine lintegral_congr fun σ => lintegral_congr fun y => ?_
  congr 1
  simp only [weightedField, norm_smul]
  rw [Real.norm_of_nonneg (by positivity), mul_pow, div_pow, one_pow, mul_comm]

theorem mollify_weighted_tendsto {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖mollify n v σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2))
      atTop (𝓝 0) := by
  have hH := volume_prod_invariantClass
  have hvl : LocallyIntegrable (joint v) volume := PerturbationFacts.velocity_locallyIntegrable hv
  have hwl := weightedField_locallyIntegrable hvl
  have hwper : IsTimePeriodic (weightedField v) := fun σ y => by
    simp only [weightedField, hv.periodic_velocity σ y]
  have hW := weightedField_sq_lt_top hv
  have hnl : LocallyIntegrable (joint (fun s x => ‖weightedField v s x‖)) volume :=
    hwl.mono hwl.aestronglyMeasurable.norm (Eventually.of_forall fun z => by simp [joint])
  set W := periodLIntegral (fun σ y => ‖weightedField v σ y‖ ^ 2) with hWdef
  set E : ℕ → ℝ≥0∞ := fun n => periodLIntegral (fun σ y =>
    ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (weightedField v)) (σ, y)
      - weightedField v σ y‖ ^ 2) with hE
  have hEt : Tendsto E atTop (𝓝 0) := convolution_sq_tendsto hwl.aestronglyMeasurable hwper hW
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      simpa [div_eq_mul_inv] using this
    simpa using (h1.pow 2).const_mul 2
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2) * W + ENNReal.ofReal 2 * E n)
      atTop (𝓝 0) := by
    have a1 := ENNReal.Tendsto.mul_const hr (Or.inr hW.ne)
    have a2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 2) hEt (Or.inr ENNReal.ofReal_ne_top)
    simpa using a1.add a2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    (fun n => ?_)
  set b := kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (fun s x => ‖weightedField v s x‖)
    with hb
  have hbc : Continuous b :=
    ((kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hnl).continuous
  have hbm : Measurable (fun z : ℝ × Space =>
      ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2 * ‖b z‖ ^ 2)) :=
    (continuous_const.mul (hbc.norm.pow 2)).measurable.ennreal_ofReal
  have hbint : ∀ σ y, ∫ t, kernel n t • joint (fun s x => ‖weightedField v s x‖) ((σ, y) - t) =
      b (σ, y) := fun σ y => by
    simp only [hb, convolution_def, ContinuousLinearMap.lsmul_apply]
  have hF : periodLIntegral (fun σ y => ‖b (σ, y)‖ ^ 2) ≤ W := by
    have := period_convolution_sq_le (kernel_contDiff n).continuous (kernel_hasCompactSupport n)
      (w := fun s x => ‖weightedField v s x‖) hwl.aestronglyMeasurable.norm
      (fun σ y => by simp only [hwper σ y])
    rw [lintegral_kernel_eq_one, one_pow, one_mul] at this
    simp only [hbint, norm_norm] at this
    exact this
  calc periodLIntegral (fun σ y => ‖mollify n v σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          (ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2 * ‖b (σ, y)‖ ^ 2) +
            ENNReal.ofReal 2 * ENNReal.ofReal
              (‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (weightedField v)) (σ, y)
                - weightedField v σ y‖ ^ 2)) := by
        refine lintegral_mono fun σ => lintegral_mono fun y => ?_
        have hp := weighted_pointwise n hvl σ y
        rw [hbint] at hp
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal (hp.trans (le_of_eq ?_))
        ring
    _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2 * ‖b (σ, y)‖ ^ 2))
          + ENNReal.ofReal 2 * ∫⁻ y, ENNReal.ofReal
              (‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint (weightedField v)) (σ, y)
                - weightedField v σ y‖ ^ 2)) := by
        refine lintegral_congr fun σ => ?_
        rw [lintegral_add_left (f := fun y => ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2 * ‖b (σ, y)‖ ^ 2))
          (hbm.comp measurable_prodMk_left), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2) * periodLIntegral (fun σ y => ‖b (σ, y)‖ ^ 2)
          + ENNReal.ofReal 2 * E n := by
        rw [lintegral_add_left (f := fun σ => ∫⁻ y,
            ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2 * ‖b (σ, y)‖ ^ 2))
          (hbm.lintegral_prod_right' (ν := (volume : Measure Space))),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        unfold periodLIntegral
        simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (2 / ((n : ℝ) + 1)) ^ 2)]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * (2 / ((n : ℝ) + 1)) ^ 2) * W + ENNReal.ofReal 2 * E n := by
        gcongr

theorem mollify_transport_tendsto {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖transportPart P (mollify n v) σ y - g σ y‖ ^ 2))
      atTop (𝓝 0) :=
  transport_tendsto_of_eq hv (mollify_transportPart_eq hv)

end Internal.SmoothApprox

end Coercive

end Breakdown
