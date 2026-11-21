import Breakdown.Frac.TorusApproxSizesAux
import Breakdown.Frac.PSlice
import Breakdown.Frac.TorusResidual
import Breakdown.Torus.TestLift

open MeasureTheory Set Real Filter Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusApproxSizes.Internal

open FracResidualCombine.Internal

def nearIdx (x : Space) : Lattice := fun i => -round (x i - 1 / 2)

theorem freq_coord (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem center_coord (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem coord_le (v w : Space) (j : Fin 3) : |v j - w j| ≤ dist v w := by
  rw [dist_eq_norm]
  have := PiLp.norm_apply_le (v - w) j
  rwa [Real.norm_eq_abs, PiLp.sub_apply] at this

theorem wrap_eq (x : Space) : wrap x = x + freq (nearIdx x) := by
  have e : wrap x = x - freq (fun i => round (x i - center i)) := rfl
  rw [e]
  ext i
  rw [PiLp.sub_apply, PiLp.add_apply, freq_coord, freq_coord, center_coord]
  simp only [nearIdx]
  push_cast
  ring

theorem periodize_wrap {f : Space → Space} (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    latticePeriodize f x = f (wrap x) := by
  rw [wrap_eq]
  unfold latticePeriodize
  refine tsum_eq_single (nearIdx x) fun j hj => ?_
  by_contra h
  apply hj
  funext i
  have a1 := (coord_le _ _ i).trans (hf _ h)
  rw [PiLp.add_apply, freq_coord, center_coord] at a1
  have a3 := abs_sub_round (x i - 1 / 2)
  rw [abs_le] at a1 a3
  have key : |((j i + round (x i - 1 / 2) : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a3.1, a3.2]
  have h' : |j i + round (x i - 1 / 2)| < 1 := by exact_mod_cast key
  have := abs_lt.mp h'
  simp only [nearIdx]
  omega

variable {α a T t : ℝ} {U : Space → Space} {P : Space → ℝ}

theorem field_contDiff (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) : ContDiff ℝ ∞ (fracApproxField α a U T t) := by
  have h := (hA a U P hU T hT).1
  rw [contDiff_iff_contDiffAt]
  intro x
  have hm : ((t, x) : ℝ × Space) ∈ Iio T ×ˢ (univ : Set Space) := ⟨ht, trivial⟩
  have h1 := h.contDiffAt ((isOpen_Iio.prod isOpen_univ).mem_nhds hm)
  have h2 : ContDiffAt ℝ ∞ (fun y : Space => ((t, y) : ℝ × Space)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h1.comp x h2

theorem field_support (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) (v : Space) (hv : fracApproxField α a U T t v ≠ 0) :
    dist v center ≤ 1 / 8 := by
  by_contra hlt
  push Not at hlt
  apply hv
  have hd : centralRadius / 2 ≤ dist v center := by rw [centralRadius]; linarith
  exact (((hA a U P hU T hT).2.2 t ht v).2.1 hd).1

theorem fderiv_rescale_apply {F : Space → Space} (hF : Differentiable ℝ F) (c σ : ℝ) (y v : Space) :
    fderiv ℝ (fun y => c • F (center + σ • y)) y v = (c * σ) • fderiv ℝ F (center + σ • y) v := by
  have h1 : HasFDerivAt (fun y : Space => center + σ • y) (σ • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul σ).const_add center
  have h2 : HasFDerivAt (fun y => c • F (center + σ • y))
      (c • ((fderiv ℝ F (center + σ • y)).comp (σ • ContinuousLinearMap.id ℝ Space))) y :=
    ((hF _).hasFDerivAt.comp y h1).const_smul c
  rw [h2.fderiv]
  simp [smul_smul]

theorem rescale_div {F : Space → Space} (hF : Differentiable ℝ F) (hdiv : ∀ x, divergenceAt F x = 0)
    (c σ : ℝ) (y : Space) : divergenceAt (fun y => c • F (center + σ • y)) y = 0 := by
  have h := hdiv (center + σ • y)
  simp only [divergenceAt] at h ⊢
  simp only [fderiv_rescale_apply hF, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h, mul_zero]

theorem sqrt_scale {ℓ : ℝ} (hℓ : 0 < ℓ) : Real.sqrt (ℓ ^ (1 / α)) = ℓ ^ (1 / (2 * α)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hℓ.le]
  congr 1
  ring

theorem scalar_one {ℓ : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) :
    ℓ ^ (-(1 - 1 / α)) * ((ℓ ^ (1 / (2 * α)))⁻¹ * ℓ ^ (1 - 1 / (2 * α))) = 1 := by
  rw [← Real.rpow_neg hℓ.le, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
  have e : -(1 - 1 / α) + (-(1 / (2 * α)) + (1 - 1 / (2 * α))) = 0 := by
    field_simp
    ring
  rw [e, Real.rpow_zero]

theorem periodic_eq (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hα : 0 < α) (hT : 0 < T) (ht : t < T) :
    latticePeriodize (fracApproxField α a U T t) =
      ((T - t) ^ (-(1 - 1 / α))) • transplantField ((T - t) ^ (1 / α)) (fracCut α a U T t) := by
  have hℓ : 0 < T - t := by linarith
  funext x
  rw [periodize_wrap (field_support hA hU hT ht) x]
  simp only [Pi.smul_apply, transplantField, simCoord, fracCut, sqrt_scale hℓ, smul_smul]
  have hσ : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hℓ _
  rw [mul_inv_cancel₀ hσ.ne', one_smul, add_sub_cancel, scalar_one hℓ hα, one_smul]

theorem coef_eq {μ ℓ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) (hα : 0 < α) :
    μ ^ dilExponent α * ℓ ^ (-(1 - 1 / α)) / (ℓ ^ (1 / α)) ^ (1 / 4 : ℝ) = (μ / ℓ) ^ dilExponent α := by
  have e : ℓ ^ (-(1 - 1 / α)) / (ℓ ^ (1 / α)) ^ (1 / 4 : ℝ) = (ℓ ^ dilExponent α)⁻¹ := by
    rw [← Real.rpow_mul hℓ.le, ← Real.rpow_sub hℓ, ← Real.rpow_neg hℓ.le]
    congr 1
    unfold dilExponent
    field_simp
    ring
  rw [mul_div_assoc, e, Real.div_rpow hμ.le hℓ.le, div_eq_mul_inv]

theorem grad_sum_le (f : Space → Space) (y : Space) :
    ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2 ≤ 3 * ‖fderiv ℝ f y‖ ^ 2 := by
  have h : ∀ i, ‖fderiv ℝ f y (unitVector i)‖ ≤ ‖fderiv ℝ f y‖ := fun i => by
    have := (fderiv ℝ f y).le_opNorm (unitVector i)
    rwa [show ‖unitVector i‖ = 1 by simp [unitVector], mul_one] at this
  calc ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖fderiv ℝ f y‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = 3 * ‖fderiv ℝ f y‖ ^ 2 := by simp

theorem slice_grad_bound (hα : 1 < α) (hU : IsRotatingProfile α a 1 U P) :
    ∃ B : ℝ, ∀ s, gradEnergy (rotatingSlice a U s) ≤ B := by
  obtain ⟨C, hC⟩ := FracInternal.SliceBounds.slice_bounds hα hU
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine ⟨3 * C ^ 2 * ∫ y : Space, (1 + ‖y‖) ^ (-(4 : ℝ)), fun s => ?_⟩
  unfold gradEnergy
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) (hint.const_mul _)
    (Eventually.of_forall fun y => ?_)
  have h1 := grad_sum_le (rotatingSlice a U s) y
  have h2 := (hC s y).2
  have hp : 0 < 1 + ‖y‖ := by positivity
  have e : (C / (1 + ‖y‖) ^ 2) ^ 2 = C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg hp.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have h3 : ‖fderiv ℝ (rotatingSlice a U s) y‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  show ∑ i : Fin 3, ‖fderiv ℝ (rotatingSlice a U s) y (unitVector i)‖ ^ 2 ≤
    3 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))
  nlinarith


theorem sq_pow_rpow (r x : ℝ) (hr : 0 ≤ r) : (r ^ x) ^ 2 = r ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

theorem sq_mass_bound {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) (hF : FracApproxFieldProperties α)
    (hD : FracSelfSimilarDecay α) {a : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hP : IsRotatingProfile α a 1 U P) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T →
      ∫ y, ‖fracApproxField α a U T t y‖ ^ 2 ≤ L := by
  obtain ⟨C, hC⟩ := hD a U P hP
  obtain ⟨G, hG0, hG⟩ := ApproxSizes.Internal.centralCut_bounds
  set β := 2 * α - 1 with hβ
  set Ks := ∫ s in Ioc (0 : ℝ) 1, s ^ (1 - β) with hKs
  have hKs0 : 0 ≤ Ks := setIntegral_nonneg measurableSet_Ioc fun s hs => Real.rpow_nonneg hs.1.le _
  set B := G * (|C| * Ks) with hB
  set h : Space → ℝ := fun z => 2 * |C| ^ 2 * ‖z‖ ^ (-(2 * β)) + 2 * B ^ 2 * ‖z‖ ^ (2 * (1 - β)) with hh
  have hh0 : ∀ z, 0 ≤ h z := fun z => by
    simp only [hh]
    have := Real.rpow_nonneg (norm_nonneg z) (-(2 * β))
    have := Real.rpow_nonneg (norm_nonneg z) (2 * (1 - β))
    positivity
  have hhi : IntegrableOn h (ball (0 : Space) 1) :=
    ((FracInternal.integrableOn_ball_norm_rpow (s := -(2 * β)) (by linarith)).const_mul _).add
      ((FracInternal.integrableOn_ball_norm_rpow (s := 2 * (1 - β)) (by linarith)).const_mul _)
  have hgi : Integrable (fun y : Space => (ball (0 : Space) 1).indicator h (y - center)) :=
    (hhi.integrable_indicator measurableSet_ball).comp_sub_right center
  refine ⟨∫ y, (ball (0 : Space) 1).indicator h (y - center),
    integral_nonneg fun y => indicator_nonneg (fun z _ => hh0 z) _, fun T t hT hT1 ht htT => ?_⟩
  have hne : ∀ᵐ y : Space ∂volume, y ≠ center := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure Space)) center
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hgi ?_
  filter_upwards [hne] with y hy
  have hy0 : 0 < ‖y - center‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hvan := ((hF a U P hP T hT).2.2 t htT y).2.1
  rcases le_or_gt (centralRadius / 2) (dist y center) with hd | hd
  · rw [(hvan hd).1, norm_zero]
    simpa using indicator_nonneg (fun z _ => hh0 z) (y - center)
  · have hmem : y - center ∈ ball (0 : Space) 1 := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      have : centralRadius / 2 < 1 := by norm_num [centralRadius]
      linarith
    rw [indicator_of_mem hmem]
    have hg : ∀ z, 0 < ‖z - center‖ → ‖fracSelfSimilar α a U T t z‖ ≤ |C| * ‖z - center‖ ^ (-β) :=
      fun z hz => self_similar_point hC h1 hT hT1 ht htT hz
    have hp := field_point (by linarith) hg hG0 hG hy0
    have hp' : ‖fracApproxField α a U T t y‖ ≤
        |C| * ‖y - center‖ ^ (-β) + B * ‖y - center‖ ^ (1 - β) := by
      simp only [hB, fracApproxField]
      linarith
    have hq := pow_le_pow_left₀ (norm_nonneg _) hp' 2
    have e1 := sq_pow_rpow ‖y - center‖ (-β) (norm_nonneg _)
    have e2 := sq_pow_rpow ‖y - center‖ (1 - β) (norm_nonneg _)
    simp only [hh]
    rw [show 2 * -β = -(2 * β) by ring] at e1
    have u0 := Real.rpow_nonneg (norm_nonneg (y - center)) (-β)
    have vfix := Real.rpow_nonneg (norm_nonneg (y - center)) (1 - β)
    have hab : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := fun u v => by nlinarith [sq_nonneg (u - v)]
    have := hab (|C| * ‖y - center‖ ^ (-β)) (B * ‖y - center‖ ^ (1 - β))
    rw [mul_pow, mul_pow, e1, e2] at this
    linarith


theorem scalar_le (hα : 1 < α) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ℓ ^ (1 / α) * ((ℓ ^ (1 - 1 / (2 * α))) ^ 2 * ((ℓ ^ (1 / (2 * α))) ^ 3)⁻¹) ≤ 1 := by
  have e : ℓ ^ (1 / α) * ((ℓ ^ (1 - 1 / (2 * α))) ^ 2 * ((ℓ ^ (1 / (2 * α))) ^ 3)⁻¹) =
      ℓ ^ (2 - 3 / (2 * α)) := by
    rw [← Real.rpow_natCast (ℓ ^ (1 - 1 / (2 * α))), ← Real.rpow_mul hℓ.le,
      ← Real.rpow_natCast (ℓ ^ (1 / (2 * α))), ← Real.rpow_mul hℓ.le, ← Real.rpow_neg hℓ.le,
      ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
    congr 1
    push_cast
    field_simp
    ring
  rw [e]
  refine Real.rpow_le_one hℓ.le hℓ1 ?_
  rw [sub_nonneg, div_le_iff₀ (by linarith)]
  linarith

theorem cut_mass (hα : 1 < α) (ht : t < T) (hℓ1 : T - t ≤ 1) :
    (T - t) ^ (1 / α) * ∫ y, ‖fracCut α a U T t y‖ ^ 2 ≤ ∫ x, ‖fracApproxField α a U T t x‖ ^ 2 := by
  have hℓ : 0 < T - t := by linarith
  have hσ0 : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hℓ _
  have e1 : ∫ y, ‖fracCut α a U T t y‖ ^ 2 = ((T - t) ^ (1 - 1 / (2 * α))) ^ 2 *
      ∫ y, ‖fracApproxField α a U T t (center + (T - t) ^ (1 / (2 * α)) • y)‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [fracCut, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have e2 : ∫ y, ‖fracApproxField α a U T t (center + (T - t) ^ (1 / (2 * α)) • y)‖ ^ 2 =
      |(((T - t) ^ (1 / (2 * α))) ^ 3)⁻¹| * ∫ x, ‖fracApproxField α a U T t (center + x)‖ ^ 2 := by
    have := Measure.integral_comp_smul (μ := (volume : Measure Space))
      (fun x => ‖fracApproxField α a U T t (center + x)‖ ^ 2) ((T - t) ^ (1 / (2 * α)))
    rw [finrank_euclideanSpace_fin, smul_eq_mul] at this
    exact this
  have e3 : ∫ x, ‖fracApproxField α a U T t (center + x)‖ ^ 2 = ∫ x, ‖fracApproxField α a U T t x‖ ^ 2 :=
    integral_add_left_eq_self (fun x => ‖fracApproxField α a U T t x‖ ^ 2) center
  have hI : 0 ≤ ∫ x, ‖fracApproxField α a U T t x‖ ^ 2 := integral_nonneg fun x => by positivity
  rw [e1, e2, e3, abs_of_pos (by positivity)]
  have hs := scalar_le hα hℓ hℓ1
  calc (T - t) ^ (1 / α) * (((T - t) ^ (1 - 1 / (2 * α))) ^ 2 *
        ((((T - t) ^ (1 / (2 * α))) ^ 3)⁻¹ * ∫ x, ‖fracApproxField α a U T t x‖ ^ 2))
      = ((T - t) ^ (1 / α) * (((T - t) ^ (1 - 1 / (2 * α))) ^ 2 * (((T - t) ^ (1 / (2 * α))) ^ 3)⁻¹)) *
          ∫ x, ‖fracApproxField α a U T t x‖ ^ 2 := by ring
    _ ≤ 1 * ∫ x, ‖fracApproxField α a U T t x‖ ^ 2 := mul_le_mul_of_nonneg_right hs hI
    _ = _ := one_mul _

theorem core_eq (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) {y : Space} (hy : (T - t) ^ (1 / (2 * α)) * ‖y‖ ≤ centralRadius / 4) :
    fracCut α a U T t y = rotatingSlice a U (similarityTime T t) y := by
  have hℓ : 0 < T - t := by linarith
  have hσ : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hℓ _
  have hd : dist (center + (T - t) ^ (1 / (2 * α)) • y) center ≤ centralRadius / 4 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact hy
  simp only [fracCut]
  rw [((hA a U P hU T hT).2.2 t ht _).2.2 hd]
  simp only [fracSelfSimilar, add_sub_cancel_left, smul_smul]
  rw [← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
  have e1 : 1 - 1 / (2 * α) + -(1 - 1 / (2 * α)) = 0 := by ring
  have e2 : -(1 / (2 * α)) + 1 / (2 * α) = 0 := by ring
  rw [e1, e2, Real.rpow_zero, one_smul, one_smul]

set_option maxHeartbeats 1600000 in
theorem cut_close (hα : 1 < α) (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hGB : FracShellGradientBound α) :
    ∀ ε : ℝ, 0 < ε → ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → T - t < ℓ₀ →
      gradEnergy (rotatingSlice a U (similarityTime T t) - fracCut α a U T t) ≤ ε := by
  intro ε hε
  obtain ⟨C, hC⟩ := FracInternal.SliceBounds.slice_bounds hα hU
  obtain ⟨G, hG⟩ := hGB a U P hU
  have hα0 : 0 < α := by linarith
  set g := 1 / (2 * α) with hg
  have hg0 : 0 < g := by positivity
  have hg3 : 0 < 2 - 3 * g := by
    rw [hg, sub_pos, ← mul_div_assoc, mul_one, div_lt_iff₀ (by positivity)]
    linarith
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  set I := ∫ y : Space, (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) with hI
  set V := (volume : Measure Space).real (closedBall (0 : Space) 1) with hV
  set G' := max G 0 with hG'
  set A₁ := 6 * C ^ 2 * 4 * I with hA₁
  set A₂ := V * 6 * G' ^ 2 / 512 with hA₂
  have hcont : ContinuousAt (fun ℓ : ℝ => A₁ * ℓ ^ (g / 2) + A₂ * ℓ ^ (2 - 3 * g)) 0 :=
    ((Real.continuousAt_rpow_const 0 _ (Or.inr (by positivity))).const_mul _).add
      ((Real.continuousAt_rpow_const 0 _ (Or.inr hg3.le)).const_mul _)
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hcont ε hε
  refine ⟨δ, hδ, fun T t hT hT1 ht0 ht hℓδ => ?_⟩
  have hℓ : 0 < T - t := by linarith
  have hf := hδf (x := T - t) (by rw [Real.dist_eq, sub_zero, abs_of_pos hℓ]; exact hℓδ)
  rw [Real.zero_rpow (by positivity), Real.zero_rpow hg3.ne', mul_zero, mul_zero, add_zero,
    Real.dist_eq, sub_zero] at hf
  have hf' := (le_abs_self _).trans hf.le
  set ℓ := T - t with hℓdef
  set σ := ℓ ^ g with hσdef
  have hσ : 0 < σ := Real.rpow_pos_of_pos hℓ _
  set F := fracApproxField α a U T t with hFdef
  have hFs : ContDiff ℝ ∞ F := field_contDiff hA hU hT ht
  have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
  set S := rotatingSlice a U (similarityTime T t) with hSdef
  have hSdec := FracInternal.SliceBounds.slice_decayField hα hU (similarityTime T t)
  have hSd : Differentiable ℝ S := hSdec.1.differentiable (by simp)
  have hhe : fracCut α a U T t = fun y => ℓ ^ (1 - g) • F (center + σ • y) := rfl
  have hhd : Differentiable ℝ (fracCut α a U T t) := by
    rw [hhe]
    exact ((hFs.comp (contDiff_const.add (contDiff_id.const_smul _))).const_smul _).differentiable (by simp)
  have hcσ : ℓ ^ (1 - g) * σ = ℓ := by
    rw [hσdef, ← Real.rpow_add hℓ, sub_add_cancel, Real.rpow_one]
  set ρ := 1 / (16 * σ) with hρ
  set Φ : Space → ℝ := fun y => 6 * C ^ 2 * (4 * Real.sqrt σ) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) +
    (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => 6 * ℓ ^ 2 * G' ^ 2) y with hΦ
  have hΦi : Integrable Φ :=
    (hint.const_mul _).add ((continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : Space) _)).integrable_indicator measurableSet_closedBall)
  have hpt : ∀ y, ∑ i : Fin 3, ‖fderiv ℝ (S - fracCut α a U T t) y (unitVector i)‖ ^ 2 ≤ Φ y := by
    intro y
    have hΦ0 : 0 ≤ Φ y := by
      simp only [hΦ]
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) (-(7 / 2 : ℝ))
      have : 0 ≤ (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => 6 * ℓ ^ 2 * G' ^ 2) y :=
        indicator_nonneg (fun _ _ => by positivity) _
      positivity
    rcases lt_or_ge ‖y‖ ρ with hy | hy
    · have hev : (S - fracCut α a U T t) =ᶠ[nhds y] fun _ => 0 := by
        have hmem : ball (0 : Space) ρ ∈ nhds y := Metric.isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
        filter_upwards [hmem] with z hz
        rw [mem_ball_zero_iff] at hz
        rw [Pi.sub_apply, core_eq hA hU hT ht, sub_self]
        rw [hρ, lt_div_iff₀ (by positivity)] at hz
        rw [centralRadius]
        have e : σ * ‖z‖ * 16 = ‖z‖ * (16 * σ) := by ring
        show σ * ‖z‖ ≤ 1 / 4 / 4
        linarith
      rw [hev.fderiv_eq]
      simpa using hΦ0
    · have hsub : fderiv ℝ (S - fracCut α a U T t) y = fderiv ℝ S y - fderiv ℝ (fracCut α a U T t) y :=
        fderiv_sub (hSd y) (hhd y)
      have h1 := grad_sum_le (S - fracCut α a U T t) y
      have hDs := ((hC (similarityTime T t) y).2)
      have hDh : ‖fderiv ℝ (fracCut α a U T t) y‖ ≤ ℓ * ‖fderiv ℝ F (center + σ • y)‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [hhe, fderiv_rescale_apply hFd, norm_smul, Real.norm_eq_abs, hcσ, abs_of_pos hℓ, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((fderiv ℝ F _).le_opNorm v) hℓ.le
      have hdist : dist (center + σ • y) center = σ * ‖y‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
      have hDF : ‖fderiv ℝ F (center + σ • y)‖ ^ 2 ≤
          (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => G' ^ 2) y := by
        by_cases hb : y ∈ closedBall (0 : Space) (1 / (8 * σ))
        · rw [indicator_of_mem hb]
          refine pow_le_pow_left₀ (norm_nonneg _) ((hG T t hT hT1 ht0 ht _ ?_).trans (le_max_left _ _)) 2
          rw [hdist, centralRadius]
          rw [hρ, div_le_iff₀ (by positivity)] at hy
          have e : σ * ‖y‖ * 16 = ‖y‖ * (16 * σ) := by ring
          linarith
        · rw [indicator_of_notMem hb]
          rw [mem_closedBall_zero_iff, not_le, div_lt_iff₀ (by positivity)] at hb
          have hev : F =ᶠ[nhds (center + σ • y)] fun _ => 0 := by
            have hopen : IsOpen {z : Space | 1 / 8 < dist z center} :=
              isOpen_lt continuous_const (continuous_id.dist continuous_const)
            filter_upwards [hopen.mem_nhds (show 1 / 8 < dist (center + σ • y) center by
              rw [hdist]; linarith)] with z hz
            exact (((hA a U P hU T hT).2.2 t ht z).2.1 (by rw [centralRadius]; linarith)).1
          rw [hev.fderiv_eq]
          simp
      have hDh2 : ‖fderiv ℝ (fracCut α a U T t) y‖ ^ 2 ≤
          (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => ℓ ^ 2 * G' ^ 2) y := by
        have := pow_le_pow_left₀ (norm_nonneg _) hDh 2
        rw [mul_pow] at this
        have e : (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => ℓ ^ 2 * G' ^ 2) y =
            ℓ ^ 2 * (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => G' ^ 2) y := by
          by_cases hb : y ∈ closedBall (0 : Space) (1 / (8 * σ))
          · rw [indicator_of_mem hb, indicator_of_mem hb]
          · rw [indicator_of_notMem hb, indicator_of_notMem hb, mul_zero]
        rw [e]
        exact this.trans (mul_le_mul_of_nonneg_left hDF (by positivity))
      have hp : 0 < 1 + ‖y‖ := by positivity
      have hDs2 : ‖fderiv ℝ S y‖ ^ 2 ≤ C ^ 2 * (4 * Real.sqrt σ) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) := by
        have h2 := pow_le_pow_left₀ (norm_nonneg _) hDs 2
        have e : (C / (1 + ‖y‖) ^ 2) ^ 2 = C ^ 2 * ((1 + ‖y‖) ^ (-(1 / 2 : ℝ)) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) := by
          rw [← Real.rpow_add hp, show -(1 / 2 : ℝ) + -(7 / 2) = -((4 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg hp.le, Real.rpow_natCast]
          field_simp
        have hq : (1 + ‖y‖) ^ (-(1 / 2 : ℝ)) ≤ 4 * Real.sqrt σ := by
          rw [Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 hp),
            mul_assoc, ← Real.sqrt_mul hσ.le]
          have : 1 / 16 ≤ σ * (1 + ‖y‖) := by
            rw [hρ, div_le_iff₀ (by positivity)] at hy
            have e : σ * ‖y‖ * 16 = ‖y‖ * (16 * σ) := by ring
            nlinarith [hσ.le]
          have h4 : (1 / 4 : ℝ) ≤ Real.sqrt (σ * (1 + ‖y‖)) := by
            rw [Real.le_sqrt (by norm_num) (by positivity)]
            linarith
          linarith
        rw [e] at h2
        have := Real.rpow_nonneg hp.le (-(7 / 2 : ℝ))
        calc ‖fderiv ℝ S y‖ ^ 2 ≤ C ^ 2 * ((1 + ‖y‖) ^ (-(1 / 2 : ℝ)) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) := h2
          _ ≤ C ^ 2 * ((4 * Real.sqrt σ) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) := by gcongr
          _ = _ := by ring
      rw [hsub] at h1 ⊢
      have htri := norm_sub_le (fderiv ℝ S y) (fderiv ℝ (fracCut α a U T t) y)
      have hab : ‖fderiv ℝ S y - fderiv ℝ (fracCut α a U T t) y‖ ^ 2 ≤
          2 * ‖fderiv ℝ S y‖ ^ 2 + 2 * ‖fderiv ℝ (fracCut α a U T t) y‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖fderiv ℝ S y‖ - ‖fderiv ℝ (fracCut α a U T t) y‖)]
      have e3 : (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => 6 * ℓ ^ 2 * G' ^ 2) y =
          6 * (closedBall (0 : Space) (1 / (8 * σ))).indicator (fun _ => ℓ ^ 2 * G' ^ 2) y := by
        by_cases hb : y ∈ closedBall (0 : Space) (1 / (8 * σ))
        · rw [indicator_of_mem hb, indicator_of_mem hb]; ring
        · rw [indicator_of_notMem hb, indicator_of_notMem hb, mul_zero]
      simp only [hΦ, e3]
      nlinarith
  have hE : gradEnergy (S - fracCut α a U T t) ≤ ∫ y, Φ y :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hΦi
      (Filter.Eventually.of_forall hpt)
  have hIΦ : ∫ y, Φ y = A₁ * ℓ ^ (g / 2) + A₂ * ℓ ^ (2 - 3 * g) := by
    simp only [hΦ]
    rw [integral_add (hint.const_mul _) ((continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : Space) _)).integrable_indicator measurableSet_closedBall),
      integral_const_mul, integral_indicator_const _ measurableSet_closedBall,
      Measure.addHaar_real_closedBall' _ _ (by positivity), finrank_euclideanSpace_fin, smul_eq_mul]
    have e1 : Real.sqrt σ = ℓ ^ (g / 2) := by
      rw [hσdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hℓ.le]
      ring_nf
    have e2 : ℓ ^ 2 / σ ^ 3 = ℓ ^ (2 - 3 * g) := by
      rw [hσdef, ← Real.rpow_natCast (ℓ ^ g), ← Real.rpow_mul hℓ.le, ← Real.rpow_natCast ℓ 2,
        ← Real.rpow_sub hℓ]
      congr 1
      push_cast
      ring
    rw [← e1, ← e2, hA₁, hA₂, ← hI, ← hV]
    field_simp
    ring
  linarith

end TorusApproxSizes.Internal

set_option maxHeartbeats 1600000 in
open TorusApproxSizes.Internal in
theorem fracApproxSizes (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hN : TransplantNorm)
    (hA : FracApproxFieldProperties α) (hL : FracApproxLinks α) (hSD : FracSelfSimilarDecay α) :
    FracApproxSizes α := by
  intro a U P lam c hU hl hl1 hc hcU
  obtain ⟨B, hB⟩ := slice_grad_bound hα hU
  obtain ⟨K, hK0, hKb⟩ := sq_mass_bound hα hα2 hA hSD hU
  have hK : ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T →
      (T - t) ^ (1 / α) * ∫ y, ‖fracCut α a U T t y‖ ^ 2 ≤ K := fun T t hT hT1 ht0 ht =>
    (cut_mass hα ht (by linarith)).trans (hKb T t hT hT1 ht0 ht)
  have hclose := cut_close hα hA hU (fracShellGradientBound α hα hα2 hA hSD)
  obtain ⟨ℓ₀, hℓ₀, hℓ⟩ := hclose ((c / 2) ^ 2) (by positivity)
  have hα0 : 0 < α := by linarith
  have hκ : 0 ≤ dilExponent α := by
    unfold dilExponent
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hE := Freq.embedNormLinear_holds.1
  have hEL := Freq.embedNormLinear_holds.2
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ = Real.sqrt ((Real.sqrt (max B 0) + c / 2) ^ 2 + |K|) := ⟨_, rfl⟩
  refine ⟨min ℓ₀ 1, (lam ^ dilExponent α)⁻¹ * M₀, lt_min hℓ₀ one_pos, fun T hT hT0 n => ?_⟩
  have hT1 : T ≤ 1 := (hT0.trans_le (min_le_right _ _)).le
  have hTℓ : T < ℓ₀ := hT0.trans_le (min_le_left _ _)
  have key : ∀ s : Icc (0 : ℝ) (1 - lam), c / 2 ≤ ‖fracApproxPiece α a U T lam n s‖ ∧
      ‖fracApproxPiece α a U T lam n s‖ ≤ (lam ^ dilExponent α)⁻¹ * M₀ := by
    intro s
    obtain ⟨s, hs0, hs1⟩ := s
    rw [(hL a U P T lam hU hT hT1 hl hl1 n).1 ⟨s, hs0, hs1⟩]
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = stepScale T lam n := ⟨_, rfl⟩
    have hμ : 0 < μ := hμdef ▸ stepScale_pos hT hl n
    have hμT : μ ≤ T := by
      rw [hμdef, stepScale]
      exact mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
    have hst : stepStart T lam n = T - μ := by rw [hμdef]; rfl
    simp only [← hμdef, hst]
    obtain ⟨t, htdef⟩ : ∃ t, t = T - μ + μ * s := ⟨_, rfl⟩
    rw [← htdef]
    have hℓe : T - t = μ * (1 - s) := by rw [htdef]; ring
    have hℓpos : 0 < T - t := by rw [hℓe]; exact mul_pos hμ (by linarith)
    have ht : t < T := by linarith
    have ht0 : 0 ≤ t := by rw [htdef]; nlinarith
    have hℓμ : T - t ≤ μ := by rw [hℓe]; nlinarith
    have hlamℓ : μ * lam ≤ T - t := by rw [hℓe]; nlinarith
    have hℓ1 : T - t ≤ 1 := by linarith
    have hℓ0 : T - t < ℓ₀ := by linarith
    set ℓ := T - t with hℓdef
    set h := fracCut α a U T t with hhdef
    set μ' := ℓ ^ (1 / α) with hμ'def
    have hμ'pos : 0 < μ' := Real.rpow_pos_of_pos hℓpos _
    have hμ'1 : μ' ≤ 1 := Real.rpow_le_one hℓpos.le hℓ1 (by positivity)
    have hσ : Real.sqrt μ' = ℓ ^ (1 / (2 * α)) := sqrt_scale hℓpos
    have hσpos : 0 < Real.sqrt μ' := Real.sqrt_pos.2 hμ'pos
    have hF := field_contDiff hA hU hT ht
    have hFd : Differentiable ℝ (fracApproxField α a U T t) := hF.differentiable (by simp)
    have hhe : h = fun y => ℓ ^ (1 - 1 / (2 * α)) • fracApproxField α a U T t (center + ℓ ^ (1 / (2 * α)) • y) := rfl
    have hs : ContDiff ℝ ∞ h := by
      rw [hhe]
      exact (hF.comp (contDiff_const.add (contDiff_id.const_smul _))).const_smul _
    have hd : ∀ y, divergenceAt h y = 0 := by
      rw [hhe]
      exact rescale_div hFd (fun x => ((hA a U P hU T hT).2.2 t ht x).1) _ _
    obtain ⟨b, hbdef⟩ : ∃ b, b = 1 / (8 * Real.sqrt μ') := ⟨_, rfl⟩
    have hbpos : 0 < b := by rw [hbdef]; positivity
    have hsh : IsShellScale μ' b := ⟨hμ'pos, hμ'1, hbpos, le_of_eq (by rw [hbdef]; field_simp)⟩
    have hsupp : tsupport h ⊆ Metric.closedBall 0 b := by
      apply closure_minimal _ Metric.isClosed_closedBall
      intro y hy
      rw [Function.mem_support] at hy
      rw [Metric.mem_closedBall, dist_zero_right]
      have hne : fracApproxField α a U T t (center + ℓ ^ (1 / (2 * α)) • y) ≠ 0 := by
        intro h0
        apply hy
        rw [hhe]
        simp only [h0, smul_zero]
      have h1 := field_support hA hU hT ht _ hne
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← hσ, abs_of_pos hσpos] at h1
      rw [hbdef, le_div_iff₀ (by positivity)]
      nlinarith
    have hn := hN h μ' b hs hd hsh hsupp
    have hdec : IsDecayField h := ApproxSizes.Internal.decay_of_support hs hd hbpos.le hsupp
    have hsl := (rotatingSliceDecay α hα hα2 a U P hU (similarityTime T t)).1
    have hnorm := hE h hdec
    have hgap := hE _ (ApproxSizes.Internal.decay_sub hsl hdec)
    rw [hEL.2.1 _ _ hsl hdec] at hgap
    have hclose' := hℓ T t hT hT1 ht0 ht hℓ0
    have hgapn : ‖Freq.embedX (rotatingSlice a U (similarityTime T t)) - Freq.embedX h‖ ≤ c / 2 := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [hgap]
      exact hclose'
    have hsln := hE _ hsl
    have hslB : ‖Freq.embedX (rotatingSlice a U (similarityTime T t))‖ ≤ Real.sqrt (max B 0) := by
      rw [← Real.sqrt_sq (norm_nonneg _), hsln]
      exact Real.sqrt_le_sqrt ((hB _).trans (le_max_left _ _))
    have hslc := hcU (similarityTime T t)
    have htri := norm_sub_norm_le (Freq.embedX (rotatingSlice a U (similarityTime T t))) (Freq.embedX h)
    have htri' := norm_le_insert' (Freq.embedX h) (Freq.embedX (rotatingSlice a U (similarityTime T t)))
    set x := ‖Freq.embedX h‖ with hx
    have hxlo : c / 2 ≤ x := by linarith
    have hxhi : x ≤ Real.sqrt (max B 0) + c / 2 := by
      have := norm_sub_rev (Freq.embedX h) (Freq.embedX (rotatingSlice a U (similarityTime T t)))
      linarith
    have hmK := hK T t hT hT1 ht0 ht
    set m := μ' * ∫ y, ‖h y‖ ^ 2 with hmdef
    have hm0 : 0 ≤ m := mul_nonneg hμ'pos.le (integral_nonneg fun y => by positivity)
    have hEN : ‖(μ' ^ (1 / 4 : ℝ)) • toV (transplantField μ' h)‖ ^ 2 = x ^ 2 + m := by
      rw [hn, hx, hnorm]
    have hper := periodic_eq hA hU hα0 hT ht
    rw [← hℓdef, ← hμ'def, ← hhdef] at hper
    rw [hper, Internal.TestLift.toV_smul, smul_smul]
    have hq : 0 < μ' ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hμ'pos _
    have hpiece : ‖(μ ^ dilExponent α * ℓ ^ (-(1 - 1 / α))) • toV (transplantField μ' h)‖ =
        (μ / ℓ) ^ dilExponent α * Real.sqrt (x ^ 2 + m) := by
      have hApos : (0 : ℝ) < μ ^ dilExponent α * ℓ ^ (-(1 - 1 / α)) :=
        mul_pos (Real.rpow_pos_of_pos hμ _) (Real.rpow_pos_of_pos hℓpos _)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hApos, ← coef_eq hμ hℓpos hα0, ← hEN,
        Real.sqrt_sq (norm_nonneg _), norm_smul, Real.norm_eq_abs, abs_of_pos hq, div_mul_eq_mul_div,
        mul_div_assoc, mul_comm (μ' ^ (1 / 4 : ℝ)), mul_div_assoc, div_self hq.ne', mul_one]
    rw [hpiece]
    have hr1 : 1 ≤ μ / ℓ := by rw [le_div_iff₀ hℓpos, one_mul]; exact hℓμ
    have hr2 : μ / ℓ ≤ 1 / lam := by
      rw [div_le_div_iff₀ hℓpos hl]
      linarith
    have hp1 : 1 ≤ (μ / ℓ) ^ dilExponent α := Real.one_le_rpow hr1 hκ
    have hp2 : (μ / ℓ) ^ dilExponent α ≤ (lam ^ dilExponent α)⁻¹ := by
      rw [← Real.inv_rpow hl.le, ← one_div]
      exact Real.rpow_le_rpow (by linarith) hr2 hκ
    have hs1 : c / 2 ≤ Real.sqrt (x ^ 2 + m) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith
    have hs2 : Real.sqrt (x ^ 2 + m) ≤ M₀ := by
      rw [hM₀]
      refine Real.sqrt_le_sqrt ?_
      have : x ^ 2 ≤ (Real.sqrt (max B 0) + c / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hxhi 2
      have : m ≤ |K| := hmK.trans (le_abs_self K)
      linarith
    have hM0 : 0 ≤ M₀ := hM₀ ▸ Real.sqrt_nonneg _
    constructor
    · nlinarith
    · exact mul_le_mul hp2 hs2 (Real.sqrt_nonneg _) (by positivity)
  exact ⟨(ContinuousMap.norm_le _ (by
    have : 0 < lam ^ dilExponent α := Real.rpow_pos_of_pos hl _
    have hM0 : 0 ≤ M₀ := hM₀ ▸ Real.sqrt_nonneg _
    positivity)).2 fun s => (key s).2, fun s => (key s).1⟩

end Breakdown.Periodic
