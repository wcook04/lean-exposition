import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

namespace Rest

theorem norm_iter_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space → E) (y : Space) :
    ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fun x => fderiv ℝ f x) y‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 1)
  rw [norm_iteratedFDeriv_one] at h
  exact h.symm

theorem coord_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h := abs_real_inner_le_norm x (unitVector i)
  simpa [unitVector, EuclideanSpace.inner_single_right] using h

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem apply_le (G : Space →L[ℝ] Space) (j i : Fin 3) : |G (unitVector j) i| ≤ ‖G‖ := by
  refine (coord_le _ i).trans ?_
  have := G.le_opNorm (unitVector j)
  rwa [unit_norm, mul_one] at this

theorem apply2_le (H : Space →L[ℝ] Space →L[ℝ] Space) (m a b : Fin 3) :
    |H (unitVector m) (unitVector a) b| ≤ ‖H‖ := by
  refine (apply_le _ a b).trans ?_
  have := H.le_opNorm (unitVector m)
  rwa [unit_norm, mul_one] at this

theorem eps_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem sum3_le (f : Fin 3 → ℝ) (b : ℝ) (h : ∀ i, |f i| ≤ b) : |∑ i, f i| ≤ 3 * b := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, b := Finset.sum_le_sum (fun i _ => h i)
    _ = 3 * b := by simp

theorem mul2_le {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x * y| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem vortGrad_le (H : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) :
    |vortGrad H j m| ≤ 3 * (3 * (1 * ‖H‖)) := by
  unfold vortGrad
  exact sum3_le _ _ (fun a => sum3_le _ _ (fun b => mul2_le (eps_le _ _ _) (apply2_le _ _ _ _)))

theorem curl_coord_le (G : Space →L[ℝ] Space) (i : Fin 3) :
    |curlVec G i| ≤ ‖curlCLM‖ * ‖G‖ := by
  refine (coord_le _ i).trans ?_
  rw [← curlCLM_apply]
  exact curlCLM.le_opNorm G

theorem curl_norm_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ≤ ‖curlCLM‖ * ‖G‖ := by
  rw [← curlCLM_apply]
  exact curlCLM.le_opNorm G

theorem matNorm_le (K : Space →L[ℝ] Space) : matSq K ≤ 3 * ‖K‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖K (unitVector i)‖ ^ 2 ≤ ‖K‖ ^ 2 := fun i => by
    have := K.le_opNorm (unitVector i)
    rw [unit_norm, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ i : Fin 3, ‖K (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖K‖ ^ 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = 3 * ‖K‖ ^ 2 := by simp

theorem matNorm_nonneg (K : Space →L[ℝ] Space) : 0 ≤ matSq K := by
  unfold matSq
  exact Finset.sum_nonneg (fun i _ => by positivity)

theorem stretch_le (G dW : Space →L[ℝ] Space) (hW : Space →L[ℝ] Space →L[ℝ] Space) (u : Space) :
    |-(∑ i : Fin 3, ∑ j : Fin 3, curlVec G i
      * ((dW (unitVector j) i + dW (unitVector i) j) / 2) * curlVec G j)
    + ∑ j : Fin 3, (∑ m : Fin 3, u m * vortGrad hW j m) * curlVec G j
    + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad hW j m * G (unitVector j) i * u l|
      ≤ 3 * (3 * (‖curlCLM‖ * ‖G‖ * ‖dW‖ * (‖curlCLM‖ * ‖G‖)))
        + 3 * (3 * (‖u‖ * (3 * (3 * (1 * ‖hW‖)))) * (‖curlCLM‖ * ‖G‖))
        + (1 / 2 : ℝ) * (3 * (3 * (3 * (3 * (1 * (3 * (3 * (1 * ‖hW‖))) * ‖G‖ * ‖u‖))))) := by
  have hS : ∀ i j : Fin 3, |(dW (unitVector j) i + dW (unitVector i) j) / 2| ≤ ‖dW‖ := by
    intro i j
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := abs_add_le (dW (unitVector j) i) (dW (unitVector i) j)
    linarith [apply_le dW j i, apply_le dW i j]
  have t1 : |∑ i : Fin 3, ∑ j : Fin 3, curlVec G i
      * ((dW (unitVector j) i + dW (unitVector i) j) / 2) * curlVec G j|
      ≤ 3 * (3 * (‖curlCLM‖ * ‖G‖ * ‖dW‖ * (‖curlCLM‖ * ‖G‖))) :=
    sum3_le _ _ (fun i => sum3_le _ _ (fun j =>
      mul2_le (mul2_le (curl_coord_le G i) (hS i j)) (curl_coord_le G j)))
  have t2 : |∑ j : Fin 3, (∑ m : Fin 3, u m * vortGrad hW j m) * curlVec G j|
      ≤ 3 * (3 * (‖u‖ * (3 * (3 * (1 * ‖hW‖)))) * (‖curlCLM‖ * ‖G‖)) :=
    sum3_le _ _ (fun j => mul2_le (sum3_le _ _ (fun m => mul2_le (coord_le u m) (vortGrad_le hW j m)))
      (curl_coord_le G j))
  have t3 : |(1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad hW j m * G (unitVector j) i * u l|
      ≤ (1 / 2 : ℝ) * (3 * (3 * (3 * (3 * (1 * (3 * (3 * (1 * ‖hW‖))) * ‖G‖ * ‖u‖))))) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact sum3_le _ _ (fun i => sum3_le _ _ (fun m => sum3_le _ _ (fun l => sum3_le _ _ (fun j =>
      mul2_le (mul2_le (mul2_le (eps_le i m l) (vortGrad_le hW j m)) (apply_le G j i)) (coord_le u l)))))
  have := abs_add_le (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec G i
      * ((dW (unitVector j) i + dW (unitVector i) j) / 2) * curlVec G j)
    + ∑ j : Fin 3, (∑ m : Fin 3, u m * vortGrad hW j m) * curlVec G j)
    ((1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad hW j m * G (unitVector j) i * u l)
  have := abs_add_le (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec G i
      * ((dW (unitVector j) i + dW (unitVector i) j) / 2) * curlVec G j))
    (∑ j : Fin 3, (∑ m : Fin 3, u m * vortGrad hW j m) * curlVec G j)
  rw [abs_neg] at this
  linarith

theorem joint_integrable (f : ℝ → Space → ℝ) (hc : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (h0 : ∀ σ y, 0 ≤ f σ y) (hf : periodLIntegral f < ⊤) :
    Integrable (fun z : ℝ × Space => f z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine (lintegral_prod (fun a : ℝ × Space => ‖f a.1 a.2‖ₑ)
    (continuous_enorm.comp hc).measurable.aemeasurable).trans_lt ?_
  have e : ∀ σ y, ‖f σ y‖ₑ = ENNReal.ofReal (f σ y) := fun σ y => by
    rw [← ofReal_norm, Real.norm_of_nonneg (h0 σ y)]
  dsimp only
  simp only [e]
  exact hf

theorem point_bound {fr cu st H B dW hWv A c D M : ℝ} (hD0 : 0 ≤ D) (hM0 : 0 ≤ M)
    (hB0 : 0 ≤ B) (hfr0 : 0 ≤ fr) (hfr : fr ≤ 3 * c ^ 2 * H ^ 2) (hcu0 : 0 ≤ cu)
    (hcu : cu ≤ c ^ 2 * B ^ 2) (hst : |st| ≤ 3 * (3 * (c * B * dW * (c * B))) + M * hWv * B)
    (hdW : dW ≤ D) (hW : hWv ≤ D * A) :
    |fr + (1 / 4 : ℝ) * cu + st| ≤
      3 * c ^ 2 * H ^ 2 + (c ^ 2 / 4 + 9 * c ^ 2 * D + M * D / 2) * B ^ 2 + M * D / 2 * A ^ 2 := by
  have s1 : |fr + (1 / 4 : ℝ) * cu + st| ≤ |fr + (1 / 4 : ℝ) * cu| + |st| := abs_add_le _ _
  have s2 : |fr + (1 / 4 : ℝ) * cu| = fr + (1 / 4 : ℝ) * cu := abs_of_nonneg (by positivity)
  have q1 : 3 * (3 * (c * B * dW * (c * B))) ≤ 9 * (c ^ 2 * B ^ 2) * D := by
    have e : 3 * (3 * (c * B * dW * (c * B))) = 9 * (c ^ 2 * B ^ 2) * dW := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hdW (by positivity)
  have q2 : M * hWv * B ≤ M * (D * A) * B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hM0) hB0
  have q3 : A * B ≤ (A ^ 2 + B ^ 2) / 2 := by nlinarith [sq_nonneg (A - B)]
  have q4 : M * (D * A) * B ≤ M * D * ((A ^ 2 + B ^ 2) / 2) := by
    have e : M * (D * A) * B = M * D * (A * B) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left q3 (mul_nonneg hM0 hD0)
  have e2 : M * D * ((A ^ 2 + B ^ 2) / 2) = M * D / 2 * A ^ 2 + M * D / 2 * B ^ 2 := by ring
  have e3 : (c ^ 2 / 4 + 9 * c ^ 2 * D + M * D / 2) * B ^ 2
      = (1 / 4 : ℝ) * (c ^ 2 * B ^ 2) + 9 * (c ^ 2 * B ^ 2) * D + M * D / 2 * B ^ 2 := by ring
  rw [s2] at s1
  rw [e3]
  linarith

end Rest

open Rest in
theorem rest_integrable (P : ℝ) (W v : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    IntegrableOn (fun σ => ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchForm W v (gradField v) σ y))
      (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨D, hD⟩ := hWdec
  have hD0 : 0 ≤ D := by
    have := hD 0 0 0 (by norm_num)
    simp at this
    exact (norm_nonneg _).trans this
  have h0 := hv.smooth
  have j1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    joint_partial v h0 (by simp) (by simp)
  have j2 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    joint_partial (fun σ x => fderiv ℝ (v σ) x) j1 (by simp) (by simp)
  have j3 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => curlCLM (fderiv ℝ (v z.1) x)) z.2) :=
    joint_partial (fun σ x => curlCLM (fderiv ℝ (v σ) x)) (curlCLM.contDiff.comp j1) (by simp) (by simp)
  have c0 : Continuous (fun z : ℝ × Space => v z.1 z.2) := h0.continuous
  have c1 := j1.continuous
  have c2 := j2.continuous
  have c3 := j3.continuous
  obtain ⟨w0, w1, w2⟩ := joint_continuous_weight hW
  have i0 := joint_integrable (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
    (by
      refine Continuous.div ((continuous_norm.comp c0).pow 2)
        ((continuous_const.add (continuous_norm.comp continuous_snd)).pow 2) (fun z => by positivity))
    (fun σ y => by positivity) hv.weighted_finite
  have e1 : (fun σ y => ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2) = fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2 := by
    funext σ y
    rw [norm_iteratedFDeriv_one]
  have e2 : (fun σ y => ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2) =
      fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2 := by
    funext σ y
    rw [norm_iter_two]
  have p1 := hv.derivatives_finite 1 le_rfl
  have p2 := hv.derivatives_finite 2 (by norm_num)
  rw [e1] at p1
  rw [e2] at p2
  have i1 := joint_integrable (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) ((continuous_norm.comp c1).pow 2)
    (fun σ y => by positivity) p1
  have i2 := joint_integrable (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2)
    ((continuous_norm.comp c2).pow 2) (fun σ y => by positivity) p2
  have hM0 : 0 ≤ 81 * ‖curlCLM‖ + 729 / 2 := by positivity
  have hdv : ∀ σ y, fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y =
      curlCLM.comp (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y) := by
    intro σ y
    have hd : DifferentiableAt ℝ (fun x => fderiv ℝ (v σ) x) y := by
      have hs : ContDiff ℝ ∞ (v σ) := h0.comp (contDiff_const.prodMk contDiff_id)
      exact ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
    exact fderiv_clm_left curlCLM hd
  refine Integrable.integral_prod_left (f := fun z : ℝ × Space =>
    matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2)
      + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v z.1) z.2)‖ ^ 2 + stretchForm W v (gradField v) z.1 z.2) ?_
  refine Integrable.mono' (((i2.const_mul (3 * ‖curlCLM‖ ^ 2)).add
    (i1.const_mul (‖curlCLM‖ ^ 2 / 4 + 9 * ‖curlCLM‖ ^ 2 * D + (81 * ‖curlCLM‖ + 729 / 2) * D / 2))).add
    (i0.const_mul ((81 * ‖curlCLM‖ + 729 / 2) * D / 2))) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    simp only [matSq, stretchForm, vortGrad, gradField, ← curlCLM_apply]
    fun_prop
  · refine Eventually.of_forall (fun z => ?_)
    obtain ⟨σ, y⟩ := z
    simp only
    have hWσ1 := hD σ y 1 (by norm_num)
    have hWσ2 := hD σ y 2 (by norm_num)
    rw [norm_iteratedFDeriv_one] at hWσ1
    rw [norm_iter_two] at hWσ2
    have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have dWle : ‖fderiv ℝ (W σ) y‖ ≤ D := by
      refine hWσ1.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (1 + ‖y‖) ^ (1 + 1) := one_le_pow₀ hy1
      nlinarith
    have hWle : ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ * ‖v σ y‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) := by
      have h3 : ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ ≤ D / (1 + ‖y‖) := by
        refine hWσ2.trans ?_
        apply div_le_div_of_nonneg_left hD0 (by positivity)
        calc 1 + ‖y‖ = (1 + ‖y‖) ^ 1 := (pow_one _).symm
          _ ≤ (1 + ‖y‖) ^ (2 + 1) := pow_le_pow_right₀ hy1 (by norm_num)
      calc ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ * ‖v σ y‖
          ≤ D / (1 + ‖y‖) * ‖v σ y‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = D * (‖v σ y‖ / (1 + ‖y‖)) := by ring
    have hst : |stretchForm W v (gradField v) σ y| ≤
        3 * (3 * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖)))
          + (81 * ‖curlCLM‖ + 729 / 2) * (‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ * ‖v σ y‖)
            * ‖fderiv ℝ (v σ) y‖ :=
      (stretch_le (fderiv ℝ (v σ) y) (fderiv ℝ (W σ) y) (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y)
        (v σ y)).trans (le_of_eq (by ring))
    have hfr : matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) ≤
        3 * ‖curlCLM‖ ^ 2 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2 := by
      rw [hdv]
      refine (matNorm_le _).trans ?_
      have h1 := ContinuousLinearMap.opNorm_comp_le curlCLM (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [mul_pow] at h2
      linarith
    have hcu : ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 ≤ ‖curlCLM‖ ^ 2 * ‖fderiv ℝ (v σ) y‖ ^ 2 := by
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (curl_norm_le (fderiv ℝ (v σ) y)) 2
      rwa [mul_pow] at h2
    rw [Real.norm_eq_abs]
    refine (point_bound hD0 hM0 (norm_nonneg _)
      (matNorm_nonneg _) hfr (by positivity) hcu hst dWle hWle).trans (le_of_eq ?_)
    rw [div_pow]
    rfl

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
