import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal


namespace SliceIntegrable

theorem int_mul {f g : Space → ℝ} (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (h1 : Integrable (fun y => f y ^ 2)) (h2 : Integrable (fun y => g y ^ 2)) :
    Integrable (fun y => f y * g y) := by
  refine ((h1.add h2).div_const 2).mono' (hf.mul hg) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have := two_mul_le_add_sq |f y| |g y|
  rw [sq_abs, sq_abs] at this
  simp only [Pi.add_apply]
  linarith

theorem unit_norm (j : Fin 3) : ‖unitVector j‖ = 1 := by
  simp [unitVector]

theorem comp_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at this

theorem entry_le (G : Space →L[ℝ] Space) (i j : Fin 3) : |G (unitVector j) i| ≤ ‖G‖ := by
  refine (comp_le _ i).trans ?_
  have := G.le_opNorm (unitVector j)
  rwa [unit_norm, mul_one] at this

theorem entry2_le (H : Space →L[ℝ] Space →L[ℝ] Space) (a b : Fin 3) (c : Fin 3) :
    |H (unitVector a) (unitVector b) c| ≤ ‖H‖ := by
  refine (comp_le _ c).trans ?_
  have := H.le_opNorm₂ (unitVector a) (unitVector b)
  rwa [unit_norm, unit_norm, mul_one, mul_one] at this

theorem eps_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem sum3 (f : Fin 3 → ℝ) (b : ℝ) (h : ∀ i, |f i| ≤ b) : |∑ i, f i| ≤ 3 * b := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)
  simp

theorem prod2 {a b α β : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) : |a * b| ≤ α * β := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem prod3 {a b c α β γ : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) (hc : |c| ≤ γ) :
    |a * b * c| ≤ α * β * γ :=
  prod2 (prod2 ha hb) hc

theorem prod4 {a b c d α β γ δ : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) (hc : |c| ≤ γ) (hd : |d| ≤ δ) :
    |a * b * c * d| ≤ α * β * γ * δ :=
  prod2 (prod3 ha hb hc) hd

theorem vort_le (H : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) : |vortGrad H j m| ≤ 3 * (3 * ‖H‖) := by
  unfold vortGrad
  refine sum3 _ _ fun a => sum3 _ _ fun b => ?_
  have := prod2 (eps_le j a b) (entry2_le H m a b)
  rwa [one_mul] at this

theorem trace_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
  unfold secondDerivTrace
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ‖H‖ := fun j => by
    have := H.le_opNorm₂ (unitVector j) (unitVector j)
    rwa [unit_norm, mul_one, mul_one] at this
  calc ∑ j, ‖H (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖H‖ := Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖H‖ := by simp

theorem curl_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ≤ ‖curlCLM‖ * ‖G‖ := by
  rw [← curlCLM_apply]
  exact curlCLM.le_opNorm G

theorem norm_iter_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F) (y : Space) :
    ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 0)
  rw [norm_iteratedFDeriv_zero] at this
  exact this.symm

theorem norm_iter_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F) (y : Space) :
    ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fun x => fderiv ℝ f x) y‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 1)
  rw [norm_iter_one] at this
  exact this.symm

theorem weight_facts (W : ℝ → Space → Space) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) :
    ∃ D, 0 ≤ D ∧ Continuous (W σ) ∧ Continuous (fun y => fderiv ℝ (W σ) y) ∧
      Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) ∧
      (∀ y, ‖W σ y‖ ≤ D) ∧ (∀ y, ‖fderiv ℝ (W σ) y‖ ≤ D) ∧
      (∀ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖)) ∧
      (∀ y, ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ ≤ D / (1 + ‖y‖)) := by
  obtain ⟨D, hD⟩ := hWdec
  have hWs : ContDiff ℝ 2 (W σ) := hW.comp (contDiff_const.prodMk contDiff_id)
  have n0 : ∀ y, ‖W σ y‖ ≤ D / (1 + ‖y‖) := fun y => by
    have := hD σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  have n1 : ∀ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := fun y => by
    have := hD σ y 1 (by norm_num)
    rw [norm_iter_one] at this
    simpa using this
  have n2 : ∀ y, ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ ≤ D / (1 + ‖y‖) ^ 3 := fun y => by
    have := hD σ y 2 (by norm_num)
    rw [norm_iter_two] at this
    simpa using this
  have hD0 : 0 ≤ D := by
    have := (norm_nonneg _).trans (n0 0)
    simpa using this
  have r1 : ∀ y : Space, (1 : ℝ) ≤ 1 + ‖y‖ := fun y => by linarith [norm_nonneg y]
  have r0 : ∀ y : Space, (0 : ℝ) < 1 + ‖y‖ := fun y => by linarith [norm_nonneg y]
  refine ⟨D, hD0, hWs.continuous, hWs.continuous_fderiv (by norm_num),
    (hWs.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num), fun y => ?_, fun y => ?_,
    fun y => ?_, fun y => ?_⟩
  · exact (n0 y).trans (div_le_self hD0 (r1 y))
  · exact (n1 y).trans (div_le_self hD0 (one_le_pow₀ (r1 y)))
  · exact (n1 y).trans (div_le_div_of_nonneg_left hD0 (r0 y) (le_self_pow₀ (r1 y) (by norm_num)))
  · exact (n2 y).trans (div_le_div_of_nonneg_left hD0 (r0 y) (le_self_pow₀ (r1 y) (by norm_num)))

theorem slice_cont (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) :
    ContDiff ℝ ∞ (v σ) ∧ Continuous (fun y => fderiv ℝ (v σ) y) ∧
    Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ (v σ) x) y) ∧
    Continuous (fun y => fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) ∧
    Continuous (fun y => deriv (fun s => v s y) σ) ∧
    Continuous (fun y => fderiv ℝ (fun x => deriv (fun s => v s x) σ) y) := by
  have h0 := hv.smooth
  have hs : ContDiff ℝ ∞ (v σ) := h0.comp (contDiff_const.prodMk contDiff_id)
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ (v σ) y) := hs.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun y => curlCLM (fderiv ℝ (v σ) y)) := curlCLM.contDiff.comp h1
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := h0.differentiable (by simp)
  have e : (fun y => deriv (fun s => v s y) σ) =
      fun y => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, y) (1, 0) := by
    funext y
    exact time_deriv_eq v hd σ y
  have ht : ContDiff ℝ ∞ (fun y => deriv (fun s => v s y) σ) := by
    rw [e]
    exact ((h0.fderiv_right (m := ∞) (by simp)).comp (contDiff_const.prodMk contDiff_id)).clm_apply
      contDiff_const
  exact ⟨hs, h1.continuous, h1.continuous_fderiv (by simp), h2.continuous_fderiv (by simp),
    ht.continuous, ht.continuous_fderiv (by simp)⟩

end SliceIntegrable

open SliceIntegrable in
theorem slice_integrable (P : ℝ) (W v : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ) :
    Integrable (fun y => inner ℝ (transportPart P v σ y) (-secondDerivTrace (secondDerivField v σ y))) ∧
    Integrable (fun y => inner ℝ (-secondDerivTrace (secondDerivField v σ y)) (-secondDerivTrace (secondDerivField v σ y))) ∧
    Integrable (fun y => inner ℝ (advectionPart W v σ y) (-secondDerivTrace (secondDerivField v σ y))) ∧
    Integrable (fun y => timePair v σ y) ∧
    Integrable (fun y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)) ∧
    Integrable (fun y => (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) ∧
    Integrable (fun y => stretchForm W v (gradField v) σ y) := by
  obtain ⟨hsm, c1, c2, c3, ct, cdt⟩ := slice_cont P v hv σ
  obtain ⟨D, hD0, w0, w1, w2, nW, nA, nA', nB⟩ := weight_facts W hW hWdec σ
  have c0 : Continuous (v σ) := hsm.continuous
  have cT : Continuous (fun y => transportPart P v σ y) := by
    unfold transportPart
    fun_prop
  have cr : Continuous (fun y : Space => ‖v σ y‖ / (1 + ‖y‖)) :=
    c0.norm.div (continuous_const.add continuous_norm) (fun y => by positivity)
  have mH : AEStronglyMeasurable (fun y => ‖secondDerivField v σ y‖) := c2.norm.aestronglyMeasurable
  have mG : AEStronglyMeasurable (fun y => ‖fderiv ℝ (v σ) y‖) := c1.norm.aestronglyMeasurable
  have mr : AEStronglyMeasurable (fun y : Space => ‖v σ y‖ / (1 + ‖y‖)) := cr.aestronglyMeasurable
  have hwr : Integrable (fun y : Space => (‖v σ y‖ / (1 + ‖y‖)) ^ 2) := by
    simpa only [div_pow] using hs.weighted
  have iTH := int_mul cT.norm.aestronglyMeasurable mH hs.transport hs.second
  have iHG := int_mul mH mG hs.second hs.first
  have iHr := int_mul mH mr hs.second hwr
  have iGr := int_mul mG mr hs.first hwr
  have itG := int_mul cdt.norm.aestronglyMeasurable mG hs.time_first hs.first
  set K := ‖curlCLM‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (iTH.const_mul 3).mono' ?_ (Eventually.of_forall fun y => ?_)
    · simp only [secondDerivTrace, secondDerivField]
      exact (cT.inner (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_neg]
      have := trace_le (secondDerivField v σ y)
      have h0 := norm_nonneg (transportPart P v σ y)
      nlinarith
  · refine (hs.second.const_mul 9).mono' ?_ (Eventually.of_forall fun y => ?_)
    · simp only [secondDerivTrace, secondDerivField]
      exact (Continuous.inner (by fun_prop) (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, real_inner_self_eq_norm_sq, norm_neg, abs_of_nonneg (by positivity)]
      have := trace_le (secondDerivField v σ y)
      have h0 := norm_nonneg (secondDerivTrace (secondDerivField v σ y))
      change ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 ≤ 9 * ‖secondDerivField v σ y‖ ^ 2
      nlinarith
  · refine ((iHG.const_mul (3 * D)).add (iHr.const_mul (3 * D))).mono' ?_
      (Eventually.of_forall fun y => ?_)
    · simp only [secondDerivTrace, secondDerivField, advectionPart]
      exact (Continuous.inner (by fun_prop) (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_neg]
      have ht := trace_le (secondDerivField v σ y)
      have ha : ‖advectionPart W v σ y‖ ≤ ‖fderiv ℝ (v σ) y‖ * D + D * (‖v σ y‖ / (1 + ‖y‖)) := by
        unfold advectionPart
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact ((fderiv ℝ (v σ) y).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (nW y) (norm_nonneg _))
        · refine ((fderiv ℝ (W σ) y).le_opNorm _).trans ?_
          calc ‖fderiv ℝ (W σ) y‖ * ‖v σ y‖ ≤ D / (1 + ‖y‖) * ‖v σ y‖ :=
                mul_le_mul_of_nonneg_right (nA' y) (norm_nonneg _)
            _ = D * (‖v σ y‖ / (1 + ‖y‖)) := by ring
      have h0 := norm_nonneg (advectionPart W v σ y)
      have h1 := norm_nonneg (secondDerivTrace (secondDerivField v σ y))
      have h2 := norm_nonneg (secondDerivField v σ y)
      have h3 : 0 ≤ ‖v σ y‖ / (1 + ‖y‖) := by positivity
      have h4 := norm_nonneg (fderiv ℝ (v σ) y)
      calc ‖advectionPart W v σ y‖ * ‖secondDerivTrace (secondDerivField v σ y)‖
          ≤ (‖fderiv ℝ (v σ) y‖ * D + D * (‖v σ y‖ / (1 + ‖y‖))) * (3 * ‖secondDerivField v σ y‖) :=
            mul_le_mul ha ht h1 (by positivity)
        _ = 3 * D * (‖secondDerivField v σ y‖ * ‖fderiv ℝ (v σ) y‖)
            + 3 * D * (‖secondDerivField v σ y‖ * (‖v σ y‖ / (1 + ‖y‖))) := by ring
  · refine (itG.const_mul 3).mono' ?_ (Eventually.of_forall fun y => ?_)
    · unfold timePair
      exact (continuous_finsetSum _ fun j _ => Continuous.inner (by fun_prop) (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      unfold timePair
      refine sum3 _ _ fun j => (abs_real_inner_le_norm _ _).trans ?_
      have a1 := (fderiv ℝ (fun x => deriv (fun s => v s x) σ) y).le_opNorm (unitVector j)
      have a2 := (fderiv ℝ (v σ) y).le_opNorm (unitVector j)
      rw [unit_norm, mul_one] at a1 a2
      exact mul_le_mul a1 a2 (norm_nonneg _) (norm_nonneg _)
  · refine (hs.second.const_mul (3 * K ^ 2)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · simp only [matSq]
      exact (continuous_finsetSum _ fun j _ => by fun_prop).aestronglyMeasurable
    · have hdd : DifferentiableAt ℝ (fun x => fderiv ℝ (v σ) x) y :=
        ((hsm.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
      have e : fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y = curlCLM.comp (secondDerivField v σ y) :=
        fderiv_clm_left curlCLM hdd
      rw [e]
      have hc : ‖curlCLM.comp (secondDerivField v σ y)‖ ≤ K * ‖secondDerivField v σ y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      have hf : matSq (curlCLM.comp (secondDerivField v σ y)) ≤ 3 * ‖curlCLM.comp (secondDerivField v σ y)‖ ^ 2 := by
        unfold matSq
        calc ∑ i : Fin 3, ‖(curlCLM.comp (secondDerivField v σ y)) (unitVector i)‖ ^ 2
            ≤ ∑ _i : Fin 3, ‖curlCLM.comp (secondDerivField v σ y)‖ ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              have := (curlCLM.comp (secondDerivField v σ y)).le_opNorm (unitVector i)
              rw [unit_norm, mul_one] at this
              exact pow_le_pow_left₀ (norm_nonneg _) this 2
          _ = 3 * ‖curlCLM.comp (secondDerivField v σ y)‖ ^ 2 := by simp
      have hf0 : 0 ≤ matSq (curlCLM.comp (secondDerivField v σ y)) := by
        unfold matSq
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      refine hf.trans ?_
      have := pow_le_pow_left₀ (norm_nonneg _) hc 2
      rw [mul_pow] at this
      change 3 * ‖curlCLM.comp (secondDerivField v σ y)‖ ^ 2 ≤ 3 * K ^ 2 * ‖secondDerivField v σ y‖ ^ 2
      linarith
  · refine (hs.first.const_mul ((1 / 4 : ℝ) * K ^ 2)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · simp only [← curlCLM_apply]
      exact (by fun_prop : Continuous fun y => (1 / 4 : ℝ) * ‖curlCLM (fderiv ℝ (v σ) y)‖ ^ 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := pow_le_pow_left₀ (norm_nonneg _) (curl_le (fderiv ℝ (v σ) y)) 2
      nlinarith
  · refine ((hs.first.const_mul (9 * (K * K) * D)).add
      (iGr.const_mul (81 * K * D + 729 / 2 * D))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · simp only [stretchForm, vortGrad, gradField, ← curlCLM_apply]
      fun_prop
    · rw [Real.norm_eq_abs]
      set G := fderiv ℝ (v σ) y with hG
      set A := fderiv ℝ (W σ) y with hA
      set B := fderiv ℝ (fun x => fderiv ℝ (W σ) x) y with hB
      have hGc : ∀ i, |curlVec G i| ≤ K * ‖G‖ := fun i => (comp_le _ i).trans (curl_le G)
      have hAs : ∀ i j : Fin 3, |(A (unitVector j) i + A (unitVector i) j) / 2| ≤ ‖A‖ := by
        intro i j
        rw [abs_div, abs_two]
        have := abs_add_le (A (unitVector j) i) (A (unitVector i) j)
        have := entry_le A i j
        have := entry_le A j i
        linarith
      have T1 : |∑ i : Fin 3, ∑ j : Fin 3, curlVec G i * ((A (unitVector j) i + A (unitVector i) j) / 2)
          * curlVec G j| ≤ 3 * (3 * (K * ‖G‖ * ‖A‖ * (K * ‖G‖))) :=
        sum3 _ _ fun i => sum3 _ _ fun j => prod3 (hGc i) (hAs i j) (hGc j)
      have T2 : |∑ j : Fin 3, (∑ m : Fin 3, v σ y m * vortGrad B j m) * curlVec G j|
          ≤ 3 * (3 * (‖v σ y‖ * (3 * (3 * ‖B‖))) * (K * ‖G‖)) :=
        sum3 _ _ fun j => prod2 (sum3 _ _ fun m => prod2 (comp_le _ m) (vort_le B j m)) (hGc j)
      have T3 : |∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad B j m * G (unitVector j) i * v σ y l|
          ≤ 3 * (3 * (3 * (3 * (1 * (3 * (3 * ‖B‖)) * ‖G‖ * ‖v σ y‖)))) :=
        sum3 _ _ fun i => sum3 _ _ fun m => sum3 _ _ fun l => sum3 _ _ fun j =>
          prod4 (eps_le i m l) (vort_le B j m) (entry_le G i j) (comp_le _ l)
      have hs3 : |stretchForm W v (gradField v) σ y| ≤
          3 * (3 * (K * ‖G‖ * ‖A‖ * (K * ‖G‖)))
          + 3 * (3 * (‖v σ y‖ * (3 * (3 * ‖B‖))) * (K * ‖G‖))
          + 1 / 2 * (3 * (3 * (3 * (3 * (1 * (3 * (3 * ‖B‖)) * ‖G‖ * ‖v σ y‖))))) := by
        unfold stretchForm
        simp only [gradField]
        rw [← hG, ← hA, ← hB]
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ T2)) ?_)
        · rw [abs_neg]
          exact T1
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left T3 (by norm_num)
      refine hs3.trans ?_
      have g0 := norm_nonneg G
      have u0 := norm_nonneg (v σ y)
      have hAD := nA y
      have hBD := nB y
      rw [← hA] at hAD
      rw [← hB] at hBD
      have r0 : (0 : ℝ) < 1 + ‖y‖ := by positivity
      calc 3 * (3 * (K * ‖G‖ * ‖A‖ * (K * ‖G‖)))
          + 3 * (3 * (‖v σ y‖ * (3 * (3 * ‖B‖))) * (K * ‖G‖))
          + 1 / 2 * (3 * (3 * (3 * (3 * (1 * (3 * (3 * ‖B‖)) * ‖G‖ * ‖v σ y‖)))))
          ≤ 3 * (3 * (K * ‖G‖ * D * (K * ‖G‖)))
          + 3 * (3 * (‖v σ y‖ * (3 * (3 * (D / (1 + ‖y‖))))) * (K * ‖G‖))
          + 1 / 2 * (3 * (3 * (3 * (3 * (1 * (3 * (3 * (D / (1 + ‖y‖)))) * ‖G‖ * ‖v σ y‖))))) := by
            gcongr
        _ = 9 * (K * K) * D * ‖G‖ ^ 2 + (81 * K * D + 729 / 2 * D) * (‖G‖ * (‖v σ y‖ / (1 + ‖y‖))) := by
            field_simp
            ring

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
