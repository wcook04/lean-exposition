import Breakdown.FracCert.StFree

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

private theorem sq_add_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) (c : ℝ) :
    ‖a + c • b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * c ^ 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a (c • b)
  rw [norm_smul, Real.norm_eq_abs] at h
  have h2 : ‖a + c • b‖ ^ 2 ≤ (‖a‖ + |c| * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_abs c, sq_nonneg (‖a‖ - |c| * ‖b‖)]

private theorem turnStep_add_smul (m : ℕ) (a b : Space) (c : ℝ) :
    turnStep m (a + c • b) = turnStep m a + c • turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

private theorem mirror_add_smul (a b : Space) (c : ℝ) :
    mirror (a + c • b) = mirror a + c • mirror b := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply] <;> ring

private theorem entrySq_continuous : Continuous entrySq :=
  continuous_finsetSum _ fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2

private theorem fullSq_continuous :
    Continuous (fun B : Space →L[ℝ] Space →L[ℝ] Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, ‖B (unitVector i) (unitVector j)‖ ^ 2) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2

private theorem col_memLp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {m : ℕ} (h : IsSecondOrderField m v G H) (i : Fin 3) :
    MemLp (fun y => G y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
      h.measurable_gradient
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h.gradient_two.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)

private theorem entry_memLp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {m : ℕ} (h : IsSecondOrderField m v G H) (i j : Fin 3) :
    MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous.comp_aestronglyMeasurable
        h.measurable_second)
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h.second_two.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖H y (unitVector i) (unitVector j)‖ ^ 2 ≤ ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖H y (unitVector i) (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i)

private theorem test_integrable {f : Space → Space} {p : ℝ≥0∞} (hf : MemLp f p volume) (hp : 1 ≤ p)
    {g : Space → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun y => g y • f y) volume :=
  (hf.locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport hg hgc

private theorem deriv_test_continuous {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem deriv_test_support {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)

private theorem lin_integral {f g : Space → Space} {a : Space → ℝ}
    (hf : Integrable (fun y => a y • f y) volume) (hg : Integrable (fun y => a y • g y) volume) (c : ℝ) :
    ∫ y, a y • (f y + c • g y) = (∫ y, a y • f y) + c • ∫ y, a y • g y := by
  calc ∫ y, a y • (f y + c • g y) = ∫ y, (a y • f y + c • (a y • g y)) := by
        congr 1
        funext y
        rw [smul_add, smul_comm]
    _ = (∫ y, a y • f y) + ∫ y, c • (a y • g y) := by
        have hg' : Integrable (fun y => c • (a y • g y)) volume := hg.smul c
        exact integral_add hf hg'
    _ = _ := by rw [integral_smul]

theorem secondOrderLinear : SecondOrderLinearStatement := by
  intro m v u G K H L c hv hu
  refine ⟨hv.measurable_velocity.add (hu.measurable_velocity.const_smul c),
    hv.measurable_gradient.add (hu.measurable_gradient.const_smul c),
    hv.measurable_second.add (hu.measurable_second.const_smul c),
    hv.velocity_six.add (hu.velocity_six.const_smul c), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((hv.gradient_two.const_mul 2).add (hu.gradient_two.const_mul (2 * c ^ 2))).mono'
      (entrySq_continuous.comp_aestronglyMeasurable
        (hv.measurable_gradient.add (hu.measurable_gradient.const_smul c))) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by unfold entrySq; positivity)]
    simp only [entrySq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, mul_assoc] using
      sq_add_smul_le (G y (unitVector i)) (K y (unitVector i)) c
  · refine ((hv.second_two.const_mul 2).add (hu.second_two.const_mul (2 * c ^ 2))).mono'
      (fullSq_continuous.comp_aestronglyMeasurable
        (hv.measurable_second.add (hu.measurable_second.const_smul c))) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
    simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, mul_assoc] using
      sq_add_smul_le (H y (unitVector i) (unitVector j)) (L y (unitVector i) (unitVector j)) c
  · intro φ hφ j
    have h1 := hv.weak_gradient φ hφ j
    have h2 := hu.weak_gradient φ hφ j
    have hc := deriv_test_continuous hφ j
    have hs := deriv_test_support hφ j
    beta_reduce
    rw [lin_integral (test_integrable hv.velocity_six (by norm_num) hc hs)
      (test_integrable hu.velocity_six (by norm_num) hc hs) c]
    have e : ∫ y, φ y • (G y + c • K y) (unitVector j) =
        ∫ y, φ y • (G y (unitVector j) + c • K y (unitVector j)) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [e, lin_integral (test_integrable (col_memLp hv j) (by norm_num) hφ.1.continuous hφ.2)
      (test_integrable (col_memLp hu j) (by norm_num) hφ.1.continuous hφ.2) c]
    beta_reduce
    linear_combination (norm := module) h1 + c • h2
  · intro φ hφ i j
    have h1 := hv.weak_second φ hφ i j
    have h2 := hu.weak_second φ hφ i j
    have hc := deriv_test_continuous hφ j
    have hs := deriv_test_support hφ j
    have e1 : ∫ y, fderiv ℝ φ y (unitVector j) • (G y + c • K y) (unitVector i) =
        ∫ y, fderiv ℝ φ y (unitVector j) • (G y (unitVector i) + c • K y (unitVector i)) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    have e2 : ∫ y, φ y • (H y + c • L y) (unitVector j) (unitVector i) =
        ∫ y, φ y • (H y (unitVector j) (unitVector i) + c • L y (unitVector j) (unitVector i)) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    beta_reduce
    rw [e1, lin_integral (test_integrable (col_memLp hv i) (by norm_num) hc hs)
      (test_integrable (col_memLp hu i) (by norm_num) hc hs) c, e2,
      lin_integral (test_integrable (entry_memLp hv j i) (by norm_num) hφ.1.continuous hφ.2)
      (test_integrable (entry_memLp hu j i) (by norm_num) hφ.1.continuous hφ.2) c]
    beta_reduce
    linear_combination (norm := module) h1 + c • h2
  · filter_upwards [hv.divergence, hu.divergence] with y h1 h2
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      real_inner_smul_left, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]
  · refine ⟨?_, ?_⟩
    · filter_upwards [hv.symmetric.1, hu.symmetric.1] with y h1 h2
      rw [h1, h2, turnStep_add_smul]
    · filter_upwards [hv.symmetric.2, hu.symmetric.2] with y h1 h2
      rw [h1, h2, mirror_add_smul]

def SixthGradientBoundStatement : Prop :=
  ∃ C : ℝ, ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
    MemLp v 6 volume → Integrable (fun y => entrySq (G y)) → IsWeakGradientOf v G →
    ∫ y, ‖v y‖ ^ 6 ≤ C * (∫ y, entrySq (G y)) ^ 3

private theorem unitVector_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem col_le (L : Space →L[ℝ] Space) (i : Fin 3) : ‖L (unitVector i)‖ ≤ ‖L‖ := by
  have h := L.le_opNorm (unitVector i)
  rwa [unitVector_norm, mul_one] at h

private theorem entry_le (B : Space →L[ℝ] Space →L[ℝ] Space) (i j : Fin 3) :
    ‖B (unitVector i) (unitVector j)‖ ≤ ‖B‖ :=
  (col_le (B (unitVector i)) j).trans (by
    have h := B.le_opNorm (unitVector i)
    rwa [unitVector_norm, mul_one] at h)

private theorem opNorm_le_sqrt_entrySq (L : Space →L[ℝ] Space) : ‖L‖ ≤ Real.sqrt (entrySq L) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hx : x = ∑ i, x i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x).symm
  calc ‖L x‖ = ‖∑ i, x i • L (unitVector i)‖ := by
        conv_lhs => rw [hx]
        simp only [map_sum, map_smul]
    _ ≤ ∑ i, ‖x i • L (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖L (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, ‖L (unitVector i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (entrySq L) * ‖x‖ := by rw [EuclideanSpace.norm_eq x, mul_comm]; rfl

private theorem opNorm_sq_le_entrySq (L : Space →L[ℝ] Space) : ‖L‖ ^ 2 ≤ entrySq L :=
  (pow_le_pow_left₀ (norm_nonneg _) (opNorm_le_sqrt_entrySq L) 2).trans
    (Real.sq_sqrt (by unfold entrySq; positivity)).le

private theorem entrySq_le (L : Space →L[ℝ] Space) : entrySq L ≤ 3 * ‖L‖ ^ 2 := by
  unfold entrySq
  calc ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 ≤ ∑ i : Fin 3, ‖L‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (col_le L i) 2
    _ = 3 * ‖L‖ ^ 2 := by simp

private theorem opNorm_sq_le_full (B : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖B‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖B (unitVector i) (unitVector j)‖ ^ 2 := by
  set F := ∑ i : Fin 3, ∑ j : Fin 3, ‖B (unitVector i) (unitVector j)‖ ^ 2
  have hF : 0 ≤ F := by positivity
  have key : ∀ x, ‖B x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
    intro x
    calc ‖B x‖ ^ 2 ≤ entrySq (B x) := opNorm_sq_le_entrySq (B x)
      _ = ∑ j : Fin 3, ‖(B.flip (unitVector j)) x‖ ^ 2 := by simp [entrySq]
      _ ≤ ∑ j : Fin 3, entrySq (B.flip (unitVector j)) * ‖x‖ ^ 2 := Finset.sum_le_sum fun j _ => by
          have h := (B.flip (unitVector j)).le_opNorm x
          have h2 := opNorm_sq_le_entrySq (B.flip (unitVector j))
          calc ‖(B.flip (unitVector j)) x‖ ^ 2 ≤ (‖B.flip (unitVector j)‖ * ‖x‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) h 2
            _ = ‖B.flip (unitVector j)‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
            _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = F * ‖x‖ ^ 2 := by
          rw [← Finset.sum_mul]
          congr 1
          simp only [entrySq, ContinuousLinearMap.flip_apply]
          exact Finset.sum_comm
  have hb : ‖B‖ ≤ Real.sqrt F := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    calc ‖B x‖ = Real.sqrt (‖B x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (F * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (key x)
      _ = Real.sqrt F * ‖x‖ := by rw [Real.sqrt_mul hF, Real.sqrt_sq (norm_nonneg _)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans (Real.sq_sqrt hF).le

private theorem full_le (B : Space →L[ℝ] Space →L[ℝ] Space) :
    ∑ i : Fin 3, ∑ j : Fin 3, ‖B (unitVector i) (unitVector j)‖ ^ 2 ≤ 9 * ‖B‖ ^ 2 := by
  calc ∑ i : Fin 3, ∑ j : Fin 3, ‖B (unitVector i) (unitVector j)‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖B‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (entry_le B i j) 2
    _ = 9 * ‖B‖ ^ 2 := by simp; ring

private theorem trace_le (B : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondTrace B‖ ^ 2 ≤ 9 * ‖B‖ ^ 2 := by
  have h : ‖secondTrace B‖ ≤ 3 * ‖B‖ := by
    unfold secondTrace
    calc ‖∑ j : Fin 3, B (unitVector j) (unitVector j)‖ ≤ ∑ j : Fin 3, ‖B (unitVector j) (unitVector j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ‖B‖ := Finset.sum_le_sum fun j _ => entry_le B j j
      _ = 3 * ‖B‖ := by simp
  nlinarith [norm_nonneg (secondTrace B), norm_nonneg B]

private theorem trace_sq_continuous :
    Continuous (fun B : Space →L[ℝ] Space →L[ℝ] Space => ‖secondTrace B‖ ^ 2) := by
  unfold secondTrace
  exact (continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2

private theorem memLp_two_of_sq {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : AEStronglyMeasurable f volume) {g : Space → ℝ} (hg : Integrable g volume)
    (h : ∀ y, ‖f y‖ ^ 2 ≤ g y) : MemLp f 2 volume :=
  (memLp_two_iff_integrable_sq_norm hf).2 (hg.mono' (hf.norm.pow 2)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (by positivity)]; exact h y))

private theorem integrable_of_sq {E : Type*} [NormedAddCommGroup E] {f : Space → E} (hf : MemLp f 2 volume)
    {g : Space → ℝ} (hg : AEStronglyMeasurable g volume) {c : ℝ} (h : ∀ y, ‖g y‖ ≤ c * ‖f y‖ ^ 2) :
    Integrable g volume :=
  (((memLp_two_iff_integrable_sq_norm hf.1).1 hf).const_mul c).mono' hg (Filter.Eventually.of_forall h)

private theorem gradient_memLp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {m : ℕ} (h : IsSecondOrderField m v G H) :
    MemLp G 2 volume :=
  memLp_two_of_sq h.measurable_gradient h.gradient_two fun y => opNorm_sq_le_entrySq _

private theorem second_memLp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {m : ℕ} (h : IsSecondOrderField m v G H) :
    MemLp H 2 volume :=
  memLp_two_of_sq h.measurable_second h.second_two fun y => opNorm_sq_le_full _


private theorem test_integrable_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    {p : ℝ≥0∞} (hf : MemLp f p volume) (hp : 1 ≤ p) {g : Space → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun y => g y • f y) volume :=
  (hf.locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport hg hgc

private theorem exists_lim {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {f : ℕ → Space → E} (hf : ∀ n, MemLp (f n) p volume)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, ∫ y, ‖f n y - f n' y‖ ^ p.toReal < ε) :
    ∃ f₀ : Space → E, MemLp f₀ p volume ∧
      Filter.Tendsto (fun n => eLpNorm (f n - f₀) p volume) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ y, ‖f n y - f₀ y‖ ^ p.toReal) Filter.atTop (nhds 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  let F : ℕ → Lp E p volume := fun n => (hf n).toLp (f n)
  have hF : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ((ε / 2) ^ p.toReal) (by positivity)
    refine ⟨N, fun n hn n' hn' => ?_⟩
    rw [Lp.dist_def, eLpNorm_congr_ae ((hf n).coeFn_toLp.sub (hf n').coeFn_toLp),
      ((hf n).sub (hf n')).eLpNorm_eq_integral_rpow_norm hp0 hpt,
      ENNReal.toReal_ofReal (by positivity)]
    have h1 : (∫ y, ‖(f n - f n') y‖ ^ p.toReal) ^ p.toReal⁻¹ ≤ ((ε / 2) ^ p.toReal) ^ p.toReal⁻¹ :=
      Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) (hN n hn n' hn').le (by positivity)
    rw [Real.rpow_rpow_inv (by positivity) hr.ne'] at h1
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hF
  have hL' : Filter.Tendsto (fun n => eLpNorm (f n - ⇑L) p volume) Filter.atTop (nhds 0) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hL
    refine hL.congr fun n => ?_
    exact eLpNorm_congr_ae ((hf n).coeFn_toLp.sub (Filter.EventuallyEq.refl _ _))
  refine ⟨L, Lp.memLp L, hL', ?_⟩
  have he : ∀ n, ∫ y, ‖f n y - L y‖ ^ p.toReal = (eLpNorm (f n - ⇑L) p volume).toReal ^ p.toReal := by
    intro n
    rw [((hf n).sub (Lp.memLp L)).eLpNorm_eq_integral_rpow_norm hp0 hpt,
      ENNReal.toReal_ofReal (by positivity), ← Real.rpow_mul (integral_nonneg fun _ => by positivity),
      inv_mul_cancel₀ hr.ne', Real.rpow_one]
    try rfl
  simp_rw [he]
  have h0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL').rpow_const (Or.inr hr.le)
  simpa [Real.zero_rpow hr.ne'] using h0

private theorem pair_lim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ≥0∞} (q : ℝ≥0∞) [ENNReal.HolderTriple q p 1] (hp : 1 ≤ p) {g : Space → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {f : ℕ → Space → E} {f₀ : Space → E} (hf : ∀ n, MemLp (f n) p volume)
    (hf₀ : MemLp f₀ p volume)
    (hlim : Filter.Tendsto (fun n => eLpNorm (f n - f₀) p volume) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ y, g y • f n y) Filter.atTop (nhds (∫ y, g y • f₀ y)) := by
  have hgq : eLpNorm g q volume < ⊤ := (hg.memLp_of_hasCompactSupport hgc).eLpNorm_lt_top
  have hbound : ∀ n, ‖(∫ y, g y • f n y) - ∫ y, g y • f₀ y‖ ≤
      (eLpNorm g q volume * eLpNorm (f n - f₀) p volume).toReal := by
    intro n
    rw [← integral_sub (test_integrable_gen (hf n) hp hg hgc) (test_integrable_gen hf₀ hp hg hgc)]
    have e : (fun y => g y • f n y - g y • f₀ y) = g • (f n - f₀) := by
      funext y
      simp [smul_sub]
    rw [e]
    calc ‖∫ y, (g • (f n - f₀)) y‖ ≤ ∫ y, ‖(g • (f n - f₀)) y‖ := norm_integral_le_integral_norm _
      _ = (eLpNorm (g • (f n - f₀)) 1 volume).toReal := by
          rw [integral_norm_eq_lintegral_enorm (hg.aestronglyMeasurable.smul ((hf n).sub hf₀).1),
            eLpNorm_one_eq_lintegral_enorm]
      _ ≤ _ := ENNReal.toReal_mono (ENNReal.mul_ne_top hgq.ne ((hf n).sub hf₀).eLpNorm_lt_top.ne)
          (eLpNorm_smul_le_mul_eLpNorm ((hf n).sub hf₀).1 hg.aestronglyMeasurable)
  have h0 : Filter.Tendsto (fun n => (eLpNorm g q volume * eLpNorm (f n - f₀) p volume).toReal)
      Filter.atTop (nhds 0) := by
    have h1 := ENNReal.Tendsto.const_mul hlim (Or.inr hgq.ne)
    rw [mul_zero] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h2
    exact h2
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound h0)

private theorem pair_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (A : E →L[ℝ] F)
    {p : ℝ≥0∞} (q : ℝ≥0∞) [ENNReal.HolderTriple q p 1] (hp : 1 ≤ p) {g : Space → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {f : ℕ → Space → E} {f₀ : Space → E} (hf : ∀ n, MemLp (f n) p volume)
    (hf₀ : MemLp f₀ p volume)
    (hlim : Filter.Tendsto (fun n => eLpNorm (f n - f₀) p volume) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ y, g y • A (f n y)) Filter.atTop (nhds (∫ y, g y • A (f₀ y))) := by
  have e : ∀ h : Space → E, MemLp h p volume → ∫ y, g y • A (h y) = A (∫ y, g y • h y) := by
    intro h hh
    rw [← A.integral_comp_comm (test_integrable_gen hh hp hg hgc)]
    simp only [map_smul]
  rw [e f₀ hf₀]
  refine ((A.continuous.tendsto _).comp (pair_lim q hp hg hgc hf hf₀ hlim)).congr fun n => ?_
  simp only [Function.comp_apply]
  exact (e _ (hf n)).symm

private theorem turnStep_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

private theorem turnStep_smul (m : ℕ) (c : ℝ) (a : Space) : turnStep m (c • a) = c • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

private theorem turnStep_norm (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, turnStep, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq (2 * π / m)

private theorem mirror_add (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply] <;> ring

private theorem mirror_smul (c : ℝ) (a : Space) : mirror (c • a) = c • mirror a := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply]

private theorem mirror_norm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]

private def turnIso (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := turnStep m, map_add' := turnStep_add m, map_smul' := turnStep_smul m,
      norm_map' := turnStep_norm m } rfl

private def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := mirror, map_add' := mirror_add, map_smul' := mirror_smul, norm_map' := mirror_norm } rfl

private theorem turnIso_coe (m : ℕ) : ⇑(turnIso m) = turnStep m := by
  unfold turnIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

private theorem mirrorIso_coe : ⇑mirrorIso = mirror := by
  unfold mirrorIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

private theorem turn_ae (m : ℕ) {P : Space → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂volume, P (turnStep m y) := by
  have h2 := (turnIso m).measurePreserving.quasiMeasurePreserving.ae h
  rwa [turnIso_coe] at h2

private theorem mirror_ae {P : Space → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂volume, P (mirror y) := by
  have h2 := mirrorIso.measurePreserving.quasiMeasurePreserving.ae h
  rwa [mirrorIso_coe] at h2

private theorem turn_continuous (m : ℕ) : Continuous (turnStep m) := turnIso_coe m ▸ (turnIso m).continuous

private theorem mirror_continuous : Continuous mirror := mirrorIso_coe ▸ mirrorIso.continuous


theorem secondOrderComplete_of (h1 : SecondSymbolEnergyStatement) (h2 : SixthGradientBoundStatement) :
    SecondOrderCompleteStatement := by
  intro m w wmin hwmin hw hwl hwu v G H hf hcau
  obtain ⟨wmax, hwmax⟩ := hwu
  obtain ⟨C, hC⟩ := h2
  haveI : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
  haveI : ENNReal.HolderTriple (1 - 6⁻¹)⁻¹ 6 1 :=
    ⟨by rw [inv_inv, inv_one, tsub_add_cancel_of_le (ENNReal.inv_le_one.2 (by norm_num))]⟩
  have hsub : ∀ {v' u : Space → Space} {G' K : Space → (Space →L[ℝ] Space)}
      {H' L : Space → (Space →L[ℝ] Space →L[ℝ] Space)}, IsSecondOrderField m v' G' H' →
      IsSecondOrderField m u K L →
      IsSecondOrderField m (fun y => v' y - u y) (fun y => G' y - K y) (fun y => H' y - L y) := by
    intro v' u G' K H' L ha hb
    have := secondOrderLinear m v' u G' K H' L (-1) ha hb
    simp only [neg_one_smul, ← sub_eq_add_neg] at this
    exact this
  have hwint : ∀ {G' : Space → (Space →L[ℝ] Space)}, Integrable (fun y => entrySq (G' y)) volume →
      Integrable (fun y => w y * entrySq (G' y)) volume := by
    intro G' hG
    refine (hG.const_mul wmax).mono' (hw.aestronglyMeasurable.mul hG.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have he : 0 ≤ entrySq (G' y) := by unfold entrySq; positivity
    rw [Real.norm_of_nonneg (mul_nonneg (hwmin.le.trans (hwl y)) he)]
    exact mul_le_mul_of_nonneg_right (hwmax y) he
  have hE : ∀ {v' : Space → Space} {G' : Space → (Space →L[ℝ] Space)}
      {H' : Space → (Space →L[ℝ] Space →L[ℝ] Space)}, IsSecondOrderField m v' G' H' →
      ∫ y, fullSecondSq (H' y) ≤ weightedEnergy w G' H' ∧
        wmin * ∫ y, entrySq (G' y) ≤ weightedEnergy w G' H' := by
    intro v' G' H' h
    obtain ⟨-, -, h3, h4⟩ := h1 m v' G' H' h
    have hA : 0 ≤ ∫ y, ‖secondTrace (H' y)‖ ^ 2 := integral_nonneg fun _ => by positivity
    have hB : wmin * ∫ y, entrySq (G' y) ≤ ∫ y, w y * entrySq (G' y) := by
      rw [← integral_const_mul]
      exact integral_mono (h.gradient_two.const_mul _) (hwint h.gradient_two) fun y =>
        mul_le_mul_of_nonneg_right (hwl y) (by unfold entrySq; positivity)
    have hB0 : 0 ≤ wmin * ∫ y, entrySq (G' y) :=
      mul_nonneg hwmin.le (integral_nonneg fun _ => by unfold entrySq; positivity)
    unfold weightedEnergy
    constructor
    · rw [h3, ← h4]; linarith
    · linarith
  have hGm : ∀ n, MemLp (G n) 2 volume := fun n => gradient_memLp (hf n)
  have hHm : ∀ n, MemLp (H n) 2 volume := fun n => second_memLp (hf n)
  have hvm : ∀ n, MemLp (v n) 6 volume := fun n => (hf n).velocity_six
  have hr2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  have hr6 : (6 : ℝ≥0∞).toReal = ((6 : ℕ) : ℝ) := by norm_num
  obtain ⟨G₀, hG₀, hGl, hGi⟩ := exists_lim (p := 2) (by norm_num) (by norm_num) hGm (by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (wmin * ε) (by positivity)
    refine ⟨N, fun n hn n' hn' => ?_⟩
    rw [hr2]
    simp only [Real.rpow_natCast]
    have hd := hsub (hf n) (hf n')
    have hb := (hE hd).2
    have hlt := hN n hn n' hn'
    have hint : ∫ y, ‖G n y - G n' y‖ ^ 2 ≤ ∫ y, entrySq (G n y - G n' y) :=
      integral_mono ((memLp_two_iff_integrable_sq_norm (gradient_memLp hd).1).1 (gradient_memLp hd))
        hd.gradient_two fun y => opNorm_sq_le_entrySq _
    have hlt2 : ∫ y, entrySq (G n y - G n' y) < ε := by
      by_contra hcon
      push_neg at hcon
      have := mul_le_mul_of_nonneg_left hcon hwmin.le
      linarith
    linarith)
  obtain ⟨H₀, hH₀, hHl, hHi⟩ := exists_lim (p := 2) (by norm_num) (by norm_num) hHm (by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun n hn n' hn' => ?_⟩
    rw [hr2]
    simp only [Real.rpow_natCast]
    have hd := hsub (hf n) (hf n')
    have hint : ∫ y, ‖H n y - H n' y‖ ^ 2 ≤ ∫ y, fullSecondSq (H n y - H n' y) :=
      integral_mono ((memLp_two_iff_integrable_sq_norm (second_memLp hd).1).1 (second_memLp hd))
        hd.second_two fun y => opNorm_sq_le_full _
    linarith [(hE hd).1, hN n hn n' hn'])
  obtain ⟨v₀, hv₀, hvl, hvi⟩ := exists_lim (p := 6) (by norm_num) (by norm_num) hvm (by
    intro ε hε
    set Cp := max C 1
    have hCp : 0 < Cp := lt_of_lt_of_le one_pos (le_max_right _ _)
    set η := min 1 (ε / (Cp + 1))
    have hη : 0 < η := lt_min one_pos (by positivity)
    obtain ⟨N, hN⟩ := hcau (wmin * η) (by positivity)
    refine ⟨N, fun n hn n' hn' => ?_⟩
    rw [hr6]
    simp only [Real.rpow_natCast]
    have hd := hsub (hf n) (hf n')
    have hS := hC _ _ hd.measurable_velocity hd.velocity_six hd.gradient_two hd.weak_gradient
    beta_reduce at hS
    have ht0 : 0 ≤ ∫ y, entrySq (G n y - G n' y) := integral_nonneg fun _ => by unfold entrySq; positivity
    have htη : ∫ y, entrySq (G n y - G n' y) < η := by
      have a1 := (hE hd).2
      have a2 := hN n hn n' hn'
      by_contra hcon
      push_neg at hcon
      have := mul_le_mul_of_nonneg_left hcon hwmin.le
      linarith
    have ht1 : ∫ y, entrySq (G n y - G n' y) ≤ 1 := htη.le.trans (min_le_left _ _)
    have ht3 : (∫ y, entrySq (G n y - G n' y)) ^ 3 ≤ ∫ y, entrySq (G n y - G n' y) :=
      pow_le_of_le_one ht0 ht1 (by norm_num)
    have hηε : η ≤ ε / (Cp + 1) := min_le_right _ _
    have hCt : C * (∫ y, entrySq (G n y - G n' y)) ^ 3 ≤ Cp * ∫ y, entrySq (G n y - G n' y) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left ht3 hCp.le)
    have hlast : Cp * ∫ y, entrySq (G n y - G n' y) < ε := by
      calc Cp * ∫ y, entrySq (G n y - G n' y) ≤ Cp * η := mul_le_mul_of_nonneg_left htη.le hCp.le
        _ ≤ Cp * (ε / (Cp + 1)) := mul_le_mul_of_nonneg_left hηε hCp.le
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
    linarith)
  have hfield : IsSecondOrderField m v₀ G₀ H₀ := by
    refine ⟨hv₀.1, hG₀.1, hH₀.1, hv₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact integrable_of_sq hG₀ (entrySq_continuous.comp_aestronglyMeasurable hG₀.1) (c := 3) fun y => by
        rw [Real.norm_of_nonneg (by unfold entrySq; positivity)]
        exact entrySq_le _
    · exact integrable_of_sq hH₀ (fullSq_continuous.comp_aestronglyMeasurable hH₀.1) (c := 9) fun y => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact full_le _
    · intro φ hφ j
      have hc := deriv_test_continuous hφ j
      have hs := deriv_test_support hφ j
      have lim1 := pair_lim (1 - 6⁻¹)⁻¹ (by norm_num) hc hs hvm hv₀ hvl
      have lim2 := (pair_clm (ContinuousLinearMap.apply ℝ Space (unitVector j)) 2 (by norm_num)
        hφ.1.continuous hφ.2 hGm hG₀ hGl).neg
      exact tendsto_nhds_unique lim1 (lim2.congr fun n => ((hf n).weak_gradient φ hφ j).symm)
    · intro φ hφ i j
      have hc := deriv_test_continuous hφ j
      have hs := deriv_test_support hφ j
      have lim1 := pair_clm (ContinuousLinearMap.apply ℝ Space (unitVector i)) 2 (by norm_num) hc hs
        hGm hG₀ hGl
      have lim2 := (pair_clm ((ContinuousLinearMap.apply ℝ Space (unitVector i)).comp
        (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j))) 2 (by norm_num)
        hφ.1.continuous hφ.2 hHm hH₀ hHl).neg
      exact tendsto_nhds_unique lim1 (lim2.congr fun n => ((hf n).weak_second φ hφ i j).symm)
    · obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun n => (hGm n).1)
        hG₀.1 hGl).exists_seq_tendsto_ae
      filter_upwards [hns, ae_all_iff.2 fun k => (hf (ns k)).divergence] with y hy hd
      have hcont : Continuous (fun L : Space →L[ℝ] Space =>
          ∑ i : Fin 3, inner ℝ (L (unitVector i)) (unitVector i)) :=
        continuous_finsetSum _ fun i _ => (continuous_id.clm_apply continuous_const).inner continuous_const
      have h3 := (hcont.tendsto _).comp hy
      refine tendsto_nhds_unique h3 ?_
      simp only [Function.comp_def, hd]
      exact tendsto_const_nhds
    · obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun n => (hvm n).1)
        hv₀.1 hvl).exists_seq_tendsto_ae
      refine ⟨?_, ?_⟩
      · filter_upwards [hns, turn_ae m hns, ae_all_iff.2 fun k => (hf (ns k)).symmetric.1] with y hy hy' hk
        refine tendsto_nhds_unique hy' ?_
        simp only [hk]
        exact ((turn_continuous m).tendsto _).comp hy
      · filter_upwards [hns, mirror_ae hns, ae_all_iff.2 fun k => (hf (ns k)).symmetric.2] with y hy hy' hk
        refine tendsto_nhds_unique hy' ?_
        simp only [hk]
        exact (mirror_continuous.tendsto _).comp hy
  refine ⟨v₀, G₀, H₀, hfield, ?_, ?_⟩
  · rw [hr2] at hGi hHi
    simp only [Real.rpow_natCast] at hGi hHi
    have hbd : ∀ n, weightedEnergy w (fun y => G n y - G₀ y) (fun y => H n y - H₀ y) ≤
        9 * (∫ y, ‖H n y - H₀ y‖ ^ 2) + 3 * wmax * ∫ y, ‖G n y - G₀ y‖ ^ 2 := by
      intro n
      have hd := hsub (hf n) hfield
      have hGd := gradient_memLp hd
      have hHd := second_memLp hd
      have iG := (memLp_two_iff_integrable_sq_norm hGd.1).1 hGd
      have iH := (memLp_two_iff_integrable_sq_norm hHd.1).1 hHd
      unfold weightedEnergy
      have a1 : ∫ y, ‖secondTrace (H n y - H₀ y)‖ ^ 2 ≤ ∫ y, 9 * ‖H n y - H₀ y‖ ^ 2 :=
        integral_mono (integrable_of_sq hHd (trace_sq_continuous.comp_aestronglyMeasurable hHd.1) (c := 9)
          fun y => by rw [Real.norm_of_nonneg (by positivity)]; exact trace_le _) (iH.const_mul 9)
          fun y => trace_le _
      have a2 : ∫ y, w y * entrySq (G n y - G₀ y) ≤ ∫ y, 3 * wmax * ‖G n y - G₀ y‖ ^ 2 :=
        integral_mono (hwint hd.gradient_two) (iG.const_mul _) fun y => by
          have he : 0 ≤ entrySq (G n y - G₀ y) := by unfold entrySq; positivity
          have hwm : 0 ≤ wmax := hwmin.le.trans ((hwl y).trans (hwmax y))
          calc w y * entrySq (G n y - G₀ y) ≤ wmax * (3 * ‖G n y - G₀ y‖ ^ 2) :=
                mul_le_mul (hwmax y) (entrySq_le _) he hwm
            _ = 3 * wmax * ‖G n y - G₀ y‖ ^ 2 := by ring
      rw [integral_const_mul] at a1 a2
      linarith
    have hnn : ∀ n, 0 ≤ weightedEnergy w (fun y => G n y - G₀ y) (fun y => H n y - H₀ y) := fun n =>
      add_nonneg (integral_nonneg fun _ => by positivity)
        (integral_nonneg fun y => mul_nonneg (hwmin.le.trans (hwl y)) (by unfold entrySq; positivity))
    have hlim0 := (hHi.const_mul 9).add (hGi.const_mul (3 * wmax))
    simp only [mul_zero, add_zero] at hlim0
    exact squeeze_zero hnn hbd hlim0
  · rw [hr6] at hvi
    simp only [Real.rpow_natCast] at hvi
    exact hvi

end SteadyCert

end Breakdown
