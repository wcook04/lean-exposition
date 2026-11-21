import Breakdown.Cert.CoerciveNodes

open scoped ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SumSecondPartialsPairing

namespace Internal

def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def cutoff (n : ℕ) (y : Space) : ℝ := bump ((((n : ℝ) + 1)⁻¹) • y)

def flux (p q : Space → Space) (l : Fin 3) (y : Space) : ℝ :=
  inner ℝ (fderiv ℝ p y (unitVector l)) (q y) - inner ℝ (fderiv ℝ q y (unitVector l)) (p y)

lemma scale_pos (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity

lemma norm_unitVector (l : Fin 3) : ‖unitVector l‖ = 1 := by
  simp [unitVector]

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ 1 (cutoff n) :=
  (bump.contDiff (n := 1)).comp (contDiff_const_smul _)

lemma cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff n) :=
  bump.hasCompactSupport.comp_smul (scale_pos n).ne'

lemma cutoff_eq_one {n : ℕ} {y : Space} (hy : ‖y‖ ≤ (n : ℝ) + 1) : cutoff n y = 1 := by
  unfold cutoff
  apply bump.one_of_mem_closedBall
  show _ ∈ Metric.closedBall (0 : Space) 1
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos n)]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [inv_mul_le_iff₀ hn]
  simpa using hy

lemma abs_cutoff_le (n : ℕ) (y : Space) : |cutoff n y| ≤ 1 := by
  unfold cutoff
  rw [abs_of_nonneg bump.nonneg]
  exact bump.le_one

lemma cutoff_eventually_one (y : Space) : ∀ᶠ n : ℕ in atTop, cutoff n y = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply cutoff_eq_one
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma fderiv_cutoff_eq_zero {n : ℕ} {y : Space} (hy : ‖y‖ < (n : ℝ) + 1) :
    fderiv ℝ (cutoff n) y = 0 := by
  have h : cutoff n =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    have hmem : y ∈ Metric.ball (0 : Space) ((n : ℝ) + 1) := by simpa using hy
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with z hz
    exact cutoff_eq_one (le_of_lt (by simpa using hz))
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

lemma fderiv_cutoff_eventually_zero (y : Space) :
    ∀ᶠ n : ℕ in atTop, fderiv ℝ (cutoff n) y = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply fderiv_cutoff_eq_zero
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma exists_fderiv_bump_bound : ∃ C, ∀ z, ‖fderiv ℝ bump z‖ ≤ C :=
  ((bump.contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (bump.hasCompactSupport.fderiv ℝ)

lemma hasFDerivAt_cutoff (n : ℕ) (y : Space) :
    HasFDerivAt (cutoff n) ((((n : ℝ) + 1)⁻¹) • fderiv ℝ bump ((((n : ℝ) + 1)⁻¹) • y)) y := by
  have hb : HasFDerivAt bump (fderiv ℝ bump ((((n : ℝ) + 1)⁻¹) • y)) ((((n : ℝ) + 1)⁻¹) • y) :=
    (((bump.contDiff (n := 1)).differentiable one_ne_zero) _).hasFDerivAt
  have h : HasFDerivAt (fun x => bump ((((n : ℝ) + 1)⁻¹) • x))
      ((fderiv ℝ bump ((((n : ℝ) + 1)⁻¹) • y)).comp
        ((((n : ℝ) + 1)⁻¹) • ContinuousLinearMap.id ℝ Space)) y :=
    hb.comp y ((hasFDerivAt_id y).const_smul (((n : ℝ) + 1)⁻¹))
  refine h.congr_fderiv ?_
  ext v
  simp

lemma norm_fderiv_cutoff_le {C : ℝ} (hC : ∀ z, ‖fderiv ℝ bump z‖ ≤ C) (n : ℕ) (y : Space) :
    ‖fderiv ℝ (cutoff n) y‖ ≤ 3 * C / (1 + ‖y‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hy0 : (0 : ℝ) < 1 + ‖y‖ := by positivity
  rw [(hasFDerivAt_cutoff n y).fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos n)]
  by_cases h : (((n : ℝ) + 1)⁻¹) • y ∈ tsupport bump
  · rw [bump.tsupport_eq] at h
    change (((n : ℝ) + 1)⁻¹) • y ∈ Metric.closedBall (0 : Space) 2 at h
    have h2 : ‖(((n : ℝ) + 1)⁻¹) • y‖ ≤ 2 := by simpa using h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos n), inv_mul_le_iff₀ hn] at h2
    have h3 : 1 + ‖y‖ ≤ 3 * ((n : ℝ) + 1) := by nlinarith
    rw [le_div_iff₀ hy0]
    calc ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ bump ((((n : ℝ) + 1)⁻¹) • y)‖ * (1 + ‖y‖)
        ≤ ((n : ℝ) + 1)⁻¹ * C * (3 * ((n : ℝ) + 1)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hC _) (scale_pos n).le) h3 hy0.le
          exact mul_nonneg (scale_pos n).le hC0
      _ = 3 * C := by field_simp
  · rw [fderiv_of_notMem_tsupport ℝ h]
    simp only [norm_zero, mul_zero]
    positivity

lemma integral_fderiv_mul_eq {a : Space → ℝ} {K : NNReal} (ha : LipschitzWith K a) {g : Space → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Space) :
    ∫ y, fderiv ℝ a y v * g y = -∫ y, a y * fderiv ℝ g y v := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg one_ne_zero
  have h := ha.integral_lineDeriv_mul_eq hD hgc v (μ := volume)
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have e1 : ∫ y, fderiv ℝ a y v * g y = ∫ y, lineDeriv ℝ a y v * g y := by
    apply integral_congr_ae
    filter_upwards [ha.ae_differentiableAt (μ := volume)] with y hy
    rw [hy.lineDeriv_eq_fderiv]
  rw [e1, h, ← integral_neg]
  congr 1
  ext y
  rw [(hdiff y).lineDeriv_eq_fderiv, map_neg]
  ring

lemma contDiff_fderiv_apply {p : Space → Space} (hp : ContDiff ℝ 2 p) (v : Space) :
    ContDiff ℝ 1 (fun y => fderiv ℝ p y v) :=
  (hp.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma flux_contDiff {p q : Space → Space} (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (l : Fin 3) :
    ContDiff ℝ 1 (flux p q l) :=
  ((contDiff_fderiv_apply hp (unitVector l)).inner ℝ (hq.of_le (by norm_num))).sub
    ((contDiff_fderiv_apply hq (unitVector l)).inner ℝ (hp.of_le (by norm_num)))

lemma hasFDerivAt_fderiv_apply {p : Space → Space} (hp : ContDiff ℝ 2 p) (v y : Space) :
    HasFDerivAt (fun x => fderiv ℝ p x v) ((fderiv ℝ (fun x => fderiv ℝ p x) y).flip v) y := by
  have h1 : HasFDerivAt (fun x => fderiv ℝ p x) (fderiv ℝ (fun x => fderiv ℝ p x) y) y :=
    (((hp.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y).hasFDerivAt
  have h2 := h1.clm_apply (hasFDerivAt_const v y)
  simpa using h2

lemma fderiv_flux_apply {p q : Space → Space} (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q)
    (l : Fin 3) (y : Space) :
    fderiv ℝ (flux p q l) y (unitVector l) =
      inner ℝ (fderiv ℝ (fun x => fderiv ℝ p x) y (unitVector l) (unitVector l)) (q y)
      - inner ℝ (fderiv ℝ (fun x => fderiv ℝ q x) y (unitVector l) (unitVector l)) (p y) := by
  have hpd : HasFDerivAt p (fderiv ℝ p y) y :=
    ((hp.differentiable (by norm_num)) y).hasFDerivAt
  have hqd : HasFDerivAt q (fderiv ℝ q y) y :=
    ((hq.differentiable (by norm_num)) y).hasFDerivAt
  have h := ((hasFDerivAt_fderiv_apply hp (unitVector l) y).inner ℝ hqd).sub
    ((hasFDerivAt_fderiv_apply hq (unitVector l) y).inner ℝ hpd)
  have e : flux p q l = (fun x => inner ℝ (fderiv ℝ p x (unitVector l)) (q x))
      - (fun x => inner ℝ (fderiv ℝ q x (unitVector l)) (p x)) := rfl
  rw [e, h.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.flip_apply]
  rw [real_inner_comm (fderiv ℝ p y (unitVector l)) (fderiv ℝ q y (unitVector l))]
  ring

lemma sum_fderiv_flux {p q : Space → Space} (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (y : Space) :
    ∑ l : Fin 3, fderiv ℝ (flux p q l) y (unitVector l) =
      inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y)) (q y)
      - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y)) (p y) := by
  simp only [fderiv_flux_apply hp hq, secondDerivTrace, sum_inner, Finset.sum_sub_distrib]

lemma abs_flux_le (p q : Space → Space) (l : Fin 3) (y : Space) :
    |flux p q l y| ≤ ‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖ := by
  unfold flux
  have e1 : |inner ℝ (fderiv ℝ p y (unitVector l)) (q y)| ≤ ‖fderiv ℝ p y‖ * ‖q y‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    simpa [norm_unitVector] using (fderiv ℝ p y).le_opNorm (unitVector l)
  have e2 : |inner ℝ (fderiv ℝ q y (unitVector l)) (p y)| ≤ ‖fderiv ℝ q y‖ * ‖p y‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    simpa [norm_unitVector] using (fderiv ℝ q y).le_opNorm (unitVector l)
  exact (abs_sub _ _).trans (add_le_add e1 e2)

lemma abs_fderiv_apply_le (f : Space → ℝ) (l : Fin 3) (y : Space) :
    |fderiv ℝ f y (unitVector l)| ≤ ‖fderiv ℝ f y‖ := by
  simpa [norm_unitVector] using (fderiv ℝ f y).le_opNorm (unitVector l)

lemma pairing_identity {a : Space → ℝ} {K : NNReal} (ha : LipschitzWith K a)
    {p q : Space → Space} (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (n : ℕ) :
    (Integrable (fun y => ∑ l : Fin 3, a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l)))) ∧
    (Integrable (fun y => ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * (cutoff n y * flux p q l y))) ∧
    (Integrable (fun y => ∑ l : Fin 3, a y * (flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)))) ∧
    ∫ y, ∑ l : Fin 3, a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l)) =
      -(∫ y, ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * (cutoff n y * flux p q l y))
      - ∫ y, ∑ l : Fin 3, a y * (flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)) := by
  have hχ := cutoff_contDiff n
  have hχc := cutoff_hasCompactSupport n
  have hac : Continuous a := ha.continuous
  have hflux := flux_contDiff hp hq
  have I1 : ∀ l : Fin 3, Integrable (fun y => a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l))) := by
    intro l
    apply Continuous.integrable_of_hasCompactSupport
    · exact hac.mul (hχ.continuous.mul (((hflux l).continuous_fderiv one_ne_zero).clm_apply continuous_const))
    · exact (hχc.mul_right).mul_left
  have I2 : ∀ l : Fin 3, Integrable (fun y => fderiv ℝ a y (unitVector l) * (cutoff n y * flux p q l y)) := by
    intro l
    have hg : Integrable (fun y => cutoff n y * flux p q l y) :=
      Continuous.integrable_of_hasCompactSupport (hχ.continuous.mul (hflux l).continuous) hχc.mul_right
    refine hg.bdd_mul (c := (K : ℝ)) (measurable_fderiv_apply_const ℝ a (unitVector l)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact (abs_fderiv_apply_le a l y).trans (norm_fderiv_le_of_lipschitz ℝ ha)
  have I3 : ∀ l : Fin 3, Integrable (fun y => a y * (flux p q l y * fderiv ℝ (cutoff n) y (unitVector l))) := by
    intro l
    apply Continuous.integrable_of_hasCompactSupport
    · exact hac.mul ((hflux l).continuous.mul ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const))
    · exact ((hχc.fderiv_apply ℝ (unitVector l)).mul_left).mul_left
  refine ⟨integrable_finsetSum _ fun l _ => I1 l, integrable_finsetSum _ fun l _ => I2 l,
    integrable_finsetSum _ fun l _ => I3 l, ?_⟩
  rw [integral_finsetSum _ fun l _ => I1 l, integral_finsetSum _ fun l _ => I2 l,
    integral_finsetSum _ fun l _ => I3 l, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hg : ContDiff ℝ 1 (fun y => cutoff n y * flux p q l y) := hχ.mul (hflux l)
  have hgc : HasCompactSupport (fun y => cutoff n y * flux p q l y) := hχc.mul_right
  have ibp := integral_fderiv_mul_eq ha hg hgc (unitVector l)
  have hderiv : ∀ y, a y * fderiv ℝ (fun y => cutoff n y * flux p q l y) y (unitVector l) =
      a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l))
        + a y * (flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)) := by
    intro y
    rw [fderiv_fun_mul ((hχ.differentiable one_ne_zero) y) (((hflux l).differentiable one_ne_zero) y)]
    simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hderiv] at ibp
  rw [integral_add (I1 l) (I3 l)] at ibp
  linarith

end Internal

end SumSecondPartialsPairing

open SumSecondPartialsPairing.Internal in
theorem weightedSumSecondPartialsPairingHolds_proof : WeightedSumSecondPartialsPairingHolds := by
  intro a K p q ha hp hq h1 h2 h3
  obtain ⟨C, hC⟩ := exists_fderiv_bump_bound
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hid := pairing_identity ha hp hq
  set D : Space → ℝ := fun y => inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y)) (q y)
      - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y)) (p y) with hD
  set B : Space → ℝ := fun y => ‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖ with hB
  have hF : ∀ n y, ∑ l : Fin 3, a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l)) =
      cutoff n y * (a y * D y) := by
    intro n y
    simp only [hD]
    rw [← sum_fderiv_flux hp hq y, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hG : ∀ n y, ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * (cutoff n y * flux p q l y) =
      cutoff n y * ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * flux p q l y := by
    intro n y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hH : ∀ n y, ∑ l : Fin 3, a y * (flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)) =
      a y * ∑ l : Fin 3, flux p q l y * fderiv ℝ (cutoff n) y (unitVector l) := by
    intro n y
    rw [Finset.mul_sum]
  have hSbound : ∀ y, ‖∑ l : Fin 3, fderiv ℝ a y (unitVector l) * flux p q l y‖ ≤
      3 * (‖fderiv ℝ a y‖ * B y) := by
    intro y
    calc ‖∑ l : Fin 3, fderiv ℝ a y (unitVector l) * flux p q l y‖
        ≤ ∑ l : Fin 3, ‖fderiv ℝ a y (unitVector l) * flux p q l y‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin 3, ‖fderiv ℝ a y‖ * B y := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul (abs_fderiv_apply_le a l y) (abs_flux_le p q l y) (abs_nonneg _)
            (norm_nonneg _)
      _ = 3 * (‖fderiv ℝ a y‖ * B y) := by simp
  have hTbound : ∀ n y, ‖a y * ∑ l : Fin 3, flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)‖ ≤
      9 * C * (|a y| * B y / (1 + ‖y‖)) := by
    intro n y
    have hy0 : (0 : ℝ) < 1 + ‖y‖ := by positivity
    have hB0 : 0 ≤ B y := by simp only [hB]; positivity
    have hs : ‖∑ l : Fin 3, flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)‖ ≤
        3 * (B y * (3 * C / (1 + ‖y‖))) := by
      calc ‖∑ l : Fin 3, flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)‖
          ≤ ∑ l : Fin 3, ‖flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)‖ := norm_sum_le _ _
        _ ≤ ∑ _l : Fin 3, B y * (3 * C / (1 + ‖y‖)) := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            exact mul_le_mul (abs_flux_le p q l y)
              ((abs_fderiv_apply_le (cutoff n) l y).trans (norm_fderiv_cutoff_le hC n y))
              (abs_nonneg _) hB0
        _ = 3 * (B y * (3 * C / (1 + ‖y‖))) := by simp
    rw [norm_mul, Real.norm_eq_abs]
    calc |a y| * ‖∑ l : Fin 3, flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)‖
        ≤ |a y| * (3 * (B y * (3 * C / (1 + ‖y‖)))) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = 9 * C * (|a y| * B y / (1 + ‖y‖)) := by ring
  have limF : Tendsto (fun n : ℕ => ∫ y, ∑ l : Fin 3, a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l)))
      atTop (𝓝 (∫ y, a y * D y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖a y * D y‖)
      (fun n => (hid n).1.aestronglyMeasurable) h1.norm (fun n => ?_) ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [hF n y, norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_cutoff_le n y)
    · refine Filter.Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [cutoff_eventually_one y] with n hn
      rw [hF n y, hn, one_mul]
  have limG : Tendsto (fun n : ℕ => ∫ y, ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * (cutoff n y * flux p q l y))
      atTop (𝓝 (∫ y, ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * flux p q l y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => 3 * (‖fderiv ℝ a y‖ * B y))
      (fun n => (hid n).2.1.aestronglyMeasurable) (h2.const_mul 3) (fun n => ?_) ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [hG n y, norm_mul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (abs_cutoff_le n y)).trans (hSbound y)
    · refine Filter.Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [cutoff_eventually_one y] with n hn
      rw [hG n y, hn, one_mul]
  have limH : Tendsto (fun n : ℕ => ∫ y, ∑ l : Fin 3, a y * (flux p q l y * fderiv ℝ (cutoff n) y (unitVector l)))
      atTop (𝓝 (∫ _y : Space, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => 9 * C * (|a y| * B y / (1 + ‖y‖)))
      (fun n => (hid n).2.2.1.aestronglyMeasurable) (h3.const_mul (9 * C)) (fun n => ?_) ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [hH n y]
      exact hTbound n y
    · refine Filter.Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [fderiv_cutoff_eventually_zero y] with n hn
      rw [hH n y, hn]
      simp
  rw [integral_zero] at limH
  have lim2 := (limG.neg).sub limH
  have lim3 : Tendsto (fun n : ℕ => ∫ y, ∑ l : Fin 3, a y * (cutoff n y * fderiv ℝ (flux p q l) y (unitVector l)))
      atTop (𝓝 (-(∫ y, ∑ l : Fin 3, fderiv ℝ a y (unitVector l) * flux p q l y) - 0)) :=
    lim2.congr fun n => ((hid n).2.2.2).symm
  have e := tendsto_nhds_unique limF lim3
  rw [sub_zero] at e
  exact e

end Coercive

end Breakdown
