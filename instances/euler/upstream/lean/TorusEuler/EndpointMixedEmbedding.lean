import TorusEuler.EndpointMeanFubini
import TorusEuler.EndpointSpaceCompatibility
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The mixed-space to joint-space embedding used in Appendix A.2. -/

open Filter MeasureTheory Set
open scoped InnerProductSpace Topology

namespace TorusEuler

local notation "A" => UnitAddTorus (Fin 3)
local notation "ν" => unitTorusMeasure
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Vt(" T ")" => Lp Vec3 2 (μt T)
local notation "W(" T ")" => HalfHolder A (Vt(T))
local infixr:25 " →ₛ " => SimpleFunc

private theorem endpointPath_norm_sq {T : ℝ} (v : Vt(T)) :
    ‖v‖ ^ 2 = ∫ t, ‖v t‖ ^ 2 ∂μt T := by
  rw [← real_inner_self_eq_norm_sq v, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem endpointJoint_norm_sq_of_slices {T : ℝ} (v : EndpointTorusL2 T)
    (f : A → Vt(T))
    (hf : ∀ᵐ a ∂ν, (fun t => f a t) =ᵐ[μt T] fun t => v (t, a)) :
    ‖v‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂ν := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  rw [← real_inner_self_eq_norm_sq v, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  change (∫ q : ℝ × A, ‖v q‖ ^ 2 ∂(μt T).prod ν) = _
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hf] with a ha
  rw [endpointPath_norm_sq]
  apply integral_congr_ae
  filter_upwards [ha] with t ht
  rw [ht]

/-- Joint time–space paths are equal when their time slices agree almost
everywhere at almost every spatial label. -/
theorem endpointJoint_eq_of_slices {T : ℝ} {v u : EndpointTorusL2 T}
    (h : ∀ᵐ a ∂ν, (fun t => v (t, a)) =ᵐ[μt T] fun t => u (t, a)) : v = u := by
  apply Lp.ext
  change ∀ᵐ q ∂(μt T).prod ν, v q = u q
  have hm : MeasurableSet {q : ℝ × A | v q = u q} :=
    (Lp.stronglyMeasurable v).measurableSet_eq_fun (Lp.stronglyMeasurable u)
  exact (Measure.ae_prod_iff_ae_ae hm).2 ((Measure.ae_ae_comm hm).2 h)

private noncomputable def endpointSimpleJoint {T : ℝ} (s : A →ₛ Vt(T))
    {M : ℝ} (hs : ∀ a, ‖s a‖ ≤ M) : EndpointTorusL2 T := by
  let F (q : ℝ × A) := s q.2 q.1
  have hFM : Measurable F := (s.comp Prod.snd measurable_snd).measurable_bind
    (fun v q => v q.1) (fun v => (Lp.stronglyMeasurable v).measurable.comp measurable_fst)
  have hsq : Integrable (fun q => ‖F q‖ ^ 2) ((μt T).prod ν) := by
    apply (integrable_prod_iff' (hFM.norm.pow_const 2).aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun a =>
        (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (s a))).mp (Lp.memLp (s a))
    · have hEq (a : A) : (∫ t, ‖‖F (t, a)‖ ^ 2‖ ∂μt T) = ‖s a‖ ^ 2 := by
        rw [endpointPath_norm_sq (s a)]
        exact integral_congr_ae (ae_of_all _ fun t =>
          Real.norm_of_nonneg (sq_nonneg ‖F (t, a)‖))
      simp_rw [hEq]
      apply (integrable_const (M ^ 2)).mono
      · exact (s.stronglyMeasurable.norm.measurable.pow_const 2).aestronglyMeasurable
      · exact ae_of_all _ fun a => by
          rw [Real.norm_of_nonneg (sq_nonneg ‖s a‖), Real.norm_of_nonneg (sq_nonneg M)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hs a) 2
  exact ((memLp_two_iff_integrable_sq_norm hFM.aestronglyMeasurable).mpr hsq).toLp F

private theorem endpointSimpleJoint_slices {T : ℝ} (s : A →ₛ Vt(T))
    {M : ℝ} (hs : ∀ a, ‖s a‖ ≤ M) :
    ∀ᵐ a ∂ν, (fun t => endpointSimpleJoint s hs (t, a)) =ᵐ[μt T] fun t => s a t := by
  unfold endpointSimpleJoint
  exact ae_endpointTimeSlice_congr (MemLp.coeFn_toLp _)

private theorem integrable_path_diff_sq {T : ℝ} {f g : A → Vt(T)} {M : ℝ}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfb : ∀ a, ‖f a‖ ≤ M) (hgb : ∀ a, ‖g a‖ ≤ M) :
    Integrable (fun a => ‖f a - g a‖ ^ 2) ν := by
  apply (integrable_const ((M + M) ^ 2)).mono
  · exact ((hf.sub hg).norm.measurable.pow_const 2).aestronglyMeasurable
  · exact ae_of_all _ fun a => by
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hfb a) (hgb a))) 2

private theorem endpointJoint_sub_slices {T : ℝ} {v u : EndpointTorusL2 T}
    {f g : A → Vt(T)}
    (hv : ∀ᵐ a ∂ν, (fun t => v (t, a)) =ᵐ[μt T] fun t => f a t)
    (hu : ∀ᵐ a ∂ν, (fun t => u (t, a)) =ᵐ[μt T] fun t => g a t) :
    ∀ᵐ a ∂ν, (fun t => (f a - g a : Vt(T)) t) =ᵐ[μt T]
      fun t => (v - u : EndpointTorusL2 T) (t, a) := by
  filter_upwards [hv, hu, ae_endpointTimeSlice_congr (Lp.coeFn_sub v u)] with a ha hb hc
  filter_upwards [ha, hb, hc, Lp.coeFn_sub (f a) (g a)] with t hva hua hJ hfg
  simpa only [Pi.sub_apply] using hfg.trans ((congrArg₂ (· - ·) hva hua).symm.trans hJ.symm)

private theorem mixedApprox_tendsto_integral {T : ℝ} {f : A → Vt(T)}
    (hf : StronglyMeasurable f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ a, ‖f a‖ ≤ M)
    (s : ℕ → A →ₛ Vt(T)) (hs : ∀ n, s n = hf.approxBounded M n) :
    Tendsto (fun n => ∫ a, ‖s n a - f a‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have hco (n : ℕ) (a : A) : ‖s n a‖ ≤ M := by
    rw [hs n]
    exact hf.norm_approxBounded_le hM n a
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun n a => ‖s n a - f a‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => (M + M) ^ 2)
    (fun n => (integrable_path_diff_sq (s n).stronglyMeasurable hf (hco n) hb).aestronglyMeasurable)
    (integrable_const _)
  simpa only [integral_zero] using h
    (fun n => ae_of_all _ fun a => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sub_le _ _).trans (add_le_add (hco n a) (hb a))) 2)
    (ae_of_all _ fun a => by
      have hl : Tendsto (fun n => s n a) atTop (𝓝 (f a)) := by
        simpa only [hs] using hf.tendsto_approxBounded_of_norm_le (hb a)
      simpa using ((hl.sub tendsto_const_nhds).norm.pow 2 :
        Tendsto (fun n => ‖s n a - f a‖ ^ 2) atTop (𝓝 (‖f a - f a‖ ^ 2))))

private theorem mixedApprox_approximates_joint {T : ℝ}
    (f : A → Vt(T)) (hf : StronglyMeasurable f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ a, ‖f a‖ ≤ M) :
    ∃ v : EndpointTorusL2 T, ∀ᵐ a ∂ν,
      (fun t => f a t) =ᵐ[μt T] fun t => v (t, a) := by
  let s := hf.approxBounded M
  have hco (n : ℕ) : ∀ a, ‖s n a‖ ≤ M := hf.norm_approxBounded_le hM n
  let J (n : ℕ) := endpointSimpleJoint (s n) (hco n)
  have hJ (n : ℕ) := endpointSimpleJoint_slices (s n) (hco n)
  let I (n : ℕ) := ∫ a, ‖s n a - f a‖ ^ 2 ∂ν
  have hI (n : ℕ) := integrable_path_diff_sq (s n).stronglyMeasurable hf (hco n) hb
  have hdct : Tendsto I atTop (𝓝 0) :=
    mixedApprox_tendsto_integral hf hM hb s (fun _ => rfl)
  have hpair (n m : ℕ) : ‖J n - J m‖ ^ 2 ≤ 2 * (I n + I m) := by
    rw [endpointJoint_norm_sq_of_slices _ _ (endpointJoint_sub_slices (hJ n) (hJ m))]
    calc
      (∫ a, ‖s n a - s m a‖ ^ 2 ∂ν) ≤
          ∫ a, 2 * (‖s n a - f a‖ ^ 2 + ‖s m a - f a‖ ^ 2) ∂ν := by
        apply integral_mono_ae (integrable_path_diff_sq
          (s n).stronglyMeasurable (s m).stronglyMeasurable (hco n) (hco m))
          (((hI n).add (hI m)).const_mul 2)
        exact ae_of_all _ fun a => by
          have htri := dist_triangle_right (s n a) (s m a) (f a)
          simp only [dist_eq_norm] at htri
          refine (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans ?_
          change (‖s n a - f a‖ + ‖s m a - f a‖) ^ 2 ≤
            2 * (‖s n a - f a‖ ^ 2 + ‖s m a - f a‖ ^ 2)
          nlinarith [sq_nonneg (‖s n a - f a‖ - ‖s m a - f a‖)]
      _ = _ := by rw [integral_const_mul, integral_add (hI n) (hI m)]
  have hc : CauchySeq J := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hdct.eventually (gt_mem_nhds (show 0 < ε ^ 2 / 4 by positivity)))
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [dist_eq_norm]
    by_contra! hbad
    have hsq := pow_le_pow_left₀ hε.le hbad 2
    nlinarith [hpair n m, hN n hn, hN m hm]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  obtain ⟨k, hk, hpointwise⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  refine ⟨v, ?_⟩
  have hpt : ∀ᵐ a ∂ν, ∀ᵐ t ∂μt T, Tendsto (fun n => J (k n) (t, a)) atTop (𝓝 (v (t, a))) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually
      hpointwise)
  filter_upwards [ae_all_iff.2 hJ, hpt] with a ha hlim
  have hseq : Tendsto (fun n => s (k n) a) atTop (𝓝 (f a)) :=
    (hf.tendsto_approxBounded_of_norm_le (hb a)).comp hk.tendsto_atTop
  have hseq_mu := tendstoInMeasure_of_tendsto_Lp hseq
  have hJ_mu := tendstoInMeasure_of_tendsto_ae (μ := μt T)
    (fun n => (Lp.aestronglyMeasurable (s (k n) a)).congr (ha (k n)).symm) hlim
  exact tendstoInMeasure_ae_unique
    (hseq_mu.congr (fun n => (ha (k n)).symm) (ae_eq_refl _)) hJ_mu

private theorem endpointMixedJoint_exists {T : ℝ} (w : W(T)) :
    ∃ v : EndpointTorusL2 T, ∀ᵐ a ∂ν,
      (fun t => HalfHolder.eval a w t) =ᵐ[μt T] fun t => v (t, a) :=
  mixedApprox_approximates_joint (fun a => HalfHolder.eval a w)
    w.val.1.continuous.stronglyMeasurable (norm_nonneg w)
    ((HalfHolder.norm_le_iff (norm_nonneg w)).mp le_rfl).1

private noncomputable def endpointMixedJointValue {T : ℝ} (w : W(T)) : EndpointTorusL2 T :=
  (endpointMixedJoint_exists w).choose

private theorem endpointMixedJointValue_slices {T : ℝ} (w : W(T)) :
    ∀ᵐ a ∂ν, (fun t => HalfHolder.eval a w t) =ᵐ[μt T]
      fun t => endpointMixedJointValue w (t, a) :=
  (endpointMixedJoint_exists w).choose_spec

private theorem norm_endpointMixedJointValue_le {T : ℝ} (w : W(T)) :
    ‖endpointMixedJointValue w‖ ≤ ‖w‖ := by
  have hcap := ((HalfHolder.norm_le_iff (norm_nonneg w)).mp le_rfl).1
  have hint : Integrable (fun a => ‖HalfHolder.eval a w‖ ^ 2) ν := by
    apply (integrable_const (‖w‖ ^ 2)).mono
    · exact (w.val.1.continuous.stronglyMeasurable.norm.measurable.pow_const 2).aestronglyMeasurable
    · exact ae_of_all _ fun a => by
        rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hcap a) 2
  apply le_of_sq_le_sq _ (norm_nonneg w)
  rw [endpointJoint_norm_sq_of_slices _ _ (endpointMixedJointValue_slices w)]
  calc
    (∫ a, ‖HalfHolder.eval a w‖ ^ 2 ∂ν) ≤ ∫ _a : A, ‖w‖ ^ 2 ∂ν := by
      exact integral_mono_ae hint (integrable_const _) (ae_of_all _ fun a =>
        pow_le_pow_left₀ (norm_nonneg _) (hcap a) 2)
    _ = _ := by rw [integral_const, probReal_univ, one_smul]

/-- A spatial half-Hölder field of temporal (L^2) paths injects into joint
(L^2) without increasing its norm. -/
noncomputable def endpointMixedToJoint (T : ℝ) : W(T) →L[ℝ] EndpointTorusL2 T := by
  let L : W(T) →ₗ[ℝ] EndpointTorusL2 T :=
    { toFun := endpointMixedJointValue
      map_add' := fun u w => by
        apply endpointJoint_eq_of_slices
        filter_upwards [endpointMixedJointValue_slices (u + w), endpointMixedJointValue_slices u,
          endpointMixedJointValue_slices w,
          ae_endpointTimeSlice_congr (Lp.coeFn_add (endpointMixedJointValue u) (endpointMixedJointValue w))]
          with a huw hu hw hJ
        filter_upwards [huw, hu, hw, hJ, Lp.coeFn_add (HalfHolder.eval a u) (HalfHolder.eval a w)]
          with t hAt hUt hWt hJt hLt
        calc
          endpointMixedJointValue (u + w) (t, a) = (HalfHolder.eval a (u + w) : Vt(T)) t := hAt.symm
          _ = HalfHolder.eval a u t + HalfHolder.eval a w t := by rw [map_add]; exact hLt
          _ = _ := by rw [hJt, Pi.add_apply, hUt, hWt]
      map_smul' := fun c w => by
        apply endpointJoint_eq_of_slices
        filter_upwards [endpointMixedJointValue_slices (c • w), endpointMixedJointValue_slices w,
          ae_endpointTimeSlice_congr (Lp.coeFn_smul c (endpointMixedJointValue w))]
          with a hcw hw hJ
        filter_upwards [hcw, hw, hJ, Lp.coeFn_smul c (HalfHolder.eval a w)]
          with t hAt hWt hJt hLt
        change endpointMixedJointValue (c • w) (t, a) = (c • endpointMixedJointValue w) (t, a)
        calc
          endpointMixedJointValue (c • w) (t, a) = HalfHolder.eval a (c • w) t := hAt.symm
          _ = c • HalfHolder.eval a w t := by rw [map_smul]; exact hLt
          _ = _ := by rw [hJt, Pi.smul_apply, hWt] }
  have hL (w : W(T)) : ‖L w‖ ≤ 1 * ‖w‖ := by
    change ‖endpointMixedJointValue w‖ ≤ 1 * ‖w‖
    simpa only [one_mul] using norm_endpointMixedJointValue_le w
  exact L.mkContinuous 1 hL

theorem endpointMixedToJoint_apply_ae {T : ℝ} (w : W(T)) :
    ∀ᵐ a ∂ν, (fun t => HalfHolder.eval a w t) =ᵐ[μt T]
      fun t => endpointMixedToJoint T w (t, a) :=
  endpointMixedJointValue_slices w

theorem endpointMixedToJoint_norm_sq {T : ℝ} (w : W(T)) :
    ‖endpointMixedToJoint T w‖ ^ 2 = ∫ a, ‖HalfHolder.eval a w‖ ^ 2 ∂ν :=
  endpointJoint_norm_sq_of_slices _ _ (endpointMixedToJoint_apply_ae w)

theorem norm_endpointMixedToJoint_apply_le {T : ℝ} (w : W(T)) :
    ‖endpointMixedToJoint T w‖ ≤ ‖w‖ :=
  norm_endpointMixedJointValue_le w

theorem endpointMixedToJoint_injective (T : ℝ) : Function.Injective (endpointMixedToJoint T) := by
  intro u w huw
  have hae : (fun a => HalfHolder.eval a u) =ᵐ[ν] fun a => HalfHolder.eval a w := by
    filter_upwards [endpointMixedToJoint_apply_ae u, endpointMixedToJoint_apply_ae w] with a hu hw
    rw [huw] at hu
    exact Lp.ext (hu.trans hw.symm)
  have h := (Continuous.ae_eq_iff_eq ν u.val.1.continuous w.val.1.continuous).mp hae
  exact HalfHolder.ext (congrFun h)

end TorusEuler
