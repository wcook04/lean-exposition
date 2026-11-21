import Breakdown.Frac.StSpace

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter Metric

noncomputable section

namespace Breakdown

private lemma weakCont_amgm (a b l : ℝ) (hl : 0 < l) : a * b ≤ l * a ^ 2 + b ^ 2 / (4 * l) := by
  have h4 : 0 < 4 * l := by positivity
  have key : 4 * l * (a * b) ≤ 4 * l * (l * a ^ 2) + b ^ 2 := by
    nlinarith [sq_nonneg (2 * l * a - b)]
  have hq : b ^ 2 / (4 * l) * (4 * l) = b ^ 2 := div_mul_cancel₀ _ h4.ne'
  nlinarith

private lemma weakCont_pair_bound (a b : Space) (l : ℝ) (hl : 0 < l) :
    ‖inner ℝ a b‖ ≤ l * ‖a‖ ^ 2 + ‖b‖ ^ 2 / (4 * l) :=
  (norm_inner_le_norm a b).trans (weakCont_amgm _ _ l hl)

private lemma weakCont_sq_integrable {g : Space → Space} (hg : Continuous g) {α C : ℝ}
    (hα : 0 < α) (hC : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(3 + 2 * α))) :
    Integrable (fun x => ‖g x‖ ^ 2) := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hint : Integrable (fun x : Space => (1 + ‖x‖) ^ (-(3 + 2 * α))) :=
    integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; linarith)
  refine (hint.const_mul (C ^ 2)).mono' (hg.norm.pow 2).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  have hw0 : 0 ≤ (1 + ‖x‖) ^ (-(3 + 2 * α)) := Real.rpow_nonneg (by positivity) _
  have hw1 : (1 + ‖x‖) ^ (-(3 + 2 * α)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)
  have h1 := hC x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h2 := mul_le_mul_of_nonneg_left hw1 (mul_nonneg (sq_nonneg C) hw0)
  calc ‖g x‖ ^ 2 = ‖g x‖ * ‖g x‖ := sq _
    _ ≤ (C * (1 + ‖x‖) ^ (-(3 + 2 * α))) * (C * (1 + ‖x‖) ^ (-(3 + 2 * α))) :=
        mul_le_mul h1 h1 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ ≤ C ^ 2 * (1 + ‖x‖) ^ (-(3 + 2 * α)) := by nlinarith

private lemma weakCont_energy {w : Space → Space} (hw : Continuous w) {A : ℝ}
    (hA : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal A) :
    Integrable (fun x => ‖w x‖ ^ 2) ∧ ∫ x, ‖w x‖ ^ 2 ≤ max A 0 := by
  have h0 : 0 ≤ᵐ[volume] fun x => ‖w x‖ ^ 2 := Eventually.of_forall fun x => sq_nonneg _
  have hfin : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) < ⊤ := hA.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨(hw.norm.pow 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 (hw.norm.pow 2).aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal A).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hA
    _ = max A 0 := ENNReal.toReal_ofReal'

theorem fracWeakContinuity_of (h1 : FracCompactDecayStatement) : FracWeakContinuityStatement := by
  intro α hα1 hα2 T v hv hE ϕ hϕ hϕc
  obtain ⟨hgc, C, hC⟩ := h1 α hα1 hα2 ϕ hϕ hϕc
  set g := fractionalPowerAt α ϕ with hg_def
  obtain ⟨A, hA⟩ := hE
  have hvc : ∀ t ∈ Icc 0 T, Continuous (v t) := fun t ht =>
    hv.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨ht, mem_univ x⟩)
  have hvt : ∀ x, ContinuousOn (fun t => v t x) (Icc 0 T) := fun x =>
    hv.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ _⟩)
  have hvE : ∀ t ∈ Icc 0 T, Integrable (fun x => ‖v t x‖ ^ 2) ∧ ∫ x, ‖v t x‖ ^ 2 ≤ max A 0 :=
    fun t ht => weakCont_energy (hvc t ht) (hA t ht)
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) := weakCont_sq_integrable hgc (by linarith) hC
  have hbd : ∀ t ∈ Icc 0 T, ∀ l : ℝ, 0 < l →
      Integrable (fun x => l * ‖v t x‖ ^ 2 + ‖g x‖ ^ 2 / (4 * l)) := fun t ht l _ =>
    ((hvE t ht).1.const_mul l).add (hg2.div_const (4 * l))
  have hint : ∀ t ∈ Icc 0 T, Integrable (fun x => inner ℝ (v t x) (g x)) := fun t ht =>
    (hbd t ht 1 one_pos).mono' ((hvc t ht).inner hgc).aestronglyMeasurable
      (Eventually.of_forall fun x => weakCont_pair_bound _ _ 1 one_pos)
  have hcont : ∀ n : ℕ, ContinuousOn
      (fun t => ∫ x in closedBall (0 : Space) n, inner ℝ (v t x) (g x)) (Icc 0 T) := by
    intro n
    have hK : IsCompact (Icc 0 T ×ˢ closedBall (0 : Space) n) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      (hv.continuousOn.mono (prod_mono subset_rfl (subset_univ _)))
    refine continuousOn_of_dominated (bound := fun x => M * ‖g x‖) ?_ ?_ ?_ ?_
    · intro t ht
      exact ((hvc t ht).inner hgc).aestronglyMeasurable
    · intro t ht
      refine ae_restrict_of_forall_mem measurableSet_closedBall fun x hx => ?_
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact hM (t, x) ⟨ht, hx⟩
    · exact (continuous_const.mul hgc.norm).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)
    · exact Eventually.of_forall fun x => (hvt x).inner continuousOn_const
  have htail : Tendsto (fun n : ℕ => ∫ x in (closedBall (0 : Space) n)ᶜ, ‖g x‖ ^ 2) atTop
      (𝓝 0) := by
    have h := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖g x‖ ^ 2)
      (s := fun n : ℕ => (closedBall (0 : Space) n)ᶜ) (fun n => measurableSet_closedBall.compl)
      (fun m n hmn => compl_subset_compl.2
        (closedBall_subset_closedBall (by exact_mod_cast hmn))) ⟨0, hg2.integrableOn⟩
    have he : (⋂ n : ℕ, (closedBall (0 : Space) n)ᶜ) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
      exact (mem_iInter.1 hx n) (mem_closedBall_zero_iff.2 hn)
    rw [he, Measure.restrict_empty, integral_zero_measure] at h
    exact h
  refine TendstoUniformlyOn.continuousOn
    (F := fun (n : ℕ) t => ∫ x in closedBall (0 : Space) n, inner ℝ (v t x) (g x))
    (p := atTop) ?_ (Frequently.of_forall hcont)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  set l := ε / (4 * (max A 0 + 1)) with hl_def
  have hl : 0 < l := by positivity
  filter_upwards [htail.eventually (gt_mem_nhds (show (0 : ℝ) < ε * l by positivity))] with n hn
  intro t ht
  rw [Real.dist_eq, ← integral_add_compl (measurableSet_closedBall (x := (0 : Space)) (ε := (n : ℝ)))
    (hint t ht), add_sub_cancel_left]
  have hvB : ∫ x in (closedBall (0 : Space) n)ᶜ, ‖v t x‖ ^ 2 ≤ max A 0 :=
    (setIntegral_le_integral (hvE t ht).1 (Eventually.of_forall fun x => sq_nonneg _)).trans
      (hvE t ht).2
  have hlA : l * max A 0 ≤ ε / 4 := by
    rw [hl_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hq : ε * l / (4 * l) = ε / 4 := by field_simp
  calc |∫ x in (closedBall (0 : Space) n)ᶜ, inner ℝ (v t x) (g x)|
      ≤ ∫ x in (closedBall (0 : Space) n)ᶜ, ‖inner ℝ (v t x) (g x)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ x in (closedBall (0 : Space) n)ᶜ, (l * ‖v t x‖ ^ 2 + ‖g x‖ ^ 2 / (4 * l)) :=
        integral_mono (hint t ht).norm.integrableOn (hbd t ht l hl).integrableOn
          (fun x => weakCont_pair_bound _ _ l hl)
    _ = l * (∫ x in (closedBall (0 : Space) n)ᶜ, ‖v t x‖ ^ 2)
          + (∫ x in (closedBall (0 : Space) n)ᶜ, ‖g x‖ ^ 2) / (4 * l) := by
        rw [integral_add ((hvE t ht).1.const_mul l).integrableOn (hg2.div_const _).integrableOn,
          integral_const_mul, integral_div]
    _ ≤ l * max A 0 + ε * l / (4 * l) := by
        gcongr
    _ < ε := by rw [hq]; linarith

end Breakdown
