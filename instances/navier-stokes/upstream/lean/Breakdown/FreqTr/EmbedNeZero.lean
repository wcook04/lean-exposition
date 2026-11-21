import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.EmbedNeZero

theorem eq_zero_of_decay {c : Space} {C : ℝ} (h : ∀ y : Space, ‖c‖ ≤ C / (1 + ‖y‖)) :
    c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set r : ℝ := |C| / ‖c‖ with hr
  have hr0 : 0 ≤ r := div_nonneg (abs_nonneg _) hpos.le
  have hy : ‖r • unitVector 0‖ = r := by
    rw [norm_smul, unitVector, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg hr0]
  have h1 := h (r • unitVector 0)
  rw [hy, le_div_iff₀ (by positivity)] at h1
  have h2 : ‖c‖ * (1 + r) = ‖c‖ + |C| := by
    rw [hr, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
  rw [h2] at h1
  linarith [le_abs_self C]

theorem clm_eq_zero_of_units {L : Space →L[ℝ] Space} (h : ∀ i, L (unitVector i) = 0) :
    L = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ i, v i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [unitVector]
  rw [hv, map_sum]
  simp [h]

theorem sq_grad_bound {f : Space → Space} {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ 2) (y : Space) :
    ‖∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2‖ ≤
      3 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  have ha : 0 < 1 + ‖y‖ := by positivity
  have hterm : ∀ i, ‖fderiv ℝ f y (unitVector i)‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ 2) ^ 2 := by
    intro i
    have h1 : ‖fderiv ℝ f y (unitVector i)‖ ≤ ‖fderiv ℝ f y‖ := by
      have := (fderiv ℝ f y).le_opNorm (unitVector i)
      rwa [unitVector, PiLp.norm_single, norm_one, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (hC y)) 2
  have hsum : ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2 ≤ 3 * (C / (1 + ‖y‖) ^ 2) ^ 2 := by
    calc ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2
        ≤ ∑ _i : Fin 3, (C / (1 + ‖y‖) ^ 2) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = 3 * (C / (1 + ‖y‖) ^ 2) ^ 2 := by simp
  have hrp : (1 + ‖y‖) ^ (-(4 : ℝ)) = ((1 + ‖y‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg ha.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity), hrp]
  refine hsum.trans (le_of_eq ?_)
  field_simp

end Internal.EmbedNeZero

open Internal.EmbedNeZero in
theorem embedNeZero (h1 : EmbedNorm) :
    EmbedNeZero := by
  intro f hf hne h0
  obtain ⟨y₀, hy₀⟩ := hne
  have hn := h1 f hf
  obtain ⟨hsm, -, C, hC⟩ := hf
  have hcont : Continuous fun x => fderiv ℝ f x := hsm.continuous_fderiv (by simp)
  have hdiff : Differentiable ℝ f := hsm.differentiable (by simp)
  set g : Space → ℝ := fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2 with hg
  have hgc : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hcont.clm_apply continuous_const).norm).pow 2
  have hgi : Integrable g := by
    refine Integrable.mono' ((integrable_one_add_norm (E := Space) (r := 4) (by norm_num [finrank_euclideanSpace])).const_mul
      (3 * C ^ 2)) hgc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    exact sq_grad_bound (fun y => (hC y).2) y
  have hg0 : ∫ y, g y = 0 := by
    rw [← hn, h0, norm_zero]
    norm_num
  have hgz : g = 0 :=
    (hgc.ae_eq_iff_eq volume continuous_zero).mp ((integral_eq_zero_iff_of_nonneg
      (fun y => Finset.sum_nonneg fun i _ => by positivity) hgi).mp hg0)
  have hfd : ∀ y, fderiv ℝ f y = 0 := by
    intro y
    refine clm_eq_zero_of_units fun i => ?_
    have hy : g y = 0 := congrFun hgz y
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖fderiv ℝ f y (unitVector j)‖)).mp hy i (Finset.mem_univ i)
    simpa using this
  have hconst : ∀ y, f y = f y₀ := fun y => is_const_of_fderiv_eq_zero hdiff hfd y y₀
  exact hy₀ (eq_zero_of_decay fun y => by rw [← hconst y]; exact (hC y).1)

end Breakdown.Freq
