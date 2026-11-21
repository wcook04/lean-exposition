import Breakdown.Frac.StRealize
import Breakdown.FreqTr.FieldOp

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.RHeat

open Breakdown.Freq

theorem factor_pos (α t : ℝ) (ξ : Space) : 0 < fracHeatFactor α t ξ := Real.exp_pos _

theorem factor_le_one (α t : ℝ) (ξ : Space) : fracHeatFactor α t ξ ≤ 1 := by
  unfold fracHeatFactor
  rw [Real.exp_le_one_iff]
  have h0 : 0 ≤ max t 0 := le_max_right t 0
  have h1 : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ max t 0 * (2 * π * ‖ξ‖) ^ (2 * α) := mul_nonneg h0 h1
  linarith

theorem measurable_factor (α t : ℝ) : Measurable (fracHeatFactor α t) := by
  unfold fracHeatFactor
  fun_prop

theorem continuous_factor_time (α : ℝ) (ξ : Space) :
    Continuous (fun t => fracHeatFactor α t ξ) := by
  unfold fracHeatFactor
  fun_prop

theorem factor_add (α s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ξ : Space) :
    fracHeatFactor α (s + t) ξ = fracHeatFactor α s ξ * fracHeatFactor α t ξ := by
  unfold fracHeatFactor
  rw [max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht), ← Real.exp_add]
  congr 1
  ring

theorem factor_neg (α t : ℝ) (ξ : Space) : fracHeatFactor α t (-ξ) = fracHeatFactor α t ξ := by
  simp [fracHeatFactor]

theorem realized (α t : ℝ) :
    IsRealizedBy (fracHeatL2 α t) id
      (fun ξ => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) := by
  have hm : AEStronglyMeasurable
      (fun ξ : Space => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    ((measurable_factor α t).smul_const _).aestronglyMeasurable
  have hb : ∀ ξ, ‖fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := by
    intro ξ
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (factor_pos α t ξ)]
    calc fracHeatFactor α t ξ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
          mul_le_mul (factor_le_one α t ξ) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have h := fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space) _ 1 hm hb
  rw [ContinuousLinearEquiv.coe_refl'] at h
  exact h

theorem op_ae (α t : ℝ) (f : L2C) :
    ∀ᵐ ξ ∂volume, (fracHeatL2 α t f : Space → CSpace) ξ =
      fracHeatFactor α t ξ • (f : Space → CSpace) ξ := by
  filter_upwards [realized α t f] with ξ hξ
  rw [hξ]
  rfl

theorem op_comm (α t : ℝ) (A : Space → Space)
    (G : Space → CSpace →L[ℝ] CSpace) (hA : Measure.QuasiMeasurePreserving A volume volume)
    (hc : ∀ ξ, fracHeatFactor α t (A ξ) = fracHeatFactor α t ξ) (f : L2C) :
    fieldOp A G (fracHeatL2 α t f) = fracHeatL2 α t (fieldOp A G f) := by
  by_cases h : ∃ T, IsRealizedBy T A G
  · have hT : IsRealizedBy (fieldOp A G) A G := by
      unfold fieldOp
      rw [dif_pos h]
      exact h.choose_spec
    apply Lp.ext
    have e4 : ∀ᵐ ξ ∂volume, (fracHeatL2 α t f : Space → CSpace) (A ξ) =
        fracHeatFactor α t (A ξ) • (f : Space → CSpace) (A ξ) := hA.ae (op_ae α t f)
    filter_upwards [hT (fracHeatL2 α t f), op_ae α t (fieldOp A G f), hT f, e4]
      with ξ ha hb hd he
    rw [ha, hb, hd, he, hc, map_smul]
  · have h0 : fieldOp A G = 0 := by
      unfold fieldOp
      rw [dif_neg h]
    simp [h0]

theorem qmp_neg :
    Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume := by
  have h := Measure.quasiMeasurePreserving_smul (volume : Measure Space) (r := -1) (by norm_num)
  simpa using h

theorem op_mem (α t : ℝ) (x : L2C) (hx : x ∈ Sig) : fracHeatL2 α t x ∈ Sig := by
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker] at hx ⊢
  obtain ⟨hr, hl⟩ := hx
  have hr' : reflConj x = x := by
    have := hr
    simp only [ContinuousLinearMap.coe_coe, sub_apply,
      ContinuousLinearMap.id_apply] at this
    exact sub_eq_zero.1 this
  have hl' : fieldOp id longitudinal x = 0 := by simpa using hl
  have hcr : reflConj (fracHeatL2 α t x) = fracHeatL2 α t (reflConj x) :=
    op_comm α t (fun ξ => -ξ) (fun _ => conjVec) qmp_neg (fun ξ => factor_neg α t ξ) x
  have hcl : fieldOp id longitudinal (fracHeatL2 α t x) =
      fracHeatL2 α t (fieldOp id longitudinal x) :=
    op_comm α t id longitudinal (Measure.QuasiMeasurePreserving.id volume) (fun ξ => rfl) x
  refine ⟨?_, ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, sub_apply,
      ContinuousLinearMap.id_apply]
    rw [hcr, hr', sub_self]
  · simp only [ContinuousLinearMap.coe_coe]
    rw [hcl, hl', map_zero]

theorem opX_coe (α t : ℝ) (x : X) : (fracHeatX α t x : L2C) = fracHeatL2 α t x := by
  unfold fracHeatX restrictX
  rw [dif_pos (fun y hy => op_mem α t y hy)]
  rfl

theorem op_continuous (α : ℝ) (f : L2C) : Continuous (fun t => fracHeatL2 α t f) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set Φ : ℝ → Space → ℝ := fun t ξ =>
    (fracHeatFactor α t ξ - fracHeatFactor α t₀ ξ) ^ 2 * ‖(f : Space → CSpace) ξ‖ ^ 2 with hΦ
  have heq : ∀ t, ‖fracHeatL2 α t f - fracHeatL2 α t₀ f‖ ^ 2 = ∫ ξ, Φ t ξ := by
    intro t
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (fracHeatL2 α t f) (fracHeatL2 α t₀ f), op_ae α t f,
      op_ae α t₀ f] with ξ hs ha hb
    rw [hs, Pi.sub_apply, ha, hb, ← sub_smul, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  have hint : Integrable (fun ξ => ‖(f : Space → CSpace) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hlim : Filter.Tendsto (fun t => ∫ ξ, Φ t ξ) (nhds t₀) (nhds (∫ ξ, Φ t₀ ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => ‖(f : Space → CSpace) ξ‖ ^ 2) ?_ ?_ hint ?_
    · refine Filter.Eventually.of_forall fun t => ?_
      exact (((measurable_factor α t).sub (measurable_factor α t₀)).pow_const
        2).aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2)
    · refine Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun ξ => ?_
      have ha := factor_pos α t ξ
      have hb := factor_pos α t₀ ξ
      have ha' := factor_le_one α t ξ
      have hb' := factor_le_one α t₀ ξ
      have hsq : (fracHeatFactor α t ξ - fracHeatFactor α t₀ ξ) ^ 2 ≤ 1 := by nlinarith
      rw [hΦ, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (by positivity) hsq
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have hc : Continuous (fun t => Φ t ξ) := by
        rw [hΦ]
        exact ((((continuous_factor_time α ξ).sub continuous_const).pow 2).mul continuous_const)
      exact hc.tendsto t₀
  have h0 : ∫ ξ, Φ t₀ ξ = 0 := by simp [hΦ]
  rw [h0] at hlim
  have hsq : Filter.Tendsto (fun t => ‖fracHeatL2 α t f - fracHeatL2 α t₀ f‖ ^ 2)
      (nhds t₀) (nhds 0) := by
    simpa only [heq] using hlim
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end Breakdown.FracInternal.RHeat

namespace Breakdown.Freq

open Breakdown.FracInternal.RHeat in
theorem fracHeatSemigroup (α : ℝ) : FracHeatSemigroup α := by
  refine ⟨?_, ?_, ?_, ?_, ?_, opX_coe α⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [opX_coe α]
    apply Lp.ext
    filter_upwards [op_ae α 0 x] with ξ h
    rw [h]
    simp [fracHeatFactor]
  · intro s t hs ht
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [opX_coe α, ContinuousLinearMap.comp_apply, opX_coe α, opX_coe α]
    apply Lp.ext
    filter_upwards [op_ae α (s + t) x, op_ae α s (fracHeatL2 α t x), op_ae α t x]
      with ξ ha hb hc
    rw [ha, hb, hc, smul_smul, factor_add α s t hs ht]
  · intro t _
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    change ‖(fracHeatX α t x : L2C)‖ ≤ ‖(x : L2C)‖
    rw [opX_coe α]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [op_ae α t x] with ξ h
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (factor_pos α t ξ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (factor_le_one α t ξ)
  · intro x
    apply Continuous.continuousOn
    apply continuous_induced_rng.2
    have h : (fun t => ((fracHeatX α t x : X) : L2C)) = fun t => fracHeatL2 α t x := by
      funext t
      exact opX_coe α t x
    rw [Function.comp_def, h]
    exact op_continuous α x
  · intro t x y
    change inner ℝ (fracHeatX α t x : L2C) (y : L2C) = inner ℝ (x : L2C) (fracHeatX α t y : L2C)
    rw [opX_coe α, opX_coe α, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [op_ae α t x, op_ae α t y] with ξ hx hy
    rw [hx, hy, real_inner_smul_left, real_inner_smul_right]

end Breakdown.Freq
