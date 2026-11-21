import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.Heat

theorem heatFactor_pos (t : ℝ) (ξ : Space) : 0 < heatFactor t ξ := Real.exp_pos _

theorem heatFactor_le_one (t : ℝ) (ξ : Space) : heatFactor t ξ ≤ 1 := by
  unfold heatFactor
  rw [Real.exp_le_one_iff]
  have h0 : 0 ≤ max t 0 := le_max_right t 0
  have : 0 ≤ 4 * π ^ 2 * max t 0 * ‖ξ‖ ^ 2 := by positivity
  linarith

theorem continuous_heatFactor (t : ℝ) : Continuous (heatFactor t) := by
  unfold heatFactor
  fun_prop

theorem continuous_heatFactor_time (ξ : Space) : Continuous (fun t => heatFactor t ξ) := by
  unfold heatFactor
  fun_prop

theorem heatFactor_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ξ : Space) :
    heatFactor (s + t) ξ = heatFactor s ξ * heatFactor t ξ := by
  unfold heatFactor
  rw [max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht), ← Real.exp_add]
  congr 1
  ring

theorem heat_realized (h1 : FieldOpRealized) (t : ℝ) :
    IsRealizedBy (heatL2 t) id (fun ξ => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace) := by
  have hm : AEStronglyMeasurable
      (fun ξ : Space => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    ((continuous_heatFactor t).smul continuous_const).aestronglyMeasurable
  have hb : ∀ ξ, ‖heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := by
    intro ξ
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (heatFactor_pos t ξ)]
    calc heatFactor t ξ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
          mul_le_mul (heatFactor_le_one t ξ) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have h := h1 (ContinuousLinearEquiv.refl ℝ Space) _ 1 hm hb
  rw [ContinuousLinearEquiv.coe_refl'] at h
  exact h

theorem heat_ae (h1 : FieldOpRealized) (t : ℝ) (f : L2C) :
    ∀ᵐ ξ ∂volume, (heatL2 t f : Space → CSpace) ξ = heatFactor t ξ • (f : Space → CSpace) ξ := by
  filter_upwards [heat_realized h1 t f] with ξ hξ
  rw [hξ]
  rfl

theorem heat_comm (h1 : FieldOpRealized) (t : ℝ) (A : Space → Space)
    (G : Space → CSpace →L[ℝ] CSpace) (hA : Measure.QuasiMeasurePreserving A volume volume)
    (hc : ∀ ξ, heatFactor t (A ξ) = heatFactor t ξ) (f : L2C) :
    fieldOp A G (heatL2 t f) = heatL2 t (fieldOp A G f) := by
  by_cases h : ∃ T, IsRealizedBy T A G
  · have hT : IsRealizedBy (fieldOp A G) A G := by
      unfold fieldOp
      rw [dif_pos h]
      exact h.choose_spec
    apply Lp.ext
    have e4 : ∀ᵐ ξ ∂volume, (heatL2 t f : Space → CSpace) (A ξ) =
        heatFactor t (A ξ) • (f : Space → CSpace) (A ξ) := hA.ae (heat_ae h1 t f)
    filter_upwards [hT (heatL2 t f), heat_ae h1 t (fieldOp A G f), hT f, e4] with ξ ha hb hd he
    rw [ha, hb, hd, he, hc, map_smul]
  · have h0 : fieldOp A G = 0 := by
      unfold fieldOp
      rw [dif_neg h]
    simp [h0]

theorem quasiMeasurePreserving_neg :
    Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume := by
  have h := Measure.quasiMeasurePreserving_smul (volume : Measure Space) (r := -1) (by norm_num)
  simpa using h

theorem heat_mem (h1 : FieldOpRealized) (t : ℝ) (x : L2C) (hx : x ∈ Sig) : heatL2 t x ∈ Sig := by
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker] at hx ⊢
  obtain ⟨hr, hl⟩ := hx
  have hr' : reflConj x = x := by
    have := hr
    simp only [ContinuousLinearMap.coe_coe, sub_apply,
      ContinuousLinearMap.id_apply] at this
    exact sub_eq_zero.1 this
  have hl' : fieldOp id longitudinal x = 0 := by simpa using hl
  have hcr : reflConj (heatL2 t x) = heatL2 t (reflConj x) :=
    heat_comm h1 t (fun ξ => -ξ) (fun _ => conjVec) quasiMeasurePreserving_neg
      (fun ξ => by simp [heatFactor]) x
  have hcl : fieldOp id longitudinal (heatL2 t x) = heatL2 t (fieldOp id longitudinal x) :=
    heat_comm h1 t id longitudinal (Measure.QuasiMeasurePreserving.id volume) (fun ξ => rfl) x
  refine ⟨?_, ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, sub_apply,
      ContinuousLinearMap.id_apply]
    rw [hcr, hr', sub_self]
  · simp only [ContinuousLinearMap.coe_coe]
    rw [hcl, hl', map_zero]

theorem heatX_coe (h1 : FieldOpRealized) (t : ℝ) (x : X) : (heatX t x : L2C) = heatL2 t x := by
  unfold heatX restrictX
  rw [dif_pos (fun y hy => heat_mem h1 t y hy)]
  rfl

theorem heatL2_continuous (h1 : FieldOpRealized) (f : L2C) : Continuous (fun t => heatL2 t f) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set Φ : ℝ → Space → ℝ := fun t ξ =>
    (heatFactor t ξ - heatFactor t₀ ξ) ^ 2 * ‖(f : Space → CSpace) ξ‖ ^ 2 with hΦ
  have heq : ∀ t, ‖heatL2 t f - heatL2 t₀ f‖ ^ 2 = ∫ ξ, Φ t ξ := by
    intro t
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (heatL2 t f) (heatL2 t₀ f), heat_ae h1 t f, heat_ae h1 t₀ f]
      with ξ hs ha hb
    rw [hs, Pi.sub_apply, ha, hb, ← sub_smul, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  have hint : Integrable (fun ξ => ‖(f : Space → CSpace) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hlim : Filter.Tendsto (fun t => ∫ ξ, Φ t ξ) (nhds t₀) (nhds (∫ ξ, Φ t₀ ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => ‖(f : Space → CSpace) ξ‖ ^ 2) ?_ ?_ hint ?_
    · refine Filter.Eventually.of_forall fun t => ?_
      exact (((continuous_heatFactor t).sub (continuous_heatFactor t₀)).pow 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable f).norm.pow 2)
    · refine Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun ξ => ?_
      have ha := heatFactor_pos t ξ
      have hb := heatFactor_pos t₀ ξ
      have ha' := heatFactor_le_one t ξ
      have hb' := heatFactor_le_one t₀ ξ
      have hsq : (heatFactor t ξ - heatFactor t₀ ξ) ^ 2 ≤ 1 := by nlinarith
      rw [hΦ, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (by positivity) hsq
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have hc : Continuous (fun t => Φ t ξ) := by
        rw [hΦ]
        exact ((((continuous_heatFactor_time ξ).sub continuous_const).pow 2).mul continuous_const)
      exact hc.tendsto t₀
  have h0 : ∫ ξ, Φ t₀ ξ = 0 := by simp [hΦ]
  rw [h0] at hlim
  have hsq : Filter.Tendsto (fun t => ‖heatL2 t f - heatL2 t₀ f‖ ^ 2) (nhds t₀) (nhds 0) := by
    simpa only [heq] using hlim
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end Internal.Heat

open Internal.Heat in
theorem heatSemigroup (h1 : FieldOpRealized) :
    HeatSemigroup := by
  refine ⟨?_, ?_, ?_, ?_, ?_, heatX_coe h1⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [heatX_coe h1]
    apply Lp.ext
    filter_upwards [heat_ae h1 0 x] with ξ h
    rw [h]
    simp [heatFactor]
  · intro s t hs ht
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [heatX_coe h1, ContinuousLinearMap.comp_apply, heatX_coe h1, heatX_coe h1]
    apply Lp.ext
    filter_upwards [heat_ae h1 (s + t) x, heat_ae h1 s (heatL2 t x), heat_ae h1 t x]
      with ξ ha hb hc
    rw [ha, hb, hc, smul_smul, heatFactor_add s t hs ht]
  · intro t _
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    change ‖(heatX t x : L2C)‖ ≤ ‖(x : L2C)‖
    rw [heatX_coe h1]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [heat_ae h1 t x] with ξ h
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (heatFactor_pos t ξ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (heatFactor_le_one t ξ)
  · intro x
    apply Continuous.continuousOn
    apply continuous_induced_rng.2
    have h : (fun t => ((heatX t x : X) : L2C)) = fun t => heatL2 t x := by
      funext t
      exact heatX_coe h1 t x
    rw [Function.comp_def, h]
    exact heatL2_continuous h1 x
  · intro t x y
    change inner ℝ (heatX t x : L2C) (y : L2C) = inner ℝ (x : L2C) (heatX t y : L2C)
    rw [heatX_coe h1, heatX_coe h1, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heat_ae h1 t x, heat_ae h1 t y] with ξ hx hy
    rw [hx, hy, real_inner_smul_left, real_inner_smul_right]

end Breakdown.Freq
