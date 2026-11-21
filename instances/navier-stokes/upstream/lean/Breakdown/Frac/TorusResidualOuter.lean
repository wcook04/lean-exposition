import Breakdown.Frac.TorusResidualOuterBound

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracResidualOuterInternal

theorem nat_le_infty (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem tail_integrable {s : ℝ} (hs : s < -3) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) {z : Space | (1 / 64 : ℝ) < ‖z‖} := by
  have hint : Integrable (fun z : Space => (1 / 128 : ℝ) ^ s * (1 + ‖z‖) ^ (-(-s))) :=
    (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)).const_mul _
  refine hint.integrableOn.mono' (measurable_norm.pow_const s).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_norm) fun z hz => ?_)
  have hz1 : (1 / 64 : ℝ) < ‖z‖ := hz
  have hle : ‖z‖ ^ s ≤ ((1 / 128 : ℝ) * (1 + ‖z‖)) ^ s :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg]
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hle
  exact hle

theorem iteratedFDeriv_eq_zero_outer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ y, centralRadius / 2 ≤ dist y center → f y = 0) (n : ℕ) {x : Space}
    (hx : centralRadius / 2 ≤ dist x center) : iteratedFDeriv ℝ n f x = 0 := by
  have hρ : centralRadius / 2 ≠ 0 := by norm_num [centralRadius]
  have hcl : IsClosed {y : Space | iteratedFDeriv ℝ n f y = 0} :=
    isClosed_eq (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)) continuous_const
  have hsub : (Metric.closedBall center (centralRadius / 2))ᶜ ⊆
      {y : Space | iteratedFDeriv ℝ n f y = 0} := by
    intro y hy
    have hy' : centralRadius / 2 < dist y center := by
      simpa [Metric.mem_closedBall, not_le] using hy
    have hev : f =ᶠ[𝓝 y] fun _ => (0 : E) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
        hy'] with w hw
      exact h0 w (le_of_lt hw)
    show iteratedFDeriv ℝ n f y = 0
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    rfl
  have hmem : x ∈ closure (Metric.closedBall center (centralRadius / 2))ᶜ := by
    rw [closure_compl, interior_closedBall center hρ]
    simpa [Metric.mem_ball, not_lt] using hx
  exact hcl.closure_subset_iff.2 hsub hmem

end FracResidualOuterInternal

open FracResidualOuterInternal

theorem fracResidualOuter_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hD : FracSelfSimilarDecay α)
    (hF : FracApproxFieldProperties α) (hP : FracPointwiseBound α)
    (hI : RemainderIntegrableStatement) : FracResidualRegionBound α outerRegion := by
  intro a U P hU
  obtain ⟨C₀, hC₀, hB⟩ := fracApproxField_bounds α h1 h2 hD hF a U P hU
  obtain ⟨Cp, hCp, hPb⟩ := hP
  have hint : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) {z : Space | (1 / 64 : ℝ) < ‖z‖} :=
    tail_integrable (by linarith)
  obtain ⟨I₀, hI₀def⟩ : ∃ I₀ : ℝ, I₀ = ∫ z in {z : Space | (1 / 64 : ℝ) < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) :=
    ⟨_, rfl⟩
  have hI₀ : 0 ≤ I₀ := by
    rw [hI₀def]
    exact setIntegral_nonneg (measurableSet_lt measurable_const measurable_norm)
      (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨Cp * (C₀ * (1 / 64 : ℝ) ^ (3 - 2 * α) + C₀ * I₀), ?_⟩
  intro T t hT hT1 ht0 htT x hx
  have hx' : centralRadius / 2 ≤ dist x center := hx
  obtain ⟨hsm, hpsm, hprop⟩ := hF a U P hU T hT
  have hmem : ∀ y : Space, ((fun y : Space => ((t, y) : ℝ × Space)) y) ∈ Iio T ×ˢ (univ : Set Space) :=
    fun y => mem_prod.2 ⟨htT, mem_univ _⟩
  have hcd : ContDiff ℝ ∞ (fun y : Space => ((t, y) : ℝ × Space)) :=
    contDiff_const.prodMk contDiff_id
  have hslice : ContDiff ℝ ∞ (fracApproxField α a U T t) := by
    have h := hsm.comp_contDiff hcd hmem
    have e : ((fun z : ℝ × Space => fracApproxField α a U T z.1 z.2) ∘
        fun y : Space => ((t, y) : ℝ × Space)) = fracApproxField α a U T t := by
      funext y
      rfl
    rw [e] at h
    exact h
  have hpslice : ContDiff ℝ ∞ (fracApproxPressure α a P T t) := by
    have h := hpsm.comp_contDiff hcd hmem
    have e : ((fun z : ℝ × Space => fracApproxPressure α a P T z.1 z.2) ∘
        fun y : Space => ((t, y) : ℝ × Space)) = fracApproxPressure α a P T t := by
      funext y
      rfl
    rw [e] at h
    exact h
  have hzero : ∀ y, centralRadius / 2 ≤ dist y center → fracApproxField α a U T t y = 0 :=
    fun y hy => ((hprop t htT y).2.1 hy).1
  have hpzero : ∀ y, centralRadius / 2 ≤ dist y center → fracApproxPressure α a P T t y = 0 :=
    fun y hy => ((hprop t htT y).2.1 hy).2
  have htime : deriv (fun τ => fracApproxField α a U T τ x) t = 0 := by
    have hev : (fun τ => fracApproxField α a U T τ x) =ᶠ[𝓝 t] fun _ => (0 : Space) := by
      filter_upwards [Iio_mem_nhds htT] with τ hτ
      exact ((hprop τ hτ x).2.1 hx').1
    rw [hev.deriv_eq, deriv_const]
  have hadv : advectionAt (fracApproxField α a U T t) x = 0 := by
    unfold advectionAt
    rw [hzero x hx', map_zero]
  have hpd : fderiv ℝ (fracApproxPressure α a P T t) x = 0 := by
    have h := iteratedFDeriv_eq_zero_outer hpslice hpzero 1 hx'
    rw [← norm_le_zero_iff, ← norm_iteratedFDeriv_zero (𝕜 := ℝ), norm_iteratedFDeriv_fderiv, h, norm_zero]
  have hgrad : gradientAt (fracApproxPressure α a P T t) x = 0 := by
    simp [gradientAt, hpd]
  have hres : fracSpaceResidual α a U P T t x = fractionalPowerAt α (fracApproxField α a U T t) x := by
    unfold fracSpaceResidual
    rw [htime, hadv, hgrad, zero_add, zero_add, add_zero]
  rw [hres]
  have hμ : 0 < T - t := by linarith
  have hμ1 : T - t ≤ 1 := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = C₀ * (T - t) ^ (-(1 - 1 / (2 * α))) := ⟨_, rfl⟩
  have hS : ∀ y, ‖fracApproxField α a U T t y‖ ≤ S := fun y => by
    rw [hSdef]
    exact (hB T t hT hT1 ht0 htT y).1
  have hf3 : ContDiff ℝ 3 (fracApproxField α a U T t) := hslice.of_le (nat_le_infty 3)
  have hrem := hI α h1 (by linarith) _ hslice (Or.inr ⟨S, hS⟩) x
  have hball : ∀ y ∈ Metric.closedBall x (1 / 64 : ℝ),
      ‖iteratedFDeriv ℝ 3 (fracApproxField α a U T t) y‖ ≤ C₀ := by
    intro y hy
    refine (hB T t hT hT1 ht0 htT y).2 ?_
    have hyx : dist y x ≤ 1 / 64 := hy
    have htri := dist_triangle x y center
    rw [dist_comm x y] at htri
    norm_num [centralRadius] at hx' ⊢
    linarith
  have hx0 : ‖fracApproxField α a U T t x‖ ≤ 0 := by rw [hzero x hx', norm_zero]
  have hx1 : ‖fderiv ℝ (fracApproxField α a U T t) x‖ ≤ 0 := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), norm_iteratedFDeriv_fderiv,
      iteratedFDeriv_eq_zero_outer hslice hzero 1 hx', norm_zero]
  have hx2 : ‖iteratedFDeriv ℝ 2 (fracApproxField α a U T t) x‖ ≤ 0 := by
    rw [iteratedFDeriv_eq_zero_outer hslice hzero 2 hx', norm_zero]
  have hcont : Continuous (fun z : Space => ‖fracApproxField α a U T t (x + z)‖) :=
    (hslice.continuous.comp (continuous_const.add continuous_id)).norm
  have hdom : ∀ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * ‖fracApproxField α a U T t (x + z)‖ ≤
      S * ‖z‖ ^ (-(3 + 2 * α)) := fun z => by
    rw [mul_comm S]
    exact mul_le_mul_of_nonneg_left (hS _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hfar : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * ‖fracApproxField α a U T t (x + z)‖)
      {z : Space | (1 / 64 : ℝ) < ‖z‖} := by
    refine (hint.const_mul S).mono'
      ((measurable_norm.pow_const _).mul hcont.measurable).aestronglyMeasurable.restrict
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (norm_nonneg _))]
    exact hdom z
  have hL : ∫ z in {z : Space | (1 / 64 : ℝ) < ‖z‖},
      ‖z‖ ^ (-(3 + 2 * α)) * ‖fracApproxField α a U T t (x + z)‖ ≤ S * I₀ := by
    rw [hI₀def, ← integral_const_mul]
    exact setIntegral_mono hfar (hint.const_mul S) hdom
  have key := hPb _ hf3 x (1 / 64) 0 C₀ (S * I₀) (by norm_num) (by norm_num) hrem hball hx0 hx1 hx2
    hfar hL
  have hg : 1 / (2 * α) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h3 : 3 / (2 * α) = 3 * (1 / (2 * α)) := by ring
  have hE1 : 1 ≤ (T - t) ^ (-(2 - 3 / (2 * α))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hμ hμ1 (by rw [h3]; linarith)
  have hE2 : (T - t) ^ (-(1 - 1 / (2 * α))) ≤ (T - t) ^ (-(2 - 3 / (2 * α))) :=
    Real.rpow_le_rpow_of_exponent_ge hμ hμ1 (by rw [h3]; linarith)
  have hr0 : 0 ≤ (1 / 64 : ℝ) ^ (3 - 2 * α) := Real.rpow_nonneg (by norm_num) _
  have hA : C₀ * (1 / 64 : ℝ) ^ (3 - 2 * α) ≤
      C₀ * (1 / 64 : ℝ) ^ (3 - 2 * α) * (T - t) ^ (-(2 - 3 / (2 * α))) :=
    le_mul_of_one_le_right (mul_nonneg hC₀ hr0) hE1
  have hSI : S * I₀ ≤ C₀ * I₀ * (T - t) ^ (-(2 - 3 / (2 * α))) := by
    rw [hSdef]
    have := mul_le_mul_of_nonneg_left hE2 hC₀
    have := mul_le_mul_of_nonneg_right this hI₀
    linarith
  rw [zero_mul, add_zero] at key
  calc ‖fractionalPowerAt α (fracApproxField α a U T t) x‖
      ≤ Cp * (C₀ * (1 / 64 : ℝ) ^ (3 - 2 * α) + S * I₀) := key
    _ ≤ Cp * (C₀ * (1 / 64 : ℝ) ^ (3 - 2 * α) * (T - t) ^ (-(2 - 3 / (2 * α))) +
          C₀ * I₀ * (T - t) ^ (-(2 - 3 / (2 * α)))) :=
        mul_le_mul_of_nonneg_left (by linarith) hCp.le
    _ = Cp * (C₀ * (1 / 64 : ℝ) ^ (3 - 2 * α) + C₀ * I₀) * (T - t) ^ (-(2 - 3 / (2 * α))) := by
        ring

end Breakdown.Periodic
