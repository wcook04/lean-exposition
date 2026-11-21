import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.StOperator
import Breakdown.Frac.OpIntegrable
import Breakdown.Frac.OpRemainder
import Breakdown.Torus.ApproxField

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def FracApproxFieldThirdBound (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ C : ℝ,
    ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center →
      ‖iteratedFDeriv ℝ 3 (fracApproxField α a U T t) x‖ ≤ C

namespace FracResidualCoreInternal

open ApproxField.Internal

theorem le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Space → E} {T t : ℝ}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Iio T ×ˢ univ)) (htT : t < T) :
    ContDiff ℝ ∞ (f t) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨htT, mem_univ x⟩)

theorem fderiv_eq_zero_of_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) {c : Space} {R : ℝ} (hR : 0 < R) (v : F)
    (h : ∀ y ∈ closedBall c R, f y = v) {x : Space} (hx : x ∈ closedBall c R) :
    fderiv ℝ f x = 0 := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hball : ball c R ⊆ {y | fderiv ℝ f y = 0} := by
    intro y hy
    have hev : f =ᶠ[𝓝 y] fun _ => v :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) fun w hw => h w (ball_subset_closedBall hw)
    show fderiv ℝ f y = 0
    rw [hev.fderiv_eq]
    exact fderiv_const_apply v
  have hcl : closure (ball c R) ⊆ {y | fderiv ℝ f y = 0} :=
    (isClosed_eq hcont continuous_const).closure_subset_iff.2 hball
  rw [closure_ball c hR.ne'] at hcl
  exact hcl hx

theorem iteratedFDeriv_eq_zero_of_ball {f : Space → Space} {c : Space} {R : ℝ}
    (h : ∀ y ∈ closedBall c R, f y = 0) {y : Space} (hy : y ∈ ball c R) (j : ℕ) :
    iteratedFDeriv ℝ j f y = 0 := by
  have hev : f =ᶠ[𝓝 y] fun _ => (0 : Space) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) fun w hw => h w (ball_subset_closedBall hw)
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

theorem iteratedFDeriv_eq_zero_closedBall {f : Space → Space} (hf : ContDiff ℝ ∞ f) {c : Space}
    {R : ℝ} (hR : 0 < R) (h : ∀ y ∈ closedBall c R, f y = 0) {x : Space} (hx : x ∈ closedBall c R)
    (j : ℕ) : iteratedFDeriv ℝ j f x = 0 := by
  have hcont : Continuous (iteratedFDeriv ℝ j f) := hf.continuous_iteratedFDeriv (le_infty j)
  have hball : ball c R ⊆ {y | iteratedFDeriv ℝ j f y = 0} := fun y hy =>
    iteratedFDeriv_eq_zero_of_ball h hy j
  have hcl : closure (ball c R) ⊆ {y | iteratedFDeriv ℝ j f y = 0} :=
    (isClosed_eq hcont continuous_const).closure_subset_iff.2 hball
  rw [closure_ball c hR.ne'] at hcl
  exact hcl hx

theorem power_le (α : ℝ) (CD m : ℝ) (hm : 0 ≤ m) (y : Space) (j : ℕ) (hα : 1 < α) (hj : j ≤ 3)
    (hd : (1 / 16 : ℝ) ≤ ‖y - center‖) :
    CD * (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) ≤ max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2)) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj3 : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  have hX0 : 0 ≤ (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) :=
    Real.rpow_nonneg (by positivity) _
  have hX : (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) ≤ (1 / 16 : ℝ) ^ (-(2 * α + 2)) := by
    calc (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) ≤ (1 / 16 : ℝ) ^ (-(2 * α - 1 + j)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      _ ≤ (1 / 16 : ℝ) ^ (-(2 * α + 2)) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
  have h3 : CD * (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) ≤
      max CD 0 * (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
  have h4 : max CD 0 * (m + ‖y - center‖) ^ (-(2 * α - 1 + j)) ≤
      max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2)) :=
    mul_le_mul_of_nonneg_left hX (le_max_right _ _)
  linarith

theorem difference_bound (α : ℝ) (hα : 1 < α) (w u : Space → Space) (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u)
    (heq : ∀ y, dist y center ≤ centralRadius / 4 → w y = u y)
    (hout : ∀ y, centralRadius / 2 ≤ dist y center → w y = 0) (CA CD m : ℝ) (hm : 0 ≤ m)
    (hwb : ∀ y, centralRadius / 4 ≤ dist y center → ‖iteratedFDeriv ℝ 3 w y‖ ≤ CA)
    (hub : ∀ y, ∀ j : ℕ, j ≤ 3 →
      ‖iteratedFDeriv ℝ j u y‖ ≤ CD * (m + ‖y - center‖) ^ (-(2 * α - 1 + j))) :
    (∀ y, ‖iteratedFDeriv ℝ 3 (w - u) y‖ ≤
      max CA 0 + max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2))) ∧
    (∀ y, ‖(w - u) y‖ ≤ max CA 0 + max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2))) := by
  have hG0 : 0 ≤ max CA 0 + max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2)) :=
    add_nonneg (le_max_right _ _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _))
  have hzero : ∀ y ∈ closedBall center (centralRadius / 4), (w - u) y = 0 := fun y hy => by
    simp [heq y (mem_closedBall.1 hy)]
  have hR : (0 : ℝ) < centralRadius / 4 := by norm_num [centralRadius]
  have hr : centralRadius / 4 = 1 / 16 := by norm_num [centralRadius]
  have hdiff : ContDiff ℝ ∞ (w - u) := hw.sub hu
  have h3 : ∀ y, ‖iteratedFDeriv ℝ 3 (w - u) y‖ ≤
      max CA 0 + max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2)) := by
    intro y
    rcases lt_or_ge (dist y center) (centralRadius / 4) with hy | hy
    · rw [iteratedFDeriv_eq_zero_of_ball hzero (mem_ball.2 hy) 3, norm_zero]
      exact hG0
    · rw [iteratedFDeriv_sub_apply ((hw.of_le (le_infty 3)).contDiffAt)
        ((hu.of_le (le_infty 3)).contDiffAt)]
      refine (norm_sub_le _ _).trans ?_
      have hd : (1 / 16 : ℝ) ≤ ‖y - center‖ := by rw [← dist_eq_norm, ← hr]; exact hy
      have h1 := hwb y hy
      have h2 := (hub y 3 le_rfl).trans (power_le α CD m hm y 3 hα le_rfl hd)
      linarith [le_max_left CA 0]
  refine ⟨h3, fun y => ?_⟩
  rcases lt_or_ge (‖y - center‖) (1 / 8) with hy | hy
  · have hrem := remainderBound (w - u) (hdiff.of_le (le_infty 3)) center (y - center) _
      (fun z _ => h3 z)
    have hc0 : (w - u) center = 0 := hzero center (mem_closedBall_self hR.le)
    have hc1 : fderiv ℝ (w - u) center = 0 := by
      have h := iteratedFDeriv_eq_zero_of_ball hzero (mem_ball_self hR) 1
      rw [← norm_eq_zero, norm_iteratedFDeriv_one] at h
      exact norm_eq_zero.1 h
    have hc2 : iteratedFDeriv ℝ 2 (w - u) center = 0 :=
      iteratedFDeriv_eq_zero_of_ball hzero (mem_ball_self hR) 2
    have hsr : secondOrderRemainder (w - u) center (y - center) = (w - u) y := by
      unfold secondOrderRemainder
      rw [hc0, hc1, hc2, add_sub_cancel]
      simp
    rw [hsr] at hrem
    have hn : ‖y - center‖ ^ 3 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (by linarith)
    calc ‖(w - u) y‖ ≤ _ * ‖y - center‖ ^ 3 := hrem
      _ ≤ (max CA 0 + max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2))) * 1 :=
          mul_le_mul_of_nonneg_left hn hG0
      _ = _ := mul_one _
  · have hw0 : w y = 0 := hout y (by
      rw [dist_eq_norm]
      norm_num [centralRadius]
      linarith)
    have hd : (1 / 16 : ℝ) ≤ ‖y - center‖ := by linarith
    have h2 := hub y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h2
    have h2' := h2.trans (power_le α CD m hm y 0 hα (by norm_num) hd)
    rw [Pi.sub_apply, hw0, zero_sub, norm_neg]
    linarith [le_max_right CA 0]

end FracResidualCoreInternal

open FracResidualCoreInternal ApproxField.Internal

theorem fracResidualCore_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hS : FracSelfSimilarSolves α)
    (hD : FracSelfSimilarDecay α) (hF : FracApproxFieldProperties α) (hP : FracPointwiseBound α)
    (hAdd : AdditivityStatement) (hI : RemainderIntegrableStatement) (_hC : CovarianceStatement)
    (hB : FracApproxFieldThirdBound α) :
    FracResidualRegionBound α coreRegion := by
  intro a U P hU
  obtain ⟨CD, hCD⟩ := hD a U P hU
  obtain ⟨CA, hCA⟩ := hB a U P hU
  obtain ⟨CP, hCP0, hCP⟩ := hP
  have hα3 : α < 3 / 2 := by linarith
  have hs : -(3 + 2 * α) < -3 := by linarith
  have hmeas : MeasurableSet {z : Space | 1 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hKball : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) {z : Space | 1 < ‖z‖} :=
    (FracInternal.integrableOn_compl_ball_norm_rpow hs).mono_set (fun z hz => by
      simp only [mem_compl_iff, mem_ball_zero_iff, not_lt]
      exact le_of_lt hz)
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = max CA 0 + max CD 0 * (1 / 16 : ℝ) ^ (-(2 * α + 2)) :=
    ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact add_nonneg (le_max_right _ _)
      (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _))
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ z in {z : Space | 1 < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) :=
    ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    exact setIntegral_nonneg hmeas (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hK0 : 0 ≤ CP * (G * 1 ^ (3 - 2 * α) + 0 * 1 ^ (-(2 * α)) + G * I) := by
    rw [Real.one_rpow, Real.one_rpow, mul_one, zero_mul, add_zero]
    exact mul_nonneg hCP0.le (add_nonneg hG0 (mul_nonneg hG0 hI0))
  refine ⟨CP * (G * 1 ^ (3 - 2 * α) + 0 * 1 ^ (-(2 * α)) + G * I), ?_⟩
  intro T t hT hT1 ht htT x hx
  have hxc : dist x center ≤ centralRadius / 4 := hx
  have hR : (0 : ℝ) < centralRadius / 4 := by norm_num [centralRadius]
  obtain ⟨hSu, hSp, hSeq⟩ := hS a U P hU T hT
  obtain ⟨hFu, hFp, hFrest⟩ := hF a U P hU T hT
  have hu : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := slice hSu htT
  have hw : ContDiff ℝ ∞ (fracApproxField α a U T t) := slice hFu htT
  have hp : ContDiff ℝ ∞ (fracSelfSimilarPressure α a P T t) := slice hSp htT
  have hpt : ContDiff ℝ ∞ (fracApproxPressure α a P T t) := slice hFp htT
  have heq : ∀ y, dist y center ≤ centralRadius / 4 →
      fracApproxField α a U T t y = fracSelfSimilar α a U T t y :=
    fun y hy => (hFrest t htT y).2.2 hy
  have hm : 0 ≤ (T - t) ^ (1 / (2 * α)) := Real.rpow_nonneg (by linarith) _
  obtain ⟨hD3, hdbd⟩ : (∀ y, ‖iteratedFDeriv ℝ 3
        (fracApproxField α a U T t - fracSelfSimilar α a U T t) y‖ ≤ G) ∧
      (∀ y, ‖(fracApproxField α a U T t - fracSelfSimilar α a U T t) y‖ ≤ G) := by
    have h := difference_bound α h1 _ _ hw hu heq (fun y hy => ((hFrest t htT y).2.1 hy).1)
      CA CD _ hm (fun y hy => hCA T t hT hT1 ht htT y hy)
      (fun y j hj => (hCD T t hT hT1 ht htT y).1 j hj)
    rw [← hGdef] at h
    exact h
  have hdiff : ContDiff ℝ ∞ (fracApproxField α a U T t - fracSelfSimilar α a U T t) := hw.sub hu
  have hzD : ∀ y ∈ closedBall center (centralRadius / 4),
      (fracApproxField α a U T t - fracSelfSimilar α a U T t) y = 0 := fun y hy => by
    simp [heq y (mem_closedBall.1 hy)]
  have hxD : ∀ j : ℕ, iteratedFDeriv ℝ j
      (fracApproxField α a U T t - fracSelfSimilar α a U T t) x = 0 := fun j =>
    iteratedFDeriv_eq_zero_closedBall hdiff hR hzD (mem_closedBall.2 hxc) j
  have hubd : ∃ C : ℝ, ∀ y, ‖fracSelfSimilar α a U T t y‖ ≤ C := by
    refine ⟨max CD 0 * ((T - t) ^ (1 / (2 * α))) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))), fun y => ?_⟩
    have h0 := (hCD T t hT hT1 ht htT y).1 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h0
    have hmpos : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos (by linarith) _
    have hX0 : 0 ≤ ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    have hX : ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) ≤
        ((T - t) ^ (1 / (2 * α))) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos hmpos (by linarith [norm_nonneg (y - center)])
        (by push_cast; linarith)
    calc ‖fracSelfSimilar α a U T t y‖
        ≤ CD * ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) := h0
      _ ≤ max CD 0 * ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (le_max_right _ _)
  have hintD := hI α h1 hα3 _ hdiff (Or.inr ⟨G, hdbd⟩) x
  have hintu := hI α h1 hα3 _ hu (Or.inr hubd) x
  have hderiv : deriv (fun τ => fracApproxField α a U T τ x) t =
      deriv (fun τ => fracSelfSimilar α a U T τ x) t :=
    Filter.EventuallyEq.deriv_eq (show (fun τ => fracApproxField α a U T τ x) =ᶠ[𝓝 t]
      (fun τ => fracSelfSimilar α a U T τ x) from
      Filter.eventually_of_mem (Iio_mem_nhds htT) fun τ hτ => (hFrest τ hτ x).2.2 hxc)
  have hfd : fderiv ℝ (fracApproxField α a U T t) x = fderiv ℝ (fracSelfSimilar α a U T t) x := by
    have hz : ∀ y ∈ closedBall center (centralRadius / 4),
        (fracApproxField α a U T t - fracSelfSimilar α a U T t) y = 0 := fun y hy => by
      simp [heq y (mem_closedBall.1 hy)]
    have h0 := fderiv_eq_zero_of_const hdiff hR 0 hz (mem_closedBall.2 hxc)
    rw [fderiv_sub (hw.differentiable (by simp) x) (hu.differentiable (by simp) x)] at h0
    exact sub_eq_zero.1 h0
  have hadv : advectionAt (fracApproxField α a U T t) x = advectionAt (fracSelfSimilar α a U T t) x := by
    unfold advectionAt
    rw [hfd, heq x hxc]
  have hgrad : gradientAt (fracApproxPressure α a P T t) x =
      gradientAt (fracSelfSimilarPressure α a P T t) x := by
    have hz : ∀ y ∈ closedBall center (centralRadius / 4),
        (fracApproxPressure α a P T t - fracSelfSimilarPressure α a P T t) y =
          -(fracSelfSimilarPressure α a P T t pressureAnchor) := fun y hy => by
      simp only [Pi.sub_apply, fracApproxPressure, centralCut_inner (mem_closedBall.1 hy), one_mul]
      ring
    have h0 := fderiv_eq_zero_of_const (hpt.sub hp) hR _ hz (mem_closedBall.2 hxc)
    rw [fderiv_fun_sub (hpt.differentiable (by simp) x) (hp.differentiable (by simp) x)] at h0
    unfold gradientAt
    rw [sub_eq_zero.1 h0]
  have hadd := hAdd α (fracApproxField α a U T t - fracSelfSimilar α a U T t)
    (fracSelfSimilar α a U T t) x hintD hintu (hdiff.differentiable (by simp) x)
    (hu.differentiable (by simp) x) ((hdiff.of_le (le_infty 2)).contDiffAt)
    ((hu.of_le (le_infty 2)).contDiffAt)
  rw [sub_add_cancel] at hadd
  have hres : fracSpaceResidual α a U P T t x =
      fractionalPowerAt α (fracApproxField α a U T t - fracSelfSimilar α a U T t) x := by
    have e0 := (hSeq t htT x).2
    unfold fracSpaceResidual
    rw [hderiv, hadv, hgrad, hadd]
    calc _ = (deriv (fun τ => fracSelfSimilar α a U T τ x) t
          + advectionAt (fracSelfSimilar α a U T t) x
          + fractionalPowerAt α (fracSelfSimilar α a U T t) x
          + gradientAt (fracSelfSimilarPressure α a P T t) x)
          + fractionalPowerAt α (fracApproxField α a U T t - fracSelfSimilar α a U T t) x := by
          abel
      _ = _ := by rw [e0, zero_add]
  have hmeasD : AEStronglyMeasurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      ‖(fracApproxField α a U T t - fracSelfSimilar α a U T t) (x + z)‖) volume :=
    ((measurable_norm.pow_const _).mul
      ((hdiff.continuous.comp (continuous_const.add continuous_id)).norm.measurable)).aestronglyMeasurable
  have hpt_le : ∀ z : Space, ‖z‖ ^ (-(3 + 2 * α)) *
      ‖(fracApproxField α a U T t - fracSelfSimilar α a U T t) (x + z)‖ ≤
        G * ‖z‖ ^ (-(3 + 2 * α)) := fun z => by
    rw [mul_comm G]
    exact mul_le_mul_of_nonneg_left (hdbd _) (Real.rpow_nonneg (norm_nonneg _) _)
  have htailInt : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      ‖(fracApproxField α a U T t - fracSelfSimilar α a U T t) (x + z)‖) {z : Space | 1 < ‖z‖} :=
    (hKball.const_mul G).mono' hmeasD.restrict (ae_restrict_of_forall_mem hmeas fun z _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (norm_nonneg _))]
      exact hpt_le z)
  have htail : ∫ z in {z : Space | 1 < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) *
      ‖(fracApproxField α a U T t - fracSelfSimilar α a U T t) (x + z)‖ ≤ G * I := by
    rw [hIdef, ← integral_const_mul]
    exact setIntegral_mono_on htailInt (hKball.const_mul G) hmeas (fun z _ => hpt_le z)
  have hA0 : ‖(fracApproxField α a U T t - fracSelfSimilar α a U T t) x‖ ≤ 0 := by
    rw [hzD x (mem_closedBall.2 hxc), norm_zero]
  have hA1 : ‖fderiv ℝ (fracApproxField α a U T t - fracSelfSimilar α a U T t) x‖ ≤ 0 := by
    rw [← norm_iteratedFDeriv_one, hxD 1, norm_zero]
  have hA2 : ‖iteratedFDeriv ℝ 2 (fracApproxField α a U T t - fracSelfSimilar α a U T t) x‖ ≤ 0 := by
    rw [hxD 2, norm_zero]
  have hbd := hCP _ (hdiff.of_le (le_infty 3)) x 1 0 G (G * I) zero_lt_one le_rfl hintD
    (fun y _ => hD3 y) hA0 hA1 hA2 htailInt htail
  rw [hres]
  have hexp : -(2 - 3 / (2 * α)) ≤ 0 := by
    have : 3 / (2 * α) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have h1le : 1 ≤ (T - t) ^ (-(2 - 3 / (2 * α))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) hexp
  calc _ ≤ CP * (G * 1 ^ (3 - 2 * α) + 0 * 1 ^ (-(2 * α)) + G * I) := hbd
    _ ≤ _ := le_mul_of_one_le_right hK0 h1le

end Breakdown.Periodic
