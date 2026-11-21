import Breakdown.FracCert.DecayPressureParts
import Breakdown.Uniqueness.FundSolEnergyAux
import Breakdown.Uniqueness.FundSolMeanValueAux

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Breakdown.FracCert.DecayPressureVanish

open Breakdown.FundSol Breakdown.FundSol.Internal

private theorem second_le_of_localMax {w : Space → ℝ} (hw : ContDiff ℝ ∞ w) {x : Space}
    (hx : IsLocalMax w x) (v : Space) : fderiv ℝ (fderiv ℝ w) x v v ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hw1 : ContDiff ℝ ∞ (fderiv ℝ w) := (contDiff_infty_iff_fderiv.1 hw).2
  have hwd1 : Differentiable ℝ (fderiv ℝ w) := hw1.differentiable (by simp)
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have d1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w (x + t • v)) (fderiv ℝ w (x + t • v) v) t :=
    fun t => (hwd (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hd1 : deriv (fun t : ℝ => w (x + t • v)) = fun t => fderiv ℝ w (x + t • v) v :=
    funext fun t => (d1 t).deriv
  have d2 : HasDerivAt (fun t : ℝ => fderiv ℝ w (x + t • v) v) (fderiv ℝ (fderiv ℝ w) x v v) 0 := by
    have h := (hwd1 (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
    have h' := h.clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using h'
  have hdd : deriv (deriv (fun t : ℝ => w (x + t • v))) 0 > 0 := by
    rw [hd1, d2.deriv]; exact hpos
  have hd0 : deriv (fun t : ℝ => w (x + t • v)) 0 = 0 := by
    rw [hd1]; simp [hx.fderiv_eq_zero]
  have hcont : ContinuousAt (fun t : ℝ => w (x + t • v)) 0 := (d1 0).continuousAt
  have hmin : IsLocalMin (fun t : ℝ => w (x + t • v)) 0 :=
    isLocalMin_of_deriv_deriv_pos hdd hd0 hcont
  have hmax : IsLocalMax (fun t : ℝ => w (x + t • v)) 0 := by
    have hg : ContinuousAt (fun t : ℝ => x + t • v) 0 := (hline 0).continuousAt
    have hx' : IsLocalMax w ((fun t : ℝ => x + t • v) 0) := by
      rw [show (fun t : ℝ => x + t • v) 0 = x by simp]; exact hx
    exact IsLocalMax.comp_continuous (g := fun t : ℝ => x + t • v) hx' hg
  have hc : (fun t : ℝ => w (x + t • v)) =ᶠ[𝓝 0] fun _ => w (x + (0 : ℝ) • v) :=
    (Filter.Eventually.and hmin hmax).mono fun t h => le_antisymm h.2 h.1
  have hdc : deriv (fun t : ℝ => w (x + t • v)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
    hc.eventuallyEq_nhds.mono fun t ht => by rw [ht.deriv_eq]; simp
  have h0 : deriv (deriv (fun t : ℝ => w (x + t • v))) 0 = 0 := by rw [hdc.deriv_eq]; simp
  linarith

private theorem trace_le_of_localMax {w : Space → ℝ} (hw : ContDiff ℝ ∞ w) {x : Space}
    (hx : IsLocalMax w x) : scalarSumSecondPartials w x ≤ 0 := by
  unfold scalarSumSecondPartials secondPartial
  refine Finset.sum_nonpos fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simpa using second_le_of_localMax hw hx (unitVector i)

private theorem trace_quadratic (ε : ℝ) (x : Space) :
    scalarSumSecondPartials (fun y : Space => ε * ‖y‖ ^ 2) x = 6 * ε := by
  have hdφ : deriv (fun s : ℝ => ε * s) = fun _ => ε :=
    funext fun s => by simpa using ((hasDerivAt_id s).const_mul ε).deriv
  have h := scalarSumSecondPartials_comp_norm_sq (φ := fun s : ℝ => ε * s) (x := x)
    (Eventually.of_forall fun _ => by fun_prop) (by rw [hdφ]; exact differentiableAt_const _)
  rw [h, hdφ]
  simp

private theorem nonpos_of_decay {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (htr : ∀ y, scalarSumSecondPartials g y = 0)
    (hdec : ∀ m > 0, ∃ R, ∀ y, R ≤ ‖y‖ → g y ≤ m) : ∀ y, g y ≤ 0 := by
  intro x0
  by_contra hneg
  push_neg at hneg
  obtain ⟨R0, hR0⟩ := hdec (g x0 / 2) (by linarith)
  set R := max R0 (‖x0‖ + 1) with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  set ε := g x0 / (4 * R ^ 2) with hεdef
  have hε : 0 < ε := by positivity
  have hq : ContDiff ℝ ∞ (fun y : Space => ε * ‖y‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hwc : ContDiff ℝ ∞ (g + fun y : Space => ε * ‖y‖ ^ 2) := hg.add hq
  have hcpt : IsCompact (Metric.closedBall (0 : Space) R) := isCompact_closedBall _ _
  have hx0 : x0 ∈ Metric.closedBall (0 : Space) R := by
    rw [mem_closedBall_zero_iff]; exact le_trans (by linarith) (le_max_right _ _)
  obtain ⟨x1, hx1, hmax⟩ := hcpt.exists_isMaxOn ⟨x0, hx0⟩ hwc.continuous.continuousOn
  have hw0 : g x0 ≤ (g + fun y : Space => ε * ‖y‖ ^ 2) x0 := by
    simp only [Pi.add_apply]; nlinarith [sq_nonneg ‖x0‖]
  have hlt : ‖x1‖ < R := by
    by_contra hge
    push_neg at hge
    have hx1' : ‖x1‖ ≤ R := mem_closedBall_zero_iff.1 hx1
    have hgx : g x1 ≤ g x0 / 2 := hR0 x1 (le_trans (le_max_left _ _) hge)
    have hn : ‖x1‖ = R := le_antisymm hx1' hge
    have h1 : (g + fun y : Space => ε * ‖y‖ ^ 2) x1 = g x1 + g x0 / 4 := by
      simp only [Pi.add_apply, hn, hεdef]
      field_simp
    have h2 : (g + fun y : Space => ε * ‖y‖ ^ 2) x0 ≤ (g + fun y : Space => ε * ‖y‖ ^ 2) x1 :=
      hmax hx0
    linarith
  have hloc : IsLocalMax (g + fun y : Space => ε * ‖y‖ ^ 2) x1 :=
    hmax.isLocalMax (Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hlt)) Metric.ball_subset_closedBall)
  have hle := trace_le_of_localMax hwc hloc
  have hadd : scalarSumSecondPartials (g + fun y : Space => ε * ‖y‖ ^ 2) x1 =
      scalarSumSecondPartials g x1 + scalarSumSecondPartials (fun y : Space => ε * ‖y‖ ^ 2) x1 := by
    unfold scalarSumSecondPartials secondPartial
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_add_apply (hg.contDiffAt.of_le ENat.LEInfty.out)
      (hq.contDiffAt.of_le ENat.LEInfty.out)]
    rfl
  rw [hadd, htr, trace_quadratic] at hle
  linarith

private theorem dir_harmonic {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (htr : ∀ y, scalarSumSecondPartials h y = 0) (v : Space) (y : Space) :
    scalarSumSecondPartials (dirDeriv v h) y = 0 := by
  have hv := contDiff_dirDeriv hh v
  have hsum : (fun x => ∑ i : Fin 3, dirDeriv (unitVector i) (dirDeriv (unitVector i) h) x) =
      fun _ => (0 : ℝ) := by
    funext x
    rw [← htr x]
    unfold scalarSumSecondPartials
    exact Finset.sum_congr rfl fun i _ => (secondPartial_eq_dirDeriv hh i i x).symm
  have e : ∀ i, secondPartial (dirDeriv v h) i i y =
      dirDeriv v (dirDeriv (unitVector i) (dirDeriv (unitVector i) h)) y := by
    intro i
    rw [secondPartial_eq_dirDeriv hv, dirDeriv_comm hh (unitVector i) v,
      dirDeriv_comm (contDiff_dirDeriv hh _) (unitVector i) v]
  unfold scalarSumSecondPartials
  rw [Finset.sum_congr rfl fun i _ => e i]
  have hdiff : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (dirDeriv (unitVector i) (dirDeriv (unitVector i) h)) y :=
    fun i _ => (contDiff_dirDeriv (contDiff_dirDeriv hh _) _).differentiable (by simp) y
  have hs : ∑ i : Fin 3, dirDeriv v (dirDeriv (unitVector i) (dirDeriv (unitVector i) h)) y =
      dirDeriv v (fun x => ∑ i : Fin 3, dirDeriv (unitVector i) (dirDeriv (unitVector i) h) x) y := by
    show _ = fderiv ℝ (fun x => ∑ i : Fin 3, dirDeriv (unitVector i) (dirDeriv (unitVector i) h) x) y v
    rw [fderiv_fun_sum hdiff, ContinuousLinearMap.sum_apply]
    rfl
  rw [hs, hsum]
  simp [dirDeriv]

theorem decayingGradientVanishes : DecayingGradientVanishesStatement := by
  intro h hh htr K s hs hdec y
  have hlim : ∀ m > 0, ∃ R, ∀ y : Space, R ≤ ‖y‖ → K * (1 + ‖y‖) ^ (-s) ≤ m := by
    intro m hm
    have ht : Tendsto (fun r : ℝ => K * (1 + r) ^ (-s)) atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_neg_atTop hs).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
      simpa [Function.comp_def] using h1.const_mul K
    obtain ⟨R, hR⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hm))
    exact ⟨R, fun y hy => (hR ‖y‖ hy).le⟩
  have hcomp : ∀ v : Space, ‖v‖ = 1 → ∀ x, dirDeriv v h x ≤ 0 := by
    intro v hv
    refine nonpos_of_decay (contDiff_dirDeriv hh v) (dir_harmonic hh htr v) fun m hm => ?_
    obtain ⟨R, hR⟩ := hlim m hm
    refine ⟨R, fun x hx => ?_⟩
    calc dirDeriv v h x ≤ ‖fderiv ℝ h x v‖ := le_abs_self _
      _ ≤ ‖fderiv ℝ h x‖ * ‖v‖ := (fderiv ℝ h x).le_opNorm v
      _ = ‖fderiv ℝ h x‖ := by rw [hv, mul_one]
      _ ≤ K * (1 + ‖x‖) ^ (-s) := hdec x
      _ ≤ m := hR x hx
  have hzero : ∀ i : Fin 3, fderiv ℝ h y (unitVector i) = 0 := by
    intro i
    have h1 := hcomp (unitVector i) (norm_unitVector i) y
    have h2 := hcomp (-unitVector i) (by rw [norm_neg, norm_unitVector]) y
    unfold dirDeriv at h1 h2
    rw [map_neg] at h2
    linarith
  ext w
  have hw : w = ∑ i : Fin 3, w i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w).symm
  rw [hw, map_sum]
  simp [hzero]

end Breakdown.FracCert.DecayPressureVanish
