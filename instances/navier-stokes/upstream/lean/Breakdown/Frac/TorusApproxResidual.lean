import Breakdown.Frac.StTorusStepApprox
import Breakdown.Torus.ApproxResidual

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracApproxResidual.Internal

theorem force_bound {α e : ℝ} {F : ℝ → Space → Space} {a b t M C0 : ℝ} (he1 : e < 1) (hC0 : 0 ≤ C0)
    (hM : 0 ≤ M)
    (hCst : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ G : Space → Space, Continuous G → IsPeriodic G →
      ‖fracTorusForce α τ G‖ ≤ C0 * τ ^ (-e) * Real.sqrt (∫ x in cell, ‖G x‖ ^ 2))
    (hF : ∀ r ∈ Icc a b, Continuous (F r) ∧ IsPeriodic (F r) ∧ ∀ x, ‖F r x‖ ≤ M)
    (hba : b - a ≤ 1) (ht : t ∈ Icc a b) :
    ‖∫ r in a..t, fracTorusForce α (t - r) (F r)‖ ≤
      C0 * (M * Real.sqrt (volume.real cell)) * ((t - a) ^ (-e + 1) / (-e + 1)) := by
  obtain ⟨hta, htb⟩ := ht
  have hv := Real.sqrt_nonneg (volume.real cell)
  set B := C0 * (M * Real.sqrt (volume.real cell)) with hBdef
  have hB : 0 ≤ B := by positivity
  have hg : IntervalIntegrable (fun r => B * (t - r) ^ (-e)) volume a t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := 0)
      (by linarith : (-1 : ℝ) < -e)).comp_sub_left t
    simp only [sub_sub_cancel, sub_zero] at h
    exact h.const_mul B
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t := compl_mem_ae_iff.mpr (measure_singleton t)
  have hbound : ∀ᵐ r ∂volume, r ∈ Ioc a t →
      ‖fracTorusForce α (t - r) (F r)‖ ≤ B * (t - r) ^ (-e) := by
    filter_upwards [hne] with r hrt hr
    have h : r < t := lt_of_le_of_ne hr.2 hrt
    have hr' : r ∈ Icc a b := ⟨hr.1.le, h.le.trans htb⟩
    obtain ⟨hc, hp, hbd⟩ := hF r hr'
    have hτ : 0 < t - r := by linarith
    have hτ1 : t - r ≤ 1 := by linarith [hr.1]
    have hq : 0 ≤ C0 * (t - r) ^ (-e) := mul_nonneg hC0 (rpow_nonneg hτ.le _)
    calc ‖fracTorusForce α (t - r) (F r)‖ ≤ C0 * (t - r) ^ (-e) * Real.sqrt (∫ x in cell, ‖F r x‖ ^ 2) :=
          hCst _ hτ hτ1 _ hc hp
      _ ≤ C0 * (t - r) ^ (-e) * (M * Real.sqrt (volume.real cell)) :=
          mul_le_mul_of_nonneg_left (ApproxResidual.Internal.sqrt_integral_le hM hbd) hq
      _ = B * (t - r) ^ (-e) := by rw [hBdef]; ring
  refine (intervalIntegral.norm_integral_le_of_norm_le hta hbound hg).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-e)) t, sub_self,
    integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
  ring

set_option maxHeartbeats 2000000 in
theorem step_identity {α : ℝ} (hα : 1 < α) {u : ℝ → V} {F : ℝ → Space → Space} {a μ L : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hL : 0 ≤ L) (hm : IsFracTorusForcedMildOnIcc α u F a (a + μ * L))
    (P : Piece V L) (hP : ∀ s : Icc (0 : ℝ) L, P s = μ ^ dilExponent α • u (a + μ * s))
    (s : Icc (0 : ℝ) L) :
    P s - (fracStepFrame α hα μ hμ hμ1).G s (extendPiece P 0) -
      ∫ σ in (0 : ℝ)..s, (fracStepFrame α hα μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ) =
      μ ^ dilExponent α • ∫ r in a..a + μ * s, fracTorusForce α (a + μ * s - r) (F r) := by
  obtain ⟨s, hs⟩ := s
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ L := hs.2
  have ht : a + μ * s ∈ Icc a (a + μ * L) := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨-, -, heq⟩ := hm.2 _ ht
  have hE : ∀ σ ∈ Icc (0 : ℝ) L, extendPiece P σ = μ ^ dilExponent α • u (a + μ * σ) := by
    intro σ hσ
    rw [extendPiece, dif_pos hL, Set.IccExtend_of_mem hL P hσ, hP]
  have e34 : μ ^ (3 / (4 * α)) * μ ^ dilExponent α = μ := by
    rw [← rpow_add hμ, show 3 / (4 * α) + dilExponent α = 1 by unfold dilExponent; ring, rpow_one]
  have hK' : EqOn (fun σ => (fracStepFrame α hα μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ))
      (fun σ => μ • (μ ^ dilExponent α •
        fracTorusKernel α (a + μ * s - (a + μ * σ)) (u (a + μ * σ)) (u (a + μ * σ))))
      (uIcc (0 : ℝ) s) := by
    intro σ hσ
    dsimp only
    rw [uIcc_of_le hs0] at hσ
    rw [hE σ ⟨hσ.1, hσ.2.trans hs1⟩]
    show ((μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * (s - σ))) _ _ = _
    rw [show a + μ * s - (a + μ * σ) = μ * (s - σ) by ring]
    simp only [smul_apply, map_smul, smul_smul]
    congr 1
    linear_combination μ ^ dilExponent α * e34
  have hc : ∫ σ in (0 : ℝ)..s, fracTorusKernel α (a + μ * s - (a + μ * σ)) (u (a + μ * σ)) (u (a + μ * σ)) =
      μ⁻¹ • ∫ r in a + μ * 0..a + μ * s, fracTorusKernel α (a + μ * s - r) (u r) (u r) :=
    intervalIntegral.integral_comp_add_mul (fun r => fracTorusKernel α (a + μ * s - r) (u r) (u r)) hμ.ne' a
  have hint : ∫ σ in (0 : ℝ)..s,
      (fracStepFrame α hα μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ) =
      μ ^ dilExponent α • ∫ r in a..a + μ * s, fracTorusKernel α (a + μ * s - r) (u r) (u r) := by
    rw [intervalIntegral.integral_congr hK']
    rw [intervalIntegral.integral_smul]
    rw [intervalIntegral.integral_smul]
    rw [hc]
    rw [mul_zero, add_zero]
    generalize (∫ r in a..a + μ * s, fracTorusKernel α (a + μ * s - r) (u r) (u r)) = I
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  rw [hint, hP, hE 0 ⟨le_rfl, hL⟩, mul_zero, add_zero]
  change μ ^ dilExponent α • u (a + μ * s) - fracTorusHeat α (μ * s) (μ ^ dilExponent α • u a) - _ = _
  rw [heq, add_sub_cancel_left, map_smul, smul_add, smul_add]
  abel

theorem scale_le {T lam θ p : ℝ} (hT : 0 < T) (hl : 0 < lam) (hθ : lam ^ p < θ) (n : ℕ) :
    (stepScale T lam n) ^ p ≤ θ ^ n * T ^ p := by
  unfold stepScale
  rw [Real.mul_rpow hT.le (pow_nonneg hl.le n), ← Real.rpow_natCast lam n, ← Real.rpow_mul hl.le,
    mul_comm (n : ℝ), Real.rpow_mul hl.le, Real.rpow_natCast, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (rpow_nonneg hl.le _) hθ.le n) (rpow_nonneg hT.le _)

theorem rate_le {α μ lam s : ℝ} (hα : 1 < α) (hμ : 0 < μ) (hl : 0 < lam) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    μ ^ dilExponent α * (μ * lam) ^ (-(2 - 3 / (2 * α))) * (μ * s) ^ (-(1 / (2 * α)) + 1) ≤
      μ ^ (1 / (4 * α)) * lam ^ (-(2 - 3 / (2 * α))) := by
  rw [Real.mul_rpow hμ.le hl.le, Real.mul_rpow hμ.le hs0]
  have hα0 : 0 < α := by linarith
  have e : μ ^ dilExponent α * μ ^ (-(2 - 3 / (2 * α))) * μ ^ (-(1 / (2 * α)) + 1) =
      μ ^ (1 / (4 * α)) := by
    rw [← rpow_add hμ, ← rpow_add hμ]
    congr 1
    unfold dilExponent
    field_simp
    ring
  have hg : 1 / (2 * α) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h1 : s ^ (-(1 / (2 * α)) + 1) ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)
  have h2 : 0 ≤ lam ^ (-(2 - 3 / (2 * α))) := rpow_nonneg hl.le _
  have h3 : 0 ≤ μ ^ (1 / (4 * α)) := rpow_nonneg hμ.le _
  calc μ ^ dilExponent α * (μ ^ (-(2 - 3 / (2 * α))) * lam ^ (-(2 - 3 / (2 * α)))) *
        (μ ^ (-(1 / (2 * α)) + 1) * s ^ (-(1 / (2 * α)) + 1))
      = (μ ^ dilExponent α * μ ^ (-(2 - 3 / (2 * α))) * μ ^ (-(1 / (2 * α)) + 1)) *
          lam ^ (-(2 - 3 / (2 * α))) * s ^ (-(1 / (2 * α)) + 1) := by ring
    _ ≤ μ ^ (1 / (4 * α)) * lam ^ (-(2 - 3 / (2 * α))) * 1 := by
        rw [e]; exact mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h2)
    _ = μ ^ (1 / (4 * α)) * lam ^ (-(2 - 3 / (2 * α))) := by ring

end FracApproxResidual.Internal

open FracApproxResidual.Internal

set_option maxHeartbeats 2000000 in
theorem fracApproxResidualSmall (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hA : FracApproxFieldProperties α)
    (hR : FracApproxResidualBound α) (hL : FracApproxLinks α) (hF : FracApproxForcedSolution α)
    (hM : FracForcedPeriodicIsMild α) (hS : FracForceSmoothing α) : FracApproxResidualSmall α hα := by
  intro a U P lam θ hl hl1 hW hθ
  obtain ⟨K, hKb⟩ := hR a U P hW
  obtain ⟨C0, hC0, hCst⟩ := hS
  have hα0 : 0 < α := by linarith
  have hv := Real.sqrt_nonneg (volume.real cell)
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have he1 : 1 / (2 * α) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hg1 : 0 < -(1 / (2 * α)) + 1 := by linarith
  have hnp : -(2 - 3 / (2 * α)) ≤ 0 := by
    have : 3 / (2 * α) ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hlr : 0 ≤ lam ^ (-(2 - 3 / (2 * α))) := rpow_nonneg hl.le _
  have hc1 : 0 ≤ C0 * (max K 0 * Real.sqrt (volume.real cell)) / (-(1 / (2 * α)) + 1) :=
    div_nonneg (mul_nonneg hC0.le (mul_nonneg hK0 hv)) hg1.le
  have hc0 : 0 ≤ C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(2 - 3 / (2 * α))) /
      (-(1 / (2 * α)) + 1) :=
    div_nonneg (mul_nonneg (mul_nonneg hC0.le (mul_nonneg hK0 hv)) hlr) hg1.le
  have hθ0 : 0 ≤ θ := (rpow_nonneg hl.le _).trans hθ.le
  refine ⟨C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(2 - 3 / (2 * α))) /
      (-(1 / (2 * α)) + 1), hc0, fun T hT hT1 n => ?_⟩
  have hμ := stepScale_pos hT hl n
  have hμ1 := stepScale_le_one hT1 hl hl1.le n
  have hμT : stepScale T lam n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
  have hLm : 0 < 1 - lam := by linarith
  have ha : 0 ≤ stepStart T lam n := by unfold stepStart; linarith
  have hb : stepStart T lam n + stepScale T lam n * (1 - lam) < T := by
    unfold stepStart; nlinarith [mul_pos hμ hl]
  have hab : stepStart T lam n < stepStart T lam n + stepScale T lam n * (1 - lam) := by
    nlinarith [mul_pos hμ hLm]
  have hsol := hF a U P hW T _ _ hT hab hb
  have hmild := hM _ _ _ _ _ hab hsol
  obtain ⟨hPB, -, hPF, -⟩ :=
    pieceOperator V (fracStepFrame α hα (stepScale T lam n) hμ hμ1) (1 - lam) hLm
  rw [ContinuousMap.norm_le _ (mul_nonneg (pow_nonneg hθ0 n) (mul_nonneg hc0 (rpow_nonneg hT.le _)))]
  intro s
  rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hPB, hPF,
    step_identity hα hμ hμ1 hLm.le hmild _ (hL a U P T lam hW hT hT1 hl hl1 n).1 s,
    norm_smul, Real.norm_of_nonneg (rpow_nonneg hμ.le _)]
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 - lam := s.2.2
  have hFr : ∀ r ∈ Icc (stepStart T lam n) (stepStart T lam n + stepScale T lam n * (1 - lam)),
      Continuous (fracApproxResidual α a U P T r) ∧ IsPeriodic (fracApproxResidual α a U P T r) ∧
        ∀ x, ‖fracApproxResidual α a U P T r x‖ ≤
          max K 0 * (stepScale T lam n * lam) ^ (-(2 - 3 / (2 * α))) := by
    intro r hr
    refine ⟨Forced.Internal.sliceContinuous hsol.2.2.1 hr, (hsol.2.2.2.1 r hr).2.2, fun x => ?_⟩
    have h1 := hKb T r hT hT1 (ha.trans hr.1) (hr.2.trans_lt hb) x
    have hTr : stepScale T lam n * lam ≤ T - r := by
      have := hr.2; unfold stepStart at this; nlinarith
    have h2 : (T - r) ^ (-(2 - 3 / (2 * α))) ≤ (stepScale T lam n * lam) ^ (-(2 - 3 / (2 * α))) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hμ hl) hTr hnp
    have h3 : 0 ≤ (T - r) ^ (-(2 - 3 / (2 * α))) := rpow_nonneg (by linarith [hr.2]) _
    calc ‖fracApproxResidual α a U P T r x‖ ≤ K * (T - r) ^ (-(2 - 3 / (2 * α))) := h1
      _ ≤ max K 0 * (T - r) ^ (-(2 - 3 / (2 * α))) := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max K 0 * (stepScale T lam n * lam) ^ (-(2 - 3 / (2 * α))) :=
          mul_le_mul_of_nonneg_left h2 hK0
  have hM' : 0 ≤ max K 0 * (stepScale T lam n * lam) ^ (-(2 - 3 / (2 * α))) :=
    mul_nonneg hK0 (rpow_nonneg (mul_pos hμ hl).le _)
  have hbd := force_bound (α := α) (e := 1 / (2 * α)) he1 hC0.le hM' hCst hFr (by nlinarith)
    (t := stepStart T lam n + stepScale T lam n * s) ⟨by nlinarith, by nlinarith⟩
  rw [add_sub_cancel_left] at hbd
  have hrate := rate_le hα hμ hl hs0 (by linarith)
  have hsc := scale_le hT hl hθ n
  have hμq : 0 ≤ stepScale T lam n ^ dilExponent α := rpow_nonneg hμ.le _
  calc stepScale T lam n ^ dilExponent α *
        ‖∫ r in stepStart T lam n..stepStart T lam n + stepScale T lam n * s,
          fracTorusForce α (stepStart T lam n + stepScale T lam n * s - r) (fracApproxResidual α a U P T r)‖
      ≤ stepScale T lam n ^ dilExponent α * (C0 * (max K 0 * (stepScale T lam n * lam) ^ (-(2 - 3 / (2 * α))) *
          Real.sqrt (volume.real cell)) * ((stepScale T lam n * s) ^ (-(1 / (2 * α)) + 1) /
            (-(1 / (2 * α)) + 1))) :=
        mul_le_mul_of_nonneg_left hbd hμq
    _ = (C0 * (max K 0 * Real.sqrt (volume.real cell)) / (-(1 / (2 * α)) + 1)) *
          (stepScale T lam n ^ dilExponent α * (stepScale T lam n * lam) ^ (-(2 - 3 / (2 * α))) *
            (stepScale T lam n * s) ^ (-(1 / (2 * α)) + 1)) := by ring
    _ ≤ (C0 * (max K 0 * Real.sqrt (volume.real cell)) / (-(1 / (2 * α)) + 1)) *
          (stepScale T lam n ^ (1 / (4 * α)) * lam ^ (-(2 - 3 / (2 * α)))) :=
        mul_le_mul_of_nonneg_left hrate hc1
    _ = (C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(2 - 3 / (2 * α))) /
          (-(1 / (2 * α)) + 1)) * stepScale T lam n ^ (1 / (4 * α)) := by ring
    _ ≤ (C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(2 - 3 / (2 * α))) /
          (-(1 / (2 * α)) + 1)) * (θ ^ n * T ^ (1 / (4 * α))) := mul_le_mul_of_nonneg_left hsc hc0
    _ = θ ^ n * ((C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(2 - 3 / (2 * α))) /
          (-(1 / (2 * α)) + 1)) * T ^ (1 / (4 * α))) := by ring

end Breakdown.Periodic
