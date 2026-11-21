import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.CompareFrame
import Breakdown.Frac.RBilinDilate

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusCompareFrame.Internal

open CompareFrame.Internal

theorem sqrtSim {α c : ℝ} (hc : 0 < c) : Real.sqrt (simScale α c) = c ^ (1 / (2 * α)) := by
  unfold simScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc.le]
  congr 1
  ring

theorem simPos {α c : ℝ} (hc : 0 < c) : 0 < simScale α c := Real.rpow_pos_of_pos hc _

theorem simLeOne {α c : ℝ} (hα : 0 < α) (hc : 0 < c) (hc1 : c ≤ 1) : simScale α c ≤ 1 :=
  Real.rpow_le_one hc.le hc1 (by positivity)

theorem gradWeight {α c : ℝ} (hc : 0 < c) :
    c ^ dilExponent α * simScale α c ^ (3 / 4 : ℝ) = c := by
  unfold simScale dilExponent
  rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc]
  conv_rhs => rw [← Real.rpow_one c]
  congr 1
  ring

theorem gradNormFactor {α c : ℝ} (hc : 0 < c) :
    c * simScale α c ^ (-(3 / 2 * (1 / 2 : ℝ))) = c ^ dilExponent α := by
  unfold simScale dilExponent
  rw [← Real.rpow_mul hc.le]
  conv_lhs => arg 1; rw [← Real.rpow_one c]
  rw [← Real.rpow_add hc]
  congr 1
  ring

theorem velWeight {α c : ℝ} (hc : 0 < c) :
    c ^ dilExponent α * simScale α c ^ (1 / 4 : ℝ) = c ^ (1 - 1 / (2 * α)) := by
  unfold simScale dilExponent
  rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc]
  congr 1
  ring

theorem velNormFactor {α c : ℝ} (hc : 0 < c) :
    c ^ (1 - 1 / (2 * α)) * simScale α c ^ (-(3 / 2 * (1 / 6 : ℝ))) = c ^ dilExponent α := by
  unfold simScale dilExponent
  rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc]
  congr 1
  ring

set_option maxHeartbeats 1000000 in
theorem gradPart {α μ c b : ℝ} (hα : 1 < α) (hD : Freq.FracDilationAlgebra α)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : IsShellScale μ (Real.sqrt (simScale α c) * b)) (Z : V) (Y : Freq.X)
    (j : Fin 3) :
    ‖(restrictTorus (μ * simScale α c) b (c ^ dilExponent α • Z) - restrictR3 b (Freq.fracDilX α c Y)).1 j‖ =
      c ^ dilExponent α * ‖(restrictTorus μ (Real.sqrt (simScale α c) * b) Z -
        restrictR3 (Real.sqrt (simScale α c) * b) Y).1 j‖ := by
  have hc' : 0 < simScale α c := simPos hc
  have hs : 0 < Real.sqrt (simScale α c) := Real.sqrt_pos.2 hc'
  have hμ : 0 < μ := hS.1
  have hS' := shellScale_mul hc' (simLeOne (by linarith) hc hc1) hS
  have e1 : (restrictTorus (μ * simScale α c) b (c ^ dilExponent α • Z) -
      restrictR3 b (Freq.fracDilX α c Y)).1 j =
      c ^ dilExponent α • (restrictTorus (μ * simScale α c) b Z).1 j -
        cutLp 2 b (Freq.partialX j (Freq.fracDilX α c Y)) := by
    simp only [Prod.fst_sub, Pi.sub_apply, restrictR3_fst, map_smul, Prod.smul_fst, Pi.smul_apply]
  have e2 : (restrictTorus μ (Real.sqrt (simScale α c) * b) Z - restrictR3 (Real.sqrt (simScale α c) * b) Y).1 j =
      (restrictTorus μ (Real.sqrt (simScale α c) * b) Z).1 j -
        cutLp 2 (Real.sqrt (simScale α c) * b) (Freq.partialX j Y) := by
    simp only [Prod.fst_sub, Pi.sub_apply, restrictR3_fst]
  rw [e1, e2]
  have hA1 : ((c ^ dilExponent α • (restrictTorus (μ * simScale α c) b Z).1 j : Freq.L2R) : Space → Space)
      =ᵐ[volume] fun y => c ^ dilExponent α • (Metric.closedBall (0 : Space) b).indicator
        (fun y => ((μ * simScale α c) ^ (3 / 4 : ℝ)) •
          Freq.realVec (torusSeries 2 (gradCoef j Z) (center + Real.sqrt (μ * simScale α c) • y))) y := by
    filter_upwards [Lp.coeFn_smul (c ^ dilExponent α) ((restrictTorus (μ * simScale α c) b Z).1 j),
      restrictTorus_fst_ae hS' Z j] with y h1 h2
    rw [h1, Pi.smul_apply, h2]
  have hB1 : ((cutLp 2 b (Freq.partialX j (Freq.fracDilX α c Y)) : Freq.L2R) : Space → Space) =ᵐ[volume]
      (Metric.closedBall (0 : Space) b).indicator
        (fun y => c • (Freq.partialX j Y : Space → Space) (Real.sqrt (simScale α c) • y)) := by
    classical
    filter_upwards [cutLp_apply 2 b (Freq.partialX j (Freq.fracDilX α c Y)),
      FracInternal.BilinDilate.partialX_fracDilX hD hc j Y] with y h1 h2
    rw [h1, Set.indicator_apply, Set.indicator_apply, h2, sqrtSim hc]
  have e : c ^ dilExponent α * (μ * simScale α c) ^ (3 / 4 : ℝ) = c * μ ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow hμ.le hc'.le, mul_left_comm, gradWeight hc, mul_comm]
  have hf := indicator_scale (b := b) hs (k0 := c ^ dilExponent α) (k := c)
    (f := fun y => ((μ * simScale α c) ^ (3 / 4 : ℝ)) •
      Freq.realVec (torusSeries 2 (gradCoef j Z) (center + Real.sqrt (μ * simScale α c) • y)))
    (g := fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j Z) (center + Real.sqrt μ • y)))
    (fun y => by
      rw [smul_smul, e, Real.sqrt_mul hμ.le, mul_smul (Real.sqrt μ) (Real.sqrt (simScale α c)) y, smul_smul c])
  have hg := fun y => (one_smul ℝ _).symm.trans (indicator_scale (b := b) hs (k0 := 1) (k := c)
    (f := fun y => c • (Freq.partialX j Y : Space → Space) (Real.sqrt (simScale α c) • y))
    (g := (Freq.partialX j Y : Space → Space)) (fun y => one_smul ℝ _) y)
  have key := sub_ae_comp_smul (p := 2) (k := c) hs (c ^ dilExponent α • (restrictTorus (μ * simScale α c) b Z).1 j)
    ((restrictTorus μ (Real.sqrt (simScale α c) * b) Z).1 j) (cutLp 2 b (Freq.partialX j (Freq.fracDilX α c Y)))
    (cutLp 2 (Real.sqrt (simScale α c) * b) (Freq.partialX j Y)) _ _ _ _ hA1 (restrictTorus_fst_ae hS Z j) hB1
    (cutLp_apply 2 (Real.sqrt (simScale α c) * b) (Freq.partialX j Y)) hf hg
  rw [norm_of_ae_comp_smul (p := 2) hs _ _ key, sqrt_cube_rpow hc', Real.norm_eq_abs, abs_of_pos hc]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  exact gradNormFactor hc

theorem velocityPart {α μ c b : ℝ} (hα : 1 < α) (hV : Freq.FracVelocityDilate α)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : IsShellScale μ (Real.sqrt (simScale α c) * b)) (Z : V) (Y : Freq.X) :
    ‖(restrictTorus (μ * simScale α c) b (c ^ dilExponent α • Z) - restrictR3 b (Freq.fracDilX α c Y)).2‖ =
      c ^ dilExponent α * ‖(restrictTorus μ (Real.sqrt (simScale α c) * b) Z -
        restrictR3 (Real.sqrt (simScale α c) * b) Y).2‖ := by
  have hc' : 0 < simScale α c := simPos hc
  have hs : 0 < Real.sqrt (simScale α c) := Real.sqrt_pos.2 hc'
  have hμ : 0 < μ := hS.1
  have hS' := shellScale_mul hc' (simLeOne (by linarith) hc hc1) hS
  have hk : 0 < c ^ (1 - 1 / (2 * α)) := Real.rpow_pos_of_pos hc _
  have e1 : (restrictTorus (μ * simScale α c) b (c ^ dilExponent α • Z) -
      restrictR3 b (Freq.fracDilX α c Y)).2 =
      c ^ dilExponent α • (restrictTorus (μ * simScale α c) b Z).2 -
        cutLp 6 b (Freq.velocity (Freq.fracDilX α c Y)) := by
    simp only [Prod.snd_sub, restrictR3_snd, map_smul, Prod.smul_snd]
  have e2 : (restrictTorus μ (Real.sqrt (simScale α c) * b) Z - restrictR3 (Real.sqrt (simScale α c) * b) Y).2 =
      (restrictTorus μ (Real.sqrt (simScale α c) * b) Z).2 -
        cutLp 6 (Real.sqrt (simScale α c) * b) (Freq.velocity Y) := by
    simp only [Prod.snd_sub, restrictR3_snd]
  rw [e1, e2]
  have hA1 : ((c ^ dilExponent α • (restrictTorus (μ * simScale α c) b Z).2 : Freq.L6R) : Space → Space)
      =ᵐ[volume] fun y => c ^ dilExponent α • (Metric.closedBall (0 : Space) b).indicator
        (fun y => ((μ * simScale α c) ^ (1 / 4 : ℝ)) •
          Freq.realVec (torusSeries 6 (coeff Z) (center + Real.sqrt (μ * simScale α c) • y))) y := by
    filter_upwards [Lp.coeFn_smul (c ^ dilExponent α) ((restrictTorus (μ * simScale α c) b Z).2),
      restrictTorus_snd_ae hS' Z] with y h1 h2
    rw [h1, Pi.smul_apply, h2]
  have hB1 : ((cutLp 6 b (Freq.velocity (Freq.fracDilX α c Y)) : Freq.L6R) : Space → Space) =ᵐ[volume]
      (Metric.closedBall (0 : Space) b).indicator
        (fun y => c ^ (1 - 1 / (2 * α)) • (Freq.velocity Y : Space → Space) (Real.sqrt (simScale α c) • y)) := by
    classical
    filter_upwards [cutLp_apply 6 b (Freq.velocity (Freq.fracDilX α c Y)), hV c hc Y] with y h1 h2
    rw [h1, Set.indicator_apply, Set.indicator_apply, h2, sqrtSim hc]
    rfl
  have e : c ^ dilExponent α * (μ * simScale α c) ^ (1 / 4 : ℝ) = c ^ (1 - 1 / (2 * α)) * μ ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow hμ.le hc'.le, mul_left_comm, velWeight hc, mul_comm]
  have hf := indicator_scale (b := b) hs (k0 := c ^ dilExponent α) (k := c ^ (1 - 1 / (2 * α)))
    (f := fun y => ((μ * simScale α c) ^ (1 / 4 : ℝ)) •
      Freq.realVec (torusSeries 6 (coeff Z) (center + Real.sqrt (μ * simScale α c) • y)))
    (g := fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff Z) (center + Real.sqrt μ • y)))
    (fun y => by
      rw [smul_smul, e, Real.sqrt_mul hμ.le, mul_smul (Real.sqrt μ) (Real.sqrt (simScale α c)) y,
        smul_smul (c ^ (1 - 1 / (2 * α)))])
  have hg := fun y => (one_smul ℝ _).symm.trans (indicator_scale (b := b) hs (k0 := 1)
    (k := c ^ (1 - 1 / (2 * α)))
    (f := fun y => c ^ (1 - 1 / (2 * α)) • (Freq.velocity Y : Space → Space) (Real.sqrt (simScale α c) • y))
    (g := (Freq.velocity Y : Space → Space)) (fun y => one_smul ℝ _) y)
  have key := sub_ae_comp_smul (p := 6) (k := c ^ (1 - 1 / (2 * α))) hs
    (c ^ dilExponent α • (restrictTorus (μ * simScale α c) b Z).2)
    ((restrictTorus μ (Real.sqrt (simScale α c) * b) Z).2) (cutLp 6 b (Freq.velocity (Freq.fracDilX α c Y)))
    (cutLp 6 (Real.sqrt (simScale α c) * b) (Freq.velocity Y)) _ _ _ _ hA1 (restrictTorus_snd_ae hS Z) hB1
    (cutLp_apply 6 (Real.sqrt (simScale α c) * b) (Freq.velocity Y)) hf hg
  rw [norm_of_ae_comp_smul (p := 6) hs _ _ key, sqrt_cube_rpow hc', Real.norm_eq_abs, abs_of_pos hk]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  exact velNormFactor hc

end TorusCompareFrame.Internal

open TorusCompareFrame.Internal in
theorem fracFrameChange (α : ℝ) (hα : 1 < α) (hV : Freq.FracVelocityDilate α)
    (hD : Freq.FracDilationAlgebra α) : FracFrameChange α := by
  intro μ c b hc hc1 hS Z Y
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [gradPart hα hD hc hc1 hS Z Y j]
    gcongr
    exact (norm_le_pi_norm _ j).trans (norm_fst_le _)
  · rw [velocityPart hα hV hc hc1 hS Z Y]
    gcongr
    exact norm_snd_le _

end Breakdown.Periodic
