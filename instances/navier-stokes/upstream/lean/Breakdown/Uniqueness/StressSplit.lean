import Breakdown.Uniqueness.CutoffBounds
import Breakdown.Uniqueness.FundSolEnergy
import Breakdown.Uniqueness.FundSolPointwise

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem sum_apply_unitVector_mul (L : Space →L[ℝ] ℝ) (v : Space) :
    ∑ i : Fin 3, L (unitVector i) * v i = L v := by
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, unitVector, mul_comm]

private theorem fderiv_cutoffPow {r : ℝ} (hr : 0 < r) (x : Space) :
    fderiv ℝ (cutoffPow r) x = (4 * radialCutoff r x ^ 3) • fderiv ℝ (radialCutoff r) x := by
  have hd : DifferentiableAt ℝ (radialCutoff r) x :=
    (contDiff_radialCutoff hr).differentiable (by simp) x
  have h := (hd.hasFDerivAt.pow 4).fderiv
  have he : cutoffPow r = fun y => radialCutoff r y ^ 4 := rfl
  rw [he, h]
  norm_num

theorem cutoffSource_eq {r : ℝ} (hr : 0 < r) {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x, divergenceAt w x = 0) (x : Space) :
    cutoffSource r w x = 4 * radialCutoff r x ^ 3 * cutoffFlux r w x := by
  have hdp : DifferentiableAt ℝ (cutoffPow r) x :=
    ((contDiff_radialCutoff hr).pow 4).differentiable (by simp) x
  have hdw : DifferentiableAt ℝ w x := hw.differentiable (by simp) x
  have hsm : (fun y => cutoffPow r y • w y) = cutoffPow r • w := rfl
  have hdx := hdiv x
  unfold divergenceAt at hdx
  unfold cutoffSource divergenceAt
  rw [hsm, fderiv_smul hdp hdw]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, hdx, mul_zero, zero_add]
  rw [sum_apply_unitVector_mul, fderiv_cutoffPow hr, cutoffFlux]
  simp [mul_assoc]

theorem contDiff_cutoffFlux {r : ℝ} (hr : 0 < r) {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (cutoffFlux r w) :=
  ((contDiff_radialCutoff hr).fderiv_right (m := ∞) le_rfl).clm_apply hw

theorem hasCompactSupport_cutoffFlux {r : ℝ} (hr : 0 < r) (w : Space → Space) :
    HasCompactSupport (cutoffFlux r w) :=
  ((hasCompactSupport_radialCutoff hr).fderiv (𝕜 := ℝ)).mono'
    (fun x hx => subset_tsupport _ (fun h => hx (by simp [cutoffFlux, h])))

private theorem secondPartial_add_smul {P Q : Space → ℝ} (hP : ContDiff ℝ ∞ P)
    (hQ : ContDiff ℝ ∞ Q) (c : ℝ) (i j : Fin 3) (x : Space) :
    FundSol.secondPartial (P + c • Q) i j x =
      FundSol.secondPartial P i j x + c * FundSol.secondPartial Q i j x := by
  have hP2 : ContDiffAt ℝ 2 P x := hP.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hQ2 : ContDiffAt ℝ 2 Q x := hQ.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hcQ2 : ContDiffAt ℝ 2 (c • Q) x := hQ2.const_smul c
  unfold FundSol.secondPartial
  rw [iteratedFDeriv_add_apply (f := P) (g := c • Q) hP2 hcQ2,
    iteratedFDeriv_const_smul_apply (f := Q) hQ2]
  simp

private theorem potential_split_generic {S γ h : Space → ℝ} (a : ℝ) (hγ : ContDiff ℝ ∞ γ)
    (hγc : HasCompactSupport γ) (hh : ContDiff ℝ ∞ h) {x : Space} (hx : h x = 0)
    (hS : S = fun y => 4 * a * γ y + 4 * (h y * γ y)) (i j : Fin 3) :
    FundSol.secondPartial (FundSol.potential S) i j x =
      4 * a * FundSol.secondPartial (FundSol.potential γ) i j x +
        4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) * (h y * γ y) := by
  have hg : ContDiff ℝ ∞ (fun y => 4 * (h y * γ y)) := contDiff_const.mul (hh.mul hγ)
  have hgc : HasCompactSupport (fun y => 4 * (h y * γ y)) :=
    (hγc.mul_left (f := h)).mul_left (f := fun _ => (4 : ℝ))
  have hg0 : (fun y => 4 * (h y * γ y)) x = 0 := by simp [hx]
  have hsc : HasCompactSupport ((4 * a) • γ) := by
    have e : (4 * a) • γ = fun y => 4 * a * γ y := by funext y; simp
    rw [e]
    exact hγc.mul_left
  have hsplit : S = (fun y => 4 * (h y * γ y)) + (4 * a) • γ := by
    rw [hS]
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcs : ContDiff ℝ ∞ ((4 * a) • γ) := hγ.const_smul (4 * a)
  rw [hsplit, FundSol.potential_add (h := (4 * a) • γ) hg hgc hcs hsc, FundSol.potential_smul,
    secondPartial_add_smul (FundSol.contDiff_potential hg hgc) (FundSol.contDiff_potential hγ hγc),
    FundSol.secondPartial_potential_eq_integral hg hgc hg0]
  have hI : ∫ y, FundSol.kernelSecondDeriv i j (x - y) * (4 * (h y * γ y)) =
      4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) * (h y * γ y) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [hI]
  ring

theorem secondPartial_source_split {r : ℝ} (hr : 0 < r) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hdiv : ∀ x, divergenceAt w x = 0) (i j : Fin 3) (x : Space) :
    FundSol.secondPartial (FundSol.potential (cutoffSource r w)) i j x =
      4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x +
        4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) *
          ((radialCutoff r y ^ 3 - radialCutoff r x ^ 3) * cutoffFlux r w y) := by
  refine potential_split_generic (radialCutoff r x ^ 3) (contDiff_cutoffFlux hr hw)
    (hasCompactSupport_cutoffFlux hr w)
    (((contDiff_radialCutoff hr).pow 3).sub contDiff_const) (sub_self _) ?_ i j
  funext y
  rw [cutoffSource_eq hr hw hdiv y]
  ring

end Breakdown
