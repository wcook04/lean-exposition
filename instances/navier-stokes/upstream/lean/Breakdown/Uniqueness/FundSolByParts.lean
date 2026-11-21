import Breakdown.Uniqueness.FundSolPotential
import Breakdown.Uniqueness.FundSolPointwise
import Breakdown.Uniqueness.FundSolByPartsRadial

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol

private theorem contDiff_secondPartial {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (i j : Fin 3) :
    ContDiff ℝ ∞ (secondPartial g i j) := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ 2 g) := hg.iteratedFDeriv_right (le_of_eq rfl)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ
    ![unitVector i, unitVector j]).contDiff.comp h

private theorem hasCompactSupport_secondPartial {g : Space → ℝ} (hc : HasCompactSupport g)
    (i j : Fin 3) : HasCompactSupport (secondPartial g i j) :=
  (hc.iteratedFDeriv (𝕜 := ℝ) 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) ℝ => L ![unitVector i, unitVector j])
    (by simp)

private theorem scalarSumSecondPartials_potential_eq_potential {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (x : Space) :
    scalarSumSecondPartials (potential g) x = potential (scalarSumSecondPartials g) x := by
  have hfun : scalarSumSecondPartials g = secondPartial g 0 0 + secondPartial g 1 1 + secondPartial g 2 2 := by
    funext y
    simp [scalarSumSecondPartials, Fin.sum_univ_three]
  rw [hfun, potential_add (g := secondPartial g 0 0 + secondPartial g 1 1) (h := secondPartial g 2 2)
    (((contDiff_secondPartial hg 0 0).add (contDiff_secondPartial hg 1 1)))
    ((hasCompactSupport_secondPartial hc 0 0).add (hasCompactSupport_secondPartial hc 1 1))
    (contDiff_secondPartial hg 2 2) (hasCompactSupport_secondPartial hc 2 2),
    potential_add (contDiff_secondPartial hg 0 0) (hasCompactSupport_secondPartial hc 0 0)
    (contDiff_secondPartial hg 1 1) (hasCompactSupport_secondPartial hc 1 1)]
  simp [scalarSumSecondPartials, Fin.sum_univ_three, secondPartial_potential hg hc]

private theorem scalarSumSecondPartials_potential_of_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {x : Space} (h0 : f x = 0) : scalarSumSecondPartials (potential f) x = 0 := by
  simp only [scalarSumSecondPartials, secondPartial_potential_eq_integral hf hc h0]
  rw [← integral_finsetSum _ (fun i _ => integrable_kernelSecondDeriv_mul hf hc h0 i i)]
  have h : ∀ y, ∑ i, kernelSecondDeriv i i (x - y) * f y = 0 := by
    intro y
    by_cases hy : y = x
    · simp [hy, h0]
    · rw [← Finset.sum_mul, sum_kernelSecondDeriv_diag (sub_ne_zero.2 (Ne.symm hy)), zero_mul]
  simp [h]

private theorem scalarSumSecondPartials_add_smul {u v : Space → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (c : ℝ) (x : Space) :
    scalarSumSecondPartials (u + c • v) x = scalarSumSecondPartials u x + c * scalarSumSecondPartials v x := by
  simp only [scalarSumSecondPartials, secondPartial]
  rw [iteratedFDeriv_add_apply (f := u) (g := c • v) (hu.contDiffAt.of_le (by norm_cast))
    ((hv.const_smul c).contDiffAt.of_le (by norm_cast)),
    iteratedFDeriv_const_smul_apply (hv.contDiffAt.of_le (by norm_cast))]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

private theorem potential_scalarSumSecondPartials_centeredBump (x : Space) :
    potential (scalarSumSecondPartials (centeredBump x)) x = 1 := by
  rw [potential, convolution_def]
  have h : ∀ t, (ContinuousLinearMap.lsmul ℝ ℝ) (scalarSumSecondPartials (centeredBump x) t) (kernel (x - t)) =
      (fun s : Space => bumpSumSecondPartialsProfile (‖s‖ ^ 2) * kernel s) (t - x) := by
    intro t
    simp [scalarSumSecondPartials_centeredBump, kernel, norm_sub_rev x t]
  simp_rw [h]
  rw [integral_sub_right_eq_self (fun s : Space => bumpSumSecondPartialsProfile (‖s‖ ^ 2) * kernel s) x]
  exact integral_bumpSumSecondPartialsProfile_mul_kernel

private theorem scalarSumSecondPartials_potential_eq_self {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (x : Space) : scalarSumSecondPartials (potential g) x = g x := by
  have hψ := contDiff_centeredBump x
  have hψc := hasCompactSupport_centeredBump x
  have hψs : ContDiff ℝ ∞ (g x • centeredBump x) := hψ.const_smul (g x)
  have hf : ContDiff ℝ ∞ (g - g x • centeredBump x) := hg.sub hψs
  have hψc' : HasCompactSupport (g x • centeredBump x) := hψc.smul_left (f := fun _ => g x)
  have hfc : HasCompactSupport (g - g x • centeredBump x) := hc.sub hψc'
  have hfx : (g - g x • centeredBump x) x = 0 := by simp [centeredBump_self]
  have hsplit : potential g = potential (g - g x • centeredBump x) + g x • potential (centeredBump x) := by
    conv_lhs => rw [show g = (g - g x • centeredBump x) + g x • centeredBump x by simp]
    rw [potential_add hf hfc hψs hψc', potential_smul]
  rw [hsplit, scalarSumSecondPartials_add_smul (contDiff_potential hf hfc) (contDiff_potential hψ hψc),
    scalarSumSecondPartials_potential_of_eq_zero hf hfc hfx,
    scalarSumSecondPartials_potential_eq_potential hψ hψc, potential_scalarSumSecondPartials_centeredBump]
  ring

theorem potential_scalarSumSecondPartials {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (x : Space) : potential (scalarSumSecondPartials f) x = f x := by
  rw [← scalarSumSecondPartials_potential_eq_potential hf hc x, scalarSumSecondPartials_potential_eq_self hf hc x]

theorem scalarSumSecondPartials_potential {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (x : Space) : scalarSumSecondPartials (potential g) x = g x :=
  scalarSumSecondPartials_potential_eq_self hg hc x

end Breakdown.FundSol
