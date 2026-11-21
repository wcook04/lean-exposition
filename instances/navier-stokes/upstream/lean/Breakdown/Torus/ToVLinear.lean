import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.Basic

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ToVLinear.Internal

theorem complexify_add (a b : Space) : complexify (a + b) = complexify a + complexify b := by
  ext i
  simp [complexify]

theorem complexify_smul (c : ℝ) (a : Space) : complexify (c • a) = c • complexify a := by
  ext i
  simp [complexify, Complex.real_smul]

theorem freqTrCoef_add {f g : Space → Space} (hf : Continuous f) (hg : Continuous g) (k : Lattice) :
    freqTrCoef (f + g) k = freqTrCoef f k + freqTrCoef g k := by
  unfold freqTrCoef
  rw [← integral_add (FreqTrSeries.Internal.integrableOn_coef hf k)
    (FreqTrSeries.Internal.integrableOn_coef hg k)]
  congr 1
  funext x
  rw [Pi.add_apply, complexify_add, smul_add]

theorem freqTrCoef_smul (c : ℝ) (f : Space → Space) (k : Lattice) :
    freqTrCoef (c • f) k = c • freqTrCoef f k := by
  unfold freqTrCoef
  rw [← integral_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, complexify_smul, smul_comm]

theorem coeff_add (u v : V) (k : Lattice) : coeff (u + v) k = coeff u k + coeff v k := by
  simp [coeff, smul_add]

theorem coeff_smul (c : ℝ) (u : V) (k : Lattice) : coeff (c • u) k = c • coeff u k := by
  rw [coeff, coeff, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_comm]

theorem isPeriodic_add {f g : Space → Space} (hf : IsPeriodic f) (hg : IsPeriodic g) :
    IsPeriodic (f + g) := by
  intro i x
  simp only [Pi.add_apply, hf i x, hg i x]

theorem isPeriodic_smul (c : ℝ) {f : Space → Space} (hf : IsPeriodic f) : IsPeriodic (c • f) := by
  intro i x
  simp only [Pi.smul_apply, hf i x]

theorem divergenceAt_add {f g : Space → Space} {x : Space} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : divergenceAt (f + g) x = divergenceAt f x + divergenceAt g x := by
  simp only [divergenceAt, fderiv_add hf hg, add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

theorem divergenceAt_smul (c : ℝ) (f : Space → Space) (x : Space) :
    divergenceAt (c • f) x = c * divergenceAt f x := by
  simp [divergenceAt, fderiv_const_smul_field, Finset.mul_sum]

end ToVLinear.Internal

open ToVLinear.Internal

theorem toV_smul (c : ℝ) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (hdiv : ∀ x, divergenceAt f x = 0) : toV (c • f) = c • toV f := by
  have hdc : ∀ x, divergenceAt (c • f) x = 0 := fun x => by rw [divergenceAt_smul, hdiv x, mul_zero]
  apply coeff_injective
  intro k
  rw [(freqTrSeriesSpec coefDeriv (c • f) (hf.const_smul c) (isPeriodic_smul c hp) hdc).1 k, coeff_smul,
    (freqTrSeriesSpec coefDeriv _ hf hp hdiv).1 k, freqTrCoef_smul]

theorem toVAdd : ToVAdd := by
  intro f g hf hg hpf hpg hdf hdg
  have hd : ∀ x, divergenceAt (f + g) x = 0 := fun x => by
    rw [divergenceAt_add ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x), hdf x,
      hdg x, add_zero]
  apply coeff_injective
  intro k
  rw [(freqTrSeriesSpec coefDeriv (f + g) (hf.add hg) (isPeriodic_add hpf hpg) hd).1 k, coeff_add,
    (freqTrSeriesSpec coefDeriv _ hf hpf hdf).1 k, (freqTrSeriesSpec coefDeriv _ hg hpg hdg).1 k,
    freqTrCoef_add hf.continuous hg.continuous]

end Breakdown.Periodic
