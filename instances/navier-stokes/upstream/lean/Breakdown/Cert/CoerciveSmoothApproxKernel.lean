import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

def timeBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / ((n : ℝ) + 1), 2 / ((n : ℝ) + 1), by positivity,
    div_lt_div_of_pos_right (by norm_num) (by positivity)⟩

def spaceBump (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / ((n : ℝ) + 1), 2 / ((n : ℝ) + 1), by positivity,
    div_lt_div_of_pos_right (by norm_num) (by positivity)⟩

def kernel (n : ℕ) (z : ℝ × Space) : ℝ :=
  (timeBump n).normed volume z.1 * (spaceBump n).normed volume z.2

def joint {β : Type*} (v : ℝ → Space → β) (z : ℝ × Space) : β := v z.1 z.2

def mollify (n : ℕ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v) (σ, y)

theorem kernel_contDiff (n : ℕ) : ContDiff ℝ ∞ (kernel n) :=
  (((timeBump n).contDiff_normed (μ := volume) (n := ⊤)).comp contDiff_fst).mul
    (((spaceBump n).contDiff_normed (μ := volume) (n := ⊤)).comp contDiff_snd)

theorem kernel_hasCompactSupport (n : ℕ) : HasCompactSupport (kernel n) := by
  refine HasCompactSupport.intro
    (((timeBump n).hasCompactSupport_normed (μ := volume)).isCompact.prod
      ((spaceBump n).hasCompactSupport_normed (μ := volume)).isCompact) ?_
  intro z hz
  rw [Set.mem_prod, not_and_or] at hz
  rcases hz with h | h
  · simp [kernel, image_eq_zero_of_notMem_tsupport h]
  · simp [kernel, image_eq_zero_of_notMem_tsupport h]

theorem kernel_nonneg (n : ℕ) (z : ℝ × Space) : 0 ≤ kernel n z :=
  mul_nonneg ((timeBump n).nonneg_normed _) ((spaceBump n).nonneg_normed _)

theorem volume_prod_invariantClass : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem mollify_smooth (n : ℕ) {v : ℝ → Space → Space} (hv : LocallyIntegrable (joint v) volume) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => mollify n v z.1 z.2) := by
  have := volume_prod_invariantClass
  exact (kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hv

theorem mollify_periodic (n : ℕ) {v : ℝ → Space → Space} (hp : IsTimePeriodic v) :
    IsTimePeriodic (mollify n v) := by
  intro σ y
  simp only [mollify, convolution_def]
  congr 1
  funext t
  simp only [joint, Prod.fst_sub, Prod.snd_sub]
  rw [show σ + 1 - t.1 = (σ - t.1) + 1 by ring, hp]

end Internal.SmoothApprox

end Coercive

end Breakdown
