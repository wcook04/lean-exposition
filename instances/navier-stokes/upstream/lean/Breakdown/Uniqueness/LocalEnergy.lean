import Breakdown.Uniqueness.LocalEnergyAuxIbp
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

open Internal.CutoffEnergy

theorem continuousOn_cutoffEnergy {T : ℝ} {u v : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (hu : IsSolutionOn T u p) (hv : IsSolutionOn T v q) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun τ => cutoffEnergy r (v τ - u τ)) (Icc 0 T) :=
  continuousOn_cutoffEnergy_sub hu hv hr

theorem hasDerivAt_cutoffEnergy {T : ℝ} {u v : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (hu : IsSolutionOn T u p) (hv : IsSolutionOn T v q) {r : ℝ} (hr : 0 < r) {t : ℝ}
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun τ => cutoffEnergy r (v τ - u τ))
      (-cutoffDissipation r (v t - u t)
        + (1 / 2) * (∫ x, ‖v t x - u t x‖ ^ 2 * FundSol.scalarSumSecondPartials (cutoffPow r) x)
        + (1 / 2) * (∫ x, ‖v t x - u t x‖ ^ 2 * inner ℝ (v t x) (gradientAt (cutoffPow r) x))
        - (∫ x, cutoffPow r x * inner ℝ (v t x - u t x) (fderiv ℝ (u t) x (v t x - u t x)))
        - (∫ x, inner ℝ (gradientAt (q t) x - gradientAt (p t) x)
            (cutoffPow r x • (v t x - u t x)))) t := by
  have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
    | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.2 le_top
  have key := hasDerivAt_cutoffEnergy_inner hu hv hr ht
  convert key using 1
  have hVs : ContDiff ℝ ∞ (v t) := contDiff_slice hv.smooth_velocity (Ioo_subset_Icc_self ht)
  have hUs : ContDiff ℝ ∞ (u t) := contDiff_slice hu.smooth_velocity (Ioo_subset_Icc_self ht)
  have hQs : ContDiff ℝ ∞ (q t) := contDiff_slice hv.smooth_pressure (Ioo_subset_Icc_self ht)
  have hPs : ContDiff ℝ ∞ (p t) := contDiff_slice hu.smooth_pressure (Ioo_subset_Icc_self ht)
  have hWs : ContDiff ℝ ∞ (v t - u t) := hVs.sub hUs
  have hφ := contDiff_cutoffPow hr
  have hφc := hasCompactSupport_cutoffPow hr
  have hpt : ∀ x, cutoffPow r x * inner ℝ (v t x - u t x)
      (deriv (fun τ => v τ x) t - deriv (fun τ => u τ x) t) =
      cutoffPow r x * inner ℝ (v t x - u t x) (sumSecondPartialsAt (v t - u t) x)
      - cutoffPow r x * inner ℝ (v t x - u t x) (gradientAt (q t) x - gradientAt (p t) x)
      - cutoffPow r x * inner ℝ (v t x - u t x) (fderiv ℝ (v t - u t) x (v t x))
      - cutoffPow r x * inner ℝ (v t x - u t x) (fderiv ℝ (u t) x (v t x - u t x)) := by
    intro x
    have e1 := hv.momentum t ht x
    have e2 := hu.momentum t ht x
    have hl : sumSecondPartialsAt (v t - u t) x = sumSecondPartialsAt (v t) x - sumSecondPartialsAt (u t) x := by
      simp only [sumSecondPartialsAt, ← Finset.sum_sub_distrib]
      congr 1
      funext i
      rw [iteratedFDeriv_sub_apply (hVs.contDiffAt.of_le h2le) (hUs.contDiffAt.of_le h2le)]
      rfl
    have hf : fderiv ℝ (v t - u t) x = fderiv ℝ (v t) x - fderiv ℝ (u t) x :=
      fderiv_sub (hVs.differentiable (by simp) x) (hUs.differentiable (by simp) x)
    simp only [advectionAt] at e1 e2
    rw [hl, hf, eq_sub_of_add_eq e1, eq_sub_of_add_eq e2, ContinuousLinearMap.sub_apply, map_sub]
    simp only [inner_sub_right]
    ring
  have hcW : Continuous (fun x => v t x - u t x) := hVs.continuous.sub hUs.continuous
  have hcL : Continuous (sumSecondPartialsAt (v t - u t)) := by
    unfold sumSecondPartialsAt
    exact continuous_finsetSum _ fun i _ =>
      (hWs.continuous_iteratedFDeriv h2le).eval_const _
  have hcG : ∀ f : Space → ℝ, ContDiff ℝ ∞ f → Continuous (gradientAt f) := by
    intro f hf
    unfold gradientAt
    exact continuous_finsetSum _ fun i _ =>
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
  have hcDW : Continuous (fun x => fderiv ℝ (v t - u t) x (v t x)) :=
    (hWs.continuous_fderiv (by simp)).clm_apply hVs.continuous
  have hcDU : Continuous (fun x => fderiv ℝ (u t) x (v t x - u t x)) :=
    (hUs.continuous_fderiv (by simp)).clm_apply hcW
  have iA := integrable_cutoffPow_mul hr (hcW.inner hcL)
  have iB : Integrable (fun x => cutoffPow r x * inner ℝ (v t x - u t x)
      (gradientAt (q t) x - gradientAt (p t) x)) := integrable_cutoffPow_mul hr (hcW.inner ((hcG _ hQs).sub (hcG _ hPs)))
  have iC := integrable_cutoffPow_mul hr (hcW.inner hcDW)
  have iD := integrable_cutoffPow_mul hr (hcW.inner hcDU)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub, integral_sub, integral_sub]
  all_goals first | exact iA | exact iB | exact iC | exact iD | exact iA.sub iB | exact (iA.sub iB).sub iC | skip
  have hA := integral_mul_inner_sumSecondPartialsAt hφ hφc hWs
  have hC := integral_mul_inner_fderiv_transport hφ hφc hVs
    (hv.incompressible t (Ioo_subset_Icc_self ht)) hWs
  simp only [Pi.sub_apply] at hA hC
  have hB : (∫ x, inner ℝ (gradientAt (q t) x - gradientAt (p t) x)
      (cutoffPow r x • (v t x - u t x))) =
      ∫ x, cutoffPow r x * inner ℝ (v t x - u t x) (gradientAt (q t) x - gradientAt (p t) x) := by
    congr 1
    funext x
    rw [inner_smul_right, real_inner_comm]
  rw [hA, hC, hB]
  unfold cutoffDissipation
  ring

end Breakdown
