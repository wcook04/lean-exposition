import Breakdown.Cert.CoerciveFrequencySeminormWeightSmooth
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

open Filter Topology

theorem integrable_of_vanish_field {φ : Space → Space} (hc : HasCompactSupport φ) {F : Space → ℝ}
    (hF : Continuous F) (h : ∀ y, y ∉ tsupport φ → F y = 0) : Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hc h)

theorem weighted_sq_le_grad_test {φ : Space → Space} (hφ : IsTestField φ) :
    ∫⁻ y, ENNReal.ofReal (‖φ y‖ ^ 2 * radialDamp y) ≤
      ENNReal.ofReal (4 * ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) := by
  have hc := hφ.2.1
  have hcont : Continuous φ := hφ.1.continuous
  have hcomp : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => φ y i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hφ.1
  have hz : ∀ y, y ∉ tsupport φ → φ y = 0 ∧ fderiv ℝ φ y = 0 := fun y hy =>
    ⟨image_eq_zero_of_notMem_tsupport hy, fderiv_of_notMem_tsupport ℝ hy⟩
  have hsupp : ∀ i : Fin 3, HasCompactSupport (fun y => φ y i) := fun i =>
    HasCompactSupport.intro hc fun y hy => by simp [(hz y hy).1]
  have hder : ∀ i j : Fin 3, ∀ y, fderiv ℝ (fun y => φ y i) y (unitVector j) =
      fderiv ℝ φ y (unitVector j) i := by
    intro i j y
    have hd : DifferentiableAt ℝ φ y := hφ.1.differentiable (by simp) y
    have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt
    rw [show (fun y => φ y i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ φ from rfl, h.fderiv]
    rfl
  have hH : ∀ i : Fin 3, ∫ y, φ y i ^ 2 * radialDamp y ≤
      4 * ∫ y, ∑ j : Fin 3, fderiv ℝ φ y (unitVector j) i ^ 2 := by
    intro i
    have := weighted_sq_le_grad_smooth (hcomp i) (hsupp i)
    simp only [hder] at this
    exact this
  have hcd : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ φ y (unitVector j)) := fun j =>
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcw : Continuous radialDamp := contDiff_radialDamp.continuous
  have hi1 : Integrable (fun y => ‖φ y‖ ^ 2 * radialDamp y) :=
    integrable_of_vanish_field hc ((hcont.norm.pow 2).mul hcw) fun y hy => by simp [(hz y hy).1]
  have hi2 : ∀ i : Fin 3, Integrable (fun y => φ y i ^ 2 * radialDamp y) := fun i =>
    integrable_of_vanish_field hc ((((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hcont).pow 2).mul hcw)
      fun y hy => by simp [(hz y hy).1]
  have hi3 : ∀ i : Fin 3, Integrable (fun y => ∑ j : Fin 3, fderiv ℝ φ y (unitVector j) i ^ 2) := fun i =>
    integrable_of_vanish_field hc (continuous_finsetSum _ fun j _ =>
      (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (hcd j)).pow 2))
      fun y hy => by simp [(hz y hy).2]
  have e1 : ∫ y, ‖φ y‖ ^ 2 * radialDamp y = ∑ i : Fin 3, ∫ y, φ y i ^ 2 * radialDamp y := by
    rw [← integral_finsetSum _ fun i _ => hi2 i]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [norm_sq_eq_sum, Finset.sum_mul]
  have e2 : ∑ i : Fin 3, ∫ y, ∑ j : Fin 3, fderiv ℝ φ y (unitVector j) i ^ 2 =
      ∫ y, ∑ j : Fin 3, ‖fderiv ℝ φ y (unitVector j)‖ ^ 2 := by
    rw [← integral_finsetSum _ fun i _ => hi3 i]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_sum _).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hi1 (Eventually.of_forall fun y =>
    mul_nonneg (sq_nonneg _) (by unfold radialDamp; positivity))]
  apply ENNReal.ofReal_le_ofReal
  rw [e1, ← e2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hH i

theorem weighted_sq_le_velocity_norm (x : Freq.X) :
    ∫⁻ y, ENNReal.ofReal (‖(Freq.velocity x : Space → Space) y‖ ^ 2 * radialDamp y) ≤
      ENNReal.ofReal (4 * ‖x‖ ^ 2) := by
  obtain ⟨a, ha, hax⟩ := mem_closure_iff_seq_limit.1 (Freq.testDense_holds.2 x)
  choose φ hφ hφa using fun n => Freq.testSpan_holds (a n) (ha n)
  have hV : Tendsto (fun n => Freq.velocity (a n)) atTop (𝓝 (Freq.velocity x)) :=
    (Freq.velocity.continuous.tendsto x).comp hax
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hV).exists_seq_tendsto_ae
  have hcw : Continuous radialDamp := contDiff_radialDamp.continuous
  have hmeas : ∀ n, AEMeasurable (fun y => ENNReal.ofReal
      (‖(Freq.velocity (a (ns n)) : Space → Space) y‖ ^ 2 * radialDamp y)) := fun n =>
    (((Lp.aestronglyMeasurable _).norm.pow 2).mul hcw.aestronglyMeasurable).aemeasurable.ennreal_ofReal
  calc _ = ∫⁻ y, liminf (fun n => ENNReal.ofReal
          (‖(Freq.velocity (a (ns n)) : Space → Space) y‖ ^ 2 * radialDamp y)) atTop := by
        refine lintegral_congr_ae (hns.mono fun y hy => ?_)
        have ht : Tendsto (fun n => ENNReal.ofReal
            (‖(Freq.velocity (a (ns n)) : Space → Space) y‖ ^ 2 * radialDamp y)) atTop
            (𝓝 (ENNReal.ofReal (‖(Freq.velocity x : Space → Space) y‖ ^ 2 * radialDamp y))) :=
          ENNReal.tendsto_ofReal ((hy.norm.pow 2).mul_const _)
        exact ht.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal
          (‖(Freq.velocity (a (ns n)) : Space → Space) y‖ ^ 2 * radialDamp y)) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ liminf (fun n => ENNReal.ofReal (4 * ‖a (ns n)‖ ^ 2)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        have he := Freq.velocityDecay_holds _ (Freq.isDecayField_of_isTestField (hφ (ns n)))
        rw [← hφa (ns n)]
        calc _ = ∫⁻ y, ENNReal.ofReal (‖φ (ns n) y‖ ^ 2 * radialDamp y) :=
              lintegral_congr_ae (he.mono fun y hy => by simp only [hy])
          _ ≤ _ := weighted_sq_le_grad_test (hφ (ns n))
          _ = _ := by
              rw [Freq.embedNormLinear_holds.1 _ (Freq.isDecayField_of_isTestField (hφ (ns n)))]
    _ = ENNReal.ofReal (4 * ‖x‖ ^ 2) := by
        have ht : Tendsto (fun n => ENNReal.ofReal (4 * ‖a (ns n)‖ ^ 2)) atTop
            (𝓝 (ENNReal.ofReal (4 * ‖x‖ ^ 2))) :=
          ENNReal.tendsto_ofReal ((((hax.comp hmono.tendsto_atTop).norm).pow 2).const_mul 4)
        exact ht.liminf_eq

theorem slice_weighted_sq_le {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f F) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (F y (unitVector i)) i = 0)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / (1 + ‖y‖ ^ 2)) ≤ 4 * ∫⁻ y, ENNReal.ofReal (matSq (F y)) := by
  obtain ⟨x, hx1, hx2⟩ := Breakdown.Coercive.Internal.PerturbationFacts.slice_embed hg hdiv h6 h2
  calc _ = ∫⁻ y, ENNReal.ofReal (‖(Freq.velocity x : Space → Space) y‖ ^ 2 * radialDamp y) :=
        lintegral_congr_ae (hx1.mono fun y hy => by dsimp only; rw [hy, radialDamp, div_eq_mul_inv])
    _ ≤ ENNReal.ofReal (4 * ‖x‖ ^ 2) := weighted_sq_le_velocity_norm x
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), hx2, ENNReal.ofReal_ofNat]

end Internal

end FrequencySeminorm

end Coercive

end Breakdown
