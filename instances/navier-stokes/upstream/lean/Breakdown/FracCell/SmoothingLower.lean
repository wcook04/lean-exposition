import Breakdown.FracCell.StClauses
import Breakdown.FracCert.SecondSymbol

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

namespace Internal.SmoothingLower

open Freq SteadyCert.Internal.SecondSymbol

theorem scalar_bound {lam x s t : ℝ} (hl : 0 < lam) (hx : 0 ≤ x) :
    ratioFn lam x * (s + t) ^ 2 ≤ s ^ 2 + x * t ^ 2 / lam := by
  unfold ratioFn
  have hlx : 0 < lam + x := by linarith
  have key : s ^ 2 + x * t ^ 2 / lam - x / (lam + x) * (s + t) ^ 2 =
      (lam * s - x * t) ^ 2 / (lam * (lam + x)) := by
    field_simp
    ring
  have : 0 ≤ (lam * s - x * t) ^ 2 / (lam * (lam + x)) := by positivity
  linarith

theorem vec_bound {lam x : ℝ} (hl : 0 < lam) (hx : 0 ≤ x) (a b : CSpace) :
    ratioFn lam x * ‖a‖ ^ 2 ≤ ‖a - b‖ ^ 2 + x * ‖b‖ ^ 2 / lam := by
  have h1 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    have := norm_sub_norm_le a b
    linarith
  have hr : 0 ≤ ratioFn lam x := div_nonneg hx (by linarith)
  calc ratioFn lam x * ‖a‖ ^ 2 ≤ ratioFn lam x * (‖a - b‖ + ‖b‖) ^ 2 := by gcongr
    _ ≤ _ := scalar_bound hl hx

theorem sq_integrable {f : Space → CSpace} (hf : MemLp f 2 volume) :
    Integrable (fun ξ => ‖f ξ‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm hf.1).1 hf

theorem sq_integrable_real {f : Space → Space} (hf : MemLp f 2 volume) :
    Integrable (fun y => ‖f y‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm hf.1).1 hf

theorem hat_grad {ψ : Space → Space} {Dψ : Space → (Space →L[ℝ] Space)} (hψ : MemLp ψ 2 volume)
    (hD : AEStronglyMeasurable Dψ volume) (hE : Integrable (fun y => entrySq (Dψ y)))
    (hw : IsWeakGradientOf ψ Dψ) (j : Fin 3) :
    (hatOf (fun y => Dψ y (unitVector j)) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * ((ξ j : ℝ) : ℂ)) • (hatOf ψ : Space → CSpace) ξ := by
  set G : Space → (Space →L[ℝ] Space) :=
    fun y => (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (ψ y) with hG
  have hGi : ∀ i, WeakProfile.gradComponent G i = fun y => (unitVector i : Space) 0 • ψ y := by
    intro i
    funext y
    simp [WeakProfile.gradComponent, G, ContinuousLinearMap.smulRight_apply]
  have hm : ∀ i, MemLp (WeakProfile.gradComponent G i) 2 volume := by
    intro i
    rw [hGi i]
    exact hψ.const_smul ((unitVector i : Space) 0)
  have h0 : WeakProfile.gradComponent G 0 = ψ := by
    rw [hGi 0]
    funext y
    simp [unitVector]
  have hw' : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector 0) = -∫ y, φ y • Dψ y (unitVector j) := by
    intro φ hφ
    have e : ∀ y, G y (unitVector 0) = ψ y := fun y => congrFun h0 y
    simp only [e]
    exact hw φ hφ j
  have h := hat_deriv (G := G) (f' := fun y => Dψ y (unitVector j)) hm (memLp_comp hD hE j) hw'
  have hc : WeakProfile.Internal.GradientFreqTr.hatComp G 0 = hatOf ψ := by
    show freqTrR (complexify (toLpOrZero 2 (WeakProfile.gradComponent G 0))) =
      freqTrR (complexify (toLpOrZero 2 ψ))
    rw [h0]
  rw [hc] at h
  exact h

theorem freq_energy {ψ : Space → Space} {Dψ : Space → (Space →L[ℝ] Space)} (hψ : MemLp ψ 2 volume)
    (hD : AEStronglyMeasurable Dψ volume) (hE : Integrable (fun y => entrySq (Dψ y)))
    (hw : IsWeakGradientOf ψ Dψ) :
    (fun ξ => freqPow 2 ξ * ‖(hatOf ψ : Space → CSpace) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => ∑ j : Fin 3, ‖(hatOf (fun y => Dψ y (unitVector j)) : Space → CSpace) ξ‖ ^ 2 := by
  filter_upwards [ae_all_iff.2 fun j => hat_grad hψ hD hE hw j] with ξ h
  simp only [h, norm_coef_smul, freqPow_two, Freq.Internal.PartialDecay.norm_sq_space,
    Finset.mul_sum, Finset.sum_mul]

theorem hat_sub {φ ψ : Space → Space} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    (hatOf (fun y => φ y - ψ y) : Space → CSpace) =ᵐ[volume]
      fun ξ => (hatOf φ : Space → CSpace) ξ - (hatOf ψ : Space → CSpace) ξ := by
  have hs : MemLp (fun y => φ y - ψ y) 2 volume := hφ.sub hψ
  have hL : toLpOrZero 2 (fun y => φ y - ψ y) = toLpOrZero 2 φ - toLpOrZero 2 ψ := by
    apply Lp.ext
    filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hs,
      Lp.coeFn_sub (toLpOrZero 2 φ) (toLpOrZero 2 ψ),
      Freq.Internal.H1Consistency.toLpOrZero_ae hφ,
      Freq.Internal.H1Consistency.toLpOrZero_ae hψ] with y h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4]
  have hH : hatOf (fun y => φ y - ψ y) = hatOf φ - hatOf ψ := by
    simp only [hatOf, hL, map_sub]
  rw [hH]
  exact Lp.coeFn_sub _ _

theorem freqPow_two_nonneg (ξ : Space) : 0 ≤ freqPow 2 ξ := by
  rw [freqPow_two]
  positivity

theorem bound_one {lam : ℝ} (hl : 0 < lam) {φ ψ : Space → Space} {Dψ : Space → (Space →L[ℝ] Space)}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (hD : AEStronglyMeasurable Dψ volume) (hE : Integrable (fun y => entrySq (Dψ y)))
    (hw : IsWeakGradientOf ψ Dψ) :
    (∫ ξ, ratioFn lam (freqPow 2 ξ) * ‖(fieldSymbol φ : Space → CSpace) ξ‖ ^ 2) ≤
      (∫ y, ‖φ y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y) := by
  have hfs : fieldSymbol φ = hatOf φ := rfl
  rw [hfs]
  have hA : Integrable (fun ξ => ‖(hatOf (fun y => φ y - ψ y) : Space → CSpace) ξ‖ ^ 2) volume :=
    sq_integrable (Lp.memLp _)
  have hB : Integrable (fun ξ => ∑ j : Fin 3,
      ‖(hatOf (fun y => Dψ y (unitVector j)) : Space → CSpace) ξ‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => sq_integrable (Lp.memLp _)
  have e1 : ∫ y, ‖φ y - ψ y‖ ^ 2 = ∫ ξ, ‖(hatOf (fun y => φ y - ψ y) : Space → CSpace) ξ‖ ^ 2 :=
    integral_sq_hat (hφ.sub hψ)
  have e2 : ∫ y, entrySq (Dψ y) = ∫ ξ, ∑ j : Fin 3,
      ‖(hatOf (fun y => Dψ y (unitVector j)) : Space → CSpace) ξ‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => sq_integrable (Lp.memLp _)]
    simp only [entrySq]
    rw [integral_finsetSum _ fun j _ => sq_integrable_real (f := fun y => Dψ y (unitVector j)) (memLp_comp hD hE j)]
    exact Finset.sum_congr rfl fun j _ => integral_sq_hat (memLp_comp hD hE j)
  rw [e1, e2, ← integral_const_mul, ← integral_add hA (hB.const_mul _)]
  refine integral_mono_of_nonneg (ae_of_all _ fun ξ => ?_) (hA.add (hB.const_mul _)) ?_
  · exact mul_nonneg (div_nonneg (freqPow_two_nonneg ξ) (by linarith [freqPow_two_nonneg ξ]))
      (by positivity)
  filter_upwards [hat_sub hφ hψ, freq_energy hψ hD hE hw] with ξ h1 h2
  rw [h1, ← h2]
  have := vec_bound hl (freqPow_two_nonneg ξ) ((hatOf φ : Space → CSpace) ξ) ((hatOf ψ : Space → CSpace) ξ)
  calc _ ≤ _ := this
    _ = _ := by ring

end Internal.SmoothingLower

theorem smoothingLower : SmoothingLowerStatement := by
  intro lam hl φ hφ
  apply le_csInf
  · refine ⟨_, 0, 0, MemLp.zero, aestronglyMeasurable_const, ?_, ?_, rfl⟩
    · simp [entrySq]
    · intro f _ j
      simp
  · rintro r ⟨ψ, Dψ, hψ, hD, hE, hw, rfl⟩
    exact Internal.SmoothingLower.bound_one hl hφ hψ hD hE hw

end CellCert

end Breakdown
