import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped ContDiff Convolution

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula SteadyCert

namespace PotentialConstantInternal

theorem locallyIntegrable_of_sq {q : Space → ℝ} (hm : AEStronglyMeasurable q volume)
    (hsq : IsLocalSquareIntegrable (fun y => q y ^ 2)) : LocallyIntegrable q volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have h2 : MemLp q 2 (volume.restrict K) := (memLp_two_iff_integrable_sq hm.restrict).2 (hsq K hK)
  exact h2.integrable (by norm_num)

theorem clm_eq_zero_of_units (c : Space →L[ℝ] ℝ) (h : ∀ j, c (unitVector j) = 0) : c = 0 := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_
  simpa [unitVector] using h i

theorem reflect_fderiv {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (x y e : Space) :
    fderiv ℝ (fun z => ρ (x - z)) y e = -(fderiv ℝ ρ (x - y) e) := by
  have h1 : HasFDerivAt (fun z : Space => x - z) (-ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := ((hρ.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
  rw [show (fun z => ρ (x - z)) = ρ ∘ (fun z : Space => x - z) from rfl, h2.fderiv]
  simp

theorem conv_fderiv_zero {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    {f : Space → ℝ} (hf : LocallyIntegrable f volume)
    (h0 : ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * f y = 0) (x : Space) :
    (fderiv ℝ ρ ⋆[(lsmul ℝ ℝ).precompL Space, volume] f) x = 0 := by
  apply clm_eq_zero_of_units
  intro j
  have hint := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left ((lsmul ℝ ℝ).precompL Space)
    (hρ.continuous_fderiv (by simp)) hf x
  rw [convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [precompL_apply, lsmul_apply, smul_eq_mul]
  have hs := integral_sub_left_eq_self (μ := volume)
    (fun y => fderiv ℝ ρ (x - y) (unitVector j) * f y) x
  simp only [sub_sub_cancel] at hs
  rw [hs]
  have hφs : ContDiff ℝ ∞ (fun z => ρ (x - z)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun z => ρ (x - z)) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hr : ∀ y, fderiv ℝ ρ (x - y) (unitVector j) = -(fderiv ℝ (fun z => ρ (x - z)) y (unitVector j)) := by
    intro y
    rw [reflect_fderiv hρ, neg_neg]
  simp_rw [hr, neg_mul]
  rw [integral_neg, h0 _ hφs hφc j, neg_zero]

theorem conv_const {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    {f : Space → ℝ} (hf : LocallyIntegrable f volume)
    (h0 : ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * f y = 0) (x y : Space) :
    (ρ ⋆[lsmul ℝ ℝ, volume] f) x = (ρ ⋆[lsmul ℝ ℝ, volume] f) y := by
  have hd : ∀ z, HasFDerivAt (ρ ⋆[lsmul ℝ ℝ, volume] f)
      ((fderiv ℝ ρ ⋆[(lsmul ℝ ℝ).precompL Space, volume] f) z) z :=
    fun z => hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) (hρ.of_le (by simp)) hf z
  refine is_const_of_fderiv_eq_zero (fun z => (hd z).differentiableAt) (fun z => ?_) x y
  rw [(hd z).fderiv, conv_fderiv_zero hρ hc hf h0 z]

def shrinkBump (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem ae_const_of_weak_grad_zero {f : Space → ℝ} (hf : LocallyIntegrable f volume)
    (h0 : ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * f y = 0) :
    ∃ C : ℝ, ∀ᵐ y, f y = C := by
  have htend : Tendsto (fun n => (shrinkBump n).rOut) atTop (𝓝 0) := by
    simpa [shrinkBump] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have hK : ∀ᶠ n in atTop, (shrinkBump n).rOut ≤ 2 * (shrinkBump n).rIn :=
    Eventually.of_forall fun n => le_rfl
  have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) htend hK hf
  have hconst : ∀ n x, ((shrinkBump n).normed volume ⋆[lsmul ℝ ℝ, volume] f) x
      = ((shrinkBump n).normed volume ⋆[lsmul ℝ ℝ, volume] f) 0 := fun n x =>
    conv_const (shrinkBump n).contDiff_normed (shrinkBump n).hasCompactSupport_normed hf h0 x 0
  have hlim' : ∀ᵐ x, Tendsto (fun n => ((shrinkBump n).normed volume ⋆[lsmul ℝ ℝ, volume] f) 0)
      atTop (𝓝 (f x)) := hlim.mono fun x hx => by
        rwa [show (fun i => ((shrinkBump i).normed volume ⋆[lsmul ℝ ℝ, volume] f) x)
          = fun n => ((shrinkBump n).normed volume ⋆[lsmul ℝ ℝ, volume] f) 0 from funext fun n => hconst n x] at hx
  have : (ae (volume : Measure Space)).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨x₀, hx₀⟩ := hlim'.exists
  exact ⟨f x₀, hlim'.mono fun x hx => tendsto_nhds_unique hx hx₀⟩

end PotentialConstantInternal

open PotentialConstantInternal in
theorem potentialConstant : PotentialConstantHolds := by
  intro Q q q' hq hq'
  have hqi := locallyIntegrable_of_sq hq.1 hq.2.1
  have hqi' := locallyIntegrable_of_sq hq'.1 hq'.2.1
  obtain ⟨C, hC⟩ := ae_const_of_weak_grad_zero (hqi'.sub hqi) (fun φ hs hc j => by
    have hD : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hDc : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) := hc.fderiv_apply (𝕜 := ℝ) _
    have i1 := hqi.integrable_smul_left_of_hasCompactSupport hD hDc
    have i2 := hqi'.integrable_smul_left_of_hasCompactSupport hD hDc
    simp only [smul_eq_mul] at i1 i2
    have e1 := hq.2.2 φ ⟨hs, hc⟩ j
    have e2 := hq'.2.2 φ ⟨hs, hc⟩ j
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub i2 i1, e1, e2, sub_self])
  exact ⟨C, hC.mono fun y hy => by simp only [Pi.sub_apply] at hy; linarith⟩

end SideTrace

end CertCell

end Breakdown
