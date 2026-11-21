import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveCurlWeight
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.WeakInX

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.CurlEnergy

open Freq

def crossMap (j : Fin 3) : Space →L[ℝ] Space :=
  ∑ i : Fin 3, ∑ l : Fin 3,
    alternatingSymbol i j l • (EuclideanSpace.proj l : Space →L[ℝ] ℝ).smulRight (unitVector i)

theorem crossMap_apply (j : Fin 3) (u : Space) :
    crossMap j u = ∑ i : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l * u l) • unitVector i := by
  simp [crossMap, smul_smul]

theorem curlVec_eq_sum (A : Space →L[ℝ] Space) :
    curlVec A = ∑ j : Fin 3, crossMap j (A (unitVector j)) := by
  simp only [crossMap_apply, curlVec, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem continuous_curlVec : Continuous (fun A : Space →L[ℝ] Space => curlVec A) := by
  simp only [curlVec_eq_sum]
  exact continuous_finsetSum _ fun j _ => (crossMap j).continuous.comp
    (continuous_id.clm_apply continuous_const)

def curlX : X →L[ℝ] L2R :=
  ∑ j : Fin 3, (ContinuousLinearMap.compLpL 2 volume (crossMap j)) ∘L partialX j

theorem curlX_ae (x : X) :
    (curlX x : Space → Space) =ᵐ[volume]
      fun y => ∑ j : Fin 3, crossMap j ((partialX j x : Space → Space) y) := by
  have e : curlX x = ∑ j : Fin 3, ContinuousLinearMap.compLpL 2 volume (crossMap j) (partialX j x) := by
    simp [curlX]
  rw [e]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j : Fin 3 => ContinuousLinearMap.compLpL 2 volume (crossMap j) (partialX j x)),
    ae_all_iff.2 fun j : Fin 3 => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
      (crossMap j) (partialX j x)] with y hs hj
  rw [hs, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hj j

theorem sq_norm_eq_integral (p : L2R) : ‖p‖ ^ 2 = ∫ y, ‖(p : Space → Space) y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext y
  exact real_inner_self_eq_norm_sq _

theorem sq_norm_eq_lintegral (p : L2R) :
    ENNReal.ofReal (‖p‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖(p : Space → Space) y‖ ^ 2) := by
  rw [sq_norm_eq_integral, ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp p).integrable_norm_pow two_ne_zero) (Filter.Eventually.of_forall fun y => sq_nonneg _)]

theorem sq_norm_curlX_embed {ψ : Space → Space} (hψ : IsTestField ψ) :
    ‖curlX (embedX ψ)‖ ^ 2 = ∑ j : Fin 3, ‖partialX j (embedX ψ)‖ ^ 2 := by
  have hd := Freq.isDecayField_of_isTestField hψ
  have hp : ∀ j, (partialX j (embedX ψ) : Space → Space) =ᵐ[volume] partialField ψ j :=
    fun j => partial_holds.1 ψ hd j
  have hc : (curlX (embedX ψ) : Space → Space) =ᵐ[volume] fun y => curlVec (fderiv ℝ ψ y) := by
    filter_upwards [curlX_ae (embedX ψ), ae_all_iff.2 hp] with y h1 h2
    rw [h1, curlVec_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h2 j]; rfl
  have hsq : ∀ j : Fin 3, (fun y => ‖(partialX j (embedX ψ) : Space → Space) y‖ ^ 2) =ᵐ[volume]
      fun y => ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2 := by
    intro j
    filter_upwards [hp j] with y hy
    rw [hy]
    rfl
  have hint : ∀ j : Fin 3, Integrable (fun y => ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) volume :=
    fun j => ((Lp.memLp (partialX j (embedX ψ))).integrable_norm_pow two_ne_zero).congr (hsq j)
  have hI := curlWeightIdentityHolds_proof (fun _ => (1 : ℝ)) ψ contDiff_const hψ.1 hψ.2.1 hψ.2.2
  simp only [one_mul, fderiv_const_apply, zero_apply, zero_mul,
    Finset.sum_const_zero, integral_zero, sub_zero] at hI
  have hc2 : (fun y => ‖(curlX (embedX ψ) : Space → Space) y‖ ^ 2) =ᵐ[volume]
      fun y => ‖curlVec (fderiv ℝ ψ y)‖ ^ 2 := by
    filter_upwards [hc] with y hy
    rw [hy]
  rw [sq_norm_eq_integral, integral_congr_ae hc2, hI]
  unfold matSq
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sq_norm_eq_integral, integral_congr_ae (hsq j)]

theorem sq_norm_curlX (z : X) : ‖curlX z‖ ^ 2 = ∑ j : Fin 3, ‖partialX j z‖ ^ 2 := by
  have hL : Continuous (fun z : X => ‖curlX z‖ ^ 2) := (curlX.continuous.norm).pow 2
  have hR : Continuous (fun z : X => ∑ j : Fin 3, ‖partialX j z‖ ^ 2) :=
    continuous_finsetSum _ fun j _ => ((partialX j).continuous.norm).pow 2
  have hsub : (testSpan : Set X) ⊆ {z : X | ‖curlX z‖ ^ 2 = ∑ j : Fin 3, ‖partialX j z‖ ^ 2} := by
    intro z hz
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds z hz
    exact sq_norm_curlX_embed hψ
  have hcl := closure_minimal hsub (isClosed_eq hL hR)
  rw [testDense_holds.2.closure_eq] at hcl
  exact hcl (Set.mem_univ z)

theorem curlVec_axialRot (φ : ℝ) (A : Space →L[ℝ] Space) (i : Fin 3) :
    ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * axialRot (-φ) (A (axialRot φ (unitVector j))) l
      = axialRot (-φ) (curlVec A) i := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases i <;>
  simp [axialRot, curlVec, unitVector, Fin.sum_univ_three, alternatingSymbol, map_add, map_smul,
    Real.cos_neg, Real.sin_neg] <;>
  ring_nf
  linear_combination ((A (EuclideanSpace.single 0 1)) 1 - (A (EuclideanSpace.single 1 1)) 0) * h

theorem curlOfGrad_modeGrad_eq {G : ℝ → Space → (Space →L[ℝ] Space)} (ι : ℤ × ℤ) {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => G (z.1 + p.1) (axialRot p.2 z.2))
      Internal.ModeRotation.boxMeasure) :
    curlOfGrad (modeGrad ι G z.1 z.2) = modeVel ι (fun s x => curlVec (G s x)) z.1 z.2 := by
  funext i
  have e := Internal.ModeRotation.modeAverage_sum ι
    (fun jl : Fin 3 × Fin 3 => alternatingSymbol i jl.1 jl.2)
    (fun jl τ φ => axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector jl.1))) jl.2)
    (fun jl => Internal.ModeRotation.integrable_gradComponent axialRotationHolds_proof hz (jl.2, jl.1))
  have hF : ∀ τ φ, axialRot (-φ) (curlVec (G (z.1 + τ) (axialRot φ z.2))) i =
      ∑ jl : Fin 3 × Fin 3, alternatingSymbol i jl.1 jl.2
        * axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector jl.1))) jl.2 := by
    intro τ φ
    rw [← curlVec_axialRot, Fintype.sum_prod_type]
  have hR : modeVel ι (fun s x => curlVec (G s x)) z.1 z.2 i =
      (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Internal.ModeRotation.expFactor ι τ φ * ((∑ jl : Fin 3 × Fin 3, alternatingSymbol i jl.1 jl.2
          * axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector jl.1))) jl.2 : ℝ) : ℂ) := by
    unfold modeVel
    rw [Internal.ModeRotation.modeAverage_eq]
    simp only [hF]
  rw [hR, e]
  unfold curlOfGrad modeGrad
  simp only [Internal.ModeRotation.modeAverage_eq]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Internal.CurlEnergy

open Internal.CurlEnergy in
theorem lintegral_curlVec_sq_eq_matSq {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f g) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (g y (unitVector i)) i = 0)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (g y)) < ⊤) :
    ∫⁻ y, ENNReal.ofReal (‖curlVec (g y)‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (matSq (g y)) := by
  set C : ℝ := (∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6)).toReal
    + 3 * (∫⁻ y, ENNReal.ofReal (matSq (g y))).toReal with hCdef
  have hC6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) ≤ ENNReal.ofReal C := by
    calc ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6)
        = ENNReal.ofReal ((∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6)).toReal) := (ENNReal.ofReal_toReal h6.ne).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal
          (le_add_of_nonneg_right (mul_nonneg (by norm_num) ENNReal.toReal_nonneg))
  have hC2 : ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ≤ ENNReal.ofReal C := by
    calc ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2)
        ≤ ∫⁻ y, ENNReal.ofReal 3 * ENNReal.ofReal (matSq (g y)) := lintegral_mono fun y => by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (Internal.PerturbationFacts.sq_norm_le_three_matNorm _)
      _ = ENNReal.ofReal 3 * ∫⁻ y, ENNReal.ofReal (matSq (g y)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (3 * (∫⁻ y, ENNReal.ofReal (matSq (g y))).toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal h2.ne]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  have hS : WeakProfile.IsSlice f g C := ⟨hg, hdiv, hC6, hC2⟩
  obtain ⟨x, hx⟩ := WeakProfile.gradientFreqTr_holds f g C hS
  have hcurl : (curlX x : Space → Space) =ᵐ[volume] fun y => curlVec (g y) := by
    filter_upwards [curlX_ae x, ae_all_iff.2 hx] with y h1 h2
    rw [h1, curlVec_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h2 j]; rfl
  have hL : ∫⁻ y, ENNReal.ofReal (‖curlVec (g y)‖ ^ 2) = ENNReal.ofReal (‖curlX x‖ ^ 2) := by
    rw [sq_norm_eq_lintegral]
    refine lintegral_congr_ae ?_
    filter_upwards [hcurl] with y hy
    rw [hy]
  have hR : ∑ j : Fin 3, ENNReal.ofReal (‖Freq.partialX j x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (matSq (g y)) := by
    simp only [sq_norm_eq_lintegral]
    have hm : ∀ j ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable
        (fun y => ENNReal.ofReal (‖(Freq.partialX j x : Space → Space) y‖ ^ 2)) volume := fun j _ =>
      ((Lp.aestronglyMeasurable (Freq.partialX j x)).norm.aemeasurable.pow_const 2).ennreal_ofReal
    rw [← lintegral_finsetSum' Finset.univ hm]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hx] with y hy
    rw [matSq, ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun j _ => by rw [hy j]; rfl
  rw [hL, sq_norm_curlX, ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _, hR]

theorem periodLIntegral_curlVec_sq_eq {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖curlVec (G σ y)‖ ^ 2) = periodLIntegral (fun σ y => matSq (G σ y)) := by
  unfold periodLIntegral
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.divergence_free,
    ae_restrict_of_ae hv.sixth_power, Internal.PerturbationFacts.ae_matSq_lt_top hv] with σ h1 h2 h3 h4
  exact lintegral_curlVec_sq_eq_matSq h1 h2 h3 h4

theorem ae_curlOfGrad_modeGrad {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) :
    ∀ᵐ z : ℝ × Space, curlOfGrad (modeGrad ι G z.1 z.2) = modeVel ι (fun s x => curlVec (G s x)) z.1 z.2 := by
  obtain ⟨-, hlG, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  filter_upwards [Internal.ModeRotation.ae_integrable_orbit axialRotationHolds_proof hlG] with z hz
  exact Internal.CurlEnergy.curlOfGrad_modeGrad_eq ι hz

end Coercive

end Breakdown
