import Breakdown.Torus.HeatComparisonStatements
import Breakdown.Torus.HeatComparisonProj
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.H1Consistency
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section

namespace Breakdown.Periodic

namespace FreeInverse.Internal

open Freq

theorem isH1Field_of_test {φ : Space → Space} (hφ : IsTestField φ) : IsH1Field φ :=
  ⟨hφ.1, hφ.2.2, Freq.Internal.BilinTestFormula.test_memLp hφ 2,
    fun k => Freq.Internal.BilinTestFormula.partialField_memLp hφ k 2⟩

def physRapid {φ : Space → Space} (hφ : IsTestField φ) : 𝓢(Space, CSpace) :=
  (hφ.2.1.comp_left (g := complexifyVec) (map_zero _)).toSchwartzMap
    (complexifyVec.contDiff.comp hφ.1)

theorem freqTrVec_eq {φ : Space → Space} (hφ : IsTestField φ) (ξ : Space) :
    freqTrVec φ ξ = 𝓕 (physRapid hφ) ξ := by
  rw [SchwartzMap.fourier_coe]
  rfl

theorem continuous_heatFactor (τ : ℝ) : Continuous (Freq.heatFactor τ) := by
  unfold Freq.heatFactor
  fun_prop

theorem norm_heatFactor_le (τ : ℝ) (ξ : Space) : ‖Freq.heatFactor τ ξ‖ ≤ 1 := by
  unfold Freq.heatFactor
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have : 0 ≤ 4 * π ^ 2 * max τ 0 * ‖ξ‖ ^ 2 := by positivity
  linarith

theorem memLp_heat (τ : ℝ) (T : 𝓢(Space, CSpace)) (p : ℝ≥0∞) :
    MemLp (fun ξ => Freq.heatFactor τ ξ • T ξ) p volume := by
  refine (T.memLp p volume).of_le
    ((continuous_heatFactor τ).smul T.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_heatFactor_le τ ξ)

theorem freqTrInv_heat (τ : ℝ) (T : 𝓢(Space, CSpace)) (y : Space) :
    𝓕⁻ (fun ξ => Freq.heatFactor τ ξ • T ξ) y =
      ∫ ξ, expChar y ξ • (Freq.heatFactor τ ξ • T ξ) := by
  rw [Real.fourierInv_eq']
  congr 1
  funext ξ
  unfold expChar
  congr 2
  push_cast
  ring

theorem toPhys_heat (h4 : FreqTrInvL1L2) (τ : ℝ) (T : 𝓢(Space, CSpace)) (f : L2C)
    (hf : (f : Space → CSpace) =ᵐ[volume] fun ξ => Freq.heatFactor τ ξ • T ξ) :
    (toPhys f : Space → Space) =ᵐ[volume]
      fun y => realVec (∫ ξ, expChar y ξ • (Freq.heatFactor τ ξ • T ξ)) := by
  have h2 := memLp_heat τ T 2
  have hf' : f = toLpOrZero 2 (fun ξ => Freq.heatFactor τ ξ • T ξ) := by
    apply Lp.ext
    exact hf.trans (Freq.Internal.BilinTestFormula.toLpOrZero_ae h2).symm
  have h4' := h4 _ (memLp_heat τ T 1) h2
  rw [← hf'] at h4'
  have e : toPhys f = realPart (freqTrL2.symm f) := rfl
  rw [e]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec
    (freqTrL2.symm f), h4'] with y e1 e2
  rw [Freq.realPart, e1, e2, freqTrInv_heat]

theorem hat_ae (h5 : FreqTrL1L2) {φ : Space → Space} (hφ : IsTestField φ) :
    (freqTrR (Freq.complexify (toLpOrZero 2 φ)) : Space → CSpace) =ᵐ[volume]
      fun ξ => 𝓕 (physRapid hφ) ξ := by
  have m1 : MemLp (fun x => complexifyVec (φ x)) 1 volume :=
    complexifyVec.comp_memLp' (Freq.Internal.BilinTestFormula.test_memLp hφ 1)
  have m2 : MemLp (fun x => complexifyVec (φ x)) 2 volume :=
    complexifyVec.comp_memLp' (Freq.Internal.BilinTestFormula.test_memLp hφ 2)
  have e : Freq.complexify (toLpOrZero 2 φ) = toLpOrZero 2 (fun x => complexifyVec (φ x)) := by
    apply Lp.ext
    exact (Freq.Internal.H1Consistency.complexify_toLp_ae
      (Freq.Internal.BilinTestFormula.test_memLp hφ 2)).trans
      (Freq.Internal.BilinTestFormula.toLpOrZero_ae m2).symm
  have e2 : freqTrR (Freq.complexify (toLpOrZero 2 φ)) =
      freqTrL2 (toLpOrZero 2 (fun x => complexifyVec (φ x))) := by
    rw [e]
    rfl
  rw [e2]
  filter_upwards [h5 _ m1 m2] with ξ h
  rw [h, ← freqTrVec_eq hφ]
  rfl

open SchwartzMap LineDeriv in
theorem freqTr_deriv_eq {φ : Space → Space} (hφ : IsTestField φ) (j : Fin 3) (ξ : Space) :
    𝓕 (∂_{unitVector j} (physRapid hφ)) ξ =
      (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • 𝓕 (physRapid hφ) ξ := by
  have h : 𝓕 (∂_{unitVector j} (physRapid hφ)) ξ =
      (2 * π * Complex.I) • ((ξ j : ℝ) • 𝓕 (physRapid hφ) ξ) := by
    rw [fourier_lineDerivOp_eq]
    have hg : (fun x : Space => inner ℝ x (unitVector j)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (unitVector j)).hasTemperateGrowth
    rw [smul_apply, smulLeftCLM_apply_apply hg]
    simp [unitVector, EuclideanSpace.inner_single_right]
  rw [h, ← Complex.coe_smul (ξ j) (𝓕 (physRapid hφ) ξ), smul_smul]

end FreeInverse.Internal

open FreeInverse.Internal Freq.Internal.H1Consistency DivFreeProjection.Internal in
theorem r3FreeFormula (h1 : Freq.FieldOpRealized) (h2 : Freq.HeatSemigroup)
    (h3 : Freq.VelocityInvertsHalfSsp) (h4 : Freq.FreqTrInvL1L2) (h5 : Freq.FreqTrL1L2)
    (h7 : Freq.FreqTrConjSym) : R3FreeFormula := by
  intro φ hφ τ _
  have hf := isH1Field_of_test hφ
  set W : Freq.L2C := Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 φ)) with hW
  have hs : W ∈ Freq.Sig := hat_mem_sig h1 h7 hf
  have hog := ofGrad_ae h1 hf
  have hmem : Freq.ofGrad φ ∈ Freq.Sig :=
    mem_sig_of_ae h1 hs (fun ξ => 2 * π * ‖ξ‖) (fun ξ => by simp) hog
  have hemb : (Freq.embedX φ : Freq.L2C) = Freq.ofGrad φ := by rw [Freq.embedX, dif_pos hmem]
  have hWfreqTr := hat_ae h5 hφ
  set S := physRapid hφ with hSdef
  set g : Freq.X := Freq.heatX τ ⟨W, hs⟩ with hgdef
  have hg : ((g : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => Freq.heatFactor τ ξ • 𝓕 S ξ := by
    have e : (g : Freq.L2C) = Freq.heatL2 τ W := h2.2.2.2.2.2 τ ⟨W, hs⟩
    rw [e]
    filter_upwards [heat_ae h1 τ W, hWfreqTr] with ξ e1 e2
    rw [Freq.heatL2, e1, e2]
  have hh : ((Freq.heatX τ (Freq.embedX φ) : Freq.X) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => Freq.heatFactor τ ξ • ((2 * π * ‖ξ‖) • 𝓕 S ξ) := by
    rw [h2.2.2.2.2.2 τ (Freq.embedX φ), hemb]
    filter_upwards [heat_ae h1 τ (Freq.ofGrad φ), hog, hWfreqTr] with ξ e1 e2 e3
    rw [Freq.heatL2, e1, e2, e3]
  refine ⟨?_, fun j => ?_⟩
  · have hhalf : Freq.IsHalfSspOf g (Freq.heatX τ (Freq.embedX φ)) := by
      filter_upwards [hg, hh] with ξ e1 e2
      rw [e1, e2, smul_comm]
    filter_upwards [h3 _ _ hhalf, toPhys_heat h4 τ (𝓕 S) g hg] with y e1 e2
    rw [e1, e2]
    congr 2
  · set T : 𝓢(Space, Freq.CSpace) := 𝓕 (LineDeriv.lineDerivOp (unitVector j) S) with hTdef
    have hT : ∀ ξ, T ξ = (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • 𝓕 S ξ :=
      fun ξ => freqTr_deriv_eq hφ j ξ
    have hd : (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
        ((Freq.heatX τ (Freq.embedX φ) : Freq.X) : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
          fun ξ => Freq.heatFactor τ ξ • T ξ := by
      filter_upwards [derivSymbol_ae h1 j _, hh, ae_ne_zero] with ξ e1 e2 hξ
      rw [e1, e2, hT, smul_comm (Freq.derivSymbol j ξ) (Freq.heatFactor τ ξ)]
      congr 1
      rw [← Complex.coe_smul (2 * π * ‖ξ‖) (𝓕 S ξ), smul_smul, deriv_mul j ξ hξ]
    have hpx : Freq.partialX j (Freq.heatX τ (Freq.embedX φ)) =
        Freq.toPhys (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
          ((Freq.heatX τ (Freq.embedX φ) : Freq.X) : Freq.L2C)) := rfl
    rw [hpx]
    filter_upwards [toPhys_heat h4 τ T _ hd] with y e1
    rw [e1]
    congr 2
    funext ξ
    rw [freeGradDensity, freeDensity, hT, freqTrVec_eq hφ,
      smul_comm (Freq.heatFactor τ ξ) (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)),
      smul_comm (expChar y ξ) (2 * π * Complex.I * ((ξ j : ℝ) : ℂ))]

end Breakdown.Periodic
