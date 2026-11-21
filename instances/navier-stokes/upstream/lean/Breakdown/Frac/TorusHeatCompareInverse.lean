import Breakdown.Frac.StTorusShell
import Breakdown.Torus.HeatComparisonInverse
import Breakdown.Torus.HeatComparisonFreeR3
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.FreqTrL1
import Breakdown.FreqTr.FreqTrConjSym

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section

namespace Breakdown.Periodic

namespace FracHeatCompareInverse.Internal

open Freq

theorem sq_le_rpow_add_one {α : ℝ} (hα : 1 ≤ α) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 ≤ t ^ (2 * α) + 1 := by
  rcases le_total t 1 with h | h
  · have h1 : t ^ 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ t ^ (2 * α) := Real.rpow_nonneg ht _
    linarith
  · have h1 : t ^ (2 : ℝ) ≤ t ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_two] at h1
    linarith

theorem fracHeatFactor_pos (α t : ℝ) (ξ : Space) : 0 < Freq.fracHeatFactor α t ξ := Real.exp_pos _

theorem fracHeatFactor_le_exp_sq {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 ≤ τ) (ξ : Space) :
    Freq.fracHeatFactor α τ ξ ≤ Real.exp τ * Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) := by
  unfold Freq.fracHeatFactor
  rw [max_eq_left hτ, ← Real.exp_add, Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left
    (sq_le_rpow_add_one hα (by positivity : 0 ≤ 2 * π * ‖ξ‖)) hτ
  have e : (4 * π ^ 2 * τ) * ‖ξ‖ ^ 2 = τ * (2 * π * ‖ξ‖) ^ 2 := by ring
  rw [e]
  rw [mul_add, mul_one] at h
  linarith

theorem fracHeatFactor_le_one (α t : ℝ) (ξ : Space) : Freq.fracHeatFactor α t ξ ≤ 1 := by
  unfold Freq.fracHeatFactor
  rw [Real.exp_le_one_iff]
  have h0 : 0 ≤ max t 0 := le_max_right t 0
  have h1 : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ max t 0 * (2 * π * ‖ξ‖) ^ (2 * α) := mul_nonneg h0 h1
  linarith

theorem continuous_fracHeatFactor {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Continuous (Freq.fracHeatFactor α t) := by
  unfold Freq.fracHeatFactor
  have hc : Continuous fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α) :=
    (by fun_prop : Continuous fun ξ : Space => 2 * π * ‖ξ‖).rpow_const
      (fun _ => Or.inr (by linarith))
  exact (continuous_const.mul hc).neg.rexp

theorem norm_source_le {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 ≤ τ) (A : Space → Space) (ξ : Space) :
    ‖Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec A ξ)‖ ≤
      (Real.exp τ * (2 * ∫ x, ‖complexifyVec (A x)‖)) *
        Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (fracHeatFactor_pos _ _ _)]
  have hl : ‖divFreeVec ξ (freqTrVec A ξ)‖ ≤ 2 * ∫ x, ‖complexifyVec (A x)‖ :=
    (SourceInverse.Internal.norm_divFreeVec_le _ _).trans
      (by gcongr; exact SourceInverse.Internal.norm_freqTrVec_le _ _)
  calc Freq.fracHeatFactor α τ ξ * ‖divFreeVec ξ (freqTrVec A ξ)‖
      ≤ (Real.exp τ * Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) *
          (2 * ∫ x, ‖complexifyVec (A x)‖) :=
        mul_le_mul (fracHeatFactor_le_exp_sq hα hτ ξ) hl (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_gradSource_le {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) (A : Space → Space) (j : Fin 3)
    (ξ : Space) :
    ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) •
        (Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec A ξ))‖ ≤
      ((Real.exp τ * (2 * ∫ x, ‖complexifyVec (A x)‖)) * (1 + 2 / τ)) *
        Real.exp (-((2 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) := by
  have hs : ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ ≤ 2 * π * ‖ξ‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
    gcongr
    exact PiLp.norm_apply_le ξ j
  have hM : 0 ≤ Real.exp τ * (2 * ∫ x, ‖complexifyVec (A x)‖) := by
    have : 0 ≤ ∫ x, ‖complexifyVec (A x)‖ := integral_nonneg fun x => norm_nonneg _
    positivity
  rw [norm_smul]
  calc ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ *
        ‖Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec A ξ)‖
      ≤ (2 * π * ‖ξ‖) * ((Real.exp τ * (2 * ∫ x, ‖complexifyVec (A x)‖)) *
          Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) :=
        mul_le_mul hs (norm_source_le hα hτ.le A ξ) (norm_nonneg _) (by positivity)
    _ = (Real.exp τ * (2 * ∫ x, ‖complexifyVec (A x)‖)) *
          (2 * π * ‖ξ‖ * Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) := by ring
    _ ≤ (Real.exp τ * (2 * ∫ x, ‖complexifyVec (A x)‖)) *
          ((1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (SourceInverse.Internal.weight_le hτ _) hM
    _ = _ := by ring

theorem fracHeat_realized {α : ℝ} (hα : 0 < α) (t : ℝ) :
    IsRealizedBy (fracHeatL2 α t) id
      (fun ξ => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) := by
  have hm : AEStronglyMeasurable
      (fun ξ : Space => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    ((continuous_fracHeatFactor hα t).smul continuous_const).aestronglyMeasurable
  have hb : ∀ ξ, ‖fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := by
    intro ξ
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (fracHeatFactor_pos α t ξ)]
    calc fracHeatFactor α t ξ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
          mul_le_mul (fracHeatFactor_le_one α t ξ) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have h := fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) _ 1 hm hb
  rw [ContinuousLinearEquiv.coe_refl'] at h
  exact h

theorem fracHeat_ae {α : ℝ} (hα : 0 < α) (t : ℝ) (f : L2C) :
    ∀ᵐ ξ ∂volume, (fracHeatL2 α t f : Space → CSpace) ξ =
      fracHeatFactor α t ξ • (f : Space → CSpace) ξ := by
  filter_upwards [fracHeat_realized hα t f] with ξ hξ
  rw [hξ]
  rfl

theorem memLp_fracHeat {α : ℝ} (hα : 0 < α) (τ : ℝ) (T : 𝓢(Space, CSpace)) (p : ℝ≥0∞) :
    MemLp (fun ξ => Freq.fracHeatFactor α τ ξ • T ξ) p volume := by
  refine (T.memLp p volume).of_le
    ((continuous_fracHeatFactor hα τ).smul T.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (fracHeatFactor_pos _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (fracHeatFactor_le_one α τ ξ)

theorem inverseTransform_fracHeat (α τ : ℝ) (T : 𝓢(Space, CSpace)) (y : Space) :
    𝓕⁻ (fun ξ => Freq.fracHeatFactor α τ ξ • T ξ) y =
      ∫ ξ, expChar y ξ • (Freq.fracHeatFactor α τ ξ • T ξ) := by
  rw [Real.fourierInv_eq']
  congr 1
  funext ξ
  unfold expChar
  congr 2
  push_cast
  ring

theorem toPhys_fracHeat {α : ℝ} (hα : 0 < α) (τ : ℝ) (T : 𝓢(Space, CSpace)) (f : L2C)
    (hf : (f : Space → CSpace) =ᵐ[volume] fun ξ => Freq.fracHeatFactor α τ ξ • T ξ) :
    (toPhys f : Space → Space) =ᵐ[volume]
      fun y => realVec (∫ ξ, expChar y ξ • (Freq.fracHeatFactor α τ ξ • T ξ)) := by
  have h2 := memLp_fracHeat hα τ T 2
  have hf' : f = toLpOrZero 2 (fun ξ => Freq.fracHeatFactor α τ ξ • T ξ) := by
    apply Lp.ext
    exact hf.trans (Freq.Internal.BilinTestFormula.toLpOrZero_ae h2).symm
  have h4' := freqTrL1L2.2 _ (memLp_fracHeat hα τ T 1) h2
  rw [← hf'] at h4'
  have e : toPhys f = realPart (freqTrL2.symm f) := rfl
  rw [e]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec
    (freqTrL2.symm f), h4'] with y e1 e2
  rw [Freq.realPart, e1, e2, inverseTransform_fracHeat]

end FracHeatCompareInverse.Internal

open SourceInverse.Internal FracHeatCompareInverse.Internal in
theorem fracR3ValueFormula_of (α : ℝ) (hα : 1 < α) (hF : FracHeatSolenoidalFactor α) :
    FracR3ValueFormula α := by
  intro b' τ hτ A hA
  obtain ⟨g, hgG, hhl⟩ := hF b' τ hτ A hA
  set G : Space → Freq.CSpace :=
    fun ξ => Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec (⇑A) ξ) with hGdef
  have hGm : AEStronglyMeasurable G volume := (Lp.aestronglyMeasurable (g : Freq.L2C)).congr hgG
  have hG1 := (memLp_of_expSq hGm (by positivity : 0 < 4 * π ^ 2 * τ)
    (FracHeatCompareInverse.Internal.norm_source_le hα.le hτ.le (⇑A))).1
  refine ⟨?_, fun j => ?_⟩
  · filter_upwards [Freq.velocityInverts_holds g _ hhl,
      toPhys_ae Freq.freqTrL1L2.2 hgG hG1] with y e1 e2
    rw [e1, e2]
    rfl
  · set Gj : Space → Freq.CSpace :=
      fun ξ => (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • G ξ with hGjdef
    have hGjm : AEStronglyMeasurable Gj volume := by
      exact (Continuous.aestronglyMeasurable
        (by fun_prop : Continuous fun ξ : Space => (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)))).smul hGm
    have hGj1 := (memLp_of_expSq hGjm (by positivity : 0 < 2 * π ^ 2 * τ)
      (FracHeatCompareInverse.Internal.norm_gradSource_le hα.le hτ (⇑A) j)).1
    have hx : (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
        ((Freq.fracHeatSolenoidal α τ A : Freq.X) : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume] Gj := by
      filter_upwards [Freq.Internal.BilinTestFormula.symbol_ae Freq.fieldOpRealized_holds
        (Freq.derivSymbol j)
        (Freq.Internal.BilinTestFormula.measurable_derivSymbol j)
        (Freq.Internal.BilinTestFormula.norm_derivSymbol_le j) _, hhl, hgG] with ξ e1 e2 e3
      rw [e1, e2, e3, derivSymbol_smul]
    filter_upwards [toPhys_ae Freq.freqTrL1L2.2 hx hGj1] with y e1
    change (Freq.toPhys (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
      ((Freq.fracHeatSolenoidal α τ A : Freq.X) : Freq.L2C)) : Space → Space) y = _
    rw [e1]
    congr 2
    funext ξ
    simp only [hGjdef, hGdef, fracGradDensity, fracValueDensity]
    exact smul_comm _ _ _

open FreeInverse.Internal FracHeatCompareInverse.Internal Freq.Internal.H1Consistency
  DivFreeProjection.Internal in
theorem fracR3FreeFormula (α : ℝ) (hα : 1 < α) (hH : Freq.FracHeatSemigroup α) :
    FracR3FreeFormula α := by
  have hα0 : 0 < α := by linarith
  have h1 := Freq.fieldOpRealized_holds
  intro φ hφ τ _
  have hf := isH1Field_of_test hφ
  set W : Freq.L2C := Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 φ)) with hW
  have hs : W ∈ Freq.Sig := hat_mem_sig h1 (Freq.freqTrConjSym h1) hf
  have hog := ofGrad_ae h1 hf
  have hmem : Freq.ofGrad φ ∈ Freq.Sig :=
    mem_sig_of_ae h1 hs (fun ξ => 2 * π * ‖ξ‖) (fun ξ => by simp) hog
  have hemb : (Freq.embedX φ : Freq.L2C) = Freq.ofGrad φ := by rw [Freq.embedX, dif_pos hmem]
  have hWfreqTr := hat_ae Freq.freqTrL1L2.1 hφ
  set S := physRapid hφ with hSdef
  set g : Freq.X := Freq.fracHeatX α τ ⟨W, hs⟩ with hgdef
  have hg : ((g : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => Freq.fracHeatFactor α τ ξ • 𝓕 S ξ := by
    have e : (g : Freq.L2C) = Freq.fracHeatL2 α τ W := hH.2.2.2.2.2 τ ⟨W, hs⟩
    rw [e]
    filter_upwards [fracHeat_ae hα0 τ W, hWfreqTr] with ξ e1 e2
    rw [e1, e2]
  have hh : ((Freq.fracHeatX α τ (Freq.embedX φ) : Freq.X) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => Freq.fracHeatFactor α τ ξ • ((2 * π * ‖ξ‖) • 𝓕 S ξ) := by
    rw [hH.2.2.2.2.2 τ (Freq.embedX φ), hemb]
    filter_upwards [fracHeat_ae hα0 τ (Freq.ofGrad φ), hog, hWfreqTr] with ξ e1 e2 e3
    rw [e1, e2, e3]
  refine ⟨?_, fun j => ?_⟩
  · have hhalf : Freq.IsHalfSspOf g (Freq.fracHeatX α τ (Freq.embedX φ)) := by
      filter_upwards [hg, hh] with ξ e1 e2
      rw [e1, e2, smul_comm]
    filter_upwards [Freq.velocityInverts_holds _ _ hhalf, toPhys_fracHeat hα0 τ (𝓕 S) g hg]
      with y e1 e2
    rw [e1, e2]
    congr 2
  · set T : 𝓢(Space, Freq.CSpace) := 𝓕 (LineDeriv.lineDerivOp (unitVector j) S) with hTdef
    have hT : ∀ ξ, T ξ = (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • 𝓕 S ξ :=
      fun ξ => freqTr_deriv_eq hφ j ξ
    have hd : (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
        ((Freq.fracHeatX α τ (Freq.embedX φ) : Freq.X) : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
          fun ξ => Freq.fracHeatFactor α τ ξ • T ξ := by
      filter_upwards [derivSymbol_ae h1 j _, hh, ae_ne_zero] with ξ e1 e2 hξ
      rw [e1, e2, hT, smul_comm (Freq.derivSymbol j ξ) (Freq.fracHeatFactor α τ ξ)]
      congr 1
      rw [← Complex.coe_smul (2 * π * ‖ξ‖) (𝓕 S ξ), smul_smul, deriv_mul j ξ hξ]
    have hpx : Freq.partialX j (Freq.fracHeatX α τ (Freq.embedX φ)) =
        Freq.toPhys (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
          ((Freq.fracHeatX α τ (Freq.embedX φ) : Freq.X) : Freq.L2C)) := rfl
    rw [hpx]
    filter_upwards [toPhys_fracHeat hα0 τ T _ hd] with y e1
    rw [e1]
    congr 2
    funext ξ
    rw [fracFreeGradDensity, fracFreeDensity, hT, freqTrVec_eq hφ,
      smul_comm (Freq.fracHeatFactor α τ ξ) (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)),
      smul_comm (expChar y ξ) (2 * π * Complex.I * ((ξ j : ℝ) : ℂ))]

end Breakdown.Periodic
