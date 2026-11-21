import Breakdown.Torus.HeatComparisonStatements
import Breakdown.Torus.HeatComparisonProj
import Breakdown.FreqTr.BilinTestFormula
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.Periodic

namespace SourceInverse.Internal

open Freq

theorem integrable_expSq {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : Space => Real.exp (-(c * ‖ξ‖ ^ 2))) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Space) (b := (c : ℂ))
    (by simpa using hc) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Complex.norm_exp, zero_mul, add_zero, neg_mul, Complex.neg_re, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem memLp_of_expSq {F : Space → CSpace} (hF : AEStronglyMeasurable F volume) {K c : ℝ}
    (hc : 0 < c) (hb : ∀ ξ, ‖F ξ‖ ≤ K * Real.exp (-(c * ‖ξ‖ ^ 2))) :
    MemLp F 1 volume ∧ MemLp F 2 volume := by
  refine ⟨memLp_one_iff_integrable.2 (Integrable.mono' ((integrable_expSq hc).const_mul K) hF
    (Filter.Eventually.of_forall hb)), ?_⟩
  have hg : MemLp (fun ξ : Space => K * Real.exp (-(c * ‖ξ‖ ^ 2))) 2 volume := by
    have hm : AEStronglyMeasurable (fun ξ : Space => K * Real.exp (-(c * ‖ξ‖ ^ 2))) volume := by
      apply Continuous.aestronglyMeasurable; fun_prop
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine ((integrable_expSq (by positivity : 0 < 2 * c)).const_mul (K ^ 2)).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Real.norm_eq_abs, sq_abs, mul_pow]
    rw [sq (Real.exp _), ← Real.exp_add]
    ring_nf
  exact hg.of_le hF (Filter.Eventually.of_forall fun ξ => (hb ξ).trans (Real.le_norm_self _))

theorem norm_divFreeVec_le (ξ : Space) (c : Coef) : ‖divFreeVec ξ c‖ ≤ 2 * ‖c‖ := by
  rw [DivFreeProjection.Internal.divFreeVec_eq]
  have hl : ‖longitudinal ξ c‖ ≤ ‖c‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    simpa using mul_le_mul_of_nonneg_right (Internal.H1Consistency.norm_longitudinal_le ξ)
      (norm_nonneg c)
  calc ‖c - longitudinal ξ c‖ ≤ ‖c‖ + ‖longitudinal ξ c‖ := norm_sub_le _ _
    _ ≤ 2 * ‖c‖ := by linarith

theorem norm_freqTrVec_le (A : Space → Space) (ξ : Space) :
    ‖freqTrVec A ξ‖ ≤ ∫ x, ‖complexifyVec (A x)‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem heatFactor_eq {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Space) :
    Freq.heatFactor τ ξ = Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) := by
  unfold Freq.heatFactor
  rw [max_eq_left hτ]

theorem norm_source_le {τ : ℝ} (hτ : 0 ≤ τ) (A : Space → Space) (ξ : Space) :
    ‖Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ)‖ ≤
      (2 * ∫ x, ‖complexifyVec (A x)‖) * Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) := by
  rw [heatFactor_eq hτ, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  gcongr
  exact (norm_divFreeVec_le _ _).trans (by gcongr; exact norm_freqTrVec_le _ _)

theorem weight_le {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    2 * π * t * Real.exp (-((4 * π ^ 2 * τ) * t ^ 2)) ≤
      (1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) := by
  have hsplit : Real.exp (-((4 * π ^ 2 * τ) * t ^ 2)) =
      Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hx := Real.add_one_le_exp ((2 * π ^ 2 * τ) * t ^ 2)
  have key : 2 * π * t ≤ (1 + 2 / τ) * ((2 * π ^ 2 * τ) * t ^ 2 + 1) := by
    have h1 : (1 + 2 / τ) * ((2 * π ^ 2 * τ) * t ^ 2 + 1) =
        (2 * π ^ 2 * τ) * t ^ 2 + 1 + (2 * π * t) ^ 2 + 2 / τ := by
      field_simp; ring
    rw [h1]
    have : 0 ≤ 2 / τ := by positivity
    have : 0 ≤ (2 * π ^ 2 * τ) * t ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * π * t - 1)]
  have hb : 2 * π * t * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2)) ≤ 1 + 2 / τ := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    exact key.trans (mul_le_mul_of_nonneg_left hx (by positivity))
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

theorem norm_gradSource_le {τ : ℝ} (hτ : 0 < τ) (A : Space → Space) (j : Fin 3) (ξ : Space) :
    ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ))‖ ≤
      ((2 * ∫ x, ‖complexifyVec (A x)‖) * (1 + 2 / τ)) *
        Real.exp (-((2 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) := by
  have hs : ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ ≤ 2 * π * ‖ξ‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
    gcongr
    exact PiLp.norm_apply_le ξ j
  have hM : 0 ≤ 2 * ∫ x, ‖complexifyVec (A x)‖ := by
    have : 0 ≤ ∫ x, ‖complexifyVec (A x)‖ := integral_nonneg fun x => norm_nonneg _
    linarith
  rw [norm_smul]
  calc ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ * ‖Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ)‖
      ≤ (2 * π * ‖ξ‖) * ((2 * ∫ x, ‖complexifyVec (A x)‖) *
          Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) :=
        mul_le_mul hs (norm_source_le hτ.le A ξ) (norm_nonneg _) (by positivity)
    _ = (2 * ∫ x, ‖complexifyVec (A x)‖) *
          (2 * π * ‖ξ‖ * Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) := by ring
    _ ≤ (2 * ∫ x, ‖complexifyVec (A x)‖) *
          ((1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * ‖ξ‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (weight_le hτ _) hM
    _ = _ := by ring

theorem derivSymbol_smul (j : Fin 3) (ξ : Space) (z : CSpace) :
    derivSymbol j ξ • ((2 * π * ‖ξ‖) • z) = (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • z := by
  rcases eq_or_ne ξ 0 with rfl | h
  · simp [derivSymbol]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  unfold derivSymbol
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
  push_cast
  field_simp

theorem toPhys_ae (h3 : FreqTrInvL1L2) {x : L2C} {F : Space → CSpace}
    (hx : (x : Space → CSpace) =ᵐ[volume] F) (h1 : MemLp F 1 volume) :
    (toPhys x : Space → Space) =ᵐ[volume] fun y => realVec (∫ ξ, expChar y ξ • F ξ) := by
  have h2 : MemLp F 2 volume := (Lp.memLp x).ae_eq hx
  have hx' : x = toLpOrZero 2 F :=
    Lp.ext (hx.trans (Freq.Internal.BilinTestFormula.toLpOrZero_ae h2).symm)
  have hinv := h3 F h1 h2
  have hc := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure Space)) realVec
    (freqTrInvR x)
  filter_upwards [hc, hinv] with y e1 e2
  change (realVec.compLpL 2 volume (freqTrInvR x) : Space → Space) y = _
  rw [e1]
  change realVec ((freqTrL2.symm x : L2C) y) = _
  rw [hx', e2, Real.fourierInv_eq']
  congr 2
  funext ξ
  unfold expChar
  congr 2
  push_cast
  ring

end SourceInverse.Internal

open SourceInverse.Internal in
theorem r3ValueFormula_of (hF : HeatDivFreeFactor) (h1 : Freq.FieldOpRealized)
    (h2 : Freq.VelocityInvertsHalfSsp) (h3 : Freq.FreqTrInvL1L2) : R3ValueFormula := by
  intro b' τ hτ A hA
  obtain ⟨g, hgG, hhl⟩ := hF b' τ hτ A hA
  set G : Space → Freq.CSpace := fun ξ => Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec (⇑A) ξ) with hGdef
  have hGm : AEStronglyMeasurable G volume := (Lp.aestronglyMeasurable (g : Freq.L2C)).congr hgG
  have hG1 := (memLp_of_expSq hGm (by positivity : 0 < 4 * π ^ 2 * τ)
    (norm_source_le hτ.le (⇑A))).1
  refine ⟨?_, fun j => ?_⟩
  · filter_upwards [h2 g _ hhl, toPhys_ae h3 hgG hG1] with y e1 e2
    rw [e1, e2]
    rfl
  · set Gj : Space → Freq.CSpace := fun ξ => (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • G ξ with hGjdef
    have hGjm : AEStronglyMeasurable Gj volume := by
      exact (Continuous.aestronglyMeasurable
        (by fun_prop : Continuous fun ξ : Space => (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)))).smul hGm
    have hGj1 := (memLp_of_expSq hGjm (by positivity : 0 < 2 * π ^ 2 * τ)
      (norm_gradSource_le hτ (⇑A) j)).1
    have hx : (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
        ((Freq.heatDivFree τ A : Freq.X) : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume] Gj := by
      filter_upwards [Freq.Internal.BilinTestFormula.symbol_ae h1 (Freq.derivSymbol j)
        (Freq.Internal.BilinTestFormula.measurable_derivSymbol j)
        (Freq.Internal.BilinTestFormula.norm_derivSymbol_le j) _, hhl, hgG] with ξ e1 e2 e3
      rw [e1, e2, e3, derivSymbol_smul]
    filter_upwards [toPhys_ae h3 hx hGj1] with y e1
    change (Freq.toPhys (Freq.fieldOp id (fun ξ => Freq.cmul (Freq.derivSymbol j ξ))
      ((Freq.heatDivFree τ A : Freq.X) : Freq.L2C)) : Space → Space) y = _
    rw [e1]
    congr 2
    funext ξ
    simp only [hGjdef, hGdef, gradDensity, valueDensity]
    exact smul_comm _ _ _

end Breakdown.Periodic
