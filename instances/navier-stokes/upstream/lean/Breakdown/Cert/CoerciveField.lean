import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveFrequencySeminorm
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoercivePieceFieldCurlWeight

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal

namespace Field

def fieldModeSum {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ψ : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    ((Complex.I * (m.epsW (m.classOf ι) y : ℂ)
        * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re
      + (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re)

def fieldPairing {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ψ : ℝ → Space → Space) : ℝ :=
  (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y)) + fieldModeSum m v G ψ

abbrev periodMeasure : Measure (ℝ × Space) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

def fieldGradNorm (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  Real.sqrt (periodLIntegral (fun σ y => matSq (G σ y))).toReal

theorem testField_add {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) : IsPeriodicTestField (ψ₁ + ψ₂) := by
  obtain ⟨c₁, p₁, ⟨R₁, s₁⟩, d₁⟩ := h₁
  obtain ⟨c₂, p₂, ⟨R₂, s₂⟩, d₂⟩ := h₂
  have hd : ∀ {ψ : ℝ → Space → Space}, ContDiff ℝ ∞ (fun z : ℝ × Space => ψ z.1 z.2) →
      ∀ σ, Differentiable ℝ (ψ σ) := by
    intro ψ hψ σ
    have : ContDiff ℝ ∞ (fun y : Space => ψ σ y) := hψ.comp (contDiff_const.prodMk contDiff_id)
    exact this.differentiable (by simp)
  refine ⟨?_, ?_, ⟨max R₁ R₂, ?_⟩, ?_⟩
  · exact c₁.add c₂
  · intro σ y
    simp only [Pi.add_apply, p₁ σ y, p₂ σ y]
  · intro σ y hy
    simp only [Pi.add_apply, s₁ σ y (lt_of_le_of_lt (le_max_left _ _) hy),
      s₂ σ y (lt_of_le_of_lt (le_max_right _ _) hy), add_zero]
  · intro σ y
    have e : (ψ₁ + ψ₂) σ = ψ₁ σ + ψ₂ σ := rfl
    have d₁' := d₁ σ y
    have d₂' := d₂ σ y
    unfold divergenceAt at d₁' d₂' ⊢
    rw [e, fderiv_add (hd c₁ σ y) (hd c₂ σ y)]
    simp only [FunLike.coe_add, Pi.add_apply, PiLp.add_apply, Finset.sum_add_distrib]
    rw [d₁', d₂', add_zero]


theorem testField_smul (a : ℝ) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    IsPeriodicTestField (a • ψ) := by
  obtain ⟨c₁, p₁, ⟨R₁, s₁⟩, d₁⟩ := hψ
  have hd : ∀ σ, Differentiable ℝ (ψ σ) := by
    intro σ
    have : ContDiff ℝ ∞ (fun y : Space => ψ σ y) := c₁.comp (contDiff_const.prodMk contDiff_id)
    exact this.differentiable (by simp)
  refine ⟨?_, ?_, ⟨R₁, ?_⟩, ?_⟩
  · exact c₁.const_smul a
  · intro σ y
    simp only [Pi.smul_apply, p₁ σ y]
  · intro σ y hy
    simp only [Pi.smul_apply, s₁ σ y hy, smul_zero]
  · intro σ y
    have e : (a • ψ) σ = a • ψ σ := rfl
    have d₁' := d₁ σ y
    unfold divergenceAt at d₁' ⊢
    rw [e, fderiv_const_smul (hd σ y)]
    simp only [FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [d₁', mul_zero]


theorem frequencySeminormSq_lt_top_of_perturbation (hPars : ModeSquareSumHolds)
    (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    m.frequencySeminormSq P v < ⊤ := by
  obtain ⟨B, hB⟩ := hm.muW_decay
  obtain ⟨Br, hBr⟩ := hm.rate_bounded
  obtain ⟨c0⟩ : Nonempty C := ⟨m.classOf 0⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c0 0).1
  have hBr0 : 0 ≤ Br := (abs_nonneg _).trans (hBr c0 0)
  have hP := hm.period_pos
  set K := max (2 * Real.pi / P) Br with hK
  have hK0 : 0 ≤ K := le_max_of_le_right hBr0
  set wt : Space → ℝ := fun y => 2 * B / (1 + ‖y‖ ^ 2) with hwt
  have hden : ∀ y : Space, 0 < 1 + ‖y‖ ^ 2 := fun y => by positivity
  have hwt0 : ∀ y, 0 ≤ wt y := fun y => div_nonneg (by positivity) (hden y).le
  have hwtc : Continuous wt :=
    continuous_const.div (continuous_const.add (continuous_norm.pow 2)) (fun y => (hden y).ne')
  have hwtB : ∃ B', ∀ y, wt y ≤ B' ∧ ‖y‖ ^ 2 * wt y ≤ B' := by
    refine ⟨2 * B, fun y => ⟨?_, ?_⟩⟩
    · exact div_le_self (by positivity) (by nlinarith [sq_nonneg ‖y‖])
    · show ‖y‖ ^ 2 * (2 * B / (1 + ‖y‖ ^ 2)) ≤ 2 * B
      rw [mul_div_assoc', div_le_iff₀ (hden y)]
      nlinarith [sq_nonneg ‖y‖]
  have hfin := FrequencySeminorm.Internal.weightedFrequency_lt_top hPars hDer hRotM hv hP wt hwt0 hwtc hwtB
  have hpt : ∀ (ι : ℤ × ℤ) (y : Space),
      m.mu ι y * |m.dop P ι y| ≤ K * ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * wt y) := by
    intro ι y
    have hmu : m.mu ι y ≤ wt y := by
      have h1 := (hB (m.classOf ι) y).2.1
      show |m.muW (m.classOf ι) y| ≤ 2 * B / (1 + ‖y‖ ^ 2)
      rw [le_div_iff₀ (hden y)]
      nlinarith [(hB (m.classOf ι) y).1]
    have hdop : |m.dop P ι y| ≤ K * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) := by
      show |2 * Real.pi * ι.1 / P + ι.2 * m.rate (m.classOf ι) y| ≤ K * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|)
      have hr := hBr (m.classOf ι) y
      have e1 : |2 * Real.pi * (ι.1 : ℝ) / P| = 2 * Real.pi / P * |(ι.1 : ℝ)| := by
        rw [show 2 * Real.pi * (ι.1 : ℝ) / P = 2 * Real.pi / P * ι.1 by ring, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / P)]
      have e2 : |(ι.2 : ℝ) * m.rate (m.classOf ι) y| ≤ |(ι.2 : ℝ)| * Br := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      have k1 : 2 * Real.pi / P * |(ι.1 : ℝ)| ≤ K * |(ι.1 : ℝ)| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      have k2 : |(ι.2 : ℝ)| * Br ≤ K * |(ι.2 : ℝ)| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
      calc _ ≤ |2 * Real.pi * (ι.1 : ℝ) / P| + |(ι.2 : ℝ) * m.rate (m.classOf ι) y| := abs_add_le _ _
        _ ≤ _ := by rw [e1]; linarith
    calc m.mu ι y * |m.dop P ι y| ≤ wt y * (K * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|)) :=
          mul_le_mul hmu hdop (abs_nonneg _) (hwt0 y)
      _ = _ := by ring
  unfold ModeWeights.frequencySeminormSq
  calc _ ≤ ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal K *
        ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * wt y * cnormSq (modeVel ι v σ y)) := by
        refine ENNReal.tsum_le_tsum (fun ι => lintegral_mono (fun σ => lintegral_mono (fun y => ?_)))
        rw [← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        have hc := Internal.FieldModes.cnormSq_nonneg (modeVel ι v σ y)
        have := mul_le_mul_of_nonneg_right (hpt ι y) hc
        calc _ ≤ K * ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * wt y) * cnormSq (modeVel ι v σ y) := this
          _ = _ := by ring
    _ = ENNReal.ofReal K * ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * wt y * cnormSq (modeVel ι v σ y)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun ι => ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr (fun σ => ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem axialRot_comp_continuous {α : Type*} [TopologicalSpace α] {f : α → ℝ} {g : α → Space}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => axialRot (f a) (g a)) := by
  unfold axialRot
  fun_prop

theorem axialRot_add (φ : ℝ) (y₁ y₂ : Space) : axialRot φ (y₁ + y₂) = axialRot φ y₁ + axialRot φ y₂ := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem modeAverage_add {β : Type*} (ι : ℤ × ℤ) (f g : ℝ → ℝ → β → ℝ) (b : β)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2 b)) (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2 b)) :
    modeAverage ι (fun τ φ b => f τ φ b + g τ φ b) b = modeAverage ι f b + modeAverage ι g b := by
  unfold modeAverage
  have hE : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) := by fun_prop
  have hF : Continuous (Function.uncurry (fun τ φ : ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ))) :=
    hE.mul (Complex.continuous_ofReal.comp hf)
  have hG : Continuous (Function.uncurry (fun τ φ : ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g τ φ b : ℝ) : ℂ))) :=
    hE.mul (Complex.continuous_ofReal.comp hg)
  have hin : ∀ τ : ℝ, (∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b + g τ φ b : ℝ) : ℂ)) =
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ))
      + ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g τ φ b : ℝ) : ℂ) := by
    intro τ
    rw [← intervalIntegral.integral_add]
    · congr 1
      funext φ
      push_cast
      ring
    · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simp_rw [hin]
  rw [intervalIntegral.integral_add, mul_add]
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _).intervalIntegrable _ _
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG _ _).intervalIntegrable _ _

theorem mode_integrand_continuous {X : ℝ → Space → Space} (h : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (σ : ℝ) (y : Space) (i : Fin 3) :
    Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (X (σ + p.1) (axialRot p.2 y)) i) := by
  have h1 : Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
    (continuous_const.add continuous_fst).prodMk
      (axialRot_comp_continuous continuous_snd continuous_const)
  have h2 : Continuous (fun p : ℝ × ℝ => X (σ + p.1) (axialRot p.2 y)) := h.comp h1
  have h3 : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (X (σ + p.1) (axialRot p.2 y))) :=
    axialRot_comp_continuous continuous_snd.neg h2
  exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp h3

theorem modeVel_add {X₁ X₂ : ℝ → Space → Space} (h₁ : Continuous (fun z : ℝ × Space => X₁ z.1 z.2))
    (h₂ : Continuous (fun z : ℝ × Space => X₂ z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (X₁ + X₂) σ y = modeVel ι X₁ σ y + modeVel ι X₂ σ y := by
  funext i
  unfold modeVel
  rw [Pi.add_apply, ← modeAverage_add _ _ _ _ (mode_integrand_continuous h₁ σ y i)
    (mode_integrand_continuous h₂ σ y i)]
  congr 1
  funext τ φ b
  simp only [Pi.add_apply, axialRot_add, PiLp.add_apply]

theorem gradField_continuous {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Continuous (fun z : ℝ × Space => gradField ψ z.1 z.2) := by
  have hpart : ∀ σ (y : Space), fderiv ℝ (ψ σ) y =
      (fderiv ℝ (fun z : ℝ × Space => ψ z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    intro σ y
    have h1 : HasFDerivAt (fun x : Space => ((σ, x) : ℝ × Space)) (ContinuousLinearMap.inr ℝ ℝ Space) y :=
      hasFDerivAt_prodMk_right σ y
    have h2 : HasFDerivAt (fun z : ℝ × Space => ψ z.1 z.2)
        (fderiv ℝ (fun z : ℝ × Space => ψ z.1 z.2) (σ, y)) (σ, y) :=
      ((hψ.1.differentiable (by simp)) (σ, y)).hasFDerivAt
    exact (h2.comp y h1).fderiv
  have hc : Continuous (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => ψ z.1 z.2) z) :=
    hψ.1.continuous_fderiv (by simp)
  have e : (fun z : ℝ × Space => gradField ψ z.1 z.2) =
      fun z => (fderiv ℝ (fun z : ℝ × Space => ψ z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact hpart z.1 z.2
  rw [e]
  exact hc.clm_comp continuous_const

theorem gradField_add {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) : gradField (ψ₁ + ψ₂) = gradField ψ₁ + gradField ψ₂ := by
  funext σ y
  have hd : ∀ {ψ : ℝ → Space → Space}, IsPeriodicTestField ψ → Differentiable ℝ (ψ σ) := fun hψ =>
    (hψ.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  show fderiv ℝ (ψ₁ σ + ψ₂ σ) y = fderiv ℝ (ψ₁ σ) y + fderiv ℝ (ψ₂ σ) y
  exact fderiv_add (hd h₁ y) (hd h₂ y)

theorem modeGrad_add {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)}
    (h₁ : Continuous (fun z : ℝ × Space => G₁ z.1 z.2)) (h₂ : Continuous (fun z : ℝ × Space => G₂ z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeGrad ι (G₁ + G₂) σ y = modeGrad ι G₁ σ y + modeGrad ι G₂ σ y := by
  have hc : ∀ {G : ℝ → Space → (Space →L[ℝ] Space)}, Continuous (fun z : ℝ × Space => G z.1 z.2) →
      ∀ ij : Fin 3 × Fin 3, Continuous (fun p : ℝ × ℝ =>
        axialRot (-p.2) (G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector ij.2))) ij.1) := by
    intro G hG ij
    have h1 : Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
      (continuous_const.add continuous_fst).prodMk
        (axialRot_comp_continuous continuous_snd continuous_const)
    have h2 : Continuous (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector ij.2))) :=
      (hG.comp h1).clm_apply (axialRot_comp_continuous continuous_snd continuous_const)
    have h3 := axialRot_comp_continuous continuous_snd.neg h2
    exact (EuclideanSpace.proj ij.1 : Space →L[ℝ] ℝ).continuous.comp h3
  funext ij
  unfold modeGrad
  rw [Pi.add_apply, ← modeAverage_add _ _ _ _ (hc h₁ ij) (hc h₂ ij)]
  congr 1
  funext τ φ b
  simp only [Pi.add_apply, FunLike.coe_add, axialRot_add, PiLp.add_apply]

theorem curlOfGrad_add (g₁ g₂ : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (g₁ + g₂) = curlOfGrad g₁ + curlOfGrad g₂ := by
  funext i
  simp only [curlOfGrad, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cdot_add_right (x z₁ z₂ : Fin 3 → ℂ) : cdot x (z₁ + z₂) = cdot x z₁ + cdot x z₂ := by
  simp only [cdot, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

def termEps {C : Type} (m : ModeWeights C) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ψ : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * (m.epsW (m.classOf ι) y : ℂ)
    * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re

def termMu {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space)
    (ψ : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re

theorem fieldModeSum_eq {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ψ : ℝ → Space → Space) :
    fieldModeSum m v G ψ = ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      (termEps m G ψ ι σ y + termMu m v ψ ι σ y) := rfl

theorem termEps_add {C : Type} (m : ModeWeights C) (G : ℝ → Space → (Space →L[ℝ] Space))
    {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁) (h₂ : IsPeriodicTestField ψ₂)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    termEps m G (ψ₁ + ψ₂) ι σ y = termEps m G ψ₁ ι σ y + termEps m G ψ₂ ι σ y := by
  unfold termEps
  rw [gradField_add h₁ h₂, modeGrad_add (gradField_continuous h₁) (gradField_continuous h₂),
    curlOfGrad_add, cdot_add_right, mul_add, Complex.add_re]

theorem termMu_add {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space)
    {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁) (h₂ : IsPeriodicTestField ψ₂)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    termMu m v (ψ₁ + ψ₂) ι σ y = termMu m v ψ₁ ι σ y + termMu m v ψ₂ ι σ y := by
  unfold termMu
  rw [modeVel_add h₁.1.continuous h₂.1.continuous, cdot_add_right, mul_add, Complex.add_re]

theorem epsW_continuous {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (c : C) :
    Continuous (m.epsW c) := by
  obtain ⟨K, hK⟩ := hm.epsW_increment c
  exact hK.continuous

theorem muW_continuous {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (c : C) :
    Continuous (m.muW c) := by
  obtain ⟨K, hK⟩ := hm.muW_increment c
  exact hK.continuous

theorem termMu_ballPart {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space) {ψ : ℝ → Space → Space}
    {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → ψ σ y = 0) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    termMu m v ψ ι σ y = termMu m (FieldModes.ballPart R v) ψ ι σ y := by
  unfold termMu
  by_cases hy : ‖y‖ ≤ R
  · rw [FieldModes.modeVel_ballPart v ι σ hy]
  · rw [FieldModes.modeVel_eq_zero hs ι σ (lt_of_not_ge hy)]
    simp [cdot]

theorem gradField_matSq_lt_top {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    periodLIntegral (fun σ y => matSq (gradField ψ σ y)) < ⊤ := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  have hc : Continuous (fun z : ℝ × Space => matSq (gradField ψ z.1 z.2)) := by
    unfold matSq
    exact continuous_finsetSum _ (fun i _ => (((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp
      (gradField_continuous hψ)).norm.pow 2))
  refine FieldModes.periodLIntegral_lt_top_of_support hc (R := R) (fun σ y hy => ?_)
  rw [FieldModes.gradField_eq_zero sR σ y hy]
  simp [matSq]

theorem termEps_aestronglyMeasurable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C}
    {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => termEps m G ψ ι z.1 z.2) periodMeasure := by
  have he := epsW_continuous hm (m.classOf ι)
  have hΦ : Continuous (fun q : Space × (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) =>
      (Complex.I * (m.epsW (m.classOf ι) q.1 : ℂ) * cdot (curlOfGrad q.2.1) (curlOfGrad q.2.2)).re) := by
    unfold cdot curlOfGrad
    fun_prop
  have hq : AEMeasurable (fun z : ℝ × Space =>
      (z.2, modeGrad ι G z.1 z.2, modeGrad ι (gradField ψ) z.1 z.2)) periodMeasure :=
    measurable_snd.aemeasurable.prodMk ((FieldModes.aemeasurable_modeGrad hG ι).prodMk
      (FieldModes.aemeasurable_modeGrad (gradField_continuous hψ).aestronglyMeasurable ι))
  exact (hΦ.measurable.comp_aemeasurable hq).aestronglyMeasurable

theorem termEps_integrable (hPars : ModeSquareSumHolds) {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => termEps m G ψ ι z.1 z.2) periodMeasure := by
  have hA := FieldModes.integrable_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient
    hv.gradient_finite ι
  have hB := FieldModes.integrable_cnormSq_modeGrad hPars (gradField_continuous hψ).aestronglyMeasurable
    (FieldModes.gradField_periodic hψ.2.1) (gradField_matSq_lt_top hψ) ι
  refine Integrable.mono' ((hA.add hB).const_mul epsSup)
    (termEps_aestronglyMeasurable hm hv.measurable_gradient hψ ι) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (FieldModes.abs_curlTerm_le _ _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hm.epsW_le _ _)
    (add_nonneg (FieldModes.cnormSq_nonneg _) (FieldModes.cnormSq_nonneg _))

theorem termMu_aestronglyMeasurable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C}
    {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {U : ℝ → Space → Space}
    (hU : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) volume) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => termMu m U ψ ι z.1 z.2) periodMeasure := by
  have he := muW_continuous hm (m.classOf ι)
  have hΦ : Continuous (fun q : Space × (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      (Complex.I * (m.muW (m.classOf ι) q.1 : ℂ) * cdot q.2.1 q.2.2).re) := by
    unfold cdot
    fun_prop
  have hq : AEMeasurable (fun z : ℝ × Space =>
      (z.2, modeVel ι U z.1 z.2, modeVel ι ψ z.1 z.2)) periodMeasure :=
    measurable_snd.aemeasurable.prodMk ((FieldModes.aemeasurable_modeVel hU ι).prodMk
      (FieldModes.aemeasurable_modeVel hψ.1.continuous.aestronglyMeasurable ι))
  exact (hΦ.measurable.comp_aemeasurable hq).aestronglyMeasurable

theorem termMu_integrable (hPars : ModeSquareSumHolds) (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => termMu m v ψ ι z.1 z.2) periodMeasure := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hU := FieldModes.isSquareField_ballPart hLoc hv R
  have hX := FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  have hA := FieldModes.integrable_cnormSq_modeVel hPars hU ι
  have hA' := FieldModes.integrable_cnormSq_modeVel hPars hX ι
  have hI : Integrable (fun z : ℝ × Space => termMu m (FieldModes.ballPart R v) ψ ι z.1 z.2)
      periodMeasure := by
    refine Integrable.mono' (((hA.add hA').div_const 2).const_mul B)
      (termMu_aestronglyMeasurable hm hU.1 hψ ι) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (FieldModes.abs_velTerm_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hB _ _).1
      (div_nonneg (add_nonneg (FieldModes.cnormSq_nonneg _) (FieldModes.cnormSq_nonneg _)) zero_le_two)
  refine hI.congr (ae_of_all _ fun z => ?_)
  exact (termMu_ballPart m v sR ι z.1 z.2).symm

theorem fieldModeTerm_integrable (hPars : ModeSquareSumHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => termEps m G ψ ι z.1 z.2 + termMu m v ψ ι z.1 z.2) periodMeasure :=
  (termEps_integrable hPars hm hv hψ ι).add (termMu_integrable hPars hLoc hm hv hψ ι)

theorem termEps_summable (hPars : ModeSquareSumHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Summable (fun ι : ℤ × ℤ => ∫ z, termEps m G ψ ι z.1 z.2 ∂periodMeasure) := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hU := FieldModes.isSquareField_ballPart hLoc hv R
  have hX := FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  have hψg : AEStronglyMeasurable (fun z : ℝ × Space => gradField ψ z.1 z.2) volume :=
    (gradField_continuous hψ).aestronglyMeasurable
  have hψgp := FieldModes.gradField_periodic hψ.2.1
  have hψg2 := gradField_matSq_lt_top hψ
  refine Summable.of_norm_bounded ((
    (FieldModes.summable_integral_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient
      hv.gradient_finite).add
    (FieldModes.summable_integral_cnormSq_modeGrad hPars hψg hψgp hψg2)).mul_left epsSup) (fun ι => ?_)
  have hA := FieldModes.integrable_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient
    hv.gradient_finite ι
  have hA' := FieldModes.integrable_cnormSq_modeGrad hPars hψg hψgp hψg2 ι
  refine (norm_integral_le_of_norm_le ((hA.add hA').const_mul epsSup) (ae_of_all _ fun z => ?_)).trans
    (le_of_eq ?_)
  · rw [Real.norm_eq_abs]
    refine (FieldModes.abs_curlTerm_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hm.epsW_le _ _)
      (add_nonneg (FieldModes.cnormSq_nonneg _) (FieldModes.cnormSq_nonneg _))
  · rw [integral_const_mul]
    congr 1
    exact integral_add hA hA'
theorem termMu_summable (hPars : ModeSquareSumHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Summable (fun ι : ℤ × ℤ => ∫ z, termMu m v ψ ι z.1 z.2 ∂periodMeasure) := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hU := FieldModes.isSquareField_ballPart hLoc hv R
  have hX := FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  have hψg : AEStronglyMeasurable (fun z : ℝ × Space => gradField ψ z.1 z.2) volume :=
    (gradField_continuous hψ).aestronglyMeasurable
  have hψgp := FieldModes.gradField_periodic hψ.2.1
  have hψg2 := gradField_matSq_lt_top hψ
  refine Summable.of_norm_bounded ((
    ((FieldModes.summable_integral_cnormSq_modeVel hPars hU).add
      (FieldModes.summable_integral_cnormSq_modeVel hPars hX)).div_const 2).mul_left B) (fun ι => ?_)
  have hA := FieldModes.integrable_cnormSq_modeVel hPars hU ι
  have hA' := FieldModes.integrable_cnormSq_modeVel hPars hX ι
  refine (norm_integral_le_of_norm_le (((hA.add hA').div_const 2).const_mul B)
    (ae_of_all _ fun z => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, termMu_ballPart m v sR ι z.1 z.2]
    refine (FieldModes.abs_velTerm_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hB _ _).1
      (div_nonneg (add_nonneg (FieldModes.cnormSq_nonneg _) (FieldModes.cnormSq_nonneg _)) zero_le_two)
  · rw [integral_const_mul, integral_div]
    congr 2
    exact integral_add hA hA'
theorem fieldModeTerm_summable (hPars : ModeSquareSumHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      (termEps m G ψ ι σ y + termMu m v ψ ι σ y)) := by
  have hSe := termEps_summable hPars hLoc hm hv hψ
  have hSm := termMu_summable hPars hLoc hm hv hψ
  refine (hSe.add hSm).congr (fun ι => ?_)
  have hIe := termEps_integrable hPars hm hv hψ ι
  have hIm := termMu_integrable hPars hLoc hm hv hψ ι
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (termEps m G ψ ι σ y + termMu m v ψ ι σ y)) =
      ∫ z, (termEps m G ψ ι z.1 z.2 + termMu m v ψ ι z.1 z.2) ∂periodMeasure :=
    (integral_prod _ (hIe.add hIm)).symm
  rw [e1]
  exact (integral_add hIe hIm).symm

theorem fieldModeSum_add (hPars : ModeSquareSumHolds) (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ₁ ψ₂ : ℝ → Space → Space}
    (h₁ : IsPeriodicTestField ψ₁) (h₂ : IsPeriodicTestField ψ₂) :
    fieldModeSum m v G (ψ₁ + ψ₂) = fieldModeSum m v G ψ₁ + fieldModeSum m v G ψ₂ := by
  rw [fieldModeSum_eq, fieldModeSum_eq, fieldModeSum_eq]
  have key : ∀ ι, (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      (termEps m G (ψ₁ + ψ₂) ι σ y + termMu m v (ψ₁ + ψ₂) ι σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (termEps m G ψ₁ ι σ y + termMu m v ψ₁ ι σ y)) +
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (termEps m G ψ₂ ι σ y + termMu m v ψ₂ ι σ y) := by
    intro ι
    have i1 := fieldModeTerm_integrable hPars hLoc hm hv h₁ ι
    have i2 := fieldModeTerm_integrable hPars hLoc hm hv h₂ ι
    have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        (termEps m G (ψ₁ + ψ₂) ι σ y + termMu m v (ψ₁ + ψ₂) ι σ y)) =
        ∫ z, ((termEps m G ψ₁ ι z.1 z.2 + termMu m v ψ₁ ι z.1 z.2)
          + (termEps m G ψ₂ ι z.1 z.2 + termMu m v ψ₂ ι z.1 z.2)) ∂periodMeasure := by
      refine Eq.trans ?_ (integral_prod _ (i1.add i2)).symm
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [Pi.add_apply]
      rw [termEps_add m G h₁ h₂, termMu_add m v h₁ h₂]
      ring
    have e2 : ∫ z, ((termEps m G ψ₁ ι z.1 z.2 + termMu m v ψ₁ ι z.1 z.2)
          + (termEps m G ψ₂ ι z.1 z.2 + termMu m v ψ₂ ι z.1 z.2)) ∂periodMeasure =
        (∫ z, (termEps m G ψ₁ ι z.1 z.2 + termMu m v ψ₁ ι z.1 z.2) ∂periodMeasure)
          + ∫ z, (termEps m G ψ₂ ι z.1 z.2 + termMu m v ψ₂ ι z.1 z.2) ∂periodMeasure :=
      integral_add i1 i2
    have e3 : ∫ z, (termEps m G ψ₁ ι z.1 z.2 + termMu m v ψ₁ ι z.1 z.2) ∂periodMeasure =
        ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (termEps m G ψ₁ ι σ y + termMu m v ψ₁ ι σ y) :=
      integral_prod _ i1
    have e4 : ∫ z, (termEps m G ψ₂ ι z.1 z.2 + termMu m v ψ₂ ι z.1 z.2) ∂periodMeasure =
        ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (termEps m G ψ₂ ι σ y + termMu m v ψ₂ ι σ y) :=
      integral_prod _ i2
    rw [e1, e2, e3, e4]
  simp_rw [key]
  exact (fieldModeTerm_summable hPars hLoc hm hv h₁).tsum_add
    (fieldModeTerm_summable hPars hLoc hm hv h₂)

theorem axialRot_smul (φ a : ℝ) (y : Space) : axialRot φ (a • y) = a • axialRot φ y := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem modeAverage_const_mul {β : Type*} (ι : ℤ × ℤ) (a : ℝ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι (fun τ φ b => a * f τ φ b) b = (a : ℂ) * modeAverage ι f b := by
  unfold modeAverage
  simp_rw [Complex.ofReal_mul, mul_left_comm _ (a : ℂ), intervalIntegral.integral_const_mul]
  ring

theorem modeVel_smul (ι : ℤ × ℤ) (a : ℝ) (X : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    modeVel ι (a • X) σ y = fun i => (a : ℂ) * modeVel ι X σ y i := by
  funext i
  unfold modeVel
  rw [← modeAverage_const_mul]
  congr 1
  funext τ φ b
  simp only [Pi.smul_apply, axialRot_smul, PiLp.smul_apply, smul_eq_mul]

theorem modeGrad_smul (ι : ℤ × ℤ) (a : ℝ) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    modeGrad ι (a • G) σ y = fun ij => (a : ℂ) * modeGrad ι G σ y ij := by
  funext ij
  unfold modeGrad
  rw [← modeAverage_const_mul]
  congr 1
  funext τ φ b
  simp only [Pi.smul_apply, FunLike.coe_smul, axialRot_smul, PiLp.smul_apply, smul_eq_mul]

theorem gradField_smul {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (a : ℝ) :
    gradField (a • ψ) = a • gradField ψ := by
  funext σ y
  have hd : Differentiable ℝ (ψ σ) :=
    (hψ.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  show fderiv ℝ (a • ψ σ) y = a • fderiv ℝ (ψ σ) y
  exact fderiv_const_smul (hd y) a

theorem curlOfGrad_smul (a : ℝ) (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (fun ij => (a : ℂ) * g ij) = fun i => (a : ℂ) * curlOfGrad g i := by
  funext i
  simp only [curlOfGrad, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem cdot_smul_right (a : ℝ) (x z : Fin 3 → ℂ) :
    cdot x (fun i => (a : ℂ) * z i) = (a : ℂ) * cdot x z := by
  simp only [cdot, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem fieldModeSum_smul {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (a : ℝ) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    fieldModeSum m v G (a • ψ) = a * fieldModeSum m v G ψ := by
  unfold fieldModeSum
  rw [← tsum_mul_left]
  refine tsum_congr (fun ι => ?_)
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  simp only
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [gradField_smul hψ, modeGrad_smul, curlOfGrad_smul, cdot_smul_right, modeVel_smul, cdot_smul_right]
  have e1 : ∀ c : ℂ, (Complex.I * (m.epsW (m.classOf ι) y : ℂ) * ((a : ℂ) * c)).re =
      a * (Complex.I * (m.epsW (m.classOf ι) y : ℂ) * c).re := by
    intro c
    rw [show Complex.I * (m.epsW (m.classOf ι) y : ℂ) * ((a : ℂ) * c) =
      (a : ℂ) * (Complex.I * (m.epsW (m.classOf ι) y : ℂ) * c) by ring, Complex.re_ofReal_mul]
  have e2 : ∀ c : ℂ, (Complex.I * (m.muW (m.classOf ι) y : ℂ) * ((a : ℂ) * c)).re =
      a * (Complex.I * (m.muW (m.classOf ι) y : ℂ) * c).re := by
    intro c
    rw [show Complex.I * (m.muW (m.classOf ι) y : ℂ) * ((a : ℂ) * c) =
      (a : ℂ) * (Complex.I * (m.muW (m.classOf ι) y : ℂ) * c) by ring, Complex.re_ofReal_mul]
  rw [e1, e2]
  ring

theorem testField_aestronglyMeasurable {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    AEStronglyMeasurable (fun z : ℝ × Space => ψ z.1 z.2) volume := by
  exact hψ.1.continuous.aestronglyMeasurable

theorem sq_lt_top_of_support {F : ℝ → Space → Space} (hc : Continuous (fun z : ℝ × Space => F z.1 z.2))
    {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → F σ y = 0) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall 0 R)
  obtain ⟨Cst, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ y, ENNReal.ofReal (‖F σ y‖ ^ 2) ≤
      (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal (Cst ^ 2)) y := by
    intro σ hσ y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      have := hC (σ, y) ⟨hσ, hy⟩
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    · rw [Set.indicator_of_notMem hy]
      have : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      simp [hs σ y this]
  unfold periodLIntegral
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Cst ^ 2) * volume (Metric.closedBall (0 : Space) R) := by
        refine setLIntegral_mono' measurableSet_Icc (fun σ hσ => ?_)
        calc ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2)
            ≤ ∫⁻ y, (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal (Cst ^ 2)) y :=
              lintegral_mono (hpt σ hσ)
          _ = _ := lintegral_indicator_const measurableSet_closedBall _
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
          (by simp)

theorem testField_sq_lt_top {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2) < ⊤ := by
  obtain ⟨c₁, _, ⟨R, sR⟩, _⟩ := hψ
  exact sq_lt_top_of_support c₁.continuous sR

theorem period_measure_eq :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
      (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem periodLIntegral_eq_prod {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
  (lintegral_prod _ hf.ennreal_ofReal).symm

theorem secondDerivTrace_continuous :
    Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace A) := by
  unfold secondDerivTrace
  refine continuous_finsetSum _ (fun j _ => ?_)
  exact (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous

theorem matSq_continuous : Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  exact continuous_finsetSum _ (fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm.pow 2))

theorem matSq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem pairing_integrable {F M : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hM : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hM2 : periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (M z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have hFμ : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) μ := by
    rw [hμ, period_measure_eq]; exact hF.restrict
  have hMμ : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) μ := by
    rw [hμ, period_measure_eq]; exact hM.restrict
  have hsq : ∀ (u : ℝ → Space → Space), AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) μ →
      periodLIntegral (fun σ y => ‖u σ y‖ ^ 2) < ⊤ → Integrable (fun z : ℝ × Space => ‖u z.1 z.2‖ ^ 2) μ := by
    intro u hu hfin
    rw [periodLIntegral_eq_prod (f := fun σ y => ‖u σ y‖ ^ 2) (hu.norm.pow 2).aemeasurable] at hfin
    refine (integrable_toReal_of_lintegral_ne_top (hu.norm.pow 2).aemeasurable.ennreal_ofReal
      hfin.ne).congr ?_
    exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))
  have hFi := hsq F hFμ hF2
  have hMi := hsq M hMμ hM2
  refine Integrable.mono' ((hFi.add hMi).div_const 2) (hFμ.inner hMμ) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖F z.1 z.2‖ - ‖M z.1 z.2‖)]

theorem testField_zero : IsPeriodicTestField (0 : ℝ → Space → Space) := by
  refine ⟨contDiff_const, fun σ y => rfl, ⟨0, fun σ y _ => rfl⟩, fun σ y => ?_⟩
  have e : (0 : ℝ → Space → Space) σ = fun _ => 0 := rfl
  unfold divergenceAt
  rw [e]
  simp

theorem memLp_of_period {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure := by
  have hFμ : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) periodMeasure := by
    rw [periodMeasure, period_measure_eq]; exact hF.restrict
  rw [memLp_two_iff_integrable_sq_norm hFμ]
  rw [periodLIntegral_eq_prod (f := fun σ y => ‖F σ y‖ ^ 2) (hFμ.norm.pow 2).aemeasurable] at hF2
  refine (integrable_toReal_of_lintegral_ne_top (hFμ.norm.pow 2).aemeasurable.ennreal_ofReal
    hF2.ne).congr ?_
  exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))

theorem period_lt_top_of_memLp {F : ℝ → Space → Space}
    (hF : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ := by
  rw [periodLIntegral_eq_prod (f := fun σ y => ‖F σ y‖ ^ 2) (hF.1.norm.pow 2).aemeasurable]
  exact ((memLp_two_iff_integrable_sq_norm hF.1).1 hF).lintegral_lt_top

theorem inner_toLp {f g : ℝ × Space → Space} (hf : MemLp f 2 periodMeasure)
    (hg : MemLp g 2 periodMeasure) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ z, inner ℝ (f z) (g z) ∂periodMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {f g : ℝ × Space → Space} (hf : MemLp f 2 periodMeasure)
    (hg : MemLp g 2 periodMeasure) :
    Integrable (fun z => inner ℝ (f z) (g z)) periodMeasure := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2]

theorem norm_toLp_eq_periodNorm {F : ℝ → Space → Space}
    (hF : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure) :
    ‖hF.toLp (fun z : ℝ × Space => F z.1 z.2)‖ = periodNorm F := by
  have h1 : ‖hF.toLp (fun z : ℝ × Space => F z.1 z.2)‖ ^ 2 = ∫ z, ‖F z.1 z.2‖ ^ 2 ∂periodMeasure := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    simp only [real_inner_self_eq_norm_sq]
  have h2 : ∫ z, ‖F z.1 z.2‖ ^ 2 ∂periodMeasure = (periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _) (hF.1.norm.pow 2),
      periodLIntegral_eq_prod (f := fun σ y => ‖F σ y‖ ^ 2) (hF.1.norm.pow 2).aemeasurable]
  unfold periodNorm
  rw [← h2, ← h1, Real.sqrt_sq (norm_nonneg _)]

theorem potential_gradient_memLp {q : ℝ → Space → ℝ} (hq : IsPeriodicTestPotential q) :
    MemLp (fun z : ℝ × Space => gradientAt (q z.1) z.2) 2 periodMeasure := by
  obtain ⟨c₁, _, ⟨R, sR⟩⟩ := hq
  have hpart : ∀ σ (y v : Space), fderiv ℝ (q σ) y v =
      fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) (σ, y) (0, v) := by
    intro σ y v
    have h1 : HasFDerivAt (fun x : Space => ((σ, x) : ℝ × Space))
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
      (hasFDerivAt_const σ y).prodMk (hasFDerivAt_id y)
    have h2 : HasFDerivAt (fun z : ℝ × Space => q z.1 z.2)
        (fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) (σ, y)) (σ, y) :=
      ((c₁.differentiable (by simp)) (σ, y)).hasFDerivAt
    have h3 := h2.comp y h1
    rw [show q σ = (fun z : ℝ × Space => q z.1 z.2) ∘ (fun x : Space => ((σ, x) : ℝ × Space)) from rfl,
      h3.fderiv]
    simp
  have hc : Continuous (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z) :=
    c₁.continuous_fderiv (by simp)
  have hcont : Continuous (fun z : ℝ × Space => gradientAt (q z.1) z.2) := by
    unfold gradientAt
    refine continuous_finsetSum _ (fun i _ => ?_)
    have e : (fun z : ℝ × Space => fderiv ℝ (q z.1) z.2 (unitVector i) • unitVector i) =
        fun z => fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z (0, unitVector i) • unitVector i := by
      funext z
      rw [hpart z.1 z.2]
    rw [e]
    exact (hc.clm_apply continuous_const).smul continuous_const
  have hsupp : ∀ σ y, R < ‖y‖ → gradientAt (q σ) y = 0 := by
    intro σ y hy
    have hev : q σ =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
      exact sR σ x hx
    unfold gradientAt
    rw [hev.fderiv_eq]
    simp
  exact memLp_of_period hcont.aestronglyMeasurable (sq_lt_top_of_support hcont hsupp)

theorem gradient_inner_testField {ψ : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (hψ : IsPeriodicTestField ψ) (hq : IsPeriodicTestPotential q) :
    ∫ z, inner ℝ (gradientAt (q z.1) z.2) (ψ z.1 z.2) ∂periodMeasure = 0 := by
  have hint := integrable_inner_of_memLp (potential_gradient_memLp hq)
    (memLp_of_period (testField_aestronglyMeasurable hψ) (testField_sq_lt_top hψ))
  obtain ⟨c₁, _, ⟨R, sR⟩, d₁⟩ := hψ
  obtain ⟨c₂, _, ⟨R', sR'⟩⟩ := hq
  rw [integral_prod _ hint]
  refine (integral_congr_ae (ae_of_all _ fun σ => ?_)).trans (integral_zero _ _)
  show ∫ y, inner ℝ (gradientAt (q σ) y) (ψ σ y) = 0
  have hψs : ContDiff ℝ ∞ (ψ σ) := c₁.comp (contDiff_const.prodMk contDiff_id)
  have hqs : ContDiff ℝ ∞ (q σ) := c₂.comp (contDiff_const.prodMk contDiff_id)
  have hψd : Differentiable ℝ (ψ σ) := hψs.differentiable (by simp)
  have hqd : Differentiable ℝ (q σ) := hqs.differentiable (by simp)
  set f : Fin 3 → Space → ℝ := fun i y => ψ σ y i with hf
  have hfd : ∀ i, Differentiable ℝ (f i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).differentiable.comp hψd
  have hff : ∀ i y v, fderiv ℝ (f i) y v = fderiv ℝ (ψ σ) y v i := by
    intro i y v
    have h := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hψd y).hasFDerivAt).fderiv
    have e : f i = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ ψ σ := rfl
    rw [e, h]
    simp
  have hfc : ∀ i, ContDiff ℝ ∞ (f i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hψs
  have hfsupp : ∀ i, HasCompactSupport (f i) := fun i =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) (fun y hy => by
      have : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      simp [hf, sR σ y this])
  have hqsupp : HasCompactSupport (q σ) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R') (fun y hy => by
      have : R' < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      exact sR' σ y this)
  have hpt : ∀ y, inner ℝ (gradientAt (q σ) y) (ψ σ y) =
      ∑ i, f i y * fderiv ℝ (q σ) y (unitVector i) := by
    intro y
    unfold gradientAt
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left]
    simp [hf, mul_comm]
  have hcontf' : ∀ i (v : Space), Continuous (fun y => fderiv ℝ (f i) y v) := fun i v =>
    ((hfc i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcontq' : ∀ v : Space, Continuous (fun y => fderiv ℝ (q σ) y v) := fun v =>
    (hqs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint_i : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y => f i y * fderiv ℝ (q σ) y (unitVector i)) := fun i _ =>
    ((hfc i).continuous.mul (hcontq' _)).integrable_of_hasCompactSupport ((hfsupp i).mul_right)
  have hint_j : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y => fderiv ℝ (f i) y (unitVector i) * q σ y) := fun i _ =>
    ((hcontf' i _).mul hqs.continuous).integrable_of_hasCompactSupport (hqsupp.mul_left)
  have hibp : ∀ i, ∫ y, f i y * fderiv ℝ (q σ) y (unitVector i) =
      -∫ y, fderiv ℝ (f i) y (unitVector i) * q σ y := by
    intro i
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint_j i (Finset.mem_univ _))
      (hint_i i (Finset.mem_univ _)) ?_ (fun y _ => hfd i y) (fun y _ => hqd y)
    exact ((hfc i).continuous.mul hqs.continuous).integrable_of_hasCompactSupport ((hfsupp i).mul_right)
  have hdiv : ∀ y, ∑ i, fderiv ℝ (f i) y (unitVector i) * q σ y = 0 := by
    intro y
    rw [← Finset.sum_mul]
    simp_rw [hff]
    have := d₁ σ y
    unfold divergenceAt at this
    rw [this, zero_mul]
  simp_rw [hpt]
  rw [integral_finsetSum _ hint_i]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hint_j]
  simp_rw [hdiv]
  simp


theorem exists_field_of_bounded (L : (ℝ → Space → Space) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hadd : ∀ ψ₁ ψ₂, IsPeriodicTestField ψ₁ → IsPeriodicTestField ψ₂ → L (ψ₁ + ψ₂) = L ψ₁ + L ψ₂)
    (hsmul : ∀ (a : ℝ) ψ, IsPeriodicTestField ψ → L (a • ψ) = a * L ψ)
    (hbd : ∀ ψ, IsPeriodicTestField ψ → |L ψ| ≤ K * periodNorm ψ) :
    ∃ M : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume ∧ IsTimePeriodic M ∧
      periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤ ∧
      (∀ q, IsPeriodicTestPotential q →
        ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) ∧
      (∀ ψ, IsPeriodicTestField ψ → ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (ψ σ y) = L ψ) ∧
      periodNorm M ≤ K := by
  classical
  have memT : ∀ ψ : ℝ → Space → Space, IsPeriodicTestField ψ →
      MemLp (fun z : ℝ × Space => ψ z.1 z.2) 2 periodMeasure := fun ψ hψ =>
    memLp_of_period (testField_aestronglyMeasurable hψ) (testField_sq_lt_top hψ)
  let T : Submodule ℝ (ℝ → Space → Space) :=
    { carrier := {ψ | IsPeriodicTestField ψ}
      add_mem' := fun h₁ h₂ => testField_add h₁ h₂
      zero_mem' := testField_zero
      smul_mem' := fun a _ h => testField_smul a h }
  let j : T →ₗ[ℝ] Lp Space 2 periodMeasure :=
    { toFun := fun ψ => (memT ψ.1 ψ.2).toLp _
      map_add' := fun ψ₁ ψ₂ => MemLp.toLp_add (memT ψ₁.1 ψ₁.2) (memT ψ₂.1 ψ₂.2)
      map_smul' := fun a ψ => MemLp.toLp_const_smul a (memT ψ.1 ψ.2) }
  let L' : T →ₗ[ℝ] ℝ :=
    { toFun := fun ψ => L ψ.1
      map_add' := fun ψ₁ ψ₂ => hadd ψ₁.1 ψ₂.1 ψ₁.2 ψ₂.2
      map_smul' := fun a ψ => hsmul a ψ.1 ψ.2 }
  have hj : ∀ ψ : T, ‖j ψ‖ = periodNorm ψ.1 := fun ψ => norm_toLp_eq_periodNorm (memT ψ.1 ψ.2)
  have hker : LinearMap.ker j ≤ LinearMap.ker L' := by
    intro ψ hψ
    rw [LinearMap.mem_ker] at hψ ⊢
    have h := hbd ψ.1 ψ.2
    rw [← hj, hψ, norm_zero, mul_zero] at h
    exact abs_nonpos_iff.1 h
  let ℓ₀ : LinearMap.range j →ₗ[ℝ] ℝ :=
    ((LinearMap.ker j).liftQ L' hker).comp j.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ ψ : T, ℓ₀ ⟨j ψ, LinearMap.mem_range_self j ψ⟩ = L ψ.1 := by
    intro ψ
    simp only [ℓ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hℓ₀b : ∀ x : LinearMap.range j, ‖ℓ₀ x‖ ≤ K * ‖x‖ := by
    rintro ⟨_, ψ, rfl⟩
    rw [hℓ₀ ψ, Real.norm_eq_abs]
    refine (hbd ψ.1 ψ.2).trans_eq ?_
    rw [← hj]
    rfl
  let ℓ₁ := ℓ₀.mkContinuous K hℓ₀b
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq (LinearMap.range j) ℓ₁
  let Gr : Submodule ℝ (Lp Space 2 periodMeasure) := Submodule.span ℝ
    {x | ∃ q, ∃ hq : IsPeriodicTestPotential q, x = (potential_gradient_memLp hq).toLp _}
  have hGc : CompleteSpace Grᗮ := Gr.isClosed_orthogonal.completeSpace_coe
  have hGp : Grᗮ.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace Grᗮ
  let M₀ := (InnerProductSpace.toDual ℝ (Lp Space 2 periodMeasure)).symm g
  let M₁ := Grᗮ.starProjection M₀
  have horth : ∀ ψ : T, j ψ ∈ Grᗮ := by
    intro ψ
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      show inner ℝ _ ((memT ψ.1 ψ.2).toLp _) = 0
      exact (inner_toLp _ _).trans (gradient_inner_testField ψ.2 hq)
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  have hM₁ψ : ∀ ψ : T, inner ℝ M₁ (j ψ) = L ψ.1 := by
    intro ψ
    rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (horth ψ),
      InnerProductSpace.toDual_symm_apply, hg (⟨j ψ, LinearMap.mem_range_self j ψ⟩ : LinearMap.range j),
      LinearMap.mkContinuous_apply, hℓ₀]
  have hM₁q : ∀ q (hq : IsPeriodicTestPotential q),
      inner ℝ M₁ ((potential_gradient_memLp hq).toLp _) = 0 := by
    intro q hq
    have hu : (potential_gradient_memLp hq).toLp _ ∈ Gr := Submodule.subset_span ⟨q, hq, rfl⟩
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hu (Grᗮ.starProjection_apply_mem M₀)
  have hM₁n : ‖M₁‖ ≤ K := by
    calc ‖M₁‖ ≤ ‖M₀‖ := by
          have h1 := (Grᗮ.starProjection).le_opNorm M₀
          have h2 : ‖Grᗮ.starProjection‖ ≤ 1 := Grᗮ.starProjection_norm_le
          nlinarith [norm_nonneg M₀]
      _ = ‖g‖ := LinearIsometryEquiv.norm_map _ _
      _ = ‖ℓ₁‖ := hgn
      _ ≤ K := LinearMap.mkContinuous_norm_le _ hK _
  have hAE := Lp.aestronglyMeasurable M₁
  set r := hAE.mk _ with hr
  have hrs : StronglyMeasurable r := hAE.stronglyMeasurable_mk
  have hrae : (M₁ : ℝ × Space → Space) =ᵐ[periodMeasure] r := hAE.ae_eq_mk
  let M : ℝ → Space → Space := fun σ y => r (Int.fract σ, y)
  have hMmeas : StronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) :=
    hrs.comp_measurable ((measurable_fract.comp measurable_fst).prodMk measurable_snd)
  have hfr : ∀ᵐ z ∂periodMeasure, Int.fract z.1 = z.1 := by
    have h1 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), Int.fract σ = σ := by
      rw [ae_restrict_iff' measurableSet_Icc]
      have h0 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ 1 := by
        rw [ae_iff]
        simp
      filter_upwards [h0] with σ hσ hmem
      exact Int.fract_eq_self.2 ⟨hmem.1, lt_of_le_of_ne hmem.2 hσ⟩
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hMae : (fun z : ℝ × Space => M z.1 z.2) =ᵐ[periodMeasure] M₁ := by
    filter_upwards [hfr, hrae] with z h1 h2
    show r (Int.fract z.1, z.2) = M₁ z
    rw [h1, h2]
  have hMmem : MemLp (fun z : ℝ × Space => M z.1 z.2) 2 periodMeasure := (Lp.memLp M₁).ae_eq hMae.symm
  have hMlp : hMmem.toLp _ = M₁ := by
    rw [← Lp.toLp_coeFn M₁ (Lp.memLp M₁)]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 hMae
  refine ⟨M, hMmeas.aestronglyMeasurable, fun σ y => by simp only [M, Int.fract_add_one],
    period_lt_top_of_memLp hMmem, ?_, ?_, ?_⟩
  · intro q hq
    have hi := integrable_inner_of_memLp hMmem (potential_gradient_memLp hq)
    refine (integral_prod _ hi).symm.trans ?_
    rw [← inner_toLp hMmem (potential_gradient_memLp hq), hMlp]
    exact hM₁q q hq
  · intro ψ hψ
    have hi := integrable_inner_of_memLp hMmem (memT ψ hψ)
    refine (integral_prod _ hi).symm.trans ?_
    rw [← inner_toLp hMmem (memT ψ hψ), hMlp]
    exact hM₁ψ ⟨ψ, hψ⟩
  · rw [← norm_toLp_eq_periodNorm hMmem, hMlp]
    exact hM₁n


theorem weightedEnergy_bounds {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (Γ : Set Symmetry) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hwb : ∃ B, ∀ y, w y ≤ B)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    periodNorm (fun σ y => secondDerivTrace (H σ y)) ≤ Real.sqrt (weightedEnergy w G H) ∧
      fieldGradNorm G ≤ Real.sqrt (weightedEnergy w G H) / Real.sqrt w₀ := by
  obtain ⟨B, hB⟩ := hwb
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have mH : AEMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (H z.1 z.2)‖ ^ 2) μ := by
    rw [hμ, period_measure_eq]
    exact ((secondDerivTrace_continuous.comp_aestronglyMeasurable hv.measurable_secondDeriv).norm.pow 2).aemeasurable.restrict
  have mG : AEMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) μ := by
    rw [hμ, period_measure_eq]
    exact (matSq_continuous.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable.restrict
  have mW : AEMeasurable (fun z : ℝ × Space =>
      ‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w z.2 * matSq (G z.1 z.2)) μ :=
    mH.add ((hm.weight_measurable.comp measurable_snd).aemeasurable.mul mG)
  have hw0 : ∀ y, 0 ≤ w y := fun y => hm.weight_pos.le.trans (hm.weight_lower y)
  have hYfin : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) < ⊤ := by
    rw [periodLIntegral_eq_prod (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) mW]
    calc ∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w z.2 * matSq (G z.1 z.2)) ∂μ
        ≤ ∫⁻ z, (ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2)
            + ENNReal.ofReal (max B 0) * ENNReal.ofReal (matSq (G z.1 z.2))) ∂μ := by
          refine lintegral_mono (fun z => ?_)
          rw [← ENNReal.ofReal_mul (le_max_right _ _),
            ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (le_max_right _ _) (matSq_nonneg _))]
          apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_right ((hB z.2).trans (le_max_left B 0)) (matSq_nonneg (G z.1 z.2))
          linarith
      _ = ∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) ∂μ
            + ENNReal.ofReal (max B 0) * ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂μ := by
          rw [lintegral_add_left' mH.ennreal_ofReal, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := by
          rw [← periodLIntegral_eq_prod (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) mH,
            ← periodLIntegral_eq_prod (f := fun σ y => matSq (G σ y)) mG]
          exact ENNReal.add_lt_top.2 ⟨hv.sumSecondPartials_finite,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite⟩
  have hX : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) := by
    unfold periodLIntegral
    refine lintegral_mono (fun σ => lintegral_mono (fun y => ENNReal.ofReal_le_ofReal ?_))
    have := mul_nonneg (hw0 y) (matSq_nonneg (G σ y))
    linarith
  have hZ : ENNReal.ofReal w₀ * periodLIntegral (fun σ y => matSq (G σ y)) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun σ => ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun y => ?_)
    rw [← ENNReal.ofReal_mul hm.weight_pos.le]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_right (hm.weight_lower y) (matSq_nonneg (G σ y))
    nlinarith [sq_nonneg ‖secondDerivTrace (H σ y)‖]
  have hE : weightedEnergy w G H =
      (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y))).toReal := rfl
  constructor
  · unfold periodNorm
    rw [hE]
    exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hYfin.ne hX)
  · unfold fieldGradNorm
    rw [hE, ← Real.sqrt_div' _ hm.weight_pos.le]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hm.weight_pos]
    have h1 := ENNReal.toReal_mono hYfin.ne hZ
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.weight_pos.le] at h1
    linarith

theorem scalar_bound {c cμ E A Gn w₀ eS eG r t : ℝ} (hc : 0 < c) (hcμ : 0 < cμ) (hw₀ : 0 < w₀)
    (heS : 0 ≤ eS) (heG : 0 ≤ eG) (hr : 0 ≤ r) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (hA : A ≤ Real.sqrt E) (hG : Gn ≤ Real.sqrt E / Real.sqrt w₀) :
    A + (eS * A + eG * Gn + Real.sqrt r * Real.sqrt t) ≤
      Real.sqrt ((1 + eS + eG / Real.sqrt w₀) ^ 2 / c + r / cμ) * Real.sqrt (c * E + cμ * t) := by
  obtain ⟨q, hq0, rfl⟩ : ∃ q, 0 ≤ q ∧ r = q ^ 2 := ⟨Real.sqrt r, Real.sqrt_nonneg _, (Real.sq_sqrt hr).symm⟩
  rw [Real.sqrt_sq hq0]
  have hsw : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw₀
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ E = s ^ 2 := ⟨Real.sqrt E, Real.sqrt_nonneg _, (Real.sq_sqrt hE).symm⟩
  obtain ⟨n, hn0, rfl⟩ : ∃ n, 0 ≤ n ∧ t = n ^ 2 := ⟨Real.sqrt t, Real.sqrt_nonneg _, (Real.sq_sqrt ht).symm⟩
  rw [Real.sqrt_sq hs0] at hA hG
  rw [Real.sqrt_sq hn0]
  set a := 1 + eS + eG / Real.sqrt w₀ with ha
  have ha0 : 0 ≤ a := by positivity
  have step1 : A + (eS * A + eG * Gn + q * n) ≤ a * s + q * n := by
    have h1 : eG * Gn ≤ eG * (s / Real.sqrt w₀) := mul_le_mul_of_nonneg_left hG heG
    have h2 : eS * A ≤ eS * s := mul_le_mul_of_nonneg_left hA heS
    have h3 : a * s = s + eS * s + eG * (s / Real.sqrt w₀) := by rw [ha]; ring
    linarith
  refine step1.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  rw [div_add_div _ _ hc.ne' hcμ.ne', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a * cμ * n - q * c * s)]

theorem secondDerivPairing_abs_le {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume)
    (hH2 : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) < ⊤)
    {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    |∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y)| ≤
      periodNorm (fun σ y => secondDerivTrace (H σ y)) * periodNorm ψ := by
  have hcont := secondDerivTrace_continuous
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => -secondDerivTrace (H z.1 z.2)) volume :=
    (hcont.comp_aestronglyMeasurable hH).neg
  have hF2 : periodLIntegral (fun σ y => ‖-secondDerivTrace (H σ y)‖ ^ 2) < ⊤ := by
    simpa only [norm_neg] using hH2
  have h := periodPairing_abs_le hF (testField_aestronglyMeasurable hψ) hF2 (testField_sq_lt_top hψ)
  have e : periodNorm (fun σ y => -secondDerivTrace (H σ y)) = periodNorm (fun σ y => secondDerivTrace (H σ y)) := by
    simp only [periodNorm, norm_neg]
  rw [← e]
  exact h

theorem secondDerivPairing_add {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume)
    (hH2 : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) < ⊤)
    {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁) (h₂ : IsPeriodicTestField ψ₂) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) ((ψ₁ + ψ₂) σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ₁ σ y))
        + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ₂ σ y) := by
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => -secondDerivTrace (H z.1 z.2)) volume :=
    (secondDerivTrace_continuous.comp_aestronglyMeasurable hH).neg
  have hF2 : periodLIntegral (fun σ y => ‖-secondDerivTrace (H σ y)‖ ^ 2) < ⊤ := by
    simpa only [norm_neg] using hH2
  have h12 := testField_add h₁ h₂
  have i1 := pairing_integrable hF (testField_aestronglyMeasurable h₁) hF2 (testField_sq_lt_top h₁)
  have i2 := pairing_integrable hF (testField_aestronglyMeasurable h₂) hF2 (testField_sq_lt_top h₂)
  have i12 := pairing_integrable hF (testField_aestronglyMeasurable h12) hF2 (testField_sq_lt_top h12)
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ₁ σ y)) =
      ∫ z, inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ₁ z.1 z.2)
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := (integral_prod _ i1).symm
  have e2 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ₂ σ y)) =
      ∫ z, inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ₂ z.1 z.2)
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := (integral_prod _ i2).symm
  have e12 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) ((ψ₁ + ψ₂) σ y)) =
      ∫ z, inner ℝ (-secondDerivTrace (H z.1 z.2)) ((ψ₁ + ψ₂) z.1 z.2)
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := (integral_prod _ i12).symm
  rw [e1, e2, e12, ← integral_add i1 i2]
  congr 1
  funext z
  simp only [Pi.add_apply, inner_add_right]

theorem secondDerivPairing_smul (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : ℝ)
    (ψ : ℝ → Space → Space) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) ((a • ψ) σ y)) =
      a * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y) := by
  simp only [Pi.smul_apply, real_inner_smul_right, integral_const_mul]

theorem fieldModeSum_split (hPars : ModeSquareSumHolds) (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    fieldModeSum m v G ψ = (∑' ι : ℤ × ℤ, ∫ z, termEps m G ψ ι z.1 z.2 ∂periodMeasure)
      + ∑' ι : ℤ × ℤ, ∫ z, termMu m v ψ ι z.1 z.2 ∂periodMeasure := by
  rw [fieldModeSum_eq, ← (termEps_summable hPars hLoc hm hv hψ).tsum_add (termMu_summable hPars hLoc hm hv hψ)]
  refine tsum_congr (fun ι => ?_)
  have hIe := termEps_integrable hPars hm hv hψ ι
  have hIm := termMu_integrable hPars hLoc hm hv hψ ι
  rw [← integral_add hIe hIm]
  exact (integral_prod _ (hIe.add hIm)).symm

theorem integral_sqrt_mul_le {μ : Measure (ℝ × Space)} {a c : ℝ × Space → ℝ} (ha0 : ∀ z, 0 ≤ a z)
    (hc0 : ∀ z, 0 ≤ c z) (ha : Integrable a μ) (hc : Integrable c μ) :
    Integrable (fun z => Real.sqrt (a z) * Real.sqrt (c z)) μ ∧
      ∫ z, Real.sqrt (a z) * Real.sqrt (c z) ∂μ ≤ Real.sqrt (∫ z, a z ∂μ) * Real.sqrt (∫ z, c z ∂μ) := by
  have amgm : ∀ z, ∀ t : ℝ, 0 < t → Real.sqrt (a z) * Real.sqrt (c z) ≤ (t * a z + c z / t) / 2 :=
    fun z t ht => FieldModes.sqrt_mul_sqrt_le_of_pos (ha0 z) (hc0 z) ht
  have hm : AEStronglyMeasurable (fun z => Real.sqrt (a z) * Real.sqrt (c z)) μ :=
    (ha.1.aemeasurable.sqrt.mul hc.1.aemeasurable.sqrt).aestronglyMeasurable
  have hI : Integrable (fun z => Real.sqrt (a z) * Real.sqrt (c z)) μ := by
    refine Integrable.mono' ((ha.add hc).div_const 2) hm (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    have h1 := amgm z 1 one_pos
    rw [one_mul, div_one] at h1
    exact h1
  refine ⟨hI, FieldModes.sq_sqrt_bound (integral_nonneg fun z => ha0 z) (integral_nonneg fun z => hc0 z)
    fun t ht => ?_⟩
  calc ∫ z, Real.sqrt (a z) * Real.sqrt (c z) ∂μ ≤ ∫ z, (t * a z + c z / t) / 2 ∂μ :=
        integral_mono hI (((ha.const_mul t).add (hc.div_const t)).div_const 2) fun z => amgm z t ht
    _ = (t * ∫ z, a z ∂μ + (∫ z, c z ∂μ) / t) / 2 := by
        rw [integral_div, integral_add (ha.const_mul t) (hc.div_const t), integral_const_mul, integral_div]

theorem epsModeTerm_abs_le (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) :
    |∫ z, termEps m G ψ ι z.1 z.2 ∂periodMeasure| ≤
      (epsSup * Real.sqrt (∫ z, cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2) ∂periodMeasure)
        + epsGradSup * Real.sqrt (∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure))
        * Real.sqrt (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure) := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  have hx : Integrable (fun z : ℝ × Space =>
      cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2)) periodMeasure :=
    FieldModes.integrable_cnormSq_modeVel hPars
      ⟨secondDerivTrace_continuous.comp_aestronglyMeasurable hv.measurable_secondDeriv,
        fun σ y => congrArg secondDerivTrace (hv.periodic_secondDeriv σ y), hv.sumSecondPartials_finite⟩ ι
  have hz : Integrable (fun z : ℝ × Space => cnormSq (modeVel ι ψ z.1 z.2)) periodMeasure :=
    FieldModes.integrable_cnormSq_modeVel hPars
      (FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR) ι
  have hy : Integrable (fun z : ℝ × Space => cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) periodMeasure := by
    have hA := FieldModes.integrable_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient
      hv.gradient_finite ι
    have hc : Continuous (fun x : Fin 3 × Fin 3 → ℂ => cnormSq (curlOfGrad x)) :=
      FieldModes.continuous_cnormSq.comp (by unfold curlOfGrad; fun_prop)
    refine Integrable.mono' (hA.const_mul 2) (hc.comp_aestronglyMeasurable
      (FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (FieldModes.cnormSq_nonneg _)]
    exact FieldModes.cnormSq_curlOfGrad_le _
  have hA0 : 0 ≤ epsSup := (abs_nonneg _).trans (hm.epsW_le (m.classOf ι) 0)
  have hA'0 : 0 ≤ epsGradSup := (norm_nonneg _).trans (hm.epsW_grad_le (m.classOf ι) 0)
  have hB := CurlWeight.Internal.curlWeightPairing_abs_le hPars hDer hRotM hv hψ ι (n := 1)
    (fun _ => (1 : ℝ)) (fun _ => m.epsW (m.classOf ι)) (fun _ => hm.epsW_increment _)
    (A := epsSup) (A' := epsGradSup) (fun y => by simpa using hm.epsW_le (m.classOf ι) y)
    (fun y _ => by simpa using hm.epsW_grad_le (m.classOf ι) y)
  simp only [Fin.sum_univ_one, one_mul] at hB
  obtain ⟨i1, c1⟩ := integral_sqrt_mul_le (fun z => FieldModes.cnormSq_nonneg _)
    (fun z => FieldModes.cnormSq_nonneg _) hx hz
  obtain ⟨i2, c2⟩ := integral_sqrt_mul_le (fun z => FieldModes.cnormSq_nonneg _)
    (fun z => FieldModes.cnormSq_nonneg _) hy hz
  have hF0 : ∀ z : ℝ × Space, 0 ≤ epsSup * (Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)))
        + epsGradSup * (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) := fun z =>
    add_nonneg (mul_nonneg hA0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (mul_nonneg hA'0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hF : Integrable (fun z : ℝ × Space =>
      epsSup * (Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)))
        + epsGradSup * (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)))) periodMeasure :=
    (i1.const_mul epsSup).add (i2.const_mul epsGradSup)
  have hlin : ∫⁻ z, ENNReal.ofReal
      ((epsSup * Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
        + epsGradSup * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))))
        * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) ∂periodMeasure =
      ENNReal.ofReal (∫ z, epsSup * (Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)))
        + epsGradSup * (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) ∂periodMeasure) := by
    rw [ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ hF0)]
    refine lintegral_congr fun z => ?_
    congr 1
    ring
  have hle := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hF0)).1 (hB.trans_eq hlin)
  rw [integral_add (i1.const_mul epsSup) (i2.const_mul epsGradSup), integral_const_mul,
    integral_const_mul] at hle
  calc |∫ z, termEps m G ψ ι z.1 z.2 ∂periodMeasure|
      ≤ epsSup * ∫ z, Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)) ∂periodMeasure
        + epsGradSup * ∫ z, Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
          * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)) ∂periodMeasure := hle
    _ ≤ epsSup * (Real.sqrt (∫ z, cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2) ∂periodMeasure)
          * Real.sqrt (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure))
        + epsGradSup * (Real.sqrt (∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure)
          * Real.sqrt (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure)) :=
        add_le_add (mul_le_mul_of_nonneg_left c1 hA0) (mul_le_mul_of_nonneg_left c2 hA'0)
    _ = _ := by ring

theorem curlMode_tsum_le (hPars : ModeSquareSumHolds) (_hDer : ModeDerivativeHolds)
    (_hRotM : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    ∑' ι : ℤ × ℤ, ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure ≤ fieldGradNorm G ^ 2 := by
  have hK : FieldModes.IsSquareField (fun s x => curlVec (G s x)) :=
    ⟨CurlEnergy.continuous_curlVec.comp_aestronglyMeasurable hv.measurable_gradient,
      fun σ y => congrArg curlVec (hv.periodic_gradient σ y),
      by rw [periodLIntegral_curlVec_sq_eq hv]; exact hv.gradient_finite⟩
  have hac : periodMeasure ≪ (volume : Measure (ℝ × Space)) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      (Measure.AbsolutelyContinuous.refl _)
  have hae : ∀ ι : ℤ × ℤ, ∀ᵐ z ∂periodMeasure, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) =
      cnormSq (modeVel ι (fun s x => curlVec (G s x)) z.1 z.2) := by
    intro ι
    filter_upwards [hac.ae_le (ae_curlOfGrad_modeGrad hv ι)] with z hz
    rw [hz]
  calc ∑' ι : ℤ × ℤ, ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure
      = ∑' ι : ℤ × ℤ, ∫ z, cnormSq (modeVel ι (fun s x => curlVec (G s x)) z.1 z.2) ∂periodMeasure :=
        tsum_congr fun ι => integral_congr_ae (hae ι)
    _ = (periodLIntegral (fun σ y => ‖curlVec (G σ y)‖ ^ 2)).toReal :=
        FieldModes.tsum_integral_cnormSq_modeVel hPars hK
    _ = fieldGradNorm G ^ 2 := by
        rw [periodLIntegral_curlVec_sq_eq hv, fieldGradNorm, Real.sq_sqrt ENNReal.toReal_nonneg]
    _ ≤ fieldGradNorm G ^ 2 := le_rfl

theorem continuous_curlOfGrad : Continuous (fun x : Fin 3 × Fin 3 → ℂ => curlOfGrad x) := by
  unfold curlOfGrad
  fun_prop

theorem epsModeSum_abs_le (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    |∑' ι : ℤ × ℤ, ∫ z, termEps m G ψ ι z.1 z.2 ∂periodMeasure| ≤
      (epsSup * periodNorm (fun σ y => secondDerivTrace (H σ y)) + epsGradSup * fieldGradNorm G)
        * periodNorm ψ := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  obtain ⟨c0⟩ : Nonempty C := ⟨m.classOf 0⟩
  have heS : 0 ≤ epsSup := (abs_nonneg _).trans (hm.epsW_le c0 0)
  have heG : 0 ≤ epsGradSup := (norm_nonneg _).trans (hm.epsW_grad_le c0 0)
  have hX := FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  have hD : FieldModes.IsSquareField (fun σ y => secondDerivTrace (H σ y)) := by
    refine ⟨secondDerivTrace_continuous.comp_aestronglyMeasurable hv.measurable_secondDeriv, fun σ y => ?_,
      hv.sumSecondPartials_finite⟩
    show secondDerivTrace (H (σ + 1) y) = secondDerivTrace (H σ y)
    rw [hv.periodic_secondDeriv σ y]
  have hAi := fun ι => FieldModes.integrable_cnormSq_modeGrad hPars hv.measurable_gradient
    hv.periodic_gradient hv.gradient_finite ι
  have hWi : ∀ ι, Integrable (fun z : ℝ × Space => cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
      periodMeasure := by
    intro ι
    refine Integrable.mono' ((hAi ι).const_mul 2)
      ((FieldModes.continuous_cnormSq.comp continuous_curlOfGrad).measurable.comp_aemeasurable
        (FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (FieldModes.cnormSq_nonneg _)]
    exact FieldModes.cnormSq_curlOfGrad_le _
  have hW0 : ∀ ι, 0 ≤ ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure :=
    fun ι => integral_nonneg (fun z => FieldModes.cnormSq_nonneg _)
  have hL0 : ∀ ι, 0 ≤ ∫ z, cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2) ∂periodMeasure :=
    fun ι => integral_nonneg (fun z => FieldModes.cnormSq_nonneg _)
  have hQ0 : ∀ ι, 0 ≤ ∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure :=
    fun ι => integral_nonneg (fun z => FieldModes.cnormSq_nonneg _)
  have hWs : Summable (fun ι => ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure) := by
    refine Summable.of_nonneg_of_le hW0 (fun ι => ?_)
      ((FieldModes.summable_integral_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient
        hv.gradient_finite).mul_left 2)
    rw [← integral_const_mul]
    exact integral_mono (hWi ι) ((hAi ι).const_mul 2) (fun z => FieldModes.cnormSq_curlOfGrad_le _)
  have hLs := FieldModes.summable_integral_cnormSq_modeVel hPars hD
  have hQs := FieldModes.summable_integral_cnormSq_modeVel hPars hX
  obtain ⟨hsL, hL⟩ := FieldModes.tsum_sqrt_mul_le hL0 hQ0 hLs hQs
  obtain ⟨hsW, hW⟩ := FieldModes.tsum_sqrt_mul_le hW0 hQ0 hWs hQs
  have hper := fun ι => epsModeTerm_abs_le hPars hDer hRotM m P b w Γ hm hv hψ ι
  have hmaj := (hsL.mul_left epsSup).add (hsW.mul_left epsGradSup)
  have hle : ∀ ι, ‖∫ z, termEps m G ψ ι z.1 z.2 ∂periodMeasure‖ ≤
      epsSup * (Real.sqrt (∫ z, cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2) ∂periodMeasure)
        * Real.sqrt (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure))
      + epsGradSup * (Real.sqrt (∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure)
        * Real.sqrt (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure)) := by
    intro ι
    rw [Real.norm_eq_abs]
    refine (hper ι).trans (le_of_eq ?_)
    ring
  have hnorm := Summable.of_nonneg_of_le (fun ι => norm_nonneg _) hle hmaj
  have hLtot := FieldModes.tsum_integral_cnormSq_modeVel hPars hD
  have hQtot := FieldModes.tsum_integral_cnormSq_modeVel hPars hX
  have hWtot := curlMode_tsum_le hPars hDer hRotM hv
  have hGn : 0 ≤ fieldGradNorm G := Real.sqrt_nonneg _
  have hsqW : Real.sqrt (∑' ι, ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂periodMeasure)
      ≤ fieldGradNorm G := by
    calc _ ≤ Real.sqrt (fieldGradNorm G ^ 2) := Real.sqrt_le_sqrt hWtot
      _ = fieldGradNorm G := Real.sqrt_sq hGn
  have hQn : Real.sqrt (∑' ι, ∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure) = periodNorm ψ := by
    rw [hQtot]
    rfl
  have hLn : Real.sqrt (∑' ι, ∫ z, cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2) ∂periodMeasure)
      = periodNorm (fun σ y => secondDerivTrace (H σ y)) := by
    rw [hLtot]
    rfl
  have hψn : 0 ≤ periodNorm ψ := Real.sqrt_nonneg _
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (Summable.tsum_le_tsum hle hnorm hmaj).trans ?_
  rw [(hsL.mul_left epsSup).tsum_add (hsW.mul_left epsGradSup), tsum_mul_left, tsum_mul_left]
  rw [hLn, hQn] at hL
  rw [hQn] at hW
  have k1 := mul_le_mul_of_nonneg_left hL heS
  have k2 := mul_le_mul_of_nonneg_left (hW.trans (mul_le_mul_of_nonneg_right hsqW hψn)) heG
  nlinarith [k1, k2]

theorem norm_cdot_le_sqrt (x z : Fin 3 → ℂ) :
    ‖cdot x z‖ ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq z) := by
  unfold cdot cnormSq
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ‖x i * (starRingEnd ℂ) (z i)‖ = ‖x i‖ * ‖z i‖ :=
    fun i _ => by rw [norm_mul, Complex.norm_conj]
  rw [Finset.sum_congr rfl h]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem termMu_abs_le_of_pos {C : Type} (m : ModeWeights C) (v ψ : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) {t : ℝ} (ht : 0 < t) :
    |termMu m v ψ ι σ y| ≤
      (t * (m.mu ι y ^ 2 * cnormSq (modeVel ι v σ y)) + cnormSq (modeVel ι ψ σ y) / t) / 2 := by
  unfold termMu
  have h1 := FieldModes.abs_re_I_mul_le (m.muW (m.classOf ι) y) (cdot (modeVel ι v σ y) (modeVel ι ψ σ y))
  have h2 := norm_cdot_le_sqrt (modeVel ι v σ y) (modeVel ι ψ σ y)
  have ha : Real.sqrt (cnormSq (modeVel ι v σ y)) ^ 2 = cnormSq (modeVel ι v σ y) :=
    Real.sq_sqrt (FieldModes.cnormSq_nonneg _)
  have hc : Real.sqrt (cnormSq (modeVel ι ψ σ y)) ^ 2 = cnormSq (modeVel ι ψ σ y) :=
    Real.sq_sqrt (FieldModes.cnormSq_nonneg _)
  have hμ : m.mu ι y = |m.muW (m.classOf ι) y| := rfl
  have he : 0 ≤ |m.muW (m.classOf ι) y| := abs_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h2 he
  rw [← ha, ← hc, hμ]
  set e := |m.muW (m.classOf ι) y|
  set a := Real.sqrt (cnormSq (modeVel ι v σ y))
  set c := Real.sqrt (cnormSq (modeVel ι ψ σ y))
  have key : 0 ≤ (t * (e * a) - c) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have eq : (t * (e * a) - c) ^ 2 / t = t * (e ^ 2 * a ^ 2) + c ^ 2 / t - 2 * (e * (a * c)) := by
    field_simp
    ring
  linarith

theorem muModeSum_abs_le (hPars : ModeSquareSumHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (hn : m.frequencySeminormSq P v < ⊤) :
    |∑' ι : ℤ × ℤ, ∫ z, termMu m v ψ ι z.1 z.2 ∂periodMeasure| ≤
      Real.sqrt ratio * Real.sqrt (m.frequencySeminormSq P v).toReal * periodNorm ψ := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  have hX := FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  set a : ℤ × ℤ → ℝ≥0∞ := fun ι => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (m.mu ι y * |m.dop P ι y| * cnormSq (modeVel ι v σ y)) with ha_def
  have hsum_a : ∑' ι, a ι = m.frequencySeminormSq P v := rfl
  have ha_fin : ∀ ι, a ι ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top (hsum_a ▸ hn.ne) (ENNReal.le_tsum ι)
  have hcv : ∀ ι, AEMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι v z.1 z.2)) periodMeasure :=
    fun ι => FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (FieldModes.aemeasurable_modeVel hv.measurable_velocity ι)
  have hmu : ∀ ι, Measurable (fun z : ℝ × Space => m.mu ι z.2) := fun ι =>
    (continuous_abs.comp (muW_continuous hm (m.classOf ι))).measurable.comp measurable_snd
  have hmeasA : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      m.mu ι z.2 * |m.dop P ι z.2| * cnormSq (modeVel ι v z.1 z.2)) periodMeasure := by
    intro ι
    have hdop : Measurable (fun y => m.dop P ι y) := by
      unfold ModeWeights.dop shiftedFrequency
      exact measurable_const.add (measurable_const.mul (hm.rate_measurable _))
    exact ((hmu ι).aemeasurable.mul
      ((continuous_abs.measurable.comp (hdop.comp measurable_snd)).aemeasurable)).mul (hcv ι)
  have hmeasQ : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2)) periodMeasure :=
    fun ι => ((hmu ι).aemeasurable.pow_const 2).mul (hcv ι)
  have hQ0 : ∀ ι (z : ℝ × Space), 0 ≤ m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2) :=
    fun ι z => mul_nonneg (sq_nonneg _) (FieldModes.cnormSq_nonneg _)
  have hlinQ : ∀ ι, ∫⁻ z, ENNReal.ofReal (m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2)) ∂periodMeasure
      ≤ ENNReal.ofReal ratio * a ι := by
    intro ι
    have e : a ι = ∫⁻ z, ENNReal.ofReal (m.mu ι z.2 * |m.dop P ι z.2| * cnormSq (modeVel ι v z.1 z.2))
        ∂periodMeasure := (lintegral_prod _ (hmeasA ι).ennreal_ofReal).symm
    rw [e, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun z => ?_)
    rw [← ENNReal.ofReal_mul hm.ratio_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hm.mu_ratio ι z.2
    have h0 : 0 ≤ m.mu ι z.2 := abs_nonneg _
    have hc := FieldModes.cnormSq_nonneg (modeVel ι v z.1 z.2)
    have h2 : m.mu ι z.2 ^ 2 ≤ ratio * (m.mu ι z.2 * |m.dop P ι z.2|) := by nlinarith
    nlinarith
  have hIQ : ∀ ι, Integrable (fun z : ℝ × Space => m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2))
      periodMeasure := by
    intro ι
    refine (integrable_toReal_of_lintegral_ne_top (hmeasQ ι).ennreal_ofReal ?_).congr
      (ae_of_all _ fun z => ENNReal.toReal_ofReal (hQ0 ι z))
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ha_fin ι)) (hlinQ ι)
  have hQle : ∀ ι, ∫ z, m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2) ∂periodMeasure
      ≤ ratio * (a ι).toReal := by
    intro ι
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => hQ0 ι z) (hmeasQ ι).aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal ratio * a ι).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ha_fin ι)) (hlinQ ι)
      _ = ratio * (a ι).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.ratio_nonneg]
  have hsa : Summable (fun ι => ratio * (a ι).toReal) :=
    (ENNReal.summable_toReal (hsum_a ▸ hn.ne)).mul_left ratio
  have hQsum : Summable (fun ι => ∫ z, m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2) ∂periodMeasure) :=
    Summable.of_nonneg_of_le (fun ι => integral_nonneg (fun z => hQ0 ι z)) hQle hsa
  have hQtot : ∑' ι, ∫ z, m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2) ∂periodMeasure
      ≤ ratio * (m.frequencySeminormSq P v).toReal := by
    calc _ ≤ ∑' ι, ratio * (a ι).toReal := Summable.tsum_le_tsum hQle hQsum hsa
      _ = ratio * (∑' ι, a ι).toReal := by rw [tsum_mul_left, ENNReal.tsum_toReal_eq ha_fin]
      _ = _ := by rw [hsum_a]
  have hBsum := FieldModes.summable_integral_cnormSq_modeVel hPars hX
  have hBtot := FieldModes.tsum_integral_cnormSq_modeVel hPars hX
  have hper : ∀ ι, ∀ t : ℝ, 0 < t → ‖∫ z, termMu m v ψ ι z.1 z.2 ∂periodMeasure‖ ≤
      (t * ∫ z, m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2) ∂periodMeasure
        + (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure) / t) / 2 := by
    intro ι t ht
    have hB := FieldModes.integrable_cnormSq_modeVel hPars hX ι
    refine (norm_integral_le_of_norm_le ((((hIQ ι).const_mul t).add (hB.div_const t)).div_const 2)
      (ae_of_all _ fun z => ?_)).trans (le_of_eq ?_)
    · rw [Real.norm_eq_abs]
      exact termMu_abs_le_of_pos m v ψ ι z.1 z.2 ht
    · rw [integral_div]
      congr 1
      rw [← integral_const_mul, ← integral_div]
      exact integral_add ((hIQ ι).const_mul t) (hB.div_const t)
  have hbound : ∀ t : ℝ, 0 < t → |∑' ι : ℤ × ℤ, ∫ z, termMu m v ψ ι z.1 z.2 ∂periodMeasure| ≤
      (t * (ratio * (m.frequencySeminormSq P v).toReal)
        + (periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2)).toReal / t) / 2 := by
    intro t ht
    have hmaj : Summable (fun ι => (t * ∫ z, m.mu ι z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2) ∂periodMeasure
        + (∫ z, cnormSq (modeVel ι ψ z.1 z.2) ∂periodMeasure) / t) / 2) :=
      ((hQsum.mul_left t).add (hBsum.div_const t)).div_const 2
    have hnorm : Summable (fun ι => ‖∫ z, termMu m v ψ ι z.1 z.2 ∂periodMeasure‖) :=
      Summable.of_nonneg_of_le (fun ι => norm_nonneg _) (fun ι => hper ι t ht) hmaj
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hnorm).trans ?_
    refine (Summable.tsum_le_tsum (fun ι => hper ι t ht) hnorm hmaj).trans ?_
    rw [tsum_div_const, (hQsum.mul_left t).tsum_add (hBsum.div_const t), tsum_mul_left, tsum_div_const, hBtot]
    have := mul_le_mul_of_nonneg_left hQtot ht.le
    linarith
  have hfin := FieldModes.sq_sqrt_bound (mul_nonneg hm.ratio_nonneg ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg hbound
  rw [Real.sqrt_mul hm.ratio_nonneg] at hfin
  exact hfin

theorem fieldModeSum_abs_le (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    |fieldModeSum m v G ψ| ≤
      (epsSup * periodNorm (fun σ y => secondDerivTrace (H σ y)) + epsGradSup * fieldGradNorm G
        + Real.sqrt ratio * Real.sqrt (m.frequencySeminormSq P v).toReal) * periodNorm ψ := by
  rw [fieldModeSum_split hPars hLoc hm hv hψ]
  have h1 := epsModeSum_abs_le hPars hDer hRotM m P b w Γ hm hv hψ
  have h2 := muModeSum_abs_le hPars hm hv hψ
    (frequencySeminormSq_lt_top_of_perturbation hPars hDer hRotM m P b w Γ hm hv)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

end Field

end Internal

open Internal.Field in
theorem modeFieldExistsHolds_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hLoc : PerturbationLocalSquareIntegrabilityHolds) :
    ModeFieldExistsHolds := by
  intro C m P b w Γ w₀ epsSup epsGradSup ratio hm hwb v G H g hv
  have hfin := frequencySeminormSq_lt_top_of_perturbation hPars hDer hRotM m P b w Γ hm hv
  refine ⟨hfin, ?_⟩
  set A := periodNorm (fun σ y => secondDerivTrace (H σ y)) with hAdef
  set Gn := fieldGradNorm G with hGndef
  set t := (m.frequencySeminormSq P v).toReal with htdef
  set K := A + (epsSup * A + epsGradSup * Gn + Real.sqrt ratio * Real.sqrt t) with hKdef
  have hC : Nonempty C := ⟨m.classOf 0⟩
  obtain ⟨c0⟩ := hC
  have heS : 0 ≤ epsSup := (abs_nonneg _).trans (hm.epsW_le c0 0)
  have heG : 0 ≤ epsGradSup := (norm_nonneg _).trans (hm.epsW_grad_le c0 0)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hGn0 : 0 ≤ Gn := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by positivity
  have hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume := hv.measurable_secondDeriv
  have hH2 := hv.sumSecondPartials_finite
  obtain ⟨M, hMm, hMp, hM2, hMq, hMψ, hMn⟩ := exists_field_of_bounded (Internal.Field.fieldPairing m v G H) hK
    (fun ψ₁ ψ₂ h₁ h₂ => by
      unfold Internal.Field.fieldPairing
      rw [secondDerivPairing_add hH hH2 h₁ h₂, fieldModeSum_add hPars hLoc m P b w Γ hm hv h₁ h₂]
      ring)
    (fun a ψ hψ => by
      unfold Internal.Field.fieldPairing
      rw [secondDerivPairing_smul H a ψ, fieldModeSum_smul m v G a hψ]
      ring)
    (fun ψ hψ => by
      unfold Internal.Field.fieldPairing
      refine (abs_add_le _ _).trans ?_
      have h1 := secondDerivPairing_abs_le hH hH2 hψ
      have h2 := fieldModeSum_abs_le hPars hDer hRotM hLoc m P b w Γ hm hv hψ
      have : K * periodNorm ψ = A * periodNorm ψ
          + (epsSup * A + epsGradSup * Gn + Real.sqrt ratio * Real.sqrt t) * periodNorm ψ := by
        rw [hKdef]; ring
      rw [this]
      exact add_le_add h1 h2)
  refine ⟨M, ⟨hMm, hMp, hM2, hMq, fun ψ hψ => hMψ ψ hψ⟩, hMn.trans ?_⟩
  obtain ⟨hAE, hGE⟩ := weightedEnergy_bounds m P b w Γ hm hwb hv
  have hE0 : 0 ≤ weightedEnergy w G H := ENNReal.toReal_nonneg
  exact scalar_bound hm.c_pos hm.cμ_pos hm.weight_pos heS heG hm.ratio_nonneg ENNReal.toReal_nonneg
    hE0 hAE hGE

end Coercive

end Breakdown
