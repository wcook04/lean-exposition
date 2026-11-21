import Breakdown.Uniqueness.RegDefs

open scoped ContDiff ENNReal FourierTransform Topology SchwartzMap RealInnerProductSpace
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem hasCompactSupport_complexifyComp {φ : Space → Space} (hφ : IsTestField φ) :
    HasCompactSupport (fun x => complexifyVec (φ x)) :=
  hφ.2.1.comp_left (map_zero complexifyVec)

private theorem contDiff_complexifyComp {φ : Space → Space} (hφ : IsTestField φ) :
    ContDiff ℝ ∞ (fun x => complexifyVec (φ x)) :=
  complexifyVec.contDiff.comp hφ.1

private def testRapid {φ : Space → Space} (hφ : IsTestField φ) : 𝓢(Space, CSpace) :=
  (hasCompactSupport_complexifyComp hφ).toSchwartzMap (contDiff_complexifyComp hφ)

private theorem testRapid_coe {φ : Space → Space} (hφ : IsTestField φ) :
    (testRapid hφ : Space → CSpace) = fun x => complexifyVec (φ x) := rfl

private def testSymbol {φ : Space → Space} (hφ : IsTestField φ) : 𝓢(Space, CSpace) :=
  𝓕 (testRapid hφ)

private theorem symbolOf_eq_freqTr {φ : Space → Space} (hφ : IsTestField φ) :
    symbolOf φ = ⇑(testSymbol hφ) := by
  rw [testSymbol, SchwartzMap.fourier_coe, testRapid_coe]
  rfl

theorem aestronglyMeasurable_symbolOf {φ : Space → Space} (hφ : IsTestField φ) :
    AEStronglyMeasurable (symbolOf φ) volume := by
  rw [symbolOf_eq_freqTr hφ]
  exact (testSymbol hφ).continuous.aestronglyMeasurable

private theorem freqTr_neg_complexify {φ : Space → Space} (hφ : IsTestField φ) (ξ : Space) :
    symbolOf φ (-ξ) = conjVec (symbolOf φ ξ) := by
  have hint : Integrable (fun x => complexifyVec (φ x)) := (testRapid hφ).integrable
  have hi : Integrable (fun v : Space => 𝐞 (-⟪v, ξ⟫) • complexifyVec (φ v)) := by
    rw [Real.fourierIntegral_convergent_iff]
    exact hint
  rw [symbolOf, Real.fourier_eq, Real.fourier_eq, ← conjVec.integral_comp_comm hi]
  congr 1
  ext v i
  simp [conjVec, complexifyVec, Circle.smul_def, Real.fourierChar_apply]
  left
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  exact Or.inl (map_ofNat _ 2).symm

private def traceMap : (Space →L[ℝ] CSpace) →L[ℝ] ℂ :=
  ∑ i : Fin 3, ((EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).restrictScalars ℝ).comp
    (ContinuousLinearMap.apply ℝ CSpace (unitVector i))

private theorem traceMap_apply (A : Space →L[ℝ] CSpace) : traceMap A = ∑ i : Fin 3, A (unitVector i) i := by
  simp [traceMap]

private theorem fderiv_complexifyComp {φ : Space → Space} (hφ : IsTestField φ) (x : Space) :
    fderiv ℝ (fun x => complexifyVec (φ x)) x = complexifyVec.comp (fderiv ℝ φ x) :=
  (complexifyVec.hasFDerivAt.comp x ((hφ.1.differentiable (by simp)) x).hasFDerivAt).fderiv

private theorem divergence_symbolOf {φ : Space → Space} (hφ : IsTestField φ) (ξ : Space) :
    ∑ i, ((ξ i : ℝ) : ℂ) * symbolOf φ ξ i = 0 := by
  set g : Space → CSpace := fun x => complexifyVec (φ x)
  have hint : Integrable g := (testRapid hφ).integrable
  have hdiff : Differentiable ℝ g := (contDiff_complexifyComp hφ).differentiable (by simp)
  have hdint : Integrable (fderiv ℝ g) :=
    ((contDiff_complexifyComp hφ).continuous_fderiv (by simp)).integrable_of_hasCompactSupport
      ((hasCompactSupport_complexifyComp hφ).fderiv ℝ)
  have hF := congrFun (Real.fourier_fderiv hint hdiff hdint) ξ
  have hi : Integrable (fun v : Space => 𝐞 (-⟪v, ξ⟫) • fderiv ℝ g v) := by
    rw [Real.fourierIntegral_convergent_iff]
    exact hdint
  have hL := congrArg traceMap hF
  rw [Real.fourier_eq, ← traceMap.integral_comp_comm hi] at hL
  have hzero : ∀ v, traceMap (𝐞 (-⟪v, ξ⟫) • fderiv ℝ g v) = 0 := by
    intro v
    have h0 := hφ.2.2 v
    rw [traceMap_apply]
    simp only [g, fderiv_complexifyComp hφ v]
    simp [complexifyVec, Circle.smul_def, divergenceAt] at h0 ⊢
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, h0, Complex.ofReal_zero, mul_zero]
  simp only [hzero, integral_zero] at hL
  rw [traceMap_apply] at hL
  simp [unitVector] at hL
  simp only [innerSL_apply_apply ℝ, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial] at hL
  rw [← Finset.mul_sum] at hL
  have hne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hs := (mul_eq_zero.mp hL.symm).resolve_left hne
  exact hs

theorem isSolenoidalSymbol_symbolOf {φ : Space → Space} (hφ : IsTestField φ) :
    IsSolenoidalSymbol (symbolOf φ) := fun ξ =>
  ⟨divergence_symbolOf hφ ξ, freqTr_neg_complexify hφ ξ⟩

private theorem hasTemperateGrowth_hsWeight (m : ℕ) : Function.HasTemperateGrowth (hsWeight m) :=
  ((Function.HasTemperateGrowth.const (1 : ℝ)).add (Function.hasTemperateGrowth_norm_sq Space)).pow m

theorem hsNormSq_symbolOf_lt_top {φ : Space → Space} (hφ : IsTestField φ) (m : ℕ) :
    hsNormSq m (symbolOf φ) < ⊤ := by
  rw [symbolOf_eq_freqTr hφ]
  set g := testSymbol hφ
  set h := SchwartzMap.smulLeftCLM CSpace (hsWeight m) g
  obtain ⟨C, -, hC⟩ := g.decay 0 0
  have hbd : ∀ ξ, ‖g ξ‖ ≤ C := fun ξ => by simpa using hC ξ
  have hint : Integrable (fun ξ => ‖h ξ‖ * ‖g ξ‖) :=
    h.integrable.norm.mul_bdd g.continuous.norm.aestronglyMeasurable
      (Eventually.of_forall fun ξ => by simpa using hbd ξ)
  have hw : ∀ ξ, 0 ≤ hsWeight m ξ := fun ξ => by unfold hsWeight; positivity
  have heq : ∀ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖g ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖h ξ‖ * ‖g ξ‖) := by
    intro ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_hsWeight m), norm_smul,
      Real.norm_of_nonneg (hw ξ), mul_assoc, ENNReal.ofReal_mul (hw ξ), ← ofReal_norm, sq,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
  unfold hsNormSq
  simp_rw [heq]
  exact hint.lintegral_lt_top

theorem physField_symbolOf {φ : Space → Space} (hφ : IsTestField φ) : physField (symbolOf φ) = φ := by
  have hint : Integrable (fun x => complexifyVec (φ x)) := (testRapid hφ).integrable
  have hFint : Integrable (symbolOf φ) := by
    rw [symbolOf_eq_freqTr hφ]
    exact (testSymbol hφ).integrable
  have hinv := Continuous.fourierInv_fourier_eq (contDiff_complexifyComp hφ).continuous hint hFint
  funext x
  rw [physField, symbolOf, hinv]
  ext i
  simp [realVec, complexifyVec]

end Breakdown.SmoothFlow
