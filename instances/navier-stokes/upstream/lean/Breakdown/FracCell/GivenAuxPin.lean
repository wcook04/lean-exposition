import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxPinCore

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open SteadyCert

private theorem pinWeakScalar (g : Space → ℝ) {K : NNReal} (hg : LipschitzWith K g)
    (Dg : Space → (Space →L[ℝ] ℝ)) (hD : ∀ᵐ y ∂volume, HasFDerivAt g (Dg y) y)
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (v : Space) :
    ∫ y, fderiv ℝ φ y v * g y = -∫ y, φ y * Dg y v := by
  obtain ⟨Kφ, hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2 hφ.1 (by simp)
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have R := hg.integral_lineDeriv_mul_eq (μ := volume) hφL hφ.2 v
  have h1 : (fun x => lineDeriv ℝ φ x (-v) * g x) = fun x => -(fderiv ℝ φ x v * g x) := by
    funext x
    rw [lineDeriv_neg, (hφd x).lineDeriv_eq_fderiv]
    ring
  have h2 : (fun x => lineDeriv ℝ g x v * φ x) =ᵐ[volume] fun x => φ x * Dg x v := by
    filter_upwards [hD] with x hx
    rw [(hx.hasLineDerivAt v).lineDeriv, mul_comm]
  rw [h1, integral_congr_ae h2, integral_neg] at R
  rw [R, neg_neg]

private theorem pinWeakSlope (g : Space → Space) {K : NNReal} (hg : LipschitzWith K g)
    (Dg : Space → (Space →L[ℝ] Space)) (hDm : AEStronglyMeasurable Dg volume) {C : ℝ}
    (hDb : ∀ᵐ y ∂volume, ‖Dg y‖ ≤ C) (hD : ∀ᵐ y ∂volume, HasFDerivAt g (Dg y) y)
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (j : Fin 3) :
    ∫ y, (fderiv ℝ φ y (unitVector j)) • g y = -∫ y, φ y • Dg y (unitVector j) := by
  have hφc : Continuous φ := hφ.1.continuous
  have hI1 : Integrable (fun y => (fderiv ℝ φ y (unitVector j)) • g y) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).smul hg.continuous
    · exact (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right
  have hI2 : Integrable (fun y => φ y • Dg y (unitVector j)) volume := by
    have hφi : Integrable φ volume := hφc.integrable_of_hasCompactSupport hφ.2
    refine hφi.smul_bdd (C * ‖unitVector j‖) ?_ ?_
    · exact (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hDm
    · filter_upwards [hDb] with y hy
      exact (Dg y).le_of_opNorm_le hy _
  have key : ∀ c : Fin 3, ∫ y, fderiv ℝ φ y (unitVector j) * g y c = -∫ y, φ y * Dg y (unitVector j) c := by
    intro c
    have hgc : LipschitzWith _ (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y)) :=
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ).lipschitz.comp hg
    have hDc : ∀ᵐ y ∂volume, HasFDerivAt (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y))
        ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).comp (Dg y)) y := by
      filter_upwards [hD] with x hx
      exact ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt).comp x hx
    have := pinWeakScalar _ hgc _ hDc φ hφ (unitVector j)
    simpa using this
  ext c
  have e1 := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hI1
  have e2 := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integral_comp_comm hI2
  simp only [EuclideanSpace.proj] at e1 e2
  simp at e1 e2 ⊢
  rw [← e1, ← e2]
  simpa [smul_eq_mul] using key c

private theorem pinWeakVec (g : Space → Space) {K : NNReal} (hg : LipschitzWith K g)
    (Dg : Space → (Space →L[ℝ] Space)) (hDm : AEStronglyMeasurable Dg volume) {C : ℝ}
    (hDb : ∀ᵐ y ∂volume, ‖Dg y‖ ≤ C) (hD : ∀ᵐ y ∂volume, HasFDerivAt g (Dg y) y)
    (Φ : Space → Space) (hΦ : IsTestVectorField Φ) (v : Space) :
    ∫ y, inner ℝ (g y) (fderiv ℝ Φ y v) = -∫ y, inner ℝ (Dg y v) (Φ y) := by
  have hΦd : Differentiable ℝ Φ := hΦ.1.differentiable (by simp)
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hcomp : ∀ c : Fin 3, IsTestScalar (fun y => Φ y c) := by
    intro c
    refine ⟨?_, ?_⟩
    · exact (EuclideanSpace.proj c : Space →L[ℝ] ℝ).contDiff.comp hΦ.1
    · exact hΦ.2.comp_left (g := fun w : Space => w c) (by simp)
  have hder : ∀ c : Fin 3, ∀ y, fderiv ℝ (fun y => Φ y c) y v = fderiv ℝ Φ y v c := by
    intro c y
    have := ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hΦd y).hasFDerivAt).fderiv
    simp only [Function.comp_def] at this
    rw [show (fun y => Φ y c) = fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (Φ y) from rfl, this]
    simp
  have hint1 : ∀ c : Fin 3, Integrable (fun y => g y c * fderiv ℝ Φ y v c) volume := by
    intro c
    apply Continuous.integrable_of_hasCompactSupport
    · have h1 : Continuous fun y => g y c :=
        (EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp hg.continuous
      have h2 : Continuous fun y => fderiv ℝ Φ y v c :=
        (EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp
          ((hΦ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
      exact h1.mul h2
    · exact ((hΦ.2.fderiv_apply (𝕜 := ℝ) v).comp_left (g := fun w : Space => w c) (by simp)).mul_left
  have hint2 : ∀ c : Fin 3, Integrable (fun y => Dg y v c * Φ y c) volume := by
    intro c
    have hφi : Integrable (fun y => Φ y c) volume :=
      ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp hΦc).integrable_of_hasCompactSupport (hcomp c).2
    have := hφi.smul_bdd (C * ‖v‖) (f := fun y => Dg y v c) ?_ ?_
    · convert this using 1
      funext y
      simp [mul_comm]
    · exact (EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        ((ContinuousLinearMap.apply ℝ Space v).continuous.comp_aestronglyMeasurable hDm)
    · filter_upwards [hDb] with y hy
      calc ‖Dg y v c‖ ≤ ‖Dg y v‖ := by
            exact PiLp.norm_apply_le (Dg y v) c
        _ ≤ C * ‖v‖ := (Dg y).le_of_opNorm_le hy _
  have key : ∀ c : Fin 3, ∫ y, g y c * fderiv ℝ Φ y v c = -∫ y, Dg y v c * Φ y c := by
    intro c
    have hgc : LipschitzWith _ (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y)) :=
      (EuclideanSpace.proj c : Space →L[ℝ] ℝ).lipschitz.comp hg
    have hDc : ∀ᵐ y ∂volume, HasFDerivAt (fun y => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (g y))
        ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).comp (Dg y)) y := by
      filter_upwards [hD] with x hx
      exact ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt).comp x hx
    have := pinWeakScalar _ hgc _ hDc (fun y => Φ y c) (hcomp c) v
    simp only [hder] at this
    simpa [mul_comm] using this
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [integral_finsetSum _ (fun c _ => by simpa [mul_comm] using hint1 c),
    integral_finsetSum _ (fun c _ => by simpa [mul_comm] using hint2 c), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simpa [mul_comm] using key c

private theorem pinSecondBound (f : Space → Space) {K : NNReal} (hG : LipschitzWith K (fun y => fderiv ℝ f y)) :
    AEStronglyMeasurable (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) volume ∧
      IsWeakSecondDerivOf (fun y => fderiv ℝ f y) (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) ∧
      ∀ y, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ K := by
  have hHm : AEStronglyMeasurable (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) volume :=
    (measurable_fderiv ℝ _).aestronglyMeasurable
  have hHb : ∀ y, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hG
  refine ⟨hHm, ?_, hHb⟩
  intro φ hφ i j
  have hGd : ∀ᵐ y ∂volume, HasFDerivAt (fun z => fderiv ℝ f z) (fderiv ℝ (fun z => fderiv ℝ f z) y) y :=
    (hG.ae_differentiableAt (μ := volume)).mono (fun y h => h.hasFDerivAt)
  let Lc : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space (unitVector i)
  have hgL : LipschitzWith _ (fun y => fderiv ℝ f y (unitVector i)) := Lc.lipschitz.comp hG
  have hm : AEStronglyMeasurable (fun y => Lc.comp (fderiv ℝ (fun z => fderiv ℝ f z) y)) volume :=
    ((ContinuousLinearMap.compL ℝ Space (Space →L[ℝ] Space) Space) Lc).continuous.comp_aestronglyMeasurable hHm
  have hb : ∀ᵐ y ∂volume, ‖Lc.comp (fderiv ℝ (fun z => fderiv ℝ f z) y)‖ ≤ ‖Lc‖ * K :=
    ae_of_all _ (fun y => (Lc.opNorm_comp_le _).trans (by gcongr; exact hHb y))
  have hd : ∀ᵐ y ∂volume, HasFDerivAt (fun y => fderiv ℝ f y (unitVector i))
      (Lc.comp (fderiv ℝ (fun z => fderiv ℝ f z) y)) y :=
    hGd.mono (fun y h => Lc.hasFDerivAt.comp y h)
  exact pinWeakSlope _ hgL _ hm hb hd φ hφ j

private theorem pinTrace (f : Space → Space) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {K : NNReal}
    (hG : LipschitzWith K (fun y => fderiv ℝ f y)) :
    CellCert.Reduction.IsWeakNegTraceOf f
      (fun y => -∑ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ f z) y (unitVector j) (unitVector j)) := by
  intro Φ hΦ
  obtain ⟨Kf, hfL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)
  have hfd : ∀ y, HasFDerivAt f (fderiv ℝ f y) y := fun y => (hf.differentiable (by simp) y).hasFDerivAt
  have hHm : AEStronglyMeasurable (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y) volume :=
    (measurable_fderiv ℝ _).aestronglyMeasurable
  have hHb : ∀ y, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hG
  have hGd : ∀ᵐ y ∂volume, HasFDerivAt (fun z => fderiv ℝ f z) (fderiv ℝ (fun z => fderiv ℝ f z) y) y :=
    (hG.ae_differentiableAt (μ := volume)).mono (fun y h => h.hasFDerivAt)
  have hΦ1 : ContDiff ℝ ∞ (fun z => fderiv ℝ Φ z) := hΦ.1.fderiv_right (m := ∞) (by simp)
  have hΦc : Continuous Φ := hΦ.1.continuous
  have step : ∀ j : Fin 3, ∫ y, inner ℝ (f y) (fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector j)) y (unitVector j)) =
      ∫ y, inner ℝ (fderiv ℝ (fun z => fderiv ℝ f z) y (unitVector j) (unitVector j)) (Φ y) := by
    intro j
    have hΨ : IsTestVectorField (fun z => fderiv ℝ Φ z (unitVector j)) :=
      ⟨hΦ1.clm_apply contDiff_const, hΦ.2.fderiv_apply (𝕜 := ℝ) _⟩
    have s1 := pinWeakVec f hfL (fun y => fderiv ℝ f y) (measurable_fderiv ℝ f).aestronglyMeasurable (C := Kf)
      (ae_of_all _ fun y => norm_fderiv_le_of_lipschitz ℝ hfL) (ae_of_all _ hfd) _ hΨ (unitVector j)
    let Lc : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space (unitVector j)
    have hgL : LipschitzWith _ (fun y => fderiv ℝ f y (unitVector j)) := Lc.lipschitz.comp hG
    have hm : AEStronglyMeasurable (fun y => Lc.comp (fderiv ℝ (fun z => fderiv ℝ f z) y)) volume :=
      ((ContinuousLinearMap.compL ℝ Space (Space →L[ℝ] Space) Space) Lc).continuous.comp_aestronglyMeasurable hHm
    have hb : ∀ᵐ y ∂volume, ‖Lc.comp (fderiv ℝ (fun z => fderiv ℝ f z) y)‖ ≤ ‖Lc‖ * K :=
      ae_of_all _ (fun y => (Lc.opNorm_comp_le _).trans (by gcongr; exact hHb y))
    have hd : ∀ᵐ y ∂volume, HasFDerivAt (fun y => fderiv ℝ f y (unitVector j))
        (Lc.comp (fderiv ℝ (fun z => fderiv ℝ f z) y)) y :=
      hGd.mono (fun y h => Lc.hasFDerivAt.comp y h)
    have s2 := pinWeakVec _ hgL _ hm hb hd Φ hΦ (unitVector j)
    rw [s1]
    rw [s2, neg_neg]
    rfl
  have hssp : ∀ y, sumSecondPartialsAt Φ y = ∑ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector j)) y (unitVector j) := by
    intro y
    simp only [sumSecondPartialsAt, iteratedFDeriv_two_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hd1 : DifferentiableAt ℝ (fun z => fderiv ℝ Φ z) y := (hΦ1.differentiable (by simp)) y
    rw [fderiv_clm_apply hd1 (differentiableAt_const _)]
    simp
  have hI1 : ∀ j : Fin 3, Integrable
      (fun y => inner ℝ (f y) (fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector j)) y (unitVector j))) volume := by
    intro j
    apply Continuous.integrable_of_hasCompactSupport
    · have : Continuous fun y => fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector j)) y (unitVector j) :=
        ((hΦ1.clm_apply contDiff_const).continuous_fderiv (by simp)).clm_apply continuous_const
      exact hf.continuous.inner this
    · refine hc.mono (fun y hy => ?_)
      intro h
      apply hy
      simp [h]
  have hI2 : ∀ j : Fin 3, Integrable
      (fun y => inner ℝ (fderiv ℝ (fun z => fderiv ℝ f z) y (unitVector j) (unitVector j)) (Φ y)) volume := by
    intro j
    have hΦi : Integrable (fun y => ‖Φ y‖) volume :=
      (hΦc.integrable_of_hasCompactSupport hΦ.2).norm
    refine Integrable.mono' (hΦi.const_mul (K * ‖unitVector j‖ * ‖unitVector j‖)) ?_ ?_
    · have hm2 : AEStronglyMeasurable (fun y => fderiv ℝ (fun z => fderiv ℝ f z) y (unitVector j) (unitVector j)) volume :=
        ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
          (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous).comp_aestronglyMeasurable hHm
      exact hm2.inner hΦc.aestronglyMeasurable
    · refine ae_of_all _ (fun y => ?_)
      refine (norm_inner_le_norm _ _).trans ?_
      gcongr
      refine ((fderiv ℝ (fun z => fderiv ℝ f z) y).le_opNorm₂ _ _).trans ?_
      gcongr
      exact hHb y
  calc ∫ y, inner ℝ (f y) (-sumSecondPartialsAt Φ y)
      = -∑ j : Fin 3, ∫ y, inner ℝ (f y) (fderiv ℝ (fun z => fderiv ℝ Φ z (unitVector j)) y (unitVector j)) := by
        simp only [hssp, inner_neg_right, inner_sum, integral_neg]
        rw [integral_finsetSum _ (fun j _ => hI1 j)]
    _ = -∑ j : Fin 3, ∫ y, inner ℝ (fderiv ℝ (fun z => fderiv ℝ f z) y (unitVector j) (unitVector j)) (Φ y) := by
        simp only [step]
    _ = ∫ y, inner ℝ (-∑ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ f z) y (unitVector j) (unitVector j)) (Φ y) := by
        simp only [inner_neg_left, sum_inner, integral_neg]
        rw [integral_finsetSum _ (fun j _ => hI2 j)]

end FracInternal

namespace CellCert

namespace GivenFields

open SteadyCert FracInternal

theorem smoothPin_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A) (l : Fin k) :
    AEStronglyMeasurable (A.smoothPinField P l) volume ∧ Integrable (fun y => entrySq (A.smoothPinField P l y)) ∧
      ContDiff ℝ 1 (A.pinPotentialField P l) ∧ HasCompactSupport (A.pinPotentialField P l) ∧
      (∃ H : Space → (Space →L[ℝ] Space →L[ℝ] Space), IsWeakSecondDerivOf (fun y => fderiv ℝ (A.pinPotentialField P l) y) H ∧
        AEStronglyMeasurable H volume ∧ ∃ C : ℝ, ∀ᵐ y ∂volume, ‖H y‖ ≤ C) := by
  obtain ⟨e, he⟩ := hA.pin_shape l
  obtain ⟨h1, h2, K, hG⟩ := compactField_regular P hP (A.pinData l) he A.phaseBase
  change ContDiff ℝ 1 (A.pinPotentialField P l) at h1
  change HasCompactSupport (A.pinPotentialField P l) at h2
  change LipschitzWith K (fun y => fderiv ℝ (A.pinPotentialField P l) y) at hG
  obtain ⟨hHm, hHw, hHb⟩ := pinSecondBound _ hG
  have hsp : A.smoothPinField P l = fun y => (A.pinScale l)⁻¹ • fderiv ℝ (A.pinPotentialField P l) y := rfl
  have hc : Continuous (fun y => (A.pinScale l)⁻¹ • fderiv ℝ (A.pinPotentialField P l) y) :=
    (continuous_const_smul (A.pinScale l)⁻¹).comp hG.continuous
  refine ⟨?_, ?_, h1, h2, ⟨_, hHw, hHm, K, ae_of_all _ hHb⟩⟩
  · rw [hsp]
    exact hc.aestronglyMeasurable
  · rw [hsp]
    apply Continuous.integrable_of_hasCompactSupport
    · have hi : ∀ i : Fin 3, Continuous
          (fun y => ‖((A.pinScale l)⁻¹ • fderiv ℝ (A.pinPotentialField P l) y) (unitVector i)‖ ^ 2) :=
        fun i => (hc.clm_apply continuous_const).norm.pow 2
      exact continuous_finsetSum _ (fun i _ => hi i)
    · exact (h2.fderiv (𝕜 := ℝ)).comp_left (g := fun T => entrySq ((A.pinScale l)⁻¹ • T)) (by simp [entrySq])

theorem pinRegular_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (l : Fin k) :
    ContDiff ℝ 1 (A.pinPotentialField P l) ∧ HasCompactSupport (A.pinPotentialField P l) ∧
      ∃ H : Space → (Space →L[ℝ] Space →L[ℝ] Space), ∃ L : Space → Space,
        AEStronglyMeasurable H volume ∧ IsWeakSecondDerivOf (fun y => fderiv ℝ (A.pinPotentialField P l) y) H ∧
        (∃ C : ℝ, ∀ᵐ y ∂volume, ‖H y‖ ≤ C) ∧
        CellCert.Reduction.IsWeakNegTraceOf (A.pinPotentialField P l) L ∧ AEStronglyMeasurable L volume ∧
        (∃ C : ℝ, ∀ᵐ y ∂volume, ‖L y‖ ≤ C) := by
  obtain ⟨e, he⟩ := hA.pin_shape l
  obtain ⟨h1, h2, K, hG⟩ := compactField_regular P hP (A.pinData l) he A.phaseBase
  change ContDiff ℝ 1 (A.pinPotentialField P l) at h1
  change HasCompactSupport (A.pinPotentialField P l) at h2
  change LipschitzWith K (fun y => fderiv ℝ (A.pinPotentialField P l) y) at hG
  obtain ⟨hHm, hHw, hHb⟩ := pinSecondBound _ hG
  refine ⟨h1, h2, _, _, hHm, hHw, ⟨K, ae_of_all _ hHb⟩, pinTrace _ h1 h2 hG, ?_, ⟨3 * K, ae_of_all _ (fun y => ?_)⟩⟩
  · have hcont : Continuous fun T : Space →L[ℝ] Space →L[ℝ] Space => -∑ j : Fin 3, T (unitVector j) (unitVector j) :=
      (continuous_finsetSum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const).neg
    exact hcont.comp_aestronglyMeasurable hHm
  · rw [norm_neg]
    refine (norm_sum_le _ _).trans ?_
    have hj : ∀ j : Fin 3, ‖fderiv ℝ (fun z => fderiv ℝ (A.pinPotentialField P l) z) y (unitVector j) (unitVector j)‖ ≤ K := by
      intro j
      refine ((fderiv ℝ (fun z => fderiv ℝ (A.pinPotentialField P l) z) y).le_opNorm₂ _ _).trans ?_
      simp [unitVector, hHb y]
    calc ∑ j : Fin 3, ‖fderiv ℝ (fun z => fderiv ℝ (A.pinPotentialField P l) z) y (unitVector j) (unitVector j)‖
        ≤ ∑ j : Fin 3, (K : ℝ) := Finset.sum_le_sum fun j _ => hj j
      _ = 3 * K := by simp

theorem phase_eq_of {k N : ℕ} (D : ProfileData k) (A : AuxData k) (c : FracCellData k N)
    (hI : IsAuxInstance D A c) : ∀ p, A.phase p = D.phase p := by
  intro p
  have hs : ∑ j, A.phaseSlope j * p j = -(2 * D.power * (D.chart.m : ℝ)) * ∑ j, D.rateSlope j * p j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hI.phaseSlope_eq j]
    ring
  simp only [AuxData.phase, hI.phaseBase_eq, hs, ProfileData.phase, ProfileData.rate]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem pinField_of {k N : ℕ} (D : ProfileData k) (A : AuxData k) (c : FracCellData k N)
    (hI : IsAuxInstance D A c) :
    ∀ l y, c.smoothPin l y = (1 / A.pinScale l) • fderiv ℝ (A.pinPotentialField D.chart l) y := by
  intro l y
  rw [hI.smoothPin_eq l]
  simp [AuxData.smoothPinField]

end GivenFields

end CellCert

end Breakdown
