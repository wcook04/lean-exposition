import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.Cert.CoercivePieceDensityPassageRight
import Breakdown.Cert.CoerciveDensityPassageEnergy
import Breakdown.Cert.CoerciveDensityPassagePairing
import Breakdown.Cert.CoerciveDensityPassageMeasurable
import Breakdown.Cert.CoerciveDensityPassageNegative
import Breakdown.Cert.CoerciveDensityPassageLiminf
import Breakdown.Cert.CoerciveFrequencySeminormBound
import Breakdown.Cert.CoercivePassageCommon
import Breakdown.Cert.CoerciveDensityPassageLinear
import Breakdown.Cert.CoerciveDensityPassageRest
import Breakdown.Cert.CoerciveDensityPassageModes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

namespace Breakdown

namespace Coercive

namespace Internal

namespace DensityPassage

open PassageLimit

section Setting

variable {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) {k : ℕ}
  (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space)
  {w₀ epsSup epsGradSup ratio : ℝ}
  (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hV : b.IsValid m W)
  (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
  (hWd : ∀ σ y, divergenceAt (W σ) y = 0)
  (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
  (hwB : ∃ B, ∀ y, w y ≤ B)
  (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
  (hactp : ∀ i, IsTimePeriodic (act i))
  (hactf : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
  (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
  (hv : IsPerturbation Γ P v G H g)
  (u : ℕ → ℝ → Space → Space) (hu : IsSmoothApproximation P v G H g u)
  (κ : Fin k → ℝ) (F : ℝ → Space → Space)
  (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
  (hFf : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hF : IsRightSide W act κ v G g F)
  (M : ℝ → Space → Space) (hM : m.IsMultiplierField v G H M)

include hA hV hWs hWp hWd hWdec hwB hactm hactp hactf hv hu hFm hFp hFf hF hM

theorem difference_frequency_converges (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    Tendsto (fun n => m.frequencySeminormSq P (fun σ y => u n σ y - v σ y)) atTop (𝓝 0) ∧
      Tendsto (fun n => (m.frequencySeminormSq P (u n)).toReal) atTop
        (𝓝 (m.frequencySeminormSq P v).toReal) := by
  obtain ⟨B, hB⟩ := hA.muW_decay
  obtain ⟨R, hR⟩ := hA.rate_bounded
  exact FrequencyBound.frequencySeminormSq_tendsto_of_approximation m hPars hDer hRot hSP hv hA.period_pos
    (B := B) (R := R) (fun c y => ⟨(hB c y).1, (hB c y).2.1⟩) hR
    (fun c => (hA.muW_increment c).choose_spec.continuous.measurable) hA.rate_measurable hu

theorem multiplier_difference_test (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) (n : ℕ)
    (M' : ℝ → Space → Space)
    (hM' : m.IsMultiplierField (fun σ y => u n σ y - v σ y) (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y) M') (ψ : ℝ → Space → Space) (hψ : IsPeriodicTestField ψ) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (Mn n σ y - M σ y - M' σ y) (ψ σ y) = 0 := by
  exact DensityPassageLinear.multiplier_difference_pairing hPars hA (hSP P (u n) (hu.1 n)) hv (hMn n) hM hM' hψ

theorem multiplier_difference_orthogonal (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) (n : ℕ)
    (M' : ℝ → Space → Space)
    (hM' : m.IsMultiplierField (fun σ y => u n σ y - v σ y) (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y) M') :
    (∀ q, IsPeriodicTestPotential q → ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        inner ℝ (Mn n σ y - M σ y - M' σ y) (gradientAt (q σ) y) = 0) ∧
      ∀ ψ, IsPeriodicTestField ψ → ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        inner ℝ (Mn n σ y - M σ y - M' σ y) (ψ σ y) = 0 := by
  have hD2 := periodL2_sub_of (hMn n).1 hM.1 (hMn n).2.2.1 hM.2.2.1
  have hX2 : periodLIntegral (fun σ y => ‖Mn n σ y - M σ y - M' σ y‖ ^ 2) < ⊤ :=
    periodL2_sub_of ((hMn n).1.sub hM.1) hM'.1 hD2 hM'.2.2.1
  refine ⟨fun q hq => ?_, fun ψ hψ => multiplier_difference_test m P b w Γ W act hA hV hWs hWp hWd hWdec hwB
    hactm hactp hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP Mn hMn n M' hM' ψ hψ⟩
  have hgq := PairingSplitInternal.gradient_square hq
  have e1 := PassageLimit.periodPairing_sub_right (A := fun σ y => gradientAt (q σ) y)
    (B := fun σ y => Mn n σ y - M σ y) (B' := M') hgq.1 ((hMn n).1.sub hM.1) hM'.1 hgq.2.2 hD2 hM'.2.2.1 hX2
  have e2 := PassageLimit.periodPairing_sub_right (A := fun σ y => gradientAt (q σ) y)
    (B := Mn n) (B' := M) hgq.1 (hMn n).1 hM.1 hgq.2.2 (hMn n).2.2.1 hM.2.2.1 hD2
  have g1 : periodPairing (fun σ y => gradientAt (q σ) y) (Mn n) = 0 := by
    rw [PassageLimit.periodPairing_comm]
    exact (hMn n).2.2.2.1 q hq
  have g2 : periodPairing (fun σ y => gradientAt (q σ) y) M = 0 := by
    rw [PassageLimit.periodPairing_comm]
    exact hM.2.2.2.1 q hq
  have g3 : periodPairing (fun σ y => gradientAt (q σ) y) M' = 0 := by
    rw [PassageLimit.periodPairing_comm]
    exact hM'.2.2.2.1 q hq
  show periodPairing (fun σ y => Mn n σ y - M σ y - M' σ y) (fun σ y => gradientAt (q σ) y) = 0
  rw [PassageLimit.periodPairing_comm, ← e1, ← e2, g1, g2, g3]
  ring

theorem multiplier_difference_ae (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) (n : ℕ)
    (M' : ℝ → Space → Space)
    (hM' : m.IsMultiplierField (fun σ y => u n σ y - v σ y) (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y) M') :
    ∀ᵐ z : ℝ × Space, Mn n z.1 z.2 - M z.1 z.2 = M' z.1 z.2 := by
  obtain ⟨hgr, hte⟩ := multiplier_difference_orthogonal m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm
    hactp hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP Mn hMn n M' hM'
  have hXm : AEStronglyMeasurable (fun z : ℝ × Space => Mn n z.1 z.2 - M z.1 z.2 - M' z.1 z.2) volume :=
    ((hMn n).1.sub hM.1).sub hM'.1
  have hXp : IsTimePeriodic (fun σ y => Mn n σ y - M σ y - M' σ y) := fun σ y => by
    simp only [(hMn n).2.1 σ y, hM.2.1 σ y, hM'.2.1 σ y]
  have hX2 : periodLIntegral (fun σ y => ‖Mn n σ y - M σ y - M' σ y‖ ^ 2) < ⊤ :=
    periodL2_sub_of ((hMn n).1.sub hM.1) hM'.1
      (periodL2_sub_of (hMn n).1 hM.1 (hMn n).2.2.1 hM.2.2.1) hM'.2.2.1
  obtain ⟨Q, -, -, -, huniq, -⟩ := hSolenoidal (fun _ _ => 0) aestronglyMeasurable_const (fun _ _ => rfl)
    (by simp [periodLIntegral])
  have h1 := huniq (fun σ y => Mn n σ y - M σ y - M' σ y)
    ⟨hXm, hXp, hX2, hgr, fun ψ hψ => by rw [hte ψ hψ]; simp⟩
  have h0 := huniq (fun _ _ => 0) ⟨aestronglyMeasurable_const, fun _ _ => rfl, by simp [periodLIntegral],
    fun q _ => by simp, fun ψ _ => rfl⟩
  filter_upwards [h1, h0] with z hz1 hz0
  rw [← hz0] at hz1
  exact sub_eq_zero.1 hz1

theorem field_converges (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hField : ModeFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨Bw, hBw⟩ := hwB
  have hDn := fun n => FrequencyBound.isPerturbation_sub (hSP P (u n) (hu.1 n)) hv
  have hex := fun n => (hField m P b w ∅ hA ⟨Bw, hBw⟩ _ _ _ _ (hDn n)).2
  choose M' hM' hb using hex
  have hae := fun n => multiplier_difference_ae m P b w Γ W act hA hV hWs hWp hWd hWdec ⟨Bw, hBw⟩ hactm hactp
    hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSolenoidal hSP Mn hMn n (M' n) (hM' n)
  have hSPn := fun n => hSP P (u n) (hu.1 n)
  have hE : Tendsto (fun n => weightedEnergy w (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y)) atTop (𝓝 0) := by
    have h := weightedEnergy_tendsto (B := Bw) (G := fun _ _ => 0) (H := fun _ _ => 0)
      (Gn := fun n σ y => gradField (u n) σ y - G σ y) (Hn := fun n σ y => secondDerivField (u n) σ y - H σ y)
      hA.weight_measurable (fun y => hA.weight_pos.le.trans (hA.weight_lower y)) hBw
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun n => (hSPn n).measurable_gradient.sub hv.measurable_gradient)
      (fun n => (hSPn n).measurable_secondDeriv.sub hv.measurable_secondDeriv)
      (by simp [periodLIntegral, matSq]) (by simp [periodLIntegral, secondDerivTrace])
      (by simpa using hu.2.1) (by simpa using hu.2.2.1)
    have h0 : weightedEnergy w (fun _ _ => (0 : Space →L[ℝ] Space)) (fun _ _ => (0 : Space →L[ℝ] Space →L[ℝ] Space))
        = 0 := by
      simp [weightedEnergy, periodLIntegral, matSq, secondDerivTrace]
    rw [h0] at h
    exact h
  have hf := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (difference_frequency_converges m P b w Γ W act hA hV hWs hWp hWd hWdec ⟨Bw, hBw⟩ hactm hactp hactf
      v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP).1)
  rw [ENNReal.toReal_zero] at hf
  have hK : Tendsto (fun n => m.multiplierConstant w₀ epsSup epsGradSup ratio
      * Real.sqrt (m.c * weightedEnergy w (fun σ y => gradField (u n) σ y - G σ y)
        (fun σ y => secondDerivField (u n) σ y - H σ y)
        + m.cμ * (m.frequencySeminormSq P (fun σ y => u n σ y - v σ y)).toReal)) atTop (𝓝 0) := by
    have h := ((hE.const_mul m.c).add (hf.const_mul m.cμ)).sqrt.const_mul (m.multiplierConstant w₀ epsSup epsGradSup ratio)
    simpa using h
  have hN : ∀ n, periodNorm (fun σ y => Mn n σ y - M σ y) = periodNorm (M' n) := fun n =>
    PairingSplitInternal.periodNorm_congr ((hMn n).1.sub hM.1) (hM' n).1 (hae n)
  have hNt : Tendsto (fun n => periodNorm (fun σ y => Mn n σ y - M σ y)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK (fun n => Real.sqrt_nonneg _)
      (fun n => ?_)
    rw [hN n]
    exact hb n
  have hfin := fun n => periodL2_sub_of (hMn n).1 hM.1 (hMn n).2.2.1 hM.2.2.1
  have eq : ∀ n, periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)
      = ENNReal.ofReal (periodNorm (fun σ y => Mn n σ y - M σ y) ^ 2) := fun n => by
    unfold periodNorm
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin n).ne]
  simp only [eq]
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp (hNt.pow 2)
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, ENNReal.ofReal_zero] at h2
  exact h2

theorem smooth_right_square_integrable (hSP : SmoothPerturbationIsPerturbationHolds) (n : ℕ) :
    AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W (u n) z.1 z.2 + ∑ i, κ i • act i z.1 z.2)
        volume ∧
      periodLIntegral (fun σ y => ‖smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y‖ ^ 2) < ⊤ := by
  exact smoothRight_memL2 κ hSP (hu.1 n) hWs hWdec hactm hactf

theorem right_model_square_integrable :
    AEStronglyMeasurable (fun z : ℝ × Space => rightSideLimit W act κ v G H g z.1 z.2) volume ∧
      periodLIntegral (fun σ y => ‖rightSideLimit W act κ v G H g σ y‖ ^ 2) < ⊤ := by
  exact rightSideLimit_memL2 κ hv hWs hWdec hactm hactf (weightedVelocity_lt_top hv hu)

theorem smooth_right_converges (hSP : SmoothPerturbationIsPerturbationHolds) :
    Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖(smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) - rightSideLimit W act κ v G H g σ y‖ ^ 2))
      atTop (𝓝 0) := by
  exact smoothRight_tendsto κ hSP hv hu hWdec

theorem pairing_right_model (hSolenoidal : SolenoidalModeHolds) :
    periodPairing F M = periodPairing (rightSideLimit W act κ v G H g) M := by
  exact pairing_rightSideLimit_eq hSolenoidal κ hv hWs hWp hWdec hactm hactp hactf (weightedVelocity_lt_top hv hu)
    hFm hFp hFf hF hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1

theorem right_pairing_converges (hSolenoidal : SolenoidalModeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n))
    (hMc : Tendsto (fun n => periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n => periodPairing (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n))
      atTop (𝓝 (periodPairing F M)) := by
  have hS := fun n => smooth_right_square_integrable m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm
    hactp hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hSP n
  have hR := right_model_square_integrable m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm
    hactp hactf v G H g hv u hu κ F hFm hFp hFf hF M hM
  have hC := smooth_right_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm
    hactp hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hSP
  rw [pairing_right_model m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hSolenoidal]
  exact periodPairing_tendsto
    (A := fun n σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y)
    (B := Mn) (A₀ := rightSideLimit W act κ v G H g) (B₀ := M)
    (fun n => (hS n).1) (fun n => (hS n).2) hR.1 hR.2 (fun n => (hMn n).1) (fun n => (hMn n).2.2.1)
    hM.1 hM.2.2.1 hC hMc

theorem action_pairing_converges (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n))
    (hMc : Tendsto (fun n => periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)) atTop (𝓝 0)) (i : Fin k) :
    Tendsto (fun n => periodPairing (act i) (Mn n)) atTop (𝓝 (periodPairing (act i) M)) := by
  exact periodPairing_tendsto_right (A := act i) (B := Mn) (B₀ := M) (hactm i) (hactf i)
    (fun n => (hMn n).1) (fun n => (hMn n).2.2.1) hM.1 hM.2.2.1 hMc

theorem energy_converges (hSP : SmoothPerturbationIsPerturbationHolds) :
    Tendsto (fun n => weightedEnergy w (gradField (u n)) (secondDerivField (u n))) atTop
      (𝓝 (weightedEnergy w G H)) := by
  obtain ⟨B, hB⟩ := hwB
  have hSPn := fun n => hSP P (u n) (hu.1 n)
  exact weightedEnergy_tendsto (B := B) hA.weight_measurable
    (fun y => hA.weight_pos.le.trans (hA.weight_lower y)) hB hv.measurable_gradient hv.measurable_secondDeriv
    (fun n => (hSPn n).measurable_gradient) (fun n => (hSPn n).measurable_secondDeriv) hv.gradient_finite
    hv.sumSecondPartials_finite hu.2.1 hu.2.2.1

theorem frequency_converges (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hField : ModeFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) :
    Tendsto (fun n => (m.frequencySeminormSq P (u n)).toReal) atTop
      (𝓝 (m.frequencySeminormSq P v).toReal) := by
  exact (difference_frequency_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP).2

theorem gap_converges (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hField : ModeFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => m.multiplierGap P w act (u n) (gradField (u n)) (secondDerivField (u n)) κ
        (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n)) atTop
      (𝓝 (m.multiplierGap P w act v G H κ F M)) := by
  have hMc := field_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hField hSolenoidal hSP Mn hMn
  have h1 := right_pairing_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hSolenoidal hSP Mn hMn hMc
  have h2 := energy_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hSP
  have h3 := frequency_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hField hSolenoidal hSP
  have h4 : ∀ i, Tendsto (fun n => periodPairing (act i) (Mn n)) atTop (𝓝 (periodPairing (act i) M)) :=
    fun i => action_pairing_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
      v G H g hv u hu κ F hFm hFp hFf hF M hM Mn hMn hMc i
  unfold ModeWeights.multiplierGap
  exact ((h1.sub (h2.const_mul _)).sub (h3.const_mul _)).sub
    (tendsto_finsetSum _ fun i _ => (h4 i).const_mul _)

theorem rest_abs_converges (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    (∀ n, AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι z.1 z.2
          - modeRest m w W v G H ι z.1 z.2|)) PairingSplitInternal.periodMeasure) ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W v G H ι σ y|)) < ⊤ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y
          - modeRest m w W v G H ι σ y|)) atTop (𝓝 0) := by
  exact DensityPassageRest.rest_abs_converges_of hPars hSP hA hWs hWp hWdec hwB hv hu

theorem rest_negative_converge (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-modeRest m w W v G H ι σ y)) < ⊤ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
          ENNReal.ofReal (-modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)) atTop
        (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-modeRest m w W v G H ι σ y))) := by
  obtain ⟨h1, h2, h3⟩ := rest_abs_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP
  exact tsum_negPart_tendsto (R := fun n σ y ι => modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)
    (R₀ := fun σ y ι => modeRest m w W v G H ι σ y) h1 h2 h3

theorem stretch_l1_converges (hSP : SmoothPerturbationIsPerturbationHolds) :
    periodLIntegral (fun σ y => |stretchForm W v G σ y|) < ⊤ ∧
      Tendsto (fun n => periodLIntegral (fun σ y =>
        |stretchForm W (u n) (gradField (u n)) σ y - stretchForm W v G σ y|)) atTop (𝓝 0) :=
  ⟨PassageCommon.stretchForm_finite hv hWdec (weightedVelocity_lt_top hv hu),
    PassageCommon.stretchForm_tendsto hSP hv hu hWdec⟩

theorem negative_parts_converge (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => modeRest m w W v G H ι σ y) (fun _ _ => 0) (stretchForm W v G) σ y) < ⊤ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)
          (fun _ _ => 0) (stretchForm W (u n) (gradField (u n))) σ y) atTop
        (𝓝 ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => modeRest m w W v G H ι σ y) (fun _ _ => 0) (stretchForm W v G) σ y))) := by
  have hJv : AEMeasurable (fun z : ℝ × Space => stretchForm W v G z.1 z.2) PairingSplitInternal.periodMeasure :=
    (PieceAbsorb.aem_stretchForm hWs hv.measurable_velocity hv.measurable_gradient).mono_ac SmoothDensity.measure_ac
  have hJn : ∀ n, AEMeasurable (fun z : ℝ × Space => stretchForm W (u n) (gradField (u n)) z.1 z.2)
      PairingSplitInternal.periodMeasure := fun n =>
    (PieceAbsorb.aem_stretchForm hWs (hSP P (u n) (hu.1 n)).measurable_velocity
      (hSP P (u n) (hu.1 n)).measurable_gradient).mono_ac SmoothDensity.measure_ac
  obtain ⟨hs1, hs2⟩ := stretch_l1_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hSP
  obtain ⟨hsf, hst⟩ := negPart_tendsto hJn hJv hs1 hs2
  obtain ⟨hrf, hrt⟩ := rest_negative_converge m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP
  rw [splitRight_integral_eq hJv]
  simp only [splitRight_integral_eq (hJn _)]
  exact ⟨ENNReal.add_lt_top.2 ⟨hrf, hsf⟩, hrt.add hst⟩

theorem left_densities_measurable (hSP : SmoothPerturbationIsPerturbationHolds) (n : ℕ) :
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        AEMeasurable (fun y => splitLeft (fun σ y ι => modePos m P (u n) (gradField (u n)) ι σ y)
          (fun σ y ι => modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y) (fun _ _ => 0)
          (stretchForm W (u n) (gradField (u n))) σ y) volume) ∧
      AEMeasurable (fun σ => ∫⁻ y, splitLeft (fun σ y ι => modePos m P (u n) (gradField (u n)) ι σ y)
          (fun σ y ι => modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y) (fun _ _ => 0)
          (stretchForm W (u n) (gradField (u n))) σ y) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  exact splitLeft_aemeasurable hA hWs hWdec (hu.1 n)

theorem modes_converge_ae (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      (∀ ι, Tendsto (fun n => modePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) atTop
          (𝓝 (modePos m P v G ι σ y))) ∧
        (∀ ι, Tendsto (fun n => modeRest m w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
          atTop (𝓝 (modeRest m w W v G H ι σ y))) ∧
        Tendsto (fun n => stretchForm W (u (φ n)) (gradField (u (φ n))) σ y) atTop
          (𝓝 (stretchForm W v G σ y)) := by
  exact DensityPassageModes.modes_converge_ae m P w W hPars hSP hv hu

theorem left_density_liminf (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRot : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      splitLeft (fun σ y ι => modePos m P v G ι σ y) (fun σ y ι => modeRest m w W v G H ι σ y)
          (fun _ _ => 0) (stretchForm W v G) σ y
        ≤ liminf (fun n => splitLeft (fun σ y ι => modePos m P (u (φ n)) (gradField (u (φ n))) ι σ y)
          (fun σ y ι => modeRest m w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
          (fun _ _ => 0) (stretchForm W (u (φ n)) (gradField (u (φ n)))) σ y) atTop := by
  obtain ⟨φ, hφ, hae⟩ := modes_converge_ae m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with σ hσ
  filter_upwards [hσ] with y hy
  exact splitLeft_le_liminf
    (Pos := fun n σ y ι => modePos m P (u (φ n)) (gradField (u (φ n))) ι σ y)
    (Rest := fun n σ y ι => modeRest m w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
    (J := fun n => stretchForm W (u (φ n)) (gradField (u (φ n))))
    (Pos₀ := fun σ y ι => modePos m P v G ι σ y) (Rest₀ := fun σ y ι => modeRest m w W v G H ι σ y)
    (J₀ := stretchForm W v G) hy.1 hy.2.1 hy.2.2

end Setting

end DensityPassage

end Internal

open Internal.DensityPassage Internal.PassageLimit in
theorem modeDensityPassageHolds_of (hSmooth : ModeDensitySmoothHolds) (hPars : ModeSquareSumHolds)
    (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds) (hField : ModeFieldExistsHolds)
    (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    ModeDensityPassageHolds := by
  intro C m P b w k Γ W act w₀ epsSup epsGradSup ratio hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM
  have hex : ∀ n, ∃ Mn : ℝ → Space → Space,
      m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) Mn := fun n => by
    obtain ⟨M', hM', -⟩ := (hField m P b w ∅ hA hwB (u n) (gradField (u n)) (secondDerivField (u n))
      (transportPart P (u n)) (hSP P (u n) (hu.1 n))).2
    exact ⟨M', hM'⟩
  choose Mn hMn using hex
  have hX := gap_converges m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf
    v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hField hSolenoidal hSP Mn hMn
  obtain ⟨hfin, hN⟩ := negative_parts_converge m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp
    hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP
  obtain ⟨φ, hφ, hlim⟩ := left_density_liminf m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp
    hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hPars hDer hRot hSP
  have hn : ∀ n, IsSplitLowerBound
      (m.multiplierGap P w act (u n) (gradField (u n)) (secondDerivField (u n)) κ
        (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n))
      (fun σ y ι => modePos m P (u n) (gradField (u n)) ι σ y)
      (fun σ y ι => modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y) (fun _ _ => 0)
      (stretchForm W (u n) (gradField (u n))) := fun n =>
    hSmooth m P b w W act hA hV hWs hWp hWd hWdec hwB hactm hactp hactf (u n) (hu.1 n) κ (Mn n) (hMn n)
  have hmeas := fun n => left_densities_measurable m P b w Γ W act hA hV hWs hWp hWd hWdec hwB hactm hactp
    hactf v G H g hv u hu κ F hFm hFp hFf hF M hM hSP (φ n)
  exact isSplitLowerBound_of_liminf (fun n => hn (φ n)) (hX.comp hφ.tendsto_atTop)
    (hN.comp hφ.tendsto_atTop) hfin (fun n => (hmeas n).1) (fun n => (hmeas n).2) hlim

end Coercive

end Breakdown
