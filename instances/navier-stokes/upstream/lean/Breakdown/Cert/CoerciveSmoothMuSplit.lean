import Breakdown.Cert.CoerciveSmoothMuSum
import Breakdown.Cert.CoerciveSmoothPressure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

theorem innerPart_eq (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    innerPart P W v σ y = smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) := by
  unfold innerPart smoothRight transportPart
  abel

theorem term_integrable (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ) {B : ℝ}
    (hB : ∀ c y, |m.muW c y| ≤ B ∧ ‖y‖ ^ 2 * |m.muW c y| ≤ B ∧ ‖y‖ * ‖fderiv ℝ (m.muW c) y‖ ≤ B)
    (hμc : ∀ c, Continuous (m.muW c))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (X : ℝ → Space → Space)
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (hXp : IsTimePeriodic X)
    (hX2 : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => (Complex.I * (m.muW (m.classOf ι) z.2 : ℂ)
      * cdot (modeVel ι v z.1 z.2) (modeVel ι X z.1 z.2)).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hw : ModeL2Internal.IsSquareField (weighted v) :=
    ⟨(weighted_continuous v hvc).aestronglyMeasurable, weighted_periodic v hv.periodic, weighted_square P v hv⟩
  have hX : ModeL2Internal.IsSquareField X := ⟨hXm, hXp, hX2⟩
  have i1 := ModeL2Internal.integrable_cnormSq_modeVel hPars hw ι
  have i2 := ModeL2Internal.integrable_cnormSq_modeVel hPars hX ι
  have hva : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2 i)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := fun i =>
    (ModeL2Internal.aestronglyMeasurable_modeVel hvc.aestronglyMeasurable ι i).mono_ac ModeL2Internal.slab_ac
  have hXa : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι X z.1 z.2 i)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := fun i =>
    (ModeL2Internal.aestronglyMeasurable_modeVel hXm ι i).mono_ac ModeL2Internal.slab_ac
  have hc := ModeL2Internal.aestronglyMeasurable_cdot hva hXa
  have hwt : Continuous (fun z : ℝ × Space => Complex.I * (m.muW (m.classOf ι) z.2 : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp ((hμc (m.classOf ι)).comp continuous_snd))
  have hf : AEStronglyMeasurable (fun z : ℝ × Space => (Complex.I * (m.muW (m.classOf ι) z.2 : ℂ)
      * cdot (modeVel ι v z.1 z.2) (modeVel ι X z.1 z.2)).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    Complex.continuous_re.comp_aestronglyMeasurable (hwt.aestronglyMeasurable.mul hc)
  refine Integrable.mono' ((i1.const_mul (2 * B)).add (i2.const_mul B)) hf
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact pairTerm_le m hB v X ι z.1 z.2

theorem pair_split_of (hPars : ModeSquareSumHolds) (hSolenoidal : SolenoidalModeHolds) {C : Type} (m : ModeWeights C)
    (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (Q : ℝ → Space → Space)
    (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    ∃ Q', IsSolenoidalPartOf (fun σ y => fderiv ℝ (W σ) y (v σ y)) Q' ∧ ∀ ι : ℤ × ℤ,
      pairMode m v Q ι = pairMode m v (innerPart P W v) ι
        + pairMode m v (fun σ y => (2 : ℝ) • Q' σ y - fderiv ℝ (W σ) y (v σ y)) ι := by
  obtain ⟨hFm, hFp, hF2, hSm, hSp, hS2, Q', hQ', hae⟩ :=
    solenoidal_split_smooth hSolenoidal P W hW hWp hWdiv hWdecay v hv Q hQ
  simp only [← innerPart_eq] at hSm hSp hS2 hae
  obtain ⟨hRm, hRp, hR2, -⟩ := solenoidal_reflection_modes hPars hSolenoidal _ Q' hFm hFp hF2 hQ'
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hμc : ∀ c, Continuous (m.muW c) := fun c => by
    obtain ⟨K, hK⟩ := hm.muW_increment c
    exact hK.continuous
  refine ⟨Q', hQ', fun ι => ?_⟩
  have hadd := modeVel_add_ae hPars (X := innerPart P W v)
    (Y := fun σ y => (2 : ℝ) • Q' σ y - fderiv ℝ (W σ) y (v σ y)) (Z := Q)
    hSm hSp hS2 hRm hRp hR2 hQ.1 hQ.2.1 hQ.2.2.1 hae ι
  exact modeTerm_add_of_ae (fun y => m.muW (m.classOf ι) y) v Q (innerPart P W v)
    (fun σ y => (2 : ℝ) • Q' σ y - fderiv ℝ (W σ) y (v σ y)) ι hadd
    (term_integrable hPars m P hB hμc v hv _ hSm hSp hS2 ι)
    (term_integrable hPars m P hB hμc v hv _ hRm hRp hR2 ι)

end Internal.MuSmooth

end Coercive

end Breakdown
