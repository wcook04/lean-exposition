import Breakdown.Cert.CoerciveSmoothMuRest
import Breakdown.Cert.CoerciveSmoothMuTransport

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

theorem transport_bound (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    dopMode m P v ι + ENNReal.ofReal (-pairMode m v (innerPart P W v) ι)
      ≤ ENNReal.ofReal (pairMode m v (innerPart P W v) ι)
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y) := by
  exact Internal.MuTransport.transport_bound_of hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι

theorem rest_measurable_of {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space) (ι : ℤ × ℤ)
    (h : Measurable (fun p : ℝ × Space => transportLoss m W v ι p.1 p.2) ∧
      Measurable (fun p : ℝ × Space => pressureLoss m W v ι p.1 p.2)) :
    Measurable (fun p : ℝ × Space => ENNReal.ofReal (-modeMuRest m W v (gradField v) ι p.1 p.2)) := by
  simp_rw [neg_rest_eq]
  exact (h.1.add h.2).ennreal_ofReal

theorem restMode_split {C : Type} (m : ModeWeights C) (hη : ∀ c, 0 < m.eta c) (W v : ℝ → Space → Space)
    (ι : ℤ × ℤ)
    (h : Measurable (fun p : ℝ × Space => transportLoss m W v ι p.1 p.2) ∧
      Measurable (fun p : ℝ × Space => pressureLoss m W v ι p.1 p.2)) :
    restMode m W v ι = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y))
      + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (pressureLoss m W v ι σ y) := by
  unfold restMode
  have hpt : ∀ σ y, ENNReal.ofReal (-modeMuRest m W v (gradField v) ι σ y)
      = ENNReal.ofReal (transportLoss m W v ι σ y) + ENNReal.ofReal (pressureLoss m W v ι σ y) :=
    fun σ y => by
      rw [neg_rest_eq, ENNReal.ofReal_add (transportLoss_nonneg m W v ι σ y)
        (pressureLoss_nonneg m hη W v ι σ y)]
  simp_rw [hpt]
  have hT := h.1.ennreal_ofReal
  have hin : ∀ σ, ∫⁻ y, (ENNReal.ofReal (transportLoss m W v ι σ y) + ENNReal.ofReal (pressureLoss m W v ι σ y))
      = (∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y)) + ∫⁻ y, ENNReal.ofReal (pressureLoss m W v ι σ y) :=
    fun σ => lintegral_add_left (hT.comp measurable_prodMk_left) _
  simp_rw [hin]
  exact lintegral_add_left (hT.lintegral_prod_right' (ν := volume)) _

theorem mode_bound_of {C : Type} (m : ModeWeights C) (P : ℝ) (hη : ∀ c, 0 < m.eta c)
    (W v Q Y : ℝ → Space → Space) (ι : ℤ × ℤ)
    (h : Measurable (fun p : ℝ × Space => transportLoss m W v ι p.1 p.2) ∧
      Measurable (fun p : ℝ × Space => pressureLoss m W v ι p.1 p.2))
    (hsplit : pairMode m v Q ι = pairMode m v (innerPart P W v) ι
      + pairMode m v Y ι)
    (htr : dopMode m P v ι + ENNReal.ofReal (-pairMode m v (innerPart P W v) ι)
      ≤ ENNReal.ofReal (pairMode m v (innerPart P W v) ι)
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y))
    (hpr : ENNReal.ofReal (-pairMode m v Y ι)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (pressureLoss m W v ι σ y)) :
    dopMode m P v ι + ENNReal.ofReal (-pairMode m v Q ι)
      ≤ ENNReal.ofReal (pairMode m v Q ι) + restMode m W v ι := by
  rw [restMode_split m hη W v ι h]
  set R1 := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y)
  set R2 := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (pressureLoss m W v ι σ y)
  set TD := pairMode m v (innerPart P W v) ι
  set TY := pairMode m v Y ι
  rw [hsplit]
  by_cases h1 : R1 = ⊤
  · rw [h1]
    simp
  by_cases h2 : R2 = ⊤
  · rw [h2]
    simp
  obtain ⟨hDt, hD⟩ := toReal_le_of h1 htr
  have hY : -TY ≤ R2.toReal := by
    have := ENNReal.toReal_mono h2 hpr
    rw [ENNReal.toReal_ofReal'] at this
    exact le_trans (le_max_left _ _) this
  rw [← ENNReal.ofReal_toReal hDt, ← ENNReal.ofReal_toReal h1, ← ENNReal.ofReal_toReal h2,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  exact ennreal_bound ENNReal.toReal_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (by linarith)

end Internal.MuSmooth

open Internal.MuSmooth in
theorem modeMuEstimateSmoothHolds_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds) : ModeMuEstimateSmoothHolds := by
  intro C m P b w W w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay _hwb v hv Q hQ
  have hL := fun ι => loss_measurable_of m P b w W hm hW v hv ι
  obtain ⟨Q', hQ', hsplit⟩ := pair_split_of hPars hSolenoidal m P b w W hm hW hWp hWdiv hWdecay v hv Q hQ
  exact split_of_modes m P W v Q hm.cμ_lt_one hm.eta_pos
    (fun ι => rest_measurable_of m W v ι (hL ι))
    (fun ι => dop_measurable_of m P b w hm v hv ι)
    (rest_finite_of hPars m P b w W hm hb hW hWp hWdecay v hv)
    (pair_summable_of hPars m P b w hm v hv _ Q hQ)
    (fun ι => mode_bound_of m P hm.eta_pos W v Q _ ι (hL ι) (hsplit ι)
      (transport_bound hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι)
      (pressure_bound_of hPars hSolenoidal m P b w W hm hb hW hWp hWdiv hWdecay v hv Q hQ Q' hQ' ι))

end Coercive

end Breakdown
