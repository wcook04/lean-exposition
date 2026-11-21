import Breakdown.Cert.CoercivePieceDensityPassageRight
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoerciveDensityPassageCutoff

open scoped ENNReal Topology
open MeasureTheory Filter

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassage

open ModeL2Internal (IsSquareField)
open PairingSplitInternal (square_add square_lin pairing_add_left pairing_lin_left normSq_add periodNorm_congr
  pairing_test_integrable_split testField_square)

theorem pairing_eq_zero_of_orthogonal (hSolenoidal : SolenoidalModeHolds) {D M : ℝ → Space → Space}
    (hD : IsSquareField D)
    (hDψ : ∀ ψ, IsPeriodicTestField ψ → ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (D σ y) (ψ σ y) = 0)
    (hM : IsSquareField M)
    (hMg : ∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) :
    periodPairing D M = 0 := by
  set X : ℝ → Space → Space := fun σ y => D σ y + M σ y with hXdef
  have hX : IsSquareField X := square_add hD hM
  obtain ⟨Q, hQ, -, hN, huniq, -⟩ := hSolenoidal X hX.1 hX.2.1 hX.2.2
  have hMX : IsSolenoidalPartOf X M := by
    refine ⟨hM.1, hM.2.1, hM.2.2, hMg, fun ψ hψ => ?_⟩
    rw [hXdef, pairing_test_integrable_split hD hM (testField_square hψ), hDψ ψ hψ, zero_add]
  have hQM := huniq M hMX
  have hN' : periodNorm (fun σ y => (2 : ℝ) • M σ y - X σ y) = periodNorm X := by
    rw [← hN]
    exact periodNorm_congr ((hM.1.const_smul (2 : ℝ)).sub hX.1) ((hQ.1.const_smul (2 : ℝ)).sub hX.1)
      (hQM.mono fun z hz => by simp only [hz])
  have hL := square_lin hD hD (-1) 0
  have eL : (fun σ y => (-1 : ℝ) • D σ y + (0 : ℝ) • D σ y) = fun σ y => -D σ y := by
    funext σ y
    simp
  rw [eL] at hL
  have e1 : (fun σ y => (2 : ℝ) • M σ y - X σ y) = fun σ y => M σ y + -D σ y := by
    funext σ y
    simp only [hXdef, two_smul]
    abel
  rw [e1] at hN'
  have h1 := normSq_add hM hL
  have h2 := normSq_add hD hM
  rw [hN'] at h1
  have hpn : periodNorm (fun σ y => -D σ y) = periodNorm D := by
    unfold periodNorm
    simp only [norm_neg]
  have hpp : periodPairing M (fun σ y => -D σ y) = -periodPairing D M := by
    rw [PassageLimit.periodPairing_comm, ← eL, pairing_lin_left hD hD hM (-1) 0]
    ring
  rw [hpn, hpp] at h1
  rw [hXdef] at h1
  linarith

theorem pairing_rightSideLimit_eq (hSolenoidal : SolenoidalModeHolds) {k : ℕ} {Γ : Set Symmetry} {P : ℝ}
    {W : ℝ → Space → Space} {act : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤)
    {F : ℝ → Space → Space} (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hF : IsRightSide W act κ v G g F) {M : ℝ → Space → Space}
    (hMm : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume) (hMp : IsTimePeriodic M)
    (hM2 : periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤)
    (hMg : ∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) :
    periodPairing F M = periodPairing (rightSideLimit W act κ v G H g) M := by
  set R := rightSideLimit W act κ v G H g with hRdef
  obtain ⟨hRm, hR2⟩ := PassageLimit.rightSideLimit_memL2 κ hv hW hWdecay hactm hact2 hvw
  have hR : IsSquareField R := ⟨hRm, rightSideLimit_periodic κ hv hWp hactp, hR2⟩
  have hFs : IsSquareField F := ⟨hFm, hFp, hF2⟩
  have hMs : IsSquareField M := ⟨hMm, hMp, hM2⟩
  have hD := square_lin hFs hR 1 (-1)
  have eD : (fun σ y => (1 : ℝ) • F σ y + (-1 : ℝ) • R σ y) = fun σ y => F σ y - R σ y := by
    funext σ y
    simp [sub_eq_add_neg]
  rw [eD] at hD
  have h0 := pairing_eq_zero_of_orthogonal hSolenoidal hD
    (rightSide_orthogonal_periodic κ hv hW hWp hWdecay hactm hactp hact2 hvw hFm hFp hF2 hF) hMs hMg
  have eF : periodPairing F M = periodPairing (fun σ y => (F σ y - R σ y) + R σ y) M := by
    congr 1
    funext σ y
    simp
  rw [eF, pairing_add_left hD hR hMs, h0, zero_add]

end Internal.DensityPassage

end Coercive

end Breakdown
