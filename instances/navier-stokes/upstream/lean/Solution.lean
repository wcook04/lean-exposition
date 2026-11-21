import Breakdown.Uniqueness.Space
import Breakdown.Torus.Main
import Breakdown.Weak.Main
import Breakdown.Frac.SpaceExports
import Breakdown.Frac.TorusBlowupExports
import Breakdown.Cert.Main
import Breakdown.Cert.ExtendedMain
import Breakdown.Cert.CoerciveMain
import Breakdown.Cert.ExtendedCoerciveMain
import Breakdown.FracCert.Main
import Breakdown.FracCell.FinalChain
import Breakdown.CellReduction.CellLayerBreakdownClosed
import Breakdown.CertTorus.CertificateCorollary

namespace Breakdown

theorem breakdown_on_space (h : PeriodicSimilarityProfileExists) : BreakdownOnSpace :=
  breakdownOnSpace_of_profile h

theorem breakdown_on_torus (h : PeriodicSimilarityProfileExists) : BreakdownOnTorus :=
  Periodic.breakdownOnTorus_of_profile h

theorem breakdown_on_space_of_weak (h : WeakPeriodicSimilarityProfileExists) : BreakdownOnSpace :=
  breakdownOnSpace_of_weak h

theorem fractional_breakdown_on_space (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnSpace α :=
  fracBreakdownOnSpace α hα₁ hα₂ h

theorem fractional_breakdown_on_torus (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnTorus α :=
  fracBreakdownOnTorus α hα₁ hα₂ h

section

open scoped ContDiff ENNReal
open MeasureTheory

theorem certificate_orbit (h : CertificateHypothesis) : WeakPeriodicSimilarityProfileExists :=
  certificate_orbit_proved h

end

section

open scoped ContDiff ENNReal
open MeasureTheory

namespace ModeWeights

variable {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)

theorem multiplier_density {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) :
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∃ M, m.IsMultiplierField v G H M ∧
        m.frequencySeminormSq P v < ⊤ ∧
        periodNorm M ≤ m.multiplierConstant w₀ epsSup epsGradSup ratio
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.frequencySeminormSq P v).toReal) ∧
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityPos P b w v G H W σ y)
            + ENNReal.ofReal (-m.multiplierGap P w act v G H κ F M)
          ≤ ENNReal.ofReal (m.multiplierGap P w act v G H κ F M)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P b w v G H W σ y :=
  multiplier_density_proved m P b w Γ W act hm hb hW hWp hWdiv hWdecay hwb hactm hactp hact2

theorem mode_azimuthal_gain (Γ : Set Symmetry) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) (hk : 2 ≤ |ι.2|) :
    ∀ᵐ z : ℝ × Space,
      ((|ι.2| : ℝ) - 1) ^ 2 / cylRadius z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2)
          ≤ cnormSq (modeGrad ι G z.1 z.2) ∧
        ((|ι.2| : ℝ) - 2) ^ 2 / cylRadius z.2 ^ 2 * cnormSq (modeGrad ι G z.1 z.2)
          ≤ cnormSq (modeSecondDeriv ι H z.1 z.2) :=
  mode_azimuthal_gain_proved P Γ v G H g hv ι hk

theorem stretch_mean_bound (Γ : Set Symmetry) (W : ℝ → Space → Space) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hlen : ∀ y, 0 < m.len y) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ y : Space,
      ENNReal.ofReal (-∫ σ in Set.Icc (0 : ℝ) 1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          stretchForm W v G σ (axialRot φ y))
        ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι : ℤ × ℤ, ENNReal.ofReal (m.stretchCharge b v G ι 0 y) :=
  stretch_mean_bound_proved m P b Γ W hb hW hWdiv hlen v G H g hv

theorem multiplierInequality_of_density {k : ℕ} {d : CertificateData k}
    (hrad : ∀ i, 0 ≤ d.radius i)
    (hsmooth : ContDiff ℝ 2 (fun q : (Fin k → ℝ) × ℝ × Space => d.profile q.1 q.2.1 q.2.2))
    (hper : ∀ p, IsTimePeriodic (d.profile p))
    (hdiv : ∀ p ∈ d.box, ∀ σ y, divergenceAt (d.profile p σ) y = 0)
    (hdecay : ∀ p ∈ d.box, ∀ σ y, ∀ j ≤ 2,
      ‖iteratedFDeriv ℝ j (d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ (j + 1))
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤)
    {C : Type} (m : (Fin k → ℝ) → ModeWeights C) (b : (Fin k → ℝ) → FlowBounds C)
    {c cμ t K epsSup epsGradSup ratio : ℝ}
    (hc : ∀ p ∈ d.box, (m p).c = c) (hcμ : ∀ p ∈ d.box, (m p).cμ = cμ) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hm : ∀ p ∈ d.box, (m p).IsAdmissible (d.period p) (b p) d.weightFn d.weight epsSup epsGradSup ratio)
    (hb : ∀ p ∈ d.box, (b p).IsValid (m p) (d.profile p))
    (hrest : ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
      ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile p) d.actuator κ v G g F →
        ∀ M, (m p).IsMultiplierField v G H M →
          (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (b p) d.weightFn v G H (d.profile p) σ y) < ⊤ ∧
          ENNReal.ofReal (c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (b p) d.weightFn v G H (d.profile p) σ y
          ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityPos (d.period p) (b p) d.weightFn v G H (d.profile p) σ y)
            + ENNReal.ofReal (-(c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2))) :
    MultiplierInequality d c cμ t
      (Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)) K :=
  multiplierInequality_of_density_proved hrad hsmooth hper hdiv hdecay hwup hactm hactp hact2 m b hc hcμ ht hK hm hb hrest

end ModeWeights

namespace PieceWeights

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
  (w : Space → ℝ)

theorem piece_multiplier_density {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) :
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∃ M, m.IsMultiplierField v G H M ∧
        m.seminormSq P v < ⊤ ∧
        periodNorm M ≤ Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.seminormSq P v).toReal) ∧
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityPos P h w v G H W σ y)
            + ENNReal.ofReal (-m.multiplierGap P w act v G H κ F M)
          ≤ ENNReal.ofReal (m.multiplierGap P w act v G H κ F M)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P h w v G H W σ y :=
  piece_multiplier_density_proved m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2

theorem multiplierInequality_of_pieceDensity {k : ℕ} {d : CertificateData k}
    (hrad : ∀ i, 0 ≤ d.radius i)
    (hsmooth : ContDiff ℝ 2 (fun q : (Fin k → ℝ) × ℝ × Space => d.profile q.1 q.2.1 q.2.2))
    (hper : ∀ p, IsTimePeriodic (d.profile p))
    (hdiv : ∀ p ∈ d.box, ∀ σ y, divergenceAt (d.profile p σ) y = 0)
    (hdecay : ∀ p ∈ d.box, ∀ σ y, ∀ j ≤ 2,
      ‖iteratedFDeriv ℝ j (d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ (j + 1))
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤)
    {C : Type} {nE nM : ℕ} (m : (Fin k → ℝ) → PieceWeights C nE nM)
    (hs : (Fin k → ℝ) → HarmonicBounds)
    {c cμ t K epsSup epsGradSup ratio : ℝ}
    (hc : ∀ p ∈ d.box, (m p).c = c) (hcμ : ∀ p ∈ d.box, (m p).cμ = cμ) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hm : ∀ p ∈ d.box, (m p).IsAdmissible (d.period p) (hs p) d.weightFn (d.profile p)
      d.weight epsSup epsGradSup ratio)
    (hrest : ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
      ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile p) d.actuator κ v G g F →
        ∀ M, (m p).IsMultiplierField v G H M →
          (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (hs p) d.weightFn v G H (d.profile p) σ y) < ⊤ ∧
          ENNReal.ofReal (c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (hs p) d.weightFn v G H (d.profile p) σ y
          ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityPos (d.period p) (hs p) d.weightFn v G H (d.profile p) σ y)
            + ENNReal.ofReal (-(c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2))) :
    MultiplierInequality d c cμ t
      (Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)) K :=
  multiplierInequality_of_pieceDensity_proved hrad hsmooth hper hdiv hdecay hwup hactm hactp hact2 m hs hc hcμ ht hK hm hrest

end PieceWeights

end

section

open scoped ContDiff ENNReal
open MeasureTheory

theorem isExtendedCertificate_withUnitWeight {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) : IsExtendedCertificate d.withUnitWeight :=
  Cert.extendedUnitWeightHolds hd

theorem isExtendedCertificate_atProfile {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) : IsExtendedCertificate d.atProfile :=
  Cert.extendedAtProfileHolds hd

theorem extended_certificate_orbit (h : ExtendedCertificateHypothesis) :
    WeakPeriodicSimilarityProfileExists :=
  extended_certificate_orbit_proved h

end

section

open scoped ContDiff ENNReal
open MeasureTheory

namespace CoerciveWeak

variable {k : ℕ}
open PieceWeights

theorem IsWeakSecondDerivState.secondDeriv_symm {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) :
    ∀ᵐ y, ∀ a b : Space, HW σ y a b = HW σ y b a :=
  weakSecondDerivSymmetricHolds_proof hW σ

theorem vortGradMap_secondDerivField (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (σ : ℝ) (y : Space) :
    vortGradMap (secondDerivField W σ y) = fderiv ℝ (fun x => curlVec (fderiv ℝ (W σ) x)) y :=
  vortGradMapSecondDerivFieldHolds_proof W hW σ y

theorem pieceMultiplierDensityWeak : PieceMultiplierDensityWeakHolds :=
  pieceMultiplierDensityWeakHolds_proof

theorem extendedCoerciveClause_of_pieceData {d : ExtendedCertificateData k}
    (hrad : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j)
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (d.actuatorBound ^ 2))
    (HW : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : (Fin k → ℝ) → ℝ)
    (hmodel : ∀ q ∈ d.params, IsWeakSecondDerivState (d.model q) (HW q) (D q))
    {C : Type} {nE nM : ℕ} (m : (Fin k → ℝ) → PieceWeights C nE nM)
    (hs : (Fin k → ℝ) → HarmonicBounds)
    {c cμ t epsSup epsGradSup ratio : ℝ}
    (hc : ∀ q ∈ d.params, (m q).c = c) (hcμ : ∀ q ∈ d.params, (m q).cμ = cμ) (ht : 0 ≤ t)
    (hm : ∀ q ∈ d.params, IsAdmissibleWeak (m q) (d.period q) (hs q) d.weightFn (d.model q) (HW q)
      d.weight epsSup epsGradSup ratio)
    (hrest : RowRestClause d m hs HW c t)
    (hL2 : Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)
      / Real.sqrt c ≤ d.coerciveL2)
    (hPin : Real.sqrt (t / c) ≤ d.coercivePin) :
    ExtendedCoerciveClause d :=
  extendedCoerciveClause_of_pieceData_proved hrad hwup hactm hactp hnorm HW D hmodel m hs hc hcμ ht hm hrest hL2 hPin

end CoerciveWeak

end

section

open scoped ContDiff ENNReal
open MeasureTheory Matrix

namespace SteadyCert

theorem fracCertificate_profile (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) (h : FracCertificateHypothesis α) :
    RotatingFractionalProfileExists α :=
  fracCertificate_profile_proved α hα₁ hα₂ h

end SteadyCert

end

theorem certificate_breakdown_on_space (h : CertificateHypothesis) : BreakdownOnSpace :=
  breakdown_on_space_of_weak (certificate_orbit h)

theorem extended_certificate_breakdown_on_space (h : ExtendedCertificateHypothesis) : BreakdownOnSpace :=
  breakdown_on_space_of_weak (extended_certificate_orbit h)

theorem fractional_certificate_breakdown (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : SteadyCert.FracCertificateHypothesis α) :
    FractionalBreakdownOnSpace α ∧ FractionalBreakdownOnTorus α :=
  ⟨fractional_breakdown_on_space α hα₁ hα₂ (SteadyCert.fracCertificate_profile α hα₁ hα₂ h),
    fractional_breakdown_on_torus α hα₁ hα₂ (SteadyCert.fracCertificate_profile α hα₁ hα₂ h)⟩

section

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

theorem fractional_breakdown_of_cell_system {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X) :
    FractionalBreakdownOnSpace (501 / 500) ∧ FractionalBreakdownOnTorus (501 / 500) :=
  fractional_breakdown_of_cell_system_proved c D A M MD RD X h

end CellSystem

end CellCert

end

section

open scoped ContDiff ENNReal
open MeasureTheory Breakdown.CertCell Breakdown.CertCell.GivenShape

namespace CellLayerSystem

theorem breakdownOnSpace_of_cell_system_condition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : BreakdownOnSpace :=
  spaceBreakdown_of_cell_system_condition D X R T Y N B h

theorem breakdownOnTorus_of_cell_system_condition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : BreakdownOnTorus :=
  torusBreakdown_of_cell_system_condition D X R T Y N B h

theorem breakdownOnSpaceAndTorus_of_cell_system_condition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) :
    BreakdownOnSpace ∧ BreakdownOnTorus :=
  spaceAndTorusBreakdown_of_cell_system_condition D X R T Y N B h

end CellLayerSystem

end

end Breakdown
