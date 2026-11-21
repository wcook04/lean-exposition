import Breakdown.CertCell.Defs
import Breakdown.FracCell.StExterior
import Breakdown.CertCell.StatementDefs

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open CellCert.CellAnalysis (CellBox radialEigen heightEigen)
open PieceWeights

namespace TailBudget

variable (b : TailBudget) (K : CellBox) (Q : ℕ) (k : ℝ)

def remainder (hessTail curlGradTail gradTail curlTail velTail : ℝ) : ℝ :=
  b.hessFloor * hessTail + b.curlGradFloor * curlGradTail
    - (b.curlAbsorb * curlTail + b.gradAbsorb * gradTail + b.velAbsorb * velTail)
    - (b.gradPotential + b.gradLeak + b.globalLeak) * gradTail - (b.velPotential + b.velLeak) * velTail

end TailBudget

def TailAbsorption : Prop :=
  ∀ (b : TailBudget) (K : CellBox) (Q : ℕ) (k hessTail curlGradTail gradTail curlTail velTail lowTop : ℝ),
    b.Holds K Q k → 0 ≤ b.hessFloor → 0 ≤ b.curlGradFloor →
    0 ≤ gradTail → 0 ≤ curlTail → 0 ≤ velTail → curlTail ≤ 2 * gradTail →
    hessTailGain K Q k * gradTail ≤ hessTail → curlTailGain K Q k * curlTail ≤ curlGradTail →
    velTail ≤ lowTop + gradTail / velTailGain K Q →
    -(b.velCharge * lowTop) ≤ b.remainder hessTail curlGradTail gradTail curlTail velTail

namespace PointCoef

variable (a : PointCoef)

def quad (x2 xc x1 xo x0 : ℝ) : ℝ :=
  a.hess * x2 ^ 2 + a.curlGrad * xc ^ 2 + a.curl * xo ^ 2 + a.grad * x1 ^ 2 + a.vel * x0 ^ 2
    - a.cross * x1 * x0

def Dominates (lo : PointCoef) : Prop :=
  lo.hess ≤ a.hess ∧ lo.curlGrad ≤ a.curlGrad ∧ lo.curl ≤ a.curl ∧ lo.grad ≤ a.grad ∧ lo.vel ≤ a.vel ∧
    a.cross ≤ lo.cross

end PointCoef

def AngularRelations (k r x2 xc x1 xo x0 : ℝ) : Prop :=
  0 ≤ x2 ∧ 0 ≤ xc ∧ 0 ≤ x1 ∧ 0 ≤ xo ∧ 0 ≤ x0 ∧ xo ^ 2 ≤ 2 * x1 ^ 2 ∧
    max (k - 1) 0 * x0 ≤ r * x1 ∧ max (k - 2) 0 * x1 ≤ r * x2 ∧ max (k - 1) 0 * xo ≤ r * xc

def PointwiseQuadraticTest : Prop :=
  ∀ (lo a : PointCoef) (kLow k r shift x2 xc x1 xo x0 : ℝ), 0 < r → kLow ≤ k → 0 ≤ a.curlGrad → a.Dominates lo →
    lo.PassesTest kLow r shift → AngularRelations k r x2 xc x1 xo x0 → 0 ≤ a.quad x2 xc x1 xo x0

def PointCoef.ofMode (a : ModeCoefficients) : PointCoef where
  hess := a.hess
  curlGrad := a.curlHess
  curl := a.curl
  grad := a.strain
  vel := a.velocity
  cross := 0

def modeCoef {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (mm : ℕ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : PointCoef :=
  PointCoef.ofMode (ModeCoefficients.ofPieces m P h w mm ι p)

def labelQuad (a : PointCoef) (mm : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (p : ℝ × ℝ) : ℝ :=
  a.quad (Real.sqrt (cnormSq (labelHess mm ι H p))) (Real.sqrt (cnormSq (curlGradOfSecondDeriv (labelHess mm ι H p))))
    (Real.sqrt (cnormSq (labelGrad mm ι G p))) (Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))))
    (Real.sqrt (cnormSq (labelVel mm ι v p)))

def offModeDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (mc : ModeCharges) (ec : EntryCharges) (mm : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (p : ℝ × ℝ) : ℝ :=
  labelQuad ((modeCoef m P h w mm ι p).withStretch ec.stretchConst (mc.curl ι p) (mc.product ι p)
    (mc.gradient ι p) (mc.length ι p) (ec.curlCharge p) (ec.gradCharge p) (ec.velCharge p)) mm ι v G H p

theorem modeTerm_eq_labelQuad {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (w : Space → ℝ) (mm : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (p : ℝ × ℝ) :
    m.modeTerm P h w v G H (labelHarmonic mm ι) 0 (planePoint p)
      = labelQuad (modeCoef m P h w mm ι p) mm ι v G H p := by
  simp only [modeTerm, modeDensity, labelQuad, PointCoef.quad, modeCoef, PointCoef.ofMode,
    ModeCoefficients.ofPieces, labelHess, labelGrad, labelVel]
  ring

def AngularModeBounds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P → ∀ (mm : ℕ) (ι : ℤ × ℤ),
    ∀ᵐ p ∂(volume.restrict halfPlane), AngularRelations |(labelAzimuth mm ι : ℝ)| p.1
      (Real.sqrt (cnormSq (labelHess mm ι H p))) (Real.sqrt (cnormSq (curlGradOfSecondDeriv (labelHess mm ι H p))))
      (Real.sqrt (cnormSq (labelGrad mm ι G p))) (Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))))
      (Real.sqrt (cnormSq (labelVel mm ι v p)))

def LabelGradFinite : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P → ∀ (mm : ℕ) (ι : ℤ × ℤ),
    ∫⁻ p in halfPlane, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) < ⊤

namespace SetPieceBounds

variable {C : Type} {nE nM : ℕ} (B : SetPieceBounds C nE nM) (m : PieceWeights C nE nM) (P : ℝ)
  (h : HarmonicBounds) (w : Space → ℝ)

end SetPieceBounds

def UniformCoefficientBounds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ),
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    ∀ (B : SetPieceBounds C nE nM) (mm : ℕ) (I : Set (ℤ × ℤ)) (Z : Set (ℝ × ℝ)), B.IsValidOn m P h mm I Z →
      ∀ ι ∈ I, ∀ p ∈ Z, (modeCoef m P h w mm ι p).Dominates (B.lowCoef m h w p)

def OffModeConditionSound : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ),
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    ∀ (mm : ℕ) (E : OffModeCondition C nE nM), ∀ mc : ModeCharges, IsOffModeCondition m P h w mc mm E →
    ∀ (Γ : Set Symmetry) v G H g, IsPerturbation Γ P v G H g → ∀ ι ∈ E.modes,
      ∀ᵐ p ∂(volume.restrict E.region), 0 ≤ offModeDensity m P h w mc E.charges mm ι v G H p

def IsFlipEven (mm : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) : Prop :=
  ∀ᵐ p ∂(volume.restrict halfPlane),
    labelVel mm ι v (p.1, -p.2) = fun a => (frameSign a : ℂ) * labelVel mm (labelFlip ι) v p a

def LabelFlipEvenHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P →
    (∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) → ∀ (mm : ℕ) (ι : ℤ × ℤ), IsFlipEven mm ι v

def ModeRayInverseSquare : Prop :=
  ∀ (R : ℝ × ℝ → ℝ) (R₀ R₁ : ℝ), IsDirectionRadius R R₀ R₁ →
    ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P → ∀ (mm : ℕ) (ι : ℤ × ℤ),
      ENNReal.ofReal (rayInverseSquareConst |(labelAzimuth mm ι : ℝ)|)
          * ∫⁻ p in planeRayRegion R, ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1)
        ≤ ∫⁻ p in planeRayRegion R, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1)

def ModeSquareInverseSquare : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P →
    ∀ (mm : ℕ) (ι : ℤ × ℤ), labelAzimuth mm ι = 0 → IsFlipEven mm ι v →
      ENNReal.ofReal 2
          * ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1)
        ≤ ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1)

def ExteriorConditionSound : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ),
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    ∀ (mm : ℕ) (E : ExteriorCondition C nE nM), ∀ mc : ModeCharges, IsExteriorCondition m P h w mc mm E →
    ∀ (Γ : Set Symmetry) v G H g, IsPerturbation Γ P v G H g → ∀ ι ∈ E.modes,
      (∀ R : ℝ, E.region = planeSquareExterior R → labelAzimuth mm ι = 0 → IsFlipEven mm ι v) →
      ∫⁻ p in E.region, ENNReal.ofReal (-(offModeDensity m P h w mc E.charges mm ι v G H p * p.1))
        ≤ ∫⁻ p in E.region, ENNReal.ofReal (offModeDensity m P h w mc E.charges mm ι v G H p * p.1)

theorem offModeConditionSound_of (hA : AngularModeBounds) (hQ : PointwiseQuadraticTest)
    (hU : UniformCoefficientBounds) : OffModeConditionSound := by
  intro C nE nM m P h w W HW w₀ epsSup epsGradSup ratio hm mm E mc hE Γ v G H g hv ι hι
  have hang := ae_restrict_of_ae_restrict_of_subset hE.region_sub (hA Γ P v G H g hv hm.period_pos mm ι)
  filter_upwards [hang, ae_restrict_mem hE.region_measurable] with p hp hpZ
  have hr : 0 < p.1 := (Set.mem_prod.mp (hE.region_sub hpZ)).1
  obtain ⟨hs, hcov⟩ := hE.charges_cover
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcov ι hι p hpZ
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ :=
    hU m P h w W HW w₀ epsSup epsGradSup ratio hm E.pieces mm E.modes E.region hE.pieces_valid ι hι p hpZ
  have hcg : 0 ≤ (modeCoef m P h w mm ι p).curlGrad := by
    have := hm.conv_le (labelHarmonic mm ι) (planePoint p)
    simp only [modeCoef, PointCoef.ofMode, ModeCoefficients.ofPieces]
    linarith
  have hs2 : 0 ≤ E.charges.stretchConst / 2 := by positivity
  have hdom : ((modeCoef m P h w mm ι p).withStretch E.charges.stretchConst (mc.curl ι p) (mc.product ι p)
      (mc.gradient ι p) (mc.length ι p) (E.charges.curlCharge p) (E.charges.gradCharge p)
      (E.charges.velCharge p)).Dominates ((E.pieces.lowCoef m h w p).charged E.charges p) := by
    simp only [PointCoef.Dominates, PointCoef.charged, PointCoef.withStretch]
    rw [h4]
    refine ⟨d1, d2, by linarith, ?_, ?_, ?_⟩
    · have : E.charges.stretchConst / 2 * mc.gradient ι p * E.charges.length p
          ≤ E.charges.stretchConst / 2 * E.charges.waveGrad p * E.charges.length p := by gcongr
      linarith
    · have : E.charges.stretchConst / 2 * mc.gradient ι p / E.charges.length p
          ≤ E.charges.stretchConst / 2 * E.charges.waveGrad p / E.charges.length p := by gcongr
      linarith
    · have : E.charges.stretchConst * mc.product ι p ≤ E.charges.stretchConst * E.charges.meanGrad p := by
        gcongr
      linarith
  unfold offModeDensity labelQuad
  exact hQ _ _ _ _ p.1 (E.shift p) _ _ _ _ _ hr (hE.pieces_valid.azimuth_ge ι hι) hcg hdom (hE.test p hpZ) hp

end TailBand

end CertCell

end Breakdown
