import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.FracCell.CellDataDefs
import Breakdown.CertCell.StatementDefs

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

open CellCert.CellAnalysis (CellBox IsCellBox cylPoint radialUnit angularUnit axialUnit)

def labelTimeFreq (P : ℝ) (ι : ℤ × ℤ) : ℝ := 2 * Real.pi * (labelTime ι : ℝ) / P

def labelHess (m : ℕ) (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    Fin 3 × Fin 3 × Fin 3 → ℂ :=
  modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p)

def labelScalar (m : ℕ) (ι : ℤ × ℤ) (q : ℝ → Space → ℝ) (p : ℝ × ℝ) : ℂ :=
  modeAverage (labelHarmonic m ι) (fun τ φ (_ : Unit) => q τ (axialRot φ (planePoint p))) ()

namespace CellPoly

end CellPoly

namespace CellMesh

variable (M : CellMesh)

def IsDeactivated (K : Fin M.count) (ι : ℤ × ℤ) : Prop := ι ∉ M.resolved K ∧ ι ∉ M.band K

def regionOf : Option (Fin M.count) → Set (ℝ × ℝ)
  | none => M.exterior
  | some K => (M.box K).rect

end CellMesh

namespace CellVecField

variable {count : ℕ} (F : CellVecField count)

end CellVecField

namespace CellMatField

variable {count : ℕ} (F : CellMatField count)

end CellMatField

def classOfLabel {C : Type} {nE nM : ℕ} (m : ℕ) (w : PieceWeights C nE nM) (ι : ℤ × ℤ) : C :=
  w.classOf (labelHarmonic m ι)

def strainWeightOf {C : Type} {nE nM : ℕ} (m : ℕ) (w : PieceWeights C nE nM) (ι : ℤ × ℤ) : Space → ℝ :=
  w.convD (classOfLabel m w ι)

def vorticityWeightOf {C : Type} {nE nM : ℕ} (m : ℕ) (w : PieceWeights C nE nM) (ι : ℤ × ℤ) : Space → ℝ :=
  w.convZ (classOfLabel m w ι)

namespace CellLayerData

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def modelHess : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) := fun _ => D.givenHess

def actuatorField (i : Fin k) : ℝ → Space → Space :=
  (D.actuatorValues i).field D.mesh.box D.azimuthOrder

def baseClass (q : Fin k → ℝ) : C := (D.pieces q).classOf (0, 0)

end CellLayerData

def multiplierRight {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ψ : ℝ → Space → Space) : ℝ :=
  (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y))
    + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      ((∑ β : Fin nE, (Complex.I * ((PieceWeights.sgn (w.epsP β).modes ι * (w.epsP β).wt y : ℝ) : ℂ)
          * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re)
        + ∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (w.muP β).modes ι * (w.muP β).wt y : ℝ) : ℂ)
          * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re)

namespace CellLayerData

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def meanStretch (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
    CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p))

def stretchNegMean (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
    ENNReal.ofReal (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))

def formNeg (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)))
    + ∫⁻ p in halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1

def formScalar (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) (F : ℝ → Space → Space) : ℝ :=
  D.coercivity * D.cert.multiplierWeight ^ 2 * ∑ i, κ i ^ 2
    - ∑ i, κ i * multiplierRight (D.pieces q) v G H (D.cert.actuator i)
    - D.coercivity * D.cert.rows F ^ 2 - D.pinWeight * vecNorm (fun i => pinValue (D.cert.pin i) G) ^ 2

end CellLayerData

namespace ModeCoefficients

def value (a : ModeCoefficients) (x2 xc x1 xo x0 : ℝ) : ℝ :=
  a.hess * x2 ^ 2 + a.curlHess * xc ^ 2 + a.curl * xo ^ 2 + a.strain * x1 ^ 2 + a.velocity * x0 ^ 2

theorem modeDensity_eq_value {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (wt : Space → ℝ) (m : ℕ) (ι : ℤ × ℤ) (p : ℝ × ℝ) (x2 xc x1 xo x0 : ℝ) :
    w.modeDensity P h wt (labelHarmonic m ι) (planePoint p) x2 xc x1 xo x0
      = (ofPieces w P h wt m ι p).value x2 xc x1 xo x0 := by
  simp only [PieceWeights.modeDensity, value, ofPieces]

end ModeCoefficients

end CertCell

end Breakdown
