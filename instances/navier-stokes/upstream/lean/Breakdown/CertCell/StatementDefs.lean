import Breakdown.Cert.ExtendedCoerciveDefs
import Breakdown.FracCell.StatementDefs
import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.EnergyDefs
import Breakdown.FracCell.MeshSkeletonSegment

section

open scoped ContDiff ENNReal

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

end SteadyCert

end Breakdown

end
end

section

section

open scoped ContDiff ENNReal

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

end CellCert

end Breakdown

end

end

section

open Matrix

noncomputable section

namespace Breakdown.CellCert.Finite

end Breakdown.CellCert.Finite

end

end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

end Assembly

end CellCert

end Breakdown

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly

end Exterior

end CellCert

end Breakdown

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBases

variable (B : CellBases)

end CellBases

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

end CellScalars

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

end CellCert

end Breakdown

end

end

section

open Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

namespace ParamData

variable {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D)

end ParamData

end Breakdown.CellCert.CellFormula

end

end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

namespace FaceSegment

variable (S : FaceSegment)

end FaceSegment

namespace CellDatum

variable {modes : Finset ℤ} {Q q segs psegs corners : ℕ}

end CellDatum

namespace CellLayout

variable (L : CellLayout)

end CellLayout

namespace CellLayout

variable (L : CellLayout)

end CellLayout

namespace CellLayout

variable (L : CellLayout)

end CellLayout

namespace CellLayout

variable (L : CellLayout)

end CellLayout

end CellFormula

end CellCert

end Breakdown

end

end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellEnergy

open CellAnalysis CellFormula

section Rows

variable {D : Type} [Fintype D] [DecidableEq D]

end Rows

section Cell

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
  (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q)

end Cell

section Low

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)

end Low

section Forms

open SteadyCert Assembly

end Forms

end CellEnergy

end CellCert

end Breakdown

end

end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

section Synthesis

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)

end Synthesis

section Pieces

end Pieces

section RowFunctional

variable {k N slots : ℕ} (c : FracCellData k N) (α : ℝ)

end RowFunctional

section Canonical

end Canonical

end CellFormula

end CellCert

end Breakdown

end

end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

end CellCoordinates

end CellCert

end Breakdown

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

end CellCoordinates

end CellCert

end Breakdown

end

end

section

open scoped ContDiff

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

end GivenFields

end CellCert

end Breakdown

end

end

section

open scoped ContDiff

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

end GivenFields

end CellCert

end Breakdown

end

end

section

open MeasureTheory

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

end Reduction

end CellCert

end Breakdown

end

end

section

open MeasureTheory

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

end Reduction

end CellCert

end Breakdown

end

end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

end GivenFields

end CellCert

end Breakdown

end

end

section

open MeasureTheory Polynomial

open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

end Spectral

end CellCert

end Breakdown

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

end GivenModel

end CellCert

end Breakdown

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

end Reduction

end CellCert

end Breakdown

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

end Reduction

end CellCert

end Breakdown

end

end

section

open scoped ContDiff ENNReal

open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly GivenFields Exterior CellAnalysis CellCoordinates CellFormula

open _root_.Breakdown.CellCert.Finite

section Choices

end Choices

end CellSystem

end CellCert

end Breakdown

end

end

end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

end CellBox

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis

end CellCert

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshSkeletonInternal

end MeshSkeletonInternal

end Breakdown.CellCert.CellCoordinates

end
end

section

open Matrix

open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Coupling

def quadForm {n : Type*} [Fintype n] (A : Matrix n n ℂ) (x : n → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

def inverseWeightedSq {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℂ) (a : n → ℂ) : ℝ :=
  quadForm D⁻¹ a

def realQuadForm {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℂ) : ℝ :=
  (star x ⬝ᵥ (A.map (fun t : ℝ => (t : ℂ)) *ᵥ x)).re

end Coupling

end CertCell

end Breakdown

end
end

section

open scoped ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

open CellCert.CellAnalysis (CellBox IsCellBox cylPoint radialUnit angularUnit axialUnit)

def labelTime (ι : ℤ × ℤ) : ℤ := 2 * ι.2 - ι.1

def labelAzimuth (m : ℕ) (ι : ℤ × ℤ) : ℤ := ι.1 * m

def labelHarmonic (m : ℕ) (ι : ℤ × ℤ) : ℤ × ℤ := (labelTime ι, labelAzimuth m ι)

def labelFlip (ι : ℤ × ℤ) : ℤ × ℤ := (-ι.1, ι.2 - ι.1)

def flipLabel (ξ : ℤ × ℤ) : ℤ × ℤ := (ξ.1, -ξ.2)

def IsLatticeHarmonic (m : ℕ) (ξ : ℤ × ℤ) : Prop := ∃ ι, labelHarmonic m ι = ξ

def planePoint (p : ℝ × ℝ) : Space := cylPoint p.1 0 p.2

def labelVel (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  modeVel (labelHarmonic m ι) v 0 (planePoint p)

def labelGrad (m : ℕ) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    Fin 3 × Fin 3 → ℂ :=
  modeGrad (labelHarmonic m ι) G 0 (planePoint p)

def flipPoint (y : Space) : Space :=
  y 0 • unitVector 0 - y 1 • unitVector 1 - y 2 • unitVector 2

def frameSign (a : Fin 3) : ℝ := if a = 0 then 1 else -1

def frameUnit (θ : ℝ) : Fin 3 → Space := ![radialUnit θ, angularUnit θ, axialUnit]

def pointAngle (y : Space) : ℝ := Complex.arg ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)

def pointPlane (y : Space) : ℝ × ℝ := (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), y 2)

def labelPhase (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * θ : ℝ) : ℂ) * Complex.I)

structure CellPoly where
  deg : ℕ
  coef : Fin (deg + 1) → Fin (deg + 1) → ℂ

namespace CellPoly

def eval (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) : ℂ :=
  ∑ i, ∑ j, P.coef i j * ((K.refR p.1 : ℂ) ^ (i : ℕ)) * ((K.refZ p.2 : ℂ) ^ (j : ℕ))

def zero : CellPoly := ⟨0, fun _ _ => 0⟩

end CellPoly

structure CellMesh where
  count : ℕ
  box : Fin count → CellBox
  resolved : Fin count → Finset (ℤ × ℤ)
  tested : Fin count → Finset (ℤ × ℤ)
  band : Fin count → Finset (ℤ × ℤ)
  skeletonDeg : Fin count → ℤ × ℤ → ℤ
  volumeDeg : Fin count → ℤ × ℤ → ℕ

namespace CellMesh

variable (M : CellMesh)

def closedHalfPlane : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ Set.Ici 0

def region : Set (ℝ × ℝ) := ⋃ K, (M.box K).rect

def exterior : Set (ℝ × ℝ) := closedHalfPlane \ M.region

def maxVolumeDeg (K : Fin M.count) : ℕ := (M.resolved K).sup (M.volumeDeg K)

end CellMesh

structure IsCellMesh (M : CellMesh) : Prop where
  box_valid : ∀ K, IsCellBox (M.box K)
  boxes_apart : ∀ K L, K ≠ L → volume ((M.box K).rect ∩ (M.box L).rect) = 0
  tested_sub : ∀ K, M.tested K ⊆ M.resolved K
  band_apart : ∀ K, Disjoint (M.resolved K) (M.band K)
  resolved_neg : ∀ K ι, ι ∈ M.resolved K → -ι ∈ M.resolved K
  tested_neg : ∀ K ι, ι ∈ M.tested K → -ι ∈ M.tested K
  band_neg : ∀ K ι, ι ∈ M.band K → -ι ∈ M.band K
  axis_resolved : ∀ K, (M.box K).IsAxis → ∀ ι ∈ M.resolved K, ι.1 = 0
  skeletonDeg_ge : ∀ K, ∀ ι ∈ M.resolved K, -1 ≤ M.skeletonDeg K ι
  skeletonDeg_tested : ∀ K, ∀ ι ∈ M.tested K, 2 ≤ M.skeletonDeg K ι
  volumeDeg_ge : ∀ K, ∀ ι ∈ M.resolved K, max (M.skeletonDeg K ι) 0 + 2 ≤ (M.volumeDeg K ι : ℤ)
  skeletonDeg_neg : ∀ K ι, M.skeletonDeg K (-ι) = M.skeletonDeg K ι
  volumeDeg_neg : ∀ K ι, M.volumeDeg K (-ι) = M.volumeDeg K ι

structure CellVecField (count : ℕ) where
  labels : Fin count → Finset (ℤ × ℤ)
  comp : Fin count → ℤ × ℤ → Fin 3 → CellPoly

structure CellMatField (count : ℕ) where
  labels : Fin count → Finset (ℤ × ℤ)
  comp : Fin count → ℤ × ℤ → Fin 3 → Fin 3 → CellPoly

def labelValueAt {count : ℕ} (box : Fin count → CellBox) (comp : Fin count → ℤ × ℤ → CellPoly)
    (K : Fin count) (ι : ℤ × ℤ) (s : ℝ) (p : ℝ × ℝ) : ℂ :=
  if 0 ≤ p.2 then (comp K ι).eval (box K) p else (s : ℂ) * (comp K (labelFlip ι)).eval (box K) (p.1, -p.2)

namespace CellVecField

variable {count : ℕ} (F : CellVecField count)

def planeValue (box : Fin count → CellBox) (K : Fin count) (ι : ℤ × ℤ) (a : Fin 3) (p : ℝ × ℝ) : ℂ :=
  labelValueAt box (fun K ι => F.comp K ι a) K ι (frameSign a) p

def field (box : Fin count → CellBox) (m : ℕ) (σ : ℝ) (y : Space) : Space :=
  ∑ K, Set.indicator (box K).solid (fun y =>
    ∑ ι ∈ F.labels K, ∑ a : Fin 3,
      (labelPhase m ι σ (pointAngle y) * F.planeValue box K ι a (pointPlane y)).re
        • frameUnit (pointAngle y) a) y

def IsConjugateClosed (box : Fin count → CellBox) : Prop :=
  (∀ K ι, ι ∈ F.labels K → -ι ∈ F.labels K ∧ labelFlip ι ∈ F.labels K) ∧
    ∀ K ι a, ∀ p : ℝ × ℝ, (F.comp K (-ι) a).eval (box K) p = starRingEnd ℂ ((F.comp K ι a).eval (box K) p)

end CellVecField

namespace CellMatField

variable {count : ℕ} (F : CellMatField count)

def planeValue (box : Fin count → CellBox) (K : Fin count) (ι : ℤ × ℤ) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  labelValueAt box (fun K ι => F.comp K ι a b) K ι (frameSign a * frameSign b) p

def frameMap (θ : ℝ) (x : Fin 3 → Fin 3 → ℝ) : Space →L[ℝ] Space :=
  ∑ a : Fin 3, ∑ b : Fin 3, x a b • (innerSL ℝ (frameUnit θ b)).smulRight (frameUnit θ a)

def field (box : Fin count → CellBox) (m : ℕ) (σ : ℝ) (y : Space) : Space →L[ℝ] Space :=
  ∑ K, Set.indicator (box K).solid (fun y =>
    ∑ ι ∈ F.labels K, frameMap (pointAngle y) (fun a b =>
      (labelPhase m ι σ (pointAngle y) * F.planeValue box K ι a b (pointPlane y)).re)) y

def IsConjugateClosed (box : Fin count → CellBox) : Prop :=
  (∀ K ι, ι ∈ F.labels K → -ι ∈ F.labels K ∧ labelFlip ι ∈ F.labels K) ∧
    ∀ K ι a b, ∀ p : ℝ × ℝ,
      (F.comp K (-ι) a b).eval (box K) p = starRingEnd ℂ ((F.comp K ι a b).eval (box K) p)

end CellMatField

structure ModelPolys (count : ℕ) where
  velocity : CellVecField count
  vorticity : CellVecField count
  strain : CellMatField count
  vorticityGrad : CellMatField count
  periodInverse : ℝ

structure ModelErrors where
  velocity : ℝ
  vorticity : ℝ
  strain : ℝ
  vorticityGrad : ℝ
  velocityHigh : ℝ
  vorticityHigh : ℝ
  strainHigh : ℝ
  vorticityGradHigh : ℝ
  periodInverse : ℝ

structure ModeCharges where
  curl : ℤ × ℤ → ℝ × ℝ → ℝ
  product : ℤ × ℤ → ℝ × ℝ → ℝ
  gradient : ℤ × ℤ → ℝ × ℝ → ℝ
  length : ℤ × ℤ → ℝ × ℝ → ℝ

structure RowValues (count rowCount : ℕ) where
  cellOf : Fin rowCount → Fin count
  labelOf : Fin rowCount → ℤ × ℤ
  realPart : Fin rowCount → Bool
  testOf : Fin rowCount → ℕ
  testWeight : Fin count → ℤ × ℤ → ℝ
  testCount : Fin count → ℤ × ℤ → ℕ
  testField : Fin count → ℤ × ℤ → ℕ → Fin 3 → CellPoly

structure CellLayerData (k : ℕ) (C : Type) (nE nM : ℕ) where
  cert : ExtendedCertificateData k
  pieces : (Fin k → ℝ) → PieceWeights C nE nM
  bounds : (Fin k → ℝ) → HarmonicBounds
  given : ℝ → Space → Space
  givenHess : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)
  givenLabels : Finset (ℤ × ℤ)
  azimuthOrder : ℕ
  mesh : CellMesh
  rows : RowValues mesh.count cert.rowCount
  model : ModelPolys mesh.count
  modelErrors : Fin mesh.count → ModelErrors
  charges : Option (Fin mesh.count) → ModeCharges
  pinValues : Fin k → CellMatField mesh.count
  actuatorValues : Fin k → CellVecField mesh.count
  coercivity : ℝ
  formCoercivity : ℝ
  pinWeight : ℝ

namespace CellLayerData

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def pinField (i : Fin k) : ℝ → Space → (Space →L[ℝ] Space) :=
  (D.pinValues i).field D.mesh.box D.azimuthOrder

end CellLayerData

def halfPlane : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioi 0

namespace CellLayerData

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def labelDensity (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  (D.pieces q).modeTerm (D.cert.period q) (D.bounds q) D.cert.weightFn v G H (labelHarmonic D.azimuthOrder ι) 0
    (planePoint p)

def stretchPosMean (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
    ENNReal.ofReal (CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))

def formPos (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1))
    + ∫⁻ p in halfPlane, D.stretchPosMean v G p * ENNReal.ofReal p.1

end CellLayerData

structure ModeCoefficients where
  hess : ℝ
  curlHess : ℝ
  curl : ℝ
  strain : ℝ
  velocity : ℝ

namespace ModeCoefficients

def ofPieces {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (wt : Space → ℝ)
    (m : ℕ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ModeCoefficients where
  hess := w.convD (w.classOf (labelHarmonic m ι)) (planePoint p) - w.c
  curlHess := 1 - w.shareHat h (labelHarmonic m ι) (planePoint p) - w.convD (w.classOf (labelHarmonic m ι)) (planePoint p)
  curl := w.coefA P h (labelHarmonic m ι) (planePoint p) - w.convZ (w.classOf (labelHarmonic m ι)) (planePoint p)
  strain := w.coefAA h wt (labelHarmonic m ι) (planePoint p)
  velocity := w.coefB P h (labelHarmonic m ι) (planePoint p)

end ModeCoefficients

end CertCell

end Breakdown

end
end

section

open scoped ContDiff ENNReal ComplexOrder

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

structure IsModeClass (Γ : Set Symmetry) (m : ℕ) : Prop where
  order_pos : 1 ≤ m
  twisted : ∃ γ ∈ Γ, (∀ y, γ.1 y = axialRot (Real.pi / m) y) ∧ γ.2 = 1 / 2
  flip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0

structure HasMeasurableBoundData {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) : Prop where
  eps_speed_measurable : ∀ β, Measurable (m.epsP β).speed
  mu_speed_measurable : ∀ β, Measurable (m.muP β).speed
  amplitudes_measurable : ∀ β, Measurable (h.ampW β) ∧ Measurable (h.ampGradW β) ∧ Measurable (h.ampVort β)
    ∧ Measurable (h.ampGradVort β)
  sups_measurable : Measurable h.supVort ∧ Measurable h.supGradVort

structure IsHarmonicExpansion (S : Finset (ℤ × ℤ)) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop where
  symmetric : ∀ β ∈ S, -β ∈ S
  field_span : ∀ σ y i, W σ y i = ∑ β ∈ S, (modeVel β W σ y i).re
  gradient_span : ∀ σ y i j, fderiv ℝ (W σ) y (unitVector j) i = ∑ β ∈ S, (modeGrad β (gradField W) σ y (i, j)).re
  hessian_span : ∀ σ y i j l, HW σ y (unitVector j) (unitVector l) i = ∑ β ∈ S, (modeSecondDeriv β HW σ y (i, j, l)).re

def azimuthPhase (m : ℕ) (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (((n * m * θ : ℝ) : ℂ) * Complex.I)

def patch (ρ₁ ρ₂ h : ℝ) : Set (ℝ × ℝ) := Set.Icc ρ₁ ρ₂ ×ˢ Set.Icc 0 h

def patchGradSq (k : ℤ) (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖fderiv ℝ φ p (1, 0)‖ ^ 2 + ‖fderiv ℝ φ p (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖φ p‖ ^ 2 / p.1 ^ 2

structure PlaneSegment where
  lower : ℝ
  upper : ℝ
  height : ℝ
  testCount : ℕ
  test : Fin testCount → ℝ → ℝ

structure IsPlaneSegment (S : PlaneSegment) : Prop where
  lower_pos : 0 < S.lower
  lower_lt_upper : S.lower < S.upper
  height_pos : 0 < S.height
  test_continuous : ∀ j, Continuous (S.test j)

structure CrossWaveEntry where
  azimuthOrder : ℕ
  waveModes : Finset ℤ
  strainMode : ℤ → ℝ × ℝ → Fin 3 × Fin 3 → ℂ
  vorticityGradMode : ℤ → ℝ × ℝ → Fin 3 × Fin 3 × Fin 3 → ℂ
  region : Set (ℝ × ℝ)
  strainBound : ℝ
  vorticityGradBound : ℝ
  balance : ℝ
  length : ℝ

structure IsCrossWaveEntry (X : CrossWaveEntry) : Prop where
  order_pos : 1 ≤ X.azimuthOrder
  strainBound_nonneg : 0 ≤ X.strainBound
  vorticityGradBound_nonneg : 0 ≤ X.vorticityGradBound
  balance_pos : 0 < X.balance
  length_pos : 0 < X.length
  strain_majorant : ∀ p ∈ X.region, ∀ θ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j : Fin 3,
      (∑ n ∈ X.waveModes, azimuthPhase X.azimuthOrder n θ
        * ((X.strainMode n p (i, j) + X.strainMode n p (j, i)) / 2)) * u j) ≤ X.strainBound ^ 2 * cnormSq u
  vorticityGrad_majorant : ∀ p ∈ X.region, ∀ θ (u : Fin 3 → ℂ), cnormSq (fun j => ∑ l : Fin 3,
      (∑ n ∈ X.waveModes, azimuthPhase X.azimuthOrder n θ
        * curlGradOfSecondDeriv (X.vorticityGradMode n p) (j, l)) * u l) ≤ X.vorticityGradBound ^ 2 * cnormSq u

end Bridge

end CertCell

end Breakdown

end
end

section

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

structure SignedTree (A B : Type) where
  Leaf : Type
  leafFintype : Fintype Leaf
  Node : Type
  nodeFintype : Fintype Node
  Column : Type
  columnFintype : Fintype Column
  leafForm : Leaf → Matrix (A ⊕ B) (A ⊕ B) ℝ
  leafNode : Leaf → Node
  parent : Node → Option Node
  root : Node
  front : Node → Matrix (A ⊕ B) (A ⊕ B) ℝ
  pivots : Node → Finset (A ⊕ B)
  slack : Node → A ⊕ B → ℝ
  columnNode : Column → Node
  column : Column → A ⊕ B → ℝ

namespace SignedTree

variable {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)

open Classical in
def nodeInput (ν : T.Node) : Matrix (A ⊕ B) (A ⊕ B) ℝ :=
  haveI := T.leafFintype; haveI := T.nodeFintype
  (∑ l ∈ Finset.univ.filter (fun l => T.leafNode l = ν), T.leafForm l)
    + ∑ μ ∈ Finset.univ.filter (fun μ => T.parent μ = some ν), T.front μ

end SignedTree

structure PassesPivotCount {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B) : Prop where
  every_variable_pivoted : ∀ j, ∃ ν, j ∈ T.pivots ν
  slack_positive : ∀ ν, ∀ j ∈ T.pivots ν, 0 < T.slack ν j
  root_front_nonneg : ∀ x, 0 ≤ quadValue (T.front T.root) x
  column_count : (haveI := T.columnFintype; Fintype.card T.Column) ≤ Fintype.card B

def pivotDiagonal {n : Type*} [DecidableEq n] (pivot : Finset n) (δ : n → ℝ) : Matrix n n ℝ :=
  diagonal (fun j => if j ∈ pivot then δ j else 0)

def slackRemainder {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p] [Fintype q]
    (M S : Matrix n n ℝ) (pivot : Finset n) (δ : n → ℝ) (Fp : Matrix n p ℝ) (Fm : Matrix n q ℝ) :
    Matrix n n ℝ :=
  M - pivotDiagonal pivot δ - Fp * Fpᵀ + Fm * Fmᵀ - S

def complexDiagonal {n : Type*} [DecidableEq n] (pivot : Finset n) (δ : n → ℝ) : Matrix n n ℂ :=
  (pivotDiagonal pivot δ).map (fun t : ℝ => (t : ℂ))

def complexSlackRemainder {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p] [Fintype q]
    (M S : Matrix n n ℂ) (pivot : Finset n) (δ : n → ℝ) (Fp : Matrix n p ℂ) (Fm : Matrix n q ℂ) :
    Matrix n n ℂ :=
  M - complexDiagonal pivot δ - Fp * Fpᴴ + Fm * Fmᴴ - S

def ofRealVec {m : Type*} (y : m → ℝ) : m → ℂ := fun k => (y k : ℂ)

def realRestriction {n m : Type*} [Fintype n] (E : Matrix n m ℂ) (M : Matrix n n ℂ) : Matrix m m ℝ :=
  (Eᴴ * M * E).map Complex.re

def realColumns {n m q : Type*} [Fintype n] (E : Matrix n m ℂ) (t : ℝ) (F : Matrix n q ℂ) :
    q ⊕ q → m → ℝ
  | Sum.inl c => fun k => Real.sqrt t * ((Eᴴ *ᵥ fun i => F i c) k).re
  | Sum.inr c => fun k => Real.sqrt t * ((Eᴴ *ᵥ fun i => F i c) k).im

structure CoordinateRealification (n m : Type) where
  realIndex : n → Option m
  imagIndex : n → Option m
  imagSign : n → ℝ

structure IsCoordinateOn {n m : Type} (R : CoordinateRealification n m) (pivot : Finset n) :
    Prop where
  sign_sq : ∀ j ∈ pivot, R.imagSign j ^ 2 = 1
  real_ne_imag : ∀ j ∈ pivot, ∀ k, R.realIndex j = some k → R.imagIndex j ≠ some k

namespace CoordinateRealification

variable {n m : Type} (R : CoordinateRealification n m)

def matrix [DecidableEq m] : Matrix n m ℂ := fun j k =>
  (if R.realIndex j = some k then 1 else 0)
    + (R.imagSign j : ℂ) * Complex.I * (if R.imagIndex j = some k then 1 else 0)

def Owns (j : n) (k : m) : Prop := R.realIndex j = some k ∨ R.imagIndex j = some k

open Classical in
def pivotImage [Fintype m] (pivot : Finset n) : Finset m :=
  Finset.univ.filter (fun k => ∃ j ∈ pivot, R.Owns j k)

open Classical in
def slackOn (pivot : Finset n) (s : n → ℝ) (k : m) : ℝ :=
  ∑ j ∈ pivot, if R.Owns j k then s j else 0

end CoordinateRealification

namespace SignedTree

variable {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)

open Classical in
def nodeColumns (ν : T.Node) : Matrix (A ⊕ B) T.Column ℝ := fun i c =>
  if T.columnNode c = ν then T.column c i else 0

end SignedTree

structure RealNodeData (A B : Type) where
  Pos : Type
  posFintype : Fintype Pos
  input : Matrix (A ⊕ B) (A ⊕ B) ℝ
  base : Matrix (A ⊕ B) (A ⊕ B) ℝ
  pivotValue : A ⊕ B → ℝ
  weight : A ⊕ B → ℝ
  radius : A ⊕ B → ℝ
  posColumns : Matrix (A ⊕ B) Pos ℝ

structure ComplexNodeData (A B : Type) where
  Index : Type
  indexFintype : Fintype Index
  Pos : Type
  posFintype : Fintype Pos
  Neg : Type
  negFintype : Fintype Neg
  coords : CoordinateRealification Index (A ⊕ B)
  factor : ℝ
  input : Matrix Index Index ℂ
  base : Matrix Index Index ℂ
  pivot : Finset Index
  pivotValue : Index → ℝ
  weight : Index → ℝ
  radius : Index → ℝ
  posColumns : Matrix Index Pos ℂ
  negColumns : Matrix Index Neg ℂ

end Breakdown.CertCell.Certificate

end
end

section

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

open Classical in
structure PassesRealNodeEnclosure {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (D : RealNodeData A B) (E F : Matrix (A ⊕ B) (A ⊕ B) ℝ) : Prop where
  input_lower : ∀ x, quadValue D.input x ≤ quadValue (T.nodeInput ν) x + quadValue E (fun i => |x i|)
  input_symm : D.inputᵀ = D.input
  base_symm : D.baseᵀ = D.base
  weight_pos : ∀ j, 0 < D.weight j
  input_error_nonneg : ∀ i j, 0 ≤ E i j
  input_error_symm : Eᵀ = E
  front_error_nonneg : ∀ i j, 0 ≤ F i j
  front_error_symm : Fᵀ = F
  row_bound : ∀ i, D.weight i * ∑ j, (|(haveI := D.posFintype; haveI := T.columnFintype;
    slackRemainder D.input D.base (T.pivots ν) D.pivotValue D.posColumns (T.nodeColumns ν)) i j|
      + E i j + F i j) / D.weight j ≤ D.radius i
  front_upper : ∀ x, quadValue (T.front ν) x
    ≤ quadValue (D.base - pivotDiagonal (Finset.univ \ T.pivots ν) D.radius) x
      + quadValue F (fun i => |x i|)
  slack_le : ∀ j ∈ T.pivots ν, T.slack ν j ≤ D.pivotValue j - D.radius j

open Classical in
structure PassesComplexNodeEnclosure {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B)
    (ν : T.Node) (D : ComplexNodeData A B) (E F : Matrix D.Index D.Index ℝ) : Prop where
  coordinates : IsCoordinateOn D.coords D.pivot
  factor_nonneg : 0 ≤ D.factor
  input_self_adjoint : D.inputᴴ = D.input
  base_self_adjoint : D.baseᴴ = D.base
  weight_pos : ∀ j, 0 < D.weight j
  input_error_nonneg : ∀ i j, 0 ≤ E i j
  input_error_symm : Eᵀ = E
  front_error_nonneg : ∀ i j, 0 ≤ F i j
  front_error_symm : Fᵀ = F
  row_bound : ∀ i, D.weight i * (haveI := D.indexFintype; ∑ j,
    (‖(haveI := D.posFintype; haveI := D.negFintype;
      complexSlackRemainder D.input D.base D.pivot D.pivotValue D.posColumns D.negColumns) i j‖
      + E i j + F i j) / D.weight j) ≤ D.radius i
  input_lower : ∀ x, quadValue (haveI := D.indexFintype;
      D.factor • realRestriction D.coords.matrix D.input) x
    ≤ quadValue (T.nodeInput ν) x + D.factor * (haveI := D.indexFintype;
      quadValue E (fun i => ‖(D.coords.matrix *ᵥ ofRealVec x) i‖))
  front_upper : ∀ x, quadValue (T.front ν) x
    ≤ quadValue (haveI := D.indexFintype; D.factor • realRestriction D.coords.matrix
        (D.base - complexDiagonal (Finset.univ \ D.pivot) D.radius)) x
      + D.factor * (haveI := D.indexFintype;
        quadValue F (fun i => ‖(D.coords.matrix *ᵥ ofRealVec x) i‖))
  pivots_eq : T.pivots ν = D.coords.pivotImage D.pivot
  slack_le : ∀ k ∈ T.pivots ν,
    T.slack ν k ≤ D.factor * D.coords.slackOn D.pivot (fun j => D.pivotValue j - D.radius j) k
  columns : ∃ e : D.Neg ⊕ D.Neg → T.Column, Function.Injective e ∧ ∀ c,
    T.columnNode (e c) = ν ∧
      T.column (e c) = (haveI := D.indexFintype; realColumns D.coords.matrix D.factor D.negColumns c)

def PassesNodeEnclosure {A B : Type} [Fintype A] [Fintype B] (T : SignedTree A B) (ν : T.Node) :
    Prop :=
  (∃ (D : RealNodeData A B) (E F : Matrix (A ⊕ B) (A ⊕ B) ℝ), PassesRealNodeEnclosure T ν D E F) ∨
    ∃ (D : ComplexNodeData A B) (E F : Matrix D.Index D.Index ℝ), PassesComplexNodeEnclosure T ν D E F

end Breakdown.CertCell.Certificate

end
end

section

open scoped ENNReal ComplexOrder

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

open CellCert.CellAnalysis (CellBox IsCellBox)

open CellCert.GivenFields (ChartParams IsChartParams chartT heightRatio Spline TensorMesh IsTensorMesh
  cellCount atFirst atSecond tDeriv xDeriv)

def CellPoly.scale (c : ℂ) (P : CellPoly) : CellPoly := ⟨P.deg, fun i j => c * P.coef i j⟩

def rowPartFactor (realPart : Bool) : ℂ := if realPart then 1 else -Complex.I

namespace RowValues

variable {count rowCount : ℕ} (R : RowValues count rowCount)

open Classical in
def generator (a : Fin rowCount) : CellVecField count where
  labels K := if K = R.cellOf a then {R.labelOf a, labelFlip (R.labelOf a)} else ∅
  comp K ι c := if K = R.cellOf a ∧ ι = R.labelOf a then
      (R.testField K ι (R.testOf a) c).scale (rowPartFactor (R.realPart a)) else CellPoly.zero

def generatorField (box : Fin count → CellBox) (m : ℕ) (a : Fin rowCount) : ℝ → Space → Space :=
  (R.generator a).field box m

def testValue (box : Fin count → CellBox) (a : Fin rowCount) (c : Fin 3) (p : ℝ × ℝ) : ℂ :=
  (R.testField (R.cellOf a) (R.labelOf a) (R.testOf a) c).eval (box (R.cellOf a)) p

def fieldPairingMatrix (box : Fin count → CellBox) (m : ℕ) : Matrix (Fin rowCount) (Fin rowCount) ℝ :=
  fun a b => periodPairing (R.generatorField box m a) (R.generatorField box m b)

open Classical in
def mix (box : Fin count → CellBox) (m : ℕ) : Matrix (Fin rowCount) (Fin rowCount) ℝ :=
  if h : (R.fieldPairingMatrix box m).IsHermitian then h.cfc (fun x => (Real.sqrt x)⁻¹) else 0

def rowFieldOf (box : Fin count → CellBox) (m : ℕ) (a : Fin rowCount) : ℝ → Space → Space :=
  fun σ y => ∑ b, R.mix box m a b • R.generatorField box m b σ y

def rowWeightOf (c : ℝ) (a : Fin rowCount) : ℝ := R.testWeight (R.cellOf a) (R.labelOf a) / c

def testBlockMatrix (box : Fin count → CellBox) (K : Fin count) (ι : ℤ × ℤ) :
    Matrix (Fin (R.testCount K ι)) (Fin (R.testCount K ι)) ℂ := fun i j =>
  ∫ p in (box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    (R.testField K ι j c).eval (box K) p * starRingEnd ℂ ((R.testField K ι i c).eval (box K) p)

end RowValues

namespace Instance

structure IsRowValues {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ) : Prop where
  mesh_valid : IsCellMesh M
  azimuth_pos : 0 < m
  row_tested : ∀ a, R.labelOf a ∈ M.tested (R.cellOf a)
  test_index : ∀ a, R.testOf a < R.testCount (R.cellOf a) (R.labelOf a)
  rows_distinct : ∀ a b, R.cellOf a = R.cellOf b → R.labelOf a = R.labelOf b → R.testOf a = R.testOf b →
    R.realPart a = R.realPart b → a = b
  weight_pos : ∀ K, ∀ ι ∈ M.tested K, 0 < R.testWeight K ι
  weight_le : ∀ K, ∀ ι ∈ M.tested K, R.testWeight K ι ≤ tauMax
  weight_neg : ∀ K, ∀ ι ∈ M.tested K, R.testWeight K (-ι) = R.testWeight K ι
  tests_conj : ∀ K, ∀ ι ∈ M.tested K, R.testCount K (-ι) = R.testCount K ι ∧
    ∀ i < R.testCount K ι, ∀ c (p : ℝ × ℝ),
      (R.testField K (-ι) i c).eval (M.box K) p = starRingEnd ℂ ((R.testField K ι i c).eval (M.box K) p)
  rows_one_member : ∀ a b, R.cellOf a = R.cellOf b → R.labelOf a = -R.labelOf b → R.labelOf a = R.labelOf b
  zero_label_real : ∀ a, R.labelOf a = -R.labelOf a → R.realPart a = true
  rows_complete : ∀ K, ∀ ι ∈ M.tested K, ∀ i < R.testCount K ι, ∀ part : Bool, (ι = -ι → part = true) →
    ∃ a, R.cellOf a = K ∧ (R.labelOf a = ι ∨ R.labelOf a = -ι) ∧ R.testOf a = i ∧ R.realPart a = part
  test_solenoidal : ∀ a (p : ℝ × ℝ),
    (p.1 : ℂ) * deriv (fun r => R.testValue M.box a 0 (r, p.2)) p.1
      + R.testValue M.box a 0 p
      + Complex.I * (labelAzimuth m (R.labelOf a) : ℂ) * R.testValue M.box a 1 p
      + (p.1 : ℂ) * deriv (fun z => R.testValue M.box a 2 (p.1, z)) p.2 = 0
  test_axis : ∀ a (p : ℝ × ℝ), (M.box (R.cellOf a)).IsAxis → p.1 = 0 →
    R.testValue M.box a 0 p = 0 ∧ R.testValue M.box a 1 p = 0
  block_posDef : ∀ K, ∀ ι ∈ M.tested K, (R.testBlockMatrix M.box K ι).PosDef

structure IsRowInstance {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (tauMax : ℝ) : Prop where
  values : IsRowValues D.mesh D.rows D.azimuthOrder tauMax
  rowField_eq : D.cert.rowField = D.rows.rowFieldOf D.mesh.box D.azimuthOrder
  rowWeight_eq : D.cert.rowWeight = D.rows.rowWeightOf D.coercivity
  coercivity_pos : 0 < D.coercivity
  rowBound_nonneg : 0 ≤ D.cert.rowBound
  rowBound_ge : tauMax / D.coercivity ≤ D.cert.rowBound ^ 2

structure ChartScalar where
  upper : Spline
  lower : Spline
  decay : ℕ

namespace ChartScalar

def eval (P : ChartParams) (S : ChartScalar) (y : Space) : ℝ :=
  (1 - chartT P y) ^ S.decay *
    (if 0 ≤ y 2 then (S.upper.evalHalf (chartT P y) (heightRatio y)).re
      else (S.lower.evalHalf (chartT P y) (-heightRatio y)).re)

def mirror (S : ChartScalar) : ChartScalar := ⟨S.lower, S.upper, S.decay⟩

end ChartScalar

structure SplineJoins (a : ℕ) (S : Spline) : Prop where
  mesh : IsTensorMesh S.mesh
  t_joins : ∀ i, 1 ≤ i → i < cellCount S.mesh.tBreaks → ∀ j < cellCount S.mesh.xBreaks, ∀ o ≤ a,
    atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (tDeriv o (S.piece (i - 1) j))
      = atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (tDeriv o (S.piece i j))
  x_joins : ∀ j, 1 ≤ j → j < cellCount S.mesh.xBreaks → ∀ i < cellCount S.mesh.tBreaks, ∀ o ≤ a,
    atSecond (S.mesh.xBreaks.getD j 0 : ℂ) (xDeriv o (S.piece i (j - 1)))
      = atSecond (S.mesh.xBreaks.getD j 0 : ℂ) (xDeriv o (S.piece i j))

structure IsJoinedScalar (a : ℕ) (S : ChartScalar) : Prop where
  upper : SplineJoins a S.upper
  lower : SplineJoins a S.lower
  same_t : S.upper.mesh.tBreaks = S.lower.mesh.tBreaks
  plane_joins : ∀ i < cellCount S.upper.mesh.tBreaks, ∀ o ≤ a,
    atSecond 0 (xDeriv o (S.upper.piece i 0))
      = MvPolynomial.C ((-1 : ℂ) ^ o) * atSecond 0 (xDeriv o (S.lower.piece i 0))

def IsConstantCore (tStar : ℝ) (S : ChartScalar) : Prop :=
  0 < tStar ∧ tStar ∈ S.upper.mesh.tBreaks ∧ ∃ v : ℂ, ∀ i < cellCount S.upper.mesh.tBreaks,
    S.upper.mesh.tBreaks.getD (i + 1) 1 ≤ tStar →
      (∀ j < cellCount S.upper.mesh.xBreaks, S.upper.piece i j = MvPolynomial.C v) ∧
      ∀ j < cellCount S.lower.mesh.xBreaks, S.lower.piece i j = MvPolynomial.C v

def IsFlatAtOrigin (S : ChartScalar) : Prop :=
  ∃ v : ℂ, (∀ j < cellCount S.upper.mesh.xBreaks, atFirst 0 (S.upper.piece 0 j) = MvPolynomial.C v) ∧
    ∀ j < cellCount S.lower.mesh.xBreaks, atFirst 0 (S.lower.piece 0 j) = MvPolynomial.C v

def HasNonnegValues (S : ChartScalar) : Prop :=
  ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ x → x ≤ 1 →
    0 ≤ (S.upper.evalHalf t x).re ∧ 0 ≤ (S.lower.evalHalf t x).re

structure StepDatum where
  mesh : TensorMesh
  upper : ℕ → ℕ → ℝ
  lower : ℕ → ℕ → ℝ
  decay : ℤ

namespace StepDatum

def upperValue (P : ChartParams) (S : StepDatum) (y : Space) : ℝ :=
  S.upper (CellCert.GivenFields.cellIndex S.mesh.tBreaks (chartT P y))
    (CellCert.GivenFields.cellIndex S.mesh.xBreaks (heightRatio y))

def lowerValue (P : ChartParams) (S : StepDatum) (y : Space) : ℝ :=
  S.lower (CellCert.GivenFields.cellIndex S.mesh.tBreaks (chartT P y))
    (CellCert.GivenFields.cellIndex S.mesh.xBreaks (-heightRatio y))

def eval (P : ChartParams) (S : StepDatum) (y : Space) : ℝ :=
  (1 - chartT P y) ^ S.decay *
    (if 0 ≤ y 2 then S.upperValue P y else S.lowerValue P y)

def mirror (S : StepDatum) : StepDatum := ⟨S.mesh, S.lower, S.upper, S.decay⟩

end StepDatum

def IsPositiveStep (S : StepDatum) : Prop :=
  IsTensorMesh S.mesh ∧ ∀ i j, i < cellCount S.mesh.tBreaks → j < cellCount S.mesh.xBreaks →
    0 < S.upper i j ∧ 0 < S.lower i j

structure EpsGiven where
  modes : Set (ℤ × ℤ)
  weight : ChartScalar
  share1 : StepDatum
  share2 : StepDatum
  len : StepDatum
  t0 : StepDatum
  t1 : StepDatum
  t2 : StepDatum
  t3 : StepDatum
  scale : StepDatum

structure MuGiven where
  modes : Set (ℤ × ℤ)
  weight : ChartScalar
  share : StepDatum
  t4 : StepDatum
  eta : ℝ

def EpsGiven.mirror (e : EpsGiven) : EpsGiven :=
  ⟨flipLabel '' e.modes, e.weight.mirror, e.share1.mirror, e.share2.mirror, e.len.mirror, e.t0.mirror,
    e.t1.mirror, e.t2.mirror, e.t3.mirror, e.scale.mirror⟩

def MuGiven.mirror (u : MuGiven) : MuGiven :=
  ⟨flipLabel '' u.modes, u.weight.mirror, u.share.mirror, u.t4.mirror, u.eta⟩

structure WeightValues (C : Type) (nE nM : ℕ) where
  chart : ChartParams
  centralRadius : ℝ
  classOf : ℤ × ℤ → C
  strainWeight : C → ChartScalar
  vorticityWeight : C → ChartScalar
  eps : Fin nE → EpsGiven
  mu : Fin nM → MuGiven
  c : ℝ
  cμ : ℝ

namespace WeightValues

variable {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM)

def epsPiece (frame : ℝ) (speed : Space → ℝ) (e : EpsGiven) (P : ChartParams) : EpsPiece where
  modes := e.modes
  frame := frame
  wt := e.weight.eval P
  share1 := e.share1.eval P
  share2 := e.share2.eval P
  len := e.len.eval P
  t0 := e.t0.eval P
  t1 := e.t1.eval P
  t2 := e.t2.eval P
  t3 := e.t3.eval P
  scale := e.scale.eval P
  speed := speed

def muPiece (frame : ℝ) (speed : Space → ℝ) (u : MuGiven) (P : ChartParams) : MuPiece where
  modes := u.modes
  frame := frame
  wt := u.weight.eval P
  share := u.share.eval P
  t4 := u.t4.eval P
  eta := u.eta
  speed := speed

def pieces (epsFrame : Fin nE → ℝ) (muFrame : Fin nM → ℝ) (epsSpeed : Fin nE → Space → ℝ)
    (muSpeed : Fin nM → Space → ℝ) : PieceWeights C nE nM where
  classOf := W.classOf
  convD c := (W.strainWeight c).eval W.chart
  convZ c := (W.vorticityWeight c).eval W.chart
  epsP β := epsPiece (epsFrame β) (epsSpeed β) (W.eps β) W.chart
  muP β := muPiece (muFrame β) (muSpeed β) (W.mu β) W.chart
  c := W.c
  cμ := W.cμ

end WeightValues

structure IsWeightValues {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM) : Prop where
  classes_finite : Finite C
  chart_valid : IsChartParams W.chart
  c_pos : 0 < W.c
  c_lt_one : W.c < 1
  cμ_pos : 0 < W.cμ
  cμ_lt_one : W.cμ < 1
  strain_joined : ∀ c, IsJoinedScalar 2 (W.strainWeight c)
  strain_core : ∀ c, IsConstantCore W.centralRadius (W.strainWeight c)
  strain_decay : ∀ c, (W.strainWeight c).decay = 0
  strain_nonneg : ∀ c, HasNonnegValues (W.strainWeight c)
  vorticity_joined : ∀ c, IsJoinedScalar 2 (W.vorticityWeight c)
  vorticity_core : ∀ c, IsConstantCore W.centralRadius (W.vorticityWeight c)
  vorticity_decay : ∀ c, (W.vorticityWeight c).decay = 0
  eps_joined : ∀ β, IsJoinedScalar 0 (W.eps β).weight
  eps_flat : ∀ β, IsFlatAtOrigin (W.eps β).weight
  eps_decay : ∀ β, (W.eps β).weight.decay = 1
  eps_nonneg : ∀ β, HasNonnegValues (W.eps β).weight
  eps_steps : ∀ β, IsPositiveStep (W.eps β).share1 ∧ IsPositiveStep (W.eps β).share2 ∧
    IsPositiveStep (W.eps β).len ∧ IsPositiveStep (W.eps β).t0 ∧ IsPositiveStep (W.eps β).t1 ∧
    IsPositiveStep (W.eps β).t2 ∧ IsPositiveStep (W.eps β).t3 ∧ IsPositiveStep (W.eps β).scale
  mu_joined : ∀ β, IsJoinedScalar 0 (W.mu β).weight
  mu_flat : ∀ β, IsFlatAtOrigin (W.mu β).weight
  mu_decay : ∀ β, (W.mu β).weight.decay = 2
  mu_nonneg : ∀ β, HasNonnegValues (W.mu β).weight
  mu_steps : ∀ β, IsPositiveStep (W.mu β).share ∧ IsPositiveStep (W.mu β).t4
  mu_eta_pos : ∀ β, 0 < (W.mu β).eta
  class_neg : ∀ ι, W.strainWeight (W.classOf (-ι)) = W.strainWeight (W.classOf ι) ∧
    W.vorticityWeight (W.classOf (-ι)) = W.vorticityWeight (W.classOf ι)

structure IsFlipClosedValues {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM)
    (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM)) : Prop where
  strain_flip : ∀ ι, W.strainWeight (W.classOf (flipLabel ι)) = (W.strainWeight (W.classOf ι)).mirror
  vorticity_flip : ∀ ι, W.vorticityWeight (W.classOf (flipLabel ι)) = (W.vorticityWeight (W.classOf ι)).mirror
  eps_flip : ∀ β, W.eps (epsMirror β) = (W.eps β).mirror
  mu_flip : ∀ β, W.mu (muMirror β) = (W.mu β).mirror

structure IsWeightInstance {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (W : WeightValues C nE nM) (epsFrame : (Fin k → ℝ) → Fin nE → ℝ) (muFrame : (Fin k → ℝ) → Fin nM → ℝ)
    (epsSpeed : Fin nE → Space → ℝ) (muSpeed : Fin nM → Space → ℝ)
    (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM)) : Prop where
  values : IsWeightValues W
  flip : IsFlipClosedValues W epsMirror muMirror
  pieces_eq : ∀ q ∈ D.cert.params, D.pieces q = W.pieces (epsFrame q) (muFrame q) epsSpeed muSpeed
  c_eq : W.c = D.coercivity
  eps_frame_flip : ∀ q β, epsFrame q (epsMirror β) = -epsFrame q β
  mu_frame_flip : ∀ q β, muFrame q (muMirror β) = -muFrame q β
  eps_speed_flip : ∀ β y, epsSpeed (epsMirror β) (flipPoint y) = epsSpeed β y
  mu_speed_flip : ∀ β y, muSpeed (muMirror β) (flipPoint y) = muSpeed β y

structure ActuatorShapeFacts (m : ℕ) (S : Finset (ℤ × ℤ)) (b : ℝ → Space → Space) : Prop where
  measurable : AEStronglyMeasurable (fun z : ℝ × Space => b z.1 z.2) volume
  periodic : IsTimePeriodic b
  bounded_support : ∃ B R : ℝ, ∀ σ y, ‖b σ y‖ ≤ B ∧ (R < ‖y‖ → b σ y = 0)
  square_finite : periodLIntegral (fun σ y => ‖b σ y‖ ^ 2) < ⊤
  gradient_measurable : AEStronglyMeasurable (fun z : ℝ × Space => gradField b z.1 z.2) volume
  gradient_periodic : IsTimePeriodic (gradField b)
  gradient_finite : periodLIntegral (fun σ y => matSq (gradField b σ y)) < ⊤
  weak_gradient : ∀ σ, IsWeakGradient (b σ) (gradField b σ)
  modes_in : ∀ ξ σ y, (pointPlane y).1 ≠ 0 → modeVel ξ b σ y ≠ 0 →
    ∃ ι ∈ S, labelHarmonic m ι = ξ ∨ labelHarmonic m ι = -ξ
  invariant : ∀ᵐ z : ℝ × Space,
    b (z.1 + 1 / 2) (axialRot (Real.pi / m) z.2) = axialRot (Real.pi / m) (b z.1 z.2) ∧
    b z.1 (flipPoint z.2) = flipPoint (b z.1 z.2)

structure IsActuatorInstance {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (modes : Fin k → Finset (ℤ × ℤ)) (jmax : ℕ) : Prop where
  azimuth_pos : 0 < D.azimuthOrder
  modes_bound : ∀ i, ∀ ι ∈ modes i, |ι.2| ≤ jmax ∧ |ι.2 - ι.1| ≤ jmax
  eps_avoid : ∀ q ∈ D.cert.params, ∀ β, ∀ ι : ℤ × ℤ, |ι.2| ≤ jmax → |ι.2 - ι.1| ≤ jmax →
    ¬ PieceWeights.inPiece ((D.pieces q).epsP β).modes (labelHarmonic D.azimuthOrder ι)
  mu_avoid : ∀ q ∈ D.cert.params, ∀ β, ∀ ι : ℤ × ℤ, |ι.2| ≤ jmax → |ι.2 - ι.1| ≤ jmax →
    ¬ PieceWeights.inPiece ((D.pieces q).muP β).modes (labelHarmonic D.azimuthOrder ι)

def GeneratedByClassSymmetries {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) : Prop :=
  ∀ γ ∈ D.cert.symmetries, ∃ (a : ℕ) (b : Bool) (j : ℤ),
    (∀ y, γ.1 y = axialRot (a * (Real.pi / D.azimuthOrder)) (if b then flipPoint y else y)) ∧
      γ.2 = a / 2 + j

structure IsPinInstance {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) : Prop where
  mesh_valid : IsCellMesh D.mesh
  pin_eq : D.cert.pin = D.pinField
  closed : ∀ i, (D.pinValues i).IsConjugateClosed D.mesh.box

structure InstanceData (k : ℕ) (C : Type) (nE nM : ℕ) where
  weights : WeightValues C nE nM
  epsFrame : (Fin k → ℝ) → Fin nE → ℝ
  muFrame : (Fin k → ℝ) → Fin nM → ℝ
  epsSpeed : Fin nE → Space → ℝ
  muSpeed : Fin nM → Space → ℝ
  epsMirror : Equiv.Perm (Fin nE)
  muMirror : Equiv.Perm (Fin nM)
  rowWeightMax : ℝ
  actuatorModes : Fin k → Finset (ℤ × ℤ)
  actuatorRange : ℕ

structure IsInstanceEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : InstanceData k C nE nM) : Prop where
  rows : IsRowInstance D X.rowWeightMax
  weights : IsWeightInstance D X.weights X.epsFrame X.muFrame X.epsSpeed X.muSpeed X.epsMirror X.muMirror
  actuators : IsActuatorInstance D X.actuatorModes X.actuatorRange
  pins : IsPinInstance D
  symmetries : GeneratedByClassSymmetries D

end Instance

end CertCell

end Breakdown

end
end

section

open scoped ContDiff

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline TensorMesh cellCount atFirst atSecond tDeriv xDeriv weightPoly radialScale
  heightDeriv heightRatio radialVec polarVecQ azimVecQ)

structure FieldKey where
  label : ℤ × ℤ
  phaseIndex : ℤ
  deriving DecidableEq

namespace FieldKey

def negKey (κ : FieldKey) : FieldKey := ⟨-κ.label, -κ.phaseIndex⟩

def flipKey (κ : FieldKey) : FieldKey := ⟨labelFlip κ.label, κ.phaseIndex⟩

end FieldKey

structure IsFullMesh (M : TensorMesh) : Prop where
  t_sorted : M.tBreaks.Pairwise (· < ·)
  x_sorted : M.xBreaks.Pairwise (· < ·)
  t_first : M.tBreaks.head? = some 0
  t_last : M.tBreaks.getLast? = some 1
  x_first : M.xBreaks.head? = some (-1)
  x_last : M.xBreaks.getLast? = some 1

structure IsJoinedSpline (a b : ℕ) (S : Spline) : Prop where
  mesh : IsFullMesh S.mesh
  t_joins : ∀ i, 1 ≤ i → i < cellCount S.mesh.tBreaks → ∀ j < cellCount S.mesh.xBreaks, ∀ o ≤ a,
    atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (tDeriv o (S.piece (i - 1) j)) =
      atFirst (S.mesh.tBreaks.getD i 0 : ℂ) (tDeriv o (S.piece i j))
  x_joins : ∀ j, 1 ≤ j → j < cellCount S.mesh.xBreaks → ∀ i < cellCount S.mesh.tBreaks, ∀ o ≤ b,
    atSecond (S.mesh.xBreaks.getD j 0 : ℂ) (xDeriv o (S.piece i (j - 1))) =
      atSecond (S.mesh.xBreaks.getD j 0 : ℂ) (xDeriv o (S.piece i j))

def reflectPoly (P : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.bind₁ (fun k => if k = 0 then MvPolynomial.X 0 else -MvPolynomial.X 1) P

def reflectSpline (odd : Bool) (S : Spline) : Spline :=
  ⟨⟨S.mesh.tBreaks, (S.mesh.xBreaks.map Neg.neg).reverse⟩,
    fun i j => MvPolynomial.C (if odd then -1 else 1 : ℂ) *
      reflectPoly (S.piece i (cellCount S.mesh.xBreaks - 1 - j))⟩

structure SplineAgrees (S T : Spline) : Prop where
  mesh_eq : S.mesh = T.mesh
  piece_eq : ∀ i < cellCount S.mesh.tBreaks, ∀ j < cellCount S.mesh.xBreaks, S.piece i j = T.piece i j

structure KeyAmp where
  radial : Spline
  polar : Spline
  stream : Spline
  swirl : Spline
  axisCoef : ℂ
  lowOrder : ℕ
  highOrder : ℕ

namespace KeyAmp

def conj (A : KeyAmp) : KeyAmp :=
  ⟨A.radial.conj, A.polar.conj, A.stream.conj, A.swirl.conj, starRingEnd ℂ A.axisCoef, A.lowOrder, A.highOrder⟩

def reflect (A : KeyAmp) : KeyAmp :=
  ⟨reflectSpline false A.radial, reflectSpline true A.polar, reflectSpline true A.stream,
    reflectSpline true A.swirl, A.axisCoef, A.lowOrder, A.highOrder⟩

end KeyAmp

inductive JetDof where
  | node (k p : ℕ)
  | bubble (i s : ℕ)
  deriving DecidableEq

structure JetAxis where
  breaks : List ℝ
  depth : ℕ
  bubbleCount : ℕ

def jetUnit (n p : ℕ) : Polynomial ℂ :=
  Polynomial.C ((p.factorial : ℂ)⁻¹) * Polynomial.X ^ p * (1 - Polynomial.X) ^ n *
    ∑ s ∈ Finset.range (n - p), Polynomial.C ((Nat.choose (n - 1 + s) s : ℕ) : ℂ) * Polynomial.X ^ s

def nodalLeft (n p : ℕ) (a b : ℝ) : Polynomial ℂ :=
  Polynomial.C (((b - a) ^ p : ℝ) : ℂ) *
    (jetUnit n p).comp (Polynomial.C (((b - a)⁻¹ : ℝ) : ℂ) * (Polynomial.X - Polynomial.C (a : ℂ)))

def nodalRight (n p : ℕ) (a b : ℝ) : Polynomial ℂ :=
  Polynomial.C (((a - b) ^ p : ℝ) : ℂ) *
    (jetUnit n p).comp (Polynomial.C (((b - a)⁻¹ : ℝ) : ℂ) * (Polynomial.C (b : ℂ) - Polynomial.X))

def bubblePoly (n s : ℕ) (a b : ℝ) : Polynomial ℂ :=
  ((Polynomial.X - Polynomial.C (a : ℂ)) * (Polynomial.C (b : ℂ) - Polynomial.X)) ^ n *
    (Polynomial.X - Polynomial.C (((a + b) / 2 : ℝ) : ℂ)) ^ s

namespace JetAxis

def dofPoly (A : JetAxis) (i : ℕ) : JetDof → Polynomial ℂ
  | .node k p =>
    if p < A.depth then
      (if k = i then nodalLeft A.depth p (A.breaks.getD i 0) (A.breaks.getD (i + 1) 0)
        else if k = i + 1 then nodalRight A.depth p (A.breaks.getD i 0) (A.breaks.getD (i + 1) 0) else 0)
    else 0
  | .bubble i' s =>
    if i' = i ∧ s < A.bubbleCount then bubblePoly A.depth s (A.breaks.getD i 0) (A.breaks.getD (i + 1) 0) else 0

def dofs (A : JetAxis) : Finset JetDof :=
  ((Finset.range (cellCount A.breaks + 1)) ×ˢ (Finset.range A.depth)).image (fun kp => JetDof.node kp.1 kp.2) ∪
    ((Finset.range (cellCount A.breaks)) ×ˢ (Finset.range A.bubbleCount)).image
      (fun is => JetDof.bubble is.1 is.2)

def reflectDof (A : JetAxis) : JetDof → JetDof
  | .node k p => .node (cellCount A.breaks - k) p
  | .bubble i s => .bubble (cellCount A.breaks - 1 - i) s

def dofSign : JetDof → ℂ
  | .node _ p => (-1) ^ p
  | .bubble _ s => (-1) ^ s

end JetAxis

structure IsJetAxis (A : JetAxis) (lo hi : ℝ) : Prop where
  sorted : A.breaks.Pairwise (· < ·)
  first : A.breaks.head? = some lo
  last : A.breaks.getLast? = some hi
  depth_pos : 1 ≤ A.depth

def IsSymmetricAxis (A : JetAxis) : Prop := (A.breaks.map Neg.neg).reverse = A.breaks

structure JetSpline where
  tAxis : JetAxis
  xAxis : JetAxis
  coef : JetDof → JetDof → ℂ

def embedFirst (P : Polynomial ℂ) : MvPolynomial (Fin 2) ℂ := Polynomial.aeval (MvPolynomial.X 0) P

def embedSecond (P : Polynomial ℂ) : MvPolynomial (Fin 2) ℂ := Polynomial.aeval (MvPolynomial.X 1) P

namespace JetSpline

def toSpline (H : JetSpline) : Spline :=
  ⟨⟨H.tAxis.breaks, H.xAxis.breaks⟩, fun i j => ∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs,
    MvPolynomial.C (H.coef d e) * embedFirst (H.tAxis.dofPoly i d) * embedSecond (H.xAxis.dofPoly j e)⟩

def IsReflectFixed (odd : Bool) (H : JetSpline) : Prop :=
  ∀ d, ∀ e ∈ H.xAxis.dofs, H.coef d (H.xAxis.reflectDof e) = (if odd then -1 else 1) * JetAxis.dofSign e * H.coef d e

def IsConjReflectFixed (odd : Bool) (H : JetSpline) : Prop :=
  ∀ d, ∀ e ∈ H.xAxis.dofs, H.coef d (H.xAxis.reflectDof e) =
    (if odd then -1 else 1) * JetAxis.dofSign e * starRingEnd ℂ (H.coef d e)

def VanishesAtStart (H : JetSpline) : Prop := ∀ e, H.coef (JetDof.node 0 0) e = 0

end JetSpline

structure OriginProfile where
  poly : Polynomial ℝ
  edge : ℝ
  tail : ℝ

def OriginProfile.eval (g : OriginProfile) (t : ℝ) : ℝ := if t ≤ g.edge then g.poly.eval t else g.tail

structure IsOriginProfile (g : OriginProfile) : Prop where
  edge_pos : 0 < g.edge
  edge_le : g.edge ≤ 1
  at_zero : g.poly.eval 0 = 1
  joins : g.edge < 1 → ∀ o ≤ 2, (Polynomial.derivative^[o] g.poly).eval g.edge = if o = 0 then g.tail else 0

structure IsRadialPhase (f : ℝ → ℝ) : Prop where
  smooth : ∃ δ > 0, ContDiffOn ℝ 3 f (Set.Ioi (-δ))
  scaled_bounded : ∃ B : ℝ, ∀ s, 0 ≤ s → |s * deriv f s| ≤ B ∧ |s ^ 2 * iteratedDeriv 2 f s| ≤ B ∧
    |s ^ 3 * iteratedDeriv 3 f s| ≤ B

structure ShapeParams where
  chartLength : ℝ
  azimuthOrder : ℕ
  radialPhase : ℝ → ℝ
  origin : OriginProfile

structure IsShapeParams (P : ShapeParams) : Prop where
  chartLength_pos : 0 < P.chartLength
  azimuthOrder_pos : 0 < P.azimuthOrder
  phase : IsRadialPhase P.radialPhase
  origin : IsOriginProfile P.origin

def chartCoord (P : ShapeParams) (y : Space) : ℝ := ‖y‖ / (‖y‖ + P.chartLength)

def chartRadius (P : ShapeParams) (t : ℝ) : ℝ := P.chartLength * t / (1 - t)

def phaseSlope (P : ShapeParams) (t : ℝ) : ℝ :=
  2 * chartRadius P t ^ 2 * deriv P.radialPhase (chartRadius P t ^ 2)

def shiftedScale (P : ShapeParams) (j : ℤ) (f : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ :=
  radialScale f t x + Complex.I * (((j : ℝ) * phaseSlope P t : ℝ) : ℂ) * f t x

def polarFactor (x : ℝ) : ℂ := ((1 - x ^ 2 : ℝ) : ℂ)

def axisFactor (x : ℝ) : ℂ := (((1 - x ^ 2) ^ 2 : ℝ) : ℂ)

def streamValue (P : ShapeParams) (A : KeyAmp) (t x : ℝ) : ℂ :=
  A.axisCoef * ((P.origin.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x

def reducedComps (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (t x : ℝ) : Fin 3 → ℂ :=
  if κ.label.1 = 0 then
    let p := fun t' : ℝ => weightPoly 1 A.highOrder t'
    ![-(p t * heightDeriv (fun t' x' => polarFactor x' * streamValue P A t' x') t x),
      -(shiftedScale P κ.phaseIndex (fun t' x' => p t' * streamValue P A t' x') t x +
        2 * (p t * streamValue P A t x)),
      p t * A.swirl.evalHalf t x]
  else
    let ur := fun t' x' : ℝ => weightPoly A.lowOrder A.highOrder t' * axisFactor x' * A.radial.evalHalf t' x'
    let uθ := fun t' x' : ℝ => weightPoly A.lowOrder A.highOrder t' * axisFactor x' * A.polar.evalHalf t' x'
    ![ur t x, uθ t x,
      (Complex.I / (labelAzimuth P.azimuthOrder κ.label : ℂ)) *
        (shiftedScale P κ.phaseIndex ur t x + 2 * ur t x -
          heightDeriv (fun t' x' => polarFactor x' * uθ t' x') t x)]

def keyPhase (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (y : Space) : ℂ :=
  Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
    (labelAzimuth P.azimuthOrder κ.label : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)

def keyVector (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) (y : Space) : Fin 3 → ℂ :=
  fun i => keyPhase P κ σ y *
    (reducedComps P κ A (chartCoord P y) (heightRatio y) 0 * (radialVec y i : ℂ) +
      reducedComps P κ A (chartCoord P y) (heightRatio y) 1 * (polarVecQ y i : ℂ) +
      reducedComps P κ A (chartCoord P y) (heightRatio y) 2 * (azimVecQ y i : ℂ))

def keyHess (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) (y : Space) :
    Space →L[ℝ] Space →L[ℝ] (Fin 3 → ℂ) :=
  fderiv ℝ (fun x => fderiv ℝ (keyVector P κ A σ) x) y

structure TimeFieldData where
  keys : Finset FieldKey
  amp : FieldKey → KeyAmp

def complexField (P : ShapeParams) (D : TimeFieldData) (σ : ℝ) (y : Space) : Fin 3 → ℂ :=
  ∑ κ ∈ D.keys, keyVector P κ (D.amp κ) σ y

def realPartVec : (Fin 3 → ℂ) →L[ℝ] Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) i))

def shapeInfoField (P : ShapeParams) (D : TimeFieldData) : ℝ → Space → Space :=
  fun σ y => realPartVec (complexField P D σ y)

def shapeHess (P : ShapeParams) (D : TimeFieldData) : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  fun σ y => ∑ κ ∈ D.keys,
    (ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp (keyHess P κ (D.amp κ) σ y)

def harmonicsOf (m : ℕ) (D : TimeFieldData) : Finset (ℤ × ℤ) :=
  D.keys.image fun κ => labelHarmonic m κ.label

def labelsOf (D : TimeFieldData) : Finset (ℤ × ℤ) := D.keys.image FieldKey.label

structure IsTimeFieldData (D : TimeFieldData) : Prop where
  keys_neg : ∀ κ, κ ∈ D.keys ↔ κ.negKey ∈ D.keys
  keys_flip : ∀ κ, κ ∈ D.keys ↔ κ.flipKey ∈ D.keys
  neg_radial : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → SplineAgrees (D.amp κ.negKey).radial (D.amp κ).radial.conj
  neg_polar : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → SplineAgrees (D.amp κ.negKey).polar (D.amp κ).polar.conj
  neg_stream : ∀ κ ∈ D.keys, κ.label.1 = 0 → SplineAgrees (D.amp κ.negKey).stream (D.amp κ).stream.conj
  neg_swirl : ∀ κ ∈ D.keys, κ.label.1 = 0 → SplineAgrees (D.amp κ.negKey).swirl (D.amp κ).swirl.conj
  neg_axisCoef : ∀ κ ∈ D.keys, κ.label.1 = 0 → (D.amp κ.negKey).axisCoef = starRingEnd ℂ (D.amp κ).axisCoef
  neg_orders : ∀ κ ∈ D.keys, (D.amp κ.negKey).lowOrder = (D.amp κ).lowOrder ∧
    (D.amp κ.negKey).highOrder = (D.amp κ).highOrder
  flip_radial : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 →
    SplineAgrees (D.amp κ.flipKey).radial (reflectSpline false (D.amp κ).radial)
  flip_polar : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 →
    SplineAgrees (D.amp κ.flipKey).polar (reflectSpline true (D.amp κ).polar)
  flip_orders : ∀ κ ∈ D.keys, (D.amp κ.flipKey).lowOrder = (D.amp κ).lowOrder ∧
    (D.amp κ.flipKey).highOrder = (D.amp κ).highOrder
  stream_odd : ∀ κ ∈ D.keys, κ.label.1 = 0 → SplineAgrees (D.amp κ).stream (reflectSpline true (D.amp κ).stream)
  swirl_odd : ∀ κ ∈ D.keys, κ.label.1 = 0 → SplineAgrees (D.amp κ).swirl (reflectSpline true (D.amp κ).swirl)
  radial_class : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → IsJoinedSpline 2 1 (D.amp κ).radial
  polar_class : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → IsJoinedSpline 1 2 (D.amp κ).polar
  lowOrder_ge : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → 2 ≤ (D.amp κ).lowOrder
  stream_class : ∀ κ ∈ D.keys, κ.label.1 = 0 → IsJoinedSpline 2 2 (D.amp κ).stream
  swirl_class : ∀ κ ∈ D.keys, κ.label.1 = 0 → IsJoinedSpline 1 1 (D.amp κ).swirl
  stream_origin : ∀ κ ∈ D.keys, κ.label.1 = 0 → ∀ j < cellCount (D.amp κ).stream.mesh.xBreaks,
    atFirst 0 ((D.amp κ).stream.piece 0 j) = 0
  swirl_origin : ∀ κ ∈ D.keys, κ.label.1 = 0 → ∀ j < cellCount (D.amp κ).swirl.mesh.xBreaks,
    atFirst 0 ((D.amp κ).swirl.piece 0 j) = 0
  highOrder_pos : ∀ κ ∈ D.keys, 1 ≤ (D.amp κ).highOrder

structure IsCompactTimeFieldData (tb : ℝ) (D : TimeFieldData) : Prop where
  field : IsTimeFieldData D
  tb_lt : tb < 1
  typeOne_vanish : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 →
    (D.amp κ).radial.VanishesFrom tb ∧ (D.amp κ).polar.VanishesFrom tb
  typeTwo_vanish : ∀ κ ∈ D.keys, κ.label.1 = 0 →
    (D.amp κ).stream.VanishesFrom tb ∧ (D.amp κ).swirl.VanishesFrom tb
  typeOne_edge : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 →
    (∃ b ∈ (D.amp κ).radial.mesh.tBreaks, tb ≤ b ∧ b < 1) ∧ (∃ b ∈ (D.amp κ).polar.mesh.tBreaks, tb ≤ b ∧ b < 1)
  typeTwo_edge : ∀ κ ∈ D.keys, κ.label.1 = 0 →
    (∃ b ∈ (D.amp κ).stream.mesh.tBreaks, tb ≤ b ∧ b < 1) ∧ (∃ b ∈ (D.amp κ).swirl.mesh.tBreaks, tb ≤ b ∧ b < 1)
  axisCoef_zero : ∀ κ ∈ D.keys, κ.label.1 = 0 → (D.amp κ).axisCoef = 0

def orbitClosure (S : Finset FieldKey) : Finset FieldKey :=
  S ∪ S.image FieldKey.negKey ∪ S.image FieldKey.flipKey ∪ S.image (fun κ => κ.flipKey.negKey)

def closureAmp (S : Finset FieldKey) (given : FieldKey → KeyAmp) (κ : FieldKey) : KeyAmp :=
  if κ ∈ S then given κ
  else if κ.negKey ∈ S then (given κ.negKey).conj
  else if κ.flipKey ∈ S then (given κ.flipKey).reflect
  else (given κ.flipKey.negKey).conj.reflect

def closureData (S : Finset FieldKey) (given : FieldKey → KeyAmp) : TimeFieldData :=
  ⟨orbitClosure S, closureAmp S given⟩

end GivenShape

end CertCell

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount atFirst)

structure GivenShapeEntry (k : ℕ) where
  params : ShapeParams
  model : TimeFieldData
  actuatorParams : Fin k → ShapeParams
  actuators : Fin k → TimeFieldData
  actuatorEdge : Fin k → ℝ

end GivenShape

end CertCell

end Breakdown

end
end

section

open scoped ENNReal ComplexOrder

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstanceSplit

open Instance

structure EnclosureAdmissibleClauses {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (epsSup epsGradSup ratio : ℝ) : Prop where
  ampW_ge : ∀ β ∈ h.harmonics, ∀ σ y, Real.sqrt (cnormSq (modeVel β W σ y)) ≤ h.ampW β y
  ampGradW_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (modeGrad β (gradField W) σ y)) ≤ h.ampGradW β y
  ampVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlOfGrad (modeGrad β (gradField W) σ y))) ≤ h.ampVort β y
  ampGradVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv β HW σ y))) ≤ h.ampGradVort β y
  supVort_ge : ∀ σ φ y, ‖curlVec (fderiv ℝ (W σ) (axialRot φ y))‖ ≤ h.supVort y
  supGradVort_ge : ∀ σ φ y, ‖CoerciveWeak.vortGradMap (HW σ (axialRot φ y))‖ ≤ h.supGradVort y
  epsSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.epsP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.epsP β).speed y
  muSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.muP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.muP β).speed y
  eps_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.epsP β).modes, Ωs ≤ PieceWeights.frameFreq P (m.epsP β).frame ι
  mu_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.muP β).modes, Ωs ≤ PieceWeights.frameFreq P (m.muP β).frame ι
  mu_ratio : ∀ y ι, (∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * (m.muP β).wt y) ^ 2
    ≤ ratio * ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
      * (m.muP β).wt y
  ratio_nonneg : 0 ≤ ratio
  eps_sum_le : ∀ y, ∑ β : Fin nE, (m.epsP β).wt y ≤ epsSup
  eps_grad_sum_le : ∀ y, ∑ β : Fin nE, PieceWeights.wtGrad (m.epsP β).wt y ≤ epsGradSup
  conv_le : ∀ ι y, m.convD (m.classOf ι) y ≤ 1 - m.shareHat h ι y

structure ValuesFlipClauses {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) : Prop where
  amplitudes_flip : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y
    ∧ h.ampGradW (flipLabel β) (flipPoint y) = h.ampGradW β y
    ∧ h.ampVort (flipLabel β) (flipPoint y) = h.ampVort β y
    ∧ h.ampGradVort (flipLabel β) (flipPoint y) = h.ampGradVort β y
  sups_flip : ∀ y, h.supVort (flipPoint y) = h.supVort y ∧ h.supGradVort (flipPoint y) = h.supGradVort y
  amplitudes_axi : ∀ β φ y, h.ampW β (axialRot φ y) = h.ampW β y
    ∧ h.ampGradW β (axialRot φ y) = h.ampGradW β y
    ∧ h.ampVort β (axialRot φ y) = h.ampVort β y
    ∧ h.ampGradVort β (axialRot φ y) = h.ampGradVort β y
  sups_axi : ∀ φ y, h.supVort (axialRot φ y) = h.supVort y ∧ h.supGradVort (axialRot φ y) = h.supGradVort y
  eps_speed_axi : ∀ β, IsAxisymmetric (m.epsP β).speed
  mu_speed_axi : ∀ β, IsAxisymmetric (m.muP β).speed

end InstanceSplit

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

structure ShapeValuesFacts {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) : Prop where
  period_pos : ∀ q ∈ D.cert.params, 0 < D.cert.period q
  weight_pos : 0 < D.cert.weight
  weight_const : ∀ y, D.cert.weightFn y = D.cert.weight
  harmonics_neg : ∀ q ∈ D.cert.params, ∀ β ∈ (D.bounds q).harmonics, -β ∈ (D.bounds q).harmonics
  harmonics_zero : ∀ q ∈ D.cert.params, ((0, 0) : ℤ × ℤ) ∈ (D.bounds q).harmonics
  harmonics_flip : ∀ q ∈ D.cert.params, ∀ β ∈ (D.bounds q).harmonics, flipLabel β ∈ (D.bounds q).harmonics
  labels_in : ∀ q ∈ D.cert.params, D.givenLabels ⊆ (D.bounds q).harmonics

end GivenShape

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

structure JetKeyData where
  radial : JetSpline
  polar : JetSpline
  stream : JetSpline
  swirl : JetSpline
  axisCoef : ℂ
  lowOrder : ℕ
  highOrder : ℕ

def JetKeyData.toAmp (J : JetKeyData) : KeyAmp :=
  ⟨J.radial.toSpline, J.polar.toSpline, J.stream.toSpline, J.swirl.toSpline, J.axisCoef, J.lowOrder, J.highOrder⟩

structure GivenJetData where
  keys : Finset FieldKey
  data : FieldKey → JetKeyData

def GivenJetData.model (J : GivenJetData) : TimeFieldData :=
  closureData J.keys fun κ => (J.data κ).toAmp

def JetSpline.HasRealCoef (H : JetSpline) : Prop := ∀ d e, starRingEnd ℂ (H.coef d e) = H.coef d e

structure IsJetClass (a b : ℕ) (H : JetSpline) : Prop where
  t_axis : IsJetAxis H.tAxis 0 1
  x_axis : IsJetAxis H.xAxis (-1) 1
  t_depth : a + 1 ≤ H.tAxis.depth
  x_depth : b + 1 ≤ H.xAxis.depth

structure IsGivenJetData (J : GivenJetData) : Prop where
  one_per_orbit : ∀ κ ∈ J.keys, ∀ κ' ∈ J.keys,
    (κ' = κ.negKey ∨ κ' = κ.flipKey ∨ κ' = κ.flipKey.negKey) → κ' = κ
  radial_class : ∀ κ ∈ J.keys, κ.label.1 ≠ 0 → IsJetClass 2 1 (J.data κ).radial
  polar_class : ∀ κ ∈ J.keys, κ.label.1 ≠ 0 → IsJetClass 1 2 (J.data κ).polar
  stream_class : ∀ κ ∈ J.keys, κ.label.1 = 0 → IsJetClass 2 2 (J.data κ).stream
  swirl_class : ∀ κ ∈ J.keys, κ.label.1 = 0 → IsJetClass 1 1 (J.data κ).swirl
  lowOrder_ge : ∀ κ ∈ J.keys, κ.label.1 ≠ 0 → 2 ≤ (J.data κ).lowOrder
  highOrder_pos : ∀ κ ∈ J.keys, 1 ≤ (J.data κ).highOrder
  typeTwo_symmetric : ∀ κ ∈ J.keys, κ.label.1 = 0 →
    IsSymmetricAxis (J.data κ).stream.xAxis ∧ IsSymmetricAxis (J.data κ).swirl.xAxis
  typeTwo_odd : ∀ κ ∈ J.keys, κ.label.1 = 0 →
    (J.data κ).stream.IsReflectFixed true ∧ (J.data κ).swirl.IsReflectFixed true
  typeTwo_start : ∀ κ ∈ J.keys, κ.label.1 = 0 →
    (J.data κ).stream.VanishesAtStart ∧ (J.data κ).swirl.VanishesAtStart
  self_conj : ∀ κ ∈ J.keys, κ.negKey = κ → (J.data κ).stream.HasRealCoef ∧ (J.data κ).swirl.HasRealCoef ∧
    starRingEnd ℂ (J.data κ).axisCoef = (J.data κ).axisCoef
  self_conj_flip : ∀ κ ∈ J.keys, κ.label.1 ≠ 0 → κ.flipKey.negKey = κ →
    IsSymmetricAxis (J.data κ).radial.xAxis ∧ IsSymmetricAxis (J.data κ).polar.xAxis ∧
      (J.data κ).radial.IsConjReflectFixed false ∧ (J.data κ).polar.IsConjReflectFixed true

end GivenShape

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace ScalarShape

open CellCert.GivenFields (ChartParams IsChartParams chartT heightRatio Spline TensorMesh IsTensorMesh
  cellCount cellIndex atFirst atSecond tDeriv xDeriv)

open Instance (ChartScalar SplineJoins IsJoinedScalar IsConstantCore IsFlatAtOrigin HasNonnegValues StepDatum
  IsPositiveStep EpsGiven MuGiven WeightValues IsWeightValues IsFlipClosedValues)

def planeMinEval (P : ChartParams) (S : StepDatum) (y : Space) : ℝ :=
  (1 - chartT P y) ^ S.decay *
    (if y 2 = 0 then min (S.upperValue P y) (S.lowerValue P y)
      else if 0 < y 2 then S.upperValue P y else S.lowerValue P y)

structure ChartBound where
  data : StepDatum
  tPower : ℤ
  originValue : ℝ

namespace ChartBound

def eval (P : ChartParams) (B : ChartBound) (y : Space) : ℝ :=
  if y = 0 then B.originValue else chartT P y ^ B.tPower * planeMinEval P B.data y

end ChartBound

structure BoundValues where
  chart : ChartParams
  harmonics : Finset (ℤ × ℤ)
  ampW : ℤ × ℤ → ChartBound
  ampGradW : ℤ × ℤ → ChartBound
  ampVort : ℤ × ℤ → ChartBound
  ampGradVort : ℤ × ℤ → ChartBound
  supVort : ChartBound
  supGradVort : ChartBound

def BoundValues.bounds (T : BoundValues) : HarmonicBounds where
  harmonics := T.harmonics
  ampW β := (T.ampW β).eval T.chart
  ampGradW β := (T.ampGradW β).eval T.chart
  ampVort β := (T.ampVort β).eval T.chart
  ampGradVort β := (T.ampGradVort β).eval T.chart
  supVort := T.supVort.eval T.chart
  supGradVort := T.supGradVort.eval T.chart

end ScalarShape

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (ChartParams)

structure BoundValuesEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) where
  valueSets : (Fin k → ℝ) → ScalarShape.BoundValues
  speedChart : ChartParams
  epsSpeed : Fin nE → ScalarShape.ChartBound
  muSpeed : Fin nM → ScalarShape.ChartBound

structure IsBoundValuesEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (B : BoundValuesEntry D) : Prop where
  bounds_eq : ∀ q ∈ D.cert.params, D.bounds q = (B.valueSets q).bounds
  eps_speed_eq : ∀ q ∈ D.cert.params, ∀ β, ((D.pieces q).epsP β).speed = (B.epsSpeed β).eval B.speedChart
  mu_speed_eq : ∀ q ∈ D.cert.params, ∀ β, ((D.pieces q).muP β).speed = (B.muSpeed β).eval B.speedChart

end GivenShape

end CertCell

end Breakdown

end
end

section

open scoped ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open CellCert.CellAnalysis (CellBox radialEigen heightEigen)

open PieceWeights

def tailGain (K : CellBox) (Q : ℕ) (k shift : ℝ) : ℝ :=
  K.innerRadius * min (radialEigen K (Q + 1)) (heightEigen K (Q + 1)) + max (k - shift) 0 ^ 2 / K.r₂

def hessTailGain (K : CellBox) (Q : ℕ) (k : ℝ) : ℝ := tailGain K Q k 2

def curlTailGain (K : CellBox) (Q : ℕ) (k : ℝ) : ℝ := tailGain K Q k 1

def velTailGain (K : CellBox) (Q : ℕ) : ℝ := min (radialEigen K Q) (heightEigen K Q)

structure TailBudget where
  hessFloor : ℝ
  curlGradFloor : ℝ
  curlAbsorb : ℝ
  gradAbsorb : ℝ
  velAbsorb : ℝ
  gradPotential : ℝ
  velPotential : ℝ
  gradLeak : ℝ
  velLeak : ℝ
  globalLeak : ℝ

namespace TailBudget

variable (b : TailBudget) (K : CellBox) (Q : ℕ) (k : ℝ)

def velCharge : ℝ := max (b.velAbsorb + b.velPotential + b.velLeak) 0

def gradCharge : ℝ := b.gradAbsorb + 2 * max (b.curlAbsorb - b.curlGradFloor * curlTailGain K Q k) 0

def Holds : Prop :=
  b.gradCharge K Q k + b.gradPotential + b.gradLeak + b.globalLeak + b.velCharge / velTailGain K Q
    ≤ b.hessFloor * hessTailGain K Q k

end TailBudget

structure PointCoef where
  hess : ℝ
  curlGrad : ℝ
  curl : ℝ
  grad : ℝ
  vel : ℝ
  cross : ℝ

namespace PointCoef

variable (a : PointCoef)

def curlWithGain (k r : ℝ) : ℝ := a.curl + a.curlGrad * max (k - 1) 0 ^ 2 / r ^ 2

def gradFloor (k r : ℝ) : ℝ :=
  a.grad + 2 * min (a.curlWithGain k r) 0 + a.hess * max (k - 2) 0 ^ 2 / r ^ 2

def velWithShift (k r shift : ℝ) : ℝ := a.vel + shift * max (k - 1) 0 ^ 2 / r ^ 2

def PassesTest (k r shift : ℝ) : Prop :=
  0 ≤ a.hess ∧ 0 ≤ shift ∧ 0 ≤ a.gradFloor k r - shift ∧ 0 ≤ a.velWithShift k r shift ∧
    a.cross ^ 2 ≤ 4 * (a.gradFloor k r - shift) * a.velWithShift k r shift

end PointCoef

structure EntryCharges where
  strain : ℝ × ℝ → ℝ
  meanGrad : ℝ × ℝ → ℝ
  waveGrad : ℝ × ℝ → ℝ
  length : ℝ × ℝ → ℝ
  curlCharge : ℝ × ℝ → ℝ
  gradCharge : ℝ × ℝ → ℝ
  velCharge : ℝ × ℝ → ℝ
  stretchConst : ℝ

def PointCoef.withStretch (a : PointCoef)
    (stretchConst strain meanGrad waveGrad len curlCharge gradCharge velCharge : ℝ) : PointCoef where
  hess := a.hess
  curlGrad := a.curlGrad
  curl := a.curl - strain - curlCharge
  grad := a.grad - (stretchConst / 2) * waveGrad * len - gradCharge
  vel := a.vel - (stretchConst / 2) * waveGrad / len - velCharge
  cross := a.cross + stretchConst * meanGrad

def PointCoef.charged (a : PointCoef) (ec : EntryCharges) (p : ℝ × ℝ) : PointCoef :=
  a.withStretch ec.stretchConst (ec.strain p) (ec.meanGrad p) (ec.waveGrad p) (ec.length p) (ec.curlCharge p) (ec.gradCharge p)
    (ec.velCharge p)

def EntryCharges.Covers (ec : EntryCharges) (mc : ModeCharges) (I : Set (ℤ × ℤ)) (Z : Set (ℝ × ℝ)) : Prop :=
  0 ≤ ec.stretchConst ∧ ∀ ι ∈ I, ∀ p ∈ Z, mc.curl ι p ≤ ec.strain p ∧ mc.product ι p ≤ ec.meanGrad p ∧
    mc.gradient ι p ≤ ec.waveGrad p ∧ mc.length ι p = ec.length p ∧ 0 < ec.length p

def ampOf (h : HarmonicBounds) : Fin 4 → ℤ × ℤ → Space → ℝ := ![h.ampW, h.ampGradW, h.ampVort, h.ampGradVort]

def bit (b : Bool) : ℝ := if b then 1 else 0

structure SetPieceBounds (C : Type) (nE nM : ℕ) where
  cls : C
  azimuthLow : ℝ
  epsMember : Fin nE → Bool
  muMember : Fin nM → Bool
  epsFreqLow : Fin nE → ℝ
  muFreqLow : Fin nM → ℝ
  epsInward : Fin nE → Fin 4 → ℝ × ℝ → ℝ
  epsOutward : Fin nE → Fin 4 → ℝ × ℝ → ℝ
  muInward : Fin nM → Fin 4 → ℝ × ℝ → ℝ
  muOutward : Fin nM → Fin 4 → ℝ × ℝ → ℝ

namespace SetPieceBounds

variable {C : Type} {nE nM : ℕ} (B : SetPieceBounds C nE nM) (m : PieceWeights C nE nM) (P : ℝ)
  (h : HarmonicBounds) (w : Space → ℝ)

def shareHatHigh (p : ℝ × ℝ) : ℝ :=
  ∑ β : Fin nE, ((m.epsP β).share1 (planePoint p) * bit (B.epsMember β)
      * ModeWeights.ind (0 < (m.epsP β).wt (planePoint p) + wtGrad (m.epsP β).wt (planePoint p))
    + (m.epsP β).share2 (planePoint p) * ModeWeights.ind (0 < (m.epsP β).wt (planePoint p))
      * B.epsOutward β 0 p / (m.epsP β).scale (planePoint p))

def curlLow (p : ℝ × ℝ) : ℝ :=
  1 / 4 + (∑ β : Fin nE, bit (B.epsMember β) *
      ((m.epsP β).wt (planePoint p) * B.epsFreqLow β
        - ((m.epsP β).wt (planePoint p) * (m.epsP β).speed (planePoint p)
            + wtGrad (m.epsP β).wt (planePoint p)) ^ 2 / (4 * (m.epsP β).share1 (planePoint p))
        - (m.epsP β).wt (planePoint p) ^ 2 * (m.epsP β).scale (planePoint p) * B.epsInward β 0 p
            / (4 * (m.epsP β).share2 (planePoint p))
        - (m.epsP β).wt (planePoint p) * (|(m.epsP β).frame|
          + (1 / 2) * (1 + (m.epsP β).t0 (planePoint p)) * h.supVort (planePoint p)
          + (1 / 2) * (m.epsP β).len (planePoint p) * h.supGradVort (planePoint p)
          + (1 / 2) * (m.epsP β).t1 (planePoint p) * B.epsInward β 1 p
          + (1 / 2) * (m.epsP β).t2 (planePoint p) * B.epsInward β 3 p
          + (1 / 2) * (m.epsP β).t3 (planePoint p) * B.epsInward β 2 p)))
    - (∑ β : Fin nE, (m.epsP β).wt (planePoint p) * B.epsOutward β 1 p / (2 * (m.epsP β).t1 (planePoint p)))
    - m.convZ B.cls (planePoint p)

def gradLow (p : ℝ × ℝ) : ℝ :=
  m.convZ B.cls (planePoint p) - ModeWeights.secondDerivNorm (m.convD B.cls) (planePoint p) - m.c * w (planePoint p)
    - (∑ β : Fin nE, (m.epsP β).wt (planePoint p) * (bit (B.epsMember β) * h.supVort (planePoint p)
        / (2 * (m.epsP β).t0 (planePoint p)) + B.epsOutward β 2 p / (2 * (m.epsP β).t3 (planePoint p))))
    - ∑ β : Fin nM, (bit (B.muMember β)
        * ModeWeights.ind (0 < (m.muP β).wt (planePoint p) + wtGrad (m.muP β).wt (planePoint p))
        * (m.muP β).share (planePoint p)
        + (m.muP β).wt (planePoint p) * B.muOutward β 0 p / (2 * (m.muP β).t4 (planePoint p)))

def velLow (p : ℝ × ℝ) : ℝ :=
  -ModeWeights.secondDerivNorm (m.convZ B.cls) (planePoint p)
    - (∑ β : Fin nE, (m.epsP β).wt (planePoint p) * (bit (B.epsMember β) * h.supGradVort (planePoint p)
        / (2 * (m.epsP β).len (planePoint p)) + B.epsOutward β 3 p / (2 * (m.epsP β).t2 (planePoint p))))
    + (∑ β : Fin nM, bit (B.muMember β) *
        ((1 - m.cμ) * (m.muP β).wt (planePoint p) * B.muFreqLow β
          - ((m.muP β).wt (planePoint p) * (m.muP β).speed (planePoint p)
              + wtGrad (m.muP β).wt (planePoint p)) ^ 2 / (4 * (m.muP β).share (planePoint p))
          - (m.muP β).wt (planePoint p) * |(m.muP β).frame|
          - (1 / 2) * (m.muP β).t4 (planePoint p) * (m.muP β).wt (planePoint p) * B.muInward β 0 p
          - (1 / 2) * (m.muP β).eta * (m.muP β).wt (planePoint p) ^ 2
          - harmonicSum h (planePoint p) ^ 2 / (2 * (m.muP β).eta)))
    - ∑ β : Fin nM, harmonicSum h (planePoint p) * B.muOutward β 1 p / (2 * (m.muP β).eta)

def lowCoef (p : ℝ × ℝ) : PointCoef where
  hess := m.convD B.cls (planePoint p) - m.c
  curlGrad := 1 - B.shareHatHigh m p - m.convD B.cls (planePoint p)
  curl := B.curlLow m h p
  grad := B.gradLow m h w p
  vel := B.velLow m h p
  cross := 0

structure IsValidOn (mm : ℕ) (I : Set (ℤ × ℤ)) (Z : Set (ℝ × ℝ)) : Prop where
  class_eq : ∀ ι ∈ I, m.classOf (labelHarmonic mm ι) = B.cls
  azimuth_ge : ∀ ι ∈ I, B.azimuthLow ≤ |(labelAzimuth mm ι : ℝ)|
  eps_member : ∀ ι ∈ I, ∀ β, (inPiece (m.epsP β).modes (labelHarmonic mm ι) ↔ B.epsMember β = true)
  mu_member : ∀ ι ∈ I, ∀ β, (inPiece (m.muP β).modes (labelHarmonic mm ι) ↔ B.muMember β = true)
  eps_freq : ∀ ι ∈ I, ∀ β, B.epsMember β = true →
    B.epsFreqLow β ≤ |frameFreq P (m.epsP β).frame (labelHarmonic mm ι)|
  mu_freq : ∀ ι ∈ I, ∀ β, B.muMember β = true →
    B.muFreqLow β ≤ |frameFreq P (m.muP β).frame (labelHarmonic mm ι)|
  eps_inward : ∀ ι ∈ I, ∀ p ∈ Z, ∀ β j,
    inward h (m.epsP β).modes (ampOf h j) (labelHarmonic mm ι) (planePoint p) ≤ B.epsInward β j p
  eps_outward : ∀ ι ∈ I, ∀ p ∈ Z, ∀ β j,
    outward h (m.epsP β).modes (ampOf h j) (labelHarmonic mm ι) (planePoint p) ≤ B.epsOutward β j p
  mu_inward : ∀ ι ∈ I, ∀ p ∈ Z, ∀ β j,
    inward h (m.muP β).modes (ampOf h j) (labelHarmonic mm ι) (planePoint p) ≤ B.muInward β j p
  mu_outward : ∀ ι ∈ I, ∀ p ∈ Z, ∀ β j,
    outward h (m.muP β).modes (ampOf h j) (labelHarmonic mm ι) (planePoint p) ≤ B.muOutward β j p

end SetPieceBounds

structure OffModeCondition (C : Type) (nE nM : ℕ) where
  modes : Set (ℤ × ℤ)
  region : Set (ℝ × ℝ)
  charges : EntryCharges
  pieces : SetPieceBounds C nE nM
  shift : ℝ × ℝ → ℝ

structure IsOffModeCondition {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (mc : ModeCharges) (mm : ℕ) (E : OffModeCondition C nE nM) : Prop where
  pieces_valid : E.pieces.IsValidOn m P h mm E.modes E.region
  region_sub : E.region ⊆ halfPlane
  region_measurable : MeasurableSet E.region
  charges_cover : E.charges.Covers mc E.modes E.region
  test : ∀ p ∈ E.region,
    ((E.pieces.lowCoef m h w p).charged E.charges p).PassesTest E.pieces.azimuthLow p.1 (E.shift p)

def planeRadius (p : ℝ × ℝ) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def planeRayRegion (R : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) := {p | p ∈ halfPlane ∧ R p < planeRadius p}

def planeSquareExterior (R : ℝ) : Set (ℝ × ℝ) := {p | p ∈ halfPlane ∧ (R < p.1 ∨ R < p.2)}

structure IsDirectionRadius (R : ℝ × ℝ → ℝ) (R₀ R₁ : ℝ) : Prop where
  measurable : Measurable R
  lower_pos : 0 < R₀
  between : ∀ p, R₀ ≤ R p ∧ R p ≤ R₁
  homogeneous : ∀ (t : ℝ) (p : ℝ × ℝ), 0 < t → R (t • p) = R p

def rayInverseSquareConst (k : ℝ) : ℝ := 1 / 4 + max (k - 1) 0 ^ 2

structure ExteriorCondition (C : Type) (nE nM : ℕ) where
  modes : Set (ℤ × ℤ)
  region : Set (ℝ × ℝ)
  charges : EntryCharges
  pieces : SetPieceBounds C nE nM
  inverseSquareConst : ℝ
  gradLow : ℝ
  velHigh : ℝ
  crossHigh : ℝ

structure IsExteriorCondition {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (mc : ModeCharges) (mm : ℕ) (E : ExteriorCondition C nE nM) : Prop where
  pieces_valid : E.pieces.IsValidOn m P h mm E.modes E.region
  shape : (∃ (R : ℝ × ℝ → ℝ) (R₀ R₁ : ℝ), IsDirectionRadius R R₀ R₁ ∧ E.region = planeRayRegion R ∧
        E.inverseSquareConst ≤ rayInverseSquareConst E.pieces.azimuthLow) ∨
      (∃ R : ℝ, 0 < R ∧ E.region = planeSquareExterior R ∧ E.inverseSquareConst ≤ 2 ∧
        ∀ ι ∈ E.modes, labelAzimuth mm ι = 0)
  inverseSquareConst_pos : 0 < E.inverseSquareConst
  charges_cover : E.charges.Covers mc E.modes E.region
  hess_nonneg : ∀ p ∈ E.region, 0 ≤ (E.pieces.lowCoef m h w p).hess
  grad_floor : ∀ p ∈ E.region,
    E.gradLow ≤ ((E.pieces.lowCoef m h w p).charged E.charges p).gradFloor E.pieces.azimuthLow p.1
  vel_ceiling : ∀ p ∈ E.region,
    planeRadius p ^ 2 * max (-((E.pieces.lowCoef m h w p).charged E.charges p).vel) 0 ≤ E.velHigh
  cross_ceiling : ∀ p ∈ E.region,
    planeRadius p * ((E.pieces.lowCoef m h w p).charged E.charges p).cross ≤ E.crossHigh
  velHigh_nonneg : 0 ≤ E.velHigh
  crossHigh_nonneg : 0 ≤ E.crossHigh
  test : E.velHigh / E.inverseSquareConst + E.crossHigh / Real.sqrt E.inverseSquareConst ≤ E.gradLow

end TailBand

end CertCell

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

def secondDeriv (f : Space → Space) (y : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  fderiv ℝ (fun x => fderiv ℝ f x) y

def matrixDivergence (K : Space → (Space →L[ℝ] Space)) (y : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ K y (unitVector i) (unitVector i)

def transposeApply (K : Space →L[ℝ] Space) (z : Space) : Space :=
  ∑ i : Fin 3, inner ℝ (K (unitVector i)) z • unitVector i

def timeDerivative (f : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  deriv (fun s => f s y) σ

def advectionShift (δ ζ : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  transposeApply (fderiv ℝ (δ σ) y) (ζ σ y) - fderiv ℝ (ζ σ) y (δ σ y)

def adjointTransport (P : ℝ) (W ζ : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  -(1 / P) • timeDerivative ζ σ y - ζ σ y - (1 / 2 : ℝ) • fderiv ℝ (ζ σ) y y + advectionShift W ζ σ y

structure PotentialData where
  theta : ℝ → Space → Space
  phi : ℝ → Space → Space
  flux : ℝ → Space → (Space →L[ℝ] Space)
  pressure : ℝ → Space → ℝ

def remainderField (w₀ : ℝ) (T : ℝ → Space → Space) (K : ℝ → Space → (Space →L[ℝ] Space))
    (p : PotentialData) (σ : ℝ) (y : Space) : Space :=
  T σ y - matrixDivergence (K σ) y + gradientAt (p.pressure σ) y + secondDerivTrace (secondDeriv (p.theta σ) y)
    + w₀ • secondDerivTrace (secondDeriv (p.phi σ) y) - matrixDivergence (p.flux σ) y

structure PotentialNumbers where
  theta : ℝ
  phiGrad : ℝ
  flux : ℝ
  remainder : ℝ

def potentialDefect (w₀ : ℝ) (n : PotentialNumbers) : ℝ :=
  Real.sqrt (n.theta ^ 2 + (w₀ * n.phiGrad + n.flux + n.remainder) ^ 2 / w₀)

structure PotentialNorms (p : PotentialData) (n : PotentialNumbers) : Prop where
  theta_nonneg : 0 ≤ n.theta
  phiGrad_nonneg : 0 ≤ n.phiGrad
  flux_nonneg : 0 ≤ n.flux
  remainder_nonneg : 0 ≤ n.remainder
  theta_le : periodLIntegral (fun σ y => ‖p.theta σ y‖ ^ 2) ≤ ENNReal.ofReal (n.theta ^ 2)
  phiGrad_le : periodLIntegral (fun σ y => matSq (fderiv ℝ (p.phi σ) y)) ≤ ENNReal.ofReal (n.phiGrad ^ 2)
  flux_le : periodLIntegral (fun σ y => matSq (p.flux σ y)) ≤ ENNReal.ofReal (n.flux ^ 2)

def RemainderBounded (R : ℝ → Space → Space) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) volume ∧
    periodLIntegral (fun σ y => ‖y‖ ^ 2 * ‖R σ y‖ ^ 2) ≤ ENNReal.ofReal ((ρ / 2) ^ 2)

def axisRotation (α : ℝ) (y : Space) : Space :=
  (Real.cos α * y 0 - Real.sin α * y 1) • unitVector 0 + (Real.sin α * y 0 + Real.cos α * y 1) • unitVector 1
    + y 2 • unitVector 2

def complexComponent (c : Fin 3) (x : Space) : ℂ :=
  if c = 0 then (x 0 : ℂ) + (x 1 : ℂ) * Complex.I
  else if c = 1 then (x 0 : ℂ) - (x 1 : ℂ) * Complex.I else (x 2 : ℂ)

def componentWeight (c : Fin 3) : ℝ := if c = 2 then 1 else 1 / 2

def AzimuthalBounded (R : ℝ → Space → Space) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) volume ∧
    ∃ (N : ℕ) (amp : Fin N → Space → ℂ) (comp : Fin N → Fin 3) (freq order : Fin N → ℤ),
    Function.Injective (fun p : Fin N => (comp p, freq p, order p)) ∧
    (∀ p, AEStronglyMeasurable (amp p) volume) ∧
    (∀ p α y, amp p (axisRotation α y) = Complex.exp ((order p : ℂ) * (α : ℂ) * Complex.I) * amp p y) ∧
    (∀ σ, ∀ᵐ y, ∀ c, complexComponent c (R σ y) = ∑ p ∈ Finset.univ.filter (fun p => comp p = c),
      Complex.exp (2 * (Real.pi : ℂ) * (freq p : ℂ) * (σ : ℂ) * Complex.I) * amp p y) ∧
    (∑ p, ENNReal.ofReal (componentWeight (comp p) / (|(order p : ℝ)| + 1 / 2) ^ 2) *
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2)) ≤ ENNReal.ofReal (ρ ^ 2)

def DualBounded (R : ℝ → Space → Space) (ρ : ℝ) : Prop :=
  ∃ (R₁ R₂ : ℝ → Space → Space) (ρ₁ ρ₂ : ℝ), (∀ σ y, R σ y = R₁ σ y + R₂ σ y) ∧
    AzimuthalBounded R₁ ρ₁ ∧ RemainderBounded R₂ ρ₂ ∧ ρ₁ + ρ₂ ≤ ρ

structure PinData (k : ℕ) where
  potential : Fin k → ℝ → Space → Space
  generator : Fin k → ℝ → Space → Space

structure AdjointDefectEntry (k : ℕ) where
  field : ℝ → Space → Space
  pinCoef : Fin k → ℝ
  pins : PinData k
  centre : (Fin k → ℝ) → ℝ → Space → Space
  centrePeriod : ℝ
  periodRate : Fin k → ℝ
  fittedSet : Finset (Fin k)
  fitted : Fin k → ℝ → Space → Space
  free : (Fin k → ℝ) → Fin k → ℝ → Space → Space
  centrePotential : PotentialData
  fittedPotential : Fin k → PotentialData
  centreNumbers : PotentialNumbers
  fittedNumbers : Fin k → PotentialNumbers
  coordBound : Fin k → ℝ
  freeWeight : Fin k → ℝ
  freeValue : ℝ
  freeDual : ℝ
  timeDual : ℝ
  pinError : ℝ
  pinRound : ℝ
  pinCoefNorm : ℝ

namespace AdjointDefectEntry

variable {k : ℕ} (r : AdjointDefectEntry k)

def pinFlux (σ : ℝ) (y : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (r.field σ) y - ∑ l, r.pinCoef l • (fderiv ℝ (r.pins.generator l σ) y
    - ContinuousLinearMap.adjoint (fderiv ℝ (r.pins.generator l σ) y))

def centreResidual (q : Fin k → ℝ) : ℝ → Space → Space :=
  adjointTransport r.centrePeriod (r.centre q) r.field

def fittedResidual (i : Fin k) (σ : ℝ) (y : Space) : Space :=
  advectionShift (r.fitted i) r.field σ y - r.periodRate i • timeDerivative r.field σ y

def defectSum (w₀ : ℝ) : ℝ :=
  potentialDefect w₀ r.centreNumbers
    + (∑ i ∈ r.fittedSet, r.coordBound i * potentialDefect w₀ (r.fittedNumbers i))
    + (Real.sqrt (∑ i ∈ r.fittedSetᶜ, r.coordBound i ^ 2 / r.freeWeight i)
        * (r.freeValue + r.freeDual)
      + (∑ i ∈ r.fittedSetᶜ, |r.periodRate i| * r.coordBound i) * r.timeDual) / Real.sqrt w₀

def pinCharge (w₀ : ℝ) : ℝ :=
  r.pinError + r.pinCoefNorm * r.pinRound / Real.sqrt w₀

end AdjointDefectEntry

end AdjointDefect

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

structure AdjointDefectBounded {k : ℕ} (d : ExtendedCertificateData k) (j : Fin k)
    (r : AdjointDefectEntry k) : Prop where
  coordBound_adjoint : ∀ i ∈ d.adjointSet, d.radius i ≤ r.coordBound i
  coordBound_stiff : ∀ i ∈ d.adjointSetᶜ, d.scale i ≠ 0 ∧ |d.stiffRadius| ≤ |d.scale i| * r.coordBound i
  centre_norms : PotentialNorms r.centrePotential r.centreNumbers
  centre_remainder : ∀ q ∈ d.params,
    DualBounded (remainderField d.weight (r.centreResidual q) r.pinFlux r.centrePotential) r.centreNumbers.remainder
  fitted_norms : ∀ i ∈ r.fittedSet, PotentialNorms (r.fittedPotential i) (r.fittedNumbers i)
  fitted_remainder : ∀ i ∈ r.fittedSet, DualBounded
    (remainderField d.weight (r.fittedResidual i) (fun _ _ => 0) (r.fittedPotential i))
    (r.fittedNumbers i).remainder
  freeWeight_pos : ∀ i ∈ r.fittedSetᶜ, 0 < r.freeWeight i
  freeValue_nonneg : 0 ≤ r.freeValue
  freeDual_nonneg : 0 ≤ r.freeDual
  free_value : ∀ q ∈ d.params, periodLIntegral (fun σ y =>
    (∑ i ∈ r.fittedSetᶜ, r.freeWeight i * ‖r.free q i σ y‖ ^ 2) * ‖r.field σ y‖ ^ 2) ≤
      ENNReal.ofReal (r.freeValue ^ 2)
  free_dual : ∃ δ : Fin k → ℝ, (∀ i ∈ r.fittedSetᶜ, ∀ q ∈ d.params,
    DualBounded (fun σ y => transposeApply (fderiv ℝ (r.free q i σ) y) (r.field σ y)) (δ i)) ∧
    ∑ i ∈ r.fittedSetᶜ, r.freeWeight i * δ i ^ 2 ≤ r.freeDual ^ 2
  time_dual : DualBounded (timeDerivative r.field) r.timeDual
  pinError_nonneg : 0 ≤ r.pinError
  pinRound_nonneg : 0 ≤ r.pinRound
  pin_error :
    periodLIntegral (fun σ y => ‖∑ l, r.pinCoef l • (r.pins.potential l σ y - r.pins.generator l σ y)‖ ^ 2) ≤
      ENNReal.ofReal (r.pinError ^ 2)
  pin_round : ∀ c : Fin k → ℝ,
    periodLIntegral (fun σ y => matSq (∑ l, c l • (d.pin l σ y - fderiv ℝ (r.pins.potential l σ) y))) ≤
      ENNReal.ofReal (r.pinRound ^ 2 * ∑ l, c l ^ 2)
  pinCoef_norm : Real.sqrt (∑ l, r.pinCoef l ^ 2) ≤ r.pinCoefNorm
  total : r.defectSum d.weight + r.pinCharge d.weight ≤ d.adjointDefect j

end AdjointDefect

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

def gapGradCoeff (w₀ : ℝ) (cubic : Bool) : ℝ :=
  if cubic then 2 / Real.sqrt 3 / Real.sqrt w₀ else supBoundFactor w₀

def shiftGradCoeff (w₀ : ℝ) (cubic : Bool) : ℝ :=
  if cubic then 2 / Real.sqrt 3 / (2 * Real.sqrt w₀) else supBoundFactor w₀

structure ModelFormNumbers where
  strainLower : ℝ
  gradCubic : ℝ

structure FrozenFormBounded {k : ℕ} (d : ExtendedCertificateData k) (r : ModelFormNumbers) : Prop where
  strainLower_nonneg : 0 ≤ r.strainLower
  gradCubic_nonneg : 0 ≤ r.gradCubic
  strain : ∀ q ∈ d.params, ∀ σ y (u : Space),
    -r.strainLower * ‖u‖ ^ 2 ≤ inner ℝ (fderiv ℝ (d.model q σ) y u) u
  grad_cubic : ∀ q ∈ d.params, ∀ σ,
    (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (d.model q σ) y‖ ^ 3)) ≤ ENNReal.ofReal (r.gradCubic ^ 3)
  sum_le : r.strainLower / d.weight + 2 / Real.sqrt 3 * r.gradCubic / (2 * Real.sqrt d.weight) ≤
    d.modelFormBound

structure AdjointQuadNumbers (k : ℕ) where
  cubicForm : Fin k → Bool
  sizeNum : Fin k → ℝ

def adjointQuadCoeff (w₀ : ℝ) (cubic : Bool) : ℝ :=
  if cubic then 2 / Real.sqrt 3 / w₀ else supBoundFactor w₀ / Real.sqrt w₀

def AdjointSizeBound (cubic : Bool) (ζ : Space → Space) (z : ℝ) : Prop :=
  if cubic then (∫⁻ y, ENNReal.ofReal (‖ζ y‖ ^ 3)) ≤ ENNReal.ofReal (z ^ 3)
  else (∫⁻ y, ENNReal.ofReal (‖ζ y‖ ^ 2)) ≤ ENNReal.ofReal (z ^ 2)

structure AdjointQuadraticBounded {k : ℕ} (d : ExtendedCertificateData k) (r : AdjointQuadNumbers k) :
    Prop where
  sizeNum_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ r.sizeNum j
  size_bound : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ σ,
    AdjointSizeBound (r.cubicForm j) (d.adjoint j q σ) (r.sizeNum j)
  coeff_le : ∀ j ∈ d.adjointSet, adjointQuadCoeff d.weight (r.cubicForm j) * r.sizeNum j ≤ d.adjointQuad j

end CertReduction

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

open CellCert.GivenFields (Spline cellCount cellIndex atFirst weightPoly heightRatio)

def movedParams (P : ShapeParams) (moving : ℝ → ℝ) (a : ℝ) : ShapeParams :=
  { P with radialPhase := fun s => P.radialPhase s + a * moving s }

def phaseRate {k : ℕ} (rate : Fin k → ℝ) (q : Fin k → ℝ) : ℝ := ∑ i, rate i * q i

def withOrigin (P : ShapeParams) (g : OriginProfile) : ShapeParams := { P with origin := g }

def affineField {k : ℕ} (P : ShapeParams) (g : OriginProfile) (centre : TimeFieldData)
    (gt : Fin k → OriginProfile) (tangent : Fin k → TimeFieldData) (q : Fin k → ℝ) : ℝ → Space → Space :=
  fun σ y => shapeInfoField (withOrigin P g) centre σ y + ∑ i, q i • shapeInfoField (withOrigin P (gt i)) (tangent i) σ y

def affineSecondDeriv {k : ℕ} (P : ShapeParams) (g : OriginProfile) (centre : TimeFieldData)
    (gt : Fin k → OriginProfile) (tangent : Fin k → TimeFieldData) (q : Fin k → ℝ) :
    ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  fun σ y => shapeHess (withOrigin P g) centre σ y + ∑ i, q i • shapeHess (withOrigin P (gt i)) (tangent i) σ y

structure StepProfile where
  breaks : List ℝ
  piece : ℕ → Polynomial ℝ

def StepProfile.eval (S : StepProfile) (t : ℝ) : ℝ := (S.piece (cellIndex S.breaks t)).eval t

structure IsStepProfile (S : StepProfile) (edge : ℝ) : Prop where
  sorted : S.breaks.Pairwise (· < ·)
  first : S.breaks.head? = some 0
  last : S.breaks.getLast? = some 1
  joins : ∀ i, 1 ≤ i → i < cellCount S.breaks → ∀ o ≤ 2,
    (Polynomial.derivative^[o] (S.piece (i - 1))).eval (S.breaks.getD i 0) =
      (Polynomial.derivative^[o] (S.piece i)).eval (S.breaks.getD i 0)
  edge_mem : edge ∈ S.breaks
  edge_pos : 0 < edge
  edge_lt : edge < 1
  zero_below : ∀ i < cellCount S.breaks, S.breaks.getD (i + 1) 1 ≤ edge → S.piece i = 0
  one_above : ∃ t₁ < 1, ∀ t, t₁ ≤ t → t ≤ 1 → S.eval t = 1

def stepPhase (L : ℝ) (S : StepProfile) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..Real.sqrt s, S.eval (r / (r + L)) / r

structure ProfileShapeEntry (k : ℕ) where
  params : ShapeParams
  step : StepProfile
  stepEdge : ℝ
  rate : Fin k → ℝ
  centre : TimeFieldData
  centreOrigin : OriginProfile
  tangent : Fin k → TimeFieldData
  tangentOrigin : Fin k → OriginProfile

namespace ProfileShapeEntry

variable {k : ℕ} (R : ProfileShapeEntry k)

def moving : ℝ → ℝ := stepPhase R.params.chartLength R.step

def matchRadius : ℝ := R.params.chartLength * R.stepEdge / (1 - R.stepEdge)

def paramsAt (q : Fin k → ℝ) : ShapeParams := movedParams R.params R.moving (phaseRate R.rate q)

def field (q : Fin k → ℝ) : ℝ → Space → Space :=
  affineField (R.paramsAt q) R.centreOrigin R.centre R.tangentOrigin R.tangent q

def secondDeriv (q : Fin k → ℝ) : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  affineSecondDeriv (R.paramsAt q) R.centreOrigin R.centre R.tangentOrigin R.tangent q

end ProfileShapeEntry

structure IsProfileShapeEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : ProfileShapeEntry k) : Prop where
  params_valid : IsShapeParams R.params
  step_valid : IsStepProfile R.step R.stepEdge
  centre_valid : IsTimeFieldData R.centre
  centreOrigin_valid : IsOriginProfile R.centreOrigin
  tangent_valid : ∀ i, IsTimeFieldData (R.tangent i)
  tangentOrigin_valid : ∀ i, IsOriginProfile (R.tangentOrigin i)
  azimuth_eq : R.params.azimuthOrder = D.azimuthOrder
  profile_eq : ∀ q, D.cert.profile q = R.field q
  profileSecondDeriv_eq : ∀ q, D.cert.profileSecondDeriv q = R.secondDeriv q
  target_eq : ∀ q i, D.cert.target q i = pinValue (D.cert.pin i) (fun σ y => fderiv ℝ (D.cert.profile q σ) y)

structure PressureKeyAmp where
  amp : Spline
  lowOrder : ℕ
  highOrder : ℕ
  axisOrder : ℕ

structure PressureFieldData where
  keys : Finset FieldKey
  amp : FieldKey → PressureKeyAmp

def pressureKeyValue (P : ShapeParams) (κ : FieldKey) (A : PressureKeyAmp) (σ : ℝ) (y : Space) : ℂ :=
  keyPhase P κ σ y * (weightPoly A.lowOrder A.highOrder (chartCoord P y) *
    (((1 - heightRatio y ^ 2) ^ A.axisOrder : ℝ) : ℂ) * A.amp.evalHalf (chartCoord P y) (heightRatio y))

def shapePressure (P : ShapeParams) (D : PressureFieldData) (σ : ℝ) (y : Space) : ℝ :=
  (∑ κ ∈ D.keys, pressureKeyValue P κ (D.amp κ) σ y).re

structure IsPressureFieldData (D : PressureFieldData) : Prop where
  keys_neg : ∀ κ, κ ∈ D.keys ↔ κ.negKey ∈ D.keys
  keys_flip : ∀ κ, κ ∈ D.keys ↔ κ.flipKey ∈ D.keys
  neg_amp : ∀ κ ∈ D.keys, SplineAgrees (D.amp κ.negKey).amp (D.amp κ).amp.conj
  flip_amp : ∀ κ ∈ D.keys, SplineAgrees (D.amp κ.flipKey).amp (reflectSpline false (D.amp κ).amp)
  neg_orders : ∀ κ ∈ D.keys, (D.amp κ.negKey).lowOrder = (D.amp κ).lowOrder ∧
    (D.amp κ.negKey).highOrder = (D.amp κ).highOrder ∧ (D.amp κ.negKey).axisOrder = (D.amp κ).axisOrder
  flip_orders : ∀ κ ∈ D.keys, (D.amp κ.flipKey).lowOrder = (D.amp κ).lowOrder ∧
    (D.amp κ.flipKey).highOrder = (D.amp κ).highOrder ∧ (D.amp κ.flipKey).axisOrder = (D.amp κ).axisOrder
  amp_class : ∀ κ ∈ D.keys, IsJoinedSpline 0 0 (D.amp κ).amp
  highOrder_ge : ∀ κ ∈ D.keys, 2 ≤ (D.amp κ).highOrder
  typeOne_axis : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → 1 ≤ (D.amp κ).axisOrder
  typeOne_origin : ∀ κ ∈ D.keys, κ.label.1 ≠ 0 → 1 ≤ (D.amp κ).lowOrder ∨
    ∀ j < cellCount (D.amp κ).amp.mesh.xBreaks, atFirst 0 ((D.amp κ).amp.piece 0 j) = 0
  typeTwo_axis : ∀ κ ∈ D.keys, κ.label.1 = 0 → (D.amp κ).axisOrder = 0
  typeTwo_origin : ∀ κ ∈ D.keys, κ.label.1 = 0 → (D.amp κ).lowOrder = 0 →
    ∃ c : ℂ, ∀ j < cellCount (D.amp κ).amp.mesh.xBreaks, atFirst 0 ((D.amp κ).amp.piece 0 j) = MvPolynomial.C c

structure PressureShapeEntry (k : ℕ) where
  centre : PressureFieldData
  tangent : Fin k → PressureFieldData

def PressureShapeEntry.pressure {k : ℕ} (Pr : PressureShapeEntry k) (R : ProfileShapeEntry k)
    (q : Fin k → ℝ) (σ : ℝ) (y : Space) : ℝ :=
  shapePressure (R.paramsAt q) Pr.centre σ y + ∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ y

structure IsPressureShapeEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k) : Prop where
  centre_valid : IsPressureFieldData Pr.centre
  tangent_valid : ∀ i, IsPressureFieldData (Pr.tangent i)
  pressureGrad_eq : ∀ q σ y, D.cert.pressureGrad q σ y =
    gradient (fun y' => Pr.pressure R q σ y' - ‖D.cert.profile q σ y'‖ ^ 2 / 2) y

structure AdjointShapeEntry (k : ℕ) where
  params : ShapeParams
  field : Fin k → TimeFieldData

structure IsAdjointShapeEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (Z : AdjointShapeEntry k) : Prop where
  params_valid : IsShapeParams Z.params
  azimuth_eq : Z.params.azimuthOrder = D.azimuthOrder
  field_valid : ∀ j ∈ D.cert.adjointSet, IsTimeFieldData (Z.field j)
  highOrder_ge : ∀ j ∈ D.cert.adjointSet, ∀ κ ∈ (Z.field j).keys, 3 ≤ ((Z.field j).amp κ).highOrder
  adjoint_eq : ∀ j ∈ D.cert.adjointSet, ∀ q, D.cert.adjoint j q = shapeInfoField Z.params (Z.field j)

def InstantiationBounded {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k) (Z : AdjointShapeEntry k) : Prop :=
  IsProfileShapeEntry D R ∧ IsPressureShapeEntry D R Pr ∧ IsAdjointShapeEntry D Z

def ballPairing (r : ℝ) (F M : ℝ → Space → Space) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y in Metric.closedBall (0 : Space) r, inner ℝ (F σ y) (M σ y)

def timeDeriv (W : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := deriv (fun s => W s y) σ

def centreDefect {k : ℕ} (freq : ℝ) (lam : Fin k → ℝ) (b : Fin k → ℝ → Space → Space)
    (W : ℝ → Space → Space) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ → Space → ℝ)
    (σ : ℝ) (y : Space) : Space :=
  freq • timeDeriv W σ y + (1 / 2 : ℝ) • W σ y + (1 / 2 : ℝ) • fderiv ℝ (W σ) y y - secondDerivTrace (H σ y)
    + advectionAt (W σ) y + (∑ l, lam l • b l σ y) + gradient (p σ) y
    - gradient (fun y' => ‖W σ y'‖ ^ 2 / 2) y

def linearDefect {k : ℕ} (freq freqi : ℝ) (lam : Fin k → ℝ) (b : Fin k → ℝ → Space → Space)
    (W Wi : ℝ → Space → Space) (Hi : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (pt : ℝ → Space → ℝ)
    (σ : ℝ) (y : Space) : Space :=
  freq • timeDeriv Wi σ y + freqi • timeDeriv W σ y + (1 / 2 : ℝ) • Wi σ y + (1 / 2 : ℝ) • fderiv ℝ (Wi σ) y y
    - secondDerivTrace (Hi σ y) + fderiv ℝ (W σ) y (Wi σ y) + fderiv ℝ (Wi σ) y (W σ y)
    + (∑ l, lam l • b l σ y) + gradient (pt σ) y - gradient (fun y' => inner ℝ (W σ y') (Wi σ y')) y

def quadraticDefect (freqi : ℝ) (Wi Wl : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  freqi • timeDeriv Wl σ y + fderiv ℝ (Wl σ) y (Wi σ y) - gradient (fun y' => inner ℝ (Wi σ y') (Wl σ y') / 2) y

structure OffsetExpansionEntry (k : ℕ) where
  freqCentre : ℝ
  freqTangent : Fin k → ℝ
  multCentre : Fin k → ℝ
  multTangent : Fin k → Fin k → ℝ
  offsetCentre : Fin k → ℝ
  offsetLinear : Fin k → Fin k → ℝ
  offsetQuad : Fin k → Fin k → Fin k → ℝ
  centreErr : Fin k → ℝ
  linearErr : Fin k → Fin k → ℝ
  quadErr : Fin k → Fin k → Fin k → ℝ
  farDefect : ℝ
  farAdjoint : Fin k → ℝ

namespace OffsetExpansionEntry

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : ProfileShapeEntry k)
  (Pr : PressureShapeEntry k) (O : OffsetExpansionEntry k)

def centreCoefficient : ℝ → Space → Space :=
  centreDefect O.freqCentre O.multCentre D.cert.actuator (shapeInfoField (withOrigin R.params R.centreOrigin) R.centre)
    (shapeHess (withOrigin R.params R.centreOrigin) R.centre) (shapePressure R.params Pr.centre)

def linearCoefficient (i : Fin k) : ℝ → Space → Space :=
  linearDefect O.freqCentre (O.freqTangent i) (O.multTangent i) D.cert.actuator
    (shapeInfoField (withOrigin R.params R.centreOrigin) R.centre)
    (shapeInfoField (withOrigin R.params (R.tangentOrigin i)) (R.tangent i))
    (shapeHess (withOrigin R.params (R.tangentOrigin i)) (R.tangent i)) (shapePressure R.params (Pr.tangent i))

def orderedQuadratic (i l : Fin k) : ℝ → Space → Space :=
  quadraticDefect (O.freqTangent i) (shapeInfoField (withOrigin R.params (R.tangentOrigin i)) (R.tangent i))
    (shapeInfoField (withOrigin R.params (R.tangentOrigin l)) (R.tangent l))

def quadraticCoefficient (i l : Fin k) : ℝ → Space → Space :=
  if i = l then O.orderedQuadratic R i i else fun σ y => O.orderedQuadratic R i l σ y + O.orderedQuadratic R l i σ y

end OffsetExpansionEntry

def coordRadius {k : ℕ} (d : ExtendedCertificateData k) (i : Fin k) : ℝ :=
  if i ∈ d.adjointSet then d.radius i else |d.stiffRadius| / |d.scale i|

def offsetSum {k : ℕ} (d : ExtendedCertificateData k) (O : OffsetExpansionEntry k) (j : Fin k) : ℝ :=
  |O.offsetCentre j| + O.centreErr j
    + (∑ i, (|O.offsetLinear j i - (if i = j then d.scale j else 0)| + O.linearErr j i) * coordRadius d i)
    + (∑ i, ∑ l ∈ Finset.Ici i, (|O.offsetQuad j i l| + O.quadErr j i l) * coordRadius d i * coordRadius d l)
    + O.farDefect * O.farAdjoint j

structure IsOffsetExpansionEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k) (Z : AdjointShapeEntry k)
    (O : OffsetExpansionEntry k) : Prop where
  period_eq : ∀ q ∈ D.cert.params, 1 / D.cert.period q = O.freqCentre + ∑ i, q i * O.freqTangent i
  multiplier_eq : ∀ q ∈ D.cert.params, ∀ l, D.cert.multiplier q l = O.multCentre l + ∑ i, q i * O.multTangent i l
  centre_close : ∀ j ∈ D.cert.adjointSet, |O.offsetCentre j - ((∑ l, D.cert.frame l j * O.multCentre l)
    - ballPairing R.matchRadius (O.centreCoefficient D R Pr) (shapeInfoField Z.params (Z.field j)))| ≤ O.centreErr j
  linear_close : ∀ j ∈ D.cert.adjointSet, ∀ i, |O.offsetLinear j i - ((∑ l, D.cert.frame l j * O.multTangent i l)
    - ballPairing R.matchRadius (O.linearCoefficient D R Pr i) (shapeInfoField Z.params (Z.field j)))| ≤ O.linearErr j i
  quad_close : ∀ j ∈ D.cert.adjointSet, ∀ i l, i ≤ l → |O.offsetQuad j i l
    + ballPairing R.matchRadius (O.quadraticCoefficient R i l) (shapeInfoField Z.params (Z.field j))| ≤ O.quadErr j i l
  farDefect_nonneg : 0 ≤ O.farDefect
  farAdjoint_nonneg : ∀ j ∈ D.cert.adjointSet, 0 ≤ O.farAdjoint j
  far_defect : ∀ q ∈ D.cert.params, periodLIntegral (fun σ y => if R.matchRadius < ‖y‖ then ‖D.cert.defect q σ y‖ ^ 2 else 0)
    ≤ ENNReal.ofReal (O.farDefect ^ 2)
  far_adjoint : ∀ j ∈ D.cert.adjointSet, periodLIntegral
    (fun σ y => if R.matchRadius < ‖y‖ then ‖shapeInfoField Z.params (Z.field j) σ y‖ ^ 2 else 0)
      ≤ ENNReal.ofReal (O.farAdjoint j ^ 2)
  offset_eq : ∀ j ∈ D.cert.adjointSet, D.cert.adjointOffset j = offsetSum D.cert O j

def profileCentreAt {k : ℕ} (R : ProfileShapeEntry k) (q : Fin k → ℝ) : ℝ → Space → Space :=
  shapeInfoField (withOrigin (R.paramsAt q) R.centreOrigin) R.centre

def profileTangentAt {k : ℕ} (R : ProfileShapeEntry k) (q : Fin k → ℝ) (i : Fin k) : ℝ → Space → Space :=
  shapeInfoField (withOrigin (R.paramsAt q) (R.tangentOrigin i)) (R.tangent i)

structure AdjointEntryLinks {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : ProfileShapeEntry k) (Z : AdjointShapeEntry k) (O : OffsetExpansionEntry k)
    (r : Fin k → AdjointDefect.AdjointDefectEntry k) : Prop where
  field_eq : ∀ j ∈ D.cert.adjointSet, (r j).field = shapeInfoField Z.params (Z.field j)
  coupling_eq : ∀ j ∈ D.cert.adjointSet, ∀ q ∈ D.cert.params, ∀ l, D.cert.coupling q j l = (r j).pinCoef l
  fitted_empty : ∀ j ∈ D.cert.adjointSet, (r j).fittedSet = ∅
  centre_eq : ∀ j ∈ D.cert.adjointSet, (r j).centre = profileCentreAt R
  free_eq : ∀ j ∈ D.cert.adjointSet, ∀ q i, (r j).free q i = profileTangentAt R q i
  centrePeriod_eq : ∀ j ∈ D.cert.adjointSet, 1 / (r j).centrePeriod = O.freqCentre
  periodRate_eq : ∀ j ∈ D.cert.adjointSet, (r j).periodRate = O.freqTangent

end Instantiation

end CellReduction

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

open Classical

namespace Breakdown

namespace CertCell

namespace KnotZero

def planeOf (y : Space) : ℝ × ℝ := (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), y 2)

def zeroOn (N : Set (ℝ × ℝ)) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  fun σ y => if planeOf y ∈ N then 0 else HW σ y

end KnotZero

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline)

def planeNorm (p : ℝ × ℝ) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def sphereKnots (P : ShapeParams) (breaks : List ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ b ∈ breaks, planeNorm p = chartRadius P b}

def coneKnots (breaks : List ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ b ∈ breaks, p.2 = b * planeNorm p}

def splineKnots (P : ShapeParams) (S : Spline) : Set (ℝ × ℝ) :=
  sphereKnots P S.mesh.tBreaks ∪ coneKnots S.mesh.xBreaks

def keyKnots (P : ShapeParams) (A : KeyAmp) : Set (ℝ × ℝ) :=
  splineKnots P A.radial ∪ splineKnots P A.polar ∪ splineKnots P A.stream ∪ splineKnots P A.swirl

def shapeKnots (P : ShapeParams) (D : TimeFieldData) : Set (ℝ × ℝ) :=
  {p | p.2 = 0} ∪ {p | p.1 = 0} ∪ {0} ∪ sphereKnots P [P.origin.edge] ∪ ⋃ κ ∈ D.keys, keyKnots P (D.amp κ)

def mirrorKnots (P : ShapeParams) (D : TimeFieldData) : Set (ℝ × ℝ) :=
  {p | p ∈ shapeKnots P D ∨ (p.1, -p.2) ∈ shapeKnots P D}

def knotZeroHess (P : ShapeParams) (D : TimeFieldData) : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  KnotZero.zeroOn (mirrorKnots P D) (shapeHess P D)

end GivenShape

end CertCell

end Breakdown

end
end

section

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount)

structure ScaledJetAxis where
  breaks : List ℝ
  depth : ℕ
  bubbleCount : ℕ
  scale : List ℝ
  bubbleConst : List ℝ

def symmetricJacobi (α j : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 : ℝ)⁻¹ ^ j) * ∑ i ∈ Finset.range (j + 1),
    Polynomial.C ((Nat.choose (j + α) i * Nat.choose (j + α) (j - i) : ℕ) : ℝ) *
      (Polynomial.X - 1) ^ (j - i) * (Polynomial.X + 1) ^ i

namespace ScaledJetAxis

def base (A : ScaledJetAxis) : JetAxis := ⟨A.breaks, A.depth, A.bubbleCount⟩

def convert (A : ScaledJetAxis) : JetDof → JetDof → ℂ
  | .node k p, .node k' p' => if k = k' ∧ p = p' then (((A.scale.getD k 1)⁻¹ ^ p : ℝ) : ℂ) else 0
  | .bubble i s, .bubble i' j =>
    if i = i' then
      ((A.bubbleConst.getD j 0 * (4 / (A.breaks.getD (i + 1) 0 - A.breaks.getD i 0) ^ 2) ^ A.depth *
        (2 / (A.breaks.getD (i + 1) 0 - A.breaks.getD i 0)) ^ s * (symmetricJacobi (2 * A.depth) j).coeff s : ℝ) : ℂ)
    else 0
  | _, _ => 0

end ScaledJetAxis

def HasSymmetricScale (A : ScaledJetAxis) : Prop := A.scale.length = A.breaks.length ∧ A.scale.reverse = A.scale

structure ScaledJetSpline where
  tAxis : ScaledJetAxis
  xAxis : ScaledJetAxis
  coef : JetDof → JetDof → ℂ

namespace ScaledJetSpline

def coefValues (H : ScaledJetSpline) : JetSpline := ⟨H.tAxis.base, H.xAxis.base, H.coef⟩

def toJet (H : ScaledJetSpline) : JetSpline :=
  ⟨H.tAxis.base, H.xAxis.base, fun d e => ∑ d' ∈ H.tAxis.base.dofs, ∑ e' ∈ H.xAxis.base.dofs,
    H.tAxis.convert d d' * H.xAxis.convert e e' * H.coef d' e'⟩

end ScaledJetSpline

structure ScaledKeyData where
  radial : ScaledJetSpline
  polar : ScaledJetSpline
  stream : ScaledJetSpline
  swirl : ScaledJetSpline
  axisCoef : ℂ
  lowOrder : ℕ
  highOrder : ℕ

namespace ScaledKeyData

def coefValueSets (K : ScaledKeyData) : JetKeyData :=
  ⟨K.radial.coefValues, K.polar.coefValues, K.stream.coefValues, K.swirl.coefValues, K.axisCoef, K.lowOrder,
    K.highOrder⟩

def toJets (K : ScaledKeyData) : JetKeyData :=
  ⟨K.radial.toJet, K.polar.toJet, K.stream.toJet, K.swirl.toJet, K.axisCoef, K.lowOrder, K.highOrder⟩

end ScaledKeyData

structure ScaledJetData where
  keys : Finset FieldKey
  data : FieldKey → ScaledKeyData

namespace ScaledJetData

def coefValueSets (S : ScaledJetData) : GivenJetData := ⟨S.keys, fun κ => (S.data κ).coefValueSets⟩

def toJets (S : ScaledJetData) : GivenJetData := ⟨S.keys, fun κ => (S.data κ).toJets⟩

end ScaledJetData

structure IsScaledJetData (S : ScaledJetData) : Prop where
  valueSets : IsGivenJetData S.coefValueSets
  typeTwo_scales : ∀ κ ∈ S.keys, κ.label.1 = 0 →
    HasSymmetricScale (S.data κ).stream.xAxis ∧ HasSymmetricScale (S.data κ).swirl.xAxis
  self_conj_flip_scales : ∀ κ ∈ S.keys, κ.label.1 ≠ 0 → κ.flipKey.negKey = κ →
    HasSymmetricScale (S.data κ).radial.xAxis ∧ HasSymmetricScale (S.data κ).polar.xAxis

structure IsScaledJetEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (F : GivenShapeEntry k) (S : ScaledJetData) : Prop where
  jets : IsScaledJetData S
  model_eq : F.model = S.toJets.model
  params_valid : IsShapeParams F.params
  actuatorParams_valid : ∀ i, IsShapeParams (F.actuatorParams i)
  actuators_valid : ∀ i, IsCompactTimeFieldData (F.actuatorEdge i) (F.actuators i)
  azimuth_eq : F.params.azimuthOrder = D.azimuthOrder
  actuatorAzimuth_eq : ∀ i, (F.actuatorParams i).azimuthOrder = D.azimuthOrder
  given_eq : D.given = shapeInfoField F.params F.model
  givenHess_eq : D.givenHess = knotZeroHess F.params F.model
  labels_cover : harmonicsOf D.azimuthOrder F.model ⊆ D.givenLabels
  labels_symm : ∀ β ∈ D.givenLabels, -β ∈ D.givenLabels
  actuator_eq : ∀ i, D.cert.actuator i = shapeInfoField (F.actuatorParams i) (F.actuators i)
  actuatorModes_eq : ∀ i, X.actuatorModes i = labelsOf (F.actuators i)

end GivenShape

end CertCell

end Breakdown

end
end

section

open scoped ContDiff ENNReal ComplexOrder

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

structure CreditPatch where
  label : ℤ × ℤ
  inner : ℝ
  outer : ℝ
  height : ℝ
  charge : ℝ × ℝ → ℝ
  chargeLower : ℝ
  chargeUpper : ℝ
  testCount : ℕ
  test : Fin testCount → ℝ × ℝ → ℝ
  testSlope : NNReal
  testForm : Matrix (Fin testCount) (Fin testCount) ℝ
  segmentCount : ℕ
  segment : Fin segmentCount → PlaneSegment
  dataCount : ℕ
  dataOf : Fin dataCount → (Σ s : Fin segmentCount, Fin (segment s).testCount)
  traceMap : Matrix (Fin testCount) (Fin dataCount) ℝ
  credit : Matrix (Fin dataCount) (Fin dataCount) ℂ

namespace CreditPatch

variable (R : CreditPatch)

def region : Set (ℝ × ℝ) := patch R.inner R.outer R.height

def testCombination (c : Fin R.testCount → ℂ) : ℝ × ℝ → ℂ :=
  fun p => ∑ i, (starRingEnd ℂ) (c i) * (R.test i p : ℂ)

def traceData (g : Fin R.dataCount → ℂ) : Fin R.testCount → ℂ :=
  fun i => ∑ d, (R.traceMap i d : ℂ) * g d

end CreditPatch

structure IsCreditPatch (R : CreditPatch) : Prop where
  inner_pos : 0 < R.inner
  inner_lt_outer : R.inner < R.outer
  height_pos : 0 < R.height
  charge_measurable : Measurable R.charge
  charge_lower_pos : 0 < R.chargeLower
  charge_between : ∀ p, R.chargeLower ≤ R.charge p ∧ R.charge p ≤ R.chargeUpper
  test_slope_bound : ∀ i, LipschitzWith R.testSlope (R.test i)
  test_sides : ∀ i z, R.test i (R.inner, z) = 0 ∧ R.test i (R.outer, z) = 0
  test_top : ∀ i r, R.test i (r, R.height) = 0
  segments : ∀ s, IsPlaneSegment (R.segment s)
  segments_cover : ∀ r, R.inner ≤ r → r ≤ R.outer →
    ∃ s, (R.segment s).lower ≤ r ∧ r ≤ (R.segment s).upper
  segments_disjoint : ∀ s s', s ≠ s' → (R.segment s).upper ≤ (R.segment s').lower ∨
    (R.segment s').upper ≤ (R.segment s).lower
  segments_inside : ∀ s, R.inner ≤ (R.segment s).lower ∧ (R.segment s).upper ≤ R.outer
  trace_expansion : ∀ i s r, (R.segment s).lower ≤ r → r ≤ (R.segment s).upper →
    r * R.test i (r, 0) = ∑ d, (if (R.dataOf d).1 = s then R.traceMap i d * (R.segment (R.dataOf d).1).test (R.dataOf d).2 r else 0)
  form_posDef : R.testForm.PosDef
  form_bound : ∀ c : Fin R.testCount → ℂ,
    ∫ p in patch R.inner R.outer R.height, patchGradSq R.label.2 (R.testCombination c) p / R.charge p * p.1
      ≤ Coupling.realQuadForm R.testForm c
  credit_le : ∀ g : Fin R.dataCount → ℂ,
    Coupling.quadForm R.credit g ≤ Coupling.realQuadForm R.testForm⁻¹ (R.traceData g)

end Bridge

end CertCell

end Breakdown

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

def gradAt (m : ℕ) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  labelGrad m ι G p (a, b)

def velAt (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) (p : ℝ × ℝ) : ℂ :=
  labelVel m ι v p a

def IsHarmonicLayout (m : ℕ) (K : CellBox) (B : CellBases) (modes : Finset ℤ) (L : CellLayout) : Prop :=
  ∃ (c : FracCellData 0 0) (S : CellScalars), c.order = m ∧ S.resolved = modes ∧ IsCellLayout c K S B L

structure CellModeLayouts where
  bases : CellBases
  layout : ℤ × ℤ → CellLayout
  param : (ι : ℤ × ℤ) → ParamData (layout ι).Datum
  selection : (ι : ℤ × ℤ) → Fin (param ι).relCount → (layout ι).RelIndex

structure IsCellModeLayouts (m : ℕ) (M : CellMesh) (K : Fin M.count) (A : CellModeLayouts) : Prop where
  skeleton_positive : ∀ ι ∈ M.resolved K, 1 ≤ M.skeletonDeg K ι
  layout_valid : ∀ ι ∈ M.resolved K, IsHarmonicLayout m (M.box K) A.bases {ι.1} (A.layout ι)
  layout_volumeDeg : ∀ ι ∈ M.resolved K, (A.layout ι).degCoef = M.volumeDeg K ι
  layout_skeletonDeg : ∀ ι ∈ M.resolved K, ((A.layout ι).degSide : ℤ) = M.skeletonDeg K ι
  param_valid : ∀ ι ∈ M.resolved K, IsCellParam (A.layout ι) (A.param ι) (A.selection ι)

def coefPairValue (A : ModeCoefficients) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  A.curl * curlSq s + A.strain * sumSq s + A.velocity * vecSq v

structure LeafValues where
  hessFloor : ℤ × ℤ → ℝ
  curlHessFloor : ℤ × ℤ → ℝ
  localMatrix : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ
  curlAbsorb : ℤ × ℤ → ℝ
  strainAbsorb : ℤ × ℤ → ℝ
  velocityAbsorb : ℤ × ℤ → ℝ
  boxCurl : ℤ × ℤ → ℝ
  boxStrain : ℤ × ℤ → ℝ
  boxVelocity : ℤ × ℤ → ℝ
  boxPairCurl : ℤ × ℤ → ℝ
  boxPairStrain : ℤ × ℤ → ℝ
  boxPairVelocity : ℤ × ℤ → ℝ

namespace LeafValues

variable (T : LeafValues)

def boxPenalty (ι : ℤ × ℤ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  T.boxCurl ι * curlSq s + T.boxStrain ι * sumSq s + T.boxVelocity ι * vecSq v

def boxPairPenalty (ι : ℤ × ℤ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  T.boxPairCurl ι * curlSq s + T.boxPairStrain ι * sumSq s + T.boxPairVelocity ι * vecSq v

def absorbValue (ι : ℤ × ℤ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  T.curlAbsorb ι * curlSq s + T.strainAbsorb ι * sumSq s + T.velocityAbsorb ι * vecSq v

end LeafValues

structure IsLeafValues (K : CellBox) (resolved : Finset (ℤ × ℤ)) (coef : ℤ × ℤ → ℝ × ℝ → ModeCoefficients)
    (ch : ModeCharges) (T : LeafValues) : Prop where
  hessFloor_pos : ∀ ι ∈ resolved, 0 < T.hessFloor ι
  hessFloor_le : ∀ ι ∈ resolved, ∀ p ∈ K.rect, T.hessFloor ι ≤ (coef ι p).hess
  curlHessFloor_nonneg : ∀ ι ∈ resolved, 0 ≤ T.curlHessFloor ι
  curlHessFloor_le : ∀ ι ∈ resolved, ∀ p ∈ K.rect, T.curlHessFloor ι ≤ (coef ι p).curlHess
  matrix_hermitian : ∀ ι ∈ resolved, ∀ p ∈ K.rect, (T.localMatrix ι p).IsHermitian
  matrix_regular : ∀ ι ∈ resolved, (∀ i j, Measurable (fun p => T.localMatrix ι p i j)) ∧
    ∃ C : ℝ, ∀ p ∈ K.rect, ∀ i j, ‖T.localMatrix ι p i j‖ ≤ C
  matrix_le : ∀ ι ∈ resolved, ∀ p ∈ K.rect, ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ),
    sesqValue (T.localMatrix ι p) (pairVec s v) ≤ coefPairValue (coef ι p) s v - T.boxPenalty ι s v
  pointwise : ∀ ι ∈ resolved, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ),
    0 ≤ CellScalars.rHat K p * (sesqValue (T.localMatrix ι p) (pairVec s v)
          - supremumLoss (ch.curl ι p) (ch.product ι p) (ch.gradient ι p) (ch.length ι p) s v
          - T.boxPairPenalty ι s v)
      + T.absorbValue ι s v
  charges_nonneg : ∀ ι ∈ resolved, ∀ p ∈ K.rect, 0 ≤ ch.product ι p ∧ 0 ≤ ch.gradient ι p ∧ 0 < ch.length ι p
  symmetric : ∀ ι ∈ resolved, T.hessFloor (-ι) = T.hessFloor ι ∧ T.curlHessFloor (-ι) = T.curlHessFloor ι ∧
    T.curlAbsorb (-ι) = T.curlAbsorb ι ∧ T.strainAbsorb (-ι) = T.strainAbsorb ι ∧
    T.velocityAbsorb (-ι) = T.velocityAbsorb ι

def ownSolid {count : ℕ} (box : Fin count → CellBox) (K : Fin count) : Set Space :=
  {y | y ∈ (box K).solid ∧ 0 < CellCert.CellAnalysis.cylRadius y ∧ ∀ L, L ≠ K → y ∉ (box L).solid}

structure IsSplitPart {β : Type*} [NormedAddCommGroup β] (solid : Set Space)
    (full model high long : ℝ → Space → β) (boundHigh boundLong bound : ℝ) : Prop where
  high_bound : ∀ σ, ∀ y ∈ solid, ‖high σ y‖ ≤ boundHigh
  long_bound : ∀ σ, ∀ y ∈ solid, ‖long σ y‖ ≤ boundLong
  rest_bound : ∀ σ, ∀ y ∈ solid, ‖full σ y - model σ y - high σ y - long σ y‖ ≤ bound

structure IsSplitPartAE {β : Type*} [NormedAddCommGroup β] (solid : Set Space)
    (full model high long : ℝ → Space → β) (boundHigh boundLong bound : ℝ) : Prop where
  high_bound : ∀ σ, ∀ y ∈ solid, ‖high σ y‖ ≤ boundHigh
  long_bound : ∀ σ, ∀ y ∈ solid, ‖long σ y‖ ≤ boundLong
  rest_bound : ∀ᵐ p : ℝ × ℝ, ∀ σ θ : ℝ, cylPoint p.1 θ p.2 ∈ solid →
    ‖full σ (cylPoint p.1 θ p.2) - model σ (cylPoint p.1 θ p.2) - high σ (cylPoint p.1 θ p.2)
      - long σ (cylPoint p.1 θ p.2)‖ ≤ bound

def IsVecOrthogonal (K : CellBox) (m : ℕ) (deg : ℕ) (f : ℝ → Space → Space) : Prop :=
  ∀ (ι : ℤ × ℤ) (a : Fin 3) (i j : ℕ), i ≤ deg → j ≤ deg →
    ∫ p in K.rect, velAt m ι f a p * ((p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) = 0

def IsMatOrthogonal (K : CellBox) (m : ℕ) (deg : ℕ) (f : ℝ → Space → (Space →L[ℝ] Space)) : Prop :=
  ∀ (ι : ℤ × ℤ) (a b : Fin 3) (i j : ℕ), i ≤ deg → j ≤ deg →
    ∫ p in K.rect, gradAt m ι f a b p * ((p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) = 0

def vorticityOf (W : ℝ → Space → Space) : ℝ → Space → Space :=
  fun σ y => curlVec (fderiv ℝ (W σ) y)

def strainOf (W : ℝ → Space → Space) : ℝ → Space → (Space →L[ℝ] Space) :=
  fun σ y => (1 / 2 : ℝ) • (fderiv ℝ (W σ) y + ContinuousLinearMap.adjoint (fderiv ℝ (W σ) y))

def vorticityGradOf (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    ℝ → Space → (Space →L[ℝ] Space) :=
  fun σ y => CoerciveWeak.vortGradMap (HW σ y)

structure CellModelHigh where
  velocity : ℝ → Space → Space
  vorticity : ℝ → Space → Space
  strain : ℝ → Space → (Space →L[ℝ] Space)
  vorticityGrad : ℝ → Space → (Space →L[ℝ] Space)

structure CellModelLong where
  velocity : ℝ → Space → Space
  vorticity : ℝ → Space → Space
  strain : ℝ → Space → (Space →L[ℝ] Space)
  vorticityGrad : ℝ → Space → (Space →L[ℝ] Space)
  cut : ℕ
  errVelocity : ℝ
  errVorticity : ℝ
  errStrain : ℝ
  errVorticityGrad : ℝ

def CellModelLong.IsLowLabel (L : CellModelLong) (α : ℤ × ℤ) : Prop := |α.1| ≤ (L.cut : ℤ)

structure IsCellModelSplit {count : ℕ} (box : Fin count → CellBox) (m : ℕ) (K : Fin count) (deg : ℕ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (model : ModelPolys count) (err : ModelErrors) (high : CellModelHigh) (long : CellModelLong) : Prop where
  velocity : IsSplitPart (ownSolid box K) W (model.velocity.field box m) high.velocity long.velocity
    err.velocityHigh long.errVelocity err.velocity
  vorticity : IsSplitPart (ownSolid box K) (vorticityOf W) (model.vorticity.field box m) high.vorticity long.vorticity
    err.vorticityHigh long.errVorticity err.vorticity
  strain : IsSplitPart (ownSolid box K) (strainOf W) (model.strain.field box m) high.strain long.strain
    err.strainHigh long.errStrain err.strain
  vorticityGrad : IsSplitPartAE (ownSolid box K) (vorticityGradOf HW) (model.vorticityGrad.field box m)
    high.vorticityGrad long.vorticityGrad err.vorticityGradHigh long.errVorticityGrad err.vorticityGrad
  long_modes : ∀ α : ℤ × ℤ, |α.1| ≤ 2 * (long.cut : ℤ) → ∀ p : ℝ × ℝ,
    (∀ a, labelVel m α long.velocity p a = 0) ∧ (∀ a, labelVel m α long.vorticity p a = 0) ∧
      (∀ a b, labelGrad m α long.strain p (a, b) = 0) ∧ (∀ a b, labelGrad m α long.vorticityGrad p (a, b) = 0)
  long_regular : ContinuousOn (fun z : ℝ × Space => long.velocity z.1 z.2)
      {z | 0 < CellCert.CellAnalysis.cylRadius z.2 ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0} ∧
    ContinuousOn (fun z : ℝ × Space => long.vorticity z.1 z.2)
      {z | 0 < CellCert.CellAnalysis.cylRadius z.2 ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0} ∧
    AEStronglyMeasurable (fun z : ℝ × Space => long.strain z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => long.vorticityGrad z.1 z.2) volume
  long_symmetric : ∀ σ y, ContinuousLinearMap.adjoint (long.strain σ y) = long.strain σ y
  long_nonneg : 0 ≤ long.errVelocity ∧ 0 ≤ long.errVorticity ∧ 0 ≤ long.errStrain ∧ 0 ≤ long.errVorticityGrad
  velocity_orthogonal : IsVecOrthogonal (box K) m (2 * deg + 1) high.velocity
  vorticity_orthogonal : IsVecOrthogonal (box K) m (2 * deg + 1) high.vorticity
  strain_orthogonal : IsMatOrthogonal (box K) m (2 * deg + 1) high.strain
  vorticityGrad_orthogonal : IsMatOrthogonal (box K) m (2 * deg + 1) high.vorticityGrad
  high_symmetric : ∀ σ y, ContinuousLinearMap.adjoint (high.strain σ y) = high.strain σ y
  high_measurable : AEStronglyMeasurable (fun z : ℝ × Space => high.velocity z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => high.vorticity z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => high.strain z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => high.vorticityGrad z.1 z.2) volume
  model_conj_closed : model.velocity.IsConjugateClosed box ∧ model.vorticity.IsConjugateClosed box ∧
    model.strain.IsConjugateClosed box ∧ model.vorticityGrad.IsConjugateClosed box
  errors_nonneg : 0 ≤ err.velocity ∧ 0 ≤ err.vorticity ∧ 0 ≤ err.strain ∧ 0 ≤ err.vorticityGrad ∧
    0 ≤ err.velocityHigh ∧ 0 ≤ err.vorticityHigh ∧ 0 ≤ err.strainHigh ∧ 0 ≤ err.vorticityGradHigh

def testValue (K : CellBox) (φ : Fin 3 → CellPoly) (p : ℝ × ℝ) : Fin 3 → ℂ := fun a => (φ a).eval K p

def turnVector (k : ℝ) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(k : ℂ) * Complex.I * x 0 - x 1, (k : ℂ) * Complex.I * x 1 + x 0, (k : ℂ) * Complex.I * x 2]

def testGrad (K : CellBox) (k : ℝ) (φ : Fin 3 → CellPoly) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => if b = 0 then CellBox.radialDeriv (fun p => (φ a).eval K p) p
    else if b = 2 then CellBox.heightDeriv (fun p => (φ a).eval K p) p
    else turnVector k (testValue K φ p) a / (p.1 : ℂ)

def IsTestSolenoidal (K : CellBox) (k : ℝ) (φ : Fin 3 → CellPoly) : Prop :=
  ∀ p ∈ K.rect, CellBox.radialDeriv (fun p => (p.1 : ℂ) * (φ 0).eval K p) p
    + (k : ℂ) * Complex.I * (φ 1).eval K p + (p.1 : ℂ) * CellBox.heightDeriv (fun p => (φ 2).eval K p) p = 0

def IsAxisRegularTest (K : CellBox) (k : ℝ) (φ : Fin 3 → CellPoly) : Prop :=
  ∃ C : ℝ, ∀ p ∈ K.rect, ∀ a, ‖turnVector k (testValue K φ p) a‖ ≤ C * p.1

def sideTestMoment (S : FaceSegment) (f : ℝ × ℝ → ℂ) (d : ℕ) : ℂ :=
  S.moment false f (CellBox.radialDeriv f) (CellBox.heightDeriv f) d

def basisValue (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : ℂ := ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)

def frameWeight (p : ℝ × ℝ) (b : Fin 3) : ℂ := if b = 0 then (p.1 : ℂ) else if b = 2 then (p.2 : ℂ) else 0

def ownStrainRow (L : CellLayout) (k : ℝ) (φ : Fin 3 → CellPoly) (a b : Fin 3) (j l : ℕ) : ℂ :=
  ∫ p in L.box.rect, (p.1 : ℂ) * basisValue L.bases j l p *
    ((starRingEnd ℂ) (testGrad L.box k φ p a b)
      + (1 / 2 : ℂ) * frameWeight p b * (starRingEnd ℂ) ((φ a).eval L.box p))

def ownVelocityRow (L : CellLayout) (freq : ℝ) (φ : Fin 3 → CellPoly) (a : Fin 3) (j l : ℕ) : ℂ :=
  ((freq : ℂ) * Complex.I + 1 / 2) *
    ∫ p in L.box.rect, (p.1 : ℂ) * basisValue L.bases j l p * (starRingEnd ℂ) ((φ a).eval L.box p)

def sideGradRow (L : CellLayout) (φ : Fin 3 → CellPoly) (s : Fin L.segCount) (a : Fin 3) (d : ℕ) : ℂ :=
  -edgeSign (L.segment s).level (L.segment s).other *
    (if (L.segment s).radial then ((L.segment s).level : ℂ) else 1) *
    (starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval L.box p) d)

def sidePresRow (L : CellLayout) (φ : Fin 3 → CellPoly) (s : Fin L.presCount) (d : ℕ) : ℂ :=
  edgeSign (L.presSegment s).level (L.presSegment s).other *
    (if (L.presSegment s).radial then ((L.presSegment s).level : ℂ) else 1) *
    (starRingEnd ℂ) (sideTestMoment (L.presSegment s)
      (fun p => (φ (if (L.presSegment s).radial then 0 else 2)).eval L.box p) d)

def ownRowVector (L : CellLayout) (k freq : ℝ) (φ : Fin 3 → CellPoly) : L.Datum → ℂ :=
  Sum.elim (fun i => ownStrainRow L k φ i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2)
  (Sum.elim (fun i => ownVelocityRow L freq φ i.2.1 i.2.2.1 i.2.2.2)
  (Sum.elim (fun _ => 0)
  (Sum.elim (fun i => sideGradRow L φ i.2.1 i.2.2.1 i.2.2.2)
  (Sum.elim (fun i => sidePresRow L φ i.2.1 i.2.2)
  (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 0)))))))

def IsPressureSegmentation (L : CellLayout) : Prop :=
  (∀ s, ((L.presSegment s).radial ∧ ((L.presSegment s).level = L.box.r₁ ∨ (L.presSegment s).level = L.box.r₂)) ∨
      (¬ (L.presSegment s).radial ∧ ((L.presSegment s).level = L.box.z₁ ∨ (L.presSegment s).level = L.box.z₂))) ∧
  (∀ s s', s ≠ s' → (L.presSegment s).radial = (L.presSegment s').radial →
      (L.presSegment s).level = (L.presSegment s').level →
      (L.presSegment s).hi ≤ (L.presSegment s').lo ∨ (L.presSegment s').hi ≤ (L.presSegment s).lo) ∧
  (∀ u, L.box.z₁ ≤ u → u ≤ L.box.z₂ → ∀ lev, (lev = L.box.r₂ ∨ (lev = L.box.r₁ ∧ L.box.r₁ ≠ 0)) →
      ∃ s, (L.presSegment s).radial ∧ (L.presSegment s).level = lev ∧ (L.presSegment s).lo ≤ u ∧ u ≤ (L.presSegment s).hi) ∧
  (∀ u, L.box.r₁ ≤ u → u ≤ L.box.r₂ → ∀ lev, (lev = L.box.z₁ ∨ lev = L.box.z₂) →
      ∃ s, ¬ (L.presSegment s).radial ∧ (L.presSegment s).level = lev ∧ (L.presSegment s).lo ≤ u ∧
        u ≤ (L.presSegment s).hi) ∧
  (∀ s, (L.presSegment s).radial → L.box.z₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ L.box.z₂ ∧
      (L.presSegment s).other = L.box.r₁ + L.box.r₂ - (L.presSegment s).level) ∧
  (∀ s, ¬ (L.presSegment s).radial → L.box.r₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ L.box.r₂ ∧
      (L.presSegment s).other = L.box.z₁ + L.box.z₂ - (L.presSegment s).level) ∧
  (∀ s d d', d < L.degSide → d' < L.degSide →
    ∫ u in Set.Icc (L.presSegment s).lo (L.presSegment s).hi, (L.presSegment s).test d u * (L.presSegment s).test d' u =
      if d = d' then 1 else 0)

def IsTestOfShape (K : CellBox) (q : ℕ) (φ : Fin 3 → CellPoly) : Prop :=
  ∀ a : Fin 3, ∃ c : ℕ → ℕ → ℂ, ∀ p : ℝ × ℝ, (φ a).eval K p
    = ∑ i ∈ Finset.range ((if a = 2 then q - 1 else q) + 1), ∑ j ∈ Finset.range ((if a = 0 then q - 1 else q) + 1),
        c i j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j

def couplingStrainRow (K : CellBox) (B : CellBases) (Wα : ℝ × ℝ → Fin 3 → ℂ) (φ : Fin 3 → CellPoly)
    (a b : Fin 3) (j l : ℕ) : ℂ :=
  ∫ p in K.rect, (p.1 : ℂ) * basisValue B j l p *
    ∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
      ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol i j' l' : ℂ) * Wα p j' * (starRingEnd ℂ) ((φ l').eval K p)

def couplingVelocityRow (K : CellBox) (B : CellBases) (Ωα : ℝ × ℝ → Fin 3 → ℂ) (φ : Fin 3 → CellPoly)
    (a : Fin 3) (j l : ℕ) : ℂ :=
  ∫ p in K.rect, (p.1 : ℂ) * basisValue B j l p *
    ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol a j' l' : ℂ) * (starRingEnd ℂ) ((φ j').eval K p) * Ωα p l'

def couplingRowVector (L : CellLayout) (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ) (φ : Fin 3 → CellPoly) : L.Datum → ℂ :=
  Sum.elim (fun i => couplingStrainRow L.box L.bases Wα φ i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2)
  (Sum.elim (fun i => couplingVelocityRow L.box L.bases Ωα φ i.2.1 i.2.2.1 i.2.2.2) (fun _ => 0))

def opBound (A : Fin 3 → Fin 3 → ℂ) (c : ℝ) : Prop :=
  ∀ u : Fin 3 → ℂ, (∑ a : Fin 3, ‖∑ b : Fin 3, A a b * u b‖ ^ 2) ≤ c ^ 2 * ∑ b : Fin 3, ‖u b‖ ^ 2

structure IsChargeBound (m : ℕ) (K : CellBox) (resolved : Finset (ℤ × ℤ)) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ch : ModeCharges) : Prop where
  strain : ∀ ι ∈ resolved, ∀ p ∈ K.rect, ∀ σ θ : ℝ, ∀ u : Space,
    inner ℝ (strainOf W σ (cylPoint p.1 θ p.2) u) u ≤ ch.curl ι p * ‖u‖ ^ 2
  mean_gradient : ∀ ι ∈ resolved, ∀ p ∈ K.rect,
    opBound (fun a b => labelGrad m (0, 0) (vorticityGradOf HW) p (a, b)) (ch.product ι p)
  wave_gradient : ∀ ι ∈ resolved, ∀ p ∈ K.rect, ∀ σ θ : ℝ, ∀ u : Space,
    ‖vorticityGradOf HW σ (cylPoint p.1 θ p.2) u
      - CellMatField.frameMap θ (fun a b => (labelGrad m (0, 0) (vorticityGradOf HW) p (a, b)).re) u‖
      ≤ ch.gradient ι p * ‖u‖

structure BoxConstants where
  sourceWeight : ℝ
  secondLength : ℝ
  strainSlack : ℝ
  rowWeight : ℤ × ℤ → ℝ
  orthWeight : ℝ

structure IsLeafBoxLink (m : ℕ) (K : CellBox) (resolved tested : Finset (ℤ × ℤ)) (err : ModelErrors)
    (bc : BoxConstants) (ch : ModeCharges) (T : LeafValues) : Prop where
  constants_pos : 0 < bc.sourceWeight ∧ 0 < bc.secondLength ∧ 0 ≤ bc.strainSlack ∧ 0 < bc.orthWeight ∧ ∀ ι, 0 ≤ bc.rowWeight ι
  box_curl : ∀ ι ∈ resolved, 2 * bc.sourceWeight * err.velocity ^ 2 ≤ T.boxCurl ι
  box_strain : ∀ ι ∈ resolved, bc.strainSlack ≤ T.boxStrain ι
  box_velocity : ∀ ι ∈ resolved, 2 * bc.sourceWeight * err.vorticity ^ 2
    + (if ι ∈ tested then bc.rowWeight ι * (2 * Real.pi * (labelTime ι : ℝ) * err.periodInverse) ^ 2 else 0)
    ≤ T.boxVelocity ι
  pair_curl : ∀ ι ∈ resolved, err.strain ≤ T.boxPairCurl ι
  pair_strain : ∀ ι ∈ resolved, ∀ p ∈ K.rect,
    3 / (2 * Real.sqrt 2) * err.vorticityGrad * bc.secondLength ≤ T.boxPairStrain ι
  pair_velocity : ∀ ι ∈ resolved, ∀ p ∈ K.rect,
    3 / (2 * Real.sqrt 2) * err.vorticityGrad / ch.length ι p ≤ T.boxPairVelocity ι

def IsPeriodModel {k : ℕ} (params : Set (Fin k → ℝ)) (period : (Fin k → ℝ) → ℝ) (x₁ ε₁ : ℝ) : Prop :=
  ∀ q ∈ params, |1 / period q - x₁| ≤ ε₁

def lowSlotForm (L : CellLayout) (A : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) : Matrix L.Datum L.Datum ℂ :=
  formOfRows (slotRow (layoutIndex L))
    (fun σ σ' => if σ.1 = σ'.1 then ∫ p in L.box.rect, ((L.box.lineWeight p.1 * CellScalars.rHat L.box p : ℝ) : ℂ) *
      matrixSesq (A p) (pairVec (slotValue L.bases σ.2 p).1 (slotValue L.bases σ.2 p).2)
        (pairVec (slotValue L.bases σ'.2 p).1 (slotValue L.bases σ'.2 p).2) else 0)

def lowStrainOf (L : CellLayout) (u : L.Datum → ℂ) (n : L.modes) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin (L.degCoef + 1), ∑ l : Fin (L.degCoef + 1),
    u (CellDatum.lowStrain n a b j l) * ((basisFn L.bases j l p : ℝ) : ℂ)

def lowVelocityOf (L : CellLayout) (u : L.Datum → ℂ) (n : L.modes) (a : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ j : Fin L.degCoef, ∑ l : Fin L.degCoef, u (CellDatum.lowVelocity n a j l) * ((basisFn L.bases j l p : ℝ) : ℂ)

abbrev CellVar (M : CellMesh) (K : Fin M.count) (A : CellModeLayouts) :=
  Σ ι : M.resolved K, (A.layout ι.1).Datum

abbrev CellIndex (M : CellMesh) (K : Fin M.count) (A : CellModeLayouts) (n k : ℕ) :=
  (CellVar M K A ⊕ Fin n) ⊕ (Fin k ⊕ Fin k)

section CellForm

variable {k : ℕ} {C : Type} {nE nM : ℕ}

end CellForm

def IsPlaneMatched (L L' : CellLayout) : Prop :=
  (∀ s, ¬ (L.segment s).radial → (L.segment s).level = 0 → ∃ s', ¬ (L'.segment s').radial ∧
    (L'.segment s').level = 0 ∧ (L'.segment s').lo = (L.segment s).lo ∧ (L'.segment s').hi = (L.segment s).hi ∧
    (L'.segment s').testCoef = (L.segment s).testCoef) ∧
  (∀ s, ¬ (L.presSegment s).radial → (L.presSegment s).level = 0 → ∃ s', ¬ (L'.presSegment s').radial ∧
    (L'.presSegment s').level = 0 ∧ (L'.presSegment s').lo = (L.presSegment s).lo ∧
    (L'.presSegment s').hi = (L.presSegment s).hi ∧ (L'.presSegment s').testCoef = (L.presSegment s).testCoef)

section Entry

variable {k : ℕ} {C : Type} {nE nM : ℕ}

structure CellCalculusEntry (D : CellLayerData k C nE nM) where
  layouts : Fin D.mesh.count → CellModeLayouts
  leaves : Fin D.mesh.count → LeafValues
  boxConstants : Fin D.mesh.count → BoxConstants
  high : Fin D.mesh.count → CellModelHigh
  long : Fin D.mesh.count → CellModelLong
  entryCharges : Fin D.mesh.count → ℤ × ℤ → TailBand.EntryCharges
  pairLabels : Finset (ℤ × ℤ)
  pairProfile : Fin D.mesh.count → Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ
  portCount : Fin D.mesh.count → ℕ
  portKey : (K : Fin D.mesh.count) → Fin (portCount K) → ℕ
  cellForm : (K : Fin D.mesh.count) →
    Matrix (CellIndex D.mesh K (layouts K) (portCount K) k) (CellIndex D.mesh K (layouts K) (portCount K) k) ℂ
  pairSlackLabels : Fin D.mesh.count → Finset (ℤ × ℤ)
  pairSlackWeight : Fin D.mesh.count → ℤ × ℤ → ℝ
  kappaCost : Fin D.mesh.count → ℝ
  creditCount : ℕ
  creditPatch : Fin creditCount → Bridge.CreditPatch
  creditOwner : (j : Fin creditCount) → Fin (creditPatch j).dataCount → Fin D.mesh.count
  creditCoord : (j : Fin creditCount) → (d : Fin (creditPatch j).dataCount) →
    CellVar D.mesh (creditOwner j d) (layouts (creditOwner j d))

structure CellCalculusConditions (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) : Prop where
  axis_modes : ∀ K, (D.mesh.box K).IsAxis → ∀ ι ∈ D.mesh.resolved K, ι.1 = 0
  layouts_valid : ∀ K, IsCellModeLayouts D.azimuthOrder D.mesh K (R.layouts K)
  leaves_valid : ∀ K, ∀ q ∈ D.cert.params, IsLeafValues (D.mesh.box K) (D.mesh.resolved K)
    (fun ι p => ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
      D.azimuthOrder ι p) (D.charges (some K)) (R.leaves K)
  charges_valid : ∀ K, IsChargeBound D.azimuthOrder (D.mesh.box K) (D.mesh.resolved K) D.given D.givenHess
    (D.charges (some K))
  box_link : ∀ K, IsLeafBoxLink D.azimuthOrder (D.mesh.box K) (D.mesh.resolved K) (D.mesh.tested K)
    (D.modelErrors K) (R.boxConstants K) (D.charges (some K)) (R.leaves K)
  model_split : ∀ K, IsCellModelSplit D.mesh.box D.azimuthOrder K (D.mesh.maxVolumeDeg K) D.given D.givenHess
    D.model (D.modelErrors K) (R.high K) (R.long K)
  period_model : ∀ K, IsPeriodModel D.cert.params D.cert.period D.model.periodInverse
    (D.modelErrors K).periodInverse
  pair_profile_regular : ∀ K g ι, (∀ a b, AEStronglyMeasurable (fun p => R.pairProfile K g ι p a b)
      (volume.restrict (D.mesh.box K).rect)) ∧ ∃ C : ℝ, ∀ p ∈ (D.mesh.box K).rect, ∀ a b, ‖R.pairProfile K g ι p a b‖ ≤ C
  pressure_placed : ∀ K, ∀ ι ∈ D.mesh.resolved K, IsPressureSegmentation ((R.layouts K).layout ι) ∧
    ∀ s, (((R.layouts K).layout ι).presSegment s).radial → (((R.layouts K).layout ι).presSegment s).level ≠ 0
  gauge_placed : ∀ K, ∀ ι ∈ D.mesh.resolved K, ((R.layouts K).layout ι).gauge.radial →
    ((R.layouts K).layout ι).gauge.level ≠ 0 ∧
      0 ≤ min ((R.layouts K).layout ι).gauge.level ((R.layouts K).layout ι).gauge.other
  plane_matched : ∀ K, ∀ ι ∈ D.mesh.resolved K, labelFlip ι ∈ D.mesh.resolved K →
    IsPlaneMatched ((R.layouts K).layout ι) ((R.layouts K).layout (labelFlip ι))

end Entry

section Assembly

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def modeBlockForm (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (ι : D.mesh.resolved K) : Matrix ((R.layouts K).layout ι.1).Datum ((R.layouts K).layout ι.1).Datum ℂ :=
  energyForm (D.mesh.box K) (R.layouts K).bases (layoutIndex ((R.layouts K).layout ι.1)) D.azimuthOrder
      (fun _ => (R.leaves K).hessFloor ι.1) (fun _ => (R.leaves K).curlHessFloor ι.1) (fun _ => 0)
    + lowSlotForm ((R.layouts K).layout ι.1) ((R.leaves K).localMatrix ι.1)

def energyLeafForm (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count) :
    Matrix (CellIndex D.mesh K (R.layouts K) (R.portCount K) k) (CellIndex D.mesh K (R.layouts K) (R.portCount K) k) ℂ :=
  Matrix.fromBlocks (Matrix.fromBlocks (Matrix.blockDiagonal' (modeBlockForm D R K)) 0 0 0) 0 0 0

end Assembly

end CellCalculus

end CertCell

end Breakdown

end
end

section

open MeasureTheory Matrix

open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace CreditEval

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def IsPlaneSideDatum (L : CellLayout) (S : Bridge.PlaneSegment) (j : Fin S.testCount) (x : L.Datum) (n : ℤ) : Prop :=
  ∃ (m : L.modes) (s : Fin L.segCount) (e : Fin (L.degSide + 2)),
    (m : ℤ) = n ∧ x = CellDatum.sideVelocity m s 2 e ∧ ¬ (L.segment s).radial ∧ (L.segment s).level = 0 ∧
    0 < (L.segment s).other ∧ (L.segment s).lo = S.lower ∧ (L.segment s).hi = S.upper ∧
    ∀ r, (L.segment s).test (e : ℕ) r = S.test j r

structure CreditEvalConditions (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) : Prop where
  mode_label : ∀ j d, labelHarmonic D.azimuthOrder (R.creditCoord j d).1.1 = (R.creditPatch j).label
  side_datum : ∀ j d, IsPlaneSideDatum ((R.layouts (R.creditOwner j d)).layout (R.creditCoord j d).1.1)
    ((R.creditPatch j).segment ((R.creditPatch j).dataOf d).1) ((R.creditPatch j).dataOf d).2
    (R.creditCoord j d).2 (R.creditCoord j d).1.1.1
  patches_valid : ∀ j, Bridge.IsCreditPatch (R.creditPatch j)
  region_in_mesh : ∀ j, (R.creditPatch j).region ⊆ ⋃ K, (D.mesh.box K).rect
  layouts_valid : ∀ K, IsCellModeLayouts D.azimuthOrder D.mesh K (R.layouts K)

end CreditEval

end CertCell

end Breakdown

end
end

section

open scoped ENNReal ComplexOrder

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

structure IsPairSurrogate {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (S : Fin k → Finset (ℤ × ℤ)) (ePair : Fin D.mesh.count → ℝ) : Prop where
  actuator_labels : ∀ i, ∀ ι ∈ S i, ι ∈ R.pairLabels ∧ -ι ∈ R.pairLabels
  pin_labels : ∀ i K, ∀ ι ∈ (D.pinValues i).labels K, ι ∈ R.pairLabels ∧ -ι ∈ R.pairLabels
  pin_profile : ∀ K i ι, ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
    R.pairProfile K (.inr i) ι p a b = CellCalculus.gradAt D.azimuthOrder ι (D.cert.pin i) a b p
  exact_off_slack : ∀ K i, ∀ ι ∈ R.pairLabels, ι ∉ R.pairSlackLabels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
    R.pairProfile K (.inl i) ι p a b = CellCalculus.gradAt D.azimuthOrder ι (gradField (D.cert.actuator i)) a b p
  profile_regular : ∀ K g ι a b, AEStronglyMeasurable (fun p => R.pairProfile K g ι p a b) (volume.restrict (D.mesh.box K).rect) ∧
    ∃ c : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖R.pairProfile K g ι p a b‖ ≤ c
  slack_in_labels : ∀ K, R.pairSlackLabels K ⊆ R.pairLabels
  slack_weight_pos : ∀ K, ∀ ι ∈ R.pairSlackLabels K, 0 < R.pairSlackWeight K ι
  surrogate_error : ∀ K, ∑ ι ∈ R.pairSlackLabels K, (4 * R.pairSlackWeight K ι)⁻¹ * ∑ i,
      ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3,
        ‖R.pairProfile K (.inl i) ι p a b
          - CellCalculus.gradAt D.azimuthOrder ι (gradField (D.cert.actuator i)) a b p‖ ^ 2
    ≤ ePair K

end InstancePair

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

def HasEdgeBreak (tb : ℝ) (D : TimeFieldData) : Prop :=
  ∀ κ ∈ D.keys, (κ.label.1 ≠ 0 → tb ∈ (D.amp κ).radial.mesh.tBreaks ∧ tb ∈ (D.amp κ).polar.mesh.tBreaks) ∧
    (κ.label.1 = 0 → tb ∈ (D.amp κ).stream.mesh.tBreaks ∧ tb ∈ (D.amp κ).swirl.mesh.tBreaks)

structure ActuatorSupportFacts {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (F : GivenShapeEntry k) (H : ℝ) : Prop where
  actuator_eq : ∀ i, D.cert.actuator i = shapeInfoField (F.actuatorParams i) (F.actuators i)
  actuatorParams_valid : ∀ i, IsShapeParams (F.actuatorParams i)
  actuators_valid : ∀ i, IsCompactTimeFieldData (F.actuatorEdge i) (F.actuators i)
  edge_break : ∀ i, HasEdgeBreak (F.actuatorEdge i) (F.actuators i)
  radius_le : ∀ i, (F.actuatorParams i).chartLength * F.actuatorEdge i / (1 - F.actuatorEdge i) ≤ H
  mesh_covers : ∀ p : ℝ × ℝ, p ∈ Set.Icc 0 H ×ˢ Set.Icc 0 H → ∃ K, p ∈ (D.mesh.box K).rect

end GivenShape

end CertCell

end Breakdown

end
end

section

noncomputable section

namespace Breakdown.CertCell.GaugeKey

open Breakdown.CellCert.CellCoordinates Breakdown.CellCert.CellFormula

open Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal

structure GaugeKeyValues where
  count : ℕ
  classLabel : Fin count → ℤ × ℤ
  conjClass : Fin count → Fin count
  deletedKey : Fin count → (ℤ × ℤ) × SkeletonKey
  endClass : ℤ × ℤ → SkeletonKey → Bool → Option (Fin count)
  incidence : Matrix (Fin count) (Fin count) ℤ
  incidenceInv : Matrix (Fin count) (Fin count) ℚ

namespace GaugeKeyValues

variable (G : GaugeKeyValues)

def endWeight (c : Fin G.count) (ι : ℤ × ℤ) (key : SkeletonKey) (b : Bool) : ℝ :=
  if G.endClass ι key b = some c then 1 else 0

def dirReal (c : Fin G.count) (ι : ℤ × ℤ) (key : SkeletonKey) : ℝ :=
  match key with
  | SkeletonKey.pressure n rad lev lo hi t d =>
      if ι = G.classLabel c ∧ n = 0 then
        (if rad then G.endWeight c ι key false * ∫ z in lo..hi, (keySegment rad lev lo hi t).test d z
          else G.endWeight c ι key true * radialWeightIntegral ((keySegment rad lev lo hi t).test d) hi
            - G.endWeight c ι key false * radialWeightIntegral ((keySegment rad lev lo hi t).test d) lo)
      else 0
  | _ => 0

def dir (c : Fin G.count) (ι : ℤ × ℤ) (key : SkeletonKey) : ℂ := (G.dirReal c ι key : ℂ)

def keyWeight : SkeletonKey → ℝ
  | SkeletonKey.pressure _ rad lev lo hi t d =>
      if rad then ∫ z in lo..hi, (keySegment rad lev lo hi t).test d z
      else radialWeightIntegral ((keySegment rad lev lo hi t).test d) hi
  | _ => 0

def deletedWeight (e : Fin G.count) : ℝ := keyWeight (G.deletedKey e).2

def matrix : Matrix (Fin G.count) (Fin G.count) ℂ :=
  fun e c => G.dir c (G.deletedKey e).1 (G.deletedKey e).2

def weightedIncidence : Matrix (Fin G.count) (Fin G.count) ℂ :=
  fun e c => (G.deletedWeight e : ℂ) * (G.incidence e c : ℂ)

end GaugeKeyValues

end Breakdown.CertCell.GaugeKey

end
end

section

noncomputable section

namespace Breakdown.CertCell.GaugeKey

open Breakdown.CellCert.CellCoordinates

def keyMode : SkeletonKey → Option ℤ
  | SkeletonKey.velocity n _ _ _ _ _ _ _ => some n
  | SkeletonKey.gradient n _ _ _ _ _ _ _ => some n
  | SkeletonKey.pressure n _ _ _ _ _ _ => some n
  | SkeletonKey.corner n _ _ => some n
  | SkeletonKey.stream _ => some 0
  | SkeletonKey.private_ => none

open Classical in
def planeSign : SkeletonKey → Option ℝ
  | SkeletonKey.velocity _ rad lev _ _ _ a _ => if rad = false ∧ lev = 0 then some (frameSign a) else none
  | SkeletonKey.gradient _ rad lev _ _ _ a _ => if rad = false ∧ lev = 0 then some (-frameSign a) else none
  | SkeletonKey.pressure _ rad lev _ _ _ _ => if rad = false ∧ lev = 0 then some 1 else none
  | SkeletonKey.corner _ p a => if p.2 = 0 then some (frameSign a) else none
  | SkeletonKey.stream p => if p.2 = 0 then some (-1) else none
  | SkeletonKey.private_ => none

def RealLabelOmitted (ι : ℤ × ℤ) (key : SkeletonKey) (imag : Bool) : Prop :=
  ι = 0 ∧ keyMode key = some 0 ∧ imag = true

def PlanePairOmitted (ι : ℤ × ℤ) (key : SkeletonKey) (imag : Bool) : Prop :=
  ι.1 = 2 * ι.2 ∧ 1 ≤ ι.2 ∧ keyMode key = some ι.1 ∧
    ((planeSign key = some 1 ∧ imag = true) ∨ (planeSign key = some (-1) ∧ imag = false))

def PlaneOddOmitted (ι : ℤ × ℤ) (key : SkeletonKey) : Prop :=
  ι.1 = 0 ∧ keyMode key = some 0 ∧ planeSign key = some (-1)

namespace GaugeKeyValues

variable (G : GaugeKeyValues)

def DeletedOmitted (ι : ℤ × ℤ) (key : SkeletonKey) : Prop := ∃ e, G.deletedKey e = (ι, key)

structure Conditions : Prop where
  label_axis : ∀ c, (G.classLabel c).1 = 0
  conj_invol : ∀ c, G.conjClass (G.conjClass c) = c
  conj_label : ∀ c, G.classLabel (G.conjClass c) = -G.classLabel c
  conj_self : ∀ c, G.classLabel c = 0 → G.conjClass c = c
  deleted_label : ∀ e, (G.deletedKey e).1 = G.classLabel e
  deleted_conj : ∀ e, (G.deletedKey (G.conjClass e)).2 = (G.deletedKey e).2
  deleted_pressure : ∀ e, ∃ rad lev lo hi t d, (G.deletedKey e).2 = SkeletonKey.pressure 0 rad lev lo hi t d
  weight_ne : ∀ e, G.deletedWeight e ≠ 0
  matrix_eq : ∀ e c, G.matrix e c = G.weightedIncidence e c
  inv_left : ∀ c c', ∑ e, G.incidenceInv c e * (G.incidence e c' : ℚ) = if c = c' then 1 else 0
  inv_right : ∀ e e', ∑ c, (G.incidence e c : ℚ) * G.incidenceInv c e' = if e = e' then 1 else 0
  inv_conj : ∀ c e, G.incidenceInv (G.conjClass c) (G.conjClass e) = G.incidenceInv c e
  inv_block : ∀ c e, G.incidenceInv c e ≠ 0 → G.classLabel c = G.classLabel e

end GaugeKeyValues

end Breakdown.CertCell.GaugeKey

end
end

section

open scoped ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellLayerData

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def withFormCoercivity (c : ℝ) : CellLayerData k C nE nM :=
  { D with pieces := fun q => { D.pieces q with c := c } }

end CellLayerData

section Statements

variable {k : ℕ} {C : Type} {nE nM : ℕ}

structure AdmissibleTuple (D : CellLayerData k C nE nM) (cForm : ℝ) (q : Fin k → ℝ) where
  v : ℝ → Space → Space
  G : ℝ → Space → (Space →L[ℝ] Space)
  H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)
  g : ℝ → Space → Space
  κ : Fin k → ℝ
  F : ℝ → Space → Space
  perturbation : IsPerturbation D.cert.symmetries (D.cert.period q) v G H g
  right_measurable : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume
  right_periodic : IsTimePeriodic F
  right_finite : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤
  right_side : IsRightSide (D.cert.model q) D.cert.actuator κ v G g F
  pos_finite : (D.withFormCoercivity cForm).formPos q v G H < ⊤

structure IsBoxUniform (D : CellLayerData k C nE nM) : Prop where
  model_eq : ∀ q ∈ D.cert.params, D.cert.model q = D.given
  classOf_eq : ∀ q ∈ D.cert.params, (D.pieces q).classOf = (D.pieces 0).classOf
  convD_eq : ∀ q ∈ D.cert.params, (D.pieces q).convD = (D.pieces 0).convD
  convZ_eq : ∀ q ∈ D.cert.params, (D.pieces q).convZ = (D.pieces 0).convZ
  eps_eq : ∀ q ∈ D.cert.params, ∀ β, { D.pieces q |>.epsP β with frame := 0 } = { D.pieces 0 |>.epsP β with frame := 0 }
  mu_eq : ∀ q ∈ D.cert.params, ∀ β, { D.pieces q |>.muP β with frame := 0 } = { D.pieces 0 |>.muP β with frame := 0 }
  c_eq : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity
  cμ_eq : ∀ q ∈ D.cert.params, (D.pieces q).cμ = (D.pieces 0).cμ
  bounds_eq : ∀ q ∈ D.cert.params, D.bounds q = D.bounds 0

def globalForm (D : CellLayerData k C nE nM) (e : ℝ) (κ ζ : Fin k → ℝ) : ℝ :=
  -(D.coercivity * D.cert.multiplierWeight ^ 2 / (4 * Real.pi) + e) * ∑ i, κ i ^ 2
    - ∑ i, ζ i ^ 2 / (4 * Real.pi * D.pinWeight)

def realLeafForm {n A : Type} [Fintype n] [Fintype A] (P : Matrix n A ℂ) (Ψ : Matrix n n ℂ) :
    Matrix A A ℝ :=
  fun i j => ((P.conjTranspose * Ψ * P) i j).re

structure TreeEntry (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D) where
  Slaved : Type
  slavedFintype : Fintype Slaved
  Free : Type
  freeFintype : Fintype Free
  embed : (K : Fin D.mesh.count) →
    Matrix (CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k) (Slaved ⊕ Free) ℂ
  globalLeaf : Matrix (Slaved ⊕ Free) (Slaved ⊕ Free) ℝ
  evalCell : Slaved → Option (Σ K : Fin D.mesh.count, CellCalculus.CellVar D.mesh K (R.layouts K))
  evalKappa : Slaved → Option (Fin k)
  evalImag : Slaved → Bool
  freeMap : Matrix Slaved Free ℝ
  Node : Type
  nodeFintype : Fintype Node
  parent : Node → Option Node
  root : Node
  Part : Fin D.mesh.count → Type
  partFintype : (K : Fin D.mesh.count) → Fintype (Part K)
  partOf : (K : Fin D.mesh.count) → CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k → Part K
  pieceNode : (K : Fin D.mesh.count) → Part K → Part K → Node
  NullPair : Type
  nullPairFintype : Fintype NullPair
  nullPairForm : NullPair → Matrix (Slaved ⊕ Free) (Slaved ⊕ Free) ℝ
  nullPairNode : NullPair → Bool → Node
  globalNode : Node
  creditNode : Fin R.creditCount → Node
  pivots : Node → Finset (Slaved ⊕ Free)
  slack : Node → Slaved ⊕ Free → ℝ
  Column : Type
  columnFintype : Fintype Column
  columnNode : Column → Node
  column : Column → Slaved ⊕ Free → ℝ
  basePoint : (q : Fin k → ℝ) → AdmissibleTuple D D.coercivity q
  skelKey : Slaved → Option ((ℤ × ℤ) × CellCert.CellCoordinates.SkeletonKey)
  keyLayout : CellCert.CellFormula.CellLayout
  gauge : GaugeKey.GaugeKeyValues

def keySeg (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) : CellCert.CellFormula.FaceSegment := ⟨rad, lev, lev + 1, lo, hi, t⟩

namespace TreeEntry

variable {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D} (T : TreeEntry D R)

abbrev Leaf := ((Option (Σ K : Fin D.mesh.count, T.Part K × T.Part K)) ⊕ (T.NullPair × Bool)) ⊕ Fin R.creditCount

instance leafFintype : Fintype T.Leaf :=
  haveI := T.partFintype
  haveI := T.nullPairFintype
  inferInstance

open Classical in
def pieceForm (K : Fin D.mesh.count) (j j' : T.Part K) :
    Matrix (CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k)
      (CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k) ℂ :=
  fun a b => if T.partOf K a = j ∧ T.partOf K b = j' then R.cellForm K a b else 0

def creditEmbed (j : Fin R.creditCount) : Matrix (Fin (R.creditPatch j).dataCount) (T.Slaved ⊕ T.Free) ℂ :=
  fun d => T.embed (R.creditOwner j d) (Sum.inl (Sum.inl (R.creditCoord j d)))

def leafForm : T.Leaf → Matrix (T.Slaved ⊕ T.Free) (T.Slaved ⊕ T.Free) ℝ
  | .inl (.inl none) => T.globalLeaf
  | .inl (.inl (some ⟨K, (j, j')⟩)) =>
      (haveI := T.slavedFintype; haveI := T.freeFintype; realLeafForm (T.embed K) (T.pieceForm K j j'))
  | .inl (.inr (p, true)) => T.nullPairForm p
  | .inl (.inr (p, false)) => -T.nullPairForm p
  | .inr j => (haveI := T.slavedFintype; haveI := T.freeFintype; 2 • realLeafForm (T.creditEmbed j) (R.creditPatch j).credit)

def leafNode : T.Leaf → T.Node
  | .inl (.inl none) => T.globalNode
  | .inl (.inl (some ⟨K, (j, j')⟩)) => T.pieceNode K j j'
  | .inl (.inr (p, b)) => T.nullPairNode p b
  | .inr j => T.creditNode j

def tree (front : T.Node → Matrix (T.Slaved ⊕ T.Free) (T.Slaved ⊕ T.Free) ℝ) :
    Certificate.SignedTree T.Slaved T.Free where
  Leaf := T.Leaf
  leafFintype := T.leafFintype
  Node := T.Node
  nodeFintype := T.nodeFintype
  Column := T.Column
  columnFintype := T.columnFintype
  leafForm := T.leafForm
  leafNode := T.leafNode
  parent := T.parent
  root := T.root
  front := front
  pivots := T.pivots
  slack := T.slack
  columnNode := T.columnNode
  column := T.column

def gaugeDir (K : Fin D.mesh.count) (c : Fin T.gauge.count) :
    CellCalculus.CellIndex D.mesh K (R.layouts K) (R.portCount K) k → ℂ :=
  Sum.elim (Sum.elim (fun d => T.gauge.dir c d.1.1 (CellCert.CellCoordinates.keyOf ((R.layouts K).layout d.1.1) d.2))
    (fun _ => 0)) (fun _ => 0)

end TreeEntry

structure TreeConditionsGiven (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) : Prop where
  root_parent : T.parent T.root = none
  only_root : ∀ ν, T.parent ν = none → ν = T.root
  piece_node_symm : ∀ K j j', T.pieceNode K j j' = T.pieceNode K j' j
  node_conditions_given : ∃ front : T.Node → Matrix (T.Slaved ⊕ T.Free) (T.Slaved ⊕ T.Free) ℝ,
    (∀ ν, (haveI := T.slavedFintype; haveI := T.freeFintype;
      Certificate.PassesNodeEnclosure (T.tree front) ν)) ∧
    (haveI := T.slavedFintype; haveI := T.freeFintype; Certificate.PassesPivotCount (T.tree front))

structure CoefficientEntry (C : Type) (nE nM : ℕ) where
  count : ℕ
  entry : Fin count → TailBand.SetPieceBounds C nE nM
  modes : Fin count → Set (ℤ × ℤ)
  region : Fin count → Set (ℝ × ℝ)
  floor : ℝ
  resolvedLow : ℕ → ℤ × ℤ → ModeCoefficients
  resolvedFloor : ℝ

structure CoefficientConditions (D : CellLayerData k C nE nM) (E : CoefficientEntry C nE nM) : Prop where
  valid : ∀ q ∈ D.cert.params, ∀ j,
    (E.entry j).IsValidOn (D.pieces q) (D.cert.period q) (D.bounds q) D.azimuthOrder (E.modes j) (E.region j)
  covers : ∀ ι : ℤ × ℤ, ∀ p ∈ halfPlane, (∀ K, p ∈ (D.mesh.box K).rect → ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K) →
    ∃ j, ι ∈ E.modes j ∧ p ∈ E.region j
  floor_bound : ∀ q ∈ D.cert.params, ∀ j, ∀ p ∈ E.region j,
    -E.floor ≤ ((E.entry j).lowCoef (D.pieces q) (D.bounds q) D.cert.weightFn p).hess ∧
    -E.floor ≤ ((E.entry j).lowCoef (D.pieces q) (D.bounds q) D.cert.weightFn p).curlGrad ∧
    -E.floor ≤ ((E.entry j).lowCoef (D.pieces q) (D.bounds q) D.cert.weightFn p).curl ∧
    -E.floor ≤ ((E.entry j).lowCoef (D.pieces q) (D.bounds q) D.cert.weightFn p).grad ∧
    -E.floor ≤ (p.1 ^ 2 + p.2 ^ 2) * ((E.entry j).lowCoef (D.pieces q) (D.bounds q) D.cert.weightFn p).vel
  resolved_valid : ∀ q ∈ D.cert.params, ∀ K, ∀ ι ∈ D.mesh.resolved K ∪ D.mesh.band K, ∀ p ∈ (D.mesh.box K).rect,
    (E.resolvedLow K ι).hess ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).hess ∧
    (E.resolvedLow K ι).curlHess ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).curlHess ∧
    (E.resolvedLow K ι).curl ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).curl ∧
    (E.resolvedLow K ι).strain ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).strain ∧
    (E.resolvedLow K ι).velocity ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.azimuthOrder ι p).velocity
  resolved_floor : ∀ K, ∀ ι ∈ D.mesh.resolved K ∪ D.mesh.band K, ∀ p ∈ (D.mesh.box K).rect,
    -E.resolvedFloor ≤ (E.resolvedLow K ι).hess ∧ -E.resolvedFloor ≤ (E.resolvedLow K ι).curlHess ∧
    -E.resolvedFloor ≤ (E.resolvedLow K ι).curl ∧ -E.resolvedFloor ≤ (E.resolvedLow K ι).strain ∧
    -E.resolvedFloor ≤ (p.1 ^ 2 + p.2 ^ 2) * (E.resolvedLow K ι).velocity

structure ContinuumConditionsGiven (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) :
    Prop where
  enclosure_admissible : ∃ epsSup epsGradSup ratio : ℝ, ∀ q ∈ D.cert.params,
    InstanceSplit.EnclosureAdmissibleClauses (D.pieces q) (D.cert.period q) (D.bounds q) D.given D.givenHess
      epsSup epsGradSup ratio
  values_flip : ∀ q ∈ D.cert.params, InstanceSplit.ValuesFlipClauses (D.pieces q) (D.bounds q)
  coefficients : ∃ E : CoefficientEntry C nE nM, CoefficientConditions D E

structure CellHypothesis (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ) : Prop where
  instance_entry : Instance.IsInstanceEntry D X
  cell_conditions : CellCalculus.CellCalculusConditions D R
  tree_conditions : TreeConditionsGiven D R T
  pair_surrogate : ∃ ePair : Fin D.mesh.count → ℝ, InstancePair.IsPairSurrogate D R X.actuatorModes ePair ∧
    ∑ K, R.kappaCost K + ∑ K, ePair K ≤ e
  credit_evaluations : CreditEval.CreditEvalConditions D R
  kappaCost_nonneg : ∀ K, 0 ≤ R.kappaCost K
  continuum_conditions_given : ContinuumConditionsGiven D X
  bound_valueSets : ∃ B : GivenShape.BoundValuesEntry D, GivenShape.IsBoundValuesEntry D B
  given_shape : ∃ (F : GivenShape.GivenShapeEntry k) (S : GivenShape.ScaledJetData) (Hs : ℝ),
    GivenShape.IsScaledJetEntry D X F S ∧ GivenShape.ActuatorSupportFacts D F Hs
  rowWeightMax_eq : X.rowWeightMax = 400 * (1 + 2 ^ (-18 : ℤ))
  mesh_valid : IsCellMesh D.mesh
  azimuth_ge : 3 ≤ D.azimuthOrder
  box_uniform : IsBoxUniform D
  weightFn_eq : D.cert.weightFn = fun _ => 39 / 50
  coercivity_eq : D.coercivity = 3 / 50
  pinWeight_eq : D.pinWeight = 1000
  mode_class : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder

end Statements

end CertCell

end Breakdown

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace GaugeKey

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def unitMoment : CellCert.CellCoordinates.SkeletonKey → ℝ
  | CellCert.CellCoordinates.SkeletonKey.pressure _ rad lev lo hi t d =>
      if rad then ∫ z in lo..hi, (CellCert.CellCoordinates.MeshSkeletonInternal.keySegment rad lev lo hi t).test d z
      else CellCert.CellFormula.radialWeightIntegral
          ((CellCert.CellCoordinates.MeshSkeletonInternal.keySegment rad lev lo hi t).test d) hi
        - CellCert.CellFormula.radialWeightIntegral
          ((CellCert.CellCoordinates.MeshSkeletonInternal.keySegment rad lev lo hi t).test d) lo
  | _ => 0

def KeyInHalfPlane : CellCert.CellCoordinates.SkeletonKey → Prop
  | CellCert.CellCoordinates.SkeletonKey.velocity _ rad lev lo _ _ _ _ => if rad then 0 < lev else 0 ≤ lo
  | CellCert.CellCoordinates.SkeletonKey.gradient _ rad lev lo _ _ _ _ => if rad then 0 < lev else 0 ≤ lo
  | CellCert.CellCoordinates.SkeletonKey.pressure _ rad lev lo _ _ _ => if rad then 0 < lev else 0 ≤ lo
  | CellCert.CellCoordinates.SkeletonKey.corner _ p _ => 0 < p.1
  | CellCert.CellCoordinates.SkeletonKey.stream p => 0 ≤ p.1
  | CellCert.CellCoordinates.SkeletonKey.private_ => True

end GaugeKey

namespace TreeEntry

open CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D}
  (T : TreeEntry D R)

def KeyPartOmitted (ι : ℤ × ℤ) (key : SkeletonKey) (imag : Bool) : Prop :=
  GaugeKey.RealLabelOmitted ι key imag ∨ (GaugeKey.PlanePairOmitted ι key imag ∧ GaugeKey.KeyInHalfPlane key) ∨
    (GaugeKey.PlaneOddOmitted ι key ∧ GaugeKey.KeyInHalfPlane key) ∨ T.gauge.DeletedOmitted ι key

def varDir (c : Fin T.gauge.count) (a : T.Slaved) : ℂ :=
  match T.evalCell a, T.evalKappa a with
  | some ⟨K, d⟩, _ => T.gaugeDir K c (Sum.inl (Sum.inl d))
  | none, some _ => 0
  | none, none =>
      match T.skelKey a with
      | some (ι, key) => T.gauge.dir c ι key
      | none => 0

def varPartDir (c : Fin T.gauge.count) (a : T.Slaved) : ℂ :=
  if T.evalImag a then (T.varDir c a - T.varDir (T.gauge.conjClass c) a) / (2 * Complex.I)
  else (T.varDir c a + T.varDir (T.gauge.conjClass c) a) / 2

def GaugeRowTransport (rowVec : ∀ K : Fin D.mesh.count, CellCalculus.CellVar D.mesh K (R.layouts K) → T.Slaved → ℂ) :
    Prop :=
  haveI := T.slavedFintype
  ∀ K d c, ¬ T.gauge.DeletedOmitted d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) →
    T.gaugeDir K c (Sum.inl (Sum.inl d)) = ∑ a, rowVec K d a * T.varPartDir c a

structure GaugeKeyConditions : Prop where
  values : T.gauge.Conditions
  kernel : ∀ K c, R.cellForm K *ᵥ T.gaugeDir K c = 0 ∧ (R.cellForm K)ᴴ *ᵥ T.gaugeDir K c = 0
  credit : ∀ j d c, T.gaugeDir (R.creditOwner j d) c (Sum.inl (Sum.inl (R.creditCoord j d))) = 0
  unit_cover : ∀ K (d : CellCalculus.CellVar D.mesh K (R.layouts K)),
    (∃ rad lev lo hi t dd, keyOf ((R.layouts K).layout d.1.1) d.2 = SkeletonKey.pressure 0 rad lev lo hi t dd) →
    ∑ c, T.gauge.dirReal c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) =
      GaugeKey.unitMoment (keyOf ((R.layouts K).layout d.1.1) d.2)

structure RealKeyConditions : Prop where
  var_key_mode : ∀ a ι key, T.skelKey a = some (ι, key) → T.evalCell a = none → T.evalKappa a = none →
    GaugeKey.keyMode key = some ι.1
  key_geometry : ∀ K (d : CellCalculus.CellVar D.mesh K (R.layouts K)),
    GaugeKey.KeyInHalfPlane (keyOf ((R.layouts K).layout d.1.1) d.2)

end TreeEntry

end CertCell

end Breakdown

end
end

section

open MeasureTheory Matrix

open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

section Residual

variable {k : ℕ} {C : Type} {nE nM : ℕ}

abbrev CellVars (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count) : Type :=
  CellIndex D.mesh K (R.layouts K) (R.portCount K) k

structure IsRegionChargeBound (m : ℕ) (Z : Set (ℝ × ℝ)) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ch : ModeCharges) : Prop where
  strain : ∀ ι, ∀ p ∈ Z, ∀ σ θ : ℝ, ∀ u : Space,
    inner ℝ (strainOf W σ (cylPoint p.1 θ p.2) u) u ≤ ch.curl ι p * ‖u‖ ^ 2
  mean_gradient : ∀ ι, ∀ p ∈ Z, opBound (fun a b => labelGrad m (0, 0) (vorticityGradOf HW) p (a, b)) (ch.product ι p)
  wave_gradient : ∀ ι, ∀ p ∈ Z, ∀ σ θ : ℝ, ∀ u : Space,
    ‖vorticityGradOf HW σ (cylPoint p.1 θ p.2) u
      - CellMatField.frameMap θ (fun a b => (labelGrad m (0, 0) (vorticityGradOf HW) p (a, b)).re) u‖
      ≤ ch.gradient ι p * ‖u‖
  length_common : ∀ ι ι', ∀ p ∈ Z, ch.length ι p = ch.length ι' p
  length_pos : ∀ ι, ∀ p ∈ Z, 0 < ch.length ι p
  charges_nonneg : ∀ ι, ∀ p ∈ Z, 0 ≤ ch.product ι p ∧ 0 ≤ ch.gradient ι p

structure CellBlocks (V : Type) where
  potentialKept : Matrix V V ℂ
  pairingKept : Matrix V V ℂ
  top : Matrix V V ℂ
  bandWeight : ℤ × ℤ → Fin 12 → ℝ
  potentialSource : ℤ × ℤ → V → ℝ × ℝ → Fin 12 → ℂ
  pairingSource : ℤ × ℤ → V → ℝ × ℝ → Fin 12 → ℂ
  rowCount : ℕ
  rowMap : Matrix (Fin rowCount) V ℂ
  rowBand : Fin rowCount → ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ
  rowWeight : Matrix (Fin rowCount) (Fin rowCount) ℂ
  leakModes : Finset (ℤ × ℤ)
  leakCurl : ℤ × ℤ → ℝ
  leakVel : ℤ × ℤ → ℝ
  leakStrain : ℤ × ℤ → ℝ
  potentialStrainCost : ℤ × ℤ → ℝ
  potentialVelCost : ℤ × ℤ → ℝ
  potentialCurlCost : ℤ × ℤ → ℝ
  pairingStrainCost : ℤ × ℤ → ℝ
  rowStrainCost : ℤ × ℤ → ℝ
  rowVelCost : ℤ × ℤ → ℝ
  bandMap : ℤ × ℤ → V → ℝ × ℝ → Fin 12 → ℂ
  bandSlack : ℝ
  rowFull : Matrix (Fin rowCount) (Fin rowCount) ℂ
  budget : ℤ × ℤ → TailBand.TailBudget
  topBlock : ℤ × ℤ → Matrix V V ℂ
  rowLabel : Fin rowCount → ℤ × ℤ
  rowTest : Fin rowCount → ℕ
  rowTailTest : Fin rowCount → ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ
  leakWeight : ℤ × ℤ → ℝ
  rowKappaCost : ℝ
  actuatorModel : ℕ → ℝ → Space → Space
  actuatorRows : Finset (ℤ × ℤ)
  actuatorCost : ℝ
  actuatorErr : ℝ
  freqCost : ℤ × ℤ → ℝ
  errorCost : ℝ
  deactCost : ℝ
  longLowCost : ℝ
  longHighCost : ℝ
  bandCurlAllowance : ℤ × ℤ → ℝ
  bandVelAllowance : ℤ × ℤ → ℝ

structure AssemblyEntry (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) where
  blocks : (K : Fin D.mesh.count) → CellBlocks (CellVars D R K)

variable (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def restrictData (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) :
    ((R.layouts K).layout ι.1).Datum → ℂ :=
  fun d => x (Sum.inl (Sum.inl ⟨ι, d⟩))

def linearField {V : Type} [Fintype V] (S : V → ℝ × ℝ → Fin 12 → ℂ) (x : V → ℂ) (p : ℝ × ℝ) : Fin 12 → ℂ :=
  fun j => ∑ d, x d * S d p j

open Classical in
def creditVelDemand (K : Fin D.mesh.count) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  ∑ j, if (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
      labelHarmonic D.azimuthOrder ι = -(flipLabel (R.creditPatch j).label)) ∧ p ∈ (R.creditPatch j).region
    then (R.creditPatch j).charge p else 0

def turnMatrix (n : ℤ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(n : ℂ) * Complex.I, -1, 0; 1, (n : ℂ) * Complex.I, 0; 0, 0, (n : ℂ) * Complex.I]

variable (A : AssemblyEntry D R)

def totalStrainCost {V : Type} (B : CellBlocks V) (ι : ℤ × ℤ) : ℝ :=
  B.potentialStrainCost ι + B.pairingStrainCost ι + B.rowStrainCost ι

def totalVelCost {V : Type} (B : CellBlocks V) (ι : ℤ × ℤ) : ℝ :=
  B.potentialVelCost ι + B.rowVelCost ι

structure EntryChargesRegular (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) : Prop where
  measurable : ∀ K ι, AEStronglyMeasurable (R.entryCharges K ι).curlCharge (volume.restrict (D.mesh.box K).rect) ∧
    AEStronglyMeasurable (R.entryCharges K ι).gradCharge (volume.restrict (D.mesh.box K).rect) ∧
    AEStronglyMeasurable (R.entryCharges K ι).velCharge (volume.restrict (D.mesh.box K).rect) ∧
    AEStronglyMeasurable ((D.charges (some K)).curl ι) (volume.restrict (D.mesh.box K).rect) ∧
    AEStronglyMeasurable ((D.charges (some K)).product ι) (volume.restrict (D.mesh.box K).rect) ∧
    AEStronglyMeasurable ((D.charges (some K)).gradient ι) (volume.restrict (D.mesh.box K).rect) ∧
    AEStronglyMeasurable ((D.charges (some K)).length ι) (volume.restrict (D.mesh.box K).rect)
  bounded : ∀ K, ∃ c : ℝ, ∀ ι, ∀ p ∈ (D.mesh.box K).rect,
    |(R.entryCharges K ι).curlCharge p| ≤ c ∧ |(R.entryCharges K ι).gradCharge p| ≤ c ∧
    |(R.entryCharges K ι).velCharge p| ≤ c ∧ |(R.entryCharges K ι).stretchConst| ≤ c ∧
    |(D.charges (some K)).curl ι p| ≤ c ∧ |(D.charges (some K)).product ι p| ≤ c ∧
    |(D.charges (some K)).gradient ι p| ≤ c ∧ c⁻¹ ≤ (D.charges (some K)).length ι p ∧
    (D.charges (some K)).length ι p ≤ c

structure FieldRegular (D : CellLayerData k C nE nM) : Prop where
  mesh_valid : IsCellMesh D.mesh
  azimuth_pos : 1 ≤ D.azimuthOrder
  model_state : ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B
  model_harmonics : Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess
  hessian_symmetric : ∀ σ y u w, D.givenHess σ y u w = D.givenHess σ y w u
  admissible : ∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q)
    (D.bounds q) D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃
  bounds_measurable : ∀ q ∈ D.cert.params, Bridge.HasMeasurableBoundData (D.pieces q) (D.bounds q)
  mode_class : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder
  actuators : ∀ i, ∃ S : Finset (ℤ × ℤ), Instance.ActuatorShapeFacts D.azimuthOrder S (D.cert.actuator i)

structure AssemblyRegular (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) : Prop where
  field : FieldRegular D
  charges : EntryChargesRegular D R
  pair_profiles : ∀ K g ι a b, AEStronglyMeasurable (fun p => R.pairProfile K g ι p a b)
      (volume.restrict (D.mesh.box K).rect) ∧ ∃ c : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖R.pairProfile K g ι p a b‖ ≤ c
  leaves : ∀ K ι i j, AEStronglyMeasurable (fun p => (R.leaves K).localMatrix ι p i j)
      (volume.restrict (D.mesh.box K).rect) ∧ ∃ c : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖(R.leaves K).localMatrix ι p i j‖ ≤ c

end Residual

section StageConditions

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def sourceSum {V : Type} [Fintype V] (B : CellBlocks V) (ι : ℤ × ℤ) (x : V → ℂ) (p : ℝ × ℝ) : Fin 12 → ℂ :=
  fun j => linearField (B.potentialSource ι) x p j + linearField (B.pairingSource ι) x p j

def gradSlot (j : Fin 9) : Fin 12 := ⟨j.val, by omega⟩

def turnedVec (n : ℤ) (p : ℝ × ℝ) (U : Fin 12 → ℂ) (j : Fin 9) : ℂ :=
  U (gradSlot j) + if j.val % 3 = 1 then
    (p.1 : ℂ) * ∑ b : Fin 3, (starRingEnd ℂ) ((turnMatrix n)⁻¹ b ⟨j.val / 3, by omega⟩) * U ⟨9 + b.val, by omega⟩
  else 0

def turnedSource {V : Type} [Fintype V] (B : CellBlocks V) (ι : ℤ × ℤ) (x : V → ℂ) (p : ℝ × ℝ) : Fin 9 → ℂ :=
  turnedVec (labelAzimuth D.azimuthOrder ι) p (sourceSum B ι x p)

def turnedRowBand {V : Type} (B : CellBlocks V) (i : Fin B.rowCount) (ι : ℤ × ℤ) (p : ℝ × ℝ) : Fin 9 → ℂ :=
  turnedVec (labelAzimuth D.azimuthOrder ι) p (B.rowBand i ι p)

def bandEliminated {V : Type} [Fintype V] (K : Fin D.mesh.count) (B : CellBlocks V) (x : V → ℂ) : ℝ :=
  ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect, p.1 *
    (∑ j : Fin 9, B.bandWeight ι (gradSlot j) * ‖linearField (B.bandMap ι) x p (gradSlot j)‖ ^ 2
      - 2 * (∑ j : Fin 9, (starRingEnd ℂ) (linearField (B.bandMap ι) x p (gradSlot j)) * turnedSource D B ι x p j).re
      - ∑ j : Fin 9, ‖turnedSource D B ι x p j - (B.bandWeight ι (gradSlot j) : ℂ) * linearField (B.bandMap ι) x p (gradSlot j)‖ ^ 2
          / (B.bandWeight ι (gradSlot j) * B.bandSlack))

def rowsEliminated {V : Type} [Fintype V] (K : Fin D.mesh.count) (B : CellBlocks V) (x : V → ℂ) : ℝ :=
  Coupling.inverseWeightedSq B.rowFull (B.rowMap *ᵥ x - fun i => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
    (p.1 : ℂ) * ∑ j : Fin 9, linearField (B.bandMap ι) x p (gradSlot j) * (starRingEnd ℂ) (turnedRowBand D B i ι p j))

def bandGram {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) : Matrix (Fin B.rowCount) (Fin B.rowCount) ℂ :=
  fun i i' => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
    (p.1 : ℂ) * ∑ j : Fin 9, (starRingEnd ℂ) (turnedRowBand D B i ι p j) * turnedRowBand D B i' ι p j
      / (B.bandWeight ι (gradSlot j) : ℂ)

def IsBoundedOnCell (K : Fin D.mesh.count) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict (D.mesh.box K).rect) ∧ ∃ c : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖f p‖ ≤ c

structure EliminationConditions (A : AssemblyEntry D R) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop where
  mesh_valid : IsCellMesh D.mesh
  residual_value_le : ∀ K (x : CellVars D R K → ℂ), S K x → quadFormValue (R.cellForm K - energyLeafForm D R K) x
    ≤ quadFormValue (A.blocks K).potentialKept x + quadFormValue (A.blocks K).pairingKept x
      - quadFormValue (A.blocks K).top x + bandEliminated D K (A.blocks K) x + rowsEliminated D K (A.blocks K) x
  band_weight_pos : ∀ K, ∀ ι ∈ D.mesh.band K, (∀ j : Fin 9, 0 < (A.blocks K).bandWeight ι (gradSlot j)) ∧
    ∀ b : Fin 3, 0 ≤ (A.blocks K).bandWeight ι ⟨9 + b.val, by omega⟩
  band_turn : ∀ K, ∀ ι ∈ D.mesh.band K, labelAzimuth D.azimuthOrder ι ≠ 0 ∧ labelAzimuth D.azimuthOrder ι ^ 2 ≠ 1
  band_slack : ∀ K, 0 ≤ (A.blocks K).bandSlack ∧ (A.blocks K).bandSlack < 1
  slack_zero : ∀ K, (A.blocks K).bandSlack = 0 → ∀ ι ∈ D.mesh.band K, ∀ (x : CellVars D R K → ℂ), S K x → ∀ p (j : Fin 9),
    turnedSource D (A.blocks K) ι x p j
      = ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
  fields_bounded : ∀ K, ∀ ι ∈ D.mesh.band K, ∀ j, (∀ d, IsBoundedOnCell D K (fun p => (A.blocks K).potentialSource ι d p j)) ∧
    (∀ d, IsBoundedOnCell D K (fun p => (A.blocks K).pairingSource ι d p j)) ∧
    (∀ d, IsBoundedOnCell D K (fun p => (A.blocks K).bandMap ι d p j)) ∧
    (∀ i, IsBoundedOnCell D K (fun p => (A.blocks K).rowBand i ι p j))
  row_weight_pos : ∀ K, (A.blocks K).rowWeight.PosDef
  row_full_dominates : ∀ K, ((A.blocks K).rowFull - (A.blocks K).rowWeight
    - ((1 - (A.blocks K).bandSlack)⁻¹ : ℂ) • bandGram D K (A.blocks K)).PosSemidef

structure TailConditions (A : AssemblyEntry D R) : Prop where
  cell_conditions : CellCalculusConditions D R
  budget_holds : ∀ K, ∀ ι ∈ D.mesh.resolved K, ((A.blocks K).budget ι).Holds (D.mesh.box K)
    ((R.layouts K).layout ι).degCoef (|labelAzimuth D.azimuthOrder ι| : ℝ)
  hess_floor : ∀ K, ∀ ι ∈ D.mesh.resolved K, ((A.blocks K).budget ι).hessFloor = (R.leaves K).hessFloor ι
  curl_floor : ∀ K, ∀ ι ∈ D.mesh.resolved K, ((A.blocks K).budget ι).curlGradFloor = (R.leaves K).curlHessFloor ι
  strain_cost : ∀ K, ∀ ι ∈ D.mesh.resolved K, totalStrainCost (A.blocks K) ι
    ≤ ((A.blocks K).budget ι).gradAbsorb + ((A.blocks K).budget ι).gradPotential + ((A.blocks K).budget ι).gradLeak + ((A.blocks K).budget ι).globalLeak
  curl_cost : ∀ K, ∀ ι ∈ D.mesh.resolved K, 0 ≤ (A.blocks K).potentialCurlCost ι ∧
    (A.blocks K).potentialCurlCost ι ≤ ((A.blocks K).budget ι).curlAbsorb
  vel_cost : ∀ K, ∀ ι ∈ D.mesh.resolved K, totalVelCost (A.blocks K) ι
    ≤ ((A.blocks K).budget ι).velAbsorb + ((A.blocks K).budget ι).velPotential + ((A.blocks K).budget ι).velLeak
  top_eq : ∀ K, (A.blocks K).top = ∑ ι ∈ D.mesh.resolved K,
    (((A.blocks K).budget ι).velCharge : ℂ) • (A.blocks K).topBlock ι

def topValue (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) : ℝ :=
  (radialEigen (D.mesh.box K) ((R.layouts K).layout ι.1).degCoef)⁻¹ *
      ∑ n : ((R.layouts K).layout ι.1).modes, ∑ a : Fin 3, ∑ j : Fin (((R.layouts K).layout ι.1).degCoef + 1),
        ∑ l : Fin (((R.layouts K).layout ι.1).degCoef + 1),
          (if ((R.layouts K).layout ι.1).degCoef ≤ j.val + 1 then
            ‖restrictData D R K ι x (CellDatum.lowStrain n a 0 j l)‖ ^ 2 else 0)
    + (heightEigen (D.mesh.box K) ((R.layouts K).layout ι.1).degCoef)⁻¹ *
      ∑ n : ((R.layouts K).layout ι.1).modes, ∑ a : Fin 3, ∑ j : Fin (((R.layouts K).layout ι.1).degCoef + 1),
        ∑ l : Fin (((R.layouts K).layout ι.1).degCoef + 1),
          (if j.val + 1 ≤ ((R.layouts K).layout ι.1).degCoef ∧ ((R.layouts K).layout ι.1).degCoef ≤ l.val + 1 then
            ‖restrictData D R K ι x (CellDatum.lowStrain n a 2 j l)‖ ^ 2 else 0)

end StageConditions

section Rows

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def testAt (K : Fin D.mesh.count) (ι : ℤ × ℤ) (j : ℕ) (c : Fin 3) (p : ℝ × ℝ) : ℂ :=
  (D.rows.testField K ι j c).eval (D.mesh.box K) p

def rowGram {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) : Matrix (Fin B.rowCount) (Fin B.rowCount) ℂ :=
  fun i i' => if B.rowLabel i = B.rowLabel i' then ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    testAt D K (B.rowLabel i) (B.rowTest i') c p * (starRingEnd ℂ) (testAt D K (B.rowLabel i) (B.rowTest i) c p) else 0

def scaledRowGram {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (c : ℤ × ℤ → ℝ) :
    Matrix (Fin B.rowCount) (Fin B.rowCount) ℂ :=
  fun i i' => rowGram D K B i i' / (c (B.rowLabel i) : ℂ)

def leakGram {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) : Matrix (Fin B.rowCount) (Fin B.rowCount) ℂ :=
  scaledRowGram D K B B.leakWeight

def rowBaseWeight {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) : Matrix (Fin B.rowCount) (Fin B.rowCount) ℂ :=
  fun i i' => rowGram D K B i i' / (D.rows.testWeight K (B.rowLabel i) : ℂ)

def tailGramPart {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (strain : Bool) (ι : ℤ × ℤ) :
    Matrix (Fin B.rowCount) (Fin B.rowCount) ℂ :=
  fun i i' => ∫ p in (D.mesh.box K).rect, ((D.mesh.box K).lineWeight p.1 : ℂ) *
    ∑ j : Fin 12, if decide (j.val < 9) = strain then
      (starRingEnd ℂ) (B.rowTailTest i ι p j) * B.rowTailTest i' ι p j else 0

structure RowConditions (A : AssemblyEntry D R) : Prop where
  mesh_valid : IsCellMesh D.mesh
  label_tested : ∀ K i, (A.blocks K).rowLabel i ∈ D.mesh.tested K
  test_range : ∀ K i, (A.blocks K).rowTest i < D.rows.testCount K ((A.blocks K).rowLabel i)
  rows_injective : ∀ K i i', (A.blocks K).rowLabel i = (A.blocks K).rowLabel i' →
    (A.blocks K).rowTest i = (A.blocks K).rowTest i' → i = i'
  rows_onto : ∀ K, ∀ ι ∈ D.mesh.tested K, ∀ j < D.rows.testCount K ι,
    ∃ i, (A.blocks K).rowLabel i = ι ∧ (A.blocks K).rowTest i = j
  leak_weight_pos : ∀ K, ∀ ι ∈ D.mesh.tested K, 0 < (A.blocks K).leakWeight ι
  gram_pos : ∀ K, (rowGram D K (A.blocks K)).PosDef
  kappa_cost_nonneg : ∀ K, 0 ≤ (A.blocks K).rowKappaCost
  kappa_cell : ∀ K, (A.blocks K).rowKappaCost ≤ R.kappaCost K
  costs_pos : ∀ K, ∀ ι ∈ D.mesh.resolved K, 0 < (A.blocks K).rowStrainCost ι ∧ 0 < (A.blocks K).rowVelCost ι
  weight_dominates : ∀ K, ((A.blocks K).rowWeight - rowBaseWeight D K (A.blocks K)
    - ∑ ι ∈ D.mesh.resolved K, (((A.blocks K).rowStrainCost ι)⁻¹ : ℂ) • tailGramPart D K (A.blocks K) true ι
    - ∑ ι ∈ D.mesh.resolved K, (((A.blocks K).rowVelCost ι)⁻¹ : ℂ) • tailGramPart D K (A.blocks K) false ι
    - leakGram D K (A.blocks K)).PosSemidef
  tail_test_bounded : ∀ K i, ∀ ι ∈ D.mesh.resolved K, ∀ j,
    IsBoundedOnCell D K (fun p => (A.blocks K).rowTailTest i ι p j)

end Rows

section Credits

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

end Credits

section PotentialPairing

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def lowGrad (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (p : ℝ × ℝ) :
    Fin 3 → Fin 3 → ℂ :=
  fun a b => ∑ n : ((R.layouts K).layout ι.1).modes,
    lowStrainOf ((R.layouts K).layout ι.1) (restrictData D R K ι x) n a b p

def lowVel (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => ∑ n : ((R.layouts K).layout ι.1).modes,
    lowVelocityOf ((R.layouts K).layout ι.1) (restrictData D R K ι x) n a p

def lowProfile (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (p : ℝ × ℝ) : Fin 12 → ℂ :=
  pairVec (lowGrad D R K ι x p) (lowVel D R K ι x p)

def sesq12 (M : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (U i) * M i j * U' j

def modelBilin (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : ℂ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * S i j * curlOfGrad g' j)
    + ∑ j : Fin 3, (∑ l : Fin 3, a l * Gω j l) * curlOfGrad g' j
    + (1 / 2 : ℂ) * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * Gω j l * g (i, j) * a' n

def modelTriple (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : ℂ :=
  (modelBilin S Gω a g a' g' + modelBilin S Gω a' g' a g) / 2

def velOf (U : Fin 12 → ℂ) : Fin 3 → ℂ := fun a => U ⟨9 + a.val, by omega⟩

def gradOf (U : Fin 12 → ℂ) : Fin 3 × Fin 3 → ℂ := fun ab => U ⟨3 * ab.1.val + ab.2.val, by omega⟩

def pairArray (s : Fin 3 → Fin 3 → ℂ) : Fin 3 × Fin 3 → ℂ := fun ab => s ab.1 ab.2

def splitCharge (σc cs cv : ℝ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  σc * cnormSq (curlOfGrad g) + cs * cnormSq g + cv * cnormSq a

structure PotentialData (V : Type) where
  couplingModel : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ
  bandProjection : Matrix V V ℂ
  portForm : Matrix V V ℂ
  groupCount : ℕ
  groupModes : Fin groupCount → Finset (ℤ × ℤ)
  groupStrain : Fin groupCount → ℝ
  groupGrad : Fin groupCount → ℝ
  groupBalance : Fin groupCount → ℝ
  groupWave : Fin groupCount → Bridge.CrossWaveEntry
  groupPartners : Fin groupCount → Finset (ℤ × ℤ)
  rowPartners : Fin groupCount → Finset (ℤ × ℤ)
  groupVel : Fin groupCount → ℝ
  groupHarmonics : Fin groupCount → Finset (ℤ × ℤ)
  groupKappa : Fin groupCount → ℝ
  groupShift : Fin groupCount → ℤ
  groupCurl : Fin groupCount → ℝ
  length : ℝ
  epsLength : ℝ
  epsStrain : ℝ
  epsGrad : ℝ
  strainBalance : ℤ × ℤ → ℝ
  velBalance : ℤ × ℤ → ℝ
  harmonicLabels : Finset (ℤ × ℤ)
  highStrain : ℝ
  highGrad : ℝ
  youngCurl : ℝ
  youngStrain : ℝ
  youngVel : ℝ
  longStrain : ℝ
  longGrad : ℝ
  longBalance : ℝ
  longCut : ℕ

structure PairingData (k : ℕ) where
  gammaModes : Finset (ℤ × ℤ)
  gammaWeight : ℤ × ℤ → ℝ
  gammaGram : ℤ × ℤ → Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ

structure CouplingEntries (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) where
  potential : (K : Fin D.mesh.count) → PotentialData (CellVars D R K)
  pairing : Fin D.mesh.count → PairingData k

def isPressureDatum (L : CellLayout) : L.Datum → Bool
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => true
  | _ => false

def upperPart (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) :
    CellVars D R K → ℂ :=
  x - P.bandProjection *ᵥ x

def bandPart (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) :
    CellVars D R K → ℂ :=
  P.bandProjection *ᵥ x

def epsOwnCharge {V : Type} (P : PotentialData V) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  splitCharge (2 * P.epsStrain) (3 / (2 * Real.sqrt 2) * P.epsGrad * (P.epsLength + P.length))
    (2 * (3 / (2 * Real.sqrt 2)) * P.epsGrad / P.epsLength) a g

open Classical in
def longFactor {V : Type} (P : PotentialData V) (ι : ℤ × ℤ) : ℝ :=
  if |ι.1| ≤ (P.longCut : ℤ) then P.longBalance else 1 + 1 / P.longBalance

def longOwnCharge {V : Type} (P : PotentialData V) (ι : ℤ × ℤ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  longFactor P ι * splitCharge (2 * P.longStrain) (3 / (2 * Real.sqrt 2) * P.longGrad * (P.epsLength + P.length))
    (2 * (3 / (2 * Real.sqrt 2)) * P.longGrad / P.epsLength) a g

def groupCharge {V : Type} (P : PotentialData V) (i : Fin P.groupCount) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  splitCharge (P.groupStrain i) (P.groupKappa i / 2 * P.groupGrad i * P.length)
    (P.groupKappa i / 2 * P.groupGrad i / P.length) a g

def couplingPair (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x y : CellVars D R K → ℂ) : ℝ :=
  ∑ ι : D.mesh.resolved K, ∑ ι' : D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
    p.1 * (sesq12 (P.couplingModel (ι.1 - ι'.1) p) (lowProfile D R K ι x p) (lowProfile D R K ι' y p)).re

def absorbValue (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (p : ℝ × ℝ) : ℝ :=
  (R.leaves K).curlAbsorb ι.1 * curlSq (lowGrad D R K ι x p) + (R.leaves K).strainAbsorb ι.1 * sumSq (lowGrad D R K ι x p)
    + (R.leaves K).velocityAbsorb ι.1 * vecSq (lowVel D R K ι x p)

def potentialExact (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) : ℝ :=
  couplingPair D R K P (upperPart D R K P x) (upperPart D R K P x)
    + 2 * couplingPair D R K P (upperPart D R K P x) (bandPart D R K P x)
    - ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        p.1 * sesqValue ((R.leaves K).localMatrix ι.1 p) (lowProfile D R K ι (bandPart D R K P x) p))
    - ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        (D.mesh.box K).lineWeight p.1 * absorbValue D R K ι (bandPart D R K P x) p)
    - quadFormValue P.portForm x
    - ∑ i, P.groupBalance i * ∑ ι : D.mesh.resolved K, (if ι.1 ∈ P.groupModes i then ∫ p in (D.mesh.box K).rect,
        p.1 * groupCharge P i
          (lowVel D R K ι (upperPart D R K P x) p) (pairArray (lowGrad D R K ι (upperPart D R K P x) p)) else 0)
    - ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        p.1 * epsOwnCharge P
          (lowVel D R K ι (upperPart D R K P x) p) (pairArray (lowGrad D R K ι (upperPart D R K P x) p)))
    - ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        p.1 * longOwnCharge P ι.1
          (lowVel D R K ι (upperPart D R K P x) p) (pairArray (lowGrad D R K ι (upperPart D R K P x) p)))

def strainOfVec (U : Fin 12 → ℂ) : Fin 3 → Fin 3 → ℂ := fun a b => gradOf U (a, b)

def lowAt (K : Fin D.mesh.count) (x : CellVars D R K → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : Fin 12 → ℂ :=
  if h : ι ∈ D.mesh.resolved K then lowProfile D R K ⟨ι, h⟩ x p else 0

def upperProfiles (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) :
    ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ :=
  lowAt D R K (upperPart D R K P x)

def highOwnCharge {V : Type} (P : PotentialData V) (U : Fin 12 → ℂ) : ℝ :=
  P.youngCurl * P.highStrain * curlSq (strainOfVec U)
    + 3 / (2 * Real.sqrt 2) * P.highGrad * (P.youngStrain * sumSq (strainOfVec U) + P.youngVel * vecSq (velOf U))

def highOwnAmount {V : Type} (K : Fin D.mesh.count) (P : PotentialData V) (S : Finset (ℤ × ℤ))
    (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ S, ∫ p in (D.mesh.box K).rect, p.1 * highOwnCharge P (X ι p)

def couplingTailFull (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (ι : D.mesh.resolved K) (strain : Bool) : ℝ :=
  ∑ j : Fin 12, if decide (j.val < 9) = strain then
    (D.mesh.box K).tailNormSq (if strain then ((R.layouts K).layout ι.1).degCoef else ((R.layouts K).layout ι.1).degCoef - 1)
      (fun p => ((CellScalars.rHat (D.mesh.box K) p : ℝ) : ℂ) *
        ((∑ ι' : D.mesh.resolved K, ∑ j', P.couplingModel (ι.1 - ι'.1) p j j' * lowProfile D R K ι' (upperPart D R K P x) p j')
          + ∑ j', (R.leaves K).localMatrix ι.1 p j j' * lowProfile D R K ι (upperPart D R K P x) p j')) else 0

def rHatMax (K : Fin D.mesh.count) : ℝ :=
  (D.mesh.box K).r₂ / (D.mesh.box K).lineWeight (D.mesh.box K).r₂

open Classical in
def modelLabels (K : Fin D.mesh.count) : Finset (ℤ × ℤ) :=
  (D.model.velocity.labels K ∪ D.model.vorticity.labels K ∪ D.model.strain.labels K ∪
      D.model.vorticityGrad.labels K).filter fun α =>
    ∃ p ∈ (D.mesh.box K).rect,
      (∃ a, D.model.velocity.planeValue D.mesh.box K α a p ≠ 0) ∨
      (∃ a, D.model.vorticity.planeValue D.mesh.box K α a p ≠ 0) ∨
      (∃ a b, D.model.strain.planeValue D.mesh.box K α a b p ≠ 0) ∨
      (∃ a b, D.model.vorticityGrad.planeValue D.mesh.box K α a b p ≠ 0)

structure PotentialConditions (A : AssemblyEntry D R) (P : CouplingEntries D R) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop where
  mesh_valid : IsCellMesh D.mesh
  cell_conditions : CellCalculusConditions D R
  kept_le : ∀ K (x : CellVars D R K → ℂ), S K x → quadFormValue (A.blocks K).potentialKept x
    ≤ potentialExact D R K (P.potential K) x
      - highOwnAmount D K (P.potential K) (D.mesh.resolved K) (upperProfiles D R K (P.potential K) x)
  port_dominates : ∀ K (x : CellVars D R K → ℂ), S K x →
    ∑ ι : D.mesh.resolved K, (couplingTailFull D R K (P.potential K) x ι true / (P.potential K).strainBalance ι.1
      + couplingTailFull D R K (P.potential K) x ι false / (P.potential K).velBalance ι.1)
      ≤ quadFormValue (P.potential K).portForm x
  balance_pos : ∀ K, ∀ ι ∈ D.mesh.resolved K, 0 < (P.potential K).strainBalance ι ∧ 0 < (P.potential K).velBalance ι
  group_pos : ∀ K i, 0 < (P.potential K).groupBalance i ∧ 0 ≤ (P.potential K).groupStrain i ∧
    0 ≤ (P.potential K).groupGrad i
  length_pos : ∀ K, 0 < (P.potential K).length
  eps_length_pos : ∀ K, 0 < (P.potential K).epsLength
  group_kappa : ∀ K i, (P.potential K).groupKappa i = Real.sqrt (7 / 2) ∨ (P.potential K).groupKappa i = Real.sqrt (9 / 2)
  eps_nonneg : ∀ K, 0 ≤ (P.potential K).epsStrain ∧ 0 ≤ (P.potential K).epsGrad
  strain_cost : ∀ K, ∀ ι ∈ D.mesh.resolved K,
    (R.leaves K).strainAbsorb ι + (P.potential K).strainBalance ι
        + rHatMax D K * (2 * (P.potential K).highStrain / (P.potential K).youngCurl
          + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel)
      ≤ (A.blocks K).potentialStrainCost ι
  vel_cost : ∀ K, ∀ ι ∈ D.mesh.resolved K,
    (R.leaves K).velocityAbsorb ι + (P.potential K).velBalance ι
        + rHatMax D K * (3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain)
      ≤ (A.blocks K).potentialVelCost ι
  labels_iff : ∀ K α, α ∈ (P.potential K).harmonicLabels ↔ labelHarmonic D.azimuthOrder α ∈ D.givenLabels
  source_eq : ∀ K, ∀ ι' ∈ D.mesh.band K, ∀ (x : CellVars D R K → ℂ), S K x → ∀ p j,
    linearField ((A.blocks K).potentialSource ι') x p j
      = ∑ ι : D.mesh.resolved K, ∑ j', (P.potential K).couplingModel (ι' - ι.1) p j j'
          * lowProfile D R K ι (upperPart D R K (P.potential K) x) p j'
  source_bounded : ∀ K, ∀ ι ∈ D.mesh.band K, ∀ d j,
    IsBoundedOnCell D K (fun p => (A.blocks K).potentialSource ι d p j)
  high_ge : ∀ K, (D.modelErrors K).strainHigh ≤ (P.potential K).highStrain ∧
    (D.modelErrors K).vorticityGradHigh ≤ (P.potential K).highGrad
  young_pos : ∀ K, 0 < (P.potential K).youngCurl ∧ 0 < (P.potential K).youngStrain ∧ 0 < (P.potential K).youngVel
  band_charges : ∀ K, ∀ ι ∈ D.mesh.band K, ∀ p ∈ (D.mesh.box K).rect,
    (P.potential K).epsStrain + longFactor (P.potential K) ι * (P.potential K).longStrain
        + (P.potential K).highStrain / (P.potential K).youngCurl + (A.blocks K).bandCurlAllowance ι
      ≤ (R.entryCharges K ι).curlCharge p ∧
    (⨆ j : Fin 9, (A.blocks K).bandWeight ι ⟨j.val, by omega⟩)
        + 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          * (P.potential K).epsLength + (P.potential K).highGrad / (P.potential K).youngVel)
        + (if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0)
      ≤ (R.entryCharges K ι).gradCharge p ∧
    (⨆ j : Fin 3, (A.blocks K).bandWeight ι ⟨9 + j.val, by omega⟩)
        + 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          / (P.potential K).length + (P.potential K).highGrad / (P.potential K).youngStrain) + (A.blocks K).bandVelAllowance ι
      ≤ (R.entryCharges K ι).velCharge p
  leak_not_band : ∀ K, Disjoint (A.blocks K).leakModes (D.mesh.band K)
  partners_not_band : ∀ K i, Disjoint ((P.potential K).groupPartners i) (D.mesh.band K)
  partners_unresolved : ∀ K i, Disjoint ((P.potential K).groupPartners i) (D.mesh.resolved K)
  group_link : ∀ K, ∀ ι ∈ D.mesh.resolved K, ∀ α ∈ modelLabels D K, ι - α ∉ D.mesh.resolved K →
    ι - α ∉ D.mesh.band K → ∃ i, ι ∈ (P.potential K).groupModes i ∧ ι - α ∈ (P.potential K).groupPartners i ∧
      -α ∈ (P.potential K).groupHarmonics i
  group_in_labels : ∀ K i, ∀ β ∈ (P.potential K).groupHarmonics i, -β ∈ (P.potential K).harmonicLabels
  group_disjoint : ∀ K i j β, β ∈ (P.potential K).groupHarmonics i → β ∈ (P.potential K).groupHarmonics j → i = j
  model_harmonics : Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess
  model_state : ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B
  azimuth_pos : 1 ≤ D.azimuthOrder
  charges_regular : EntryChargesRegular D R
  regular : AssemblyRegular D R
  hessian_symmetric : ∀ σ y u w, D.givenHess σ y u w = D.givenHess σ y w u
  eps_box : ∀ K, ∀ ι ∈ D.mesh.resolved K,
    (P.potential K).epsStrain + longFactor (P.potential K) ι * (P.potential K).longStrain ≤ (R.leaves K).boxPairCurl ι ∧
    3 / (2 * Real.sqrt 2) * ((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
        * (P.potential K).epsLength ≤ (R.leaves K).boxPairStrain ι ∧
    3 / (2 * Real.sqrt 2) * ((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
        / (P.potential K).length ≤ (R.leaves K).boxPairVelocity ι
  long_ge : ∀ K, (R.long K).errStrain ≤ (P.potential K).longStrain ∧
    (R.long K).errVorticityGrad ≤ (P.potential K).longGrad
  long_cut : ∀ K, (P.potential K).longCut ≤ (R.long K).cut
  long_pos : ∀ K, 0 ≤ (P.potential K).longStrain ∧ 0 ≤ (P.potential K).longGrad ∧ 0 < (P.potential K).longBalance
  model_off_labels : ∀ K α, α ∉ (P.potential K).harmonicLabels → ∀ p ∈ (D.mesh.box K).rect,
    (P.potential K).couplingModel α p = 0
  strain_off_labels : ∀ K α, α ∉ D.model.strain.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
    D.model.strain.planeValue D.mesh.box K α a b p = 0
  vorticity_grad_off_labels : ∀ K α, α ∉ D.model.vorticityGrad.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
    D.model.vorticityGrad.planeValue D.mesh.box K α a b p = 0
  velocity_off_labels : ∀ K α, α ∉ D.model.velocity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
    D.model.velocity.planeValue D.mesh.box K α a p = 0
  vorticity_off_labels : ∀ K α, α ∉ D.model.vorticity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
    D.model.vorticity.planeValue D.mesh.box K α a p = 0
  allowance_nonneg : ∀ K, ∀ ι ∈ D.mesh.band K, 0 ≤ (A.blocks K).bandCurlAllowance ι ∧ 0 ≤ (A.blocks K).bandVelAllowance ι
  curl_cost : ∀ K, ∀ ι ∈ D.mesh.resolved K, (R.leaves K).curlAbsorb ι ≤ (A.blocks K).potentialCurlCost ι
  leak_unresolved : ∀ K, ∀ ι ∈ (A.blocks K).leakModes, ι ∉ D.mesh.resolved K
  charges_all : ∀ K, IsRegionChargeBound D.azimuthOrder (D.mesh.box K).rect D.given D.givenHess (D.charges (some K))
  stretch_const : ∀ K ι, ι ∉ D.mesh.resolved K → Real.sqrt (7 / 2) ≤ (R.entryCharges K ι).stretchConst
  projection_block : ∀ K (i j : CellVars D R K), (P.potential K).bandProjection i j ≠ 0 →
    ∃ d d' : CellVar D.mesh K (R.layouts K), i = Sum.inl (Sum.inl d) ∧ j = Sum.inl (Sum.inl d') ∧ d.1 = d'.1 ∧
      isPressureDatum ((R.layouts K).layout d.1.1) d.2 = false ∧ isPressureDatum ((R.layouts K).layout d'.1.1) d'.2 = false
  coupling_model : ∀ K α, ∀ p ∈ (D.mesh.box K).rect, ∀ U U' : Fin 12 → ℂ,
    sesq12 ((P.potential K).couplingModel α p) U U'
      = modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K α a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K α a b p)
          (velOf U') (gradOf U') (star (velOf U)) (star (gradOf U))
  eps_ge : ∀ K, (D.modelErrors K).strain ≤ (P.potential K).epsStrain ∧
    (D.modelErrors K).vorticityGrad ≤ (P.potential K).epsGrad
  group_wave : ∀ K i, Bridge.IsCrossWaveEntry ((P.potential K).groupWave i) ∧
    ((P.potential K).groupWave i).azimuthOrder = D.azimuthOrder ∧
    ((P.potential K).groupWave i).region = (D.mesh.box K).rect ∧
    ((P.potential K).groupWave i).strainBound = (P.potential K).groupStrain i ∧
    ((P.potential K).groupWave i).vorticityGradBound = (P.potential K).groupGrad i ∧
    ((P.potential K).groupWave i).balance = (P.potential K).groupBalance i ∧
    ((P.potential K).groupWave i).length = (P.potential K).length ∧
    (P.potential K).groupHarmonics i
      = ((P.potential K).groupWave i).waveModes.image (fun n => (n, (P.potential K).groupShift i)) ∧
    (∀ n p a b, ((P.potential K).groupWave i).strainMode n p (a, b)
      = D.model.strain.planeValue D.mesh.box K (n, (P.potential K).groupShift i) a b p) ∧
    (∀ n p a b, curlGradOfSecondDeriv (((P.potential K).groupWave i).vorticityGradMode n p) (a, b)
      = D.model.vorticityGrad.planeValue D.mesh.box K (n, (P.potential K).groupShift i) a b p) ∧
    ((P.potential K).groupKappa i = Real.sqrt (7 / 2) → ∀ p θ, ∑ j : Fin 3, ∑ n ∈ ((P.potential K).groupWave i).waveModes,
      Bridge.azimuthPhase D.azimuthOrder n θ * curlGradOfSecondDeriv (((P.potential K).groupWave i).vorticityGradMode n p) (j, j) = 0)
  credit_patches : ∀ j, Bridge.IsCreditPatch (R.creditPatch j)
  credit_lattice : ∀ j, IsLatticeHarmonic D.azimuthOrder (flipLabel (R.creditPatch j).label)
  credit_label_ne : ∀ j, (R.creditPatch j).label ≠ 0
  credit_deactivated : ∀ j K ι, (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
      labelHarmonic D.azimuthOrder ι = -(flipLabel (R.creditPatch j).label)) →
    ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K
  model_labels_in : ∀ K α, α ∉ (P.potential K).harmonicLabels → ∀ p ∈ (D.mesh.box K).rect,
    (∀ a, D.model.velocity.planeValue D.mesh.box K α a p = 0) ∧ (∀ a, D.model.vorticity.planeValue D.mesh.box K α a p = 0)
  long_labels_in : ∀ K α, α ∉ (P.potential K).harmonicLabels → ∀ p ∈ (D.mesh.box K).rect,
    (∀ a, labelVel D.azimuthOrder α (R.long K).velocity p a = 0) ∧
    (∀ a, labelVel D.azimuthOrder α (R.long K).vorticity p a = 0) ∧
    (∀ a b, labelGrad D.azimuthOrder α (R.long K).strain p (a, b) = 0) ∧
    (∀ a b, labelGrad D.azimuthOrder α (R.long K).vorticityGrad p (a, b) = 0)
  model_strain_symmetric : ∀ K α a b, ∀ p ∈ (D.mesh.box K).rect,
    D.model.strain.planeValue D.mesh.box K α a b p = D.model.strain.planeValue D.mesh.box K α b a p
  groups_cover : ∀ K, ∀ ι ∈ D.mesh.resolved K, ∀ ι', ι' ∉ D.mesh.resolved K → ι' ∉ D.mesh.band K →
    ι - ι' ∈ modelLabels D K → ∃ i, ι ∈ (P.potential K).groupModes i ∧ ι' ∈ (P.potential K).groupPartners i
  charges_cover : ∀ K ι, ι ∉ D.mesh.resolved K → ι ∉ D.mesh.band K → ∀ p ∈ (D.mesh.box K).rect,
    (∑ i, if ι ∈ (P.potential K).groupPartners i then
        (P.potential K).groupStrain i / (P.potential K).groupBalance i else 0)
      + (if ι ∈ (A.blocks K).leakModes then (A.blocks K).leakCurl ι else 0)
      + (if ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ (P.potential K).harmonicLabels then (P.potential K).epsStrain + longFactor (P.potential K) ι * (P.potential K).longStrain
        + (P.potential K).highStrain / (P.potential K).youngCurl else 0)
      ≤ (R.entryCharges K ι).curlCharge p ∧
    (∑ i, if ι ∈ (P.potential K).groupPartners i then (P.potential K).groupKappa i / 2 * (P.potential K).length
        * (P.potential K).groupGrad i / (P.potential K).groupBalance i else 0)
      + (if ι ∈ (A.blocks K).leakModes then (A.blocks K).leakStrain ι else 0)
      + (if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0)
      + (if ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ (P.potential K).harmonicLabels then 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          * (P.potential K).epsLength + (P.potential K).highGrad / (P.potential K).youngVel) else 0)
      ≤ (R.entryCharges K ι).gradCharge p ∧
    (∑ i, if ι ∈ (P.potential K).groupPartners i then (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
        / ((P.potential K).length * (P.potential K).groupBalance i) else 0)
      + (if ι ∈ (A.blocks K).leakModes then (A.blocks K).leakVel ι else 0)
      + (if ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ (P.potential K).harmonicLabels then 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          / (P.potential K).length + (P.potential K).highGrad / (P.potential K).youngStrain) else 0)
      + creditVelDemand D R K ι p
      ≤ (R.entryCharges K ι).velCharge p

def pairWeightOf {V : Type} (x : V ⊕ (Fin k ⊕ Fin k) → ℂ) : Fin k ⊕ Fin k → ℂ
  | .inl i => x (Sum.inr (Sum.inl i))
  | .inr i => 2 * x (Sum.inr (Sum.inr i))

def pairingProfile (K : Fin D.mesh.count) (w : Fin k ⊕ Fin k → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => ∑ g, w g * R.pairProfile K g ι p a b

def pairingExact (K : Fin D.mesh.count) (Q : PairingData k) (x : CellVars D R K → ℂ) : ℝ :=
  ∑ ι : D.mesh.resolved K, (if ι.1 ∈ R.pairLabels then ∫ p in (D.mesh.box K).rect, p.1 *
      (∑ a : Fin 3, ∑ b : Fin 3, lowGrad D R K ι x p a b
        * (starRingEnd ℂ) (pairingProfile D R K (pairWeightOf x) ι.1 p a b)).re else 0)
    - ∑ ι ∈ Q.gammaModes, Coupling.quadForm (Q.gammaGram ι) (pairWeightOf x) / (4 * Q.gammaWeight ι)

structure PairingConditions (A : AssemblyEntry D R) (Q : Fin D.mesh.count → PairingData k) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop where
  mesh_valid : IsCellMesh D.mesh
  cell_conditions : CellCalculusConditions D R
  kept_le : ∀ K (x : CellVars D R K → ℂ), S K x → quadFormValue (A.blocks K).pairingKept x ≤ pairingExact D R K (Q K) x
  source_eq : ∀ K, ∀ ι ∈ D.mesh.band K, ∀ (x : CellVars D R K → ℂ), S K x → ∀ p, ι ∈ R.pairLabels →
    linearField ((A.blocks K).pairingSource ι) x p
      = pairVec (fun a b => (1 / 2 : ℂ) * pairingProfile D R K (pairWeightOf x) ι p a b) 0
  source_zero : ∀ K, ∀ ι ∈ D.mesh.band K, ι ∉ R.pairLabels → ∀ (x : CellVars D R K → ℂ), S K x → ∀ p,
    linearField ((A.blocks K).pairingSource ι) x p = 0
  gamma_resolved : ∀ K, ∀ ι ∈ D.mesh.resolved K, ι ∈ R.pairLabels →
    (∃ g a b, ¬ (fun p => R.pairProfile K g ι p a b) =ᵐ[volume.restrict (D.mesh.box K).rect] 0) → ι ∈ (Q K).gammaModes ∧
    0 < (Q K).gammaWeight ι ∧ (Q K).gammaWeight ι ≤ (A.blocks K).pairingStrainCost ι ∧
    ∀ w : Fin k ⊕ Fin k → ℝ, ∑ a : Fin 3, ∑ b : Fin 3, (D.mesh.box K).tailNormSq ((R.layouts K).layout ι).degCoef
        (fun p => ((CellScalars.rHat (D.mesh.box K) p : ℝ) : ℂ) * pairingProfile D R K (fun g => (w g : ℂ)) ι p a b)
      ≤ Coupling.quadForm ((Q K).gammaGram ι) (fun g => (w g : ℂ))
  gamma_other : ∀ K ι, ι ∈ R.pairLabels → ι ∉ D.mesh.resolved K → ι ∉ D.mesh.band K →
    (∃ g a b, ¬ (fun p => R.pairProfile K g ι p a b) =ᵐ[volume.restrict (D.mesh.box K).rect] 0) →
    ι ∈ (Q K).gammaModes ∧ ι ∈ (A.blocks K).leakModes ∧ 0 < (Q K).gammaWeight ι ∧
    (Q K).gammaWeight ι ≤ (A.blocks K).leakStrain ι ∧
    ∀ w : Fin k ⊕ Fin k → ℝ, ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3,
        ‖pairingProfile D R K (fun g => (w g : ℂ)) ι p a b‖ ^ 2 ≤ Coupling.quadForm ((Q K).gammaGram ι) (fun g => (w g : ℂ))
  gamma_gram : ∀ K, ∀ ι ∈ (Q K).gammaModes, 0 < (Q K).gammaWeight ι ∧
    ∀ w : Fin k ⊕ Fin k → ℝ, 0 ≤ Coupling.quadForm ((Q K).gammaGram ι) (fun g => (w g : ℂ))
  leak_nonneg : ∀ K ι, 0 ≤ (A.blocks K).leakStrain ι
  cost_nonneg : ∀ K ι, 0 ≤ (A.blocks K).pairingStrainCost ι

end PotentialPairing

section RowFunctionals

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def rowTestPoly {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) : Fin 3 → CellPoly :=
  fun c => D.rows.testField K (B.rowLabel i) (B.rowTest i) c

def modelVelocity (K : Fin D.mesh.count) (α : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => D.model.velocity.planeValue D.mesh.box K α a p

def modelVorticity (K : Fin D.mesh.count) (α : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => D.model.vorticity.planeValue D.mesh.box K α a p

def crossTest (Wα Ωα φ : Fin 3 → ℂ) : Fin 12 → ℂ :=
  pairVec (fun a b => (starRingEnd ℂ) (∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
      ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) * Wα j * (starRingEnd ℂ) (φ l)))
    (fun a => (starRingEnd ℂ) (∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) * (starRingEnd ℂ) (φ j) * Ωα l))

def rowCrossTest {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (ι' : ℤ × ℤ)
    (p : ℝ × ℝ) : Fin 12 → ℂ :=
  crossTest (modelVelocity D K (B.rowLabel i - ι') p) (modelVorticity D K (B.rowLabel i - ι') p)
    (fun c => (rowTestPoly D K B i c).eval (D.mesh.box K) p)

def actuatorRow (K : Fin D.mesh.count) (ι : ℤ × ℤ) (φ : Fin 3 → CellPoly) (b : ℝ → Space → Space) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    labelVel D.azimuthOrder ι b p c * (starRingEnd ℂ) ((φ c).eval (D.mesh.box K) p)

def deactSources {W : Type} (K : Fin D.mesh.count) (P : PotentialData W) : Finset (ℤ × ℤ) :=
  ((D.mesh.tested K ×ˢ P.harmonicLabels).image (fun x => x.1 - x.2)).filter
    (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K)

def activeGroups {V : Type} (P : PotentialData V) (ℓ : ℤ × ℤ) : Finset (Fin P.groupCount) :=
  Finset.univ.filter (fun j => ∃ ι' ∈ P.rowPartners j, ℓ - ι' ∈ P.groupHarmonics j)

open Classical in
def longRowCost {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (ι : ℤ × ℤ) : ℝ :=
  if (R.long K).IsLowLabel ι then B.longLowCost else B.longHighCost

open Classical in
def longSourceCost {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (ι : ℤ × ℤ) : ℝ :=
  if (R.long K).IsLowLabel ι then B.longHighCost else B.longLowCost + B.longHighCost

open Classical in
def longRowTerm {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (ι : ℤ × ℤ) : ℝ :=
  if (R.long K).errVelocity = 0 ∧ (R.long K).errVorticity = 0 then 0 else 1 / longRowCost D R K B ι

structure RowFunctionalConditions (A : AssemblyEntry D R) (P : CouplingEntries D R) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop where
  cell_conditions : CellCalculusConditions D R
  row_map : ∀ K i (x : CellVars D R K → ℂ), S K x → ((A.blocks K).rowMap *ᵥ x) i
    = (∑ ι : D.mesh.resolved K, if ι.1 = (A.blocks K).rowLabel i then
          ∑ d, ownRowVector ((R.layouts K).layout ι.1) (labelAzimuth D.azimuthOrder ι.1 : ℝ)
            (2 * Real.pi * (labelTime ι.1 : ℝ) * D.model.periodInverse) (rowTestPoly D K (A.blocks K) i) d
            * restrictData D R K ι x d
        else 0)
      + ∑ ι' : D.mesh.resolved K, ∑ d, couplingRowVector ((R.layouts K).layout ι'.1)
          (modelVelocity D K ((A.blocks K).rowLabel i - ι'.1)) (modelVorticity D K ((A.blocks K).rowLabel i - ι'.1))
          (rowTestPoly D K (A.blocks K) i) d * restrictData D R K ι' x d
      + ∑ l, x (Sum.inr (Sum.inl l)) * actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i)
          ((A.blocks K).actuatorModel (l : ℕ))
  row_band : ∀ K i, ∀ ι' ∈ D.mesh.band K, ∀ p ∈ (D.mesh.box K).rect,
    (A.blocks K).rowBand i ι' p = rowCrossTest D K (A.blocks K) i ι' p
  row_tail : ∀ K i, ∀ ι' ∈ D.mesh.resolved K, ∀ p ∈ (D.mesh.box K).rect, ∀ j : Fin 12,
    (A.blocks K).rowTailTest i ι' p j
      = ((CellScalars.rHat (D.mesh.box K) p : ℝ) : ℂ) * rowCrossTest D K (A.blocks K) i ι' p j
        - (D.mesh.box K).proj (if j.val < 9 then ((R.layouts K).layout ι').degCoef
              else ((R.layouts K).layout ι').degCoef - 1)
            (if j.val < 9 then ((R.layouts K).layout ι').degCoef else ((R.layouts K).layout ι').degCoef - 1)
            (fun p' => ((CellScalars.rHat (D.mesh.box K) p' : ℝ) : ℂ) * rowCrossTest D K (A.blocks K) i ι' p' j) p
  partners_leak : ∀ K g, (P.potential K).rowPartners g ⊆ (A.blocks K).leakModes
  leak_curl : ∀ K ι, ι ∈ (A.blocks K).leakModes →
    2 * (A.blocks K).deactCost *
        ∑ g, (if ι ∈ (P.potential K).rowPartners g then (P.potential K).groupVel g ^ 2 else 0)
      + (if ∃ ι₀ ∈ D.mesh.tested K, ι₀ - ι ∈ (P.potential K).harmonicLabels then 2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
        + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVelocity ^ 2 else 0)
      ≤ (A.blocks K).leakCurl ι
  leak_vel : ∀ K ι, ι ∈ (A.blocks K).leakModes →
    2 * (A.blocks K).deactCost *
        ∑ g, (if ι ∈ (P.potential K).rowPartners g then (P.potential K).groupCurl g ^ 2 else 0)
      + (if ∃ ι₀ ∈ D.mesh.tested K, ι₀ - ι ∈ (P.potential K).harmonicLabels then 2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
        + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVorticity ^ 2 else 0)
      ≤ (A.blocks K).leakVel ι
  tests_valid : ∀ K i,
    IsTestSolenoidal (D.mesh.box K) (labelAzimuth D.azimuthOrder ((A.blocks K).rowLabel i) : ℝ) (rowTestPoly D K (A.blocks K) i) ∧
    IsAxisRegularTest (D.mesh.box K) (labelAzimuth D.azimuthOrder ((A.blocks K).rowLabel i) : ℝ) (rowTestPoly D K (A.blocks K) i) ∧
    IsTestOfShape (D.mesh.box K) ((R.layouts K).layout ((A.blocks K).rowLabel i)).degSide (rowTestPoly D K (A.blocks K) i) ∧
    ((R.layouts K).layout ((A.blocks K).rowLabel i)).degSide + 2 ≤ ((R.layouts K).layout ((A.blocks K).rowLabel i)).degCoef ∧
    IsPressureSegmentation ((R.layouts K).layout ((A.blocks K).rowLabel i))
  rows_groups_cover : ∀ K, ∀ ι ∈ D.mesh.tested K, ∀ ι', ι' ∉ D.mesh.resolved K → ι' ∉ D.mesh.band K →
    ι - ι' ∈ modelLabels D K → ∃ g, ι' ∈ (P.potential K).rowPartners g ∧ ι - ι' ∈ (P.potential K).groupHarmonics g
  sources_leak : ∀ K, deactSources D K (P.potential K) ⊆ (A.blocks K).leakModes
  actuator_pos : ∀ K, 0 < (A.blocks K).actuatorCost ∧ 0 ≤ (A.blocks K).actuatorErr
  actuator_kappa : ∀ K, (A.blocks K).actuatorCost * (A.blocks K).actuatorErr ≤ (A.blocks K).rowKappaCost
  actuator_err : ∀ K, ∑ ι ∈ (A.blocks K).actuatorRows, ∫ p in (D.mesh.box K).rect, p.1 * ∑ l, ∑ c : Fin 3,
      ‖labelVel D.azimuthOrder ι (D.cert.actuator l) p c - labelVel D.azimuthOrder ι ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2
    ≤ (A.blocks K).actuatorErr
  actuator_model_regular : ∀ K l ι c,
    AEStronglyMeasurable (fun p => labelVel D.azimuthOrder ι ((A.blocks K).actuatorModel l) p c)
      (volume.restrict (D.mesh.box K).rect) ∧
    IntegrableOn (fun p => p.1 * ‖labelVel D.azimuthOrder ι ((A.blocks K).actuatorModel l) p c‖ ^ 2) (D.mesh.box K).rect
  actuator_off_rows : ∀ K i, (A.blocks K).rowLabel i ∉ (A.blocks K).actuatorRows → ∀ l,
    actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i) (D.cert.actuator l)
      = actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i) ((A.blocks K).actuatorModel (l : ℕ))
  pair_slack_pos : ∀ K, ∀ ι ∈ R.pairSlackLabels K, 0 < R.pairSlackWeight K ι
  box_strain_pair : ∀ K, ∀ ι ∈ D.mesh.resolved K, ι ∈ R.pairSlackLabels K →
    R.pairSlackWeight K ι ≤ (R.leaves K).boxStrain ι
  costs_pos : ∀ K, 0 < (A.blocks K).errorCost ∧ 0 < (A.blocks K).deactCost ∧ 0 < (A.blocks K).longLowCost ∧
    0 < (A.blocks K).longHighCost ∧ ∀ ι ∈ D.mesh.tested K, 0 < (A.blocks K).freqCost ι
  leak_budget : ∀ K, ∀ ι ∈ D.mesh.tested K, (A.blocks K).leakWeight ι *
      (1 / (A.blocks K).errorCost + (if labelTime ι = 0 then 0 else 1 / (A.blocks K).freqCost ι)
        + ((activeGroups (P.potential K) ι).card : ℝ) / (A.blocks K).deactCost
        + longRowTerm D R K (A.blocks K) ι
        + (if ι ∈ (A.blocks K).actuatorRows then 1 / (A.blocks K).actuatorCost else 0)) ≤ 1
  box_curl_rows : ∀ K, ∀ ι ∈ D.mesh.resolved K,
    2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
        + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVelocity ^ 2 ≤ (R.leaves K).boxCurl ι
  box_velocity_rows : ∀ K, ∀ ι ∈ D.mesh.resolved K,
    2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
      + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVorticity ^ 2
      + (if ι ∈ D.mesh.tested K then (A.blocks K).freqCost ι
          * (2 * Real.pi * (labelTime ι : ℝ) * (D.modelErrors K).periodInverse) ^ 2 else 0)
      ≤ (R.leaves K).boxVelocity ι
  band_allowance_rows : ∀ K, ∀ ι ∈ D.mesh.band K,
    2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
        + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVelocity ^ 2
      ≤ (A.blocks K).bandCurlAllowance ι ∧
    2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
        + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVorticity ^ 2
      ≤ (A.blocks K).bandVelAllowance ι
  group_velocity : ∀ K g, ∀ p ∈ (D.mesh.box K).rect, ∀ σ θ : ℝ,
    cnormSq (fun a => ∑ α ∈ (P.potential K).groupHarmonics g,
        labelPhase D.azimuthOrder α σ θ * modelVelocity D K α p a)
      ≤ (P.potential K).groupVel g ^ 2
  group_curl : ∀ K g, ∀ p ∈ (D.mesh.box K).rect, ∀ σ θ : ℝ,
    cnormSq (fun a => ∑ α ∈ (P.potential K).groupHarmonics g,
        labelPhase D.azimuthOrder α σ θ * modelVorticity D K α p a)
      ≤ (P.potential K).groupCurl g ^ 2
  period_box : ∀ q ∈ D.cert.params, ∀ K,
    |1 / D.cert.period q - D.model.periodInverse| ≤ (D.modelErrors K).periodInverse

end RowFunctionals

section Pressure

open SteadyCert

end Pressure

section OffModes

variable {k : ℕ} {C : Type} {nE nM : ℕ}

structure OffModeCover (D : CellLayerData k C nE nM) where
  count : ℕ
  conditions : Fin count → TailBand.OffModeCondition C nE nM
  choose : Fin D.mesh.count → ℤ × ℤ → Finset (Fin count)

structure IsOffModeCover (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (O : OffModeCover D) : Prop where
  valid : ∀ q ∈ D.cert.params, ∀ K, ∀ ι ∉ D.mesh.resolved K, ∀ j ∈ O.choose K ι,
    TailBand.IsOffModeCondition (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
      D.azimuthOrder (O.conditions j)
  mode_mem : ∀ K, ∀ ι ∉ D.mesh.resolved K, ∀ j ∈ O.choose K ι, ι ∈ (O.conditions j).modes
  region_sup : ∀ K, ∀ ι ∉ D.mesh.resolved K, (D.mesh.box K).rect ∩ halfPlane ⊆ ⋃ j ∈ O.choose K ι, (O.conditions j).region
  charges_le : ∀ K, ∀ ι ∉ D.mesh.resolved K, ∀ j ∈ O.choose K ι, ∀ p ∈ (D.mesh.box K).rect ∩ (O.conditions j).region,
    (R.entryCharges K ι).curlCharge p ≤ (O.conditions j).charges.curlCharge p ∧
    (R.entryCharges K ι).gradCharge p ≤ (O.conditions j).charges.gradCharge p ∧
    (R.entryCharges K ι).velCharge p ≤ (O.conditions j).charges.velCharge p ∧
    (R.entryCharges K ι).stretchConst = (O.conditions j).charges.stretchConst

structure ExteriorCover (C : Type) (nE nM : ℕ) where
  rayCount : ℕ
  rayConditions : Fin rayCount → TailBand.ExteriorCondition C nE nM
  pointCount : ℕ
  pointConditions : Fin pointCount → TailBand.OffModeCondition C nE nM
  parts : ℤ × ℤ → Finset (Fin rayCount ⊕ Fin pointCount)
  charges : TailBand.EntryCharges

def ExteriorCover.region {C : Type} {nE nM : ℕ} (X : ExteriorCover C nE nM) :
    Fin X.rayCount ⊕ Fin X.pointCount → Set (ℝ × ℝ)
  | .inl i => (X.rayConditions i).region
  | .inr j => (X.pointConditions j).region

def ExteriorCover.modes {C : Type} {nE nM : ℕ} (X : ExteriorCover C nE nM) :
    Fin X.rayCount ⊕ Fin X.pointCount → Set (ℤ × ℤ)
  | .inl i => (X.rayConditions i).modes
  | .inr j => (X.pointConditions j).modes

structure IsExteriorCover (D : CellLayerData k C nE nM) (X : ExteriorCover C nE nM) : Prop where
  ray_valid : ∀ q ∈ D.cert.params, ∀ i, TailBand.IsExteriorCondition (D.pieces q) (D.cert.period q) (D.bounds q)
    D.cert.weightFn (D.charges none) D.azimuthOrder (X.rayConditions i)
  point_valid : ∀ q ∈ D.cert.params, ∀ j, TailBand.IsOffModeCondition (D.pieces q) (D.cert.period q) (D.bounds q)
    D.cert.weightFn (D.charges none) D.azimuthOrder (X.pointConditions j)
  ray_charges : ∀ i, (X.rayConditions i).charges = X.charges
  point_charges : ∀ j, (X.pointConditions j).charges = X.charges
  mode_mem : ∀ ι, ∀ a ∈ X.parts ι, ι ∈ X.modes a
  charges_cover : X.charges.Covers (D.charges none) Set.univ (D.mesh.exterior ∩ halfPlane)
  charges_nonneg : ∀ p, 0 ≤ X.charges.curlCharge p ∧ 0 ≤ X.charges.gradCharge p ∧ 0 ≤ X.charges.velCharge p
  covers : ∀ ι, D.mesh.exterior ∩ halfPlane ⊆ ⋃ a ∈ X.parts ι, X.region a
  apart : ∀ ι, ∀ a ∈ X.parts ι, ∀ b ∈ X.parts ι, a ≠ b → volume (X.region a ∩ X.region b) = 0
  in_exterior : ∀ ι, ∀ a ∈ X.parts ι, X.region a ⊆ D.mesh.exterior ∩ halfPlane
  region_measurable : ∀ a, MeasurableSet (X.region a)
  charges_measurable : Measurable X.charges.curlCharge ∧ Measurable X.charges.gradCharge ∧ Measurable X.charges.velCharge ∧
    ∀ ι, Measurable ((D.charges none).curl ι) ∧ Measurable ((D.charges none).product ι) ∧
      Measurable ((D.charges none).gradient ι) ∧ Measurable ((D.charges none).length ι)
  charges_bounded : ∃ c : ℝ, ∀ p ∈ D.mesh.exterior ∩ halfPlane, |X.charges.curlCharge p| ≤ c ∧
    |X.charges.gradCharge p| ≤ c ∧ |X.charges.velCharge p| ≤ c ∧ |X.charges.stretchConst| ≤ c ∧
    ∀ ι, |(D.charges none).curl ι p| ≤ c ∧ |(D.charges none).product ι p| ≤ c ∧ |(D.charges none).gradient ι p| ≤ c ∧
      (D.charges none).gradient ι p * (D.charges none).length ι p ≤ c ∧
      (D.charges none).gradient ι p * ((D.charges none).length ι p)⁻¹ ≤ c

end OffModes

section Tree

variable {k : ℕ} {C : Type} {nE nM : ℕ}

open CellCert.CellCoordinates

def keyWithMode (m : ℤ) : SkeletonKey → SkeletonKey
  | .velocity _ r l lo hi t a d => .velocity m r l lo hi t a d
  | .gradient _ r l lo hi t a d => .gradient m r l lo hi t a d
  | .pressure _ r l lo hi t d => .pressure m r l lo hi t d
  | .corner _ p a => .corner m p a
  | .stream p => .stream p
  | .private_ => .private_

def keyOnPlane : SkeletonKey → Prop
  | .velocity _ r l _ _ _ _ _ => r = false ∧ l = 0
  | .gradient _ r l _ _ _ _ _ => r = false ∧ l = 0
  | .pressure _ r l _ _ _ _ => r = false ∧ l = 0
  | .corner _ p _ => p.2 = 0
  | .stream p => p.2 = 0
  | .private_ => False

def keyFlipSign : SkeletonKey → ℝ
  | .velocity _ _ _ _ _ _ a _ => frameSign a
  | .gradient _ _ _ _ _ _ a _ => -frameSign a
  | .pressure _ _ _ _ _ _ _ => 1
  | .corner _ _ a => frameSign a
  | .stream _ => frameSign 2
  | .private_ => 0

def sideKeyGeom : SkeletonKey → Option (Bool × ℝ × ℝ × ℝ × (ℕ → ℕ → ℝ) × ℕ)
  | .velocity _ r l lo hi t _ d => some (r, l, lo, hi, t, d)
  | .gradient _ r l lo hi t _ d => some (r, l, lo, hi, t, d)
  | .pressure _ r l lo hi t d => some (r, l, lo, hi, t, d)
  | _ => none

def retileKey (lo hi : ℝ) (t : ℕ → ℕ → ℝ) (i : ℕ) : SkeletonKey → SkeletonKey
  | .velocity n r l _ _ _ a _ => .velocity n r l lo hi t a i
  | .gradient n r l _ _ _ a _ => .gradient n r l lo hi t a i
  | .pressure n r l _ _ _ _ => .pressure n r l lo hi t i
  | key => key

def presUnitMoment (L : CellLayout) : L.Datum → ℂ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) =>
      (L.presSegment i.2.1).moment true (fun p => presMode L.order (i.1 : ℤ) (fun _ => 1) p.1 p.2) (fun _ => 0) (fun _ => 0) i.2.2
  | _ => 0

def headUnit (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count) (ι : ℤ × ℤ) :
    CellVars D R K → ℂ
  | Sum.inl (Sum.inl d) => if d.1.1 = ι then presUnitMoment ((R.layouts K).layout d.1.1) d.2 else 0
  | _ => 0

def keyVelNormal : SkeletonKey → Prop
  | .velocity n r _ _ _ _ a _ => n = 0 ∧ a = (if r then 0 else 2)
  | _ => False

def ConjDatum (L L' : CellLayout) : L.Datum → L'.Datum → Prop
  | Sum.inl i, Sum.inl i' =>
      L.box = L'.box ∧ L.bases = L'.bases ∧ (i'.1 : ℤ) = -(i.1 : ℤ) ∧ i.2.1 = i'.2.1 ∧ i.2.2.1 = i'.2.2.1 ∧
        (i.2.2.2.1 : ℕ) = i'.2.2.2.1 ∧ (i.2.2.2.2 : ℕ) = i'.2.2.2.2
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl i') =>
      L.box = L'.box ∧ L.bases = L'.bases ∧ (i'.1 : ℤ) = -(i.1 : ℤ) ∧ i.2.1 = i'.2.1 ∧
        (i.2.2.1 : ℕ) = i'.2.2.1 ∧ (i.2.2.2 : ℕ) = i'.2.2.2
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inr (Sum.inl i')) =>
      (i'.1 : ℤ) = -(i.1 : ℤ) ∧ L.segment i.2.1 = L'.segment i'.2.1 ∧ i.2.2.1 = i'.2.2.1 ∧ (i.2.2.2 : ℕ) = i'.2.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))), Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))) =>
      (i'.1 : ℤ) = -(i.1 : ℤ) ∧ L.segment i.2.1 = L'.segment i'.2.1 ∧ i.2.2.1 = i'.2.2.1 ∧ (i.2.2.2 : ℕ) = i'.2.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))), Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i')))) =>
      (i'.1 : ℤ) = -(i.1 : ℤ) ∧ L.presSegment i.2.1 = L'.presSegment i'.2.1 ∧ (i.2.2 : ℕ) = i'.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))))) =>
      (i'.1 : ℤ) = -(i.1 : ℤ) ∧ L.corner i.2.1 = L'.corner i'.2.1 ∧ L.cornerOther i.2.1 = L'.cornerOther i'.2.1 ∧
        i.2.2 = i'.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c')))))) =>
      L.corner c = L'.corner c' ∧ L.cornerOther c = L'.cornerOther c'
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))))) =>
      L.box = L'.box ∧ L.bases = L'.bases ∧ (i'.1 : ℤ) = -(i.1 : ℤ) ∧ i.2.1 = i'.2.1 ∧ i.2.2.1 = i'.2.2.1 ∧
        (i.2.2.2 : ℕ) = i'.2.2.2
  | _, _ => False

def streamEnds (S : FaceSegment) (e : Fin 2) : ℝ × ℝ :=
  if S.radial then (S.level, if e = 0 then S.lo else S.hi) else (if e = 0 then S.lo else S.hi, S.level)

structure KeyEvaluation where
  label : ℤ × ℤ
  conj : Bool
  sign : ℝ

def IsKeyEvaluation (ι : ℤ × ℤ) (key : SkeletonKey) (w : KeyEvaluation) : Prop :=
  (w.label = ι ∧ w.conj = false ∧ w.sign = 1) ∨ (w.label = -ι ∧ w.conj = true ∧ w.sign = 1) ∨
    (w.label = labelFlip ι ∧ w.conj = false ∧ keyOnPlane key ∧ w.sign = keyFlipSign key) ∨
    (w.label = -labelFlip ι ∧ w.conj = true ∧ keyOnPlane key ∧ w.sign = keyFlipSign key)

def IsKeyVar {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R) (ι : ℤ × ℤ)
    (key : SkeletonKey) (imag : Bool) (a : T.Slaved) : Prop :=
  T.evalCell a = none ∧ T.evalKappa a = none ∧ T.skelKey a = some (ι, key) ∧ T.evalImag a = imag

def PartBound {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R) (ι : ℤ × ℤ)
    (key : SkeletonKey) (imag : Bool) : Option T.Slaved → Prop
  | some a => IsKeyVar T ι key imag a
  | none => T.KeyPartOmitted ι key imag ∨ ∃ p : ℝ × ℝ, key = .stream p ∧ p.1 = 0

open Classical in
def partVec {S : Type} (re im : Option S) (conj : Bool) : S → ℂ :=
  fun a => (if re = some a then 1 else 0) + (if im = some a then (if conj then -Complex.I else Complex.I) else 0)

structure SplitChoice {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R) where
  evaluation : KeyEvaluation
  tiles : ℕ
  tlo : Fin tiles → ℝ
  thi : Fin tiles → ℝ
  ttest : Fin tiles → ℕ → ℕ → ℝ
  tdeg : ℕ
  coef : Fin tiles → ℕ → ℝ
  re : Fin tiles → ℕ → Option T.Slaved
  im : Fin tiles → ℕ → Option T.Slaved
  flux : Fin tiles → Bool
  fre : Fin tiles → Fin 2 → Option T.Slaved
  fim : Fin tiles → Fin 2 → Option T.Slaved

structure FluxChoice {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R) where
  evaluation : KeyEvaluation
  endRe : Fin 2 → Option T.Slaved
  endIm : Fin 2 → Option T.Slaved

inductive RowReason {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) where
  | key (evaluation : KeyEvaluation) (re im : Option T.Slaved)
  | split (w : SplitChoice T)
  | flux (w : FluxChoice T)
  | derived (rows : Finset ((R.layouts K).layout d.1.1).RelIndex) (mult : ((R.layouts K).layout d.1.1).RelIndex → ℂ)
  | normal (pcoef : ℕ → ℝ) (pdeg : ℕ)
  | leaf (conj : Bool) (source : CellVar D.mesh K (R.layouts K)) (re im : Option T.Slaved)
  | unused

def RowReason.IsUnused {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    {K : Fin D.mesh.count} {d : CellVar D.mesh K (R.layouts K)} : RowReason T K d → Prop
  | .unused => True
  | _ => False

structure RowEntry (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (T : TreeEntry D R) where
  rowVars : (K : Fin D.mesh.count) → CellVar D.mesh K (R.layouts K) → Finset T.Slaved
  rowCoef : (K : Fin D.mesh.count) → CellVar D.mesh K (R.layouts K) → T.Slaved → ℂ
  rank : (K : Fin D.mesh.count) → CellVar D.mesh K (R.layouts K) → ℕ
  reason : (K : Fin D.mesh.count) → (d : CellVar D.mesh K (R.layouts K)) → RowReason T K d
  kappa : Fin k → T.Slaved
  zeta : Fin k → T.Free
  portRe : ℕ → T.Free
  portIm : ℕ → Option T.Free
  portConj : ℕ → Bool

namespace RowEntry

variable {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R} (W : RowEntry D R T)

open Classical in
def rowVec (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : T.Slaved → ℂ :=
  fun a => if a ∈ W.rowVars K d then W.rowCoef K d a else 0

def rowValue (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (f : T.Slaved → ℝ) : ℂ :=
  ∑ a ∈ W.rowVars K d, W.rowCoef K d a * (f a : ℂ)

open Classical in
def rowEmbed (K : Fin D.mesh.count) : Matrix (CellVars D R K) (T.Slaved ⊕ T.Free) ℂ :=
  fun i v => match i, v with
  | Sum.inl (Sum.inl d), Sum.inl a => W.rowVec K d a
  | Sum.inl (Sum.inr j), Sum.inr f =>
      (if f = W.portRe (R.portKey K j) then 1 else 0)
        + (if W.portIm (R.portKey K j) = some f then (if W.portConj (R.portKey K j) then -Complex.I else Complex.I) else 0)
  | Sum.inr (Sum.inl i), Sum.inl a => if a = W.kappa i then 1 else 0
  | Sum.inr (Sum.inr i), Sum.inr f => if f = W.zeta i then 1 else 0
  | _, _ => 0

def KeyRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (rd : KeyEvaluation) (re im : Option T.Slaved) :
    Prop :=
  keyOf ((R.layouts K).layout d.1.1) d.2 ≠ .private_ ∧
  IsKeyEvaluation d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) rd ∧
  PartBound T rd.label (keyWithMode rd.label.1 (keyOf ((R.layouts K).layout d.1.1) d.2)) false re ∧
  PartBound T rd.label (keyWithMode rd.label.1 (keyOf ((R.layouts K).layout d.1.1) d.2)) true im ∧
  W.rowVec K d = (rd.sign : ℂ) • partVec re im rd.conj

def tileSeg (rad : Bool) (lev : ℝ) (w : SplitChoice T) (j : Fin w.tiles) : FaceSegment :=
  keySeg rad lev (w.tlo j) (w.thi j) (w.ttest j)

def tileFlux (rad : Bool) (lev : ℝ) (w : SplitChoice T) (j : Fin w.tiles) : T.Slaved → ℂ :=
  if rad then
    ((-(w.ttest j 0 0 / lev) : ℝ) : ℂ) •
      (partVec (w.fre j 1) (w.fim j 1) w.evaluation.conj - partVec (w.fre j 0) (w.fim j 0) w.evaluation.conj)
  else
    ((w.ttest j 0 0 / w.ttest j 1 0 : ℝ) : ℂ) •
      (partVec (w.re j 1) (w.im j 1) w.evaluation.conj
        - ((w.ttest j 1 1 : ℝ) : ℂ) •
          (partVec (w.fre j 1) (w.fim j 1) w.evaluation.conj - partVec (w.fre j 0) (w.fim j 0) w.evaluation.conj))

def tileVec (rad : Bool) (lev : ℝ) (w : SplitChoice T) (j : Fin w.tiles) (i : ℕ) : T.Slaved → ℂ :=
  if w.flux j = true ∧ i = 0 then tileFlux rad lev w j else partVec (w.re j i) (w.im j i) w.evaluation.conj

def SplitRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (w : SplitChoice T) : Prop :=
  match sideKeyGeom (keyOf ((R.layouts K).layout d.1.1) d.2) with
  | none => False
  | some (rad, lev, lo, hi, t, deg) =>
      IsKeyEvaluation d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) w.evaluation ∧ 0 < w.tiles ∧
      ¬ T.gauge.DeletedOmitted d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) ∧
      (∀ j, ∀ i ∈ Finset.range (w.tdeg + 1), w.coef j i ≠ 0 →
        ¬ T.gauge.DeletedOmitted w.evaluation.label
          (keyWithMode w.evaluation.label.1 (retileKey (w.tlo j) (w.thi j) (w.ttest j) i (keyOf ((R.layouts K).layout d.1.1) d.2)))) ∧
      (∀ j, w.tlo j < w.thi j) ∧ (∀ j j' : Fin w.tiles, j.val + 1 = j'.val → w.thi j = w.tlo j') ∧
      (∀ j : Fin w.tiles, j.val = 0 → w.tlo j = lo) ∧ (∀ j : Fin w.tiles, j.val + 1 = w.tiles → w.thi j = hi) ∧
      (∀ j (s : ℝ), (keySeg rad lev lo hi t).test deg s
        = ∑ i ∈ Finset.range (w.tdeg + 1), w.coef j i * (tileSeg rad lev w j).test i s) ∧
      (∀ j, ∀ i ∈ Finset.range (w.tdeg + 1), w.coef j i ≠ 0 → ¬ (w.flux j = true ∧ i = 0) →
        PartBound T w.evaluation.label
          (keyWithMode w.evaluation.label.1 (retileKey (w.tlo j) (w.thi j) (w.ttest j) i (keyOf ((R.layouts K).layout d.1.1) d.2)))
          false (w.re j i) ∧
        PartBound T w.evaluation.label
          (keyWithMode w.evaluation.label.1 (retileKey (w.tlo j) (w.thi j) (w.ttest j) i (keyOf ((R.layouts K).layout d.1.1) d.2)))
          true (w.im j i)) ∧
      (∀ j, w.flux j = true →
        keyVelNormal (keyOf ((R.layouts K).layout d.1.1) d.2) ∧ w.evaluation.sign = 1 ∧
        ((w.evaluation.label = d.1.1 ∧ w.evaluation.conj = false) ∨ (w.evaluation.label = -d.1.1 ∧ w.evaluation.conj = true)) ∧
        (∀ e : Fin 2,
          PartBound T w.evaluation.label (.stream (streamEnds (tileSeg rad lev w j) e)) false (w.fre j e) ∧
          PartBound T w.evaluation.label (.stream (streamEnds (tileSeg rad lev w j) e)) true (w.fim j e)) ∧
        (rad = true → lev ≠ 0) ∧
        (rad = false → w.ttest j 1 0 ≠ 0 ∧
          PartBound T w.evaluation.label
            (keyWithMode w.evaluation.label.1 (retileKey (w.tlo j) (w.thi j) (w.ttest j) 1 (keyOf ((R.layouts K).layout d.1.1) d.2)))
            false (w.re j 1) ∧
          PartBound T w.evaluation.label
            (keyWithMode w.evaluation.label.1 (retileKey (w.tlo j) (w.thi j) (w.ttest j) 1 (keyOf ((R.layouts K).layout d.1.1) d.2)))
            true (w.im j 1))) ∧
      W.rowVec K d = (w.evaluation.sign : ℂ) •
        ∑ j, ∑ i ∈ Finset.range (w.tdeg + 1), (w.coef j i : ℂ) • tileVec rad lev w j i

def FluxRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (w : FluxChoice T) : Prop :=
  ((w.evaluation.label = d.1.1 ∧ w.evaluation.conj = false) ∨ (w.evaluation.label = -d.1.1 ∧ w.evaluation.conj = true)) ∧ w.evaluation.sign = 1 ∧
  ∃ (n : ((R.layouts K).layout d.1.1).modes) (s : Fin ((R.layouts K).layout d.1.1).segCount), (n : ℤ) = 0 ∧
    (∀ e : Fin 2,
      PartBound T w.evaluation.label (.stream (streamEnds (((R.layouts K).layout d.1.1).segment s) e)) false (w.endRe e) ∧
      PartBound T w.evaluation.label (.stream (streamEnds (((R.layouts K).layout d.1.1).segment s) e)) true (w.endIm e)) ∧
    ((((R.layouts K).layout d.1.1).segment s).radial = true ∧ d.2 = CellDatum.sideVelocity n s 0 ⟨0, by omega⟩ ∧
        0 < (((R.layouts K).layout d.1.1).segment s).level ∧
        W.rowVec K d = (((-((((R.layouts K).layout d.1.1).segment s).testCoef 0 0
            / (((R.layouts K).layout d.1.1).segment s).level) : ℝ) : ℂ)) •
          (partVec (w.endRe 1) (w.endIm 1) w.evaluation.conj - partVec (w.endRe 0) (w.endIm 0) w.evaluation.conj) ∨
     (((R.layouts K).layout d.1.1).segment s).radial = false ∧ d.2 = CellDatum.sideVelocity n s 2 ⟨0, by omega⟩ ∧
        (((R.layouts K).layout d.1.1).segment s).testCoef 1 0 ≠ 0 ∧
        W.rank K ⟨d.1, CellDatum.sideVelocity n s 2 ⟨1, by omega⟩⟩ < W.rank K d ∧
        ¬ (W.reason K ⟨d.1, CellDatum.sideVelocity n s 2 ⟨1, by omega⟩⟩).IsUnused ∧
        W.rowVec K d = ((((((R.layouts K).layout d.1.1).segment s).testCoef 0 0
            / (((R.layouts K).layout d.1.1).segment s).testCoef 1 0) : ℝ) : ℂ) •
          (W.rowVec K ⟨d.1, CellDatum.sideVelocity n s 2 ⟨1, by omega⟩⟩
            - ((((R.layouts K).layout d.1.1).segment s).testCoef 1 1 : ℂ) •
              (partVec (w.endRe 1) (w.endIm 1) w.evaluation.conj - partVec (w.endRe 0) (w.endIm 0) w.evaluation.conj)))

def relCoef (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (rows : Finset ((R.layouts K).layout d.1.1).RelIndex) (mult : ((R.layouts K).layout d.1.1).RelIndex → ℂ)
    (d' : ((R.layouts K).layout d.1.1).Datum) : ℂ :=
  ∑ ρ ∈ rows, mult ρ * ((R.layouts K).layout d.1.1).relationRow ρ d'

open Classical in
def DerivedRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (rows : Finset ((R.layouts K).layout d.1.1).RelIndex) (mult : ((R.layouts K).layout d.1.1).RelIndex → ℂ) : Prop :=
  relCoef K d rows mult d.2 = 1 ∧
  (∀ d', isPressureDatum ((R.layouts K).layout d.1.1) d' = true → relCoef K d rows mult d' = 0) ∧
  (∀ d', d' ≠ d.2 → relCoef K d rows mult d' ≠ 0 →
    W.rank K ⟨d.1, d'⟩ < W.rank K d ∧ ¬ (W.reason K ⟨d.1, d'⟩).IsUnused) ∧
  W.rowVec K d = -∑ d' ∈ Finset.univ.filter (fun d' => d' ≠ d.2), relCoef K d rows mult d' • W.rowVec K ⟨d.1, d'⟩

def LeafRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (conj : Bool)
    (source : CellVar D.mesh K (R.layouts K)) (re im : Option T.Slaved) : Prop :=
  (conj = false → source = d) ∧
  (conj = true → source.1.1 = -d.1.1 ∧ ConjDatum ((R.layouts K).layout d.1.1) ((R.layouts K).layout source.1.1) d.2 source.2) ∧
  re.isSome = true ∧
  (∀ a, re = some a → T.evalCell a = some ⟨K, source⟩ ∧ T.evalImag a = false) ∧
  (∀ a, im = some a → T.evalCell a = some ⟨K, source⟩ ∧ T.evalImag a = true) ∧
  (im = none → d.1.1 = (0, 0)) ∧
  W.rowVec K d = partVec re im conj

def UnusedRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  W.rowVec K d = 0 ∧
  (∀ i, R.cellForm K (Sum.inl (Sum.inl d)) i = 0 ∧ R.cellForm K i (Sum.inl (Sum.inl d)) = 0) ∧
  (∀ j e, (⟨R.creditOwner j e, R.creditCoord j e⟩ : Σ K' : Fin D.mesh.count, CellVar D.mesh K' (R.layouts K'))
    ≠ ⟨K, d⟩)

open Classical in
def velRow (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (n : ((R.layouts K).layout ι.1).modes)
    (s : Fin ((R.layouts K).layout ι.1).segCount) (a : Fin 3) (i : ℕ) : T.Slaved → ℂ :=
  if h : i < ((R.layouts K).layout ι.1).degSide + 2 then W.rowVec K ⟨ι, CellDatum.sideVelocity n s a ⟨i, h⟩⟩ else 0

def velReady (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (n : ((R.layouts K).layout d.1.1).modes)
    (s : Fin ((R.layouts K).layout d.1.1).segCount) (a : Fin 3) (i : ℕ) : Prop :=
  ∃ h : i < ((R.layouts K).layout d.1.1).degSide + 2,
    W.rank K ⟨d.1, CellDatum.sideVelocity n s a ⟨i, h⟩⟩ < W.rank K d ∧
      ¬ (W.reason K ⟨d.1, CellDatum.sideVelocity n s a ⟨i, h⟩⟩).IsUnused

def cornerRow (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (n : ((R.layouts K).layout ι.1).modes)
    (c : Option (Fin ((R.layouts K).layout ι.1).cornerCount)) (a : Fin 3) : T.Slaved → ℂ :=
  match c with
  | none => 0
  | some c => W.rowVec K ⟨ι, CellDatum.cornerVelocity n c a⟩

def cornerReady (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (n : ((R.layouts K).layout d.1.1).modes)
    (c : Fin ((R.layouts K).layout d.1.1).cornerCount) : Prop :=
  ∀ a : Fin 3, W.rank K ⟨d.1, CellDatum.cornerVelocity n c a⟩ < W.rank K d ∧
    ¬ (W.reason K ⟨d.1, CellDatum.cornerVelocity n c a⟩).IsUnused

def NormalRow (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (pcoef : ℕ → ℝ) (pdeg : ℕ) : Prop :=
  ∃ (n : ((R.layouts K).layout d.1.1).modes) (s : Fin ((R.layouts K).layout d.1.1).segCount)
    (deg : Fin (((R.layouts K).layout d.1.1).degSide + 1)) (c₀ : Option (Fin ((R.layouts K).layout d.1.1).cornerCount))
    (c₁ : Fin ((R.layouts K).layout d.1.1).cornerCount),
    ((R.layouts K).layout d.1.1).segEnd s 1 = some c₁ ∧
    ((R.layouts K).layout d.1.1).corner c₁ = streamEnds (((R.layouts K).layout d.1.1).segment s) 1 ∧
    W.cornerReady K d n c₁ ∧
    (match c₀ with
      | some c => ((R.layouts K).layout d.1.1).segEnd s 0 = some c ∧
          ((R.layouts K).layout d.1.1).corner c = streamEnds (((R.layouts K).layout d.1.1).segment s) 0 ∧
          W.cornerReady K d n c
      | none => (((R.layouts K).layout d.1.1).segment s).radial = false ∧
          (((R.layouts K).layout d.1.1).segment s).lo = 0) ∧
    (∀ a : Fin 3, W.velReady K d n s a deg ∧ ∀ i ∈ Finset.range (pdeg + 1), W.velReady K d n s a i) ∧
    ((((R.layouts K).layout d.1.1).segment s).radial = true ∧
        d.2 = CellDatum.sideGradient n s 0 deg ∧ (((R.layouts K).layout d.1.1).segment s).level ≠ 0 ∧
        (∀ u : ℝ, ∑ j ∈ Finset.range ((deg : ℕ) + 1),
            ((j : ℝ) * (((R.layouts K).layout d.1.1).segment s).testCoef deg j) * u ^ (j - 1)
          = ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (((R.layouts K).layout d.1.1).segment s).test i u) ∧
        W.rowVec K d =
          -(((1 / (((R.layouts K).layout d.1.1).segment s).level : ℝ) : ℂ) •
              (W.velRow K d.1 n s 0 deg
                + ((azimuth ((R.layouts K).layout d.1.1).order n : ℂ) * Complex.I) • W.velRow K d.1 n s 1 deg))
          - (((((R.layouts K).layout d.1.1).segment s).test deg (((R.layouts K).layout d.1.1).segment s).hi : ℝ) : ℂ) •
              W.rowVec K ⟨d.1, CellDatum.cornerVelocity n c₁ 2⟩
          + (((((R.layouts K).layout d.1.1).segment s).test deg (((R.layouts K).layout d.1.1).segment s).lo : ℝ) : ℂ) •
              W.cornerRow K d.1 n c₀ 2
          + ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) • W.velRow K d.1 n s 2 i ∨
     (((R.layouts K).layout d.1.1).segment s).radial = false ∧
        d.2 = CellDatum.sideGradient n s 2 deg ∧
        (∀ u : ℝ, u * ∑ j ∈ Finset.range ((deg : ℕ) + 1),
            ((j : ℝ) * (((R.layouts K).layout d.1.1).segment s).testCoef deg j) * u ^ (j - 1)
          = ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (((R.layouts K).layout d.1.1).segment s).test i u) ∧
        W.rowVec K d =
          -((((((R.layouts K).layout d.1.1).segment s).hi * (((R.layouts K).layout d.1.1).segment s).test deg
                (((R.layouts K).layout d.1.1).segment s).hi : ℝ) : ℂ) •
              W.rowVec K ⟨d.1, CellDatum.cornerVelocity n c₁ 0⟩)
          + (((((R.layouts K).layout d.1.1).segment s).lo * (((R.layouts K).layout d.1.1).segment s).test deg
                (((R.layouts K).layout d.1.1).segment s).lo : ℝ) : ℂ) •
              W.cornerRow K d.1 n c₀ 0
          + ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) • W.velRow K d.1 n s 0 i
          - ((azimuth ((R.layouts K).layout d.1.1).order n : ℂ) * Complex.I) • W.velRow K d.1 n s 1 deg)

def Accounted (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  match W.reason K d with
  | .key rd re im => W.KeyRow K d rd re im
  | .split w => W.SplitRow K d w
  | .flux w => W.FluxRow K d w
  | .derived rows mult => W.DerivedRow K d rows mult
  | .normal pcoef pdeg => W.NormalRow K d pcoef pdeg
  | .leaf conj source re im => W.LeafRow K d conj source re im
  | .unused => W.UnusedRow K d

end RowEntry

structure TreeRowConditions (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ) (T : TreeEntry D R)
    (W : RowEntry D R T) : Prop where
  embed_eq : ∀ K, T.embed K = W.rowEmbed K
  key_order : T.keyLayout.order = D.azimuthOrder
  head_credit : ∀ j e (ι : ℤ × ℤ), headUnit D R (R.creditOwner j e) ι (Sum.inl (Sum.inl (R.creditCoord j e))) = 0
  justified : ∀ K d, W.Accounted K d
  global_eq : ∀ y : T.Slaved ⊕ T.Free → ℝ,
    (haveI := T.slavedFintype; haveI := T.freeFintype; y ⬝ᵥ (T.globalLeaf *ᵥ y))
      ≤ globalForm D e (fun i => y (Sum.inl (W.kappa i))) (fun i => y (Sum.inr (W.zeta i)))
  freeMap_zero : T.freeMap = 0
  kappa_eval : ∀ i, T.evalCell (W.kappa i) = none ∧ T.evalKappa (W.kappa i) = some i
  head_kernel : ∀ K (ι : D.mesh.resolved K), R.cellForm K *ᵥ headUnit D R K ι.1 = 0 ∧
    (R.cellForm K)ᴴ *ᵥ headUnit D R K ι.1 = 0
  base_zero : ∀ q ∈ D.cert.params, (T.basePoint q).v = 0 ∧ (T.basePoint q).G = 0 ∧ (T.basePoint q).H = 0 ∧
    (T.basePoint q).g = 0 ∧ (T.basePoint q).κ = 0 ∧ (T.basePoint q).F = 0

open Classical in
def InRowRange {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R} (W : RowEntry D R T)
    (K : Fin D.mesh.count) (x : CellVars D R K → ℂ) : Prop :=
  ∃ (y : T.Slaved → ℝ) (β : Fin T.gauge.count → ℂ) (γ : ℤ × ℤ → ℂ),
    (∀ d, ¬ (W.reason K d).IsUnused → x (Sum.inl (Sum.inl d)) = W.rowValue K d y
      + ∑ c, β c * T.gaugeDir K c (Sum.inl (Sum.inl d))
      + ∑ ι ∈ D.mesh.resolved K, γ ι * headUnit D R K ι (Sum.inl (Sum.inl d))) ∧
    (∀ i, (x (Sum.inr (Sum.inl i))).im = 0) ∧ (∀ i, (x (Sum.inr (Sum.inr i))).im = 0)

end Tree

section Initial

end Initial

section CellLayerBreakdown

variable {k : ℕ} {C : Type} {nE nM : ℕ}

end CellLayerBreakdown

end Assembly

end CertCell

end Breakdown

end
end

section

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

structure FarFieldValueSets where
  chart : CellCert.GivenFields.ChartParams
  strain : ScalarShape.ChartBound
  meanGrad : ScalarShape.ChartBound
  waveGrad : ScalarShape.ChartBound

structure FarFieldConditions {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (Tb : FarFieldValueSets) : Prop where
  chart_valid : CellCert.GivenFields.IsChartParams Tb.chart
  strain_enclosed : ∀ p ∈ D.mesh.exterior ∩ halfPlane, ∀ σ θ : ℝ, ∀ u : Space,
    inner ℝ (strainOf D.given σ (cylPoint p.1 θ p.2) u) u ≤ Tb.strain.eval Tb.chart (cylPoint p.1 θ p.2) * ‖u‖ ^ 2
  mean_enclosed : ∀ p ∈ D.mesh.exterior ∩ halfPlane,
    opBound (fun a b => labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p (a, b))
      (Tb.meanGrad.eval Tb.chart (planePoint p))
  wave_enclosed : ∀ p ∈ D.mesh.exterior ∩ halfPlane, ∀ σ θ : ℝ, ∀ u : Space,
    ‖vorticityGradOf D.givenHess σ (cylPoint p.1 θ p.2) u
      - CellMatField.frameMap θ (fun a b => (labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p (a, b)).re) u‖
      ≤ Tb.waveGrad.eval Tb.chart (cylPoint p.1 θ p.2) * ‖u‖
  charges_eq : ∀ ι, ∀ p ∈ D.mesh.exterior ∩ halfPlane,
    (D.charges none).curl ι p = Tb.strain.eval Tb.chart (planePoint p) ∧
    (D.charges none).product ι p = Tb.meanGrad.eval Tb.chart (planePoint p) ∧
    (D.charges none).gradient ι p = Tb.waveGrad.eval Tb.chart (planePoint p)
  length_common : ∀ ι ι', ∀ p ∈ D.mesh.exterior ∩ halfPlane, (D.charges none).length ι p = (D.charges none).length ι' p
  length_pos : ∀ ι, ∀ p ∈ D.mesh.exterior ∩ halfPlane, 0 < (D.charges none).length ι p
  valueSets_nonneg : ∀ p ∈ D.mesh.exterior ∩ halfPlane,
    0 ≤ Tb.meanGrad.eval Tb.chart (planePoint p) ∧ 0 ≤ Tb.waveGrad.eval Tb.chart (planePoint p)

end Assembly

end CertCell

end Breakdown

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

section Closure

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def PotentialEntryConditions (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (A : Assembly.AssemblyEntry D R) (P : Assembly.CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (Assembly.CellVars D R K → ℂ) → Prop) : Prop :=
  IsCellMesh D.mesh → CellCalculus.CellCalculusConditions D R →
    Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess →
    (∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) → 1 ≤ D.azimuthOrder →
    Assembly.EntryChargesRegular D R → Assembly.AssemblyRegular D R →
    (∀ σ y u w, D.givenHess σ y u w = D.givenHess σ y w u) → Assembly.PotentialConditions D R A P S

structure CellLayerEntries (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) where
  assembly : Assembly.AssemblyEntry D R
  coupling : Assembly.CouplingEntries D R
  offModes : Assembly.OffModeCover D
  exterior : Assembly.ExteriorCover C nE nM
  farField : Assembly.FarFieldValueSets
  rows : Assembly.RowEntry D R T

structure CellLayerEntryConditions (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (e : ℝ) (Y : CellLayerEntries D R T) : Prop where
  charges_regular : Assembly.EntryChargesRegular D R
  leaves : ∀ K ι i j, AEStronglyMeasurable (fun p => (R.leaves K).localMatrix ι p i j)
      (volume.restrict (D.mesh.box K).rect) ∧ ∃ c : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖(R.leaves K).localMatrix ι p i j‖ ≤ c
  potential : PotentialEntryConditions D R Y.assembly Y.coupling (Assembly.InRowRange Y.rows)
  pairing : Assembly.PairingConditions D R Y.assembly Y.coupling.pairing (Assembly.InRowRange Y.rows)
  rows : Assembly.RowConditions D R Y.assembly
  row_functionals : Assembly.RowFunctionalConditions D R Y.assembly Y.coupling (Assembly.InRowRange Y.rows)
  tails : Assembly.TailConditions D R Y.assembly
  top_block : ∀ K (ι : D.mesh.resolved K) (x : Assembly.CellVars D R K → ℂ), Assembly.InRowRange Y.rows K x →
    CellCert.CellFormula.quadFormValue ((Y.assembly.blocks K).topBlock ι.1) x = Assembly.topValue D R K ι x
  elimination : Assembly.EliminationConditions D R Y.assembly (Assembly.InRowRange Y.rows)
  rows_gauge_blind : ∀ K (c : Fin T.gauge.count), (Y.assembly.blocks K).rowMap *ᵥ T.gaugeDir K c = 0
  rows_head_blind : ∀ K (ι : D.mesh.resolved K), (Y.assembly.blocks K).rowMap *ᵥ Assembly.headUnit D R K ι.1 = 0
  pressure_blind : ∀ K (d : CellCalculus.CellVar D.mesh K (R.layouts K)),
    Assembly.isPressureDatum ((R.layouts K).layout d.1.1) d.2 = true →
    (∀ j, (Y.assembly.blocks K).potentialKept (Sum.inl (Sum.inl d)) j = 0 ∧
      (Y.assembly.blocks K).potentialKept j (Sum.inl (Sum.inl d)) = 0 ∧
      (Y.assembly.blocks K).pairingKept (Sum.inl (Sum.inl d)) j = 0 ∧
      (Y.assembly.blocks K).pairingKept j (Sum.inl (Sum.inl d)) = 0 ∧
      (Y.assembly.blocks K).top (Sum.inl (Sum.inl d)) j = 0 ∧ (Y.assembly.blocks K).top j (Sum.inl (Sum.inl d)) = 0 ∧
      (Y.coupling.potential K).portForm (Sum.inl (Sum.inl d)) j = 0 ∧
      (Y.coupling.potential K).portForm j (Sum.inl (Sum.inl d)) = 0) ∧
    (∀ ι, (Y.assembly.blocks K).topBlock ι (Sum.inl (Sum.inl d)) = 0 ∧
      ∀ j, (Y.assembly.blocks K).topBlock ι j (Sum.inl (Sum.inl d)) = 0) ∧
    (∀ ι p j, (Y.assembly.blocks K).potentialSource ι (Sum.inl (Sum.inl d)) p j = 0 ∧
      (Y.assembly.blocks K).pairingSource ι (Sum.inl (Sum.inl d)) p j = 0 ∧
      (Y.assembly.blocks K).bandMap ι (Sum.inl (Sum.inl d)) p j = 0)
  off_mode_cover : Assembly.IsOffModeCover D R Y.offModes
  exterior_cover : Assembly.IsExteriorCover D Y.exterior
  exterior_stretch_const : Real.sqrt (7 / 2) ≤ Y.exterior.charges.stretchConst
  far_field_given : Assembly.FarFieldConditions D Y.farField
  tree_rows : Assembly.TreeRowConditions D R e T Y.rows
  gauge_keys : T.GaugeKeyConditions
  real_keys : T.RealKeyConditions
  gauge_transport : T.GaugeRowTransport Y.rows.rowVec

end Closure

end CertCell

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

open CellCert.GivenFields (weightPoly heightRatio radialVec polarVecQ cellCount)

inductive PotComponent where
  | plus
  | minus
  | axial
  deriving DecidableEq

def PotComponent.shift : PotComponent → ℤ
  | .plus => 1
  | .minus => -1
  | .axial => 0

def PotComponent.carriesSine : PotComponent → Bool
  | .axial => false
  | _ => true

structure PotScalar where
  amp : JetSpline
  lowOrder : ℕ
  highOrder : ℕ
  axisPower : ℕ

def polarSine (y : Space) : ℝ := Real.sqrt (1 - heightRatio y ^ 2)

def scalarValue (P : ShapeParams) (κ : FieldKey) (M : ℤ) (withSine : Bool) (S : PotScalar) (σ : ℝ)
    (y : Space) : ℂ :=
  Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
    weightPoly S.lowOrder S.highOrder (chartCoord P y) *
    (((1 - heightRatio y ^ 2) ^ S.axisPower * (if withSine then polarSine y else 1) : ℝ) : ℂ) *
    S.amp.toSpline.evalHalf (chartCoord P y) (heightRatio y)

def componentValue (P : ShapeParams) (κ : FieldKey) (S : PotComponent → PotScalar) (c : PotComponent)
    (σ : ℝ) (y : Space) : ℂ :=
  scalarValue P κ (labelAzimuth P.azimuthOrder κ.label + c.shift) c.carriesSine (S c) σ y

def coordsOfComponents (gp gn gz : ℂ) : Fin 3 → ℂ :=
  ![(gp + gn) / 2, (gp - gn) / (2 * Complex.I), gz]

structure PotKeyData where
  theta : PotComponent → PotScalar
  phi : PotComponent → PotScalar
  radialFlux : PotComponent → PotScalar
  polarFlux : PotComponent → PotScalar
  pressure : PotScalar

structure PotentialSeries where
  keys : Finset FieldKey
  data : FieldKey → PotKeyData

def vectorPotential (P : ShapeParams) (F : PotentialSeries) (pick : PotKeyData → PotComponent → PotScalar)
    (σ : ℝ) (y : Space) : Space :=
  realPartVec (∑ κ ∈ F.keys, coordsOfComponents (componentValue P κ (pick (F.data κ)) .plus σ y)
    (componentValue P κ (pick (F.data κ)) .minus σ y) (componentValue P κ (pick (F.data κ)) .axial σ y))

def fluxVector (P : ShapeParams) (κ : FieldKey) (K : PotKeyData) (c : PotComponent) (σ : ℝ) (y : Space) :
    Fin 3 → ℂ :=
  fun i => componentValue P κ K.radialFlux c σ y * (radialVec y i : ℂ) +
    componentValue P κ K.polarFlux c σ y * (polarVecQ y i : ℂ)

def fluxEntry (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (y : Space) (a i : Fin 3) : ℝ :=
  (∑ κ ∈ F.keys, coordsOfComponents (fluxVector P κ (F.data κ) .plus σ y i)
    (fluxVector P κ (F.data κ) .minus σ y i) (fluxVector P κ (F.data κ) .axial σ y i) a).re

def fluxMap (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (y : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.of fun a i => fluxEntry P F σ y a i))

def pressureValue (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (y : Space) : ℝ :=
  (∑ κ ∈ F.keys, scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ y).re

def PotentialSeries.toPotentialData (P : ShapeParams) (F : PotentialSeries) : PotentialData :=
  ⟨vectorPotential P F PotKeyData.theta, vectorPotential P F PotKeyData.phi, fluxMap P F, pressureValue P F⟩

structure IsJetMesh (A : JetAxis) (lo hi : ℝ) : Prop where
  sorted : A.breaks.Pairwise (· < ·)
  first : A.breaks.head? = some lo
  last : A.breaks.getLast? = some hi

def StartVanishOrder (H : JetSpline) (z : ℕ) : Prop :=
  ∀ p < z, ∀ e, H.coef (JetDof.node 0 p) e = 0

def EndVanishOrder (H : JetSpline) (z : ℕ) : Prop :=
  ∀ p < z, ∀ e, H.coef (JetDof.node (cellCount H.tAxis.breaks) p) e = 0

def dofMeetsEndCells (N : ℕ) : JetDof → Prop
  | .node k _ => k ≤ 1 ∨ N - 1 ≤ k
  | .bubble i _ => i = 0 ∨ N - 1 ≤ i

def AxisCellsVanish (H : JetSpline) : Prop :=
  ∀ d, ∀ e ∈ H.xAxis.dofs, dofMeetsEndCells (cellCount H.xAxis.breaks) e → H.coef d e = 0

def StartRowConstant (H : JetSpline) : Prop :=
  (∀ e ∈ H.xAxis.dofs, (∀ k, e ≠ JetDof.node k 0) → H.coef (JetDof.node 0 0) e = 0) ∧
    ∀ k k', k ≤ cellCount H.xAxis.breaks → k' ≤ cellCount H.xAxis.breaks →
      H.coef (JetDof.node 0 0) (JetDof.node k 0) = H.coef (JetDof.node 0 0) (JetDof.node k' 0)

structure IsPotentialScalar (lowBound highBound : ℕ) (S : PotScalar) : Prop where
  smooth_class : IsJetClass 1 1 S.amp
  start_order : ∃ z ≤ S.amp.tAxis.depth, lowBound ≤ S.lowOrder + z ∧ StartVanishOrder S.amp z
  end_order : ∃ z ≤ S.amp.tAxis.depth, highBound ≤ S.highOrder + z ∧ EndVanishOrder S.amp z

structure IsPotentialSeries (F : PotentialSeries) : Prop where
  theta_scalar : ∀ κ ∈ F.keys, ∀ c, IsPotentialScalar 2 2 ((F.data κ).theta c)
  phi_scalar : ∀ κ ∈ F.keys, ∀ c, IsPotentialScalar 2 1 ((F.data κ).phi c)
  theta_axis : ∀ κ ∈ F.keys, κ.label.1 ≠ 0 → ∀ c,
    1 ≤ ((F.data κ).theta c).axisPower ∨ AxisCellsVanish ((F.data κ).theta c).amp
  phi_axis : ∀ κ ∈ F.keys, κ.label.1 ≠ 0 → ∀ c,
    1 ≤ ((F.data κ).phi c).axisPower ∨ AxisCellsVanish ((F.data κ).phi c).amp
  radialFlux_mesh : ∀ κ ∈ F.keys, ∀ c, IsJetAxis ((F.data κ).radialFlux c).amp.tAxis 0 1 ∧
    IsJetMesh ((F.data κ).radialFlux c).amp.xAxis (-1) 1
  polarFlux_mesh : ∀ κ ∈ F.keys, ∀ c, IsJetMesh ((F.data κ).polarFlux c).amp.tAxis 0 1 ∧
    IsJetAxis ((F.data κ).polarFlux c).amp.xAxis (-1) 1
  flux_end : ∀ κ ∈ F.keys, ∀ c,
    (∃ z ≤ ((F.data κ).radialFlux c).amp.tAxis.depth, 2 ≤ ((F.data κ).radialFlux c).highOrder + z ∧
      EndVanishOrder ((F.data κ).radialFlux c).amp z) ∧
    (∃ z ≤ ((F.data κ).polarFlux c).amp.tAxis.depth, 2 ≤ ((F.data κ).polarFlux c).highOrder + z ∧
      EndVanishOrder ((F.data κ).polarFlux c).amp z)
  pressure_class : ∀ κ ∈ F.keys, IsJetClass 0 0 (F.data κ).pressure.amp
  pressure_end : ∀ κ ∈ F.keys, ∃ z ≤ (F.data κ).pressure.amp.tAxis.depth,
    2 ≤ (F.data κ).pressure.highOrder + z ∧ EndVanishOrder (F.data κ).pressure.amp z
  pressure_axis : ∀ κ ∈ F.keys, κ.label.1 ≠ 0 →
    1 ≤ (F.data κ).pressure.axisPower ∧ (1 ≤ (F.data κ).pressure.lowOrder ∨ StartVanishOrder (F.data κ).pressure.amp 1)
  pressure_start : ∀ κ ∈ F.keys, κ.label.1 = 0 →
    1 ≤ (F.data κ).pressure.lowOrder ∨ StartRowConstant (F.data κ).pressure.amp

structure CylModeData where
  labels : Finset (ℤ × ℤ)
  amp : ℤ × ℤ → Fin 3 → JetSpline

def cylField (m : ℕ) (G : CylModeData) (σ : ℝ) (y : Space) : Space :=
  ∑ ι ∈ G.labels, ∑ a : Fin 3,
    (labelPhase m ι σ (pointAngle y) * (((pointPlane y).1 : ℝ) : ℂ) *
      ((G.amp ι a).toSpline.evalHalf (pointPlane y).1 (pointPlane y).2)).re • frameUnit (pointAngle y) a

def VanishesBeyond (H : JetSpline) (R : ℝ) : Prop :=
  (∀ k p e, R ≤ |H.tAxis.breaks.getD k R| → H.coef (JetDof.node k p) e = 0) ∧
  (∀ i s e, R ≤ |H.tAxis.breaks.getD i R| → R ≤ |H.tAxis.breaks.getD (i + 1) R| →
    H.coef (JetDof.bubble i s) e = 0) ∧
  (∀ d k p, R ≤ |H.xAxis.breaks.getD k R| → H.coef d (JetDof.node k p) = 0) ∧
  (∀ d i s, R ≤ |H.xAxis.breaks.getD i R| → R ≤ |H.xAxis.breaks.getD (i + 1) R| →
    H.coef d (JetDof.bubble i s) = 0)

structure IsCylModeData (Rmesh Rsupp : ℝ) (G : CylModeData) : Prop where
  support_lt : 0 < Rsupp ∧ Rsupp < Rmesh
  axes : ∀ ι ∈ G.labels, ∀ a, IsJetAxis (G.amp ι a).tAxis 0 Rmesh ∧ IsJetAxis (G.amp ι a).xAxis (-Rmesh) Rmesh
  support_break : ∀ ι ∈ G.labels, ∀ a, Rsupp ∈ (G.amp ι a).tAxis.breaks ∧ Rsupp ∈ (G.amp ι a).xAxis.breaks ∧
    -Rsupp ∈ (G.amp ι a).xAxis.breaks
  vanish : ∀ ι ∈ G.labels, ∀ a, VanishesBeyond (G.amp ι a) Rsupp

structure PinShapeEntry (k : ℕ) where
  mesh : CellMesh
  azimuthOrder : ℕ
  pinCells : Fin k → CellMatField mesh.count
  cells : Fin k → CylModeData
  cellMesh : ℝ
  cellSupport : ℝ
  params : Fin k → ShapeParams
  generators : Fin k → TimeFieldData
  edge : Fin k → ℝ

def PinShapeEntry.pinData {k : ℕ} (R : PinShapeEntry k) : PinData k :=
  ⟨fun l => cylField R.azimuthOrder (R.cells l), fun l => shapeInfoField (R.params l) (R.generators l)⟩

def PinShapeEntry.pinField {k : ℕ} (R : PinShapeEntry k) (l : Fin k) : ℝ → Space → (Space →L[ℝ] Space) :=
  (R.pinCells l).field R.mesh.box R.azimuthOrder

structure IsPinShapeEntry {k : ℕ} (R : PinShapeEntry k) : Prop where
  mesh_valid : IsCellMesh R.mesh
  cells_valid : ∀ l, IsCylModeData R.cellMesh R.cellSupport (R.cells l)
  params_valid : ∀ l, IsShapeParams (R.params l)
  generators_valid : ∀ l, IsCompactTimeFieldData (R.edge l) (R.generators l)
  generators_break : ∀ l, HasEdgeBreak (R.edge l) (R.generators l)

end PotentialShape

end Breakdown

end
end

section

open scoped ContDiff ENNReal

open MeasureTheory Breakdown.CertCell Breakdown.CertCell.GivenShape

noncomputable section

namespace Breakdown

namespace CellLayerSystem

structure CertificateClauses {k : ℕ} (d : ExtendedCertificateData k) : Prop where
  radius_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j
  stiffRadius_nonneg : 0 ≤ d.stiffRadius
  scale_ne_zero : ∀ j, d.scale j ≠ 0
  weight_le_weightMax : d.weight ≤ d.weightMax
  multiplierWeight_pos : 0 < d.multiplierWeight
  coerciveL2_nonneg : 0 ≤ d.coerciveL2
  coercivePin_nonneg : 0 ≤ d.coercivePin
  rowBound_nonneg : 0 ≤ d.rowBound
  gapSize_nonneg : 0 ≤ d.gapSize
  formShift_nonneg : 0 ≤ d.formShift
  transfer_lt : d.transferLoss < 1
  coerciveTotal_ge : d.coerciveL2 + d.rowBound ≤ (1 - d.transferLoss) * d.coerciveTotal
  coerciveTotal_pos : 0 < d.coerciveTotal
  actuatorBound_nonneg : 0 ≤ d.actuatorBound
  modelFormBound_nonneg : 0 ≤ d.modelFormBound
  formBound_ge : d.modelFormBound + d.formShift ≤ d.formBound
  sizeBound_nonneg : 0 ≤ d.sizeBound
  supBound_pos : 0 < d.supBound
  period_le : ∀ q ∈ d.params, d.period q ≤ d.periodMax
  twist_pos : 0 < d.twist
  twist_mem : d.twist = 1 ∨ (d.twist = 2 ∧ ∃ Q, (Q, (1 / 2 : ℝ)) ∈ d.symmetries)
  actuator_norm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
    ENNReal.ofReal (d.actuatorBound ^ 2)
  defect_nonneg : ∀ q ∈ d.params, 0 ≤ d.defectBound q ∧ 0 ≤ d.defectRowBound q
  defect_l2 : ∀ q ∈ d.params,
    periodLIntegral (fun σ y => ‖d.defect q σ y‖ ^ 2) ≤ ENNReal.ofReal (d.defectBound q ^ 2)
  defect_rows : ∀ q ∈ d.params, d.rows (d.defect q) ≤ d.defectRowBound q
  defect_le : ∀ q ∈ d.params, d.defectBound q ≤ d.defectMax
  size : ∀ q ∈ d.params, d.coerciveL2 * d.defectBound q + d.defectRowBound q
    + d.coercivePin * vecNorm (d.targetGap q) ≤ (1 - d.transferLoss) * d.sizeBound
  small_first : 2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound < 1
  small_second : 4 * d.sizeBound ^ 2 * ((1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
      + 2 * (d.periodMax / d.twist) * (d.actuatorBound / d.multiplierWeight)
      + 2 * (d.periodMax / d.twist) / d.coerciveTotal) ≤ d.supBound ^ 2
  small_third : 4 * (1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound) * d.sizeBound ^ 2
    + 4 * (d.periodMax / d.twist) * d.sizeBound * (d.defectMax
      + 2 * supBoundFactor d.weight * d.sizeBound * d.supBound
      + 2 * (d.actuatorBound / d.multiplierWeight) * d.sizeBound) ≤ d.supBound ^ 2
  frame_unit : IsUnit d.frame
  adjoint_l2 : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ σ,
    ∫⁻ y, ENNReal.ofReal (‖d.adjoint j q σ y‖ ^ 2) ≤ ENNReal.ofReal (d.adjointL2 j ^ 2)
  adjointL2_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.adjointL2 j
  adjointDefect_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.adjointDefect j
  adjointQuad_nonneg : ∀ j ∈ d.adjointSet, 0 ≤ d.adjointQuad j
  adjoint_inclusion : ∀ j ∈ d.adjointSet, ∀ q ∈ d.params,
    d.adjointQuad j * (2 * d.sizeBound) ^ 2 + 2 * d.sizeBound * Real.sqrt (d.adjointDefect j ^ 2
      + (vecNorm (d.actuatorAdjointError q j) / d.multiplierWeight) ^ 2) + d.adjointOffset j ≤
      |d.scale j| * d.radius j
  stiffNorm_nonneg : 0 ≤ d.stiffNorm
  stiff_norm : ∀ x : Fin k → ℝ, ∑ j ∈ d.adjointSetᶜ, (∑ i, d.frame i j * x i) ^ 2 ≤
    d.stiffNorm ^ 2 * ∑ i, x i ^ 2
  stiff_offset : ∀ q ∈ d.params, Real.sqrt (∑ j ∈ d.adjointSetᶜ,
    (∑ i, d.frame i j * d.multiplier q i - d.scale j * q j) ^ 2) ≤ d.stiffOffset
  stiff_inclusion : 2 * d.sizeBound * d.stiffNorm / d.multiplierWeight + d.stiffOffset ≤ d.stiffRadius
  nontrivial : ∀ q ∈ d.params, 4 * d.sizeBound ^ 2 / d.weight <
    (periodLIntegral (fun σ y => matSq (fderiv ℝ (d.profile q σ) y))).toReal

structure CoerciveNumbers where
  epsSup : ℝ
  epsGradSup : ℝ
  ratio : ℝ
  globalError : ℝ

structure ShiftNumbers where
  centreSup : ℝ
  centreGrad : ℝ
  boxSup : ℝ
  boxGrad : ℝ

structure ShiftNumbersBounded {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (P : CellReduction.Instantiation.ProfileShapeEntry k) (N : ShiftNumbers) : Prop where
  centreSup_nonneg : 0 ≤ N.centreSup
  centreGrad_nonneg : 0 ≤ N.centreGrad
  boxSup_nonneg : 0 ≤ N.boxSup
  boxGrad_nonneg : 0 ≤ N.boxGrad
  centre_sup : ∀ σ y, ‖P.field 0 σ y - D.given σ y‖ ≤ N.centreSup
  box_sup : ∀ q ∈ D.cert.params, ∀ σ y, ‖P.field q σ y - P.field 0 σ y‖ ≤ N.boxSup
  centre_grad : ∀ σ, (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (fun x => P.field 0 σ x - D.given σ x) y‖ ^ 2)) ≤
    ENNReal.ofReal (N.centreGrad ^ 2)
  box_grad : ∀ q ∈ D.cert.params, ∀ σ,
    (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (fun x => P.field q σ x - P.field 0 σ x) y‖ ^ 3)) ≤
      ENNReal.ofReal (N.boxGrad ^ 3)
  gap_sum : CertReduction.gapGradCoeff D.cert.weight false * N.centreGrad + N.centreSup / Real.sqrt D.cert.weight
    + (CertReduction.gapGradCoeff D.cert.weight true * N.boxGrad + N.boxSup / Real.sqrt D.cert.weight) ≤
      D.cert.gapSize
  shift_sum : CertReduction.shiftGradCoeff D.cert.weight false * N.centreGrad
    + N.centreSup / (2 * Real.sqrt D.cert.weight)
    + (CertReduction.shiftGradCoeff D.cert.weight true * N.boxGrad + N.boxSup / (2 * Real.sqrt D.cert.weight)) ≤
      D.cert.formShift

structure PotentialEntries (k : ℕ) where
  series : Fin k → PotentialShape.PotentialSeries
  params : Fin k → ShapeParams
  pins : PotentialShape.PinShapeEntry k

structure PotentialEntriesBounded {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (P : PotentialEntries k) (r : Fin k → AdjointDefect.AdjointDefectEntry k) : Prop where
  params_valid : ∀ j ∈ D.cert.adjointSet, IsShapeParams (P.params j)
  series_valid : ∀ j ∈ D.cert.adjointSet, PotentialShape.IsPotentialSeries (P.series j)
  pins_valid : PotentialShape.IsPinShapeEntry P.pins
  centre_eq : ∀ j ∈ D.cert.adjointSet, (r j).centrePotential = (P.series j).toPotentialData (P.params j)
  pins_eq : ∀ j ∈ D.cert.adjointSet, (r j).pins = P.pins.pinData
  pinField_eq : P.pins.pinField = D.pinField

structure ReductionEntries (k : ℕ) where
  profile : CellReduction.Instantiation.ProfileShapeEntry k
  pressure : CellReduction.Instantiation.PressureShapeEntry k
  adjointFields : CellReduction.Instantiation.AdjointShapeEntry k
  offset : CellReduction.Instantiation.OffsetExpansionEntry k
  shift : ShiftNumbers
  modelForm : CertReduction.ModelFormNumbers
  adjointQuad : CertReduction.AdjointQuadNumbers k
  adjointDefect : Fin k → AdjointDefect.AdjointDefectEntry k
  potentials : PotentialEntries k

structure CellSystemCondition {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k) : Prop where
  cell : CellHypothesis D X R T N.globalError
  shape_valueSets : GivenShape.ShapeValuesFacts D
  entry_conditions : CellLayerEntryConditions D R T N.globalError Y
  enclosure_numbers : ∀ q ∈ D.cert.params, InstanceSplit.EnclosureAdmissibleClauses (D.pieces q) (D.cert.period q)
    (D.bounds q) D.given D.givenHess N.epsSup N.epsGradSup N.ratio
  coerciveL2_ge : Real.sqrt ((1 + N.epsSup + N.epsGradSup / Real.sqrt D.cert.weight) ^ 2 / D.coercivity
    + N.ratio / (D.pieces 0).cμ) / Real.sqrt D.coercivity ≤ D.cert.coerciveL2
  coercivePin_ge : Real.sqrt (D.pinWeight / D.coercivity) ≤ D.cert.coercivePin
  certificate : CertificateClauses D.cert
  instantiation : CellReduction.Instantiation.InstantiationBounded D B.profile B.pressure B.adjointFields
  offset_expansion : CellReduction.Instantiation.IsOffsetExpansionEntry D B.profile B.pressure B.adjointFields B.offset
  shift_numbers : ShiftNumbersBounded D B.profile B.shift
  frozen_form : CertReduction.FrozenFormBounded D.cert B.modelForm
  adjoint_quadratic : CertReduction.AdjointQuadraticBounded D.cert B.adjointQuad
  adjoint_links : CellReduction.Instantiation.AdjointEntryLinks D B.profile B.adjointFields B.offset B.adjointDefect
  potential_entries : PotentialEntriesBounded D B.potentials B.adjointDefect
  adjoint_defect : ∀ j ∈ D.cert.adjointSet, AdjointDefect.AdjointDefectBounded D.cert j (B.adjointDefect j)

end CellLayerSystem

end Breakdown

end
end

section

open Breakdown.CertCell

namespace Breakdown

namespace CellLayerSystem

end CellLayerSystem

end Breakdown

end
