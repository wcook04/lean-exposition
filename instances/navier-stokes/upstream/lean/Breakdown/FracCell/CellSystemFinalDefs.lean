import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.StMesh

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace FinalCellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite
open CellSystem

section FinalParts

open CellFormula

def RotationRateContinuousOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ContinuousOn d.rotationRate (box d.radius)

def MultiplierContinuousOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ContinuousOn d.multiplier (box d.radius)

def ProfileSmoothOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p)

def ProfileSecondOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ∀ p ∈ box d.radius, IsWeakSecondDerivOf (d.gradProfile p) (d.profileSecond p) ∧
      AEStronglyMeasurable (d.profileSecond p) volume

def ProfileDivergenceOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ∀ p ∈ box d.radius, ∀ y, divergenceAt (d.profile p) y = 0

def ProfileClassOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ∀ p ∈ box d.radius, IsClassField d.order (d.profile p)

def ProfileBoundsOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ y,
      ‖d.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖d.gradProfile p y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
        (∀ᵐ z ∂volume, ‖d.profileSecond p z‖ ≤ C * (1 + ‖z‖) ^ (-(3 : ℝ)))

def ProfileDriftOfStatement : Prop :=
  ∀ {k N : ℕ} (α : ℝ) (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d) (_ : α = D.power),
    ∀ p ∈ box d.radius,
      MemLp (driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p)) 2 volume

def ProfilePowerOfStatement : Prop :=
  ∀ {k N : ℕ} (α : ℝ) (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d) (_ : α = D.power),
    ∀ p ∈ box d.radius, IsWeakFractionalPower α (d.profile p) (d.profilePower p)

def ProfileContinuousOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (_ : IsProfileData D) (_ : IsProfileInstance D d),
    ∀ p ∈ box d.radius, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p' ∈ box d.radius,
      dist p' p < δ → ∫ y, entrySq (d.gradProfile p' y - d.gradProfile p y) < ε

def CentreSmoothOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c), ContDiff ℝ 1 c.centre

def CentreSecondOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c),
    IsWeakSecondDerivOf c.centreGrad c.centreSecond ∧ AEStronglyMeasurable c.centreSecond volume

def CentreDivergenceOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c), ∀ y, divergenceAt c.centre y = 0

def CentreClassOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c), IsClassField c.order c.centre

def CentreBoundsOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c),
    ∃ C : ℝ, ∀ y, ‖c.centre y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
      ‖c.centreGrad y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ ‖c.centreSecond y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))

def CentreSecondSymmOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c),
    ∀ y (u w : Space), c.centreSecond y u w = c.centreSecond y w u

def CentreTraceFreeOfStatement : Prop :=
  ∀ {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (_ : IsProfileData D) (_ : IsCentreInstance D c),
    ∀ y, ∑ i : Fin 3, entry (c.centreCurlGrad y) i i = 0

def ActuatorOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k N : ℕ} (A : AuxData k) (_ : IsAuxData P A)
    (d : FracCertData k N) (_ : d.order = P.m) (_ : ∀ i, d.actuator i = A.actuatorField P i),
    (∀ i, MemLp (d.actuator i) 2 volume) ∧ (∀ i, IsClassField d.order (d.actuator i))

def ActuatorGradientOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k : ℕ} (A : AuxData k) (_ : IsAuxData P A) (i : Fin k),
    IsWeakGradientOf (A.actuatorField P i) (fun y => fderiv ℝ (A.actuatorField P i) y) ∧
      AEStronglyMeasurable (fun y => fderiv ℝ (A.actuatorField P i) y) volume ∧
      Integrable (fun y => entrySq (fderiv ℝ (A.actuatorField P i) y))

def ActuatorSupportOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k : ℕ} (A : AuxData k) (_ : IsAuxData P A)
    (region : Set Space) (_ : ∀ y, chartT P y < A.supportBreak → y ∈ region) (i : Fin k),
    ∀ y ∉ region, A.actuatorField P i y = 0

def SmoothPinOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k : ℕ} (A : AuxData k) (_ : IsAuxData P A) (l : Fin k),
    AEStronglyMeasurable (A.smoothPinField P l) volume ∧ Integrable (fun y => entrySq (A.smoothPinField P l y)) ∧
      ContDiff ℝ 1 (A.pinPotentialField P l) ∧ HasCompactSupport (A.pinPotentialField P l) ∧
      (∃ H : Space → (Space →L[ℝ] Space →L[ℝ] Space), IsWeakSecondDerivOf (fun y => fderiv ℝ (A.pinPotentialField P l) y) H ∧
        AEStronglyMeasurable H volume ∧ ∃ C : ℝ, ∀ᵐ y ∂volume, ‖H y‖ ≤ C)

def AdjointSolenoidalOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k N : ℕ} (A : AuxData k) (_ : IsAuxData P A)
    (d : FracCertData k N) (_ : d.order = P.m)
    (_ : ∀ j p, d.adjoint j p = A.adjointField P j p)
    (_ : ∀ j p, d.adjointSharp j p = A.sharpField P d.splitVisc j p),
    ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsSolenoidalL2 (d.adjoint j p) ∧
      IsClassField d.order (d.adjoint j p) ∧ MemLp (d.adjointSharp j p) 2 volume

def AdjointRegularOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k : ℕ} (A : AuxData k) (_ : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ),
    CellCert.Reduction.IsAdjointRegular (A.adjointField P j p) (fun y => fderiv ℝ (A.adjointField P j p) y)
      (fun y => fderiv ℝ (fun z => fderiv ℝ (A.adjointField P j p) z) y)

def AdjointDualCoreOfGivenStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k : ℕ} (A : AuxData k) (_ : IsAuxData P A)
    (ν : ℝ) (j : Fin k) (p : Fin k → ℝ),
    IsWeakGradientOf (A.adjointField P j p) (fun y => fderiv ℝ (A.adjointField P j p) y) ∧
      (AEStronglyMeasurable (A.adjointField P j p) volume ∧
        AEStronglyMeasurable (fun y => fderiv ℝ (A.adjointField P j p) y) volume) ∧
      (∃ L : Space → Space, CellCert.Reduction.IsWeakNegTraceOf
          (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) L ∧
        MemLp (fun y => ‖y‖ • L y) 2 volume) ∧
      MemLp (A.sharpField P ν j p) 2 volume ∧
      IsWeakGradientOf (A.sharpField P ν j p) (fun y => fderiv ℝ (A.sharpField P ν j p) y) ∧
      AEStronglyMeasurable (fun y => fderiv ℝ (A.sharpField P ν j p) y) volume ∧
      Integrable (fun y => entrySq (fderiv ℝ (A.sharpField P ν j p) y))

def SupportRegionOfStatement : Prop :=
  ∀ (P : ChartParams) (_ : IsChartParams P) {k : ℕ} (A : AuxData k) (_ : IsAuxData P A)
    (region : Set Space) (R : ℝ) (_ : ∀ y : Space, ‖y‖ ≤ R → y ∈ region)
    (_ : P.L0 * A.supportBreak / (1 - A.supportBreak) ≤ R),
    ∀ y, chartT P y < A.supportBreak → y ∈ region

def CellRegionClausesStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (_ : IsCellMesh M)
    (_ : c.cellRegion = M.region),
    MeasurableSet c.cellRegion ∧ Bornology.IsBounded c.cellRegion ∧
      ∀ y ∈ c.cellRegion, turnStep c.order y ∈ c.cellRegion ∧ mirror y ∈ c.cellRegion

def ModelClausesStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (_ : IsCellMesh M) (_ : IsModelData D) (_ : IsModelInstance c M D) (_ : IsCentreRegular c),
    (AEStronglyMeasurable c.modelVelocity volume ∧ AEStronglyMeasurable c.modelCurl volume ∧
      AEStronglyMeasurable c.modelStrain volume ∧ AEStronglyMeasurable c.modelCurlGrad volume) ∧
    (∃ C : ℝ, ∀ y ∈ c.cellRegion, ‖c.modelVelocity y‖ ≤ C ∧ ‖c.modelCurl y‖ ≤ C ∧
      ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C) ∧
    (∀ y ∉ c.cellRegion, c.modelVelocity y = 0 ∧ c.modelCurl y = 0) ∧
    (∀ y ∉ c.cellRegion, c.modelStrain y = c.centreStrain y ∧ c.modelCurlGrad y = c.centreCurlGrad y) ∧
    (∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)) ∧
    (∀ y, ∑ i : Fin 3, entry (c.modelCurlGrad y) i i = 0)

def ModelAuxClausesStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (_ : IsCellMesh M) (_ : IsModelInstance c M D),
    (∀ i, MemLp (c.modelActuator i) 2 volume ∧ ∀ y ∉ c.cellRegion, c.modelActuator i y = 0) ∧
    (∀ i, AEStronglyMeasurable (c.modelActuatorGrad i) volume ∧
      Integrable (fun y => entrySq (c.modelActuatorGrad i y)) ∧ ∀ y ∉ c.cellRegion, c.modelActuatorGrad i y = 0) ∧
    (∀ i, AEStronglyMeasurable (c.modelPinField i) volume ∧
      Integrable (fun y => entrySq (c.modelPinField i y)) ∧ ∀ y ∉ c.cellRegion, c.modelPinField i y = 0) ∧
    (∀ i, AEStronglyMeasurable (c.pin i) volume ∧ Integrable (fun y => entrySq (c.pin i y))) ∧
    (∀ i, ∀ y ∉ c.cellRegion, c.pin i y = 0)

def RowClausesStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (_ : IsCellMesh M) (_ : IsRowData R c.order c.rowMax) (_ : IsRowInstance c M R) (_ : 0 < c.order),
    (∀ a, MemLp (c.row a) 2 volume) ∧
    (∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0) ∧
    (∀ a, ∃ r : ℝ, ∀ y, r < ‖y‖ → c.row a y = 0) ∧
    (∀ a, IsClassField c.order (c.row a)) ∧
    (∀ a, 0 < c.rowWeight a) ∧ (∀ a, c.rowWeight a ≤ c.rowMax) ∧
    (∀ a, ∀ y ∉ c.cellRegion, c.row a y = 0) ∧
    Measurable c.cellWeight ∧ (∀ y, 0 ≤ c.cellWeight y) ∧ (∀ y, c.cellWeight y ≤ c.rowMax) ∧
    (∀ y ∉ c.cellRegion, c.cellWeight y = 0) ∧
    (∀ F : Space → Space, MemLp F 2 volume →
      c.toFracCertData.rows F ^ 2 ≤ ∫ y, c.cellWeight y * ‖F y‖ ^ 2)

def WeightClausesStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (w₀ : ℝ) (_ : c.weight = fun _ => w₀)
    (_ : 0 < w₀) (_ : c.weightMin = w₀) (_ : c.weightMax = w₀),
    Measurable c.weight ∧ 0 < c.weightMin ∧ (∀ y, c.weightMin ≤ c.weight y) ∧ (∀ y, c.weight y ≤ c.weightMax) ∧
      IsClassScalar c.order c.weight ∧ ∀ K : CellBox, ∀ p ∈ K.rect, ∀ θ : ℝ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p

def ExteriorClausesStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (_ : IsCellMesh M)
    (_ : c.cellRegion = M.region) (e : Exterior.ExteriorData) (_ : e.radius = boxRadius M.outerSize)
    (_ : e.radiusMin = M.outerSize) (_ : e.radiusMax = Real.sqrt 2 * M.outerSize),
    Measurable e.radius ∧ 0 < e.radiusMin ∧ (∀ y, e.radiusMin ≤ e.radius y ∧ e.radius y ≤ e.radiusMax) ∧
      (∀ (t : ℝ) (y : Space), 0 < t → e.radius (t • y) = e.radius y) ∧
      c.cellRegionᶜ =ᵐ[volume] {y : Space | e.radius y < ‖y‖}

def BallSubsetRegionStatement : Prop :=
  ∀ (M : CellMesh) (_ : IsCellMesh M),
    ∀ y : Space, ‖y‖ ≤ M.outerSize → y ∈ M.region

def RowsInCellOfStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (_ : IsCellMesh M) (_ : IsRowData RD c.order c.rowMax)
    (_ : IsRowsInstance c M RD K₀ R),
    ∀ a ∈ R.rowSet, ∀ y ∉ (M.box K₀).solid, c.row a y = 0

def RowModesOfStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (_ : IsCellMesh M) (_ : IsRowData RD c.order c.rowMax)
    (_ : IsRowsInstance c M RD K₀ R) (_ : 0 < c.order),
    ∀ a ∈ R.rowSet, ∀ n ∉ R.rowModes, ∀ p ∈ (M.box K₀).rect, CellScalars.rowMode c a n p = 0

def RowModeOfOfStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (_ : IsCellMesh M) (_ : IsRowData RD c.order c.rowMax)
    (_ : IsRowsInstance c M RD K₀ R) (_ : 0 < c.order),
    ∀ a ∈ R.rowSet, ∀ n, n ≠ R.rowModeOf a → n ≠ -R.rowModeOf a → ∀ p ∈ (M.box K₀).rect,
      CellScalars.rowMode c a n p = 0

def RowTracesOfStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (_ : IsCellMesh M) (_ : IsRowData RD c.order c.rowMax)
    (_ : IsRowsInstance c M RD K₀ R) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (_ : IsPressureLayout c (M.box K₀) S B L) (_ : RD.degree ≤ L.degSide),
    ∀ a ∈ R.rowSet, ∀ s n i, ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
        ∀ p ∈ (M.box K₀).rect, ((L.segment s).radial → p.1 = (L.segment s).level → CellFormula.rowModeVec c a n p i = Pl p.2) ∧
          (¬ (L.segment s).radial → p.2 = (L.segment s).level → CellFormula.rowModeVec c a n p i = Pl p.1)

def RowNormalTracesOfStatement : Prop :=
  ∀ {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (_ : IsCellMesh M) (_ : IsRowData RD c.order c.rowMax)
    (_ : IsRowsInstance c M RD K₀ R) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (_ : IsPressureLayout c (M.box K₀) S B L) (_ : RD.degree ≤ L.degSide),
    ∀ a ∈ R.rowSet, ∀ s n, ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin L.degSide → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
        ∀ p ∈ (M.box K₀).rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level →
            CellFormula.rowModeVec c a n p 0 = Pl p.2) ∧
          (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → CellFormula.rowModeVec c a n p 2 = Pl p.1)

def RowsInBlockOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (_ : IsCellMesh M) (_ : IsRowData RD c.order c.rowMax) (_ : IsRowInstance c M RD) (a : Fin N),
    Spectral.IsBlockField (rowBlock M RD c.order a) (c.row a)

structure IsGivenBase (α : ℝ) {k N : ℕ} (d : FracCertData k N) : Prop where
  weight_measurable : Measurable d.weight
  weightMin_pos : 0 < d.weightMin
  weight_lower : ∀ y, d.weightMin ≤ d.weight y
  weight_upper : ∀ y, d.weight y ≤ d.weightMax
  weight_class : IsClassScalar d.order d.weight
  rotationRate_continuous : ContinuousOn d.rotationRate (box d.radius)
  multiplier_continuous : ContinuousOn d.multiplier (box d.radius)
  profile_smooth : ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p)
  profile_second : ∀ p ∈ box d.radius, IsWeakSecondDerivOf (d.gradProfile p) (d.profileSecond p) ∧
    AEStronglyMeasurable (d.profileSecond p) volume
  profile_divergence : ∀ p ∈ box d.radius, ∀ y, divergenceAt (d.profile p) y = 0
  profile_class : ∀ p ∈ box d.radius, IsClassField d.order (d.profile p)
  profile_bounds : ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ y,
    ‖d.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖d.gradProfile p y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
      (∀ᵐ z ∂volume, ‖d.profileSecond p z‖ ≤ C * (1 + ‖z‖) ^ (-(3 : ℝ)))
  profile_drift : ∀ p ∈ box d.radius,
    MemLp (driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p)) 2 volume
  profile_power : ∀ p ∈ box d.radius, IsWeakFractionalPower α (d.profile p) (d.profilePower p)
  profile_continuous : ∀ p ∈ box d.radius, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p' ∈ box d.radius,
    dist p' p < δ → ∫ y, entrySq (d.gradProfile p' y - d.gradProfile p y) < ε
  actuator_two : ∀ i, MemLp (d.actuator i) 2 volume
  actuator_class : ∀ i, IsClassField d.order (d.actuator i)
  pin_measurable : ∀ i, AEStronglyMeasurable (d.pin i) volume ∧ AEStronglyMeasurable (d.smoothPin i) volume
  pin_two : ∀ i, Integrable (fun y => entrySq (d.pin i y)) ∧ Integrable (fun y => entrySq (d.smoothPin i y))
  row_two : ∀ a, MemLp (d.row a) 2 volume
  row_orthonormal : ∀ a b, l2Pair (d.row a) (d.row b) = if a = b then 1 else 0
  row_support : ∀ a, ∃ R : ℝ, ∀ y, R < ‖y‖ → d.row a y = 0
  row_class : ∀ a, IsClassField d.order (d.row a)
  rowWeight_pos : ∀ a, 0 < d.rowWeight a
  rowWeight_le : ∀ a, d.rowWeight a ≤ d.rowMax
  adjoint_solenoidal : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsSolenoidalL2 (d.adjoint j p) ∧
    IsClassField d.order (d.adjoint j p) ∧ MemLp (d.adjointSharp j p) 2 volume

structure IsGivenCell {k N : ℕ} (c : FracCellData k N) : Prop where
  cellRegion_measurable : MeasurableSet c.cellRegion
  cellRegion_bounded : Bornology.IsBounded c.cellRegion
  cellRegion_class : ∀ y ∈ c.cellRegion, turnStep c.order y ∈ c.cellRegion ∧ mirror y ∈ c.cellRegion
  cellWeight_measurable : Measurable c.cellWeight
  cellWeight_nonneg : ∀ y, 0 ≤ c.cellWeight y
  cellWeight_le : ∀ y, c.cellWeight y ≤ c.rowMax
  cellWeight_support : ∀ y ∉ c.cellRegion, c.cellWeight y = 0
  rows_dominated : ∀ F : Space → Space, MemLp F 2 volume →
    c.toFracCertData.rows F ^ 2 ≤ ∫ y, c.cellWeight y * ‖F y‖ ^ 2
  row_in_cells : ∀ a, ∀ y ∉ c.cellRegion, c.row a y = 0
  centre_smooth : ContDiff ℝ 1 c.centre
  centre_second : IsWeakSecondDerivOf c.centreGrad c.centreSecond ∧ AEStronglyMeasurable c.centreSecond volume
  centre_divergence : ∀ y, divergenceAt c.centre y = 0
  centre_class : IsClassField c.order c.centre
  centre_bounds : ∃ C : ℝ, ∀ y, ‖c.centre y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
    ‖c.centreGrad y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ ‖c.centreSecond y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))
  model_measurable : AEStronglyMeasurable c.modelVelocity volume ∧ AEStronglyMeasurable c.modelCurl volume ∧
    AEStronglyMeasurable c.modelStrain volume ∧ AEStronglyMeasurable c.modelCurlGrad volume
  model_bounded : ∃ C : ℝ, ∀ y ∈ c.cellRegion, ‖c.modelVelocity y‖ ≤ C ∧ ‖c.modelCurl y‖ ≤ C ∧
    ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C
  model_in_cells : ∀ y ∉ c.cellRegion, c.modelVelocity y = 0 ∧ c.modelCurl y = 0
  model_outside : ∀ y ∉ c.cellRegion, c.modelStrain y = c.centreStrain y ∧ c.modelCurlGrad y = c.centreCurlGrad y
  modelStrain_symmetric : ∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)
  modelCurlGrad_trace : ∀ y, ∑ i : Fin 3, entry (c.modelCurlGrad y) i i = 0
  modelActuator_data : ∀ i, MemLp (c.modelActuator i) 2 volume ∧ ∀ y ∉ c.cellRegion, c.modelActuator i y = 0
  modelActuatorGrad_data : ∀ i, AEStronglyMeasurable (c.modelActuatorGrad i) volume ∧
    Integrable (fun y => entrySq (c.modelActuatorGrad i y)) ∧ ∀ y ∉ c.cellRegion, c.modelActuatorGrad i y = 0
  modelPin_data : ∀ i, AEStronglyMeasurable (c.modelPinField i) volume ∧
    Integrable (fun y => entrySq (c.modelPinField i y)) ∧ ∀ y ∉ c.cellRegion, c.modelPinField i y = 0
  actuator_gradient : ∀ i, IsWeakGradientOf (c.actuator i) (c.actuatorGrad i) ∧
    AEStronglyMeasurable (c.actuatorGrad i) volume ∧ Integrable (fun y => entrySq (c.actuatorGrad i y))
  actuator_in_cells : ∀ i, ∀ y ∉ c.cellRegion, c.actuator i y = 0
  pin_in_cells : ∀ i, ∀ y ∉ c.cellRegion, c.pin i y = 0

structure IsGivenExterior (α : ℝ) {k N : ℕ} (c : FracCellData k N) (e : ExteriorData) : Prop where
  radius_measurable : Measurable e.radius
  radiusMin_pos : 0 < e.radiusMin
  radius_between : ∀ y, e.radiusMin ≤ e.radius y ∧ e.radius y ≤ e.radiusMax
  radius_homogeneous : ∀ (t : ℝ) (y : Space), 0 < t → e.radius (t • y) = e.radius y
  exterior_eq : c.cellRegionᶜ =ᵐ[volume] {y : Space | e.radius y < ‖y‖}
  curlGrad_traceFree : ∀ y ∉ c.cellRegion, ∑ i : Fin 3, entry (c.centreCurlGrad y) i i = 0

structure IsGivenExtra {k N : ℕ} (d : FracCertData k N) : Prop where
  adjoint_measurable : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, AEStronglyMeasurable (d.adjoint j p) volume
  profile_decay : ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p) ∧ (∀ y, divergenceAt (d.profile p) y = 0) ∧
    ∃ K : ℝ, ∀ y, ‖d.profile p y‖ ≤ K * (1 + ‖y‖)⁻¹ ∧ ‖d.gradProfile p y‖ ≤ K * (1 + ‖y‖) ^ (-2 : ℝ)
  adjoint_regular : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius,
    IsAdjointRegular (d.adjoint j p) (fun y => fderiv ℝ (d.adjoint j p) y)
      (fun y => fderiv ℝ (fun z => fderiv ℝ (d.adjoint j p) z) y) ∧ AEStronglyMeasurable (d.adjoint j p) volume

def KernelBoundOfCellSumsStatement : Prop :=
  ∀ (m : ℕ) (V : Space → ℝ) (D : CellSumData), IsCellSumData m V D → ∀ Λ : ℝ, (∀ a, D.boxBound a ≤ Λ) → KernelBound V Λ

def AdjointLocalOfDualStatement : Prop :=
  ∀ (Hc : ℝ)
    (α : ℝ) (_ : 1 < α) (_ : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (_ : InverseSquareConstStatement d.order Hc) (_ : 0 < d.weightMin) (_ : ∀ y, d.weightMin ≤ d.weight y)
    (_ : Measurable d.weight) (_ : ∀ y, d.weight y ≤ d.weightMax)
    (_ : ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p) ∧ (∀ y, divergenceAt (d.profile p) y = 0) ∧
      ∃ K : ℝ, ∀ y, ‖d.profile p y‖ ≤ K * (1 + ‖y‖)⁻¹ ∧ ‖d.gradProfile p y‖ ≤ K * (1 + ‖y‖) ^ (-2 : ℝ))
    (_ : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsSolenoidalL2 (d.adjoint j p))
    (D : Fin k → (Fin k → ℝ) → AdjointDual k)
    (_ : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsAdjointDual α d j p (D j p))
    (_ : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius,
      Real.sqrt ((D j p).dualBound ^ 2 + ((D j p).potentialScale * (D j p).potentialBound + (D j p).fluxBound
        + (D j p).inverseSquareBound
        + ∑ i ∈ Finset.univ \ (D j p).exactSet, |p i| * ((D j p).shiftBound i + Hc * (D j p).shiftGradBound i)) ^ 2
          / d.weightMin) ≤ d.adjointLocal j p),
    ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H →
      ∀ P, IsWeakFractionalPower α v P → MemLp (driftField α (d.rotationRate p) v G) 2 volume →
        |l2Pair (d.localField α p v G H 0) (d.adjoint j p) + l2Pair (negSecondTrace H) (d.adjointSharp j p)
          - ∑ l, d.adjointPin j p l * SteadyCert.pinValue (d.smoothPin l) G| ≤ d.adjointLocal j p * Real.sqrt (d.energy G H)

def CellOfSystemStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      IsCellData (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes (X.cell K₂).rows ∧
      IsCellCoords (501 / 500) c X.split K₂ (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes
        (X.cell K₂).rows (X.mesh.coords K₂) ∧
      ∀ a, X.split.rowCell a = K₂ ↔ a ∈ (X.cell K₂).rows.rowSet

def SplitGeometryStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X →
      (∀ K, MeasurableSet (X.split.cell K)) ∧
      (∀ K L, K ≠ L → volume (X.split.cell K ∩ X.split.cell L) = 0) ∧
      ((⋃ K, X.split.cell K) = c.cellRegion) ∧
      (∀ a, ∀ y ∉ X.split.cell (X.split.rowCell a), c.row a y = 0)

open CellFormula

structure CellDataRest (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (Cl : CellClasses) {slots : ℕ} (R : CellRows N slots k) : Prop where
  multiplier_bound : ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
    (∑ a ∈ R.rowSet, μ a ^ 2 / (4 * Real.pi * c.rowWeight a)) + (∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2)
        + CellScalars.rowSquare c K S R B μ (fun _ _ => True)
        + CellScalars.rowSquareFar c K S R B μ / (1 - R.farShare)
      ≤ ∑ a ∈ R.rowSet, ∑ b ∈ R.rowSet, μ a * R.multiplierMatrix a b * μ b
  box : IsCellBox K
  scalars : IsCellScalars α c K S
  bases : IsCellBases K B
  weight_axisymmetric : ∀ p ∈ K.rect, ∀ θ : ℝ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p
  model_mirror : ∀ y ∈ K.solid, cylHeight y ≠ 0 → c.modelVelocity (mirror y) = mirror (c.modelVelocity y) ∧
    c.modelCurl (mirror y) = -mirror (c.modelCurl y) ∧
    (∀ u, c.modelStrain (mirror y) u = mirror (c.modelStrain y (mirror u))) ∧
    (∀ u, c.modelCurlGrad (mirror y) u = -mirror (c.modelCurlGrad y (mirror u))) ∧
    ∀ i, (∀ u, c.modelActuatorGrad i (mirror y) u = mirror (c.modelActuatorGrad i y (mirror u))) ∧
      (∀ u, c.modelPinField i (mirror y) u = mirror (c.modelPinField i y (mirror u)))
  solid_in_region : K.solid ⊆ c.cellRegion
  model_strain_symm : ∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)
  actuator_memLp : ∀ i, MemLp (c.modelActuator i) 2 volume
  curlGrad_traceFree : ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ θ : ℝ, ∑ i : Fin 3, entry (c.modelCurlGrad (cylPoint p.1 θ p.2)) i i = 0
  class_regular : ∀ i, Measurable (Cl.strainDev i) ∧ Measurable (Cl.gradDev i) ∧ Measurable (Cl.velocityDev i) ∧
    Measurable (Cl.curlDev i) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C ∧ |Cl.gradDev i p| ≤ C ∧
      |Cl.velocityDev i p| ≤ C ∧ |Cl.curlDev i p| ≤ C
  linear_modes : ∀ n ∉ R.yModes, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ i,
    modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0
  rows_in_cell : ∀ a ∈ R.rowSet, ∀ y ∉ K.solid, c.row a y = 0
  row_modes : ∀ a ∈ R.rowSet, ∀ n ∉ R.rowModes, ∀ p ∈ K.rect, CellScalars.rowMode c a n p = 0
  row_mode_of : ∀ a ∈ R.rowSet, ∀ n, n ≠ R.rowModeOf a → n ≠ -R.rowModeOf a → ∀ p ∈ K.rect,
    CellScalars.rowMode c a n p = 0
  rowWeight_pos : ∀ a ∈ R.rowSet, 0 < c.rowWeight a
  class_cover : ∀ n ∈ S.resolved, ∀ n' ∉ S.resolved ∪ S.band,
    (∃ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 ∧ (modeVec c.order (n - n') c.modelVelocity p.1 p.2 ≠ 0 ∨
      modeVec c.order (n - n') c.modelCurl p.1 p.2 ≠ 0 ∨
      modeMat c.order (n - n') c.modelStrain p.1 p.2 ≠ 0 ∨ modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 ≠ 0)) →
    ∃ i, n - n' ∈ Cl.modes i
  far_bound : ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
    CellScalars.farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R ≤ CellScalars.farFormValue c K S R B x ζ

structure CellCoordsRest (α : ℝ) {k N : ℕ} (c : FracCellData k N) (Sp : CellSplit k N) (K₂ : Fin Sp.cellCount)
    (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N Sp.slots k)
    (C : CellCoords k Sp.slots) : Prop where
  visc_pos : 0 < c.splitVisc
  rows_shape : IsRowShape c K S R
  gauge_spec : IsGaugeSpec C.layout C.gaugeSpec
  gauge_linear : ∀ (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
    C.gaugeLeft (a • x + b • y) = a * C.gaugeLeft x + b * C.gaugeLeft y ∧
      C.gaugeRight (a • x + b • y) = a * C.gaugeRight x + b * C.gaugeRight y
  edge_jump : ∀ e, C.gaugeSpec.edge = some e → ∀ x, IsAdmissible c x →
    C.gaugeRight x = C.gaugeLeft x + C.layout.gaugeJump C.gaugeSpec x
  root_zero : ∀ r ∈ C.gaugeSpec.roots, ∀ x, IsAdmissible c x → C.layout.rootShifted C.gaugeLeft C.gaugeRight x r = 0
  skeleton_slot : ∀ x, IsAdmissible c x → ∀ j, ∑ i, C.Tmap j i * Sp.moment x i =
    C.layout.realPart (C.layout.shiftedData (C.layout.gaugeShiftOf C.gaugeLeft C.gaugeRight) x) ((systemSkeletonCoords C.layout C.param).equivFin.symm j).1 /
      presetScale C.layout c.splitVisc ((systemSkeletonCoords C.layout C.param).equivFin.symm j).1.1

def CellDataRestStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      CellDataRest (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes
        (X.cell K₂).rows

def CellCoordsRestStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      CellCoordsRest (501 / 500) c X.split K₂ (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases
        (X.cell K₂).classes (X.cell K₂).rows (X.mesh.coords K₂)

def RowsHereStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ (K₂ : Fin X.split.cellCount) a,
      X.split.rowCell a = K₂ ↔ a ∈ (X.cell K₂).rows.rowSet

open CellFormula

structure CellDataBoxPart (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (Cl : CellClasses) {slots : ℕ} (R : CellRows N slots k) : Prop where
  box : IsCellBox K
  scalars : IsCellScalars α c K S
  bases : IsCellBases K B

def CellDataBoxStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      CellDataBoxPart (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes
        (X.cell K₂).rows

structure CellDataModelPart (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (Cl : CellClasses) {slots : ℕ} (R : CellRows N slots k) : Prop where
  weight_axisymmetric : ∀ p ∈ K.rect, ∀ θ : ℝ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p
  model_mirror : ∀ y ∈ K.solid, cylHeight y ≠ 0 → c.modelVelocity (mirror y) = mirror (c.modelVelocity y) ∧
    c.modelCurl (mirror y) = -mirror (c.modelCurl y) ∧
    (∀ u, c.modelStrain (mirror y) u = mirror (c.modelStrain y (mirror u))) ∧
    (∀ u, c.modelCurlGrad (mirror y) u = -mirror (c.modelCurlGrad y (mirror u))) ∧
    ∀ i, (∀ u, c.modelActuatorGrad i (mirror y) u = mirror (c.modelActuatorGrad i y (mirror u))) ∧
      (∀ u, c.modelPinField i (mirror y) u = mirror (c.modelPinField i y (mirror u)))
  solid_in_region : K.solid ⊆ c.cellRegion
  model_strain_symm : ∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)
  actuator_memLp : ∀ i, MemLp (c.modelActuator i) 2 volume
  curlGrad_traceFree : ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ θ : ℝ, ∑ i : Fin 3, entry (c.modelCurlGrad (cylPoint p.1 θ p.2)) i i = 0
  class_regular : ∀ i, Measurable (Cl.strainDev i) ∧ Measurable (Cl.gradDev i) ∧ Measurable (Cl.velocityDev i) ∧
    Measurable (Cl.curlDev i) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C ∧ |Cl.gradDev i p| ≤ C ∧
      |Cl.velocityDev i p| ≤ C ∧ |Cl.curlDev i p| ≤ C
  linear_modes : ∀ n ∉ R.yModes, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ i,
    modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0

def CellDataModelStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      CellDataModelPart (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes
        (X.cell K₂).rows

structure CellDataRowsPart (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (Cl : CellClasses) {slots : ℕ} (R : CellRows N slots k) : Prop where
  rows_in_cell : ∀ a ∈ R.rowSet, ∀ y ∉ K.solid, c.row a y = 0
  row_modes : ∀ a ∈ R.rowSet, ∀ n ∉ R.rowModes, ∀ p ∈ K.rect, CellScalars.rowMode c a n p = 0
  row_mode_of : ∀ a ∈ R.rowSet, ∀ n, n ≠ R.rowModeOf a → n ≠ -R.rowModeOf a → ∀ p ∈ K.rect,
    CellScalars.rowMode c a n p = 0
  rowWeight_pos : ∀ a ∈ R.rowSet, 0 < c.rowWeight a

def CellDataRowsStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      CellDataRowsPart (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes
        (X.cell K₂).rows

structure CellDataFarPart (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (Cl : CellClasses) {slots : ℕ} (R : CellRows N slots k) : Prop where
  class_cover : ∀ n ∈ S.resolved, ∀ n' ∉ S.resolved ∪ S.band,
    (∃ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 ∧ (modeVec c.order (n - n') c.modelVelocity p.1 p.2 ≠ 0 ∨
      modeVec c.order (n - n') c.modelCurl p.1 p.2 ≠ 0 ∨
      modeMat c.order (n - n') c.modelStrain p.1 p.2 ≠ 0 ∨ modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 ≠ 0)) →
    ∃ i, n - n' ∈ Cl.modes i
  far_bound : ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
    CellScalars.farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R ≤ CellScalars.farFormValue c K S R B x ζ
  multiplier_bound : ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
    (∑ a ∈ R.rowSet, μ a ^ 2 / (4 * Real.pi * c.rowWeight a)) + (∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2)
        + CellScalars.rowSquare c K S R B μ (fun _ _ => True)
        + CellScalars.rowSquareFar c K S R B μ / (1 - R.farShare)
      ≤ ∑ a ∈ R.rowSet, ∑ b ∈ R.rowSet, μ a * R.multiplierMatrix a b * μ b

def CellDataFarStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      CellDataFarPart (501 / 500) c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).bases (X.cell K₂).classes
        (X.cell K₂).rows

def CellsApartStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X → ∀ K L, K ≠ L → volume (X.split.cell K ∩ X.split.cell L) = 0

def AxisGradientAllStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (X : CellSystemData k N M), CellSystemCondition c D A M MD RD X →
      ∀ q, AxisGradientBound q (X.spectral.axisGradient q)

def RowTurnDataOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (rate : ℝ) (hS : IsGivenData c D A M MD RD)
    (hN : IsRowTurnNumbers c M RD rate),
    IsRowTurnData c (turnOf RD c.order rate)

def SumWeightsOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k) (M : CellMesh)
    (MD : ModelData M k) (RD : RowData M N) (hS : IsGivenData c D A M MD RD) (w : ℝ) (hw : 0 < w)
    (step : Fin k → ℝ) (hamp : ∀ i, Pi.single i 1 ∈ D.index),
    IsSumWeight c.order (fun y => ‖c.curlGradError y‖ ^ 2) ∧
    IsSumWeight c.order (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2) ∧
    (∀ i β, IsSumWeight c.order (gradSq (ampField D step i β))) ∧
    (∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ β, IsSumWeight c.order (gradSq (fieldOf D.chart (D.part μ) β))) ∧
    (∀ β, IsSumWeight c.order (gradSq (phaseCurvField D.chart (D.part 0) β))) ∧
    (∀ j ∈ c.activeSet, ∀ γ ∈ (A.adjointFamily j).indices, ∀ β,
      IsSumWeight c.order (fun y => ‖fieldOf D.chart ((A.adjointFamily j).coef γ) β y‖ ^ 2 / w))

def AdjointDualStructureOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N)
    (h : IsGivenData c D A M MD RD) (hpow : D.power = 501 / 500) (hamp : ∀ i, Pi.single i 1 ∈ D.index)
    (nums : AdjointNumbers k) (j : Fin k) (p : Fin k → ℝ),
    IsAdjointDualStructure (501 / 500) c.toFracCertData j p
      (adjointDualOf (501 / 500) D c.toFracCertData A c.splitVisc j p nums)

def CentreKernelSplitOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X),
    ∀ p ∈ box c.radius, KernelBound (fun y => ‖c.gradProfile p y - c.centreGrad y‖ ^ 2) (X.centreKernel ^ 2)

def AdjointKernelOfStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X),
    ∀ j ∈ c.activeSet, ∀ p ∈ box c.radius, KernelBound (adjointWeightOf c X.weightValue j p) (X.adjointKernel j)

def RowPolynomialOfSystemStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M),
    CellSystemCondition c D A M MD RD X → ∀ K₂ : Fin X.split.cellCount,
      IsRowPolynomial c (X.cell K₂).box (X.cell K₂).scalars (X.cell K₂).rows (X.cell K₂).rowDegree

end FinalParts

end FinalCellSystem

end CellCert

end Breakdown
