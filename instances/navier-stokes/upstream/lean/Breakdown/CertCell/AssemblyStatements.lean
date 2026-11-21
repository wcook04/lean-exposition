import Breakdown.CertCell.GaugeKeyStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

section Residual

variable {k : ℕ} {C : Type} {nE nM : ℕ}

variable (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def bandProfile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    Fin 12 → ℂ :=
  pairVec (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)

def bandQuad (K : Fin D.mesh.count) (w : ℤ × ℤ → Fin 12 → ℝ) (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, w ι j * ‖σ ι p j‖ ^ 2

def bandLinear {V : Type} [Fintype V] (K : Fin D.mesh.count) (S : ℤ × ℤ → V → ℝ × ℝ → Fin 12 → ℂ)
    (x : V → ℂ) (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
    p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField (S ι) x p j) * σ ι p j).re)

def BandSquareIntegrable (K : Fin D.mesh.count) (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : Prop :=
  ∀ ι ∈ D.mesh.band K, (∀ j, AEStronglyMeasurable (fun p => σ ι p j) (volume.restrict (D.mesh.box K).rect)) ∧
    IntegrableOn (fun p => p.1 * ∑ j, ‖σ ι p j‖ ^ 2) (D.mesh.box K).rect

def rowVector {V : Type} [Fintype V] (K : Fin D.mesh.count) (B : CellBlocks V) (x : V → ℂ)
    (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : Fin B.rowCount → ℂ :=
  B.rowMap *ᵥ x + fun i => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
    (p.1 : ℂ) * ∑ j, σ ι p j * (starRingEnd ℂ) (B.rowBand i ι p j)

def tailStrainSq (K : Fin D.mesh.count) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (D.mesh.box K).tailNormSq ((R.layouts K).layout ι).degCoef (fun p => gradAt D.azimuthOrder ι G a b p)

def tailVelSq (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space) : ℝ :=
  ∑ a : Fin 3,
    (D.mesh.box K).tailNormSq (((R.layouts K).layout ι).degCoef - 1) (fun p => velAt D.azimuthOrder ι v a p)

def tailCurlSq (K : Fin D.mesh.count) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ i : Fin 3,
    (D.mesh.box K).tailNormSq ((R.layouts K).layout ι).degCoef (fun p => curlComp (gradArray D.azimuthOrder ι G p) i)

def modeCurlSq (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 3, ‖curlComp (gradArray D.azimuthOrder ι G p) i‖ ^ 2

def modeStrainSq (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2

def modeVelSq (ι : ℤ × ℤ) (v : ℝ → Space → Space) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ‖velAt D.azimuthOrder ι v a p‖ ^ 2

def rowLeakAmount {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ B.leakModes, ∫ p in (D.mesh.box K).rect,
    p.1 * (B.leakCurl ι * modeCurlSq D ι G p + B.leakVel ι * modeVelSq D ι v p)

def pairingLeakAmount {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ B.leakModes, ∫ p in (D.mesh.box K).rect, p.1 * (B.leakStrain ι * modeStrainSq D ι G p)

def boxAmount (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect, p.1 *
    (R.leaves K).boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)

def bandAllowance (K : Fin D.mesh.count) (cCurl cVel : ℤ × ℤ → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
    p.1 * (cCurl ι * modeCurlSq D ι G p + cVel ι * modeVelSq D ι v p)

def creditAmount (K : Fin D.mesh.count) (v : ℝ → Space → Space) : ℝ :=
  CellCalculus.creditShare D R K v

def pairSlackAmount (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ)) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  CellCalculus.pairStrainSlack D K (S ∩ R.pairSlackLabels K) (R.pairSlackWeight K) G

def deactSlackLabels (K : Fin D.mesh.count) : Finset (ℤ × ℤ) :=
  (R.pairSlackLabels K).filter (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K)

def kappaSq {V : Type} [Fintype V] {k : ℕ} (x : V ⊕ (Fin k ⊕ Fin k) → ℂ) : ℝ :=
  ∑ i, ‖x (Sum.inr (Sum.inl i))‖ ^ 2

def resolvedAmount (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect, D.labelDensity q v G H ι p * p.1

def stretchAmount (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∫ p in (D.mesh.box K).rect, D.meanStretch v G p * p.1

open Classical in
def offChargeAmount (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑' ι : ℤ × ℤ, if ι ∈ D.mesh.resolved K then 0 else ∫ p in (D.mesh.box K).rect,
    (D.labelDensity q v G H ι p
      - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (R.entryCharges K ι) D.azimuthOrder ι v G H p) * p.1

structure IsCellTuple (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (κ : Fin k → ℝ) (F Pg : ℝ → Space → Space) : Prop where
  param : q ∈ D.cert.params
  perturbation : IsPerturbation D.cert.symmetries (D.cert.period q) v G H g
  pressure : IsPeriodicPressure Pg
  right_side : IsStrongRightSide D.given D.cert.actuator κ v G H g F Pg
  pos_finite : cellPos D K q v G H < ⊤
  right_measurable : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume
  right_periodic : IsTimePeriodic F
  right_finite : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤
  pressure_flip : ∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)

def CellPiecesFinite : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    cellNeg D K q v G H < ⊤ ∧ offPos D K q (D.charges (some K)) (R.entryCharges K) v G H < ⊤ ∧
      offNeg D K q (D.charges (some K)) (R.entryCharges K) v G H < ⊤

def AllocationSplit : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    (cellPos D K q v G H).toReal - (cellNeg D K q v G H).toReal
        - (offPos D K q (D.charges (some K)) (R.entryCharges K) v G H).toReal
        + (offNeg D K q (D.charges (some K)) (R.entryCharges K) v G H).toReal
      = resolvedAmount D K q v G H + offChargeAmount D R K q v G H + stretchAmount D K v G

def IsBandTurned (K : Fin D.mesh.count) (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : Prop :=
  ∀ ι ∈ D.mesh.band K, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ∀ a : Fin 3,
    (p.1 : ℂ) * σ ι p ⟨3 * a.val + 1, by omega⟩
      = ∑ b : Fin 3, turnMatrix (labelAzimuth D.azimuthOrder ι) a b * σ ι p ⟨9 + b.val, by omega⟩

def CellStatesIn (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ (ζ : Fin k → ℝ) (η : Fin (R.portCount K) → ℂ),
    S K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)

variable (A : AssemblyEntry D R)

def PotentialStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    quadFormValue (A.blocks K).potentialKept (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
        + bandQuad D K (A.blocks K).bandWeight (fun ι => bandProfile D ι v G)
        + bandLinear D K (A.blocks K).potentialSource (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
            (fun ι => bandProfile D ι v G)
        - ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).potentialStrainCost ι * tailStrainSq D R K ι G
            + (A.blocks K).potentialVelCost ι * tailVelSq D R K ι v
            + (A.blocks K).potentialCurlCost ι * tailCurlSq D R K ι G)
        + rowLeakAmount D K (A.blocks K) v G + pairingLeakAmount D K (A.blocks K) G + boxAmount D R K v G
        + bandAllowance D K (A.blocks K).bandCurlAllowance (A.blocks K).bandVelAllowance v G
        + creditAmount D R K v
        + pairSlackAmount D R K (D.mesh.band K) G + pairSlackAmount D R K (deactSlackLabels D R K) G
      ≤ resolvedAmount D K q v G H + offChargeAmount D R K q v G H + stretchAmount D K v G
        - (energyBudget D R K v G H Pg + tailCredit D R K G H)

def PairingStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    quadFormValue (A.blocks K).pairingKept (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
        + bandLinear D K (A.blocks K).pairingSource (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
            (fun ι => bandProfile D ι v G)
      ≤ pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
        + ∑ ι ∈ D.mesh.resolved K, (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G
        + pairingLeakAmount D K (A.blocks K) G

def RowStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    Coupling.inverseWeightedSq (A.blocks K).rowWeight
        (rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G))
        + pairSlackAmount D R K (D.mesh.resolved K) G
      ≤ rowShare D K F
        + ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).rowStrainCost ι * tailStrainSq D R K ι G
            + (A.blocks K).rowVelCost ι * tailVelSq D R K ι v)
        + rowLeakAmount D K (A.blocks K) v G + boxAmount D R K v G
        + bandAllowance D K (A.blocks K).bandCurlAllowance (A.blocks K).bandVelAllowance v G
        + (A.blocks K).rowKappaCost * kappaSq (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)

def TailStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    -quadFormValue (A.blocks K).top (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
      ≤ tailCredit D R K G H
        - ∑ ι ∈ D.mesh.resolved K, (totalStrainCost (A.blocks K) ι * tailStrainSq D R K ι G
            + totalVelCost (A.blocks K) ι * tailVelSq D R K ι v
            + (A.blocks K).potentialCurlCost ι * tailCurlSq D R K ι G)

def EliminationStage (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop :=
  ∀ K (x : CellVars D R K → ℂ) (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ), S K x → BandSquareIntegrable D K σ →
    IsBandTurned D K σ →
    quadFormValue (R.cellForm K - energyLeafForm D R K) x
      ≤ quadFormValue (A.blocks K).potentialKept x + quadFormValue (A.blocks K).pairingKept x
        - quadFormValue (A.blocks K).top x
        + bandQuad D K (A.blocks K).bandWeight σ
        + bandLinear D K (A.blocks K).potentialSource x σ + bandLinear D K (A.blocks K).pairingSource x σ
        + Coupling.inverseWeightedSq (A.blocks K).rowWeight (rowVector D K (A.blocks K) x σ)

def CellProfileRegular : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    (∀ ι, (∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect)) ∧
      IntegrableOn (fun p => p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) (D.mesh.box K).rect) ∧
    Summable (fun ι : ℤ × ℤ => ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2)

def BandProfileIntegrable : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → BandSquareIntegrable D K (fun ι => bandProfile D ι v G)

def BandProfileTurned : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → IsBandTurned D K (fun ι => bandProfile D ι v G)

structure AmplitudesMeasurable (D : CellLayerData k C nE nM) : Prop where
  amplitudes : ∀ q ∈ D.cert.params, ∀ β, Measurable ((D.bounds q).ampW β) ∧ Measurable ((D.bounds q).ampGradW β) ∧
    Measurable ((D.bounds q).ampVort β) ∧ Measurable ((D.bounds q).ampGradVort β)
  suprema : ∀ q ∈ D.cert.params, Measurable (D.bounds q).supVort ∧ Measurable (D.bounds q).supGradVort

def ExteriorDensityMeasurable (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    (∀ ι, AEStronglyMeasurable (D.labelDensity q v G H ι) (volume.restrict (D.mesh.exterior ∩ halfPlane))) ∧
      AEStronglyMeasurable (D.meanStretch v G) (volume.restrict (D.mesh.exterior ∩ halfPlane))

def CellDensityMeasurable (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ K, (∀ ι, AEStronglyMeasurable (D.labelDensity q v G H ι) (volume.restrict (D.mesh.box K).rect)) ∧
      AEStronglyMeasurable (D.meanStretch v G) (volume.restrict (D.mesh.box K).rect)

def StretchIntegrandMeasurable (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g → ∀ K,
    AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ × ℝ =>
        CoerciveWeak.stretchFormWith D.given D.givenHess v G z.2.1 (axialRot z.2.2 (planePoint z.1)))
      (((volume.restrict (D.mesh.box K).rect).prod
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))))

def GivenModeMeasurable (D : CellLayerData k C nE nM) : Prop :=
  ∀ K α, (∀ a b, AEStronglyMeasurable (fun p => labelGrad D.azimuthOrder α (gradField D.given) p (a, b))
      (volume.restrict (D.mesh.box K).rect)) ∧
    (∀ a b c, AEStronglyMeasurable (fun p => labelHess D.azimuthOrder α D.givenHess p (a, b, c))
      (volume.restrict (D.mesh.box K).rect)) ∧
    (∀ a, AEStronglyMeasurable (fun p => labelVel D.azimuthOrder α D.given p a) (volume.restrict (D.mesh.box K).rect)) ∧
    (∀ a, AEStronglyMeasurable (fun p => labelVel D.azimuthOrder α (vorticityOf D.given) p a)
      (volume.restrict (D.mesh.box K).rect))

def TrueFieldRegular (D : CellLayerData k C nE nM) : Prop :=
  CellProfileRegular D ∧ CellDensityMeasurable D ∧ StretchIntegrandMeasurable D ∧ GivenModeMeasurable D ∧
    ExteriorDensityMeasurable D

def TrueFieldRegularHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), FieldRegular D → TrueFieldRegular D

def CellPiecesFiniteHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    AssemblyRegular D R → TrueFieldRegular D →
    IsCellMesh D.mesh → CellCalculusConditions D R → CoefficientLowerBounds D D.coercivity →
    FormNegFinite D D.coercivity → (∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity) →
    EntryChargesRegular D R → CellPiecesFinite D R

def DensityMeasurableHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM),
    (∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
    (∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) →
    (∀ q ∈ D.cert.params, Bridge.HasMeasurableBoundData (D.pieces q) (D.bounds q)) → CellDensityMeasurable D

def AllocationSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    AssemblyRegular D R → TrueFieldRegular D →
    IsCellMesh D.mesh → EntryChargesRegular D R → CellDensityMeasurable D → CellPiecesFinite D R → AllocationSplit D R

def BandProfileIntegrableHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), IsCellMesh D.mesh → BandProfileIntegrable D

def BandProfileTurnedHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), IsCellMesh D.mesh → BandProfileTurned D

theorem ofReal_eq_ofReal_max (t : ℝ) : ENNReal.ofReal t = ENNReal.ofReal (max t 0) := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

theorem ofReal_add_four {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ENNReal.ofReal x + ENNReal.ofReal y + ENNReal.ofReal z + ENNReal.ofReal w = ENNReal.ofReal (x + y + z + w) := by
  rw [ENNReal.ofReal_add (by linarith) hw, ENNReal.ofReal_add (by linarith) hz, ENNReal.ofReal_add hx hy]

theorem max_sub_max_neg (t : ℝ) : max t 0 - max (-t) 0 = t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

theorem signed_budget (A S : ℝ) (a b c d : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (h : A - S + b.toReal + c.toReal ≤ a.toReal + d.toReal) :
    ENNReal.ofReal A + ENNReal.ofReal (-S) + b + c ≤ a + d + ENNReal.ofReal S + ENNReal.ofReal (-A) := by
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_toReal hc,
    ← ENNReal.ofReal_toReal hd, ofReal_eq_ofReal_max A, ofReal_eq_ofReal_max (-S), ofReal_eq_ofReal_max S,
    ofReal_eq_ofReal_max (-A),
    ofReal_add_four (le_max_right _ _) (le_max_right _ _) ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ofReal_add_four ENNReal.toReal_nonneg ENNReal.toReal_nonneg (le_max_right _ _) (le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := max_sub_max_neg A
  have h2 := max_sub_max_neg S
  linarith

end Residual


section StageConditions

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def EliminationStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D →
    EliminationConditions D R A S → EliminationStage D R A S

def TopBound (A : AssemblyEntry D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ, ∀ ι ∈ D.mesh.resolved K,
    tailVelSq D R K ι v ≤ quadFormValue ((A.blocks K).topBlock ι) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
      + tailStrainSq D R K ι G / TailBand.velTailGain (D.mesh.box K) ((R.layouts K).layout ι).degCoef

def TailGainHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    AssemblyRegular D R → TrueFieldRegular D →
    CellCalculusConditions D R → ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ι ∈ D.mesh.resolved K,
      TailBand.hessTailGain (D.mesh.box K) ((R.layouts K).layout ι).degCoef (|labelAzimuth D.azimuthOrder ι| : ℝ)
          * tailStrainSq D R K ι G
        ≤ labelStrainTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H ∧
      TailBand.curlTailGain (D.mesh.box K) ((R.layouts K).layout ι).degCoef (|labelAzimuth D.azimuthOrder ι| : ℝ)
          * tailCurlSq D R K ι G
        ≤ labelVorticityTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H ∧
      tailCurlSq D R K ι G ≤ 2 * tailStrainSq D R K ι G

def TailStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R),
    AssemblyRegular D R → TrueFieldRegular D →
    TailConditions D R A → TopBound D R A → TailStage D R A

def TopBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R),
    AssemblyRegular D R → TrueFieldRegular D →
    ∀ (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellCalculusConditions D R → CellStatesIn D R S →
    (∀ K (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ), S K x →
      quadFormValue ((A.blocks K).topBlock ι.1) x = topValue D R K ι x) → TopBound D R A

theorem tailStage_of_parts (hT : TailBand.TailAbsorption) (hG : TailGainHolds) : TailStageHolds := by
  intro k C nE nM D R A hreg htrue hc htop
  have quadForm_sum_smul : ∀ {V ι : Type} [Fintype V] (s : Finset ι) (c : ι → ℝ)
      (M : ι → Matrix V V ℂ) (x : V → ℂ),
      quadFormValue (∑ i ∈ s, (c i : ℂ) • M i) x = ∑ i ∈ s, c i * quadFormValue (M i) x := by
    intro V ι _ s c M x
    classical
    induction s using Finset.induction_on with
    | empty => simp [quadFormValue]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [quadFormValue, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
        dotProduct_smul, Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  have tailNormSq_nonneg : ∀ (Kb : CellBox) (Q : ℕ) (F : ℝ × ℝ → ℂ), 0 ≤ Kb.tailNormSq Q F := by
    intro Kb Q F
    unfold CellBox.tailNormSq CellBox.normSqOn CellBox.lineWeightFn
    refine setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
    have hw : 0 ≤ Kb.lineWeight p.1 := by
      unfold CellBox.lineWeight
      split_ifs with h0
      · exact h0 ▸ hp.1.1
      · exact zero_le_one
    positivity
  unfold TailStage
  intro K q v G H g κ F Pg hx ζ η
  have hleaf := hc.cell_conditions.leaves_valid K q hx.param
  have key : ∀ ι ∈ D.mesh.resolved K,
      -(((A.blocks K).budget ι).velCharge
          * quadFormValue ((A.blocks K).topBlock ι) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        ≤ ((R.leaves K).hessFloor ι
              * labelStrainTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H
            + (R.leaves K).curlHessFloor ι
              * labelVorticityTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
          - (totalStrainCost (A.blocks K) ι * tailStrainSq D R K ι G
            + totalVelCost (A.blocks K) ι * tailVelSq D R K ι v
            + (A.blocks K).potentialCurlCost ι * tailCurlSq D R K ι G) := by
    intro ι hι
    obtain ⟨g1, g2, g3⟩ := hG D R hreg htrue hc.cell_conditions K q v G H g κ F Pg hx ι hι
    have hS : 0 ≤ tailStrainSq D R K ι G :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => tailNormSq_nonneg _ _ _
    have hV : 0 ≤ tailVelSq D R K ι v := Finset.sum_nonneg fun _ _ => tailNormSq_nonneg _ _ _
    have hO : 0 ≤ tailCurlSq D R K ι G := Finset.sum_nonneg fun _ _ => tailNormSq_nonneg _ _ _
    have hf := hc.hess_floor K ι hι
    have hcf := hc.curl_floor K ι hι
    have hb := hT ((A.blocks K).budget ι) (D.mesh.box K) ((R.layouts K).layout ι).degCoef
      (|labelAzimuth D.azimuthOrder ι| : ℝ)
      (labelStrainTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
      (labelVorticityTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
      (tailStrainSq D R K ι G) (tailCurlSq D R K ι G) (tailVelSq D R K ι v)
      (quadFormValue ((A.blocks K).topBlock ι) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
      (hc.budget_holds K ι hι) (hf ▸ (hleaf.hessFloor_pos ι hι).le)
      (hcf ▸ hleaf.curlHessFloor_nonneg ι hι) hS hO hV g3 g1 g2 (htop K q v G H g κ F Pg hx ζ η ι hι)
    unfold TailBand.TailBudget.remainder at hb
    rw [hf, hcf] at hb
    have e1 := mul_le_mul_of_nonneg_right (hc.strain_cost K ι hι) hS
    have e2 := mul_le_mul_of_nonneg_right (hc.vel_cost K ι hι) hV
    have e3 := mul_le_mul_of_nonneg_right (hc.curl_cost K ι hι).2 hO
    nlinarith [e1, e2, e3, hb]
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hsum
  rw [hc.top_eq K, quadForm_sum_smul]
  unfold tailCredit
  linarith

end StageConditions

section Rows

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def rowMoment {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (F : ℝ → Space → Space) : Fin B.rowCount → ℂ :=
  fun i => ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    labelVel D.azimuthOrder (B.rowLabel i) F p c * (starRingEnd ℂ) (testAt D K (B.rowLabel i) (B.rowTest i) c p)

def tailProfile (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : Fin 12 → ℂ :=
  pairVec (fun a b => gradAt D.azimuthOrder ι G a b p
      - (D.mesh.box K).proj ((R.layouts K).layout ι).degCoef ((R.layouts K).layout ι).degCoef
          (fun p' => gradAt D.azimuthOrder ι G a b p') p)
    (fun a => velAt D.azimuthOrder ι v a p
      - (D.mesh.box K).proj (((R.layouts K).layout ι).degCoef - 1) (((R.layouts K).layout ι).degCoef - 1)
          (fun p' => velAt D.azimuthOrder ι v a p') p)

def tailRow {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : Fin B.rowCount → ℂ :=
  fun i => ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
    ((D.mesh.box K).lineWeight p.1 : ℂ) * ∑ j, tailProfile D R K ι v G p j * (starRingEnd ℂ) (B.rowTailTest i ι p j)

def RowMomentExpansion (A : AssemblyEntry D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    Coupling.inverseWeightedSq (leakGram D K (A.blocks K))
        (rowMoment D K (A.blocks K) F
          - rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G)
          - tailRow D R K (A.blocks K) v G)
        + pairSlackAmount D R K (D.mesh.resolved K) G
      ≤ rowLeakAmount D K (A.blocks K) v G + boxAmount D R K v G
        + bandAllowance D K (A.blocks K).bandCurlAllowance (A.blocks K).bandVelAllowance v G
        + (A.blocks K).rowKappaCost * kappaSq (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)

def RowShareStackedHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R),
    AssemblyRegular D R → TrueFieldRegular D →
    ∀ tauMax : ℝ, Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax → RowConditions D R A →
    ∀ K (F : ℝ → Space → Space),
      rowShare D K F = Coupling.inverseWeightedSq (rowBaseWeight D K (A.blocks K)) (rowMoment D K (A.blocks K) F)

def RowRemovalHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R),
    AssemblyRegular D R → TrueFieldRegular D →
    ∀ tauMax : ℝ, Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax →
    RowConditions D R A → BandProfileIntegrable D →
    ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
      Coupling.inverseWeightedSq (A.blocks K).rowWeight
          (rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G))
        ≤ Coupling.inverseWeightedSq (rowBaseWeight D K (A.blocks K)) (rowMoment D K (A.blocks K) F)
          + ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).rowStrainCost ι * tailStrainSq D R K ι G
              + (A.blocks K).rowVelCost ι * tailVelSq D R K ι v)
          + Coupling.inverseWeightedSq (leakGram D K (A.blocks K))
              (rowMoment D K (A.blocks K) F
                - rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
                    (fun ι => bandProfile D ι v G)
                - tailRow D R K (A.blocks K) v G)

def RowStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R),
    AssemblyRegular D R → TrueFieldRegular D →
    ∀ tauMax : ℝ, Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax → RowConditions D R A →
    BandProfileIntegrable D → RowMomentExpansion D R A → RowStage D R A

end Rows

section Credits

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

end Credits

section PotentialPairing

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def epsPartnerCharge {V : Type} (P : PotentialData V) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  splitCharge P.epsStrain (3 / (2 * Real.sqrt 2) * P.epsGrad * P.epsLength) (3 / (2 * Real.sqrt 2) * P.epsGrad / P.length) a g

def longPartnerCharge {V : Type} (P : PotentialData V) (ι : ℤ × ℤ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : ℝ :=
  longFactor P ι * splitCharge P.longStrain (3 / (2 * Real.sqrt 2) * P.longGrad * P.epsLength)
    (3 / (2 * Real.sqrt 2) * P.longGrad / P.length) a g

def couplingTail (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (ι : D.mesh.resolved K) (strain : Bool) : ℝ :=
  ∑ j : Fin 12, if decide (j.val < 9) = strain then
    (D.mesh.box K).tailNormSq (if strain then ((R.layouts K).layout ι.1).degCoef else ((R.layouts K).layout ι.1).degCoef - 1)
      (fun p => ((CellScalars.rHat (D.mesh.box K) p : ℝ) : ℂ) * ∑ ι' : D.mesh.resolved K,
        ∑ j', P.couplingModel (ι.1 - ι'.1) p j j' * lowProfile D R K ι' (upperPart D R K P x) p j') else 0

def highPartnerCharge {V : Type} (P : PotentialData V) (U : Fin 12 → ℂ) : ℝ :=
  P.highStrain / P.youngCurl * curlSq (strainOfVec U)
    + 3 / (2 * Real.sqrt 2) * P.highGrad * (vecSq (velOf U) / P.youngStrain + sumSq (strainOfVec U) / P.youngVel)

def highPartnerAmount {V : Type} (K : Fin D.mesh.count) (P : PotentialData V) (S : Finset (ℤ × ℤ))
    (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ S, ∫ p in (D.mesh.box K).rect, p.1 * highPartnerCharge P (X ι p)

def PotentialStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D → CellPiecesFinite D R →
    CellStatesIn D R S → PotentialConditions D R A P S → PotentialStage D R A

def PairingStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (Q : Fin D.mesh.count → PairingData k) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D →
    CellStatesIn D R S → PairingConditions D R A Q S → PairingStage D R A

end PotentialPairing

section RowFunctionals

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def RowMomentExpansionHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D →
    ∀ tauMax : ℝ, Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax → CellStatesIn D R S →
    PotentialConditions D R A P S → RowConditions D R A → RowFunctionalConditions D R A P S → RowMomentExpansion D R A

end RowFunctionals

section Pressure

open SteadyCert

def IsStationaryTestField (φ : Space → Space) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ ∀ y, divergenceAt φ y = 0

def AnnihilatorGradientHolds : Prop :=
  ∀ Q : Space → Space, AEStronglyMeasurable Q volume → IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2) →
    (∀ φ, IsStationaryTestField φ → ∫ y, inner ℝ (Q y) (φ y) = 0) → IsGradientField Q

def IsSpaceTimeAnnihilator (P : ℝ → Space → Space) : Prop :=
  ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (P z.1 z.2) (φ z.1 z.2) = 0

def HasLocalSquare (P : ℝ → Space → Space) : Prop :=
  ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖P σ y‖ ^ 2) < ⊤

def HarmonicAnnihilatorHolds : Prop :=
  ∀ P : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume → IsTimePeriodic P →
    HasLocalSquare P → IsSpaceTimeAnnihilator P → ∀ ν : ℤ,
      AEStronglyMeasurable (harmonicCos ν P) volume ∧ AEStronglyMeasurable (harmonicSin ν P) volume ∧
      IsLocalSquareIntegrable (fun y => ‖harmonicCos ν P y‖ ^ 2) ∧
      IsLocalSquareIntegrable (fun y => ‖harmonicSin ν P y‖ ^ 2) ∧
      (∀ φ, IsStationaryTestField φ → ∫ y, inner ℝ (harmonicCos ν P y) (φ y) = 0) ∧
      (∀ φ, IsStationaryTestField φ → ∫ y, inner ℝ (harmonicSin ν P y) (φ y) = 0)

def strongRemainder {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g F : ℝ → Space → Space) : ℝ → Space → Space :=
  fun σ y => F σ y - (g σ y - secondDerivTrace (H σ y) + couplingField W v G σ y + ∑ i, κ i • b i σ y)

theorem strongRightSide_remainder {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space)
    (κ : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g F : ℝ → Space → Space) :
    IsStrongRightSide W b κ v G H g F (strongRemainder W b κ v G H g F) := by
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [strongRemainder]
  abel

theorem chosenPressure_eq_remainder {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q) :
    chosenPressure D x = strongRemainder D.given D.cert.actuator x.κ x.v x.G x.H x.g (flipAverage x.F) :=
  rfl

structure PressureFacts {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) : Prop where
  model_state : ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B
  model_eq : ∀ q ∈ D.cert.params, D.cert.model q = D.given
  mode_class : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder
  flip_model : Bridge.IsFlipInvariantModel D.given D.givenHess
  actuators : ∀ i, ∃ S : Finset (ℤ × ℤ), Instance.ActuatorShapeFacts D.azimuthOrder S (D.cert.actuator i)

def FlipAverageRightSideHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), PressureFacts D →
    ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q,
      AEStronglyMeasurable (fun z : ℝ × Space => flipAverage x.F z.1 z.2) volume ∧
      IsTimePeriodic (flipAverage x.F) ∧ periodLIntegral (fun σ y => ‖flipAverage x.F σ y‖ ^ 2) < ⊤ ∧
      IsRightSide D.given D.cert.actuator x.κ x.v x.G x.g (flipAverage x.F)

def RemainderAnnihilatesHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), PressureFacts D →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ → IsRightSide D.given D.cert.actuator κ v G g F →
        IsSpaceTimeAnnihilator (strongRemainder D.given D.cert.actuator κ v G H g F)

def RemainderRegularHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), PressureFacts D →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        AEStronglyMeasurable (fun z : ℝ × Space => strongRemainder D.given D.cert.actuator κ v G H g F z.1 z.2)
          volume ∧
        IsTimePeriodic (strongRemainder D.given D.cert.actuator κ v G H g F) ∧
        HasLocalSquare (strongRemainder D.given D.cert.actuator κ v G H g F)

def PressureRecoveryHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), PressureFacts D → PressureRecovered D

theorem pressureRecovery_of_parts (hA : AnnihilatorGradientHolds) (hH : HarmonicAnnihilatorHolds)
    (hF : FlipAverageRightSideHolds) (hS : RemainderAnnihilatesHolds) (hR : RemainderRegularHolds) :
    PressureRecoveryHolds := by
  intro k C nE nM D hD q hq x
  obtain ⟨hFm, hFp, hF2, hFr⟩ := hF D hD q hq x
  obtain ⟨hRm, hRp, hRl⟩ :=
    hR D hD q hq x.v x.G x.H x.g x.perturbation x.κ (flipAverage x.F) hFm hFp hF2
  have hSa := hS D hD q hq x.v x.G x.H x.g x.perturbation x.κ (flipAverage x.F) hFm hFp hF2 hFr
  have hHa := hH _ hRm hRp hRl hSa
  refine ⟨hRm, hRp, hRl, fun ν => ?_⟩
  obtain ⟨hcm, hsm, hcl, hsl, hco, hso⟩ := hHa ν
  exact ⟨hA _ hcm hcl hco, hA _ hsm hsl hso⟩

end Pressure

section OffModes

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def OffModesVanishHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (O : OffModeCover D),
    AssemblyRegular D R → TrueFieldRegular D →
    (∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
    IsCellMesh D.mesh → IsOffModeCover D R O → OffModesVanish D R

def exteriorChargeDensity (D : CellLayerData k C nE nM) (ec : TailBand.EntryCharges) (q : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  D.labelDensity q v G H ι p
    - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges none) ec
        D.azimuthOrder ι v G H p

def ExteriorStretchCharged (D : CellLayerData k C nE nM) (ec : TailBand.EntryCharges) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    (∑' ι : ℤ × ℤ, ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (-(exteriorChargeDensity D ec q v G H ι p * p.1)))
        + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1 < ⊤ ∧
    (∑' ι : ℤ × ℤ, ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (-(exteriorChargeDensity D ec q v G H ι p * p.1)))
        + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1
      ≤ (∑' ι : ℤ × ℤ, ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (exteriorChargeDensity D ec q v G H ι p * p.1))
        + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchPosMean v G p * ENNReal.ofReal p.1

structure ExteriorDecayEntry where
  radius : ℝ
  strainDecay : ℝ
  meanGradDecay : ℝ
  waveGradDecay : ℝ

def ExteriorDecay (D : CellLayerData k C nE nM) (E : ExteriorDecayEntry) : Prop :=
  ∀ p : ℝ × ℝ, p ∈ halfPlane → E.radius ≤ TailBand.planeRadius p → ∀ σ θ : ℝ, ∀ u : Space,
    inner ℝ (strainOf D.given σ (cylPoint p.1 θ p.2) u) u ≤ E.strainDecay / TailBand.planeRadius p ^ 2 * ‖u‖ ^ 2 ∧
    opBound (fun a b => labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p (a, b))
      (E.meanGradDecay / TailBand.planeRadius p ^ 3) ∧
    ‖vorticityGradOf D.givenHess σ (cylPoint p.1 θ p.2) u
      - CellMatField.frameMap θ (fun a b => (labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p (a, b)).re) u‖
      ≤ E.waveGradDecay / TailBand.planeRadius p ^ 3 * ‖u‖

def ExteriorDecayHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (E : ExteriorDecayEntry) (B : ℝ),
    CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B → 0 < E.radius →
    B ≤ E.strainDecay → 6 * B ≤ E.meanGradDecay → 12 * B ≤ E.waveGradDecay → ExteriorDecay D E

structure ExteriorChargeConditions (D : CellLayerData k C nE nM) (E : ExteriorDecayEntry) : Prop where
  near_part : IsRegionChargeBound D.azimuthOrder (D.mesh.exterior ∩ halfPlane ∩ {p | TailBand.planeRadius p < E.radius})
    D.given D.givenHess (D.charges none)
  tail_curl : ∀ ι p, p ∈ D.mesh.exterior ∩ halfPlane → E.radius ≤ TailBand.planeRadius p →
    E.strainDecay / TailBand.planeRadius p ^ 2 ≤ (D.charges none).curl ι p
  tail_product : ∀ ι p, p ∈ D.mesh.exterior ∩ halfPlane → E.radius ≤ TailBand.planeRadius p →
    E.meanGradDecay / TailBand.planeRadius p ^ 3 ≤ (D.charges none).product ι p
  tail_gradient : ∀ ι p, p ∈ D.mesh.exterior ∩ halfPlane → E.radius ≤ TailBand.planeRadius p →
    E.waveGradDecay / TailBand.planeRadius p ^ 3 ≤ (D.charges none).gradient ι p
  length_common : ∀ ι ι' p, p ∈ D.mesh.exterior ∩ halfPlane → (D.charges none).length ι p = (D.charges none).length ι' p
  length_pos : ∀ ι p, p ∈ D.mesh.exterior ∩ halfPlane → 0 < (D.charges none).length ι p
  decay_nonneg : 0 ≤ E.meanGradDecay ∧ 0 ≤ E.waveGradDecay

def ExteriorChargeBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (E : ExteriorDecayEntry),
    ExteriorDecay D E → ExteriorChargeConditions D E →
    IsRegionChargeBound D.azimuthOrder (D.mesh.exterior ∩ halfPlane) D.given D.givenHess (D.charges none)

def ExteriorStretchChargedHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : ExteriorCover C nE nM),
    FieldRegular D → TrueFieldRegular D →
    (∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) →
    Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess →
    IsRegionChargeBound D.azimuthOrder (D.mesh.exterior ∩ halfPlane) D.given D.givenHess (D.charges none) →
    Real.sqrt (7 / 2) ≤ X.charges.stretchConst →
    IsExteriorCover D X → ExteriorStretchCharged D X.charges

def ExteriorNonnegHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : ExteriorCover C nE nM),
    FieldRegular D → TrueFieldRegular D →
    (∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
    Bridge.IsModeClass D.cert.symmetries D.azimuthOrder → IsCellMesh D.mesh → FormNegFinite D D.coercivity →
    (∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity) →
    IsExteriorCover D X → ExteriorStretchCharged D X.charges → ExteriorNonneg D

end OffModes


section Tree

variable {k : ℕ} {C : Type} {nE nM : ℕ}

open CellCert.CellCoordinates

namespace RowEntry

variable {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R} (W : RowEntry D R T)

end RowEntry

def RowsMatchState (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (T : TreeEntry D R)
    (W : RowEntry D R T) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q, ∀ K d, ¬ (W.reason K d).IsUnused →
    W.rowValue K d (T.trueData x) = T.shiftedState x K (Sum.inl (Sum.inl d))

def RowsMatchFields (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (T : TreeEntry D R)
    (W : RowEntry D R T) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ Pg : ℝ → Space → Space, IsPeriodicPressure Pg →
      (∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) → ∀ (κ : Fin k → ℝ) K d,
        ¬ (W.reason K d).IsUnused →
          W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))

def RowsMatchFieldsHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), Bridge.IsModeClass D.cert.symmetries D.azimuthOrder →
    IsCellMesh D.mesh → CellCalculusConditions D R → HarmonicRelationsStatement → Bridge.StripMomentTraceHolds →
    Bridge.TraceMatchHolds → Bridge.TraceHeightHolds → Bridge.CornerTraceHolds → Bridge.CornerMatchHolds →
    Bridge.ModeHeightDerivHolds → Bridge.StripDataFlipHolds → Bridge.CornerDataFlipHolds →
    Bridge.ScalarPlaneFlipHolds → PressureFacts D → T.GaugeKeyConditions → T.RealKeyConditions →
    T.FieldGaugeHolds → T.GaugeRowTransport W.rowVec → TreeRowConditions D R e T W → RowsMatchFields D R T W

def ChosenPressureFlips (D : CellLayerData k C nE nM) : Prop :=
  ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q,
    ∀ᵐ z : ℝ × Space, chosenPressure D x z.1 (flipPoint z.2) = flipPoint (chosenPressure D x z.1 z.2)

def RowsMatchStateOfFieldsHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (T : TreeEntry D R) (W : RowEntry D R T), PressureFacts D → PressureRecovered D → ChosenPressureFlips D →
    RowsMatchFields D R T W → RowsMatchState D R T W

def CellStateInRowRangeHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), IsCellMesh D.mesh → CellCalculusConditions D R →
    TreeRowConditions D R e T W → RowsMatchFields D R T W → CellStatesIn D R (InRowRange W)

def TreeStateHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T),
    CellCalculusConditions D R → T.GaugeKeyConditions → TreeRowConditions D R e T W → RowsMatchState D R T W →
      ChosenPressureFlips D →
      TreeStateFromInitial D R e T

end Tree

section Initial

def FormSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), IsCellMesh D.mesh →
    ∀ q v G H, D.formPos q v G H = (∑ K, cellPos D K q v G H) + extPos D q v G H ∧
      D.formNeg q v G H = (∑ K, cellNeg D K q v G H) + extNeg D q v G H

end Initial



section CellLayerBreakdown

variable {k : ℕ} {C : Type} {nE nM : ℕ}

structure ResidualParts (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop) : Prop where
  pieces_finite : CellPiecesFinite D R
  allocation : AllocationSplit D R
  band_integrable : BandProfileIntegrable D
  potential : PotentialStage D R A
  pairing : PairingStage D R A
  rows : RowStage D R A
  tails : TailStage D R A
  band_turned : BandProfileTurned D
  states_in : CellStatesIn D R S
  elimination : EliminationStage D R A S

structure AssemblyConditions (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {T : TreeEntry D R} (W : RowEntry D R T) : Prop where
  mesh_valid : IsCellMesh D.mesh
  cell_conditions : CellCalculusConditions D R
  coefficient_bounds : CoefficientLowerBounds D D.coercivity
  charges_regular : EntryChargesRegular D R
  regular : AssemblyRegular D R
  amplitudes_measurable : AmplitudesMeasurable D
  admissible : ∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q)
    (D.bounds q) D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃
  model_state : ∃ B : ℝ, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B
  row_values : ∃ tauMax : ℝ, Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax
  potential : PotentialConditions D R A P (InRowRange W)
  pairing : PairingConditions D R A P.pairing (InRowRange W)
  rows : RowConditions D R A
  row_functionals : RowFunctionalConditions D R A P (InRowRange W)
  tails : TailConditions D R A
  top_block : ∀ K (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ), InRowRange W K x →
    quadFormValue ((A.blocks K).topBlock ι.1) x = topValue D R K ι x
  elimination : EliminationConditions D R A (InRowRange W)
  rows_gauge_blind : ∀ K (c : Fin T.gauge.count), (A.blocks K).rowMap *ᵥ T.gaugeDir K c = 0
  rows_head_blind : ∀ K (ι : D.mesh.resolved K), (A.blocks K).rowMap *ᵥ headUnit D R K ι.1 = 0
  pressure_blind : ∀ K (d : CellVar D.mesh K (R.layouts K)), isPressureDatum ((R.layouts K).layout d.1.1) d.2 = true →
    (∀ j, (A.blocks K).potentialKept (Sum.inl (Sum.inl d)) j = 0 ∧ (A.blocks K).potentialKept j (Sum.inl (Sum.inl d)) = 0 ∧
      (A.blocks K).pairingKept (Sum.inl (Sum.inl d)) j = 0 ∧ (A.blocks K).pairingKept j (Sum.inl (Sum.inl d)) = 0 ∧
      (A.blocks K).top (Sum.inl (Sum.inl d)) j = 0 ∧ (A.blocks K).top j (Sum.inl (Sum.inl d)) = 0 ∧
      (P.potential K).portForm (Sum.inl (Sum.inl d)) j = 0 ∧ (P.potential K).portForm j (Sum.inl (Sum.inl d)) = 0) ∧
    (∀ ι, (A.blocks K).topBlock ι (Sum.inl (Sum.inl d)) = 0 ∧ ∀ j, (A.blocks K).topBlock ι j (Sum.inl (Sum.inl d)) = 0) ∧
    (∀ ι p j, (A.blocks K).potentialSource ι (Sum.inl (Sum.inl d)) p j = 0 ∧
      (A.blocks K).pairingSource ι (Sum.inl (Sum.inl d)) p j = 0 ∧ (A.blocks K).bandMap ι (Sum.inl (Sum.inl d)) p j = 0)

end CellLayerBreakdown

end Assembly

end CertCell

end Breakdown
