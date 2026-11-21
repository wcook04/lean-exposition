import Breakdown.CertCell.AssemblyStatements

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

section RowParts

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def trueVelocity (α : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun a => labelVel D.azimuthOrder α D.given p a

def trueVorticity (α : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => labelVel D.azimuthOrder α (vorticityOf D.given) p a

def longVelocity (K : Fin D.mesh.count) (α : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => labelVel D.azimuthOrder α (R.long K).velocity p a

def longVorticity (K : Fin D.mesh.count) (α : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => labelVel D.azimuthOrder α (R.long K).vorticity p a

def rowTestValue {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun c => (rowTestPoly D K B i c).eval (D.mesh.box K) p

def freqPiece {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (P : ℝ) (v : ℝ → Space → Space) :
    Fin B.rowCount → ℂ :=
  fun i => ((2 * Real.pi * (labelTime (B.rowLabel i) : ℝ) * (1 / P - D.model.periodInverse) : ℝ) : ℂ) * Complex.I *
    ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ a : Fin 3,
      velAt D.azimuthOrder (B.rowLabel i) v a p * (starRingEnd ℂ) (rowTestValue D K B i p a)

def errorPiece {V W : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (P : PotentialData W) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : Fin B.rowCount → ℂ :=
  fun i => ∑ ι' ∈ D.mesh.resolved K ∪ D.mesh.band K ∪ deactSources D K P, ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j,
    bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest
      (fun a => trueVelocity D (B.rowLabel i - ι') p a - modelVelocity D K (B.rowLabel i - ι') p a
        - longVelocity D R K (B.rowLabel i - ι') p a)
      (fun a => trueVorticity D (B.rowLabel i - ι') p a - modelVorticity D K (B.rowLabel i - ι') p a
        - longVorticity D R K (B.rowLabel i - ι') p a)
      (rowTestValue D K B i p) j)

def longPiece {V W : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (P : PotentialData W) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : Fin B.rowCount → ℂ :=
  fun i => ∑ ι' ∈ D.mesh.resolved K ∪ D.mesh.band K ∪ deactSources D K P, ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j,
    bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest
      (longVelocity D R K (B.rowLabel i - ι') p) (longVorticity D R K (B.rowLabel i - ι') p)
      (rowTestValue D K B i p) j)

open Classical in
def deactGroupPiece {V W : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (P : PotentialData W)
    (j : Fin P.groupCount) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    Fin B.rowCount → ℂ :=
  fun i => ∑ ι' ∈ P.rowPartners j, if B.rowLabel i - ι' ∈ P.groupHarmonics j then
    ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c, bandProfile D ι' v G p c * (starRingEnd ℂ)
      (crossTest (modelVelocity D K (B.rowLabel i - ι') p) (modelVorticity D K (B.rowLabel i - ι') p)
        (rowTestValue D K B i p) c) else 0

open Classical in
def deactPiece {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (H : Finset (ℤ × ℤ)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : Fin B.rowCount → ℂ :=
  fun i => ∑ α ∈ H, if B.rowLabel i - α ∉ D.mesh.resolved K ∧ B.rowLabel i - α ∉ D.mesh.band K then ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j,
    bandProfile D (B.rowLabel i - α) v G p j * (starRingEnd ℂ)
      (crossTest (modelVelocity D K α p) (modelVorticity D K α p) (rowTestValue D K B i p) j) else 0

def actuatorPiece {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (κ : Fin k → ℝ) : Fin B.rowCount → ℂ :=
  fun i => ∑ l, (κ l : ℂ) * (actuatorRow D K (B.rowLabel i) (rowTestPoly D K B i) (D.cert.actuator l)
    - actuatorRow D K (B.rowLabel i) (rowTestPoly D K B i) (B.actuatorModel (l : ℕ)))

def RowIdentity (A : AssemblyEntry D R) (P : CouplingEntries D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    rowMoment D K (A.blocks K) F
        - rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G)
        - tailRow D R K (A.blocks K) v G
      = freqPiece D K (A.blocks K) (D.cert.period q) v + errorPiece D R K (A.blocks K) (P.potential K) v G
        + longPiece D R K (A.blocks K) (P.potential K) v G + deactPiece D K (A.blocks K) (P.potential K).harmonicLabels v G
        + actuatorPiece D K (A.blocks K) κ

def freqAllowance {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (v : ℝ → Space → Space) : ℝ :=
  ∑ ι ∈ D.mesh.tested K, B.freqCost ι
    * (2 * Real.pi * (labelTime ι : ℝ) * (D.modelErrors K).periodInverse) ^ 2
    * ∫ p in (D.mesh.box K).rect, p.1 * modeVelSq D ι v p

def errorAllowance {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (S : Finset (ℤ × ℤ)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ S, 2 * B.errorCost * ∫ p in (D.mesh.box K).rect, p.1 *
    (((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2 * modeCurlSq D ι G p
      + ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2 * modeVelSq D ι v p)

def longAllowance {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (S : Finset (ℤ × ℤ)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ S, 2 * longSourceCost D R K B ι * ∫ p in (D.mesh.box K).rect, p.1 *
    ((R.long K).errVelocity ^ 2 * modeCurlSq D ι G p + (R.long K).errVorticity ^ 2 * modeVelSq D ι v p)

def FreqPieceBound (A : AssemblyEntry D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    Coupling.inverseWeightedSq (scaledRowGram D K (A.blocks K) (A.blocks K).freqCost)
        (freqPiece D K (A.blocks K) (D.cert.period q) v)
      ≤ freqAllowance D K (A.blocks K) v

def ErrorPieceBound (A : AssemblyEntry D R) (P : CouplingEntries D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    Coupling.inverseWeightedSq (scaledRowGram D K (A.blocks K) (fun _ => (A.blocks K).errorCost))
        (errorPiece D R K (A.blocks K) (P.potential K) v G)
      ≤ errorAllowance D K (A.blocks K) (D.mesh.resolved K) v G + errorAllowance D K (A.blocks K) (D.mesh.band K) v G
        + errorAllowance D K (A.blocks K) (deactSources D K (P.potential K)) v G

def deactAllowance {V W : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (P : PotentialData W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ B.leakModes, ∫ p in (D.mesh.box K).rect, p.1 * (2 * B.deactCost *
    ((∑ j, if ι ∈ P.rowPartners j then P.groupVel j ^ 2 else 0) * modeCurlSq D ι G p
      + (∑ j, if ι ∈ P.rowPartners j then P.groupCurl j ^ 2 else 0) * modeVelSq D ι v p))

def LongPieceBound (A : AssemblyEntry D R) (P : CouplingEntries D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    Coupling.inverseWeightedSq (scaledRowGram D K (A.blocks K) (longRowCost D R K (A.blocks K)))
        (longPiece D R K (A.blocks K) (P.potential K) v G)
      ≤ longAllowance D R K (A.blocks K) (D.mesh.resolved K) v G + longAllowance D R K (A.blocks K) (D.mesh.band K) v G
        + longAllowance D R K (A.blocks K) (deactSources D K (P.potential K)) v G

def DeactPieceBound (A : AssemblyEntry D R) (P : CouplingEntries D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    (A.blocks K).deactCost * ∑ j, Coupling.inverseWeightedSq (rowGram D K (A.blocks K))
        (deactGroupPiece D K (A.blocks K) (P.potential K) j v G)
      ≤ deactAllowance D K (A.blocks K) (P.potential K) v G

def DeactSplit (A : AssemblyEntry D R) (P : CouplingEntries D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ i,
    deactPiece D K (A.blocks K) (P.potential K).harmonicLabels v G i
      = ∑ j, deactGroupPiece D K (A.blocks K) (P.potential K) j v G i

def ActuatorPieceBound (A : AssemblyEntry D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    Coupling.inverseWeightedSq (scaledRowGram D K (A.blocks K) (fun _ => (A.blocks K).actuatorCost))
        (actuatorPiece D K (A.blocks K) κ)
      ≤ (A.blocks K).actuatorCost * (A.blocks K).actuatorErr * ∑ l, κ l ^ 2

def AllowanceSplit (A : AssemblyEntry D R) (P : CouplingEntries D R) : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    freqAllowance D K (A.blocks K) v + errorAllowance D K (A.blocks K) (D.mesh.resolved K) v G
        + longAllowance D R K (A.blocks K) (D.mesh.resolved K) v G
        + pairSlackAmount D R K (D.mesh.resolved K) G ≤ boxAmount D R K v G ∧
    errorAllowance D K (A.blocks K) (D.mesh.band K) v G + longAllowance D R K (A.blocks K) (D.mesh.band K) v G
      ≤ bandAllowance D K (A.blocks K).bandCurlAllowance (A.blocks K).bandVelAllowance v G ∧
    errorAllowance D K (A.blocks K) (deactSources D K (P.potential K)) v G
        + longAllowance D R K (A.blocks K) (deactSources D K (P.potential K)) v G
        + deactAllowance D K (A.blocks K) (P.potential K) v G
      ≤ rowLeakAmount D K (A.blocks K) v G

def RowIdentityHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D →
    ∀ tauMax : ℝ, Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax →
    (∀ i, ∃ S : Finset (ℤ × ℤ), Instance.ActuatorShapeFacts D.azimuthOrder S (D.cert.actuator i)) →
    Bridge.IsModeClass D.cert.symmetries D.azimuthOrder → PotentialConditions D R A P S → RowConditions D R A → RowFunctionalConditions D R A P S → RowIdentity D R A P

def FreqPieceBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D →
    RowConditions D R A → RowFunctionalConditions D R A P S → FreqPieceBound D R A

def ErrorPieceBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D →
    (∀ K α, α ∉ D.model.velocity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
      D.model.velocity.planeValue D.mesh.box K α a p = 0) →
    (∀ K α, α ∉ D.model.vorticity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
      D.model.vorticity.planeValue D.mesh.box K α a p = 0) →
    RowConditions D R A → RowFunctionalConditions D R A P S → ErrorPieceBound D R A P

def LongPieceBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D →
    RowConditions D R A → RowFunctionalConditions D R A P S → LongPieceBound D R A P

def DeactSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
    RowConditions D R A → RowFunctionalConditions D R A P S → DeactSplit D R A P

def DeactPieceBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
    RowConditions D R A → RowFunctionalConditions D R A P S → DeactPieceBound D R A P

def AllowanceSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → CellCalculusConditions D R → PotentialConditions D R A P S →
    RowConditions D R A → RowFunctionalConditions D R A P S → AllowanceSplit D R A P

def ActuatorPieceBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D →
    RowConditions D R A → RowFunctionalConditions D R A P S → ActuatorPieceBound D R A

def RowCombineHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → RowConditions D R A → RowFunctionalConditions D R A P S →
    RowIdentity D R A P → FreqPieceBound D R A → ErrorPieceBound D R A P → LongPieceBound D R A P →
    DeactSplit D R A P → DeactPieceBound D R A P → ActuatorPieceBound D R A → AllowanceSplit D R A P →
    RowMomentExpansion D R A

end RowParts

end Assembly

end CertCell

end Breakdown
