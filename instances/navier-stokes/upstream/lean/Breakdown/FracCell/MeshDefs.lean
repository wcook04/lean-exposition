import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.CellCoordsDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

end CellBox

namespace TailFamily

variable {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O)

def inputFn (m : ℕ) (B : CellBases) (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (i : I) (c : Fin (T.dim i))
    (p : ℝ × ℝ) (θ : ℝ) : ℂ :=
  ∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
    w i n' j l c * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
      Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)

def outputMode (m : ℕ) (B : CellBases) (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) (n : ℤ)
    (p : ℝ × ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (∑ i, ∑ c : Fin (T.dim i), T.mult i o c p θ * T.inputFn m B w i c p θ)

def majorant (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) : ℝ :=
  ∑ i, ∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
    (T.radialTotal * T.radialBound i j + T.heightTotal * T.heightBound i l) * ∑ c, ‖w i n' j l c‖ ^ 2

end TailFamily

structure IsTailRegular (K : CellBox) {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) : Prop where
  mult_measurable : ∀ i o c, AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => T.mult i o c q.1 q.2)
    ((volume.restrict K.rect).prod volume)
  mult_bounded : ∀ i o c, ∃ C : ℝ, ∀ p ∈ K.rect, ∀ θ : ℝ, ‖T.mult i o c p θ‖ ≤ C

structure IsTailBounds (K : CellBox) (B : CellBases) (D : ℕ) {I O : Type} [Fintype I] [Fintype O]
    (T : TailFamily I O) : Prop where
  outWeight_nonneg : ∀ o, 0 ≤ T.outWeight o
  radialBound_nonneg : ∀ i j, 0 ≤ T.radialBound i j
  heightBound_nonneg : ∀ i l, 0 ≤ T.heightBound i l
  radial_bound : ∀ i, ∀ j ≤ T.inputDeg i, ∀ z ∈ Set.Ioo K.z₁ K.z₂, ∀ θ : ℝ, ∀ u : Fin (T.dim i) → ℂ,
    (∑ o, T.outWeight o * K.radialTail B D
        (fun r => (∑ c, T.mult i o c (r, z) θ * u c) * (B.radialPoly j r : ℂ)))
      ≤ T.radialBound i j ^ 2 * ∑ c, ‖u c‖ ^ 2
  height_bound : ∀ i, ∀ l ≤ T.inputDeg i, ∀ r ∈ Set.Ioo K.r₁ K.r₂, ∀ θ : ℝ, ∀ u : Fin (T.dim i) → ℂ,
    (∑ o, T.outWeight o * K.heightTail B D
        (fun z => (∑ c, T.mult i o c (r, z) θ * u c) * (B.heightPoly l z : ℂ)))
      ≤ T.heightBound i l ^ 2 * ∑ c, ‖u c‖ ^ 2

def farCoefSum (K : CellBox) (B : CellBases) (D : ℕ) (Y : ℝ × ℝ → ℂ) : ℝ :=
  ∑' jl : ℕ × ℕ, (if D < max jl.1 jl.2 then ‖B.coef K Y jl.1 jl.2‖ ^ 2 else 0)

def TailMajorantStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (m : ℕ), 1 ≤ m → ∀ (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T → IsTailBounds K B D T →
      ∀ w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ,
        (∑ o, T.outWeight o * ∑ n ∈ T.outModes o, farCoefSum K B D (T.outputMode m B w o n)) ≤ T.majorant w

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

end CellScalars

structure IsFarMajorant {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    {slots : ℕ} (R : CellRows N slots k) (F : FarMajorantData) : Prop where
  strain_bounds : IsTailBounds K B S.degNear (CellScalars.strainGroupFamily c K S F)
  velocity_bounds : IsTailBounds K B S.degNear (CellScalars.velocityGroupFamily c K S F)
  band_bounds : S.band ≠ ∅ → IsTailBounds K B S.degNear (CellScalars.bandGroupFamily c K S F)
  share_pos : 0 < F.share
  turnBound_nonneg : 0 ≤ F.turnBound
  turn_bound : ∀ n ∈ S.band, ∀ w : Fin 3 → ℂ, vecSq (turnAdjInv (azimuth c.order n) w) ≤ F.turnBound ^ 2 * vecSq w
  floors_pos : 0 < F.strainFloor ∧ 0 < F.velocityFloor
  far_floor : ∀ n j l, S.degNear < max j l →
    (n ∈ S.resolved ∪ S.band → F.strainFloor ≤ S.symWeight n j l ∧ F.strainFloor ≤ S.antiWeight n j l) ∧
    (n ∈ S.resolved → F.velocityFloor ≤ S.velWeight n j l)
  strainWeight_ge : (if S.band = ∅ then 1 else 1 + F.share) / F.strainFloor ≤ F.strainWeight
  resolvedVelocityWeight_ge : 1 / F.velocityFloor ≤ F.resolvedVelocityWeight
  bandVelocityWeight_ge : S.band ≠ ∅ → (1 + 1 / F.share) * F.turnBound ^ 2 / F.strainFloor ≤ F.bandVelocityWeight
  localMatrix_const : ∀ n ∈ S.resolved, ∀ p ∈ K.rect, S.localMatrix n p = S.localMatrix n (K.r₁, K.z₁)
  actuator_poly : ∀ i : Fin k, ∀ n ∈ R.yModes, ∀ a b : Fin 3, ∃ P ∈ polyFn S.degNear S.degNear, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
    ((CellScalars.rHat K p : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b = P p
  pin_poly : ∀ i : Fin k, ∀ n ∈ R.yModes, ∀ a b : Fin 3, ∃ P ∈ polyFn S.degNear S.degNear, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
    ((CellScalars.rHat K p : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b = P p
  support_contains : ∀ n ∈ S.resolved, ∀ (a : Fin 3) (comp : Fin 4) (j l : ℕ), j ≤ S.degHigh → l ≤ S.degHigh →
    (n, a, comp, j, l) ∈ R.farSupport
  kernel_dominates : ∀ u : (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ,
    CellScalars.farMajorantForm c K S F u
      ≤ (∑ i ∈ R.farSupport.disjSum Finset.univ, ∑ i' ∈ R.farSupport.disjSum Finset.univ,
          (starRingEnd ℂ) (u i) * R.farKernel i i' * u i').re

def FarMajorantStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) {slots : ℕ} (R : CellRows N slots k) (F : FarMajorantData),
      IsCellBox K → K.solid ⊆ c.cellRegion → IsCellScalars α c K S → IsCellBases K B → S.resolved ∪ S.band ⊆ R.yModes →
      IsFarMajorant c K S B R F →
      ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
        CellScalars.farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R ≤ CellScalars.farFormValue c K S R B x ζ

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

end CellScalars

structure IsRowPolynomial {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (E : ℕ) : Prop where
  folded_poly : ∀ a ∈ R.rowSet, ∀ n' ∈ S.resolved ∪ S.band, ∀ i q : Fin 3,
    ∃ P ∈ polyFn E E, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → CellScalars.rowCouplingFolded c K S R a n' p i q = P p
  velocity_poly : ∀ a ∈ R.rowSet, ∀ n' ∈ S.resolved, ∀ i : Fin 3,
    ∃ P ∈ polyFn E E, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → CellScalars.rowCouplingVelocity c K R a n' p i = P p

def RowFarFiniteStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) {slots : ℕ}
    (R : CellRows N slots k) (E : ℕ), IsCellBox K → IsCellBases K B → IsRowPolynomial c K S R E →
    ∀ μ : Fin N → ℝ, CellScalars.rowSquareFar c K S R B μ = CellScalars.rowSquareUpTo c K S B R E μ

end CellAnalysis


namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshData

variable {k N : ℕ} {Sp : CellSplit k N} (M : MeshData k N Sp)

end MeshData

def StreamIndependenceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (cr cz oz oz' : ℝ), 0 < cr → oz ≠ cz → oz' ≠ cz →
      heightStripMoment cz oz 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)
        = heightStripMoment cz oz' 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)

def streamValue (L : CellLayout) {k : ℕ} (x : FieldTuple k) (r z oz : ℝ) : ℂ :=
  heightStripMoment z oz 0 r (fun ρ => ρ) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)

def FluxStreamStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (S : FaceSegment), IsFaceSegment S → ∀ (o o' : ℝ),
      (S.radial = true → 0 < S.level → 0 ≤ S.lo → o ≠ S.lo → o' ≠ S.hi → ∀ c0 : ℝ,
        (∀ z ∈ Set.Icc S.lo S.hi, (1 : ℝ) = c0 * S.test 0 z) →
          ((S.level * c0 : ℝ) : ℂ) * S.moment false (L.velMode 0 x 0) (L.gradModeOf 0 x 0 0) (L.gradModeOf 0 x 0 2) 0
            = streamValue L x S.level S.lo o - streamValue L x S.level S.hi o') ∧
      (S.radial = false → 0 ≤ S.lo → o ≠ S.level → o' ≠ S.level → ∀ c0 c1 : ℝ,
        (∀ r ∈ Set.Icc S.lo S.hi, r = c0 * S.test 0 r + c1 * S.test 1 r) →
          (c0 : ℂ) * S.moment false (L.velMode 0 x 2) (L.gradModeOf 0 x 2 0) (L.gradModeOf 0 x 2 2) 0
            + (c1 : ℂ) * S.moment false (L.velMode 0 x 2) (L.gradModeOf 0 x 2 0) (L.gradModeOf 0 x 2 2) 1
            = streamValue L x S.hi S.level o - streamValue L x S.lo S.level o') ∧
      (∀ r o, 0 ≤ r → o ≠ 0 → streamValue L x r 0 o = 0)

def MeshCompatibilityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      (∀ x, IsAdmissible c x → ∀ K j, ∑ i, (M.coords K).Tmap j i * M.canonicalMoment c x i =
          M.localValue c K x j) ∧
      (∀ K, ∀ r ∈ (M.coords K).gaugeSpec.roots, ∀ x, IsAdmissible c x →
          (M.coords K).layout.rootShifted (M.canonicalLeft K) (M.canonicalRight K) x r = 0) ∧
      (∀ K e, (M.coords K).gaugeSpec.edge = some e → ∀ x, IsAdmissible c x →
          M.canonicalRight K x = M.canonicalLeft K x + (M.coords K).layout.gaugeJump (M.coords K).gaugeSpec x) ∧
      (∀ K (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
          M.canonicalLeft K (a • x + b • y) = a * M.canonicalLeft K x + b * M.canonicalLeft K y ∧
            M.canonicalRight K (a • x + b • y) = a * M.canonicalRight K x + b * M.canonicalRight K y) ∧
      M.canonicalMoment c 0 = 0 ∧
      (∀ x x', IsAdmissible c x → IsAdmissible c x' →
          M.canonicalMoment c (x + x') = M.canonicalMoment c x + M.canonicalMoment c x') ∧
      (∀ (r : ℝ) x, IsAdmissible c x → M.canonicalMoment c (r • x) = r • M.canonicalMoment c x) ∧
      (∀ x, IsAdmissible c x → ∀ a, M.canonicalMoment c x (Sp.kappaSlot a) = x.2.2.2.1 a)

end CellCoordinates

end CellCert

end Breakdown
