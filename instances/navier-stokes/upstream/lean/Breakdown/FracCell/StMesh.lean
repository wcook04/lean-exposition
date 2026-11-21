import Breakdown.FracCell.MeshDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

def MeshSkeletonSlotStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      ∀ x, IsAdmissible c x → ∀ K j, ∑ i, (M.coords K).Tmap j i * M.canonicalMoment c x i =
          M.localValue c K x j

def MeshRootZeroStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      ∀ K, ∀ r ∈ (M.coords K).gaugeSpec.roots, ∀ x, IsAdmissible c x →
          (M.coords K).layout.rootShifted (M.canonicalLeft K) (M.canonicalRight K) x r = 0

def MeshEdgeJumpStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      ∀ K e, (M.coords K).gaugeSpec.edge = some e → ∀ x, IsAdmissible c x →
          M.canonicalRight K x = M.canonicalLeft K x + (M.coords K).layout.gaugeJump (M.coords K).gaugeSpec x

def MeshGaugeLinearStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      ∀ K (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
          M.canonicalLeft K (a • x + b • y) = a * M.canonicalLeft K x + b * M.canonicalLeft K y ∧
            M.canonicalRight K (a • x + b • y) = a * M.canonicalRight K x + b * M.canonicalRight K y

def MeshMomentLinearStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      M.canonicalMoment c 0 = 0 ∧
      (∀ x x', IsAdmissible c x → IsAdmissible c x' →
          M.canonicalMoment c (x + x') = M.canonicalMoment c x + M.canonicalMoment c x') ∧
      (∀ (r : ℝ) x, IsAdmissible c x → M.canonicalMoment c (r • x) = r • M.canonicalMoment c x) ∧
      (∀ x, IsAdmissible c x → ∀ a, M.canonicalMoment c x (Sp.kappaSlot a) = x.2.2.2.1 a)

end CellCoordinates

end CellCert

end Breakdown
namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

def FluxRadialStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (S : FaceSegment), IsFaceSegment S → ∀ (o o' : ℝ),
      S.radial = true → 0 < S.level → 0 ≤ S.lo → o ≠ S.lo → o' ≠ S.hi → ∀ c0 : ℝ,
        (∀ z ∈ Set.Icc S.lo S.hi, (1 : ℝ) = c0 * S.test 0 z) →
          ((S.level * c0 : ℝ) : ℂ) * S.moment false (L.velMode 0 x 0) (L.gradModeOf 0 x 0 0) (L.gradModeOf 0 x 0 2) 0
            = streamValue L x S.level S.lo o - streamValue L x S.level S.hi o'

def FluxHeightStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (S : FaceSegment), IsFaceSegment S → ∀ (o o' : ℝ),
      S.radial = false → 0 ≤ S.lo → o ≠ S.level → o' ≠ S.level → ∀ c0 c1 : ℝ,
        (∀ r ∈ Set.Icc S.lo S.hi, r = c0 * S.test 0 r + c1 * S.test 1 r) →
          (c0 : ℂ) * S.moment false (L.velMode 0 x 2) (L.gradModeOf 0 x 2 0) (L.gradModeOf 0 x 2 2) 0
            + (c1 : ℂ) * S.moment false (L.velMode 0 x 2) (L.gradModeOf 0 x 2 0) (L.gradModeOf 0 x 2 2) 1
            = streamValue L x S.hi S.level o - streamValue L x S.lo S.level o'

def StreamPlaneStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ r o, 0 ≤ r → o ≠ 0 → streamValue L x r 0 o = 0

end CellCoordinates

end CellCert

end Breakdown
