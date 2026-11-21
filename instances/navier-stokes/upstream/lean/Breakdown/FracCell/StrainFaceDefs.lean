import Breakdown.FracCell.FormulaDataDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def IsPolyFn (D : ℕ) (f : ℝ → ℝ) : Prop := ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ u, f u = p.eval u

def IsAnyPolyFn (f : ℝ → ℝ) : Prop := ∃ p : Polynomial ℝ, ∀ u, f u = p.eval u

namespace CellLayout

variable (L : CellLayout)

def sideVelocityValue {k : ℕ} (n : ℤ) (x : FieldTuple k) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ) : ℂ :=
  if e.val < 2 then radialFaceMoment L.box (L.velMode n x a) (L.gradModeOf n x a 0) (sideRadialIndex e) f
  else if sideHeightIndex e = 1 then
    heightStripMoment L.box.z₂ L.box.z₁ L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2) f
  else heightStripMoment L.box.z₁ L.box.z₂ L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2) f

def sideGradientValue {k : ℕ} (n : ℤ) (x : FieldTuple k) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ) : ℂ :=
  if e.val < 2 then radialFaceMoment L.box (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) (sideRadialIndex e) t
  else heightFaceMoment L.box (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2) (sideHeightIndex e) t

def cornerValue {k : ℕ} (n : ℤ) (x : FieldTuple k) (i j : Fin 2) (a : Fin 3) : ℂ :=
  cornerMoment (if i = 0 then L.box.r₁ else L.box.r₂) (if i = 0 then L.box.r₂ else L.box.r₁)
    (if j = 0 then L.box.z₁ else L.box.z₂) (if j = 0 then L.box.z₂ else L.box.z₁)
    (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) (L.secondModeOf n x a 0 2)

def turnValue {k : ℕ} (n : ℤ) (x : FieldTuple k) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ) : ℂ :=
  if a = 0 then (azimuth L.order n : ℂ) * Complex.I * L.sideVelocityValue n x e 0 f - L.sideVelocityValue n x e 1 f
  else if a = 1 then (azimuth L.order n : ℂ) * Complex.I * L.sideVelocityValue n x e 1 f + L.sideVelocityValue n x e 0 f
  else (azimuth L.order n : ℂ) * Complex.I * L.sideVelocityValue n x e 2 f

end CellLayout

def SideVelocityEvalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ), (e.val = 0 → K.r₁ ≠ 0) → IsPolyFn (L.degSide + 1) f →
        ∑ d, L.sideVelocityRow n e a f d * L.trueData x d = L.sideVelocityValue n x e a f

def SideGradientEvalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : L.modes) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), (e.val = 0 → K.r₁ ≠ 0) → IsPolyFn L.degSide t →
        ∑ d, L.sideGradientRow n e a t d * L.trueData x d = L.sideGradientValue n x e a t

def RadialTangentStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), e.val < 2 → (e.val = 0 → K.r₁ ≠ 0) → IsAnyPolyFn t →
        radialFaceMoment L.box (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (CellLayout.sideRadialIndex e) t =
          ((t L.box.z₂ : ℝ) : ℂ) * L.cornerValue n x (CellLayout.sideRadialIndex e) 1 a
            - ((t L.box.z₁ : ℝ) : ℂ) * L.cornerValue n x (CellLayout.sideRadialIndex e) 0 a
            - L.sideVelocityValue n x e a (deriv t)

def RadialTurnStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), e.val < 2 → (e.val = 0 → K.r₁ ≠ 0) → IsAnyPolyFn t →
        radialFaceMoment L.box (L.gradModeOf n x a 1) (L.secondModeOf n x a 1 0) (CellLayout.sideRadialIndex e) t =
          ((1 / L.sideRadius e : ℝ) : ℂ) * L.turnValue n x e a t

def HeightNormalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), 2 ≤ e.val → IsAnyPolyFn t →
        heightFaceMoment L.box (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 2) (CellLayout.sideHeightIndex e) t =
          ((L.box.r₂ * t L.box.r₂ : ℝ) : ℂ) * L.cornerValue n x 1 (CellLayout.sideHeightIndex e) a
            - ((L.box.r₁ * t L.box.r₁ : ℝ) : ℂ) * L.cornerValue n x 0 (CellLayout.sideHeightIndex e) a
            - L.sideVelocityValue n x e a (deriv (fun r => r * t r))

def HeightTurnStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), 2 ≤ e.val → IsAnyPolyFn t →
        heightFaceMoment L.box (L.gradModeOf n x a 1) (L.secondModeOf n x a 1 2) (CellLayout.sideHeightIndex e) t =
          L.turnValue n x e a t

def FaceTraceFreeStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : ℤ) (i : Fin 2) (t : ℝ → ℝ), IsAnyPolyFn t →
        radialFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) i t
            + radialFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 0) i t
            + radialFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) i t = 0 ∧
          heightFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 2) i t
            + heightFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 2) i t
            + heightFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2) i t = 0

namespace CellLayout

variable (L : CellLayout)

def sideLevel (e : Fin 4) : ℝ :=
  if e.val = 0 then L.box.r₁ else if e.val = 1 then L.box.r₂ else if e.val = 2 then L.box.z₁ else L.box.z₂

def sideOther (e : Fin 4) : ℝ :=
  (if e.val < 2 then L.box.r₁ + L.box.r₂ else L.box.z₁ + L.box.z₂) - L.sideLevel e

end CellLayout

def SideStripIntegrableStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3), (e.val = 0 → K.r₁ ≠ 0) →
        (e.val < 2 →
          IntegrableOn (fun p : ℝ × ℝ => (((1 / (L.sideLevel e - L.sideOther e) : ℝ)) : ℂ) * L.velMode n x a p
              + (((p.1 - L.sideOther e) / (L.sideLevel e - L.sideOther e) : ℝ) : ℂ) * L.gradModeOf n x a 0 p)
            (Set.Icc (min (L.sideLevel e) (L.sideOther e)) (max (L.sideLevel e) (L.sideOther e)) ×ˢ
              Set.Icc L.box.z₁ L.box.z₂) ∧
          IntegrableOn (fun p : ℝ × ℝ => (((1 / (L.sideLevel e - L.sideOther e) : ℝ)) : ℂ) * L.gradModeOf n x a 0 p
              + (((p.1 - L.sideOther e) / (L.sideLevel e - L.sideOther e) : ℝ) : ℂ) * L.secondModeOf n x a 0 0 p)
            (Set.Icc (min (L.sideLevel e) (L.sideOther e)) (max (L.sideLevel e) (L.sideOther e)) ×ˢ
              Set.Icc L.box.z₁ L.box.z₂)) ∧
        (2 ≤ e.val →
          IntegrableOn (fun p : ℝ × ℝ => ((((1 / (L.sideLevel e - L.sideOther e) : ℝ)) : ℂ) * L.velMode n x a p
              + (((p.2 - L.sideOther e) / (L.sideLevel e - L.sideOther e) : ℝ) : ℂ) * L.gradModeOf n x a 2 p)
              * ((1 : ℝ) : ℂ))
            (Set.Icc L.box.r₁ L.box.r₂ ×ˢ
              Set.Icc (min (L.sideLevel e) (L.sideOther e)) (max (L.sideLevel e) (L.sideOther e))) ∧
          IntegrableOn (fun p : ℝ × ℝ => ((((1 / (L.sideLevel e - L.sideOther e) : ℝ)) : ℂ) * L.gradModeOf n x a 2 p
              + (((p.2 - L.sideOther e) / (L.sideLevel e - L.sideOther e) : ℝ) : ℂ) * L.secondModeOf n x a 2 2 p)
              * ((p.1 : ℝ) : ℂ))
            (Set.Icc L.box.r₁ L.box.r₂ ×ˢ
              Set.Icc (min (L.sideLevel e) (L.sideOther e)) (max (L.sideLevel e) (L.sideOther e))))

end CellFormula

end CellCert

end Breakdown
