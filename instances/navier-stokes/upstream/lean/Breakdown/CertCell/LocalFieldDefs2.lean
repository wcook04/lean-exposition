import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.StrainFaceDefs
import Breakdown.FracCell.StrainFaceFaceTraceFree
import Breakdown.FracCell.StrainFaceHeightNormal
import Breakdown.FracCell.StrainFaceRadialTangent
import Breakdown.FracCell.StrainFaceRadialTurn
import Breakdown.FracCell.StAngularHeightMode
import Breakdown.FracCell.StCornerModesOpen
import Breakdown.FracCell.EnergyRadialParts
import Breakdown.FracCell.EnergyHeightParts
import Breakdown.FracCell.StEnergyProof

open scoped ContDiff
open MeasureTheory Matrix Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

def LocalSideVelocityEvalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ), (e.val = 0 → K.r₁ ≠ 0) → IsPolyFn (L.degSide + 1) f →
        ∑ d, L.sideVelocityRow n e a f d * L.trueData x d = L.sideVelocityValue n x e a f

def LocalSideGradientEvalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : L.modes) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), (e.val = 0 → K.r₁ ≠ 0) → IsPolyFn L.degSide t →
        ∑ d, L.sideGradientRow n e a t d * L.trueData x d = L.sideGradientValue n x e a t

def LocalRadialTangentStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), e.val < 2 → (e.val = 0 → K.r₁ ≠ 0) → IsAnyPolyFn t →
        radialFaceMoment L.box (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (CellLayout.sideRadialIndex e) t =
          ((t L.box.z₂ : ℝ) : ℂ) * L.cornerValue n x (CellLayout.sideRadialIndex e) 1 a
            - ((t L.box.z₁ : ℝ) : ℂ) * L.cornerValue n x (CellLayout.sideRadialIndex e) 0 a
            - L.sideVelocityValue n x e a (deriv t)

def LocalRadialTurnStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), e.val < 2 → (e.val = 0 → K.r₁ ≠ 0) → IsAnyPolyFn t →
        radialFaceMoment L.box (L.gradModeOf n x a 1) (L.secondModeOf n x a 1 0) (CellLayout.sideRadialIndex e) t =
          ((1 / L.sideRadius e : ℝ) : ℂ) * L.turnValue n x e a t

def LocalHeightNormalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), 2 ≤ e.val → IsAnyPolyFn t →
        heightFaceMoment L.box (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 2) (CellLayout.sideHeightIndex e) t =
          ((L.box.r₂ * t L.box.r₂ : ℝ) : ℂ) * L.cornerValue n x 1 (CellLayout.sideHeightIndex e) a
            - ((L.box.r₁ * t L.box.r₁ : ℝ) : ℂ) * L.cornerValue n x 0 (CellLayout.sideHeightIndex e) a
            - L.sideVelocityValue n x e a (deriv (fun r => r * t r))

def LocalHeightTurnStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : ℤ) (e : Fin 4) (a : Fin 3) (t : ℝ → ℝ), 2 ≤ e.val → IsAnyPolyFn t →
        heightFaceMoment L.box (L.gradModeOf n x a 1) (L.secondModeOf n x a 1 2) (CellLayout.sideHeightIndex e) t =
          L.turnValue n x e a t

def LocalFaceTraceFreeStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : ℤ) (i : Fin 2) (t : ℝ → ℝ), IsAnyPolyFn t → (i = 0 → K.r₁ ≠ 0) →
        radialFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) i t
            + radialFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 0) i t
            + radialFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) i t = 0 ∧
          heightFaceMoment L.box (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 2) i t
            + heightFaceMoment L.box (L.gradModeOf n x 1 1) (L.secondModeOf n x 1 1 2) i t
            + heightFaceMoment L.box (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2) i t = 0

def LocalSideStripIntegrableStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
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

def LocalStrainFaceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ), l ≤ L.degSide → (e.val = 0 → K.r₁ ≠ 0) →
        L.strainFaceValue n x e a b l = ∑ d, L.strainFaceRow n e a b l d * L.trueData x d

def LocalAxisGradModeIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
      ∀ K : CellBox, IsCellBox K → K.r₁ = 0 → ∀ (n : ℤ) (a b : Fin 3), IntegrableOn (gradMode m n G a b) K.rect

def LocalRadialMixedWeakStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H → ∀ (n : ℤ) (a : Fin 3),
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
        ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * gradMode m n G a 2 p + ((ψ p.1 : ℝ) : ℂ) * modeThird m n H a 0 2 p)
          * ((t p.2 : ℝ) : ℂ) = 0

def LocalModeHeightAxisStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (n : ℤ) (a : Fin 3) (R Z : ℝ), IntegrableOn (gradMode m n G a 2) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z)

def LocalAngularHeightModeStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * modeThird m n H 0 1 2 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 0 2 p - gradMode m n G 1 2 p ∧
      (p.1 : ℂ) * modeThird m n H 1 1 2 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 1 2 p + gradMode m n G 0 2 p ∧
      (p.1 : ℂ) * modeThird m n H 2 1 2 p = ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 2 2 p

def LocalModeThirdSwapStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (n : ℤ) (a : Fin 3), ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → modeThird m n H a 2 0 p = modeThird m n H a 0 2 p

def LocalRadialStripIbpStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a : Fin 3) (c o : ℝ),
      ((c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁)) →
      IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 0 p) K.rect ∧
        IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) K.rect ∧
        ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h K.z₁ = 0 → h K.z₂ = 0 →
          ∫ p in K.rect,
            ((((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 0 p) * ((deriv h p.2 : ℝ) : ℂ)
              + (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) * ((h p.2 : ℝ) : ℂ)) = 0

def LocalGradModeAxisStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (n : ℤ) (a b : Fin 3) (R Z : ℝ), IntegrableOn (gradMode m n G a b) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z)

def LocalTurnRadialWeakStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p : ℝ × ℝ => gradMode m n G a 1 p) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a 1 0 p) K.rect ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
        ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * gradMode m n G a 1 p
          + ((ψ p.1 : ℝ) : ℂ) * modeThird m n H a 1 0 p) * ((t p.2 : ℝ) : ℂ) = 0

def LocalTurnSecondStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * modeThird m n H 0 1 0 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 0 0 p - gradMode m n G 1 0 p - gradMode m n G 0 1 p ∧
      (p.1 : ℂ) * modeThird m n H 1 1 0 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 1 0 p + gradMode m n G 0 0 p - gradMode m n G 1 1 p ∧
      (p.1 : ℂ) * modeThird m n H 2 1 0 p =
          ((azimuth m n : ℂ) * Complex.I) * gradMode m n G 2 0 p - gradMode m n G 2 1 p

def LocalRadialTraceStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H → ∀ (n : ℤ) (a b : Fin 3),
      IntegrableOn (gradMode m n G a b) K.rect ∧
      IntegrableOn (fun p => (p.1 : ℂ) * radialGradMode m n H a b p) K.rect ∧
      (K.r₁ ≠ 0 → IntegrableOn (radialGradMode m n H a b) K.rect) ∧
      ∀ (ψ t : ℝ → ℝ), ContDiff ℝ 1 ψ → Continuous t → (K.r₁ ≠ 0 ∨ ψ 0 = 0) →
        ∫ p in K.rect, (radialGradMode m n H a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ)
            + gradMode m n G a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) =
          ((ψ K.r₂ : ℝ) : ℂ) * radialFaceMoment K (gradMode m n G a b) (radialGradMode m n H a b) 1 t
            - ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K (gradMode m n G a b) (radialGradMode m n H a b) 0 t

def LocalHeightModeWeakStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a b : Fin 3),
      HeightWeakPair K (gradMode m n G a b) (heightGradMode m n H a b)

def LocalAngularFrameStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a b : Fin 3),
      ∀ᵐ p ∂(volume.restrict K.rect),
        angularGradMode m n H a b p =
          ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p

def LocalRepresentsStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      Represents K B (layoutIndex L) c.order x.1 x.2.1 x.2.2.1 (L.trueData x)

def RadialTracePair (K : CellBox) (F dF : ℝ × ℝ → ℂ) : Prop :=
  IntegrableOn F K.rect ∧ IntegrableOn (fun p => (p.1 : ℂ) * dF p) K.rect ∧
    (K.r₁ ≠ 0 → IntegrableOn dF K.rect) ∧
    ∀ (ψ t : ℝ → ℝ), ContDiff ℝ 1 ψ → Continuous t → (K.r₁ ≠ 0 ∨ ψ 0 = 0) →
      ∫ p in K.rect, (dF p * ((ψ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) =
        ((ψ K.r₂ : ℝ) : ℂ) * radialFaceMoment K F dF 1 t - ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K F dF 0 t

structure IsModeData {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ)
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ) : Prop where
  strain : ∀ n a b j l, u (I.strainSlot n a b j l) = B.coef K (F n a b) j l
  radial_face : ∀ n e a b l, (e = 0 → K.r₁ ≠ 0) →
    rowApply (I.radialFaceRow n e a b l) u = radialFaceMoment K (F n a b) (T n a b 0) e (B.heightPoly l)
  height_face : ∀ n e a b j,
    rowApply (I.heightFaceRow n e a b j) u = heightFaceMoment K (F n a b) (T n a b 2) e (B.radialPoly j)
  radial_trace : ∀ n a b, RadialTracePair K (F n a b) (T n a b 0)
  height_weak : ∀ n a b, HeightWeakPair K (F n a b) (T n a b 2)
  line_integrable : ∀ n a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F n a b p) K.rect
  angular_frame : ∀ n a b, ∀ᵐ p ∂(volume.restrict K.rect),
    (p.1 : ℂ) * T n a b 1 p = ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * F n a' b' p

def modeSum (C : Fin 3 → Fin 3 → ℂ) (F : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * F a b p

open Classical in
def LocalComponentRadialStatement : Prop :=
  ∀ {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ) (K : CellBox) (B : CellBases)
    (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ),
    IsCellBox K → IsCellBases K B → 1 ≤ q → q + 1 ≤ Q → IsModeData m K B I F T u →
    ∀ (n : modes) (C : Fin 3 → Fin 3 → ℂ),
      quadFormValue (radialProjForm K B I n C + (if K.r₁ = 0 then 0 else radialInnerForm K B I n C)
          + radialOuterForm K B I n C) u =
        K.radialEnergy Q q (modeSum C (F n)) (modeSum C (fun a b => T n a b 0))

open Classical in
def LocalComponentHeightStatement : Prop :=
  ∀ {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ) (K : CellBox) (B : CellBases)
    (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ),
    IsCellBox K → IsCellBases K B → 1 ≤ q → q + 1 ≤ Q → IsModeData m K B I F T u →
    ∀ (n : modes) (C : Fin 3 → Fin 3 → ℂ),
      quadFormValue (heightProjForm K B I n C + (if K.r₁ = 0 then 0 else heightInnerForm K B I n C)
          + heightOuterForm K B I n C) u =
        K.heightEnergy Q q (modeSum C (F n)) (modeSum C (fun a b => T n a b 2))

open Classical in
def LocalComponentAngularStatement : Prop :=
  ∀ {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ) (K : CellBox) (B : CellBases)
    (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ),
    IsCellBox K → IsCellBases K B → 1 ≤ q → q + 1 ≤ Q → IsModeData m K B I F T u →
    ∀ (n : modes) (C : Fin 3 → Fin 3 → ℂ),
      quadFormValue (if K.r₁ = 0 then angularAxisForm K B I n (angularArray (azimuth m n) C)
          else angularOffForm K B I n (angularArray (azimuth m n) C)) u =
        K.angularEnergy Q (modeSum C (fun a b p => (p.1 : ℂ) * T n a b 1 p))

def LocalEnergyValueStatement : Prop :=
  ∀ {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ) (K : CellBox) (B : CellBases)
    (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ),
    IsCellBox K → IsCellBases K B → 1 ≤ q → q + 1 ≤ Q → IsModeData m K B I F T u →
    ∀ (ew vw : ℤ → ℝ),
      quadFormValue (energyForm K B I m ew vw (fun _ => 0)) u =
        ∑ n : modes,
          (ew n * ∑ a : Fin 3, ∑ b : Fin 3,
              (K.radialEnergy Q q (F n a b) (T n a b 0) + K.heightEnergy Q q (F n a b) (T n a b 2)
                + K.angularEnergy Q (fun p => (p.1 : ℂ) * T n a b 1 p))
            + vw n * ∑ i : Fin 3,
              (K.radialEnergy Q q (fun p => curlComp (fun a b => F n a b p) i)
                  (fun p => curlComp (fun a b => T n a b 0 p) i)
                + K.heightEnergy Q q (fun p => curlComp (fun a b => F n a b p) i)
                  (fun p => curlComp (fun a b => T n a b 2 p) i)
                + K.angularEnergy Q (fun p => curlComp (fun a b => (p.1 : ℂ) * T n a b 1 p) i)))

def LocalModeDataPairStatement : Prop :=
  ∀ {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ) (K : CellBox) (B : CellBases)
    (I : LowIndex D modes Q q) (v₁ : Space → Space) (G₁ : Space → (Space →L[ℝ] Space))
    (H₁ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v₂ : Space → Space) (G₂ : Space → (Space →L[ℝ] Space))
    (H₂ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u₁ u₂ : D → ℂ),
    IsCellBox K → IsCellBases K B → IsLocalSecondOrderField v₁ G₁ H₁ → IsLocalSecondOrderField v₂ G₂ H₂ →
    Represents K B I m v₁ G₁ H₁ u₁ → Represents K B I m v₂ G₂ H₂ u₂ →
    IsModeData m K B I (fun n a b p => gradMode m n G₁ a b p + Complex.I * gradMode m n G₂ a b p)
      (fun n a b c p => modeThird m n H₁ a b c p + Complex.I * modeThird m n H₂ a b c p)
      (fun d => u₁ d + Complex.I * u₂ d)

def EnergyAeCongrStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q q : ℕ) (F F' dF dF' : ℝ × ℝ → ℂ),
    F =ᵐ[volume.restrict K.rect] F' → dF =ᵐ[volume.restrict K.rect] dF' →
      K.radialEnergy Q q F dF = K.radialEnergy Q q F' dF' ∧ K.heightEnergy Q q F dF = K.heightEnergy Q q F' dF' ∧
        K.angularEnergy Q F = K.angularEnergy Q F'

end LocalField

end CertCell

end Breakdown
