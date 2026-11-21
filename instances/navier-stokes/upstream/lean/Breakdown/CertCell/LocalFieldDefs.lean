import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.ResolvedEnergySt
import Breakdown.FracCell.VelocityTailSt
import Breakdown.FracCell.ModeRadialWeak
import Breakdown.FracCell.StHeightModeIbp
import Breakdown.FracCell.StAngularMode
import Breakdown.FracCell.StCornerModesOpen

open scoped ContDiff
open MeasureTheory Matrix Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

structure IsLocalSecondOrderField (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop where
  measurable_velocity : AEStronglyMeasurable v volume
  measurable_gradient : AEStronglyMeasurable G volume
  measurable_second : AEStronglyMeasurable H volume
  velocity_six : MemLp v 6 volume
  gradient_two : Integrable (fun y => entrySq (G y))
  second_two : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
  weak_gradient : IsWeakGradientOf v G
  weak_second : IsWeakSecondDerivOf G H
  divergence : ∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (G y (unitVector i)) (unitVector i) = 0

def IsLocalAdmissible {k : ℕ} (x : FieldTuple k) : Prop :=
  IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 ∧ IsGradientField x.2.2.2.2

theorem isLocalSecondOrderField_of {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) :
    IsLocalSecondOrderField v G H :=
  ⟨h.measurable_velocity, h.measurable_gradient, h.measurable_second, h.velocity_six, h.gradient_two,
    h.second_two, h.weak_gradient, h.weak_second, h.divergence⟩

theorem isLocalAdmissible_of {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k} (h : IsAdmissible c x) :
    IsLocalAdmissible x :=
  ⟨isLocalSecondOrderField_of h.1, h.2.1⟩

def LocalRelationsHoldStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ : L.RelIndex, ∑ d, L.relationRow ρ d * L.trueData x d = 0

def LocalTrueParamStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ (P : ParamData L.Datum) (sel : Fin P.relCount → L.RelIndex), IsCellParam L P sel →
      ∀ x : FieldTuple k, IsLocalAdmissible x → P.param (L.trueData x) = L.trueData x

def LocalRelRadialCoefStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inl ρ) d * L.trueData x d) = 0

def LocalRelHeightCoefStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inl ρ)) d * L.trueData x d) = 0

def LocalRelTurnStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inl ρ))) d * L.trueData x d) = 0

def LocalRelTraceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ)))) d * L.trueData x d) = 0

def LocalRelZeroModeStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ))))) d * L.trueData x d) = 0

def LocalRelRadialSideStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ)))))) d
        * L.trueData x d) = 0

def LocalRelHeightSideStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ρ))))))) d
        * L.trueData x d) = 0

def LocalRelAxisStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl ρ)))))))) d * L.trueData x d) = 0

def LocalRelStreamStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl ρ))))))))) d * L.trueData x d) = 0

def LocalRelSideSplitStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x →
      ∀ ρ, (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr ρ))))))))) d * L.trueData x d) = 0

def LocalModeSquareIntegrableStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
      ∀ (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ),
        AEStronglyMeasurable (comboGrad κ m n G) (volume.restrict K.rect) ∧
        IntegrableOn (fun p => K.lineWeight p.1 * ‖comboGrad κ m n G p‖ ^ 2) K.rect ∧
        ∀ c : Fin 3, AEStronglyMeasurable (comboThird κ m n H c) (volume.restrict K.rect) ∧
          IntegrableOn (fun p => p.1 * ‖comboThird κ m n H c p‖ ^ 2) K.rect

def LocalModeRadialPartsStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
      ∀ (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) (ψ : ℝ × ℝ → ℂ), ContDiff ℝ 1 ψ →
        (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * comboThird κ m n H 0 p * ψ p
            = -∫ p in K.rect, comboGrad κ m n G p *
                CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p

def LocalModeHeightPartsStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
      ∀ (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) (ψ : ℝ × ℝ → ℂ), ContDiff ℝ 1 ψ →
        (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * comboThird κ m n H 2 p * ψ p
            = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * comboGrad κ m n G p * CellBox.heightDeriv ψ p

def LocalResolvedEnergyStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (Q q : ℕ), 3 ≤ q → q + 2 ≤ Q →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsLocalSecondOrderField v G H → ∀ n : ℤ, (K.IsAxis → n = 0) →
        K.strainEnergy m n Q q G H
            + ∑ a : Fin 3, ∑ b : Fin 3,
                (K.tailGradWeight Q (gradMode m n G a b) (radialGradMode m n H a b) (heightGradMode m n H a b)
                  + K.angularWeight n * K.tailNormSq Q (angularGradMode m n H a b))
          ≤ ∫ p in K.rect, p.1 * secondModeSq m n H p ∧
        K.vorticityEnergy m n Q q G H
            + ∑ i : Fin 3,
                (K.tailGradWeight Q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
                    (fun p => curlComp (fun a b => radialGradMode m n H a b p) i)
                    (fun p => curlComp (fun a b => heightGradMode m n H a b p) i)
                  + K.angularWeight n * K.tailNormSq Q (fun p => curlComp (fun a b => angularGradMode m n H a b p) i))
          ≤ ∫ p in K.rect, p.1 * curlGradModeSq m n H p

def LocalModeGradSquareStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsLocalSecondOrderField v G H → ∀ (n : ℤ) (a b : Fin 3),
        AEStronglyMeasurable (gradMode m n G a b) (volume.restrict K.rect) ∧
        IntegrableOn (fun p => K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2) K.rect

def LocalModeRadialWeakStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a 0 p) K.rect ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
        ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a + ((ψ p.1 : ℝ) : ℂ) * gradMode m n G a 0 p)
          * ((t p.2 : ℝ) : ℂ) = 0

def LocalModeRectIntegrableStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout),
    IsCellLayout c K S B L → ∀ x : FieldTuple k, IsLocalAdmissible x → ∀ (n : ℤ) (a b : Fin 3),
      IntegrableOn (L.velMode n x a) K.rect ∧ IntegrableOn (L.gradModeOf n x a b) K.rect

def LocalModeTraceStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → ∑ a : Fin 3, gradMode m n G a a p = 0

def LocalStripTraceStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ z₁ z₂ : ℝ, z₁ < z₂ → ∃ T : ℝ → ℂ, ∀ a b : ℝ, 0 ≤ a → a < b → ∀ α β : ℝ,
      ∫ p in Icc a b ×ˢ Icc z₁ z₂,
          ((α : ℂ) * modeVec m 0 v p.1 p.2 0 + ((α * p.1 + β : ℝ) : ℂ) * gradMode m 0 G 0 0 p)
        = ((α * b + β : ℝ) : ℂ) * T b - ((α * a + β : ℝ) : ℂ) * T a

def LocalRadialFluxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (R o z₁ z₂ : ℝ), 0 < R → 0 ≤ o → o ≠ R → z₁ < z₂ →
      (R : ℂ) * radialStripMoment R o z₁ z₂ (fun p => modeVec m 0 v p.1 p.2 0) (gradMode m 0 G 0 0)
          (fun _ => 1)
        = ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p)

def LocalHeightModeIbpStatement : Prop :=
  ∀ (m : ℕ) (n : ℤ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ K : CellBox, IsCellBox K → ∀ a : Fin 3,
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p) K.rect ∧
      ∀ f h : ℝ → ℝ, Continuous f → ContDiff ℝ 1 h → h K.z₁ = 0 → h K.z₂ = 0 →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a * ((f p.1 * deriv h p.2 : ℝ) : ℂ) =
          -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((f p.1 * h p.2 : ℝ) : ℂ)

def LocalAxisModeIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
      ∀ (R z₁ z₂ : ℝ) (n : ℤ) (a b : Fin 3),
        IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p) (Set.Icc 0 R ×ˢ Set.Icc z₁ z₂)

def LocalAxisFluxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
      ∀ (R z₁ z₂ : ℝ), 0 < R → z₁ < z₂ → ∀ (t : ℝ → ℝ), Continuous t → ∀ (i : ℕ) (σ : Fin 2),
        ((R * R ^ i : ℝ) : ℂ) * radialStripMoment R 0 z₁ z₂
            (fun p => modeVec m 0 v p.1 p.2 (if σ = 0 then 0 else 1))
            (gradMode m 0 G (if σ = 0 then 0 else 1) 0) t
          = (∫ p in Set.Icc 0 R ×ˢ Set.Icc z₁ z₂, ((p.1 * (((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) *
              (if σ = 0 then gradMode m 0 G 1 1 p else -gradMode m 0 G 0 1 p))
            + ∫ p in Set.Icc 0 R ×ˢ Set.Icc z₁ z₂, ((p.1 * p.1 ^ i * t p.2 : ℝ) : ℂ) *
              gradMode m 0 G (if σ = 0 then 0 else 1) 0 p

def LocalModeIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) K.rect ∧
      ∀ b : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect

def LocalAngularModeStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * gradMode m n G 0 1 p =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 0 - modeVec m n v p.1 p.2 1 ∧
      (p.1 : ℂ) * gradMode m n G 1 1 p =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 1 + modeVec m n v p.1 p.2 0 ∧
      (p.1 : ℂ) * gradMode m n G 2 1 p = ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 2

def LocalModeWeakIdentityStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (n : ℤ) (a : Fin 3) (ψ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a = -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a = -∫ p, (ψ p : ℂ) * gradMode m n G a 2 p) ∧
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * gradMode m n G a 2 p =
        -∫ p, (ψ p : ℂ) * modeThird m n H a 0 2 p) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a 0 p =
        -∫ p, (ψ p : ℂ) * modeThird m n H a 0 2 p)

def LocalModeStripIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (n : ℤ) (R z₁ z₂ : ℝ),
      (∀ a, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc 0 R ×ˢ Icc z₁ z₂)) ∧
        ∀ a b, IntegrableOn (gradMode m n G a b) (Icc 0 R ×ˢ Icc z₁ z₂)

def LocalCylinderFluxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v G H →
    ∀ (R o z₁ z₂ : ℝ), 0 < R → 0 ≤ o → o ≠ R → z₁ < z₂ →
      (R : ℂ) * radialStripMoment R o z₁ z₂ (fun p => modeVec m 0 v p.1 p.2 0) (gradMode m 0 G 0 0)
          (fun _ => 1)
        + heightStripMoment z₂ z₁ 0 R (fun r => r) (fun p => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2)
          (fun _ => 1)
        - heightStripMoment z₁ z₂ 0 R (fun r => r) (fun p => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2)
          (fun _ => 1) = 0

def LocalSideHeightPartsStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsLocalAdmissible x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (K : CellBox), IsCellBox K → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * L.velMode n x a p) K.rect ∧
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p) K.rect ∧
      ∀ (s φ φ' : ℝ → ℝ), Continuous s → Continuous φ' → (∀ z, HasDerivAt φ (φ' z) z) →
        φ K.z₁ = 0 → φ K.z₂ = 0 →
        ∫ p in K.rect, ((K.lineWeight p.1 : ℂ) * L.velMode n x a p * ((s p.1 * φ' p.2 : ℝ) : ℂ)
          + (K.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p * ((s p.1 * φ p.2 : ℝ) : ℂ)) = 0

end LocalField

end CertCell

end Breakdown
