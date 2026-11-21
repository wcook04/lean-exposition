import Breakdown.FracCell.EnergyDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

structure EnergySetting (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N)
    (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ) : Prop where
  modes_eq : modes = S.resolved
  degHigh_eq : Q = S.degHigh
  degLow_eq : q = S.degLow
  box : IsCellBox K
  bases : IsCellBases K B
  scalars : IsCellScalars α c K S
  field : IsSecondOrderField c.order v G H
  represents : Represents K B I c.order v G H u
  form : IsFormData α c

def IsClassRegular (K : CellBox) (Cl : CellClasses) : Prop :=
  ∀ i, Measurable (Cl.strainDev i) ∧ Measurable (Cl.gradDev i) ∧ Measurable (Cl.velocityDev i) ∧
    Measurable (Cl.curlDev i) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C ∧ |Cl.gradDev i p| ≤ C ∧
      |Cl.velocityDev i p| ≤ C ∧ |Cl.curlDev i p| ≤ C

def strainField (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (C : Fin 3 → Fin 3 → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradMode m n G a b p

def radialField (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (C : Fin 3 → Fin 3 → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * radialGradMode m n H a b p

def heightField (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (C : Fin 3 → Fin 3 → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * heightGradMode m n H a b p

def angularField (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (C : Fin 3 → Fin 3 → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * angularGradMode m n H a b p

open Classical in
def ComponentRadialStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ),
    EnergySetting α c K B S I v G H u → ∀ (n : modes) (C : Fin 3 → Fin 3 → ℂ),
      quadFormValue (radialProjForm K B I n C + (if K.r₁ = 0 then 0 else radialInnerForm K B I n C)
          + radialOuterForm K B I n C) u =
        K.radialEnergy Q q (strainField c.order n G C) (radialField c.order n H C)

open Classical in
def ComponentHeightStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ),
    EnergySetting α c K B S I v G H u → ∀ (n : modes) (C : Fin 3 → Fin 3 → ℂ),
      quadFormValue (heightProjForm K B I n C + (if K.r₁ = 0 then 0 else heightInnerForm K B I n C)
          + heightOuterForm K B I n C) u =
        K.heightEnergy Q q (strainField c.order n G C) (heightField c.order n H C)

def AngularFrameStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ),
    EnergySetting α c K B S I v G H u → ∀ (n : ℤ) (a b : Fin 3),
      ∀ᵐ p ∂(volume.restrict K.rect),
        angularGradMode c.order n H a b p =
          ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth c.order n) a b a' b' * gradMode c.order n G a' b' p

open Classical in
def ComponentAngularStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ),
    EnergySetting α c K B S I v G H u → ∀ (n : modes) (C : Fin 3 → Fin 3 → ℂ),
      quadFormValue (if K.r₁ = 0 then angularAxisForm K B I n (angularArray (azimuth c.order n) C)
          else angularOffForm K B I n (angularArray (azimuth c.order n) C)) u =
        K.angularEnergy Q (angularField c.order n H C)

def TopFormStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ),
    EnergySetting α c K B S I v G H u → ∀ n : modes,
      quadFormValue (topForm I n) u =
        ∑ a : Fin 3, K.topPart Q (gradMode c.order n G a 0) (gradMode c.order n G a 2)

def ClassFormStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) (Cl : CellClasses) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u → IsClassRegular K Cl →
      quadFormValue (classForm K B S Cl I) u = CellScalars.classTerm c K S Cl v G

def PairFormStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u →
      quadFormValue (pairForm c K B S I) u = CellScalars.localPairForm c K S v G

def CrossFormStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) (Cl : CellClasses) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u → ∀ κ ζ : Fin k → ℝ,
      quadFormValue (localForm c K B S Cl I) (dataVector u κ ζ) =
        quadFormValue (energyForm K B I c.order S.energyWeight S.vorticityWeight S.tailShift
            - classForm K B S Cl I + pairForm c K B S I) u
          + CellScalars.linearTerm c K S κ ζ G

def EnergyFormStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u →
      quadFormValue (energyForm K B I c.order S.energyWeight S.vorticityWeight S.tailShift) u =
        CellScalars.energyTerm c K S G H

end CellEnergy

end CellCert

end Breakdown

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

def LocalFormBoundStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N)
    (K : CellBox) (B : CellBases) (S : CellScalars) (Cl : CellClasses)
    {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q), modes = S.resolved → Q = S.degHigh →
    q = S.degLow → IsCellBox K → IsCellBases K B →
    IsCellScalars α c K S → IsFormData α c → IsClassRegular K Cl → ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), SteadyCert.IsSecondOrderField c.order v G H →
    ∀ (u : D → ℂ), Represents K B I c.order v G H u → ∀ (κ ζ : Fin k → ℝ),
    quadFormValue (localForm c K B S Cl I) (dataVector u κ ζ) ≤
      CellScalars.localCellForm c K S Cl κ ζ v G H

end Breakdown.CellCert.CellEnergy

