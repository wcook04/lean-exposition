import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula

def IsBivariatePoly (M N : ℕ) (h : ℝ × ℝ → ℂ) : Prop :=
  ∃ a : ℕ → ℕ → ℂ, ∀ p : ℝ × ℝ,
    h p = ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range N, a i k * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k

def IsUnivariatePoly (N : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ a : ℕ → ℂ, ∀ u : ℝ, f u = ∑ i ∈ Finset.range N, a i * (u : ℂ) ^ i

def SegmentTestExpansionStatement : Prop :=
  ∀ (S : FaceSegment) (N : ℕ), (∀ d, S.testCoef d d ≠ 0) →
    (∀ d d', d < N → d' < N →
      ∫ u in Set.Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0) →
    ∀ f : ℝ → ℂ, IsUnivariatePoly N f →
      ∀ u : ℝ, f u = ∑ d ∈ Finset.range N, (∫ w in Set.Icc S.lo S.hi, f w * (S.test d w : ℂ)) * (S.test d u : ℂ)

def CellBasisExpansionStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B →
    ∀ (N : ℕ) (h : ℝ × ℝ → ℂ), IsBivariatePoly N N h →
      ∀ p : ℝ × ℝ, h p = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B j l x) * basisValue B j l p

end CellCalculus

end CertCell

end Breakdown
