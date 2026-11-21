import Breakdown.FracCell.FormulaDataDefs

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

def IsRadialWeakPair (F dF : ℝ × ℝ → ℂ) : Prop :=
  (∀ R Z : ℝ, IntegrableOn F (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) ∧
      IntegrableOn (fun p => (p.1 : ℂ) * dF p) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z)) ∧
  (∀ δ R Z : ℝ, 0 < δ → IntegrableOn dF (Set.Icc δ R ×ˢ Set.Icc (-Z) Z)) ∧
  ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
    ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * dF p

def IsHeightWeakPair (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) : Prop :=
  (∀ R Z : ℝ, IntegrableOn (fun p => (wt p.1 : ℂ) * F p) (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z) ∧
      IntegrableOn (fun p => (wt p.1 : ℂ) * dF p) (Set.Icc (-R) R ×ˢ Set.Icc (-Z) Z)) ∧
  (∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn F {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn dF {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z}) ∧
  ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.1 ≠ 0) →
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * dF p

def radialStripTerm (c o : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ)

def heightStripTerm (c o : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * t p.1 : ℝ) : ℂ)

end Breakdown.CellCert.CellFormula
