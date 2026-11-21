import Breakdown.CertCell.RowsMatchNormalField
import Breakdown.CertCell.GaugePlaneFlipFacts

noncomputable section

namespace Breakdown.CertCell.SegmentNormal

open CellCert.CellAnalysis CellCert.CellFormula Breakdown.CertCell.Assembly

theorem normalSegmentIdentity_combine (L : CellLayout) (f g : L.Datum → ℂ) (hf : NormalSegmentIdentity L f)
    (hg : NormalSegmentIdentity L g) : NormalSegmentIdentity L (fun d => f d + Complex.I * g d) := by
  intro n s deg c₀ c₁ pcoef pdeg h1 h2 h3
  obtain ⟨f1, f2⟩ := hf n s deg c₀ c₁ pcoef pdeg h1 h2 h3
  obtain ⟨g1, g2⟩ := hg n s deg c₀ c₁ pcoef pdeg h1 h2 h3
  have hv : ∀ (a : Fin 3) (i : ℕ), velVal L (fun d => f d + Complex.I * g d) n s a i =
      velVal L f n s a i + Complex.I * velVal L g n s a i := by
    intro a i
    unfold velVal
    split_ifs <;> simp
  have hc : ∀ (c : Option (Fin L.cornerCount)) (a : Fin 3), cornerVal L (fun d => f d + Complex.I * g d) n c a =
      cornerVal L f n c a + Complex.I * cornerVal L g n c a := by
    intro c a
    cases c <;> simp [cornerVal]
  have hs : ∀ (a : Fin 3), ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L (fun d => f d + Complex.I * g d) n s a i =
      ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L f n s a i
        + Complex.I * ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L g n s a i := by
    intro a
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hv]; ring)
  constructor
  · intro hr hl hp
    rw [hs, hv, hv, hc, hc]
    show f _ + Complex.I * g _ = _
    rw [f1 hr hl hp, g1 hr hl hp]
    ring
  · intro hr hp
    rw [hs, hv, hc, hc]
    show f _ + Complex.I * g _ = _
    rw [f2 hr hp, g2 hr hp]
    ring

theorem normalSegmentHolds_of (hH : CellCalculus.HarmonicLiftStatement)
    (hP : PlaneFlipFacts.PeriodicSecondOrderHolds) : NormalSegmentHolds := by
  intro m K B modes L hlay Γ P v G H g Pg hpert _ ν
  obtain ⟨cd, S, -, -, hcl⟩ := hlay
  obtain ⟨hc, hs, -⟩ := hH m v G H (hP Γ P v G H g hpert) ν
  exact normalSegmentIdentity_combine L _ _
    (normalSegmentIdentity_trueData hcl (CellCalculus.cosTuple ν v G H Pg) hc)
    (normalSegmentIdentity_trueData hcl (CellCalculus.sinTuple ν v G H Pg) hs)

end Breakdown.CertCell.SegmentNormal
