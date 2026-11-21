import Breakdown.FracCell.StFormulaProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

theorem exactFormula_represents_of (hP : PolarizationStatement) (hQ : FormulaQuadraticStatement)
    (h1 : NearIdentityStatement) (h2 : RowYIdentityStatement)
    (h3 : FarIdentityStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N slots : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N slots k) (hd : IsCellData α c K S B Cl R) (hfar : R.farSupport ⊆ lowSupport S)
    (hv : 0 < c.splitVisc) (F : CellFormulaInputs k N S) (hF : IsFormulaInputs α c K S B Cl R.rowSet F) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      Finite.quadValue (F.exactFormula c K B R) (F.coordsOf x ζ c.splitVisc) ≤
        cellForm c K S R α B Cl x ζ / c.splitVisc := by
  intro x hx ζ
  let _ := F.dataFintype
  let _ := F.dataDecEq
  have hpol := hP (F.formulaValue c K B R) (hQ F c K B R hF.coord_linear) (F.coordsOf x ζ c.splitVisc)
  have hexact : F.exactFormula c K B R = polarized (F.formulaValue c K B R) := rfl
  rw [hexact, hpol]
  have hvne : c.splitVisc ≠ 0 := hv.ne'
  have hu : F.coordToData (fun e => F.coordsOf x ζ c.splitVisc
      (Sum.elim (fun s => Sum.inl s) (fun t => Sum.inr (Sum.inl t)) e)) = F.trueData x := by
    rw [← hF.data_represents x hx]
    congr 1
    funext e
    cases e <;> rfl
  have hκ : (fun i => c.splitVisc * F.coordsOf x ζ c.splitVisc (Sum.inr (Sum.inr (Sum.inl i)))) = x.2.2.2.1 := by
    funext i
    simp only [CellFormulaInputs.coordsOf, Sum.elim_inr, Sum.elim_inl]
    field_simp
  have hζ : (fun i => c.splitVisc * F.coordsOf x ζ c.splitVisc (Sum.inr (Sum.inr (Sum.inr i)))) = ζ := by
    funext i
    simp only [CellFormulaInputs.coordsOf, Sum.elim_inr]
    field_simp
  have haug : F.augOfData (F.trueData x) x.2.2.2.1 ζ = augVector c K S B x ζ := by
    funext e
    rcases e with i | i | i
    · simpa [CellFormulaInputs.augOfData, augVector] using hF.lowEntry_agree x hx i
    · rfl
    · rfl
  have hres : ∀ a ∈ R.rowSet, F.residualValue c K B R a (F.trueData x) x.2.2.2.1 ζ =
      rowResidual c K S R α B x ζ a := by
    intro a ha
    unfold CellFormulaInputs.residualValue rowResidual
    rw [haug, hF.row_value x hx a ha, h2 α hα₁ hα₂ c hc K S B Cl R hd x hx ζ a ha]
  have hsum : (∑ b : Fin R.reducerCount, (∑ a ∈ R.rowSet, R.reducer b a *
      F.residualValue c K B R a (F.trueData x) x.2.2.2.1 ζ) ^ 2) =
      ∑ b : Fin R.reducerCount, (∑ a ∈ R.rowSet, R.reducer b a * rowResidual c K S R α B x ζ a) ^ 2 := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl fun a ha => by rw [hres a ha]]
  have hloc := hF.local_form x hx ζ
  have hnear := h1 α hα₁ hα₂ c hc K S B Cl R hd x hx ζ
  have hfarv := h3 c K S B R hfar x ζ
  unfold CellFormulaInputs.formulaValue
  dsimp only
  rw [hu, hκ, hζ, haug, hsum, ← hnear, ← hfarv]
  unfold cellForm
  apply div_le_div_of_nonneg_right _ hv.le
  linarith
