import Breakdown.CertCell.RowsMatchAssemble
import Breakdown.CertCell.RowsMatchKeyRows
import Breakdown.CertCell.RowsMatchFlux
import Breakdown.CertCell.RowsMatchDerivedNormal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

theorem keyRowsMatchHolds_of
    (hS : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyHeadMatch D R T.keyLayout)
    (hX : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyEvalTransfer D T.keyLayout) :
    KeyRowsMatchHolds := by
  intro k C nE nM D R e T W h q v G H g Pg hfh κ K d ⟨rd, re, im, hw⟩ _
  exact keyRow_fields W (hS D R e T W h) (hX D R e T W h) h.field_gauge h.gauge_keys.values h.real_keys h.transport
    h.cell_conditions hfh κ K d rd re im hw

theorem fluxRowsMatchHolds_of
    (hF : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyFluxHolds D)
    (hM : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → SideVelocityKeyMatch D R T) :
    FluxRowsMatchHolds := by
  intro k C nE nM D R e T W h q v G H g Pg hfh κ K d ⟨w, hw⟩ hprev
  exact fluxRow_fields W (hF D R e T W h) (hM D R e T W h) (TreeEntry.fieldKeyConj_holds T) h.field_gauge
    h.cell_conditions h.rows.key_order hfh κ K d w hw hprev

theorem splitRowsMatchHolds_of
    (hS : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyHeadMatch D R T.keyLayout)
    (hX : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyEvalTransfer D T.keyLayout)
    (hA : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeySplitAdditive D T.keyLayout)
    (hF : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyFluxHolds D) :
    SplitRowsMatchHolds := by
  intro k C nE nM D R e T W h q v G H g Pg hfh κ K d ⟨w, hw⟩ _
  exact splitRow_fields W (hS D R e T W h) (hX D R e T W h) (hA D R e T W h) h.field_gauge h.gauge_keys.values
    h.real_keys h.transport h.cell_conditions hfh κ K d w hw
    (fun hgeom j hj => tileFlux_fields W (hF D R e T W h) (TreeEntry.fieldKeyConj_holds T) h.field_gauge
      h.cell_conditions h.rows.key_order hfh κ K d w hgeom hw j hj)

theorem derivedRowsMatchHolds_of
    (hP : ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → IsPeriodicSecondOrder v G H) :
    DerivedRowsMatchHolds := by
  intro k C nE nM D R e T W h q v G H g Pg hfh κ K d ⟨rows, mult, hw⟩ hprev
  obtain ⟨-, -, hpert, hPg, -⟩ := hfh
  exact W.derived_row_fields K d rows mult hw v G H Pg κ
    (fun ρ => h.relations _ _ _ _ _ ((h.cell_conditions.layouts_valid K).layout_valid d.1.1 d.1.2) v G H Pg
      (hP _ _ v G H g hpert) hPg _ ρ)
    (fun d' hne hc => hprev ⟨d.1, d'⟩ (hw.2.2.1 d' hne hc).1 (hw.2.2.1 d' hne hc).2)

theorem normalRowsMatchHolds_of (hN : NormalSegmentHolds) : NormalRowsMatchHolds := by
  intro k C nE nM D R e T W h q v G H g Pg hfh κ K d ⟨pcoef, pdeg, hw⟩ hprev
  obtain ⟨-, -, hpert, hPg, -⟩ := hfh
  exact W.normal_row_fields K d pcoef pdeg hw v G H Pg κ
    (hN _ _ _ _ _ ((h.cell_conditions.layouts_valid K).layout_valid d.1.1 d.1.2) _ _ v G H g Pg hpert hPg _)
    (fun e hr hu => hprev ⟨d.1, e⟩ hr hu)

theorem rowsMatchFieldsHolds_of_parts
    (hS : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyHeadMatch D R T.keyLayout)
    (hX : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyEvalTransfer D T.keyLayout)
    (hA : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeySplitAdditive D T.keyLayout)
    (hF : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → KeyFluxHolds D)
    (hM : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
      (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → SideVelocityKeyMatch D R T)
    (hP : ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → IsPeriodicSecondOrder v G H)
    (hN : NormalSegmentHolds) : RowsMatchFieldsHolds :=
  rowsMatchFieldsHolds_of_kinds (keyRowsMatchHolds_of hS hX) (splitRowsMatchHolds_of hS hX hA hF)
    (fluxRowsMatchHolds_of hF hM) (derivedRowsMatchHolds_of hP) (normalRowsMatchHolds_of hN)

end Assembly

end CertCell

end Breakdown
