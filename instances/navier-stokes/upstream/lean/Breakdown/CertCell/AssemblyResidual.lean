import Breakdown.CertCell.AssemblyStatements

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal

theorem residual_budget_with_slack (A S s c t : ℝ) (a b e d : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (he : e ≠ ⊤)
    (hd : d ≠ ⊤) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (h : A - S + s + c + b.toReal + e.toReal ≤ a.toReal + d.toReal + t) :
    ENNReal.ofReal A + ENNReal.ofReal (-S) + ENNReal.ofReal s + ENNReal.ofReal c + b + e
      ≤ a + d + ENNReal.ofReal S + ENNReal.ofReal (-A) + ENNReal.ofReal t := by
  have m1 := le_max_right A 0
  have m2 := le_max_right (-S) 0
  have m3 := le_max_right S 0
  have m4 := le_max_right (-A) 0
  have m5 := le_max_right t 0
  have tb : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have te : 0 ≤ e.toReal := ENNReal.toReal_nonneg
  have ta : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have td : 0 ≤ d.toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_toReal he,
    ← ENNReal.ofReal_toReal hd, ofReal_eq_ofReal_max A, ofReal_eq_ofReal_max (-S), ofReal_eq_ofReal_max S,
    ofReal_eq_ofReal_max (-A), ofReal_eq_ofReal_max t, ofReal_add_four m1 m2 hs hc,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg m1 m2) hs) hc) tb,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg (add_nonneg m1 m2) hs) hc) tb) te,
    ofReal_add_four ta td m3 m4,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg ta td) m3) m4) m5]
  apply ENNReal.ofReal_le_ofReal
  have h1 := max_sub_max_neg A
  have h2 := max_sub_max_neg S
  have h3 : t ≤ max t 0 := le_max_left _ _
  linarith

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem residual_rect_radius_nonneg (hmesh : IsCellMesh D.mesh) (K : Fin D.mesh.count) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) : 0 ≤ p.1 := by
  have hp' : p.1 ∈ Set.Icc (D.mesh.box K).r₁ (D.mesh.box K).r₂ := (Set.mem_prod.1 hp).1
  exact le_trans (hmesh.box_valid K).r_order.1 hp'.1

theorem residual_rect_measurable (K : Fin D.mesh.count) : MeasurableSet (D.mesh.box K).rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem residual_slack_nonneg (hmesh : IsCellMesh D.mesh) (K : Fin D.mesh.count) (L : Finset (ℤ × ℤ))
    (w : ℤ × ℤ → ℝ) (hw : ∀ ι ∈ L, 0 < w ι) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    0 ≤ pairStrainSlack D K L w G := by
  unfold pairStrainSlack
  refine Finset.sum_nonneg fun ι hι => mul_nonneg (hw ι hι).le ?_
  refine setIntegral_nonneg (residual_rect_measurable D K) fun p hp => ?_
  exact mul_nonneg (residual_rect_radius_nonneg D hmesh K hp)
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)

theorem residual_credit_nonneg (hmesh : IsCellMesh D.mesh) (hpatch : ∀ j, Bridge.IsCreditPatch (R.creditPatch j))
    (K : Fin D.mesh.count) (v : ℝ → Space → Space) : 0 ≤ creditShare D R K v := by
  unfold creditShare
  refine Finset.sum_nonneg fun j _ => integral_nonneg_of_ae ?_
  refine ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right ?_
  refine (ae_restrict_iff' (residual_rect_measurable D K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h0 := residual_rect_radius_nonneg D hmesh K hp
  have hc : 0 ≤ (R.creditPatch j).charge p :=
    le_trans (hpatch j).charge_lower_pos.le ((hpatch j).charge_between p).1
  have hn : 0 ≤ cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p))
      + cnormSq (modeVel (-(flipLabel (R.creditPatch j).label)) v 0 (planePoint p)) :=
    add_nonneg (Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.sum_nonneg fun b _ => sq_nonneg _)
  exact mul_nonneg (mul_nonneg hc hn) h0

theorem residual_slack_split (K : Fin D.mesh.count) (hd : Disjoint (D.mesh.resolved K) (D.mesh.band K)) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    pairStrainSlack D K (R.pairSlackLabels K) (R.pairSlackWeight K) G
      = pairSlackAmount D R K (D.mesh.resolved K) G + pairSlackAmount D R K (D.mesh.band K) G
        + pairSlackAmount D R K (deactSlackLabels D R K) G := by
  have hD : deactSlackLabels D R K ∩ R.pairSlackLabels K = deactSlackLabels D R K :=
    Finset.inter_eq_left.2 (Finset.filter_subset _ _)
  unfold pairSlackAmount
  rw [hD]
  unfold pairStrainSlack
  have hU : D.mesh.resolved K ∩ R.pairSlackLabels K ∪ D.mesh.band K ∩ R.pairSlackLabels K
      ∪ deactSlackLabels D R K = R.pairSlackLabels K := by
    ext ι
    simp only [deactSlackLabels, Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    tauto
  have hd1 : Disjoint (D.mesh.resolved K ∩ R.pairSlackLabels K) (D.mesh.band K ∩ R.pairSlackLabels K) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hd)
  have hd2 : Disjoint (D.mesh.resolved K ∩ R.pairSlackLabels K ∪ D.mesh.band K ∩ R.pairSlackLabels K)
      (deactSlackLabels D R K) := by
    rw [Finset.disjoint_left]
    intro ι h1 h2
    simp only [deactSlackLabels, Finset.mem_union, Finset.mem_inter, Finset.mem_filter] at h1 h2
    tauto
  conv_lhs => rw [← hU]
  rw [Finset.sum_union hd2, Finset.sum_union hd1]

theorem residual_kappaSq_state (K : Fin D.mesh.count) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ) (η : Fin (R.portCount K) → ℂ) :
    kappaSq (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) = ∑ i, κ i ^ 2 := by
  unfold kappaSq
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cellState, Sum.elim_inr, Sum.elim_inl, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Internal

section Residual

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
  (A : AssemblyEntry D R)

theorem residualFormBound_of_stages (hfin : CellPiecesFinite D R) (hled : AllocationSplit D R)
    (hband : BandProfileIntegrable D) (hpot : PotentialStage D R A) (hpair : PairingStage D R A)
    (hrow : RowStage D R A) (htail : TailStage D R A) {S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop}
    (helim : EliminationStage D R A S) (hstates : CellStatesIn D R S) (hturn : BandProfileTurned D)
    (hmesh : IsCellMesh D.mesh) (hslack : ∀ K, ∀ ι ∈ R.pairSlackLabels K, 0 < R.pairSlackWeight K ι)
    (hpatch : ∀ j, Bridge.IsCreditPatch (R.creditPatch j))
    (hkappa : ∀ K, (A.blocks K).rowKappaCost ≤ R.kappaCost K) (K : Fin D.mesh.count) :
    IsResidualFormBound D R K (R.cellForm K - energyLeafForm D R K) := by
  intro q hq v G H g hv κ F Pg hFm hFp hF2 hP hPf hR ζ η
  by_cases hcp : cellPos D K q v G H = ⊤
  · rw [hcp]
    simp only [top_add]
    exact le_top
  have ht : IsCellTuple D K q v G H g κ F Pg :=
    { param := hq, perturbation := hv, pressure := hP, right_side := hR, pos_finite := lt_top_iff_ne_top.2 hcp,
      right_measurable := hFm, right_periodic := hFp, right_finite := hF2,
      pressure_flip := hPf }
  obtain ⟨hcN, hoP, hoN⟩ := hfin K q v G H g κ F Pg ht
  have hL := hled K q v G H g κ F Pg ht
  have h1 := hpot K q v G H g κ F Pg ht ζ η
  have h2 := hpair K q v G H g κ F Pg ht ζ η
  have h3 := hrow K q v G H g κ F Pg ht ζ η
  have h4 := htail K q v G H g κ F Pg ht ζ η
  have h5 := helim K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G)
    (hstates K q v G H g κ F Pg ht ζ η) (hband K q v G H g κ F Pg ht) (hturn K q v G H g κ F Pg ht)
  have hsum : ∑ ι ∈ D.mesh.resolved K, (totalStrainCost (A.blocks K) ι * tailStrainSq D R K ι G
        + totalVelCost (A.blocks K) ι * tailVelSq D R K ι v
        + (A.blocks K).potentialCurlCost ι * tailCurlSq D R K ι G)
      = ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).potentialStrainCost ι * tailStrainSq D R K ι G
          + (A.blocks K).potentialVelCost ι * tailVelSq D R K ι v
          + (A.blocks K).potentialCurlCost ι * tailCurlSq D R K ι G)
        + ∑ ι ∈ D.mesh.resolved K, (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G
        + ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).rowStrainCost ι * tailStrainSq D R K ι G
          + (A.blocks K).rowVelCost ι * tailVelSq D R K ι v) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    simp only [totalStrainCost, totalVelCost]
    ring
  have hsplit := Internal.residual_slack_split D R K (hmesh.band_apart K) G
  have hσ := Internal.residual_slack_nonneg D hmesh K (R.pairSlackLabels K) (R.pairSlackWeight K) (hslack K) G
  have hcr := Internal.residual_credit_nonneg D R hmesh hpatch K v
  have hcred : creditAmount D R K v = creditShare D R K v := rfl
  have hk := Internal.residual_kappaSq_state D R K v G H Pg κ ζ η
  have hkle : (A.blocks K).rowKappaCost * kappaSq (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
      ≤ R.kappaCost K * ∑ i, κ i ^ 2 := by
    rw [hk]
    exact mul_le_mul_of_nonneg_right (hkappa K) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  refine Internal.residual_budget_with_slack _ _ _ _ _ _ _ _ _ hcp hcN.ne hoP.ne hoN.ne hσ hcr ?_
  linarith

end Residual

section Rows

theorem rowStage_of_parts (hS : RowShareStackedHolds) (hR : RowRemovalHolds) : RowStageHolds := by
  intro k C nE nM D R A hReg hTF tauMax hT hC hB hE K q v G H g κ F Pg ht ζ η
  have h1 := hS D R A hReg hTF tauMax hT hC K F
  have h2 := hR D R A hReg hTF tauMax hT hC hB K q v G H g κ F Pg ht ζ η
  have h3 := hE K q v G H g κ F Pg ht ζ η
  rw [← h1] at h2
  linarith

end Rows

section CellLayerBreakdown

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem cellResidual_of_parts (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    {S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (h : ResidualParts D R A S) (hmesh : IsCellMesh D.mesh)
    (hslack : ∀ K, ∀ ι ∈ R.pairSlackLabels K, 0 < R.pairSlackWeight K ι)
    (hpatch : ∀ j, Bridge.IsCreditPatch (R.creditPatch j))
    (hkappa : ∀ K, (A.blocks K).rowKappaCost ≤ R.kappaCost K) :
    ∀ K, IsResidualFormBound D R K (R.cellForm K - energyLeafForm D R K) :=
  residualFormBound_of_stages D R A h.pieces_finite h.allocation h.band_integrable h.potential h.pairing h.rows
    h.tails h.elimination h.states_in h.band_turned hmesh hslack hpatch hkappa

theorem residualParts_of_holds (hF : CellPiecesFiniteHolds) (hL : AllocationSplitHolds) (hTF : TrueFieldRegularHolds)
    (hB : BandProfileIntegrableHolds) (hP : PotentialStageHolds) (hQ : PairingStageHolds) (hR : RowStageHolds)
    (hM : RowMomentExpansionHolds) (hT : TailStageHolds) (hTop : TopBoundHolds) (hE : EliminationStageHolds)
    (hBT : BandProfileTurnedHolds)
    (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R) (P : CouplingEntries D R)
    (hN : FormNegFinite D D.coercivity) (hc : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity)
    {T : TreeEntry D R} (W : RowEntry D R T) (h : AssemblyConditions D R A P W)
    (hS : CellStatesIn D R (InRowRange W)) : ResidualParts D R A (InRowRange W) := by
  have hreg := h.regular
  have htf := hTF D hreg.field
  have hfin := hF D R hreg htf h.mesh_valid h.cell_conditions h.coefficient_bounds hN hc h.charges_regular
  have hband := hB D h.mesh_valid
  obtain ⟨τ, hτ⟩ := h.row_values
  exact
    { pieces_finite := hfin
      allocation := hL D R hreg htf h.mesh_valid h.charges_regular htf.2.1 hfin
      band_integrable := hband
      potential := hP D R A P _ hreg htf hfin hS h.potential
      pairing := hQ D R A P.pairing _ hreg htf hS h.pairing
      rows := hR D R A hreg htf τ hτ h.rows hband
        (hM D R A P _ hreg htf τ hτ hS h.potential h.rows h.row_functionals)
      tails := hT D R A hreg htf h.tails (hTop D R A hreg htf _ h.cell_conditions hS h.top_block)
      band_turned := hBT D h.mesh_valid
      states_in := hS
      elimination := hE D R A _ hreg htf h.elimination }

theorem cellResidual_of_conditions (hF : CellPiecesFiniteHolds) (hL : AllocationSplitHolds) (hTF : TrueFieldRegularHolds)
    (hB : BandProfileIntegrableHolds) (hP : PotentialStageHolds) (hQ : PairingStageHolds) (hR : RowStageHolds)
    (hM : RowMomentExpansionHolds) (hT : TailStageHolds) (hTop : TopBoundHolds) (hE : EliminationStageHolds)
    (hBT : BandProfileTurnedHolds)
    (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R) (P : CouplingEntries D R)
    (T : TreeEntry D R) (W : RowEntry D R T)
    (hN : FormNegFinite D D.coercivity) (hc : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity)
    (hslack : ∀ K, ∀ ι ∈ R.pairSlackLabels K, 0 < R.pairSlackWeight K ι)
    (h : AssemblyConditions D R A P W) (hS : CellStatesIn D R (InRowRange W)) :
    ∀ K, IsResidualFormBound D R K (R.cellForm K - energyLeafForm D R K) :=
  cellResidual_of_parts D R A (residualParts_of_holds hF hL hTF hB hP hQ hR hM hT hTop hE hBT D R A P hN hc W h hS)
    h.mesh_valid hslack h.potential.credit_patches h.rows.kappa_cell

end CellLayerBreakdown

end Assembly

end CertCell

end Breakdown
