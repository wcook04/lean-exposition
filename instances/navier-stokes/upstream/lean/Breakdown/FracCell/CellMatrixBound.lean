import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

open Classical in
private lemma systemVector_eq_of_mem (L : CellLayout) (P : ParamData L.Datum) (f : L.Datum → ℝ)
    (u : L.Datum × Fin 2 → ℝ)
    (s : Fin (systemSkeletonCoords L P).card → ℝ) (ξ : Fin (systemInteriorCoords L P).card → ℝ)
    (hs : ∀ j, s j = u ((systemSkeletonCoords L P).equivFin.symm j).1 / f ((systemSkeletonCoords L P).equivFin.symm j).1.1)
    (hξ : ∀ j, ξ j = u ((systemInteriorCoords L P).equivFin.symm j).1 / f ((systemInteriorCoords L P).equivFin.symm j).1.1)
    (p : L.Datum × Fin 2) (hp : L.IsSystemCoord p) (hm : p.1 ∈ P.skeleton ∨ p.1 ∈ P.interiorSet) :
    systemVector L P s ξ p = u p / f p.1 := by
  unfold systemVector
  split_ifs with h h'
  · rw [hs]; simp
  · rw [hξ]; simp
  · exfalso
    rcases hm with hm | hm
    · exact h (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, hp⟩)
    · exact h' (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, hp⟩)

private lemma expandSystem_div_of_mem (L : CellLayout) (P : ParamData L.Datum) (hconj : IsConjClosedParam L P)
    (f : L.Datum → ℝ) (hf : ∀ d, f (L.conjDatum d) = f d) (u v : L.Datum × Fin 2 → ℝ)
    (h : ∀ p, L.IsSystemCoord p → (p.1 ∈ P.skeleton ∨ p.1 ∈ P.interiorSet) → v p = u p / f p.1)
    (q : L.Datum × Fin 2) (hq : q.1 ∈ P.skeleton ∨ q.1 ∈ P.interiorSet) :
    L.expandSystem v q = L.expandSystem u q / f q.1 := by
  have hq' : L.conjDatum q.1 ∈ P.skeleton ∨ L.conjDatum q.1 ∈ P.interiorSet := by
    rcases hq with hq | hq
    · exact Or.inl ((hconj q.1).1.1 hq)
    · right
      simp only [ParamData.interiorSet, ParamData.freeSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hq ⊢
      exact ⟨fun hh => hq.1 ((hconj q.1).2.2 hh), fun hh => hq.2 ((hconj q.1).1.2 hh)⟩
  unfold CellLayout.expandSystem
  split_ifs with h1 h2
  · exact h q h1 hq
  · rw [h _ h2.2 hq', hf, mul_div_assoc]
  · simp

private lemma presetScale_conj (L : CellLayout) (visc : ℝ) (d : L.Datum) :
    presetScale L visc (L.conjDatum d) = presetScale L visc d := by
  rcases d with d | d | d | d | d | d | d | d <;> rfl

private lemma presetScale_ne (L : CellLayout) {visc : ℝ} (hv : 0 < visc) (d : L.Datum) :
    presetScale L visc d ≠ 0 := by
  unfold presetScale
  split_ifs
  · exact hv.ne'
  · exact one_ne_zero

theorem cellMatrix_le_cellForm_of_parts (h1 : ExactFormulaBoundStatement) (h2 : CanonicalInputsValidStatement)
    (h3 : ShiftedRealReductionStatement) (h4 : GaugeShiftOfStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ}
    (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N) (hS : ∀ x, IsAdmissible c x → ∀ i,
      Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i) (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hconj : IsConjClosedParam C.layout C.param) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ 4 * Real.pi * CellScalars.cellForm c K S R α B Cl x ζ := by
  intro x hx ζ
  have hν := hC.visc_pos
  obtain ⟨hg, hzero⟩ := h4 c K S B C.layout C.gaugeSpec hC.layout_valid hC.gauge_spec C.gaugeLeft C.gaugeRight
    hC.gauge_linear hC.edge_jump hC.root_zero
  set u := C.layout.realPart (C.layout.shiftedData (C.layout.gaugeShiftOf C.gaugeLeft C.gaugeRight) x) with hu
  have hred : C.layout.expandSystem u = u :=
    h3 c K S B C.layout _ hC.layout_valid hg x hx (hzero x hx)
  have hTF : C.Tmap * Sp.freeMap = 0 := by
    ext j i
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact hC.skeleton_free j i
  set s : Fin (systemSkeletonCoords C.layout C.param).card → ℝ :=
    fun j => ∑ i, C.Tmap j i * Sp.stateOf x ζ (Sum.inl i) with hsdef
  have hs : ∀ j, s j = u ((systemSkeletonCoords C.layout C.param).equivFin.symm j).1 /
      presetScale C.layout c.splitVisc ((systemSkeletonCoords C.layout C.param).equivFin.symm j).1.1 := by
    intro j
    have e1 : s j = (C.Tmap *ᵥ Sp.moment x) j + (C.Tmap *ᵥ (Sp.freeMap *ᵥ ζ)) j := by
      show ∑ i, C.Tmap j i * (Sp.moment x i + (Sp.freeMap *ᵥ ζ) i) = _
      simp only [mul_add, Finset.sum_add_distrib]
      rfl
    rw [e1, Matrix.mulVec_mulVec, hTF, Matrix.zero_mulVec, Pi.zero_apply, add_zero]
    exact hC.skeleton_slot x hx j
  have hκ : ∀ i, Sp.stateOf x ζ (Sum.inl (Sp.kappaSlot i)) = x.2.2.2.1 i := by
    intro i
    simp only [CellSplit.stateOf, Sum.elim_inl, Pi.add_apply, mulVec, dotProduct, hfree,
      zero_mul, Finset.sum_const_zero, add_zero]
    exact hS x hx i
  set ξ : Fin (systemInteriorCoords C.layout C.param).card → ℝ :=
    fun j => u ((systemInteriorCoords C.layout C.param).equivFin.symm j).1 /
      presetScale C.layout c.splitVisc ((systemInteriorCoords C.layout C.param).equivFin.symm j).1.1 with hξdef
  have hexp : ∀ q : C.layout.Datum × Fin 2, (q.1 ∈ C.param.skeleton ∨ q.1 ∈ C.param.interiorSet) →
      presetScale C.layout c.splitVisc q.1 * C.layout.expandSystem (systemVector C.layout C.param s ξ) q = u q := by
    intro q hq
    rw [expandSystem_div_of_mem C.layout C.param hconj _ (presetScale_conj C.layout c.splitVisc) u _
      (fun p hp hm => systemVector_eq_of_mem _ _ _ u s ξ hs (fun j => rfl) p hp hm) q hq, hred]
    have := presetScale_ne C.layout hν q.1
    field_simp
  have hF := h2 α hα₁ hα₂ c hc K S B Cl R hd hC.rows_shape C.layout C.param C.selection hC.layout_valid
    hC.param_valid _ hg hC.row_traces hC.row_normal_traces
  have hB := h1 α hα₁ hα₂ c hc K S B Cl R hd hC.far_low hν (C.formula c K S B Cl R α) hF x hx ζ
  have hle := hC.given_le_exact s ξ (fun i => x.2.2.2.1 i / c.splitVisc) (fun i => ζ i / c.splitVisc)
  have hvec : C.restrictState c.splitVisc Sp.kappaSlot (Sp.stateOf x ζ) =
      Sum.elim s (Sum.elim (fun i => x.2.2.2.1 i / c.splitVisc) (fun i => ζ i / c.splitVisc)) := by
    funext e
    rcases e with j | i | i
    · rfl
    · simp only [CellCoords.restrictState, Sum.elim_inr, Sum.elim_inl, hκ]
    · simp only [CellCoords.restrictState, Sum.elim_inr, CellSplit.stateOf]
  have hvec2 : (Sum.elim (fun i => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inl i))
      (Sum.elim (fun j => expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inr j))
        (Sum.elim (fun i => x.2.2.2.1 i / c.splitVisc) (fun i => ζ i / c.splitVisc))) :
        (C.formula c K S B Cl R α).Coord → ℝ) =
      (C.formula c K S B Cl R α).coordsOf x ζ c.splitVisc := by
    funext e
    rcases e with i | j | i | i
    · show expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inl i) =
        u ((skeletonCoords C.layout C.param).equivFin.symm i).1
      simp only [expandedCoords]
      apply hexp
      left
      have := ((skeletonCoords C.layout C.param).equivFin.symm i).2
      exact (Finset.mem_filter.mp this).2
    · show expandedCoords C.layout C.param c.splitVisc s ξ (Sum.inr j) =
        u ((interiorCoords C.layout C.param).equivFin.symm j).1
      simp only [expandedCoords]
      apply hexp
      right
      have := ((interiorCoords C.layout C.param).equivFin.symm j).2
      exact (Finset.mem_filter.mp this).2
    · rfl
    · rfl
  rw [hvec2] at hle
  have hpos : 0 < 4 * Real.pi * c.splitVisc := by positivity
  calc quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ)
      ≤ 4 * Real.pi * c.splitVisc * quadValue C.given (C.restrictState c.splitVisc Sp.kappaSlot (Sp.stateOf x ζ)) :=
        hC.matrix_embedding _
    _ = 4 * Real.pi * c.splitVisc * quadValue C.given
          (Sum.elim s (Sum.elim (fun i => x.2.2.2.1 i / c.splitVisc) (fun i => ζ i / c.splitVisc))) := by
        rw [hvec]
    _ ≤ 4 * Real.pi * c.splitVisc * (CellScalars.cellForm c K S R α B Cl x ζ / c.splitVisc) :=
        mul_le_mul_of_nonneg_left (hle.trans hB) hpos.le
    _ = 4 * Real.pi * CellScalars.cellForm c K S R α B Cl x ζ := by
        field_simp

end Breakdown.CellCert.CellCoordinates
