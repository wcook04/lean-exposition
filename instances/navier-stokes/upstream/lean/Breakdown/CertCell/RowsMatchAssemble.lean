import Breakdown.CertCell.RowsMatchConj

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ}

namespace Internal.LeafRows

theorem rowValue_expand {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    [Fintype T.Slaved] (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (f : T.Slaved → ℝ) : W.rowValue K d f = ∑ a, W.rowVec K d a * ((f a : ℝ) : ℂ) := by
  classical
  simp only [RowEntry.rowValue, RowEntry.rowVec, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_partVec_two {S : Type} [Fintype S] (r i : S) (cj : Bool) (F : S → ℂ) :
    ∑ a, partVec (some r) (some i) cj a * F a = F r + (if cj then -Complex.I else Complex.I) * F i := by
  classical
  simp only [partVec, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Option.some.injEq]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

theorem sum_partVec_one {S : Type} [Fintype S] (r : S) (cj : Bool) (F : S → ℂ) :
    ∑ a, partVec (some r) none cj a * F a = F r := by
  classical
  simp only [partVec, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Option.some.injEq]
  rw [Finset.sum_ite_eq]
  simp

theorem fieldData_cell {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    {a : T.Slaved} {K : Fin D.mesh.count} {d : CellVar D.mesh K (R.layouts K)}
    (h : T.evalCell a = some ⟨K, d⟩) :
    T.fieldData v G H Pg κ a = if T.evalImag a then (T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))).im
      else (T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))).re := by
  simp only [TreeEntry.fieldData, h]

theorem varDir_cell {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (c : Fin T.gauge.count) {a : T.Slaved} {K : Fin D.mesh.count} {d : CellVar D.mesh K (R.layouts K)}
    (h : T.evalCell a = some ⟨K, d⟩) : T.varDir c a = T.gaugeDir K c (Sum.inl (Sum.inl d)) := by
  simp only [TreeEntry.varDir, h]

theorem fieldShifted_cell {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) :
    T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))
      = headHarmonic ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d.2
        + ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl d)) := rfl

theorem gaugeDir_cell {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (K : Fin D.mesh.count) (c : Fin T.gauge.count) (d : CellVar D.mesh K (R.layouts K)) :
    T.gaugeDir K c (Sum.inl (Sum.inl d)) = T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) := rfl

theorem conj_gaugeDir {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (K : Fin D.mesh.count) (c : Fin T.gauge.count) (d : CellVar D.mesh K (R.layouts K)) :
    conj (T.gaugeDir K c (Sum.inl (Sum.inl d))) = T.gaugeDir K c (Sum.inl (Sum.inl d)) := by
  rw [gaugeDir_cell]
  simp only [GaugeKey.GaugeKeyValues.dir, Complex.conj_ofReal]

theorem layout_facts {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (hcc : CellCalculusConditions D R)
    (K : Fin D.mesh.count) (ι : D.mesh.resolved K) :
    ((R.layouts K).layout ι.1).order = D.azimuthOrder ∧ ∀ n ∈ ((R.layouts K).layout ι.1).modes, n = ι.1.1 := by
  obtain ⟨c, S, hco, hS, hcl⟩ := (hcc.layouts_valid K).layout_valid ι.1 ι.2
  refine ⟨hcl.order_eq.trans hco, fun n hn => ?_⟩
  rw [hcl.modes_eq, hS] at hn
  simpa using hn

theorem gaugeSum_zeroLabel_im {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hGc : T.gauge.Conditions) (hG : T.FieldGaugeHolds) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (h0 : d.1.1 = 0) :
    (∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl d))).im = 0 := by
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [gaugeDir_cell]
  by_cases hd : T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) = 0
  · simp [hd]
  · obtain ⟨hl, -⟩ := T.gauge.dir_support hd
    have hself := hGc.conj_self c (hl.symm.trans h0)
    have hre : (T.fieldGauge c v G H Pg).im = 0 := by
      have := hG.conj v G H Pg c
      rw [hself] at this
      exact Complex.conj_eq_iff_im.mp this.symm
    simp only [GaugeKey.GaugeKeyValues.dir, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hre]
    ring

theorem fieldShifted_zeroLabel_im {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hcc : CellCalculusConditions D R) (hGc : T.gauge.Conditions) (hG : T.FieldGaugeHolds) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (κ : Fin k → ℝ) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (h0 : d.1.1 = 0) : (T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))).im = 0 := by
  have hm := (layout_facts hcc K d.1).2
  have ht : labelTime d.1.1 = 0 := by rw [h0]; rfl
  rw [fieldShifted_cell, Complex.add_im, gaugeSum_zeroLabel_im T hGc hG v G H Pg K d h0, ht,
    Internal.DatumConj.headHarmonic_zero_im _ (fun n hn => by rw [hm n hn, h0]; rfl)]
  simp

theorem conj_gaugeSum_swap {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hGc : T.gauge.Conditions) (hG : T.FieldGaugeHolds) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (K : Fin D.mesh.count)
    (s : CellVar D.mesh K (R.layouts K)) :
    ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K (T.gauge.conjClass c) (Sum.inl (Sum.inl s))
      = conj (∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl s))) := by
  have hinv : Function.Involutive T.gauge.conjClass := hGc.conj_invol
  rw [map_sum, ← Equiv.sum_comp hinv.toPerm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Function.Involutive.coe_toPerm, hinv c, map_mul, conj_gaugeDir, hG.conj v G H Pg c]

end Internal.LeafRows

namespace Internal.LeafRows

theorem gaugeSum_deleted {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hGc : T.gauge.Conditions) (hG : T.FieldGaugeHolds) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (K : Fin D.mesh.count)
    (d s : CellVar D.mesh K (R.layouts K)) (hl : s.1.1 = -d.1.1)
    (hcd : ConjDatum ((R.layouts K).layout d.1.1) ((R.layouts K).layout s.1.1) d.2 s.2)
    (hdel : T.gauge.DeletedOmitted d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2)) :
    ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl d))
      = conj (∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl s))) := by
  obtain ⟨e, he⟩ := hdel
  obtain ⟨rad, lev, lo, hi, t, dd, hp⟩ := hGc.deleted_pressure e
  rw [he] at hp
  have hk : keyOf ((R.layouts K).layout d.1.1) d.2 = SkeletonKey.pressure 0 rad lev lo hi t dd := hp
  have hks := Internal.DatumConj.keyOf_conj_of_modeZero _ _ d.2 s.2 hcd ⟨rad, lev, lo, hi, t, dd, hk⟩
  have he' : T.gauge.deletedKey (T.gauge.conjClass e) = (s.1.1, keyOf ((R.layouts K).layout d.1.1) d.2) := by
    refine Prod.ext ?_ ?_
    · rw [hGc.deleted_label, hGc.conj_label, ← hGc.deleted_label, he, hl]
    · rw [hGc.deleted_conj, he]
  have h1 := hG.deleted v G H Pg e
  have h2 := hG.deleted v G H Pg (T.gauge.conjClass e)
  rw [he] at h1
  rw [he'] at h2
  have ht : labelTime s.1.1 = -labelTime d.1.1 := by rw [hl, TreeEntry.labelTime_neg]
  have hkc : keyHarmonic T.keyLayout (labelTime s.1.1) v G H Pg (keyOf ((R.layouts K).layout d.1.1) d.2)
      = conj (keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg (keyOf ((R.layouts K).layout d.1.1) d.2)) := by
    rw [ht]
    exact keyHarmonic_negFreq_eq_conj _ _ _ _ _ _ _ (by rw [hk]; rfl)
  simp only [TreeEntry.fieldKey] at h1 h2
  have hgs : ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl s))
      = ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c s.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [gaugeDir_cell, hks]
  have h2' := congrArg conj h2
  rw [map_add, hkc, Complex.conj_conj, map_zero] at h2'
  rw [hgs]
  show ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) = _
  linear_combination h1 - h2'

theorem gaugeDir_transport {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (htr : T.GaugeRowTransport W.rowVec) (K : Fin D.mesh.count)
    (d s : CellVar D.mesh K (R.layouts K)) (r i : T.Slaved)
    (hvec : W.rowVec K d = partVec (some r) (some i) true)
    (hrc : T.evalCell r = some ⟨K, s⟩) (hri : T.evalImag r = false)
    (hic : T.evalCell i = some ⟨K, s⟩) (hii : T.evalImag i = true)
    (hdel : ¬ T.gauge.DeletedOmitted d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2)) (c : Fin T.gauge.count) :
    T.gaugeDir K c (Sum.inl (Sum.inl d)) = T.gaugeDir K (T.gauge.conjClass c) (Sum.inl (Sum.inl s)) := by
  let _ := T.slavedFintype
  have h := htr K d c hdel
  rw [hvec, sum_partVec_two] at h
  rw [h]
  simp only [TreeEntry.varPartDir, hri, hii, varDir_cell T _ hrc, varDir_cell T _ hic, if_true,
    Bool.false_eq_true, if_false]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

end Internal.LeafRows

open Internal.LeafRows in
theorem leafRow_fields {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hcc : CellCalculusConditions D R) (hGc : T.gauge.Conditions) (hG : T.FieldGaugeHolds)
    (htr : T.GaugeRowTransport W.rowVec) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (cj : Bool) (source : CellVar D.mesh K (R.layouts K))
    (re im : Option T.Slaved) (hw : W.LeafRow K d cj source re im) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) := by
  let _ := T.slavedFintype
  obtain ⟨hs0, hs1, hsome, hre, him, hnone, hvec⟩ := hw
  obtain ⟨r, rfl⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hrc, hri⟩ := hre r rfl
  have hfr : ((T.fieldData v G H Pg κ r : ℝ) : ℂ)
      = ((T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl source))).re : ℂ) := by
    rw [fieldData_cell T v G H Pg κ hrc, hri]
    rfl
  rw [rowValue_expand, hvec]
  cases cj with
  | false =>
    have hsd := hs0 rfl
    subst hsd
    cases im with
    | none =>
      have h0 := hnone rfl
      rw [sum_partVec_one, hfr]
      apply Complex.ext <;> simp [fieldShifted_zeroLabel_im T hcc hGc hG v G H Pg κ K _ h0]
    | some i =>
      obtain ⟨hic, hii⟩ := him i rfl
      have hfi : ((T.fieldData v G H Pg κ i : ℝ) : ℂ)
          = ((T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl source))).im : ℂ) := by
        rw [fieldData_cell T v G H Pg κ hic, hii]
        rfl
      rw [sum_partVec_two, hfr, hfi]
      apply Complex.ext <;> simp
  | true =>
    obtain ⟨hl, hcd⟩ := hs1 rfl
    have hord : ((R.layouts K).layout source.1.1).order = ((R.layouts K).layout d.1.1).order := by
      rw [(layout_facts hcc K source.1).1, (layout_facts hcc K d.1).1]
    have ht : labelTime source.1.1 = -labelTime d.1.1 := by rw [hl, TreeEntry.labelTime_neg]
    have hhead : headHarmonic ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d.2
        = conj (headHarmonic ((R.layouts K).layout source.1.1) (labelTime source.1.1) v G H Pg source.2) := by
      rw [ht, Internal.DatumConj.headHarmonic_negLabel _ _ hord (labelTime d.1.1) v G H Pg d.2 source.2 hcd,
        Complex.conj_conj]
    have hfs : ∀ hg : ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl d))
          = conj (∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl source))),
        T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) = conj (T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl source))) := by
      intro hg
      rw [fieldShifted_cell T v G H Pg κ K d, fieldShifted_cell T v G H Pg κ K source, hhead, hg, map_add]
    cases im with
    | none =>
      have h0 := hnone rfl
      have hs0' : source.1.1 = 0 := by rw [hl, h0]; rfl
      have hsd : source.1.1 = d.1.1 := by rw [hs0', h0]; rfl
      have hg : ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl d))
          = conj (∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl source))) := by
        rw [Complex.conj_eq_iff_im.mpr (gaugeSum_zeroLabel_im T hGc hG v G H Pg K source hs0')]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [gaugeDir_cell, gaugeDir_cell, Internal.DatumConj.dir_keyOf_conj _ _ _ _ _ d.2 source.2 hcd, hsd]
      rw [sum_partVec_one, hfr, hfs hg]
      have hz := fieldShifted_zeroLabel_im T hcc hGc hG v G H Pg κ K source hs0'
      apply Complex.ext <;> simp [hz]
    | some i =>
      obtain ⟨hic, hii⟩ := him i rfl
      have hfi : ((T.fieldData v G H Pg κ i : ℝ) : ℂ)
          = ((T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl source))).im : ℂ) := by
        rw [fieldData_cell T v G H Pg κ hic, hii]
        rfl
      have hg : ∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl d))
          = conj (∑ c, T.fieldGauge c v G H Pg * T.gaugeDir K c (Sum.inl (Sum.inl source))) := by
        by_cases hdel : T.gauge.DeletedOmitted d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2)
        · exact gaugeSum_deleted T hGc hG v G H Pg K d source hl hcd hdel
        · rw [← conj_gaugeSum_swap T hGc hG v G H Pg K source]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [gaugeDir_transport W htr K d source r i hvec hrc hri hic hii hdel c]
      rw [sum_partVec_two, hfr, hfi, hfs hg]
      apply Complex.ext <;> simp

section RowInduction

variable {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}

def RowKindMatch (W : RowEntry D R T) (P : ∀ K : Fin D.mesh.count, CellVar D.mesh K (R.layouts K) → Prop) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (κ : Fin k → ℝ) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)),
      P K d →
      (∀ d' : CellVar D.mesh K (R.layouts K), W.rank K d' < W.rank K d → ¬ (W.reason K d').IsUnused →
        W.rowValue K d' (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d'))) →
      W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))

def IsKeyRow (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  ∃ rd re im, W.KeyRow K d rd re im

def IsSplitRow (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  ∃ w, W.SplitRow K d w

def IsFluxRow (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  ∃ w, W.FluxRow K d w

def IsDerivedRow (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  ∃ rows mult, W.DerivedRow K d rows mult

def IsNormalRow (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) : Prop :=
  ∃ pcoef pdeg, W.NormalRow K d pcoef pdeg

end RowInduction

structure RowMatchHypotheses (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ) (T : TreeEntry D R)
    (W : RowEntry D R T) : Prop where
  mode_class : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder
  mesh_valid : IsCellMesh D.mesh
  cell_conditions : CellCalculusConditions D R
  relations : HarmonicRelationsStatement
  strip_trace : Bridge.StripMomentTraceHolds
  trace_match : Bridge.TraceMatchHolds
  trace_height : Bridge.TraceHeightHolds
  corner_trace : Bridge.CornerTraceHolds
  corner_match : Bridge.CornerMatchHolds
  height_deriv : Bridge.ModeHeightDerivHolds
  strip_flip : Bridge.StripDataFlipHolds
  corner_flip : Bridge.CornerDataFlipHolds
  plane_flip : Bridge.ScalarPlaneFlipHolds
  pressure : PressureFacts D
  gauge_keys : T.GaugeKeyConditions
  real_keys : T.RealKeyConditions
  field_gauge : T.FieldGaugeHolds
  transport : T.GaugeRowTransport W.rowVec
  rows : TreeRowConditions D R e T W

def KeyRowsMatchHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → RowKindMatch W (IsKeyRow W)

def SplitRowsMatchHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → RowKindMatch W (IsSplitRow W)

def FluxRowsMatchHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → RowKindMatch W (IsFluxRow W)

def DerivedRowsMatchHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → RowKindMatch W (IsDerivedRow W)

def NormalRowsMatchHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (e : ℝ)
    (T : TreeEntry D R) (W : RowEntry D R T), RowMatchHypotheses D R e T W → RowKindMatch W (IsNormalRow W)

theorem rowsMatchFields_of_kinds {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {e : ℝ}
    {T : TreeEntry D R} {W : RowEntry D R T} (h : RowMatchHypotheses D R e T W)
    (hkey : RowKindMatch W (IsKeyRow W)) (hsplit : RowKindMatch W (IsSplitRow W))
    (hflux : RowKindMatch W (IsFluxRow W)) (hder : RowKindMatch W (IsDerivedRow W))
    (hnorm : RowKindMatch W (IsNormalRow W)) : RowsMatchFields D R T W := by
  intro q hq v G H g hpert Pg hP hflip κ K
  have hfh : GaugeKey.fieldHyp D q v G H g Pg := ⟨hq, h.mode_class, hpert, hP, hflip⟩
  suffices main : ∀ (n : ℕ) (d : CellVar D.mesh K (R.layouts K)), W.rank K d < n → ¬ (W.reason K d).IsUnused →
      W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) by
    intro d hd
    exact main _ d (Nat.lt_succ_self _) hd
  intro n
  induction n with
  | zero => intro d hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro d hlt hd
    have hprev : ∀ d' : CellVar D.mesh K (R.layouts K), W.rank K d' < W.rank K d → ¬ (W.reason K d').IsUnused →
        W.rowValue K d' (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d')) :=
      fun d' hr hu => ih d' (by omega) hu
    have hj := h.rows.justified K d
    unfold RowEntry.Accounted at hj
    split at hj
    · exact hkey q v G H g Pg hfh κ K d ⟨_, _, _, hj⟩ hprev
    · exact hsplit q v G H g Pg hfh κ K d ⟨_, hj⟩ hprev
    · exact hflux q v G H g Pg hfh κ K d ⟨_, hj⟩ hprev
    · exact hder q v G H g Pg hfh κ K d ⟨_, _, hj⟩ hprev
    · exact hnorm q v G H g Pg hfh κ K d ⟨_, _, hj⟩ hprev
    · exact leafRow_fields W h.cell_conditions h.gauge_keys.values h.field_gauge h.transport v G H Pg κ K d _ _ _ _ hj
    · next hw => exact absurd (by rw [hw]; exact trivial) hd

theorem rowsMatchFieldsHolds_of_kinds (hkey : KeyRowsMatchHolds) (hsplit : SplitRowsMatchHolds)
    (hflux : FluxRowsMatchHolds) (hder : DerivedRowsMatchHolds) (hnorm : NormalRowsMatchHolds) :
    RowsMatchFieldsHolds := by
  intro k C nE nM D R e T W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
  have h : RowMatchHypotheses D R e T W :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  exact rowsMatchFields_of_kinds h (hkey D R e T W h) (hsplit D R e T W h) (hflux D R e T W h)
    (hder D R e T W h) (hnorm D R e T W h)

theorem rowsMatchStateOfFields_holds : RowsMatchStateOfFieldsHolds := by
  intro k C nE nM D R T W _ hP hC hF q hq x K d hd
  exact hF q hq x.v x.G x.H x.g x.perturbation (chosenPressure D x) (hP q hq x) (hC q hq x) x.κ K d hd

end Assembly

end CertCell

end Breakdown
