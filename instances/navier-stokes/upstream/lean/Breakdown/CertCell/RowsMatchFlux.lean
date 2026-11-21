import Breakdown.CertCell.AssemblyStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ}

section Flux

def KeyFluxHolds (D : CellLayerData k C nE nM) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ L : CellLayout, L.order = D.azimuthOrder →
    ∀ (ν : ℤ) (x : CellCert.Assembly.FieldTuple 0), (x = cosTuple ν v G H Pg ∨ x = sinTuple ν v G H Pg) →
      (∀ (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ), 0 < lev → 0 ≤ lo → lo < hi →
        keyValue L x (.velocity 0 true lev lo hi t 0 0)
          = -((t 0 0 / lev : ℝ) : ℂ) * (keyValue L x (.stream (lev, hi)) - keyValue L x (.stream (lev, lo)))) ∧
      (∀ (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ), 0 ≤ lo → lo < hi → t 1 0 ≠ 0 →
        keyValue L x (.velocity 0 false lev lo hi t 2 0)
          = ((t 0 0 / t 1 0 : ℝ) : ℂ) * (keyValue L x (.velocity 0 false lev lo hi t 2 1)
              - (t 1 1 : ℂ) * (keyValue L x (.stream (hi, lev)) - keyValue L x (.stream (lo, lev)))))

def SideVelocityKeyMatch (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (T : TreeEntry D R) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (K : Fin D.mesh.count) (ι : D.mesh.resolved K)
      (n : ((R.layouts K).layout ι.1).modes) (s : Fin ((R.layouts K).layout ι.1).segCount) (a : Fin 3)
      (i : Fin (((R.layouts K).layout ι.1).degSide + 2)),
      headHarmonic ((R.layouts K).layout ι.1) (labelTime ι.1) v G H Pg (CellDatum.sideVelocity n s a i)
        = keyHarmonic T.keyLayout (labelTime ι.1) v G H Pg
            (keyOf ((R.layouts K).layout ι.1) (CellDatum.sideVelocity n s a i))

namespace Internal.FluxRows

theorem radial_harmonic {D : CellLayerData k C nE nM} (hF : KeyFluxHolds D) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) {L : CellLayout} (hL : L.order = D.azimuthOrder) (ν : ℤ)
    {lev lo hi : ℝ} (t : ℕ → ℕ → ℝ) (hlev : 0 < lev) (hlo : 0 ≤ lo) (hlh : lo < hi) :
    keyHarmonic L ν v G H Pg (.velocity 0 true lev lo hi t 0 0)
      = -((t 0 0 / lev : ℝ) : ℂ) *
          (keyHarmonic L ν v G H Pg (.stream (lev, hi)) - keyHarmonic L ν v G H Pg (.stream (lev, lo))) := by
  have hc := (hF q v G H g Pg hfh L hL ν _ (Or.inl rfl)).1 lev lo hi t hlev hlo hlh
  have hs := (hF q v G H g Pg hfh L hL ν _ (Or.inr rfl)).1 lev lo hi t hlev hlo hlh
  simp only [keyHarmonic]
  rw [hc, hs]
  ring

theorem height_harmonic {D : CellLayerData k C nE nM} (hF : KeyFluxHolds D) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) {L : CellLayout} (hL : L.order = D.azimuthOrder) (ν : ℤ)
    {lev lo hi : ℝ} (t : ℕ → ℕ → ℝ) (hlo : 0 ≤ lo) (hlh : lo < hi) (h10 : t 1 0 ≠ 0) :
    keyHarmonic L ν v G H Pg (.velocity 0 false lev lo hi t 2 0)
      = ((t 0 0 / t 1 0 : ℝ) : ℂ) * (keyHarmonic L ν v G H Pg (.velocity 0 false lev lo hi t 2 1)
          - (t 1 1 : ℂ) * (keyHarmonic L ν v G H Pg (.stream (hi, lev))
            - keyHarmonic L ν v G H Pg (.stream (lo, lev)))) := by
  have hc := (hF q v G H g Pg hfh L hL ν _ (Or.inl rfl)).2 lev lo hi t hlo hlh h10
  have hs := (hF q v G H g Pg hfh L hL ν _ (Or.inr rfl)).2 lev lo hi t hlo hlh h10
  simp only [keyHarmonic]
  rw [hc, hs]
  ring

theorem dir_stream (Γ : GaugeKey.GaugeKeyValues) (c : Fin Γ.count) (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    Γ.dir c ι (.stream p) = 0 := by
  simp [GaugeKey.GaugeKeyValues.dir, GaugeKey.GaugeKeyValues.dirReal]

theorem dir_velocity (Γ : GaugeKey.GaugeKeyValues) (c : Fin Γ.count) (ι : ℤ × ℤ) (n : ℤ) (rad : Bool)
    (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3) (i : ℕ) :
    Γ.dir c ι (.velocity n rad lev lo hi t a i) = 0 := by
  simp [GaugeKey.GaugeKeyValues.dir, GaugeKey.GaugeKeyValues.dirReal]

theorem strip_axis (c o : ℝ) (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) :
    heightStripMoment c o 0 0 wt F dF t = 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) (Set.Icc (0 : ℝ) 0 ×ˢ Set.Icc (min c o) (max c o)) = 0 := by
    refine measure_mono_null (t := ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) ?_ ?_
    · rintro ⟨a, b⟩ ⟨⟨ha, ha'⟩, -⟩
      exact ⟨le_antisymm ha' ha, trivial⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
  simp only [heightStripMoment]
  rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure, mul_zero]

theorem keyHarmonic_axis (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (z : ℝ) :
    keyHarmonic L ν v G H Pg (.stream (0, z)) = 0 := by
  simp only [keyHarmonic, keyValue, strip_axis, mul_zero, add_zero]

end Internal.FluxRows


namespace Internal.FluxRows

theorem sum_ite_some {α : Type} [Fintype α] (b : α) (F : α → ℂ) (dec : ∀ x, Decidable (some b = some x)) :
    (∑ x, @ite _ (some b = some x) (dec x) (F x) 0) = F b := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    have : ¬ (some b = some x) := fun h => hx (Option.some_injective _ h).symm
    simp [this]
  · simp

theorem sum_partVec {α : Type} [Fintype α] (re im : Option α) (conj : Bool) (F : α → ℂ) :
    ∑ a, partVec re im conj a * F a
      = re.elim 0 F + (if conj then -Complex.I else Complex.I) * im.elim 0 F := by
  simp only [partVec, add_mul, Finset.sum_add_distrib]
  cases re <;> cases im <;> simp [ite_mul, sum_ite_some]

theorem fieldData_keyVar {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    {ι : ℤ × ℤ} {key : SkeletonKey} {imag : Bool} {a : T.Slaved} (h : IsKeyVar T ι key imag a) :
    T.fieldData v G H Pg κ a = GaugeKey.keyPart imag (T.fieldKey v G H Pg ι key) := by
  obtain ⟨hc, hk, hs, hi⟩ := h
  simp only [TreeEntry.fieldData, hc, hk, hs, hi, GaugeKey.keyPart]

theorem fieldKey_axis {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (ι : ℤ × ℤ) (z : ℝ) :
    T.fieldKey v G H Pg ι (.stream (0, z)) = 0 := by
  simp only [TreeEntry.fieldKey, keyHarmonic_axis, dir_stream, mul_zero, Finset.sum_const_zero, add_zero]

theorem fieldKey_stream {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    T.fieldKey v G H Pg ι (.stream p) = keyHarmonic T.keyLayout (labelTime ι) v G H Pg (.stream p) := by
  simp only [TreeEntry.fieldKey, dir_stream, mul_zero, Finset.sum_const_zero, add_zero]

theorem fieldKey_velocity {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (ι : ℤ × ℤ) (n : ℤ) (rad : Bool)
    (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3) (i : ℕ) :
    T.fieldKey v G H Pg ι (.velocity n rad lev lo hi t a i)
      = keyHarmonic T.keyLayout (labelTime ι) v G H Pg (.velocity n rad lev lo hi t a i) := by
  simp only [TreeEntry.fieldKey, dir_velocity, mul_zero, Finset.sum_const_zero, add_zero]

theorem part_elim {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hG : T.FieldGaugeHolds) {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) {ι : ℤ × ℤ} {key : SkeletonKey} {imag : Bool}
    {o : Option T.Slaved} (h : PartBound T ι key imag o) :
    o.elim 0 (fun a => ((T.fieldData v G H Pg κ a : ℝ) : ℂ))
      = ((GaugeKey.keyPart imag (T.fieldKey v G H Pg ι key) : ℝ) : ℂ) := by
  cases o with
  | some a =>
    simp only [Option.elim]
    rw [fieldData_keyVar T v G H Pg κ h]
  | none =>
    simp only [Option.elim]
    rcases h with h | ⟨p, rfl, hp⟩
    · rw [hG.omitted q v G H g Pg hfh ι key imag h, Complex.ofReal_zero]
    · obtain ⟨p1, p2⟩ := p
      simp only at hp
      subst hp
      rw [fieldKey_axis]
      cases imag <;> simp [GaugeKey.keyPart]

theorem partVec_fieldData {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    [Fintype T.Slaved] (hG : T.FieldGaugeHolds) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g Pg : ℝ → Space → Space} (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) {ι : ℤ × ℤ}
    {key : SkeletonKey} {re im : Option T.Slaved} (conj : Bool) (hre : PartBound T ι key false re)
    (him : PartBound T ι key true im) :
    ∑ a, partVec re im conj a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ)
      = if conj then (starRingEnd ℂ) (T.fieldKey v G H Pg ι key) else T.fieldKey v G H Pg ι key := by
  rw [sum_partVec, part_elim T hG hfh κ hre, part_elim T hG hfh κ him]
  simp only [GaugeKey.keyPart, Bool.false_eq_true, if_false, if_true]
  cases conj
  · simp only [Bool.false_eq_true, if_false]
    rw [mul_comm]
    exact Complex.re_add_im _
  · simp only [if_true]
    apply Complex.ext <;> simp

theorem labelTime_negate (ι : ℤ × ℤ) : labelTime (-ι) = -labelTime ι := by
  simp only [labelTime, Prod.fst_neg, Prod.snd_neg]
  ring

theorem partVec_stream {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    [Fintype T.Slaved] (hG : T.FieldGaugeHolds) (hK : T.FieldKeyConjHolds) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (ι : ℤ × ℤ) (rd : KeyEvaluation)
    (hrd : (rd.label = ι ∧ rd.conj = false) ∨ (rd.label = -ι ∧ rd.conj = true)) (p : ℝ × ℝ)
    {re im : Option T.Slaved} (hre : PartBound T rd.label (.stream p) false re)
    (him : PartBound T rd.label (.stream p) true im) :
    ∑ a, partVec re im rd.conj a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ)
      = keyHarmonic T.keyLayout (labelTime ι) v G H Pg (.stream p) := by
  rw [partVec_fieldData T hG hfh κ rd.conj hre him, fieldKey_stream]
  rcases hrd with ⟨hl, hc⟩ | ⟨hl, hc⟩
  · rw [hc, hl]
    rfl
  · rw [hc, hl, labelTime_negate, hK (labelTime ι) v G H Pg (.stream p) rfl]
    simp

theorem rowValue_sum {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    [Fintype T.Slaved] (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (f : T.Slaved → ℝ) : W.rowValue K d f = ∑ a, W.rowVec K d a * ((f a : ℝ) : ℂ) := by
  classical
  simp only [RowEntry.rowValue, RowEntry.rowVec, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end Internal.FluxRows

namespace Internal.FluxRows

theorem pair_smul_sub {α : Type} [Fintype α] (c : ℂ) (u w : α → ℂ) (F : α → ℂ) :
    ∑ a, (c • (u - w)) a * F a = c * (∑ a, u a * F a - ∑ a, w a * F a) := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem pair_smul_sub_smul {α : Type} [Fintype α] (c b : ℂ) (r u w : α → ℂ) (F : α → ℂ) :
    ∑ a, (c • (r - b • (u - w))) a * F a
      = c * (∑ a, r a * F a - b * (∑ a, u a * F a - ∑ a, w a * F a)) := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem fieldShifted_side {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hM : SideVelocityKeyMatch D R T) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g Pg : ℝ → Space → Space} (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ)
    (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (n : ((R.layouts K).layout ι.1).modes)
    (s : Fin ((R.layouts K).layout ι.1).segCount) (a : Fin 3) (i : Fin (((R.layouts K).layout ι.1).degSide + 2)) :
    T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨ι, CellDatum.sideVelocity n s a i⟩))
      = keyHarmonic T.keyLayout (labelTime ι.1) v G H Pg
          (.velocity (n : ℤ) (((R.layouts K).layout ι.1).segment s).radial (((R.layouts K).layout ι.1).segment s).level
            (((R.layouts K).layout ι.1).segment s).lo (((R.layouts K).layout ι.1).segment s).hi
            (((R.layouts K).layout ι.1).segment s).testCoef a i) := by
  have h := hM q v G H g Pg hfh K ι n s a i
  change headHarmonic ((R.layouts K).layout ι.1) (labelTime ι.1) v G H Pg (CellDatum.sideVelocity n s a i)
      + ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c ι.1
          (.velocity (n : ℤ) (((R.layouts K).layout ι.1).segment s).radial (((R.layouts K).layout ι.1).segment s).level
            (((R.layouts K).layout ι.1).segment s).lo (((R.layouts K).layout ι.1).segment s).hi
            (((R.layouts K).layout ι.1).segment s).testCoef a i) = _
  rw [h]
  simp only [dir_velocity, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

end Internal.FluxRows

open Internal.FluxRows in
theorem fluxRow_fields {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hF : KeyFluxHolds D) (hM : SideVelocityKeyMatch D R T) (hK : T.FieldKeyConjHolds)
    (hG : T.FieldGaugeHolds) (hcc : CellCalculusConditions D R) (horder : T.keyLayout.order = D.azimuthOrder)
    {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (w : FluxChoice T) (hw : W.FluxRow K d w)
    (hprev : ∀ d' : CellVar D.mesh K (R.layouts K), W.rank K d' < W.rank K d → ¬ (W.reason K d').IsUnused →
      W.rowValue K d' (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d'))) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) := by
  let _ := T.slavedFintype
  obtain ⟨hrd, -, n, s, hn, hends, hcase⟩ := hw
  have hval : ∀ e : Fin 2, ∑ a, partVec (w.endRe e) (w.endIm e) w.evaluation.conj a
        * ((T.fieldData v G H Pg κ a : ℝ) : ℂ)
      = keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg
          (.stream (streamEnds (((R.layouts K).layout d.1.1).segment s) e)) :=
    fun e => partVec_stream T hG hK hfh κ d.1.1 w.evaluation hrd _ (hends e).1 (hends e).2
  obtain ⟨c, S', -, -, hcl⟩ := (hcc.layouts_valid K).layout_valid d.1.1 d.1.2
  have hbox := hcl.box_valid
  have hseg := hcl.segment_valid s
  rcases hcase with ⟨hrad, hd, hlev, hrow⟩ | ⟨hrad, hd, h10, hrank, hnu, hrow⟩
  · have e : T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))
        = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨d.1, CellDatum.sideVelocity n s 0 ⟨0, by omega⟩⟩)) := by
      rw [← hd]
    have hlo : 0 ≤ (((R.layouts K).layout d.1.1).segment s).lo := by
      rcases hcl.segment_on_side s with ⟨-, -, hz, -, -⟩ | ⟨hr, -⟩
      · exact le_trans hbox.z_order.1 hz
      · exact absurd hrad hr
    rw [e, rowValue_sum, hrow, pair_smul_sub, hval 1, hval 0, fieldShifted_side T hM hfh κ K d.1 n s 0 ⟨0, by omega⟩,
      hn, hrad, radial_harmonic hF hfh horder _ _ hlev hlo hseg.lo_lt_hi]
    simp only [streamEnds, hrad, if_true, Fin.isValue, one_ne_zero, if_false]
    push_cast
    ring
  · have e : T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))
        = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨d.1, CellDatum.sideVelocity n s 2 ⟨0, by omega⟩⟩)) := by
      rw [← hd]
    have hlo : 0 ≤ (((R.layouts K).layout d.1.1).segment s).lo := by
      rcases hcl.segment_on_side s with ⟨hr, -⟩ | ⟨-, -, hr, -⟩
      · exact absurd hr (by simp [hrad])
      · exact le_trans hbox.r_order.1 hr
    have h1 := hprev _ hrank hnu
    rw [rowValue_sum] at h1
    rw [e, rowValue_sum, hrow, pair_smul_sub_smul, h1, hval 1, hval 0,
      fieldShifted_side T hM hfh κ K d.1 n s 2 ⟨1, by omega⟩, fieldShifted_side T hM hfh κ K d.1 n s 2 ⟨0, by omega⟩,
      hn, hrad, height_harmonic hF hfh horder _ _ hlo hseg.lo_lt_hi h10]
    simp only [streamEnds, hrad, Bool.false_eq_true, if_false, Fin.isValue, one_ne_zero, if_true]

namespace Internal.FluxRows

theorem partVec_modeZero {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    [Fintype T.Slaved] (hG : T.FieldGaugeHolds) (hK : T.FieldKeyConjHolds) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (ι : ℤ × ℤ) (rd : KeyEvaluation)
    (hrd : (rd.label = ι ∧ rd.conj = false) ∨ (rd.label = -ι ∧ rd.conj = true)) (key : SkeletonKey)
    (hmode : GaugeKey.keyMode key = some 0) (hdir : ∀ c ι', T.gauge.dir c ι' key = 0)
    {re im : Option T.Slaved} (hre : PartBound T rd.label key false re) (him : PartBound T rd.label key true im) :
    ∑ a, partVec re im rd.conj a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ)
      = keyHarmonic T.keyLayout (labelTime ι) v G H Pg key := by
  have hfk : ∀ ι', T.fieldKey v G H Pg ι' key = keyHarmonic T.keyLayout (labelTime ι') v G H Pg key := by
    intro ι'
    simp only [TreeEntry.fieldKey, hdir, mul_zero, Finset.sum_const_zero, add_zero]
  rw [partVec_fieldData T hG hfh κ rd.conj hre him, hfk]
  rcases hrd with ⟨hl, hc⟩ | ⟨hl, hc⟩
  · rw [hc, hl]
    rfl
  · rw [hc, hl, labelTime_negate, hK (labelTime ι) v G H Pg key hmode]
    simp

theorem tile_lo_le {n : ℕ} (tlo thi : Fin n → ℝ) (lo : ℝ) (hlt : ∀ j, tlo j < thi j)
    (hnext : ∀ j j' : Fin n, j.val + 1 = j'.val → thi j = tlo j') (hfirst : ∀ j : Fin n, j.val = 0 → tlo j = lo) :
    ∀ j : Fin n, lo ≤ tlo j := by
  intro j
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => exact (hfirst ⟨0, hm⟩ rfl).ge
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hnext ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
    have h3 := hlt ⟨m, by omega⟩
    linarith

theorem side_geometry {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (hcc : CellCalculusConditions D R)
    (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (dd : ((R.layouts K).layout ι.1).Datum) {rad : Bool}
    {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ} {deg : ℕ} (hvn : keyVelNormal (keyOf ((R.layouts K).layout ι.1) dd))
    (hgeom : sideKeyGeom (keyOf ((R.layouts K).layout ι.1) dd) = some (rad, lev, lo, hi, t, deg)) :
    0 ≤ lo ∧ (rad = true → 0 ≤ lev) ∧ ι.1.1 = 0 ∧
      keyOf ((R.layouts K).layout ι.1) dd = .velocity 0 rad lev lo hi t (if rad then 0 else 2) deg := by
  obtain ⟨c, S', -, hres, hcl⟩ := (hcc.layouts_valid K).layout_valid ι.1 ι.2
  have hbox := hcl.box_valid
  rcases dd with x | x | x | x | x | x | x | x
  · exact absurd hvn (by simp [keyOf, keyVelNormal])
  · exact absurd hvn (by simp [keyOf, keyVelNormal])
  · obtain ⟨n, s, a, i⟩ := x
    change keyVelNormal (.velocity (n : ℤ) (((R.layouts K).layout ι.1).segment s).radial
      (((R.layouts K).layout ι.1).segment s).level (((R.layouts K).layout ι.1).segment s).lo
      (((R.layouts K).layout ι.1).segment s).hi (((R.layouts K).layout ι.1).segment s).testCoef a i) at hvn
    change some ((((R.layouts K).layout ι.1).segment s).radial, (((R.layouts K).layout ι.1).segment s).level,
      (((R.layouts K).layout ι.1).segment s).lo, (((R.layouts K).layout ι.1).segment s).hi,
      (((R.layouts K).layout ι.1).segment s).testCoef, (i : ℕ)) = some (rad, lev, lo, hi, t, deg) at hgeom
    simp only [Option.some.injEq, Prod.mk.injEq] at hgeom
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hgeom
    obtain ⟨hn, ha⟩ := hvn
    have hmem : (n : ℤ) ∈ ({ι.1.1} : Finset ℤ) := by
      rw [← hres, ← hcl.modes_eq]
      exact n.2
    have hι : ι.1.1 = 0 := by
      rw [Finset.mem_singleton] at hmem
      rw [← hmem, hn]
    refine ⟨?_, ?_, hι, ?_⟩
    · rw [← h3]
      rcases hcl.segment_on_side s with ⟨-, -, hz, -, -⟩ | ⟨-, -, hr, -⟩
      · exact le_trans hbox.z_order.1 hz
      · exact le_trans hbox.r_order.1 hr
    · intro hr
      rw [← h2]
      rcases hcl.segment_on_side s with ⟨-, hl, -, -, -⟩ | ⟨hr', -⟩
      · rcases hl with hl | hl <;> rw [hl] <;> linarith [hbox.r_order.1, hbox.r_order.2]
      · exact absurd (h1.trans hr) hr'
    · change SkeletonKey.velocity (n : ℤ) (((R.layouts K).layout ι.1).segment s).radial
        (((R.layouts K).layout ι.1).segment s).level (((R.layouts K).layout ι.1).segment s).lo
        (((R.layouts K).layout ι.1).segment s).hi (((R.layouts K).layout ι.1).segment s).testCoef a i = _
      rw [hn, ha, h1, h2, h3, h4, h5, h6]
  · exact absurd hvn (by simp [keyOf, keyVelNormal])
  · exact absurd hvn (by simp [keyOf, keyVelNormal])
  · exact absurd hvn (by simp [keyOf, keyVelNormal])
  · exact absurd hvn (by simp [keyOf, keyVelNormal])
  · exact absurd hvn (by simp [keyOf, keyVelNormal])

end Internal.FluxRows

open Internal.FluxRows in
theorem tileFlux_fields {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hF : KeyFluxHolds D) (hK : T.FieldKeyConjHolds) (hG : T.FieldGaugeHolds)
    (hcc : CellCalculusConditions D R) (horder : T.keyLayout.order = D.azimuthOrder)
    {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (w : SplitChoice T) {rad : Bool} {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ}
    {deg : ℕ} (hgeom : sideKeyGeom (keyOf ((R.layouts K).layout d.1.1) d.2) = some (rad, lev, lo, hi, t, deg))
    (hw : W.SplitRow K d w) (j : Fin w.tiles) (hj : w.flux j = true) :
    (haveI := T.slavedFintype; ∑ a, RowEntry.tileFlux rad lev w j a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ))
      = keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg
          (retileKey (w.tlo j) (w.thi j) (w.ttest j) 0 (keyOf ((R.layouts K).layout d.1.1) d.2)) := by
  let _ := T.slavedFintype
  simp only [RowEntry.SplitRow, hgeom] at hw
  obtain ⟨-, -, -, -, hlt, hnext, hfirst, -, -, -, hflux, -⟩ := hw
  obtain ⟨hvn, -, hrd, hends, hradlev, hheight⟩ := hflux j hj
  obtain ⟨hlo, hlev0, hι, hkey⟩ := side_geometry hcc K d.1 d.2 hvn hgeom
  have htlo : 0 ≤ w.tlo j := le_trans hlo (tile_lo_le w.tlo w.thi lo hlt hnext hfirst j)
  have hval : ∀ e : Fin 2, ∑ a, partVec (w.fre j e) (w.fim j e) w.evaluation.conj a
        * ((T.fieldData v G H Pg κ a : ℝ) : ℂ)
      = keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg (.stream (streamEnds (RowEntry.tileSeg rad lev w j) e)) :=
    fun e => partVec_modeZero T hG hK hfh κ d.1.1 w.evaluation hrd _ rfl (fun c ι' => dir_stream _ c ι' _)
      (hends e).1 (hends e).2
  rw [hkey]
  cases rad with
  | true =>
    have hlev : 0 < lev := lt_of_le_of_ne (hlev0 rfl) (Ne.symm (hradlev rfl))
    simp only [RowEntry.tileFlux, if_true]
    rw [pair_smul_sub, hval 1, hval 0]
    simp only [retileKey]
    rw [radial_harmonic hF hfh horder _ _ hlev htlo (hlt j)]
    simp only [streamEnds, RowEntry.tileSeg, keySeg, if_true, Fin.isValue, one_ne_zero, if_false]
    push_cast
    ring
  | false =>
    obtain ⟨h10, hre1, him1⟩ := hheight rfl
    rw [hkey] at hre1 him1
    have hlab : w.evaluation.label.1 = 0 := by
      rcases hrd with ⟨hl, -⟩ | ⟨hl, -⟩
      · rw [hl, hι]
      · rw [hl, Prod.fst_neg, hι, neg_zero]
    simp only [retileKey, keyWithMode, hlab, Bool.false_eq_true, if_false] at hre1 him1
    have h1 := partVec_modeZero T hG hK hfh κ d.1.1 w.evaluation hrd _ rfl (fun c ι' => dir_velocity _ c ι' _ _ _ _ _ _ _ _)
      hre1 him1
    simp only [RowEntry.tileFlux, Bool.false_eq_true, if_false]
    rw [pair_smul_sub_smul, h1, hval 1, hval 0]
    simp only [retileKey]
    rw [height_harmonic hF hfh horder _ _ htlo (hlt j) h10]
    simp only [streamEnds, RowEntry.tileSeg, keySeg, Bool.false_eq_true, if_false, Fin.isValue, one_ne_zero, if_true]

end Flux

end Assembly

end CertCell

end Breakdown
