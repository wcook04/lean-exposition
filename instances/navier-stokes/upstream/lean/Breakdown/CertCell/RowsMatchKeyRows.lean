import Breakdown.CertCell.AssemblyStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ}

section KeyRows

def evalValue (rd : KeyEvaluation) (z : ℂ) : ℂ :=
  (rd.sign : ℂ) * (if rd.conj then (starRingEnd ℂ) z else z)

def KeyHeadMatch (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (L : CellLayout) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (K : Fin D.mesh.count) (ι : D.mesh.resolved K)
      (d : ((R.layouts K).layout ι.1).Datum), keyOf ((R.layouts K).layout ι.1) d ≠ SkeletonKey.private_ →
      headHarmonic ((R.layouts K).layout ι.1) (labelTime ι.1) v G H Pg d
        = keyHarmonic L (labelTime ι.1) v G H Pg (keyOf ((R.layouts K).layout ι.1) d)

def KeyEvalTransfer (D : CellLayerData k C nE nM) (L : CellLayout) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ι : ℤ × ℤ) (key : SkeletonKey) (rd : KeyEvaluation),
      key ≠ SkeletonKey.private_ → (GaugeKey.keyMode key = some ι.1 ∨ ∃ p, key = SkeletonKey.stream p) →
      GaugeKey.KeyInHalfPlane key → IsKeyEvaluation ι key rd →
      keyHarmonic L (labelTime ι) v G H Pg key
        = evalValue rd (keyHarmonic L (labelTime rd.label) v G H Pg (keyWithMode rd.label.1 key))

def KeySplitAdditive (D : CellLayerData k C nE nM) (L : CellLayout) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ν : ℤ) (key : SkeletonKey) (rad : Bool) (lev lo hi : ℝ)
      (t : ℕ → ℕ → ℝ) (deg : ℕ), sideKeyGeom key = some (rad, lev, lo, hi, t, deg) → GaugeKey.KeyInHalfPlane key →
    ∀ (n : ℕ) (tlo thi : Fin n → ℝ) (ttest : Fin n → ℕ → ℕ → ℝ) (tdeg : ℕ) (coef : Fin n → ℕ → ℝ),
      0 < n → (∀ j, tlo j < thi j) → (∀ j j' : Fin n, j.val + 1 = j'.val → thi j = tlo j') →
      (∀ j : Fin n, j.val = 0 → tlo j = lo) → (∀ j : Fin n, j.val + 1 = n → thi j = hi) →
      (∀ j (s : ℝ), (keySeg rad lev lo hi t).test deg s
        = ∑ i ∈ Finset.range (tdeg + 1), coef j i * (keySeg rad lev (tlo j) (thi j) (ttest j)).test i s) →
      keyHarmonic L ν v G H Pg key
        = ∑ j, ∑ i ∈ Finset.range (tdeg + 1),
            (coef j i : ℂ) * keyHarmonic L ν v G H Pg (retileKey (tlo j) (thi j) (ttest j) i key)

namespace Internal.KeyRows

theorem sum_partVec_mul {α : Type} [Fintype α] (re im : Option α) (conj : Bool) (F : α → ℂ) :
    ∑ a, partVec re im conj a * F a
      = re.elim 0 F + (if conj then -Complex.I else Complex.I) * im.elim 0 F := by
  have key : ∀ (o : Option α) (c : ℂ) (dec : ∀ a, Decidable (o = some a)),
      ∑ a, (@ite ℂ (o = some a) (dec a) c 0) * F a = c * o.elim 0 F := by
    intro o c dec
    cases o with
    | none => simp
    | some b =>
      rw [Fintype.sum_eq_single b]
      · rw [if_pos rfl]
        rfl
      · intro x hx
        rw [if_neg (fun h => hx (Option.some_injective _ h).symm), zero_mul]
  simp only [partVec, add_mul, Finset.sum_add_distrib]
  rw [key re 1, key im]
  simp

theorem keyPart_add (imag : Bool) (a b : ℂ) :
    GaugeKey.keyPart imag (a + b) = GaugeKey.keyPart imag a + GaugeKey.keyPart imag b := by
  cases imag <;> simp [GaugeKey.keyPart]

theorem parts_combine (conj : Bool) (X : ℂ) :
    ((GaugeKey.keyPart false X : ℝ) : ℂ) + (if conj then -Complex.I else Complex.I) * ((GaugeKey.keyPart true X : ℝ) : ℂ)
      = if conj then (starRingEnd ℂ) X else X := by
  cases conj <;> apply Complex.ext <;> simp [GaugeKey.keyPart]

theorem dir_conj (Γ : GaugeKey.GaugeKeyValues) (c : Fin Γ.count) (ι : ℤ × ℤ) (key : SkeletonKey) :
    (starRingEnd ℂ) (Γ.dir c ι key) = Γ.dir c ι key := by
  simp [GaugeKey.GaugeKeyValues.dir]

theorem gauge_sum_conj {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hchk : T.gauge.Conditions) (hc : T.FieldGaugeConj) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (ι : ℤ × ℤ) (key : SkeletonKey) :
    ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir (T.gauge.conjClass c) ι key
      = (starRingEnd ℂ) (∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c ι key) := by
  have hinv : Function.Involutive T.gauge.conjClass := hchk.conj_invol
  rw [map_sum]
  rw [← Equiv.sum_comp hinv.toPerm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Function.Involutive.coe_toPerm, hchk.conj_invol, map_mul, dir_conj, hc v G H Pg c]

theorem gauge_part {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hchk : T.gauge.Conditions) (hc : T.FieldGaugeConj) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (ι : ℤ × ℤ) (key : SkeletonKey)
    (imag : Bool) :
    ((GaugeKey.keyPart imag (∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c ι key) : ℝ) : ℂ)
      = ∑ c, T.fieldGauge c v G H Pg *
          (if imag then (T.gauge.dir c ι key - T.gauge.dir (T.gauge.conjClass c) ι key) / (2 * Complex.I)
           else (T.gauge.dir c ι key + T.gauge.dir (T.gauge.conjClass c) ι key) / 2) := by
  have h := gauge_sum_conj T hchk hc v G H Pg ι key
  cases imag
  · simp only [GaugeKey.keyPart, Bool.false_eq_true, if_false]
    rw [Complex.re_eq_add_conj, ← h, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  · simp only [GaugeKey.keyPart, if_true]
    rw [Complex.im_eq_sub_conj, ← h, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring

def harmData {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (a : T.Slaved) : ℂ :=
  ((T.fieldData v G H Pg κ a : ℝ) : ℂ) - ∑ c, T.fieldGauge c v G H Pg * T.varPartDir c a

theorem harmData_key {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hchk : T.gauge.Conditions) (hc : T.FieldGaugeConj) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    {ι : ℤ × ℤ} {key : SkeletonKey} {imag : Bool} {a : T.Slaved} (h : IsKeyVar T ι key imag a) :
    harmData T v G H Pg κ a = ((GaugeKey.keyPart imag (keyHarmonic T.keyLayout (labelTime ι) v G H Pg key) : ℝ) : ℂ) := by
  obtain ⟨hcell, hk, hs, hi⟩ := h
  have hd : T.fieldData v G H Pg κ a = GaugeKey.keyPart imag (T.fieldKey v G H Pg ι key) := by
    simp only [TreeEntry.fieldData, hcell, hk, hs, hi, GaugeKey.keyPart]
  have hv : ∀ c, T.varDir c a = T.gauge.dir c ι key := by
    intro c
    simp only [TreeEntry.varDir, hcell, hk, hs]
  have hp : ∀ c, T.varPartDir c a =
      (if imag then (T.gauge.dir c ι key - T.gauge.dir (T.gauge.conjClass c) ι key) / (2 * Complex.I)
       else (T.gauge.dir c ι key + T.gauge.dir (T.gauge.conjClass c) ι key) / 2) := by
    intro c
    simp only [TreeEntry.varPartDir, hi, hv]
  unfold harmData
  rw [hd, TreeEntry.fieldKey, keyPart_add, Complex.ofReal_add, gauge_part T hchk hc v G H Pg ι key imag]
  simp only [hp, add_sub_cancel_right]

end Internal.KeyRows


namespace Internal.KeyRows

theorem strip_null_moment (c o : ℝ) (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) :
    heightStripMoment c o 0 0 wt F dF t = 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) (Set.Icc (0 : ℝ) 0 ×ˢ Set.Icc (min c o) (max c o)) = 0 := by
    apply measure_mono_null (t := ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
    · rintro ⟨a, b⟩ ⟨⟨ha, ha'⟩, -⟩
      exact ⟨le_antisymm ha' ha, trivial⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
  unfold heightStripMoment
  rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure, mul_zero]

theorem keyHarmonic_stream_axis (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (p : ℝ × ℝ) (hp : p.1 = 0) :
    keyHarmonic L ν v G H Pg (SkeletonKey.stream p) = 0 := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp
  subst hp
  simp only [keyHarmonic, keyValue, strip_null_moment, mul_zero, add_zero]

theorem dir_eq_zero_of_not_label (Γ : GaugeKey.GaugeKeyValues) (hchk : Γ.Conditions) {ι : ℤ × ℤ} (h : ι.1 ≠ 0)
    (c : Fin Γ.count) (key : SkeletonKey) : Γ.dir c ι key = 0 := by
  by_contra hd
  obtain ⟨hl, -⟩ := Γ.dir_support hd
  exact h (by rw [hl]; exact hchk.label_axis c)

theorem dir_eq_zero_of_not_pressure (Γ : GaugeKey.GaugeKeyValues) {key : SkeletonKey}
    (h : ∀ n rad lev lo hi t d, key ≠ SkeletonKey.pressure n rad lev lo hi t d) (c : Fin Γ.count) (ι : ℤ × ℤ) :
    Γ.dir c ι key = 0 := by
  by_contra hd
  obtain ⟨-, rad, lev, lo, hi, t, d, hk⟩ := Γ.dir_support hd
  exact h _ _ _ _ _ _ _ hk

theorem gauge_keyPart_zero {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hchk : T.gauge.Conditions) (hc : T.FieldGaugeConj) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) {ι : ℤ × ℤ} {key : SkeletonKey}
    {imag : Bool} (h : T.KeyPartOmitted ι key imag) (hnd : ¬ T.gauge.DeletedOmitted ι key) :
    GaugeKey.keyPart imag (∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c ι key) = 0 := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | h
  · obtain ⟨rfl, -, rfl⟩ := h
    simp only [GaugeKey.keyPart, if_true, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hd : T.gauge.dir c 0 key = 0
    · simp [hd]
    · obtain ⟨hl, -⟩ := T.gauge.dir_support hd
      have hself := hchk.conj_self c hl.symm
      have hre : (T.fieldGauge c v G H Pg).im = 0 := by
        have e := hc v G H Pg c
        rw [hself] at e
        exact Complex.conj_eq_iff_im.mp e.symm
      simp only [GaugeKey.GaugeKeyValues.dir, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hre]
      ring
  · obtain ⟨h1, h2, -⟩ := h
    have hne : ι.1 ≠ 0 := by omega
    simp only [dir_eq_zero_of_not_label T.gauge hchk hne, mul_zero, Finset.sum_const_zero]
    cases imag <;> simp [GaugeKey.keyPart]
  · obtain ⟨-, -, hs⟩ := h
    have hnp : ∀ n rad lev lo hi t d, key ≠ SkeletonKey.pressure n rad lev lo hi t d := by
      rintro n rad lev lo hi t d rfl
      simp only [GaugeKey.planeSign] at hs
      split_ifs at hs <;> simp at hs <;> norm_num at hs
    simp only [dir_eq_zero_of_not_pressure T.gauge hnp, mul_zero, Finset.sum_const_zero]
    cases imag <;> simp [GaugeKey.keyPart]
  · exact absurd h hnd

theorem harmData_part {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (hG : T.FieldGaugeHolds) (hchk : T.gauge.Conditions) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g Pg : ℝ → Space → Space} (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) {ι : ℤ × ℤ}
    {key : SkeletonKey} {imag : Bool} {o : Option T.Slaved} (h : PartBound T ι key imag o)
    (hnd : ¬ T.gauge.DeletedOmitted ι key) :
    o.elim 0 (harmData T v G H Pg κ)
      = ((GaugeKey.keyPart imag (keyHarmonic T.keyLayout (labelTime ι) v G H Pg key) : ℝ) : ℂ) := by
  cases o with
  | some a => exact harmData_key T hchk hG.conj v G H Pg κ h
  | none =>
    simp only [Option.elim]
    rcases h with h | ⟨p, rfl, hp⟩
    · have e := hG.omitted q v G H g Pg hfh ι key imag h
      rw [TreeEntry.fieldKey, keyPart_add, gauge_keyPart_zero T hchk hG.conj v G H Pg h hnd, add_zero] at e
      rw [e, Complex.ofReal_zero]
    · rw [keyHarmonic_stream_axis _ _ _ _ _ _ p hp]
      cases imag <;> simp [GaugeKey.keyPart]

theorem partVec_harmData {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    [Fintype T.Slaved] (hG : T.FieldGaugeHolds) (hchk : T.gauge.Conditions) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g Pg : ℝ → Space → Space} (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) {ι : ℤ × ℤ}
    {key : SkeletonKey} {re im : Option T.Slaved} (conj : Bool) (hre : PartBound T ι key false re)
    (him : PartBound T ι key true im) (hnd : ¬ T.gauge.DeletedOmitted ι key) :
    ∑ a, partVec re im conj a * harmData T v G H Pg κ a
      = if conj then (starRingEnd ℂ) (keyHarmonic T.keyLayout (labelTime ι) v G H Pg key)
        else keyHarmonic T.keyLayout (labelTime ι) v G H Pg key := by
  rw [sum_partVec_mul, harmData_part T hG hchk hfh κ hre hnd, harmData_part T hG hchk hfh κ him hnd,
    parts_combine]

theorem transport_split {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    [Fintype T.Slaved] (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (rv : T.Slaved → ℂ) :
    ∑ a, rv a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ)
      = ∑ a, rv a * harmData T v G H Pg κ a
        + ∑ c, T.fieldGauge c v G H Pg * ∑ a, rv a * T.varPartDir c a := by
  simp only [harmData, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun c a => T.fieldGauge c v G H Pg * (rv a * T.varPartDir c a))]
  have e : ∀ a, ∑ c, rv a * (T.fieldGauge c v G H Pg * T.varPartDir c a)
      = ∑ c, T.fieldGauge c v G H Pg * (rv a * T.varPartDir c a) :=
    fun a => Finset.sum_congr rfl (fun c _ => by ring)
  simp only [e]
  ring

theorem rowValue_eq_sum {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    [Fintype T.Slaved] (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (f : T.Slaved → ℝ) : W.rowValue K d f = ∑ a, W.rowVec K d a * ((f a : ℝ) : ℂ) := by
  classical
  simp only [RowEntry.rowValue, RowEntry.rowVec, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem deleted_facts (Γ : GaugeKey.GaugeKeyValues) (hchk : Γ.Conditions) {ι : ℤ × ℤ} {key : SkeletonKey}
    (h : Γ.DeletedOmitted ι key) :
    ι.1 = 0 ∧ (∃ rad lev lo hi t d, key = SkeletonKey.pressure 0 rad lev lo hi t d) ∧ Γ.DeletedOmitted (-ι) key := by
  obtain ⟨e, he⟩ := h
  obtain ⟨rad, lev, lo, hi, t, d, hd⟩ := hchk.deleted_pressure e
  have hl := hchk.deleted_label e
  rw [he] at hl hd
  simp only at hl hd
  refine ⟨by rw [hl]; exact hchk.label_axis e, ⟨rad, lev, lo, hi, t, d, hd⟩, Γ.conjClass e, ?_⟩
  have h1 := hchk.deleted_label (Γ.conjClass e)
  have h2 := hchk.deleted_conj e
  rw [hchk.conj_label, ← hl] at h1
  rw [he] at h2
  exact Prod.ext h1 h2

theorem evaluation_labels {ι : ℤ × ℤ} {key : SkeletonKey} {rd : KeyEvaluation} (hr : IsKeyEvaluation ι key rd)
    (h0 : ι.1 = 0) : rd.label = ι ∨ rd.label = -ι := by
  have hf : labelFlip ι = ι := by
    ext
    · simp [labelFlip, h0]
    · simp [labelFlip, h0]
  rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl (h.trans hf)
  · exact Or.inr (by rw [h, hf])

theorem evaluation_fst {ι : ℤ × ℤ} {key : SkeletonKey} {rd : KeyEvaluation} (hr : IsKeyEvaluation ι key rd) :
    rd.label.1 = ι.1 ∨ rd.label.1 = -ι.1 := by
  rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · left
    simp [labelFlip]

theorem deleted_evaluation (Γ : GaugeKey.GaugeKeyValues) (hchk : Γ.Conditions) {ι : ℤ × ℤ} {key : SkeletonKey}
    {rd : KeyEvaluation} (hr : IsKeyEvaluation ι key rd) (h : Γ.DeletedOmitted ι key) :
    Γ.DeletedOmitted rd.label (keyWithMode rd.label.1 key) := by
  obtain ⟨h0, ⟨rad, lev, lo, hi, t, d, rfl⟩, hneg⟩ := deleted_facts Γ hchk h
  have hm : rd.label.1 = 0 := by
    rcases evaluation_fst hr with e | e <;> rw [e, h0] <;> simp
  rw [hm]
  simp only [keyWithMode]
  rcases evaluation_labels hr h0 with e | e <;> rw [e]
  · exact h
  · exact hneg

theorem evaluation_deleted (Γ : GaugeKey.GaugeKeyValues) (hchk : Γ.Conditions) {ι : ℤ × ℤ} {key : SkeletonKey}
    {rd : KeyEvaluation} (hr : IsKeyEvaluation ι key rd)
    (hmode : GaugeKey.keyMode key = some ι.1 ∨ ∃ p, key = SkeletonKey.stream p)
    (h : Γ.DeletedOmitted rd.label (keyWithMode rd.label.1 key)) : Γ.DeletedOmitted ι key := by
  obtain ⟨h0, ⟨rad, lev, lo, hi, t, d, hk⟩, hneg⟩ := deleted_facts Γ hchk h
  have hι0 : ι.1 = 0 := by
    rcases evaluation_fst hr with e | e <;> rw [e] at h0 <;> linarith
  have hkey : keyWithMode rd.label.1 key = key := by
    rcases hmode with hm | ⟨p, rfl⟩
    · cases key with
      | pressure n rad' lev' lo' hi' t' d' =>
        simp only [GaugeKey.keyMode, Option.some.injEq] at hm
        simp only [keyWithMode, h0, hm, hι0]
      | velocity n r l lo' hi' t' a d' => simp [keyWithMode] at hk
      | gradient n r l lo' hi' t' a d' => simp [keyWithMode] at hk
      | corner n p a => simp [keyWithMode] at hk
      | stream p => simp [keyWithMode] at hk
      | private_ => simp [keyWithMode] at hk
    · simp [keyWithMode] at hk
  rw [hkey] at h hneg
  rcases evaluation_labels hr hι0 with e | e
  · rw [e] at h
    exact h
  · rw [e, neg_neg] at hneg
    exact hneg

theorem evalValue_eq (rd : KeyEvaluation) (X : ℂ) :
    (rd.sign : ℂ) * (if rd.conj then (starRingEnd ℂ) X else X) = evalValue rd X := rfl

end Internal.KeyRows

namespace Internal.KeyRows

theorem key_mode_of {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (hcc : CellCalculusConditions D R)
    (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (d : ((R.layouts K).layout ι.1).Datum)
    (hp : keyOf ((R.layouts K).layout ι.1) d ≠ SkeletonKey.private_) :
    GaugeKey.keyMode (keyOf ((R.layouts K).layout ι.1) d) = some ι.1.1 ∨
      ∃ p, keyOf ((R.layouts K).layout ι.1) d = SkeletonKey.stream p := by
  obtain ⟨c, S, -, hS, hcl⟩ := (hcc.layouts_valid K).layout_valid ι.1 ι.2
  have hm : ((R.layouts K).layout ι.1).modes = {ι.1.1} := hcl.modes_eq.trans hS
  have hmem : ∀ n : ((R.layouts K).layout ι.1).modes, (n : ℤ) = ι.1.1 := by
    intro n
    have h : (n : ℤ) ∈ ({ι.1.1} : Finset ℤ) := by
      rw [← hm]
      exact n.2
    exact Finset.mem_singleton.mp h
  rcases d with q|q|q|q|q|q|q|q
  · exact absurd rfl hp
  · exact absurd rfl hp
  · left
    simp only [keyOf, Sum.elim_inr, Sum.elim_inl, GaugeKey.keyMode, hmem]
  · left
    simp only [keyOf, Sum.elim_inr, Sum.elim_inl, GaugeKey.keyMode, hmem]
  · left
    simp only [keyOf, Sum.elim_inr, Sum.elim_inl, GaugeKey.keyMode, hmem]
  · left
    simp only [keyOf, Sum.elim_inr, Sum.elim_inl, GaugeKey.keyMode, hmem]
  · right
    exact ⟨_, rfl⟩
  · exact absurd rfl hp

end Internal.KeyRows

open Internal.KeyRows in
theorem keyRow_fields {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hS : KeyHeadMatch D R T.keyLayout) (hX : KeyEvalTransfer D T.keyLayout)
    (hG : T.FieldGaugeHolds) (hchk : T.gauge.Conditions) (hRK : T.RealKeyConditions)
    (hT : T.GaugeRowTransport W.rowVec) (hcc : CellCalculusConditions D R) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g Pg : ℝ → Space → Space} (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (rd : KeyEvaluation) (re im : Option T.Slaved)
    (hw : W.KeyRow K d rd re im) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) := by
  let _ := T.slavedFintype
  obtain ⟨hpriv, hread, hre, him, hrow⟩ := hw
  have hshift : T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))
      = headHarmonic ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d.2
        + ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) := rfl
  have hhead := hS q v G H g Pg hfh K d.1 d.2 hpriv
  have hmode := key_mode_of hcc K d.1 d.2 hpriv
  have hgeo := hRK.key_geometry K d
  have hx := hX q v G H g Pg hfh d.1.1 _ rd hpriv hmode hgeo hread
  rw [rowValue_eq_sum, hshift, hhead]
  by_cases hdel : T.gauge.DeletedOmitted d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2)
  · obtain ⟨e, he⟩ := hdel
    have hz := hG.deleted v G H Pg e
    rw [he] at hz
    have hz' : keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg (keyOf ((R.layouts K).layout d.1.1) d.2)
        + ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) = 0 := hz
    rw [hz']
    obtain ⟨e', he'⟩ := deleted_evaluation T.gauge hchk hread ⟨e, he⟩
    have hz2 := hG.deleted v G H Pg e'
    rw [he'] at hz2
    have hpart : ∀ (imag : Bool) (o : Option T.Slaved),
        PartBound T rd.label (keyWithMode rd.label.1 (keyOf ((R.layouts K).layout d.1.1) d.2)) imag o →
        o.elim 0 (fun a => ((T.fieldData v G H Pg κ a : ℝ) : ℂ)) = 0 := by
      intro imag o ho
      cases o with
      | none => rfl
      | some a =>
        obtain ⟨hc1, hk1, hs1, hi1⟩ := ho
        simp only [Option.elim, TreeEntry.fieldData, hc1, hk1, hs1, hi1, hz2]
        cases imag <;> simp
    rw [hrow]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [sum_partVec_mul, hpart false re hre, hpart true im him]
    simp
  · have hnd : ¬ T.gauge.DeletedOmitted rd.label (keyWithMode rd.label.1 (keyOf ((R.layouts K).layout d.1.1) d.2)) :=
      fun h => hdel (evaluation_deleted T.gauge hchk hread hmode h)
    have htr : ∀ c, T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2)
        = ∑ a, W.rowVec K d a * T.varPartDir c a := fun c => hT K d c hdel
    rw [transport_split T v G H Pg κ (W.rowVec K d)]
    simp only [← htr]
    congr 1
    rw [hrow]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [partVec_harmData T hG hchk hfh κ rd.conj hre him hnd, evalValue_eq, ← hx]


namespace Internal.KeyRows

theorem side_cases {key : SkeletonKey} {rad : Bool} {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ} {deg : ℕ}
    (h : sideKeyGeom key = some (rad, lev, lo, hi, t, deg)) :
    (∃ n a, key = SkeletonKey.velocity n rad lev lo hi t a deg) ∨
      (∃ n a, key = SkeletonKey.gradient n rad lev lo hi t a deg) ∨
      (∃ n, key = SkeletonKey.pressure n rad lev lo hi t deg) := by
  cases key with
  | velocity n r l lo' hi' t' a d =>
    simp only [sideKeyGeom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨n, a, rfl⟩
  | gradient n r l lo' hi' t' a d =>
    simp only [sideKeyGeom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact Or.inr (Or.inl ⟨n, a, rfl⟩)
  | pressure n r l lo' hi' t' d =>
    simp only [sideKeyGeom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact Or.inr (Or.inr ⟨n, rfl⟩)
  | corner n p a => simp [sideKeyGeom] at h
  | stream p => simp [sideKeyGeom] at h
  | private_ => simp [sideKeyGeom] at h

theorem retile_facts {key : SkeletonKey} {rad : Bool} {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ} {deg : ℕ}
    (h : sideKeyGeom key = some (rad, lev, lo, hi, t, deg)) (tl th : ℝ) (tt : ℕ → ℕ → ℝ) (i : ℕ) :
    retileKey tl th tt i key ≠ SkeletonKey.private_ ∧
      GaugeKey.keyMode (retileKey tl th tt i key) = GaugeKey.keyMode key ∧
      (keyOnPlane (retileKey tl th tt i key) ↔ keyOnPlane key) ∧
      keyFlipSign (retileKey tl th tt i key) = keyFlipSign key ∧
      (GaugeKey.KeyInHalfPlane key → lo ≤ tl → GaugeKey.KeyInHalfPlane (retileKey tl th tt i key)) := by
  rcases side_cases h with ⟨n, a, rfl⟩ | ⟨n, a, rfl⟩ | ⟨n, rfl⟩ <;>
    refine ⟨by simp [retileKey], rfl, Iff.rfl, rfl, fun hk hl => ?_⟩ <;>
    cases rad <;> simp only [retileKey, GaugeKey.KeyInHalfPlane, if_true, Bool.false_eq_true, if_false] at hk ⊢ <;>
    first | exact hk | linarith

theorem evaluation_retile {ι : ℤ × ℤ} {key : SkeletonKey} {rd : KeyEvaluation} {rad : Bool} {lev lo hi : ℝ}
    {t : ℕ → ℕ → ℝ} {deg : ℕ} (h : sideKeyGeom key = some (rad, lev, lo, hi, t, deg)) (tl th : ℝ)
    (tt : ℕ → ℕ → ℝ) (i : ℕ) (hr : IsKeyEvaluation ι key rd) : IsKeyEvaluation ι (retileKey tl th tt i key) rd := by
  obtain ⟨-, -, hp, hs, -⟩ := retile_facts h tl th tt i
  unfold IsKeyEvaluation at hr ⊢
  rw [hp, hs]
  exact hr

theorem sign_sq {ι : ℤ × ℤ} {key : SkeletonKey} {rd : KeyEvaluation} (hr : IsKeyEvaluation ι key rd) :
    (rd.sign : ℂ) * (rd.sign : ℂ) = 1 := by
  have hf : ∀ a : Fin 3, frameSign a * frameSign a = 1 := by
    intro a
    unfold frameSign
    split_ifs <;> norm_num
  have hr' : rd.sign * rd.sign = 1 := by
    rcases hr with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, hp, h⟩ | ⟨-, -, hp, h⟩
    · rw [h]; norm_num
    · rw [h]; norm_num
    all_goals
      rw [h]
      cases key with
      | velocity n r l lo hi t a d => exact hf a
      | gradient n r l lo hi t a d => simp only [keyFlipSign, neg_mul_neg]; exact hf a
      | pressure n r l lo hi t d => simp [keyFlipSign]
      | corner n p a => exact hf a
      | stream p => exact hf 2
      | private_ => exact absurd hp (by simp [keyOnPlane])
  exact_mod_cast hr'

theorem sign_cancel (s c Y : ℂ) (h : s * s = 1) : c * Y = s * (c * (s * Y)) := by
  linear_combination (-(c * Y)) * h

theorem tile_lo_ge {n : ℕ} (tlo thi : Fin n → ℝ) (lo : ℝ) (hlt : ∀ j, tlo j < thi j)
    (hnext : ∀ j j' : Fin n, j.val + 1 = j'.val → thi j = tlo j') (hfirst : ∀ j : Fin n, j.val = 0 → tlo j = lo) :
    ∀ j, lo ≤ tlo j := by
  intro j
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => exact le_of_eq (hfirst ⟨0, hm⟩ rfl).symm
  | succ m ih =>
    have hm' : m < n := by omega
    have h1 := ih hm'
    have h2 := hlt ⟨m, hm'⟩
    have h3 := hnext ⟨m, hm'⟩ ⟨m + 1, hm⟩ rfl
    linarith

theorem sum_smul_double {α : Type} [Fintype α] {n : ℕ} (s : ℂ) (c : Fin n → ℕ → ℂ)
    (f : Fin n → ℕ → α → ℂ) (N : ℕ) (F : α → ℂ) :
    ∑ a, (s • ∑ j, ∑ i ∈ Finset.range N, c j i • f j i) a * F a
      = s * ∑ j, ∑ i ∈ Finset.range N, c j i * ∑ a, f j i a * F a := by
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => by ring))

theorem partVec_gauge_zero {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    [Fintype T.Slaved] {ι : ℤ × ℤ} {key : SkeletonKey} {re im : Option T.Slaved} (conj : Bool)
    (hre : PartBound T ι key false re) (him : PartBound T ι key true im) (hz : ∀ c ι', T.gauge.dir c ι' key = 0)
    (c : Fin T.gauge.count) : ∑ a, partVec re im conj a * T.varPartDir c a = 0 := by
  have hv : ∀ (imag : Bool) (o : Option T.Slaved), PartBound T ι key imag o → o.elim 0 (T.varPartDir c) = 0 := by
    intro imag o ho
    cases o with
    | none => rfl
    | some a =>
      obtain ⟨hc1, hk1, hs1, hi1⟩ := ho
      have hd : ∀ c', T.varDir c' a = 0 := by
        intro c'
        simp only [TreeEntry.varDir, hc1, hk1, hs1, hz]
      simp only [Option.elim, TreeEntry.varPartDir, hd, sub_zero, add_zero, zero_div, ite_self]
  rw [sum_partVec_mul, hv false re hre, hv true im him, mul_zero, add_zero]

theorem dir_stream_zero (Γ : GaugeKey.GaugeKeyValues) (p : ℝ × ℝ) (c : Fin Γ.count) (ι : ℤ × ℤ) :
    Γ.dir c ι (SkeletonKey.stream p) = 0 := by
  simp [GaugeKey.GaugeKeyValues.dir, GaugeKey.GaugeKeyValues.dirReal]

theorem dir_velocity_zero (Γ : GaugeKey.GaugeKeyValues) (n : ℤ) (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ)
    (a : Fin 3) (i : ℕ) (c : Fin Γ.count) (ι : ℤ × ℤ) :
    Γ.dir c ι (SkeletonKey.velocity n rad lev lo hi t a i) = 0 := by
  simp [GaugeKey.GaugeKeyValues.dir, GaugeKey.GaugeKeyValues.dirReal]

end Internal.KeyRows

open Internal.KeyRows in
theorem splitRow_fields {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hS : KeyHeadMatch D R T.keyLayout) (hX : KeyEvalTransfer D T.keyLayout)
    (hA : KeySplitAdditive D T.keyLayout) (hG : T.FieldGaugeHolds) (hchk : T.gauge.Conditions)
    (hRK : T.RealKeyConditions) (hT : T.GaugeRowTransport W.rowVec) (hcc : CellCalculusConditions D R)
    {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (w : SplitChoice T) (hw : W.SplitRow K d w)
    (hflux : ∀ {rad : Bool} {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ} {deg : ℕ},
      sideKeyGeom (keyOf ((R.layouts K).layout d.1.1) d.2) = some (rad, lev, lo, hi, t, deg) →
      ∀ j, w.flux j = true →
        (haveI := T.slavedFintype; ∑ a, RowEntry.tileFlux rad lev w j a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ))
          = keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg
              (retileKey (w.tlo j) (w.thi j) (w.ttest j) 0 (keyOf ((R.layouts K).layout d.1.1) d.2))) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) := by
  let _ := T.slavedFintype
  obtain ⟨⟨rad, lev, lo, hi, t, deg⟩, hgeom⟩ :
      ∃ x, sideKeyGeom (keyOf ((R.layouts K).layout d.1.1) d.2) = some x := by
    cases h : sideKeyGeom (keyOf ((R.layouts K).layout d.1.1) d.2) with
    | none =>
      exfalso
      simp only [RowEntry.SplitRow, h] at hw
    | some x => exact ⟨x, rfl⟩
  have hfl := @hflux rad lev lo hi t deg hgeom
  simp only [RowEntry.SplitRow, hgeom] at hw
  obtain ⟨hread, htiles, hdel, hndt, hlt, hnext, hfirst, hlast, hpoly, hparts, hfx, hrow⟩ := hw
  have hpriv : keyOf ((R.layouts K).layout d.1.1) d.2 ≠ SkeletonKey.private_ := by
    intro h
    rw [h] at hgeom
    simp [sideKeyGeom] at hgeom
  have hshift : T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d))
      = headHarmonic ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d.2
        + ∑ c, T.fieldGauge c v G H Pg * T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2) := rfl
  have hhead := hS q v G H g Pg hfh K d.1 d.2 hpriv
  have hmode : GaugeKey.keyMode (keyOf ((R.layouts K).layout d.1.1) d.2) = some d.1.1.1 := by
    rcases key_mode_of hcc K d.1 d.2 hpriv with h | ⟨p, hp⟩
    · exact h
    · rw [hp] at hgeom
      simp [sideKeyGeom] at hgeom
  have hgeo := hRK.key_geometry K d
  have htr : ∀ c, T.gauge.dir c d.1.1 (keyOf ((R.layouts K).layout d.1.1) d.2)
      = ∑ a, W.rowVec K d a * T.varPartDir c a := fun c => hT K d c hdel
  have hlo := tile_lo_ge w.tlo w.thi lo hlt hnext hfirst
  have hsq := sign_sq hread
  have hadd := hA q v G H g Pg hfh (labelTime d.1.1) _ rad lev lo hi t deg hgeom hgeo w.tiles w.tlo w.thi w.ttest
    w.tdeg w.coef htiles hlt hnext hfirst hlast hpoly
  have hterm : ∀ j, ∀ i ∈ Finset.range (w.tdeg + 1),
      (w.coef j i : ℂ) * ∑ a, RowEntry.tileVec rad lev w j i a * harmData T v G H Pg κ a
        = (w.evaluation.sign : ℂ) * ((w.coef j i : ℂ) * keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg
            (retileKey (w.tlo j) (w.thi j) (w.ttest j) i (keyOf ((R.layouts K).layout d.1.1) d.2))) := by
    intro j i hi
    by_cases hc : w.coef j i = 0
    · simp [hc]
    by_cases hf : w.flux j = true ∧ i = 0
    · obtain ⟨hfj, rfl⟩ := hf
      obtain ⟨hvn, hs1, hrd, hends, -, hheight⟩ := hfx j hfj
      have hv : RowEntry.tileVec rad lev w j 0 = RowEntry.tileFlux rad lev w j := by
        simp [RowEntry.tileVec, hfj]
      have hz : ∀ c, ∑ a, RowEntry.tileFlux rad lev w j a * T.varPartDir c a = 0 := by
        intro c
        have he : ∀ e : Fin 2, ∑ a, partVec (w.fre j e) (w.fim j e) w.evaluation.conj a * T.varPartDir c a = 0 :=
          fun e => partVec_gauge_zero T w.evaluation.conj (hends e).1 (hends e).2
            (fun c' ι' => dir_stream_zero _ _ c' ι') c
        cases rad with
        | true =>
          simp only [RowEntry.tileFlux, if_true, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, sub_mul,
            mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, he, sub_zero, mul_zero]
        | false =>
          obtain ⟨-, hre1, him1⟩ := hheight rfl
          have hkv : ∃ n r l lo' hi' t' a' d', keyWithMode w.evaluation.label.1 (retileKey (w.tlo j) (w.thi j) (w.ttest j) 1
              (keyOf ((R.layouts K).layout d.1.1) d.2)) = SkeletonKey.velocity n r l lo' hi' t' a' d' := by
            revert hvn
            cases keyOf ((R.layouts K).layout d.1.1) d.2 <;> simp [keyVelNormal, retileKey, keyWithMode]
          obtain ⟨n, r, l, lo', hi', t', a', d', hkeq⟩ := hkv
          rw [hkeq] at hre1 him1
          have h1 := partVec_gauge_zero T w.evaluation.conj hre1 him1 (fun c' ι' => dir_velocity_zero _ _ _ _ _ _ _ _ _ c' ι') c
          simp only [RowEntry.tileFlux, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
            mul_sub, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, he, h1, sub_zero, mul_zero]
      rw [hv]
      have e1 := transport_split T v G H Pg κ (RowEntry.tileFlux rad lev w j)
      simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at e1
      rw [← e1, hfl j hfj, hs1]
      push_cast
      ring
    · have hv : RowEntry.tileVec rad lev w j i = partVec (w.re j i) (w.im j i) w.evaluation.conj := by
        simp only [RowEntry.tileVec, hf, if_false]
      obtain ⟨hre, him⟩ := hparts j i hi hc hf
      obtain ⟨hrp, hrm, -, -, hrh⟩ := retile_facts hgeom (w.tlo j) (w.thi j) (w.ttest j) i
      have hx := hX q v G H g Pg hfh d.1.1 _ w.evaluation hrp (Or.inl (hrm.trans hmode)) (hrh hgeo (hlo j))
        (evaluation_retile hgeom _ _ _ i hread)
      rw [hv, partVec_harmData T hG hchk hfh κ w.evaluation.conj hre him (hndt j i hi hc), hx, ← evalValue_eq]
      exact sign_cancel _ _ _ hsq
  rw [rowValue_eq_sum, hshift, hhead, transport_split T v G H Pg κ (W.rowVec K d)]
  simp only [← htr]
  congr 1
  rw [hrow, sum_smul_double, Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (hterm j)), hadd]
  simp only [← Finset.mul_sum]
  rw [← mul_assoc, hsq, one_mul]

end KeyRows

end Assembly

end CertCell

end Breakdown
