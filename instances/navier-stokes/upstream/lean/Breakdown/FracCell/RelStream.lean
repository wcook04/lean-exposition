import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def ModeStripIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (n : ℤ) (R z₁ z₂ : ℝ),
      (∀ a, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc 0 R ×ˢ Icc z₁ z₂)) ∧
        ∀ a b, IntegrableOn (gradMode m n G a b) (Icc 0 R ×ˢ Icc z₁ z₂)

def CylinderFluxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (R o z₁ z₂ : ℝ), 0 < R → 0 ≤ o → o ≠ R → z₁ < z₂ →
      (R : ℂ) * radialStripMoment R o z₁ z₂ (fun p => modeVec m 0 v p.1 p.2 0) (gradMode m 0 G 0 0)
          (fun _ => 1)
        + heightStripMoment z₂ z₁ 0 R (fun r => r) (fun p => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2)
          (fun _ => 1)
        - heightStripMoment z₁ z₂ 0 R (fun r => r) (fun p => modeVec m 0 v p.1 p.2 2) (gradMode m 0 G 2 2)
          (fun _ => 1) = 0

namespace Internal.RelStream

theorem pairUnit (L : CellLayout) (T : L.Datum → ℂ) (d₀ : L.Datum) :
    ∑ d, L.unitAt d₀ d * T d = T d₀ := by
  simp [CellLayout.unitAt, Pi.single_apply]

theorem pairAdd (L : CellLayout) (T f g : L.Datum → ℂ) :
    ∑ d, (f + g) d * T d = ∑ d, f d * T d + ∑ d, g d * T d := by
  simp [add_mul, Finset.sum_add_distrib]

theorem pairSub (L : CellLayout) (T f g : L.Datum → ℂ) :
    ∑ d, (f - g) d * T d = ∑ d, f d * T d - ∑ d, g d * T d := by
  simp [sub_mul, Finset.sum_sub_distrib]

theorem pairSmul (L : CellLayout) (T f : L.Datum → ℂ) (a : ℂ) :
    ∑ d, (a • f) d * T d = a * ∑ d, f d * T d := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem test_zero (S : FaceSegment) : S.test 0 = fun _ => S.testCoef 0 0 := by
  funext u; simp [FaceSegment.test]

theorem test_one (S : FaceSegment) : S.test 1 = fun u => S.testCoef 1 0 + S.testCoef 1 1 * u := by
  funext u; simp [FaceSegment.test, Finset.sum_range_succ]

theorem radialStrip_const (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (k : ℝ) :
    radialStripMoment c o lo hi F dF (fun _ => k) = (k : ℂ) * radialStripMoment c o lo hi F dF (fun _ => 1) := by
  simp only [radialStripMoment, Complex.ofReal_one, mul_one, integral_mul_const]
  ring

theorem split_core (g : ℝ × ℝ → ℂ) (Z : Set ℝ) (hZ : IsCompact Z) (hZm : MeasurableSet Z)
    (lo hi c00 c10 c11 : ℝ) (h00 : c00 ≠ 0) (h11 : c11 ≠ 0) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hg : IntegrableOn g (Icc 0 hi ×ˢ Z)) :
    ((1 / c11 : ℝ) : ℂ) * ((∫ p in Icc lo hi ×ˢ Z, g p * ((1 * (c10 + c11 * p.1) : ℝ) : ℂ))
        - ((c10 / c00 : ℝ) : ℂ) * ∫ p in Icc lo hi ×ˢ Z, g p * ((1 * c00 : ℝ) : ℂ))
      - (∫ p in Icc 0 hi ×ˢ Z, g p * ((p.1 * 1 : ℝ) : ℂ))
      + (∫ p in Icc 0 lo ×ˢ Z, g p * ((p.1 * 1 : ℝ) : ℂ)) = 0 := by
  have hK : IsCompact (Icc 0 hi ×ˢ Z) := isCompact_Icc.prod hZ
  have hr : IntegrableOn (fun p : ℝ × ℝ => g p * ((p.1 : ℝ) : ℂ)) (Icc 0 hi ×ˢ Z) :=
    hg.mul_continuousOn (by fun_prop) hK
  have hsubb : Icc lo hi ×ˢ Z ⊆ Icc 0 hi ×ˢ Z :=
    prod_mono (Icc_subset_Icc hlo le_rfl) le_rfl
  have hsuba : Icc 0 lo ×ˢ Z ⊆ Icc 0 hi ×ˢ Z :=
    prod_mono (Icc_subset_Icc le_rfl hlh) le_rfl
  have hunion : Icc 0 hi ×ˢ Z = Icc 0 lo ×ˢ Z ∪ Icc lo hi ×ˢ Z := by
    rw [← union_prod, Icc_union_Icc_eq_Icc hlo hlh]
  have hdisj : AEDisjoint volume (Icc 0 lo ×ˢ Z) (Icc lo hi ×ˢ Z) := by
    refine measure_mono_null (t := ({lo} : Set ℝ) ×ˢ (univ : Set ℝ)) ?_ ?_
    · rintro ⟨a, b⟩ ⟨⟨⟨-, ha⟩, -⟩, ⟨⟨ha', -⟩, -⟩⟩
      exact ⟨le_antisymm ha ha', trivial⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have e1 : (∫ p in Icc 0 hi ×ˢ Z, g p * ((p.1 * 1 : ℝ) : ℂ)) =
      (∫ p in Icc 0 lo ×ˢ Z, g p * ((p.1 * 1 : ℝ) : ℂ)) + ∫ p in Icc lo hi ×ˢ Z, g p * ((p.1 : ℝ) : ℂ) := by
    simp only [mul_one]
    rw [hunion, setIntegral_union₀ hdisj ((measurableSet_Icc.prod hZm).nullMeasurableSet)
      (hr.mono_set hsuba) (hr.mono_set hsubb)]
  have e2 : (∫ p in Icc lo hi ×ˢ Z, g p * ((1 * (c10 + c11 * p.1) : ℝ) : ℂ)) =
      (c10 : ℂ) * (∫ p in Icc lo hi ×ˢ Z, g p) + (c11 : ℂ) * ∫ p in Icc lo hi ×ˢ Z, g p * ((p.1 : ℝ) : ℂ) := by
    have : (fun p : ℝ × ℝ => g p * ((1 * (c10 + c11 * p.1) : ℝ) : ℂ)) =
        fun p => (c10 : ℂ) * g p + (c11 : ℂ) * (g p * ((p.1 : ℝ) : ℂ)) := by
      funext p; push_cast; ring
    rw [this, integral_add ((hg.mono_set hsubb).const_mul _) ((hr.mono_set hsubb).const_mul _),
      integral_const_mul, integral_const_mul]
  have e3 : (∫ p in Icc lo hi ×ˢ Z, g p * ((1 * c00 : ℝ) : ℂ)) = (c00 : ℂ) * ∫ p in Icc lo hi ×ˢ Z, g p := by
    simp only [one_mul]; rw [integral_mul_const]; ring
  rw [e1, e2, e3]
  have h00' : (c00 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h00
  have h11' : (c11 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h11
  push_cast
  field_simp
  ring

end Internal.RelStream

namespace Internal.RelStream

theorem strip_point (c o : ℝ) (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) :
    heightStripMoment c o 0 0 wt F dF t = 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) (Icc (0 : ℝ) 0 ×ˢ Icc (min c o) (max c o)) = 0 := by
    refine measure_mono_null (t := ({0} : Set ℝ) ×ˢ (univ : Set ℝ)) ?_ ?_
    · rintro ⟨a, b⟩ ⟨⟨ha, ha'⟩, -⟩
      exact ⟨le_antisymm ha' ha, trivial⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  simp only [heightStripMoment]
  rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure, mul_zero]

end Internal.RelStream

open Internal.RelStream in
theorem relStream_of (hI : ModeStripIntegrableStatement) (hF : CylinderFluxStatement) :
    RelStreamStatement := by
  intro k N c K S B L hL x hx s
  have hso := hx.1
  have hord := hL.order_eq
  have hbox := hL.box_valid
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  by_cases h0 : (0 : ℤ) ∈ L.modes
  swap
  · simp [CellLayout.zeroMode, h0]
  rw [show L.zeroMode = some ⟨0, h0⟩ by simp [CellLayout.zeroMode, h0]]
  dsimp only
  have hv := hL.segment_valid s
  by_cases hrad : (L.segment s).radial = true
  · rw [if_pos hrad]
    rcases hL.segment_on_side s with ⟨-, hlev, hzlo, hzhi, hlev0⟩ | ⟨hnr, -⟩
    swap
    · exact absurd hrad hnr
    have hoth := (hL.segment_other_in_box s).1 hrad
    have h00 := hL.radial_test_const s hrad
    obtain ⟨c1, h1⟩ : ∃ c1, L.segEnd s 1 = some c1 := by
      cases h : L.segEnd s 1 with
      | none => exact absurd (hL.segEnd_axis s 1 h).2.1 (by decide)
      | some c1 => exact ⟨c1, rfl⟩
    obtain ⟨c0, h0'⟩ : ∃ c0, L.segEnd s 0 = some c0 := by
      cases h : L.segEnd s 0 with
      | none => exact absurd hrad (hL.segEnd_axis s 0 h).1
      | some c0 => exact ⟨c0, rfl⟩
    have hc1 : L.corner c1 = ((L.segment s).level, (L.segment s).hi) := by
      simpa [hrad] using hL.segEnd_spec s 1 c1 h1
    have hc0 : L.corner c0 = ((L.segment s).level, (L.segment s).lo) := by
      simpa [hrad] using hL.segEnd_spec s 0 c0 h0'
    have hhi : (L.segment s).hi = K.z₂ := by
      have h := (hL.corner_is_corner c1).2.1
      rw [hc1] at h
      rcases h with h | h
      · have := hv.lo_lt_hi; linarith
      · exact h
    have hlo : (L.segment s).lo = K.z₁ := by
      have h := (hL.corner_is_corner c0).2.1
      rw [hc0] at h
      rcases h with h | h
      · exact h
      · have := hv.lo_lt_hi; linarith
    have ho1 := (hL.corner_other c1).2
    have ho0 := (hL.corner_other c0).2
    rw [hc1] at ho1
    rw [hc0] at ho0
    rw [h1, h0']
    simp only [CellLayout.streamAt]
    rw [pairSub, pairAdd, pairSmul, dif_pos (by omega : 0 < L.degSide + 2), pairUnit, pairUnit,
      pairUnit]
    simp only [CellLayout.trueData, CellDatum.sideVelocity, CellDatum.cornerStream, Sum.elim_inr,
      Sum.elim_inl, FaceSegment.moment, hrad, if_true, test_zero]
    rw [ho1, ho0, hc1, hc0, radialStrip_const]
    simp only [hhi, hlo, show K.z₁ + K.z₂ - K.z₂ = K.z₁ by ring, show K.z₁ + K.z₂ - K.z₁ = K.z₂ by ring]
    have hR : 0 < (L.segment s).level := by
      rcases hlev with h | h <;> rw [h] at hlev0 ⊢ <;> [exact lt_of_le_of_ne hbox.r_order.1 (Ne.symm hlev0);
        exact lt_of_le_of_ne (hbox.r_order.1.trans hbox.r_order.2.le) (Ne.symm hlev0)]
    have ho : 0 ≤ (L.segment s).other := by
      rw [hoth]; rcases hlev with h | h <;> rw [h] <;> linarith [hbox.r_order.1, hbox.r_order.2]
    have key := hF c.order x.1 x.2.1 x.2.2.1 hso (L.segment s).level (L.segment s).other K.z₁ K.z₂ hR ho
      hv.other_ne hbox.z_order.2
    have ev : ∀ a, L.velMode 0 x a = fun p => modeVec c.order 0 x.1 p.1 p.2 a := by
      intro a; funext p; rw [← hord]; rfl
    have eg : ∀ a b, L.gradModeOf 0 x a b = gradMode c.order 0 x.2.1 a b := by
      intro a b; rw [← hord]; rfl
    rw [ev, ev, eg, eg]
    have h00' : ((L.segment s).testCoef 0 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h00
    rw [← key]
    push_cast
    field_simp
  · rw [if_neg hrad]
    rcases hL.segment_on_side s with ⟨hr, -⟩ | ⟨-, hlev, hrlo, hrhi⟩
    · exact absurd hr hrad
    have hoth := (hL.segment_other_in_box s).2 hrad
    obtain ⟨h00, h11⟩ := hL.height_test_affine s hrad
    have hlo0 : 0 ≤ (L.segment s).lo := le_trans hbox.r_order.1 hrlo
    have hlh : (L.segment s).lo ≤ (L.segment s).hi := hv.lo_lt_hi.le
    have hψ : ∀ e : Fin 2, ∑ d, L.streamAt (L.segEnd s e) d * L.trueData x d =
        heightStripMoment (L.segment s).level (L.segment s).other 0
          (if e = 0 then (L.segment s).lo else (L.segment s).hi) (fun r => r)
          (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1) := by
      intro e
      cases h : L.segEnd s e with
      | none =>
        obtain ⟨-, he, hl⟩ := hL.segEnd_axis s e h
        subst he
        simp only [CellLayout.streamAt, Pi.zero_apply, zero_mul, Finset.sum_const_zero, if_true, hl]
        exact (strip_point _ _ _ _ _ _).symm
      | some c0 =>
        have hc := hL.segEnd_spec s e c0 h
        rw [if_neg hrad] at hc
        have ho := (hL.corner_other c0).2
        simp only [CellLayout.streamAt]
        rw [pairUnit]
        simp only [CellLayout.trueData, CellDatum.cornerStream, Sum.elim_inr, Sum.elim_inl]
        rw [ho, hc, hoth]
    rw [pairAdd, pairSub, pairSmul, pairSub, pairSmul, pairUnit, pairUnit, hψ 0, hψ 1]
    simp only [CellLayout.trueData, CellDatum.sideVelocity, Sum.elim_inr, Sum.elim_inl, FaceSegment.moment,
      hrad, if_false, Bool.false_eq_true, test_zero, test_one, Fin.isValue, one_ne_zero]
    have hZ : IsCompact (Icc (min (L.segment s).level (L.segment s).other)
        (max (L.segment s).level (L.segment s).other)) := isCompact_Icc
    have hIx := hI c.order x.1 x.2.1 x.2.2.1 hso 0 (L.segment s).hi
      (min (L.segment s).level (L.segment s).other) (max (L.segment s).level (L.segment s).other)
    have hU := hIx.1 2
    have hdU := hIx.2 2 2
    have hg : IntegrableOn (fun p : ℝ × ℝ =>
        (((1 / ((L.segment s).level - (L.segment s).other) : ℝ)) : ℂ) * L.velMode 0 x 2 p
          + (((p.2 - (L.segment s).other) / ((L.segment s).level - (L.segment s).other) : ℝ) : ℂ)
            * L.gradModeOf 0 x 2 2 p)
        (Icc 0 (L.segment s).hi ×ˢ Icc (min (L.segment s).level (L.segment s).other)
          (max (L.segment s).level (L.segment s).other)) := by
      simp only [CellLayout.velMode, CellLayout.gradModeOf, hord]
      exact (hU.const_mul _).add (IntegrableOn.continuousOn_mul (by fun_prop) hdU (isCompact_Icc.prod hZ))
    have key := split_core _ _ hZ measurableSet_Icc (L.segment s).lo (L.segment s).hi
      ((L.segment s).testCoef 0 0) ((L.segment s).testCoef 1 0) ((L.segment s).testCoef 1 1) h00 h11 hlo0 hlh hg
    simp only [heightStripMoment, ↓reduceIte]
    simp only [mul_one] at key ⊢
    linear_combination (edgeSign (L.segment s).level (L.segment s).other) * key

end CellFormula

end CellCert

end Breakdown
