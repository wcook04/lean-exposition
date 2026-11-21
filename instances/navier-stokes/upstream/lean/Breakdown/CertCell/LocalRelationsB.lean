import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.AxisFlux
import Breakdown.FracCell.RelStream
import Breakdown.FracCell.CylinderFlux
import Breakdown.FracCell.StripTrace
import Breakdown.FracCell.RelSideSplit

open MeasureTheory Matrix Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

theorem localAxisFlux_of (hI : LocalAxisModeIntegrableStatement) (hA : LocalAngularModeStatement) :
    LocalAxisFluxStatement := by
  intro m v G H hv R z₁ z₂ hR hz t ht i σ
  have hRP' := CellFormula.modeRadialParts m v G hv.measurable_velocity hv.velocity_six hv.measurable_gradient
    hv.gradient_two hv.weak_gradient 0 (if σ = 0 then 0 else 1) 0 R z₁ z₂ le_rfl hR hz
  have hnz : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * (if σ = 0 then gradMode m 0 G 1 1 p else -gradMode m 0 G 0 1 p)
        = modeVec m 0 v p.1 p.2 (if σ = 0 then 0 else 1) := by
    filter_upwards [hA m v G H hv 0] with p hp hpos
    obtain ⟨h1, h2, -⟩ := hp hpos
    by_cases hσ : σ = 0
    · simp only [if_pos hσ]
      rw [h2]
      simp [azimuth]
    · simp only [if_neg hσ]
      rw [mul_neg, h1]
      simp [azimuth]
  have hFint : IntegrableOn (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 (if σ = 0 then 0 else 1))
      (Icc 0 R ×ˢ Icc z₁ z₂) := by
    have hrX : IntegrableOn (fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (if σ = 0 then gradMode m 0 G 1 1 p else -gradMode m 0 G 0 1 p))
        (Icc 0 R ×ˢ Icc z₁ z₂) := by
      by_cases hσ : σ = 0
      · simp only [if_pos hσ]
        exact hI m v G H hv R z₁ z₂ 0 1 1
      · simp only [if_neg hσ, mul_neg]
        exact (hI m v G H hv R z₁ z₂ 0 0 1).neg
    refine hrX.congr_fun_ae ?_
    refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 ?_
    filter_upwards [hnz, AxisFluxInternal.ae_fst_ne_zero] with p hp hne hpS
    exact hp (lt_of_le_of_ne (Set.mem_prod.1 hpS).1.1 (Ne.symm hne))
  exact AxisFluxInternal.hbase hR ht i hFint hnz (fun g hg => hRP'.1 g t hg ht)
    (fun ψ hψ h0 hR' => hRP'.2 ψ t hψ ht h0 hR')

open RelAxisInternal in
theorem localRelAxis_of (hI : LocalAxisModeIntegrableStatement) (hF : LocalAxisFluxStatement) :
    LocalRelAxisStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨σ, l, i⟩ := ρ
  have hB : IsCellBases L.box L.bases := by rw [hL.box_eq, hL.bases_eq]; exact hL.bases_valid
  have hbox : IsCellBox L.box := by rw [hL.box_eq]; exact hL.box_valid
  have hsec : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  rcases hz : L.zeroMode with _ | n0
  · simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  have hn0 := zeroMode_val L n0 hz
  dsimp only
  by_cases hK : L.box.r₁ = 0
  swap
  · simp only [if_pos hK, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  rw [if_neg (not_not.mpr hK)]
  have hl : (l : ℕ) < L.degCoef + 1 := l.2
  have hi : (i : ℕ) ≤ L.degCoef := Nat.lt_succ_iff.1 i.2
  have hr : 0 < L.box.r₂ := by have := hbox.r_order; linarith
  have hz' : L.box.z₁ < L.box.z₂ := hbox.z_order.2
  have hψ := heightPoly_continuous L.bases l
  have hflux := hF L.order x.1 x.2.1 x.2.2.1 hsec L.box.r₂ L.box.z₁ L.box.z₂ hr hz' _ hψ i σ
  have hrect : L.box.rect = Set.Icc 0 L.box.r₂ ×ˢ Set.Icc L.box.z₁ L.box.z₂ := by
    simp [CellBox.rect, hK]
  rw [← hrect] at hflux
  have hint : ∀ a b : Fin 3,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode L.order 0 x.2.1 a b p) L.box.rect := by
    intro a b
    rw [hrect]
    exact hI L.order x.1 x.2.1 x.2.2.1 hsec L.box.r₂ L.box.z₁ L.box.z₂ 0 a b
  rw [ev_sub, ev_sub, ev_smul, ev_extra _ _ _ _ _ _ hl, ev_sum, ev_sum]
  have hext : L.extraValue (n0 : ℤ) x 1 (if σ = 0 then 0 else 1) l =
      radialStripMoment L.box.r₂ 0 L.box.z₁ L.box.z₂
        (fun p => modeVec L.order 0 x.1 p.1 p.2 (if σ = 0 then 0 else 1))
        (gradMode L.order 0 x.2.1 (if σ = 0 then 0 else 1) 0) (L.bases.heightPoly l) := by
    simp [CellLayout.extraValue, CellLayout.sideTest, CellLayout.gradModeOf, hK, hn0]
    rfl
  rw [hext]
  by_cases hσ : σ = 0
  · simp only [hσ, if_true] at hflux ⊢
    rw [ev_strain_sum L x n0 1 1 l hl, ev_strain_sum L x n0 0 0 l hl]
    simp only [CellLayout.gradModeOf, hn0]
    exact hbase L hB hK i l hi _ _ (hint 1 1) (hint 0 0) _ hflux
  · simp only [hσ, if_false] at hflux ⊢
    rw [ev_negstrain_sum L x n0 0 1 l hl, ev_strain_sum L x n0 1 0 l hl]
    simp only [CellLayout.gradModeOf, hn0]
    refine hbase L hB hK i l hi _ _ ?_ (hint 1 0) _ hflux
    simpa [mul_neg] using (hint 0 1).neg

open Internal.RelStream in
theorem localRelStream_of (hI : LocalModeStripIntegrableStatement) (hF : LocalCylinderFluxStatement) :
    LocalRelStreamStatement := by
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

open Internal.CylinderFlux in
theorem localRadialFlux_of (hT : LocalStripTraceStatement) : LocalRadialFluxStatement := by
  intro m v G H hs R o z₁ z₂ hR0 ho hoR hz
  obtain ⟨T, hTr⟩ := hT m v G H hs z₁ z₂ hz
  have hne : R - o ≠ 0 := sub_ne_zero.2 (Ne.symm hoR)
  have hα1 : 1 / (R - o) * R + -o / (R - o) = 1 := by field_simp; ring
  have hα0 : 1 / (R - o) * o + -o / (R - o) = 0 := by ring
  have hrhs : (∫ p in Icc 0 R ×ˢ Icc z₁ z₂,
      (modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p)) = (R : ℂ) * T R := by
    have h0 := hTr 0 R le_rfl hR0 1 0
    simp only [Complex.ofReal_one, one_mul, add_zero, mul_zero, Complex.ofReal_zero, zero_mul,
      sub_zero] at h0
    exact h0
  rw [hrhs]
  rcases lt_or_gt_of_ne hoR with h | h
  · simp only [radialStripMoment, edgeSign, if_pos h, min_eq_right h.le, max_eq_left h.le, one_mul]
    rw [strip_eq, hTr o R ho h, hα1, hα0]
    simp
  · simp only [radialStripMoment, edgeSign, if_neg (not_lt.mpr h.le), min_eq_left h.le,
      max_eq_right h.le]
    rw [strip_eq, hTr R o hR0.le h, hα1, hα0]
    simp

open Internal.CylinderFlux in
theorem localModeTrace : LocalModeTraceStatement := by
  intro m v G H hs n
  filter_upwards [slice_aesm hs.measurable_gradient, slice_lint hs.gradient_two,
    slice_ae hs.divergence] with p hpA hpL hpP hpos
  have hint := fun a : Fin 3 => slice_int m n a a p (hpA hpos) (hpL hpos)
  simp_rw [LowEntry.Internal.gradMode_eq]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun a _ => hint a)]
  have h0 : ∫ θ in Ioo (-Real.pi) Real.pi,
      ∑ a : Fin 3, LowEntry.Internal.gradKernel m n a a θ (G (cylPoint p.1 θ p.2)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hpP hpos] with θ hθ
    simp only [LowEntry.Internal.gradKernel, ← Finset.mul_sum]
    have hs3 : ∑ a : Fin 3, frameMat θ (G (cylPoint p.1 θ p.2)) a a = 0 := by
      simp_rw [Internal.RelTrace.frameMat_diag]
      rw [Internal.RelTrace.diag_sum]
      simpa only [Internal.RelTrace.ent] using hθ
    have hs4 : ∑ a : Fin 3, ((frameMat θ (G (cylPoint p.1 θ p.2)) a a : ℝ) : ℂ) = 0 := by
      exact_mod_cast hs3
    rw [Pi.zero_apply, hs4, mul_zero]
  rw [h0, mul_zero]

open Internal.CylinderFlux in
theorem localCylinderFlux_of (hS : LocalModeStripIntegrableStatement) (hA : LocalAngularModeStatement)
    (hST : LocalStripTraceStatement) : LocalCylinderFluxStatement := by
  have hT : LocalModeTraceStatement := localModeTrace
  have hR : LocalRadialFluxStatement := localRadialFlux_of hST
  intro m v G H hs R o z₁ z₂ hR0 ho hoR hz
  obtain ⟨hv, hg⟩ := hS m v G H hs 0 R z₁ z₂
  have hD := heightDiff R z₁ z₂ hz _ _ (hv 2) (hg 2 2)
  have hae : ∀ᵐ p ∂(volume.restrict (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂)),
      (p.1 : ℂ) * gradMode m 0 G 2 2 p = -(modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p) := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc),
      ae_restrict_of_ae (hA m v G H hs 0), ae_restrict_of_ae (hT m v G H hs 0),
      ae_restrict_of_ae axis_ae] with p hpD hAp hTp hp0
    have hpos : 0 < p.1 := lt_of_le_of_ne hpD.1.1 (Ne.symm hp0)
    obtain ⟨-, h11, -⟩ := hAp hpos
    have az : azimuth m 0 = 0 := by simp [azimuth]
    rw [az] at h11
    simp only [Complex.ofReal_zero, zero_mul, zero_add] at h11
    have hTp := hTp hpos
    rw [Fin.sum_univ_three] at hTp
    linear_combination (p.1 : ℂ) * hTp - h11
  have hI : (∫ p in Icc (0 : ℝ) R ×ˢ Icc z₁ z₂, (p.1 : ℂ) * gradMode m 0 G 2 2 p)
      = -∫ p in Icc (0 : ℝ) R ×ˢ Icc z₁ z₂,
          (modeVec m 0 v p.1 p.2 0 + (p.1 : ℂ) * gradMode m 0 G 0 0 p) := by
    rw [integral_congr_ae hae, integral_neg]
  rw [add_sub_assoc, hD, hI, hR m v G H hs R o z₁ z₂ hR0 ho hoR hz, add_neg_cancel]

theorem localStripTrace_of (hS : LocalModeStripIntegrableStatement) : LocalStripTraceStatement := by
  intro m v G H hs z₁ z₂ hz
  exact Internal.StripTrace.st_core (F := fun p => modeVec m 0 v p.1 p.2 0) (dF := gradMode m 0 G 0 0)
    (fun R => (hS m v G H hs 0 R z₁ z₂).1 0)
    (fun R => (hS m v G H hs 0 R z₁ z₂).2 0 0)
    (fun N hN ψ hψ h0 hN' => (CellFormula.modeRadialParts m v G hs.measurable_velocity hs.velocity_six
      hs.measurable_gradient hs.gradient_two hs.weak_gradient 0 0 0 N z₁ z₂ le_rfl hN hz).2 ψ
        (fun _ => 1) hψ continuous_const h0 hN')

open RelSideSplit.Internal in
private theorem localExtraSplit (hI : LocalModeRectIntegrableStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox)
    (S : CellScalars) (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (x : FieldTuple k)
    (hx : IsLocalAdmissible x) (n : L.modes) (e : Fin 4) (a : Fin 3) (d : Fin (L.degCoef + 1))
    (hdeg : ¬ (e.val = 0 ∧ L.box.r₁ = 0) ∧ (if e.val < 2 then d.val ≤ L.degSide
      else if L.box.r₁ = 0 then d.val ≤ L.degSide else d.val ≤ L.degSide + 1)) :
    L.trueData x (CellDatum.extraVelocity n e a d) = ∑ s ∈ L.sideSegments e, ∑ d' : Fin (L.degSide + 2),
      ((L.segmentTestPair s (L.sideTest e d) d' : ℝ) : ℂ) * L.trueData x (CellDatum.sideVelocity n s a d') := by
  have hb := hL.box_eq
  subst hb
  simp only [CellLayout.trueData, CellDatum.extraVelocity, CellDatum.sideVelocity, Sum.elim_inr, Sum.elim_inl]
  have hbox := hL.box_valid
  have hr12 : L.box.r₁ ≤ L.box.r₂ := hbox.r_order.2.le
  have hz12 : L.box.z₁ ≤ L.box.z₂ := hbox.z_order.2.le
  obtain ⟨hF, hF0⟩ := hI c L.box S B L hL x hx n a 0
  obtain ⟨-, hF2⟩ := hI c L.box S B L hL x hx n a 2
  have hF' : IntegrableOn (L.velMode n x a) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := hF
  have hF0' : IntegrableOn (L.gradModeOf n x a 0) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := hF0
  have hF2' : IntegrableOn (L.gradModeOf n x a 2) (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := hF2
  have hK : IsCompact (Icc L.box.r₁ L.box.r₂ ×ˢ Icc L.box.z₁ L.box.z₂) := isCompact_Icc.prod isCompact_Icc
  have hlead : ∀ s, ∀ d, (L.segment s).testCoef d d ≠ 0 := fun s => (hL.segment_valid s).test_leading
  have he4 : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨ e.val = 3 := by omega
  rcases he4 with he | he | he | he
  · have hr1 : L.box.r₁ ≠ 0 := fun h => hdeg.1 ⟨he, h⟩
    have hd : d.val ≤ L.degSide := by
      have := hdeg.2
      rwa [if_pos (by omega)] at this
    rw [CellLayout.extraValue, if_pos he]
    refine radial_side L _ L.box.r₁ L.box.r₂ L.box.z₁ L.box.z₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_lo L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = true := h1.2 (by omega)
      obtain ⟨hz1, hz2, hot⟩ := seg_radial hL s hr
      rw [if_pos he] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun _ => hr1) u (by rw [if_pos (by omega)]; exact hu)
    · rw [min_eq_left hr12, max_eq_right hr12]
      exact (hF'.const_mul _).add (hF0'.continuousOn_mul (by fun_prop) hK)
  · have hd : d.val ≤ L.degSide := by
      have := hdeg.2
      rwa [if_pos (by omega)] at this
    rw [CellLayout.extraValue, if_neg (by omega), if_pos he]
    refine radial_side L _ L.box.r₂ L.box.r₁ L.box.z₁ L.box.z₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_lo L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = true := h1.2 (by omega)
      obtain ⟨hz1, hz2, hot⟩ := seg_radial hL s hr
      rw [if_neg (by omega), if_pos he] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun h => absurd h (by omega)) u (by rw [if_pos (by omega)]; exact hu)
    · rw [min_eq_right hr12, max_eq_left hr12]
      exact (hF'.const_mul _).add (hF0'.continuousOn_mul (by fun_prop) hK)
  · have hd := hdeg.2
    rw [if_neg (by omega)] at hd
    rw [CellLayout.extraValue, if_neg (by omega), if_neg (by omega), if_pos he]
    refine height_side L _ L.box.z₁ L.box.z₂ L.box.r₁ L.box.r₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_hi L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = false := Bool.eq_false_iff.2 (fun h => absurd (h1.1 h) (by omega))
      obtain ⟨hz1, hz2, hot⟩ := seg_height hL s hr
      rw [if_neg (by omega), if_neg (by omega), if_pos he] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun h => absurd h (by omega)) u (by rw [if_neg (by omega)]; exact hu)
    · rw [min_eq_left hz12, max_eq_right hz12]
      exact (hF'.const_mul _).add (hF2'.continuousOn_mul (by fun_prop) hK)
  · have hd := hdeg.2
    rw [if_neg (by omega)] at hd
    rw [CellLayout.extraValue, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    refine height_side L _ L.box.z₂ L.box.z₁ L.box.r₁ L.box.r₂ (fun s hs => ?_) (fun u hu => ?_)
      (hL.sideSegments_disjoint e) hL.segment_orthonormal _ (sideTest_cont L e d)
      (fun s _ => mem_hi L _ (hlead s) e (by omega) d hd) _ _ _ ?_
    · obtain ⟨h1, h2⟩ := hL.sideSegments_spec e s hs
      have hr : (L.segment s).radial = false := Bool.eq_false_iff.2 (fun h => absurd (h1.1 h) (by omega))
      obtain ⟨hz1, hz2, hot⟩ := seg_height hL s hr
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h2
      exact ⟨hr, h2, by rw [hot, h2]; ring, hz1, hz2⟩
    · exact hL.sideSegments_cover e (fun h => absurd h (by omega)) u (by rw [if_neg (by omega)]; exact hu)
    · rw [min_eq_right hz12, max_eq_left hz12]
      exact (hF'.const_mul _).add (hF2'.continuousOn_mul (by fun_prop) hK)

open RelSideSplit.Internal in
theorem localRelSideSplit_of (hI : LocalModeRectIntegrableStatement) : LocalRelSideSplitStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, e, a, d⟩ := ρ
  simp only [CellLayout.relationRow, Sum.elim_inr]
  by_cases hdeg : ¬ (e.val = 0 ∧ L.box.r₁ = 0) ∧ (if e.val < 2 then d.val ≤ L.degSide
      else if L.box.r₁ = 0 then d.val ≤ L.degSide else d.val ≤ L.degSide + 1)
  · rw [if_pos hdeg, RelSideSplit.Internal.pair_row, sub_eq_zero]
    exact localExtraSplit hI c K S B L hL x hx n e a d hdeg
  · rw [if_neg hdeg]
    simp

end LocalField

end CertCell

end Breakdown
