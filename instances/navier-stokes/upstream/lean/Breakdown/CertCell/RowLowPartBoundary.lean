import Breakdown.CertCell.RowLowPartPressure

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

def fluxConj (K : CellBox) (φ : Fin 3 → CellPoly) : ℂ :=
  (K.r₂ : ℂ) * (∫ z in Icc K.z₁ K.z₂, (starRingEnd ℂ) ((φ 0).eval K (K.r₂, z)))
    - (K.r₁ : ℂ) * (∫ z in Icc K.z₁ K.z₂, (starRingEnd ℂ) ((φ 0).eval K (K.r₁, z)))
    + (∫ r in Icc K.r₁ K.r₂, (r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₂)))
    - (∫ r in Icc K.r₁ K.r₂, (r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₁)))

theorem rect_const_fst {K : CellBox} (hK : IsCellBox K) {w : ℝ → ℂ} (hw : Continuous w) :
    ∫ p in K.rect, w p.2 = ((K.r₂ - K.r₁ : ℝ) : ℂ) * ∫ z in Icc K.z₁ K.z₂, w z := by
  rw [CellBox.rect, rect_iter_snd (f := fun p : ℝ × ℝ => w p.2) (cont_int_rect (hw.comp continuous_snd) _ _ _ _),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
  simp only
  rw [integral_const]
  simp [Measure.real, Real.volume_Icc, hK.r_order.2.le, Complex.real_smul]

theorem rect_const_snd {K : CellBox} (hK : IsCellBox K) {w : ℝ → ℂ} (hw : Continuous w) :
    ∫ p in K.rect, (p.1 : ℂ) * w p.1 = ((K.z₂ - K.z₁ : ℝ) : ℂ) * ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * w r := by
  rw [CellBox.rect, rect_iter_fst (f := fun p : ℝ × ℝ => (p.1 : ℂ) * w p.1)
    (cont_int_rect ((Complex.continuous_ofReal.comp continuous_fst).mul (hw.comp continuous_fst)) _ _ _ _),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun r _ => ?_)
  simp only
  rw [integral_const]
  simp [Measure.real, Real.volume_Icc, hK.z_order.2.le, Complex.real_smul]

theorem radial_combine {K : CellBox} {c o : ℝ} {Fc Fs dFc dFs P dP : ℝ × ℝ → ℂ} {C0 : ℂ}
    (ic : IntegrableOn (radialIntegrand c o Fc dFc) K.rect) (is : IntegrableOn (radialIntegrand c o Fs dFs) K.rect)
    (ip : IntegrableOn (radialIntegrand c o P dP) K.rect)
    (hP : ∀ᵐ p ∂(volume.restrict K.rect), Fc p + Complex.I * Fs p = P p - C0)
    (hd : ∀ᵐ p ∂(volume.restrict K.rect), dFc p + Complex.I * dFs p = dP p) {w : ℝ → ℂ} (hw : Continuous w) :
    (∫ p in K.rect, radialIntegrand c o Fc dFc p * w p.2) + Complex.I * ∫ p in K.rect, radialIntegrand c o Fs dFs p * w p.2
      = (∫ p in K.rect, radialIntegrand c o P dP p * w p.2)
        - C0 * (((1 / (c - o) : ℝ)) : ℂ) * ∫ p in K.rect, w p.2 := by
  have hwc : ContinuousOn (fun p : ℝ × ℝ => w p.2) K.rect := (hw.comp continuous_snd).continuousOn
  have i1 := ic.mul_continuousOn hwc (rect_compact K)
  have i2 := is.mul_continuousOn hwc (rect_compact K)
  have i3 := ip.mul_continuousOn hwc (rect_compact K)
  have i4 : IntegrableOn (fun p : ℝ × ℝ => w p.2) K.rect := hwc.integrableOn_compact (rect_compact K)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _), ← integral_const_mul, ← integral_sub i3 (i4.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hP, hd] with p h1 h2
  unfold radialIntegrand
  have e1 : P p = Fc p + Complex.I * Fs p + C0 := by rw [h1]; ring
  rw [e1, ← h2]
  ring

theorem height_combine {K : CellBox} {c o : ℝ} {Fc Fs dFc dFs P dP : ℝ × ℝ → ℂ} {C0 : ℂ}
    (ic : IntegrableOn (fun p => heightIntegrand c o Fc dFc p * (p.1 : ℂ)) K.rect)
    (is : IntegrableOn (fun p => heightIntegrand c o Fs dFs p * (p.1 : ℂ)) K.rect)
    (ip : IntegrableOn (fun p => heightIntegrand c o P dP p * (p.1 : ℂ)) K.rect)
    (hP : ∀ᵐ p ∂(volume.restrict K.rect), Fc p + Complex.I * Fs p = P p - C0)
    (hd : ∀ᵐ p ∂(volume.restrict K.rect), dFc p + Complex.I * dFs p = dP p) {w : ℝ → ℂ} (hw : Continuous w) :
    (∫ p in K.rect, heightIntegrand c o Fc dFc p * (p.1 : ℂ) * w p.1)
        + Complex.I * ∫ p in K.rect, heightIntegrand c o Fs dFs p * (p.1 : ℂ) * w p.1
      = (∫ p in K.rect, heightIntegrand c o P dP p * (p.1 : ℂ) * w p.1)
        - C0 * (((1 / (c - o) : ℝ)) : ℂ) * ∫ p in K.rect, (p.1 : ℂ) * w p.1 := by
  have hwc : ContinuousOn (fun p : ℝ × ℝ => w p.1) K.rect := (hw.comp continuous_fst).continuousOn
  have i1 := ic.mul_continuousOn hwc (rect_compact K)
  have i2 := is.mul_continuousOn hwc (rect_compact K)
  have i3 := ip.mul_continuousOn hwc (rect_compact K)
  have i4 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * w p.1) K.rect :=
    ((Complex.continuous_ofReal.comp continuous_fst).mul (hw.comp continuous_fst)).continuousOn.integrableOn_compact
      (rect_compact K)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _), ← integral_const_mul, ← integral_sub i3 (i4.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hP, hd] with p h1 h2
  unfold heightIntegrand
  have e1 : P p = Fc p + Complex.I * Fs p + C0 := by rw [h1]; ring
  rw [e1, ← h2]
  ring

section Layout

variable {k N' : ℕ} {c0 : FracCellData k N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

theorem radial_pres_side_value (hK : IsCellBox K) {c o : ℝ} (hmin : min c o = K.r₁) (hmax : max c o = K.r₂)
    (hco : c ≠ o) (ho : c ≠ 0 → o = 0 ∨ 0 < K.r₁)
    {Fc Fs dFc dFs P dP : ℝ × ℝ → ℂ} {C0 : ℂ}
    (ic : IntegrableOn Fc K.rect) (is : IntegrableOn Fs K.rect) (ip : IntegrableOn P K.rect)
    (ic' : IntegrableOn (fun p => (p.1 : ℂ) * dFc p) K.rect) (is' : IntegrableOn (fun p => (p.1 : ℂ) * dFs p) K.rect)
    (ip' : IntegrableOn (fun p => (p.1 : ℂ) * dP p) K.rect)
    (hP : ∀ᵐ p ∂(volume.restrict K.rect), Fc p + Complex.I * Fs p = P p - C0)
    (hd : ∀ᵐ p ∂(volume.restrict K.rect), dFc p + Complex.I * dFs p = dP p) {w : ℝ → ℂ} (hw : Continuous w) :
    (c : ℂ) * (∫ p in K.rect, radialIntegrand c o Fc dFc p * w p.2)
        + Complex.I * ((c : ℂ) * ∫ p in K.rect, radialIntegrand c o Fs dFs p * w p.2)
      = edgeSign c o * (∫ z in Icc K.z₁ K.z₂, (c : ℂ) * radialStripTrace c o P dP z * w z)
        - C0 * edgeSign c o * ((c : ℂ) * ∫ z in Icc K.z₁ K.z₂, w z) := by
  by_cases hc0 : c = 0
  · simp [hc0]
  have h1 := radial_combine (radialIntegrand_int (c := c) hK (ho hc0) ic ic') (radialIntegrand_int (c := c) hK (ho hc0) is is')
    (radialIntegrand_int (c := c) hK (ho hc0) ip ip') hP hd hw (C0 := C0)
  have h2 := (trace_radial hmin hmax (radialIntegrand_int (c := c) hK (ho hc0) ip ip') hw).2
  have h3 := rect_const_fst hK hw
  have hes : (((1 / (c - o) : ℝ)) : ℂ) * ((K.r₂ - K.r₁ : ℝ) : ℂ) = edgeSign c o := by
    rw [← hmin, ← hmax]
    have hco' : (c - o) ≠ 0 := sub_ne_zero.2 hco
    unfold edgeSign
    rcases lt_or_gt_of_ne hco with h | h
    · rw [min_eq_left h.le, max_eq_right h.le, if_neg (not_lt.2 h.le), ← Complex.ofReal_mul]
      have : 1 / (c - o) * (o - c) = (-1 : ℝ) := by
        rw [show o - c = -(c - o) by ring, mul_neg, one_div_mul_cancel hco']
      rw [this]
      simp
    · rw [min_eq_right h.le, max_eq_left h.le, if_pos h, ← Complex.ofReal_mul, one_div_mul_cancel hco']
      simp
  have e2 : ∫ z in Icc K.z₁ K.z₂, (c : ℂ) * radialStripTrace c o P dP z * w z =
      (c : ℂ) * ∫ z in Icc K.z₁ K.z₂, radialStripTrace c o P dP z * w z := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => by ring)
  rw [e2, h2]
  have hsq := edgeSign_sq c o
  have : (c : ℂ) * (∫ p in K.rect, radialIntegrand c o Fc dFc p * w p.2)
        + Complex.I * ((c : ℂ) * ∫ p in K.rect, radialIntegrand c o Fs dFs p * w p.2)
      = (c : ℂ) * ((∫ p in K.rect, radialIntegrand c o Fc dFc p * w p.2)
        + Complex.I * ∫ p in K.rect, radialIntegrand c o Fs dFs p * w p.2) := by ring
  rw [this, h1, h3]
  linear_combination (-(c : ℂ) * (∫ p in K.rect, radialIntegrand c o P dP p * w p.2)) * hsq
    + (-(c : ℂ) * C0 * ∫ z in Icc K.z₁ K.z₂, w z) * hes

theorem edge_factor {c o x y : ℝ} (hmin : min c o = x) (hmax : max c o = y) (hco : c ≠ o) :
    (((1 / (c - o) : ℝ)) : ℂ) * ((y - x : ℝ) : ℂ) = edgeSign c o := by
  rw [← hmin, ← hmax]
  have hco' : (c - o) ≠ 0 := sub_ne_zero.2 hco
  unfold edgeSign
  rcases lt_or_gt_of_ne hco with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, if_neg (not_lt.2 h.le), ← Complex.ofReal_mul]
    have : 1 / (c - o) * (o - c) = (-1 : ℝ) := by
      rw [show o - c = -(c - o) by ring, mul_neg, one_div_mul_cancel hco']
    rw [this]
    simp
  · rw [min_eq_right h.le, max_eq_left h.le, if_pos h, ← Complex.ofReal_mul, one_div_mul_cancel hco']
    simp

theorem height_pres_side_value (hK : IsCellBox K) {c o : ℝ} (hmin : min c o = K.z₁) (hmax : max c o = K.z₂)
    (hco : c ≠ o) {Fc Fs dFc dFs P dP : ℝ × ℝ → ℂ} {C0 : ℂ}
    (ic : IntegrableOn (fun p => (p.1 : ℂ) * Fc p) K.rect) (is : IntegrableOn (fun p => (p.1 : ℂ) * Fs p) K.rect)
    (ip : IntegrableOn (fun p => (p.1 : ℂ) * P p) K.rect)
    (ic' : IntegrableOn (fun p => (p.1 : ℂ) * dFc p) K.rect) (is' : IntegrableOn (fun p => (p.1 : ℂ) * dFs p) K.rect)
    (ip' : IntegrableOn (fun p => (p.1 : ℂ) * dP p) K.rect)
    (hP : ∀ᵐ p ∂(volume.restrict K.rect), Fc p + Complex.I * Fs p = P p - C0)
    (hd : ∀ᵐ p ∂(volume.restrict K.rect), dFc p + Complex.I * dFs p = dP p) {w : ℝ → ℂ} (hw : Continuous w) :
    (∫ p in K.rect, heightIntegrand c o Fc dFc p * (p.1 : ℂ) * w p.1)
        + Complex.I * (∫ p in K.rect, heightIntegrand c o Fs dFs p * (p.1 : ℂ) * w p.1)
      = edgeSign c o * (∫ r in Icc K.r₁ K.r₂, (r : ℂ) * heightStripTrace c o P dP r * w r)
        - C0 * edgeSign c o * ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * w r := by
  have h1 := height_combine (heightIntegrand_w_int ic ic') (heightIntegrand_w_int is is')
    (heightIntegrand_w_int ip ip') hP hd hw (C0 := C0) (c := c) (o := o)
  have h2 := (trace_height hmin hmax (heightIntegrand_w_int ip ip') hw).2
  have h3 := rect_const_snd hK hw
  have hes := edge_factor hmin hmax hco
  have hsq := edgeSign_sq c o
  rw [h1, h2, h3]
  linear_combination (-(∫ p in K.rect, heightIntegrand c o P dP p * (p.1 : ℂ) * w p.1)) * hsq
    + (-C0 * ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * w r) * hes

end Layout

section Layout

variable {k N' : ℕ} {c0 : FracCellData k N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

theorem sum_presFiber (K : CellBox) (L : CellLayout) (F : Fin L.presCount → ℂ) :
    ∑ s, F s = ∑ e : Fin 4, ∑ s ∈ presFiber K L e, F s :=
  (Finset.sum_fiberwise Finset.univ (fun s => segSide K (L.presSegment s)) F).symm

theorem w_int_fst {K : CellBox} {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F K.rect) :
    IntegrableOn (fun p => (p.1 : ℂ) * F p) K.rect :=
  hF.continuousOn_mul (Complex.continuous_ofReal.comp continuous_fst).continuousOn (rect_compact K)

theorem pres_one (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L)
    (hps : IsPressureSegmentation L) (φ : Fin 3 → CellPoly)
    (hφ0 : IsBivariatePoly (L.degSide + 1) L.degSide (fun p => (φ 0).eval L.box p))
    (hφ2 : IsBivariatePoly L.degSide (L.degSide + 1) (fun p => (φ 2).eval L.box p))
    (F dF0 dF2 : ℝ × ℝ → ℂ) (i : IntegrableOn F L.box.rect) (i0 : IntegrableOn (fun p => (p.1 : ℂ) * dF0 p) L.box.rect)
    (i2 : IntegrableOn (fun p => (p.1 : ℂ) * dF2 p) L.box.rect) :
    ∑ s, ∑ d : Fin L.degSide, sidePresRow L φ s d * (L.presSegment s).moment true F dF0 dF2 d
      = (L.box.r₁ : ℂ) * (∫ p in L.box.rect, radialIntegrand L.box.r₁ L.box.r₂ F dF0 p *
            (starRingEnd ℂ) ((φ 0).eval L.box (L.box.r₁, p.2)))
        + (L.box.r₂ : ℂ) * (∫ p in L.box.rect, radialIntegrand L.box.r₂ L.box.r₁ F dF0 p *
            (starRingEnd ℂ) ((φ 0).eval L.box (L.box.r₂, p.2)))
        + (∫ p in L.box.rect, heightIntegrand L.box.z₁ L.box.z₂ F dF2 p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ 2).eval L.box (p.1, L.box.z₁)))
        + (∫ p in L.box.rect, heightIntegrand L.box.z₂ L.box.z₁ F dF2 p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ 2).eval L.box (p.1, L.box.z₂))) := by
  have hK := hL.box_valid
  rw [hL.box_eq] at hφ0 hφ2 i i0 i2 ⊢
  have o0 : K.r₁ + K.r₂ - K.r₁ = K.r₂ := by ring
  have o1 : K.r₁ + K.r₂ - K.r₂ = K.r₁ := by ring
  have o2 : K.z₁ + K.z₂ - K.z₁ = K.z₂ := by ring
  have o3 : K.z₁ + K.z₂ - K.z₂ = K.z₁ := by ring
  rw [sum_presFiber K L, Fin.sum_univ_four]
  have hb := hL.box_eq
  have e0 := pres_radial_side hexp hL hps (e := 0) (by decide) (c := K.r₁) (by simp [hb]) φ (by rw [hb]; exact hφ0)
    F dF0 dF2 (fun hc0 => by
      rw [hb]; exact radialIntegrand_int hK (Or.inr (lt_of_le_of_ne hK.r_order.1 (Ne.symm hc0))) i i0)
  have e1 := pres_radial_side hexp hL hps (e := 1) (by decide) (c := K.r₂) (by simp [hb]) φ (by rw [hb]; exact hφ0)
    F dF0 dF2 (fun _ => by
      rw [hb]
      refine radialIntegrand_int hK ?_ i i0
      rw [o1]
      rcases eq_or_lt_of_le hK.r_order.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h)
  have e2 := pres_height_side hexp hL hps (e := 2) (by decide) (c := K.z₁) (by simp [hb]) φ (by rw [hb]; exact hφ2)
    F dF2 dF0 (by rw [hb]; exact heightIntegrand_w_int (w_int_fst i) i2)
  have e3 := pres_height_side hexp hL hps (e := 3) (by decide) (c := K.z₂) (by simp [hb]) φ (by rw [hb]; exact hφ2)
    F dF2 dF0 (by rw [hb]; exact heightIntegrand_w_int (w_int_fst i) i2)
  rw [hb] at e0 e1 e2 e3
  rw [o0] at e0
  rw [o1] at e1
  rw [o2] at e2
  rw [o3] at e3
  rw [e0, e1, e2, e3]

theorem pres_block (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L)
    (hps : IsPressureSegmentation L) (φ : Fin 3 → CellPoly)
    (hφ0 : IsBivariatePoly (L.degSide + 1) L.degSide (fun p => (φ 0).eval K p))
    (hφ2 : IsBivariatePoly L.degSide (L.degSide + 1) (fun p => (φ 2).eval K p))
    (Fc dFc0 dFc2 Fs dFs0 dFs2 P dP0 dP2 : ℝ × ℝ → ℂ) (C0 : ℂ) (R : RowProfile)
    (hRr : ∀ e z, R.radialPres e z = radialStripTrace (sideRadius K e) (otherRadius K e) P dP0 z)
    (hRh : ∀ e r, R.heightPres e r = heightStripTrace (sideHeight K e) (otherHeight K e) P dP2 r)
    (ic : IntegrableOn Fc K.rect) (is : IntegrableOn Fs K.rect) (ip : IntegrableOn P K.rect)
    (ic0 : IntegrableOn (fun p => (p.1 : ℂ) * dFc0 p) K.rect) (is0 : IntegrableOn (fun p => (p.1 : ℂ) * dFs0 p) K.rect)
    (ip0 : IntegrableOn (fun p => (p.1 : ℂ) * dP0 p) K.rect)
    (ic2 : IntegrableOn (fun p => (p.1 : ℂ) * dFc2 p) K.rect) (is2 : IntegrableOn (fun p => (p.1 : ℂ) * dFs2 p) K.rect)
    (ip2 : IntegrableOn (fun p => (p.1 : ℂ) * dP2 p) K.rect)
    (hP : ∀ᵐ p ∂(volume.restrict K.rect), Fc p + Complex.I * Fs p = P p - C0)
    (hd0 : ∀ᵐ p ∂(volume.restrict K.rect), dFc0 p + Complex.I * dFs0 p = dP0 p)
    (hd2 : ∀ᵐ p ∂(volume.restrict K.rect), dFc2 p + Complex.I * dFs2 p = dP2 p)
    (hC : C0 * fluxConj K φ = 0) :
    ∑ s, ∑ d : Fin L.degSide, sidePresRow L φ s d *
        ((L.presSegment s).moment true Fc dFc0 dFc2 d + Complex.I * (L.presSegment s).moment true Fs dFs0 dFs2 d)
      = rowBoundaryPres K R φ := by
  have hK := hL.box_valid
  have hr := hK.r_order.2
  have hz := hK.z_order.2
  have hb := hL.box_eq
  have hsplit : ∑ s, ∑ d : Fin L.degSide, sidePresRow L φ s d *
      ((L.presSegment s).moment true Fc dFc0 dFc2 d + Complex.I * (L.presSegment s).moment true Fs dFs0 dFs2 d)
      = (∑ s, ∑ d : Fin L.degSide, sidePresRow L φ s d * (L.presSegment s).moment true Fc dFc0 dFc2 d)
        + Complex.I * ∑ s, ∑ d : Fin L.degSide, sidePresRow L φ s d * (L.presSegment s).moment true Fs dFs0 dFs2 d := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun d _ => by ring))
  rw [hsplit, pres_one hexp hL hps φ (by rw [hb]; exact hφ0) (by rw [hb]; exact hφ2) Fc dFc0 dFc2 (by rw [hb]; exact ic)
      (by rw [hb]; exact ic0) (by rw [hb]; exact ic2),
    pres_one hexp hL hps φ (by rw [hb]; exact hφ0) (by rw [hb]; exact hφ2) Fs dFs0 dFs2 (by rw [hb]; exact is)
      (by rw [hb]; exact is0) (by rw [hb]; exact is2)]
  rw [hb]
  have hw0 : ∀ c : ℝ, Continuous (fun z : ℝ => (starRingEnd ℂ) ((φ 0).eval K (c, z))) := fun c =>
    Complex.continuous_conj.comp ((bi_contDiff hφ0).continuous.comp (continuous_const.prodMk continuous_id))
  have hw2 : ∀ c : ℝ, Continuous (fun r : ℝ => (starRingEnd ℂ) ((φ 2).eval K (r, c))) := fun c =>
    Complex.continuous_conj.comp ((bi_contDiff hφ2).continuous.comp (continuous_id.prodMk continuous_const))
  have m0 := minmax_of hr (Or.inl rfl : K.r₁ = K.r₁ ∨ K.r₁ = K.r₂)
  have m1 := minmax_of hr (Or.inr rfl : K.r₂ = K.r₁ ∨ K.r₂ = K.r₂)
  have m2 := minmax_of hz (Or.inl rfl : K.z₁ = K.z₁ ∨ K.z₁ = K.z₂)
  have m3 := minmax_of hz (Or.inr rfl : K.z₂ = K.z₁ ∨ K.z₂ = K.z₂)
  have o0 : K.r₁ + K.r₂ - K.r₁ = K.r₂ := by ring
  have o1 : K.r₁ + K.r₂ - K.r₂ = K.r₁ := by ring
  have o2 : K.z₁ + K.z₂ - K.z₁ = K.z₂ := by ring
  have o3 : K.z₁ + K.z₂ - K.z₂ = K.z₁ := by ring
  rw [o0] at m0
  rw [o1] at m1
  rw [o2] at m2
  rw [o3] at m3
  have v0 := radial_pres_side_value hK m0.1 m0.2 hr.ne (fun hc0 => Or.inr (lt_of_le_of_ne hK.r_order.1 (Ne.symm hc0)))
    ic is ip ic0 is0 ip0 hP hd0 (hw0 K.r₁)
  have v1 := radial_pres_side_value hK m1.1 m1.2 hr.ne' (fun _ => by
      rcases eq_or_lt_of_le hK.r_order.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h)
    ic is ip ic0 is0 ip0 hP hd0 (hw0 K.r₂)
  have v2 := height_pres_side_value hK m2.1 m2.2 hz.ne (w_int_fst ic) (w_int_fst is) (w_int_fst ip)
    ic2 is2 ip2 hP hd2 (hw2 K.z₁)
  have v3 := height_pres_side_value hK m3.1 m3.2 hz.ne' (w_int_fst ic) (w_int_fst is) (w_int_fst ip)
    ic2 is2 ip2 hP hd2 (hw2 K.z₂)
  unfold rowBoundaryPres
  rw [Fin.sum_univ_two]
  simp only [hRr, hRh, sideSign, sideRadius, otherRadius, sideHeight, otherHeight, Fin.isValue, if_true,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
  rw [(edgeSign_lt hr).1] at v0
  rw [(edgeSign_lt hr).2] at v1
  rw [(edgeSign_lt hz).1] at v2
  rw [(edgeSign_lt hz).2] at v3
  unfold fluxConj at hC
  linear_combination v0 + v1 + v2 + v3 - hC

end Layout

theorem flux_zero {K : CellBox} (hK : IsCellBox K) (φ : Fin 3 → CellPoly) {M N M' N' : ℕ}
    (hφ0 : IsBivariatePoly M N (fun p => (φ 0).eval K p)) (hφ2 : IsBivariatePoly M' N' (fun p => (φ 2).eval K p))
    (hsol : IsTestSolenoidal K 0 φ) : fluxConj K φ = 0 := by
  have hf0 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ) * (φ 0).eval K p) := bi_contDiff (bi_mul_fst hφ0)
  have hc2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (φ 2).eval K p) := bi_contDiff hφ2
  have hd2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * CellBox.heightDeriv (fun p => (φ 2).eval K p) p) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul (continuous_heightDeriv hc2)
  have I1 := rect_ftc_fst (continuous_radialDeriv hf0) (hasDerivAt_fst hf0) hK.r_order.2.le
    (c := K.z₁) (d := K.z₂)
  have I2 := rect_ftc_snd (F := fun p : ℝ × ℝ => (p.1 : ℂ) * (φ 2).eval K p) hd2
    (fun p => (hasDerivAt_snd hc2 p).const_mul (p.1 : ℂ)) hK.z_order.2.le (a := K.r₁) (b := K.r₂)
  have hsum : (∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂,
        CellBox.radialDeriv (fun p : ℝ × ℝ => (p.1 : ℂ) * (φ 0).eval K p) p)
      + (∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, (p.1 : ℂ) * CellBox.heightDeriv (fun p => (φ 2).eval K p) p) = 0 := by
    rw [← integral_add (cont_int_rect (continuous_radialDeriv hf0) _ _ _ _) (cont_int_rect hd2 _ _ _ _)]
    have h0 : ∀ p ∈ Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂,
        CellBox.radialDeriv (fun p : ℝ × ℝ => (p.1 : ℂ) * (φ 0).eval K p) p
          + (p.1 : ℂ) * CellBox.heightDeriv (fun p => (φ 2).eval K p) p = 0 := by
      intro p hp
      have h := hsol p hp
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
      exact h
    rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) h0]
    simp
  rw [I1, I2] at hsum
  have hcz : ∀ c : ℝ, Continuous (fun z : ℝ => (φ 0).eval K (c, z)) := fun c =>
    (bi_contDiff hφ0).continuous.comp (continuous_const.prodMk continuous_id)
  have hcr : ∀ c : ℝ, Continuous (fun r : ℝ => (r : ℂ) * (φ 2).eval K (r, c)) := fun c =>
    Complex.continuous_ofReal.mul (hc2.continuous.comp (continuous_id.prodMk continuous_const))
  simp only at hsum
  have j1 : IntegrableOn (fun z : ℝ => (K.r₂ : ℂ) * (φ 0).eval K (K.r₂, z)) (Icc K.z₁ K.z₂) :=
    (continuous_const.mul (hcz K.r₂)).integrableOn_Icc
  have j2 : IntegrableOn (fun z : ℝ => (K.r₁ : ℂ) * (φ 0).eval K (K.r₁, z)) (Icc K.z₁ K.z₂) :=
    (continuous_const.mul (hcz K.r₁)).integrableOn_Icc
  have j3 : IntegrableOn (fun r : ℝ => (r : ℂ) * (φ 2).eval K (r, K.z₂)) (Icc K.r₁ K.r₂) := (hcr K.z₂).integrableOn_Icc
  have j4 : IntegrableOn (fun r : ℝ => (r : ℂ) * (φ 2).eval K (r, K.z₁)) (Icc K.r₁ K.r₂) := (hcr K.z₁).integrableOn_Icc
  rw [integral_sub j1 j2, integral_sub j3 j4, integral_const_mul, integral_const_mul] at hsum
  unfold fluxConj
  have c1 : ∀ c : ℝ, ∫ z in Icc K.z₁ K.z₂, (starRingEnd ℂ) ((φ 0).eval K (c, z)) =
      (starRingEnd ℂ) (∫ z in Icc K.z₁ K.z₂, (φ 0).eval K (c, z)) := fun c => integral_conj
  have c2 : ∀ c : ℝ, ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, c)) =
      (starRingEnd ℂ) (∫ r in Icc K.r₁ K.r₂, (r : ℂ) * (φ 2).eval K (r, c)) := by
    intro c
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Icc (fun r _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
  rw [c1, c1, c2, c2]
  have := congrArg (starRingEnd ℂ) hsum
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_zero] at this
  linear_combination this

end Breakdown.CertCell.CellCalculus.RowLow.Internal
