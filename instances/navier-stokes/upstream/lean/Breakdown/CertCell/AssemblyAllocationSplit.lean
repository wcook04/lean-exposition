import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.FormNegativeFinite

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.AllocationSplitParts

theorem ofReal_abs_split (x : ℝ) : ENNReal.ofReal |x| = ENNReal.ofReal x + ENNReal.ofReal (-x) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]

theorem integrable_of_parts {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ofReal_abs_split]
  simp_rw [e]
  rw [lintegral_add_left' hf.aemeasurable.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨hp.lt_top, hn.lt_top⟩

theorem integral_eq_parts {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤) :
    ∫ x, f x ∂μ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal - (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal :=
  integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_parts hf hp hn)

theorem measurableSet_boxRect (B : CellBox) : MeasurableSet B.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem boxRect_ae_le (B : CellBox) (hB : IsCellBox B) : B.rect ≤ᵐ[volume] halfPlane := by
  rw [ae_le_set]
  refine measure_mono_null (t := ({0} ×ˢ univ) ∪ (univ ×ˢ {0})) ?_ ?_
  · rintro ⟨r, z⟩ ⟨⟨⟨hr, -⟩, ⟨hz, -⟩⟩, hn⟩
    have h0r : 0 ≤ r := hB.r_order.1.trans hr
    have h0z : 0 ≤ z := hB.z_order.1.trans hz
    by_cases hr0 : r = 0
    · exact Or.inl ⟨hr0, mem_univ _⟩
    by_cases hz0 : z = 0
    · exact Or.inr ⟨mem_univ _, hz0⟩
    exact absurd (show (r, z) ∈ halfPlane from
      ⟨lt_of_le_of_ne h0r (Ne.symm hr0), lt_of_le_of_ne h0z (Ne.symm hz0)⟩) hn
  · refine measure_union_null ?_ ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp

theorem tsum_allocation {β : Type*} (s : Finset β) (a b c d : β → ℝ≥0∞) (F O : β → ℝ)
    (ha : ∑' i, a i ≠ ⊤) (hb : ∑' i, b i ≠ ⊤) (hc : ∑' i, c i ≠ ⊤) (hd : ∑' i, d i ≠ ⊤)
    (hF : ∀ i, F i = (a i).toReal - (b i).toReal)
    (hin : ∀ i ∈ s, (c i).toReal - (d i).toReal = 0 ∧ O i = 0)
    (hout : ∀ i ∉ s, O i = F i - ((c i).toReal - (d i).toReal)) :
    (∑' i, a i).toReal - (∑' i, b i).toReal - (∑' i, c i).toReal + (∑' i, d i).toReal
      = ∑ i ∈ s, F i + ∑' i, O i := by
  classical
  have sa := ENNReal.summable_toReal ha
  have sb := ENNReal.summable_toReal hb
  have sc := ENNReal.summable_toReal hc
  have sd := ENNReal.summable_toReal hd
  have hFs : Summable F := (sa.sub sb).congr fun i => (hF i).symm
  have hYs := sc.sub sd
  have hIs : Summable (fun i => if i ∈ s then F i else 0) :=
    summable_of_ne_finset_zero (s := s) fun i hi => if_neg hi
  have hO : ∀ i, O i = F i - ((c i).toReal - (d i).toReal) - (if i ∈ s then F i else 0) := by
    intro i
    by_cases hi : i ∈ s
    · rw [if_pos hi, (hin i hi).2, (hin i hi).1]
      ring
    · rw [if_neg hi, hout i hi]
      ring
  have e1 : ∑' i, O i = ∑' i, F i - ∑' i, ((c i).toReal - (d i).toReal)
      - ∑' i, (if i ∈ s then F i else 0) := by
    rw [tsum_congr hO, (hFs.sub hYs).tsum_sub hIs, hFs.tsum_sub hYs]
  have e2 : ∑' i, (if i ∈ s then F i else 0) = ∑ i ∈ s, F i := by
    rw [tsum_eq_sum (s := s) fun i hi => if_neg hi]
    exact Finset.sum_congr rfl fun i hi => if_pos hi
  have e3 : ∑' i, F i = ∑' i, (a i).toReal - ∑' i, (b i).toReal := by
    rw [tsum_congr hF, sa.tsum_sub sb]
  have e4 : ∑' i, ((c i).toReal - (d i).toReal) = ∑' i, (c i).toReal - ∑' i, (d i).toReal :=
    sc.tsum_sub sd
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top ha),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hb),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hc),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hd)]
  linarith

theorem aemeasurable_gap {μ : Measure (ℝ × ℝ)} {st cc gc vc mg wg len xo x1 x0 : ℝ × ℝ → ℝ} (k : ℝ)
    (hst : AEMeasurable st μ) (hcc : AEMeasurable cc μ) (hgc : AEMeasurable gc μ) (hvc : AEMeasurable vc μ)
    (hmg : AEMeasurable mg μ) (hwg : AEMeasurable wg μ) (hlen : AEMeasurable len μ)
    (hxo : AEMeasurable xo μ) (hx1 : AEMeasurable x1 μ) (hx0 : AEMeasurable x0 μ) :
    AEMeasurable (fun p => (st p + cc p) * Real.sqrt (xo p) ^ 2
      + (k * wg p * len p / 2 + gc p) * Real.sqrt (x1 p) ^ 2
      + (k * wg p * (len p)⁻¹ / 2 + vc p) * Real.sqrt (x0 p) ^ 2
      + k * mg p * (Real.sqrt (x1 p) * Real.sqrt (x0 p))) μ := by
  have hs : ∀ {u : ℝ × ℝ → ℝ}, AEMeasurable u μ → AEMeasurable (fun p => Real.sqrt (u p)) μ :=
    fun h => Real.continuous_sqrt.measurable.comp_aemeasurable h
  have so := hs hxo
  have s1 := hs hx1
  have s0 := hs hx0
  refine (((hst.add hcc).mul (so.pow_const 2)).add ?_).add ?_ |>.add ?_
  · exact ((((aemeasurable_const.mul hwg).mul hlen).div_const 2).add hgc).mul (s1.pow_const 2)
  · exact ((((aemeasurable_const.mul hwg).mul hlen.inv).div_const 2).add hvc).mul (s0.pow_const 2)
  · exact (aemeasurable_const.mul hmg).mul (s1.mul s0)


theorem mean_split {S : Set (ℝ × ℝ)} (hS : ∀ᵐ p ∂(volume.restrict S), 0 < p.1) (s : ℝ × ℝ → ℝ → ℝ → ℝ)
    (hs : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ × ℝ => s z.1 z.2.1 z.2.2)
      ((volume.restrict S).prod
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))))
    (hP : ∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) * ENNReal.ofReal p.1 ≠ ⊤)
    (hN : ∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) * ENNReal.ofReal p.1 ≠ ⊤) :
    ∫ p in S, ((1 / (2 * Real.pi)) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), s p τ φ) * p.1
      = (∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
          ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) * ENNReal.ofReal p.1).toReal
        - (∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
          ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) * ENNReal.ofReal p.1).toReal := by
  set c : ℝ := 1 / (2 * Real.pi) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set ν : Measure (ℝ × ℝ) := (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))
    with hνdef
  set Sp : ℝ × ℝ → ℝ≥0∞ := fun p => ∫⁻ y, ENNReal.ofReal (s p y.1 y.2) ∂ν with hSp
  set Sn : ℝ × ℝ → ℝ≥0∞ := fun p => ∫⁻ y, ENNReal.ofReal (-s p y.1 y.2) ∂ν with hSn
  have hsec := hs.prodMk_left
  have hSpm : AEMeasurable Sp (volume.restrict S) := hs.aemeasurable.ennreal_ofReal.lintegral_prod_right'
  have hSnm : AEMeasurable Sn (volume.restrict S) := hs.aemeasurable.neg.ennreal_ofReal.lintegral_prod_right'
  have hit : ∀ᵐ p ∂(volume.restrict S),
      (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) = Sp p ∧
      (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) = Sn p := by
    filter_upwards [hsec] with p hp
    exact ⟨(lintegral_prod (fun y : ℝ × ℝ => ENNReal.ofReal (s p y.1 y.2)) hp.aemeasurable.ennreal_ofReal).symm,
      (lintegral_prod (fun y : ℝ × ℝ => ENNReal.ofReal (-s p y.1 y.2)) hp.aemeasurable.neg.ennreal_ofReal).symm⟩
  set A : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal c * Sp p * ENNReal.ofReal p.1 with hA
  set B : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal c * Sn p * ENNReal.ofReal p.1 with hB
  have hAm : AEMeasurable A (volume.restrict S) :=
    (hSpm.const_mul _).mul measurable_fst.ennreal_ofReal.aemeasurable
  have hBm : AEMeasurable B (volume.restrict S) :=
    (hSnm.const_mul _).mul measurable_fst.ennreal_ofReal.aemeasurable
  have eA : (∫⁻ p in S, (ENNReal.ofReal c * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) * ENNReal.ofReal p.1) = ∫⁻ p in S, A p := by
    refine lintegral_congr_ae ?_
    filter_upwards [hit] with p hp
    rw [hp.1]
  have eB : (∫⁻ p in S, (ENNReal.ofReal c * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) * ENNReal.ofReal p.1) = ∫⁻ p in S, B p := by
    refine lintegral_congr_ae ?_
    filter_upwards [hit] with p hp
    rw [hp.2]
  rw [eA] at hP ⊢
  rw [eB] at hN ⊢
  have hAl := ae_lt_top' hAm hP
  have hBl := ae_lt_top' hBm hN
  have hpt : ∀ᵐ p ∂(volume.restrict S),
      (c * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), s p τ φ) * p.1 = (A p).toReal - (B p).toReal := by
    filter_upwards [hsec, hS, hAl, hBl] with p hp h1 hAp hBp
    have hcn : ENNReal.ofReal c ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc0
    have h1n : ENNReal.ofReal p.1 ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h1
    have hSpf : Sp p ≠ ⊤ := by
      intro h
      have : A p = ⊤ := by
        simp only [hA, h, ENNReal.mul_top hcn, ENNReal.top_mul h1n]
      exact absurd hAp (by rw [this]; exact lt_irrefl _)
    have hSnf : Sn p ≠ ⊤ := by
      intro h
      have : B p = ⊤ := by
        simp only [hB, h, ENNReal.mul_top hcn, ENNReal.top_mul h1n]
      exact absurd hBp (by rw [this]; exact lt_irrefl _)
    have hint : Integrable (fun y : ℝ × ℝ => s p y.1 y.2) ν := integrable_of_parts hp hSpf hSnf
    have hval : ∫ y, s p y.1 y.2 ∂ν = (Sp p).toReal - (Sn p).toReal := integral_eq_parts hp hSpf hSnf
    rw [integral_prod _ hint] at hval
    have hiv : (∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), s p τ φ)
        = ∫ τ in Icc (0 : ℝ) 1, ∫ φ in Icc (0 : ℝ) (2 * Real.pi), s p τ φ := by
      simp only [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le h2pi,
        ← integral_Icc_eq_integral_Ioc]
    rw [hiv, hval]
    simp only [hA, hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le, ENNReal.toReal_ofReal h1.le]
    ring
  rw [integral_congr_ae hpt, integral_sub (integrable_toReal_of_lintegral_ne_top hAm hP)
    (integrable_toReal_of_lintegral_ne_top hBm hN), integral_toReal hAm hAl, integral_toReal hBm hBl]

theorem density_sub_offMode {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (q : Fin k → ℝ)
    (mc : ModeCharges) (ec : TailBand.EntryCharges) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    D.labelDensity q v G H ι p - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
        mc ec D.azimuthOrder ι v G H p
      = (mc.curl ι p + ec.curlCharge p) * Real.sqrt (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p))) ^ 2
        + (ec.stretchConst * mc.gradient ι p * mc.length ι p / 2 + ec.gradCharge p)
          * Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p)) ^ 2
        + (ec.stretchConst * mc.gradient ι p * (mc.length ι p)⁻¹ / 2 + ec.velCharge p)
          * Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p)) ^ 2
        + ec.stretchConst * mc.product ι p
          * (Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p)) * Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p))) := by
  have eD : D.labelDensity q v G H ι p = TailBand.labelQuad (TailBand.modeCoef (D.pieces q) (D.cert.period q)
      (D.bounds q) D.cert.weightFn D.azimuthOrder ι p) D.azimuthOrder ι v G H p :=
    TailBand.modeTerm_eq_labelQuad _ _ _ _ _ _ _ _ _ _
  rw [eD]
  simp only [TailBand.offModeDensity, TailBand.labelQuad, TailBand.PointCoef.quad, TailBand.PointCoef.withStretch]
  ring

end Internal.AllocationSplitParts

open Internal.AllocationSplitParts in
theorem allocationSplit_of_regular {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculusEntry D) (hTF : TrueFieldRegular D) (hM : IsCellMesh D.mesh)
    (hreg : EntryChargesRegular D R) (hDM : CellDensityMeasurable D) (hfin : CellPiecesFinite D R) :
    AllocationSplit D R := by
  intro K q v G H g κ F Pg ht
  obtain ⟨hNf, hOPf, hONf⟩ := hfin K q v G H g κ F Pg ht
  have hPf := ht.pos_finite
  have hv := ht.perturbation
  obtain ⟨hLDm, -⟩ := hDM q ht.param v G H g hv K
  obtain ⟨-, -, hSI, -⟩ := hTF
  have hSIm := hSI q ht.param v G H g hv K
  have hae := boxRect_ae_le (D.mesh.box K) (hM.box_valid K)
  have hμ : volume.restrict (D.mesh.box K).rect ≤ volume.restrict halfPlane := Measure.restrict_mono_ae hae
  have hpos : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), 0 < p.1 :=
    (ae_restrict_iff' (measurableSet_boxRect _)).2 (hae.mono fun p h hp => (h hp).1)
  have hst := mean_split hpos
    (fun p τ φ => CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p))) hSIm
    (ne_top_of_lt (lt_of_le_of_lt le_add_self hPf)) (ne_top_of_lt (lt_of_le_of_lt le_add_self hNf))
  have hFm : ∀ ι, AEStronglyMeasurable (fun p => D.labelDensity q v G H ι p * p.1)
      (volume.restrict (D.mesh.box K).rect) := fun ι => (hLDm ι).mul measurable_fst.aestronglyMeasurable
  have hOm : ∀ ι, AEStronglyMeasurable (fun p => TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p * p.1)
      (volume.restrict (D.mesh.box K).rect) := by
    intro ι
    obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hreg.measurable K ι
    obtain ⟨hLV, hLG, -⟩ := TailBand.aestronglyMeasurable_labelFields hv D.azimuthOrder ι
    have hLV' := hLV.mono_measure hμ
    have hLG' := hLG.mono_measure hμ
    have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => cnormSq (curlOfGrad x)) := by
      unfold cnormSq curlOfGrad
      fun_prop
    have hgap := aemeasurable_gap (R.entryCharges K ι).stretchConst m4.aemeasurable m1.aemeasurable
      m2.aemeasurable m3.aemeasurable m5.aemeasurable m6.aemeasurable m7.aemeasurable
      (hcurl.comp_aestronglyMeasurable hLG').aemeasurable
      (Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable hLG').aemeasurable
      (Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable hLV').aemeasurable
    refine (((hLDm ι).sub hgap.aestronglyMeasurable).mul measurable_fst.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun p => ?_)
    have e := density_sub_offMode D q (D.charges (some K)) (R.entryCharges K ι) ι v G H p
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [← e]
    ring
  have ha : (∑' ι : ℤ × ℤ, ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1)) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt le_self_add hPf)
  have hb : (∑' ι : ℤ × ℤ, ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1))) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt le_self_add hNf)
  have hled := tsum_allocation (D.mesh.resolved K)
    (fun ι => ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1))
    (fun ι => ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)))
    (fun ι => if ι ∈ D.mesh.resolved K then 0 else ∫⁻ p in (D.mesh.box K).rect,
      ENNReal.ofReal (TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
        (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p * p.1))
    (fun ι => if ι ∈ D.mesh.resolved K then 0 else ∫⁻ p in (D.mesh.box K).rect,
      ENNReal.ofReal (-(TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
        (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p * p.1)))
    (fun ι => ∫ p in (D.mesh.box K).rect, D.labelDensity q v G H ι p * p.1)
    (fun ι => if ι ∈ D.mesh.resolved K then 0 else ∫ p in (D.mesh.box K).rect,
      (D.labelDensity q v G H ι p - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p) * p.1)
    ha hb hOPf.ne hONf.ne
    (fun ι => integral_eq_parts (hFm ι) (ENNReal.ne_top_of_tsum_ne_top ha ι) (ENNReal.ne_top_of_tsum_ne_top hb ι))
    (fun ι hι => ⟨by simp [hι], by simp [hι]⟩)
    (fun ι hι => by
      have hc := ENNReal.ne_top_of_tsum_ne_top hOPf.ne ι
      have hd := ENNReal.ne_top_of_tsum_ne_top hONf.ne ι
      simp only [if_neg hι] at hc hd ⊢
      rw [← integral_eq_parts (hOm ι) hc hd, ← integral_sub
        (integrable_of_parts (hFm ι) (ENNReal.ne_top_of_tsum_ne_top ha ι) (ENNReal.ne_top_of_tsum_ne_top hb ι))
        (integrable_of_parts (hOm ι) hc hd)]
      simp only [sub_mul])
  have hpA : (cellPos D K q v G H).toReal
      = (∑' ι : ℤ × ℤ, ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1)).toReal
        + (∫⁻ p in (D.mesh.box K).rect, D.stretchPosMean v G p * ENNReal.ofReal p.1).toReal :=
    ENNReal.toReal_add ha (ne_top_of_lt (lt_of_le_of_lt le_add_self hPf))
  have hnA : (cellNeg D K q v G H).toReal
      = (∑' ι : ℤ × ℤ, ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1))).toReal
        + (∫⁻ p in (D.mesh.box K).rect, D.stretchNegMean v G p * ENNReal.ofReal p.1).toReal :=
    ENNReal.toReal_add hb (ne_top_of_lt (lt_of_le_of_lt le_add_self hNf))
  have hS : stretchAmount D K v G = (∫⁻ p in (D.mesh.box K).rect, D.stretchPosMean v G p * ENNReal.ofReal p.1).toReal
      - (∫⁻ p in (D.mesh.box K).rect, D.stretchNegMean v G p * ENNReal.ofReal p.1).toReal := hst
  rw [hpA, hnA, hS]
  unfold resolvedAmount offChargeAmount offPos offNeg
  beta_reduce at hled
  linarith

theorem allocationSplitHolds : AllocationSplitHolds :=
  fun D R _ hTF hM hreg hDM hfin => allocationSplit_of_regular D R hTF hM hreg hDM hfin

end Assembly

end CertCell

end Breakdown
