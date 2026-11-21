import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.TailAngularPlane

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal.ExteriorNonneg

open TailBand

theorem ofReal_balance (f g : ℝ) :
    ENNReal.ofReal (-f) + ENNReal.ofReal g + ENNReal.ofReal (f - g)
      = ENNReal.ofReal f + ENNReal.ofReal (-g) + ENNReal.ofReal (-(f - g)) := by
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).1 ?_
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal']
  have h1 := max_zero_sub_max_neg_zero_eq_self f
  have h2 := max_zero_sub_max_neg_zero_eq_self g
  have h3 := max_zero_sub_max_neg_zero_eq_self (f - g)
  linarith

theorem mode_step {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (ho : (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) ≤ (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ))
    (hfp : (∫⁻ p, ENNReal.ofReal (f p) ∂μ) ≠ ⊤) (hgn : (∫⁻ p, ENNReal.ofReal (-g p) ∂μ) ≠ ⊤) :
    (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (g p) ∂μ)
      ≤ (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ) := by
  have mfn : AEMeasurable (fun p => ENNReal.ofReal (-f p)) μ := hf.neg.ennreal_ofReal
  have mgp : AEMeasurable (fun p => ENNReal.ofReal (g p)) μ := hg.ennreal_ofReal
  have mfp : AEMeasurable (fun p => ENNReal.ofReal (f p)) μ := hf.ennreal_ofReal
  have mgn : AEMeasurable (fun p => ENNReal.ofReal (-g p)) μ := hg.neg.ennreal_ofReal
  have hsum : (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (g p) ∂μ)
        + (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ)
      = (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ)
        + (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) := by
    calc (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (g p) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ)
        = (∫⁻ p, (ENNReal.ofReal (-f p) + ENNReal.ofReal (g p)) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ) := by rw [lintegral_add_left' mfn]
      _ = (∫⁻ p, (ENNReal.ofReal (-f p) + ENNReal.ofReal (g p) + ENNReal.ofReal (f p - g p)) ∂μ) :=
          (lintegral_add_left' (mfn.add mgp) _).symm
      _ = (∫⁻ p, (ENNReal.ofReal (f p) + ENNReal.ofReal (-g p) + ENNReal.ofReal (-(f p - g p))) ∂μ) :=
          lintegral_congr fun p => ofReal_balance (f p) (g p)
      _ = (∫⁻ p, (ENNReal.ofReal (f p) + ENNReal.ofReal (-g p)) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) := lintegral_add_left' (mfp.add mgn) _
      _ = (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ)
          + (∫⁻ p, ENNReal.ofReal (-(f p - g p)) ∂μ) := by rw [lintegral_add_left' mfp]
  have hofin : (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfp, hgn⟩) ?_
    calc (∫⁻ p, ENNReal.ofReal (f p - g p) ∂μ)
        ≤ (∫⁻ p, (ENNReal.ofReal (f p) + ENNReal.ofReal (-g p)) ∂μ) := by
          refine lintegral_mono fun p => ?_
          rw [sub_eq_add_neg]
          exact ENNReal.ofReal_add_le
      _ = (∫⁻ p, ENNReal.ofReal (f p) ∂μ) + (∫⁻ p, ENNReal.ofReal (-g p) ∂μ) := lintegral_add_left' mfp _
  refine (ENNReal.add_le_add_iff_right hofin).1 ?_
  rw [hsum]
  exact add_le_add le_rfl ho

theorem total_step {a b a' b' : ℤ × ℤ → ℝ≥0∞} {SN SP : ℝ≥0∞}
    (hstep : (∑' ι, b ι) ≠ ⊤ → ∀ ι, a ι + b' ι ≤ b ι + a' ι)
    (hfin : (∑' ι, a' ι) + SN < ⊤) (hle : (∑' ι, a' ι) + SN ≤ (∑' ι, b' ι) + SP) :
    (∑' ι, a ι) + SN ≤ (∑' ι, b ι) + SP := by
  by_cases hb : (∑' ι, b ι) = ⊤
  · rw [hb, top_add]
    exact le_top
  have hsum : (∑' ι, a ι) + ∑' ι, b' ι ≤ (∑' ι, b ι) + ∑' ι, a' ι := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum (hstep hb)
  have ha' : (∑' ι, a' ι) ≠ ⊤ := (ENNReal.add_lt_top.1 hfin).1.ne
  have hb' : (∑' ι, b' ι) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hb, ha'⟩) (le_trans le_add_self hsum)
  refine (ENNReal.add_le_add_iff_right hb').1 ?_
  calc (∑' ι, a ι) + SN + ∑' ι, b' ι = ((∑' ι, a ι) + ∑' ι, b' ι) + SN := by ring
    _ ≤ ((∑' ι, b ι) + ∑' ι, a' ι) + SN := add_le_add hsum le_rfl
    _ = (∑' ι, b ι) + ((∑' ι, a' ι) + SN) := add_assoc _ _ _
    _ ≤ (∑' ι, b ι) + ((∑' ι, b' ι) + SP) := add_le_add le_rfl hle
    _ = (∑' ι, b ι) + SP + ∑' ι, b' ι := by ring

theorem formNeg_eq_withCoercivity {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (q : Fin k → ℝ) (hc : (D.pieces q).c = D.coercivity) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    (D.withFormCoercivity D.coercivity).formNeg q v G H = D.formNeg q v G H := by
  have hp : (D.withFormCoercivity D.coercivity).pieces q = D.pieces q := by
    simp only [CellLayerData.withFormCoercivity]
    rw [← hc]
  unfold CellLayerData.formNeg CellLayerData.labelDensity
  rw [hp]
  rfl

def chargeGap (mc : ModeCharges) (ec : EntryCharges) (mm : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  (mc.curl ι p + ec.curlCharge p) * Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))) ^ 2
    + (ec.stretchConst / 2 * mc.gradient ι p * mc.length ι p + ec.gradCharge p)
      * Real.sqrt (cnormSq (labelGrad mm ι G p)) ^ 2
    + (ec.stretchConst / 2 * mc.gradient ι p / mc.length ι p + ec.velCharge p)
      * Real.sqrt (cnormSq (labelVel mm ι v p)) ^ 2
    + ec.stretchConst * mc.product ι p * Real.sqrt (cnormSq (labelGrad mm ι G p))
      * Real.sqrt (cnormSq (labelVel mm ι v p))

theorem chargeDensity_eq {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ec : EntryCharges)
    (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    exteriorChargeDensity D ec q v G H ι p = chargeGap (D.charges none) ec D.azimuthOrder ι v G p := by
  unfold exteriorChargeDensity CellLayerData.labelDensity
  rw [modeTerm_eq_labelQuad]
  simp only [offModeDensity, labelQuad, PointCoef.quad, PointCoef.withStretch, chargeGap]
  ring

theorem offMode_eq {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ec : EntryCharges)
    (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    D.labelDensity q v G H ι p * p.1 - exteriorChargeDensity D ec q v G H ι p * p.1
      = offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges none) ec
          D.azimuthOrder ι v G H p * p.1 := by
  unfold exteriorChargeDensity
  ring

theorem aemeasurable_chargeGap {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (mc : ModeCharges) (ec : EntryCharges)
    (mm : ℕ) (ι : ℤ × ℤ) (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ halfPlane)
    (hcc : Measurable ec.curlCharge) (hgc : Measurable ec.gradCharge) (hvc : Measurable ec.velCharge)
    (hc : Measurable (mc.curl ι)) (hp : Measurable (mc.product ι)) (hg : Measurable (mc.gradient ι))
    (hl : Measurable (mc.length ι)) :
    AEMeasurable (chargeGap mc ec mm ι v G) (volume.restrict Z) := by
  have hL := aestronglyMeasurable_labelFields hv mm ι
  have hmono : volume.restrict Z ≤ volume.restrict halfPlane := Measure.restrict_mono hZ le_rfl
  have hsq : ∀ {β : Type} [Fintype β], Continuous (fun x : β → ℂ => Real.sqrt (cnormSq x)) := by
    intro β _
    unfold cnormSq
    fun_prop
  have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq (curlOfGrad x))) := by
    unfold cnormSq curlOfGrad
    fun_prop
  have x1 : AEMeasurable (fun p => Real.sqrt (cnormSq (labelGrad mm ι G p))) (volume.restrict Z) :=
    (hsq.comp_aestronglyMeasurable (hL.2.1.mono_measure hmono)).aemeasurable
  have x0 : AEMeasurable (fun p => Real.sqrt (cnormSq (labelVel mm ι v p))) (volume.restrict Z) :=
    (hsq.comp_aestronglyMeasurable (hL.1.mono_measure hmono)).aemeasurable
  have xo : AEMeasurable (fun p => Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))))
      (volume.restrict Z) :=
    (hcurl.comp_aestronglyMeasurable (hL.2.1.mono_measure hmono)).aemeasurable
  unfold chargeGap
  exact ((((hc.aemeasurable.add hcc.aemeasurable).mul (xo.pow_const 2)).add
    ((((hg.aemeasurable.const_mul (ec.stretchConst / 2)).mul hl.aemeasurable).add hgc.aemeasurable).mul
      (x1.pow_const 2))).add
    ((((hg.aemeasurable.const_mul (ec.stretchConst / 2)).div hl.aemeasurable).add hvc.aemeasurable).mul
      (x0.pow_const 2))).add
    (((hp.aemeasurable.const_mul ec.stretchConst).mul x1).mul x0)

end Internal.ExteriorNonneg

open TailBand Internal.ExteriorNonneg in
theorem exteriorOffMode_balance (h₁ : ExteriorConditionSound) (h₂ : OffModeConditionSound) (h₃ : LabelFlipEvenHolds)
    {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : ExteriorCover C nE nM)
    (hadm : ∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q)
      (D.bounds q) D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃)
    (hmc : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder) (hX : IsExteriorCover D X)
    {q : Fin k → ℝ} (hq : q ∈ D.cert.params) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation D.cert.symmetries (D.cert.period q) v G H g) (ι : ℤ × ℤ) :
    ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (-(offModeDensity (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn (D.charges none) X.charges D.azimuthOrder ι v G H p * p.1))
      ≤ ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (offModeDensity (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn (D.charges none) X.charges D.azimuthOrder ι v G H p * p.1) := by
  obtain ⟨e₁, e₂, e₃, he⟩ := hadm
  have hP : 0 < D.cert.period q := (he q hq).period_pos
  have hZ : D.mesh.exterior ∩ halfPlane = ⋃ a ∈ X.parts ι, X.region a :=
    Set.Subset.antisymm (hX.covers ι) (Set.iUnion₂_subset fun a ha => hX.in_exterior ι a ha)
  have hd : Set.Pairwise (↑(X.parts ι)) (Function.onFun (AEDisjoint volume) X.region) := by
    intro a ha b hb hab
    exact hX.apart ι a ha b hb hab
  have hm : ∀ a ∈ X.parts ι, NullMeasurableSet (X.region a) volume := fun a _ =>
    (hX.region_measurable a).nullMeasurableSet
  rw [hZ, lintegral_biUnion_finset₀ hd hm, lintegral_biUnion_finset₀ hd hm]
  refine Finset.sum_le_sum fun a ha => ?_
  have hmem := hX.mode_mem ι a ha
  rcases a with i | j
  · have key := h₁ _ _ _ _ _ _ _ _ _ _ (he q hq) D.azimuthOrder (X.rayConditions i) (D.charges none)
      (hX.ray_valid q hq i) D.cert.symmetries v G H g hv ι hmem
      (fun _ _ _ => h₃ D.cert.symmetries (D.cert.period q) v G H g hv hP hmc.flip D.azimuthOrder ι)
    rw [hX.ray_charges i] at key
    exact key
  · have hE := hX.point_valid q hq j
    have key := h₂ _ _ _ _ _ _ _ _ _ _ (he q hq) D.azimuthOrder (X.pointConditions j) (D.charges none)
      hE D.cert.symmetries v G H g hv ι hmem
    rw [hX.point_charges j] at key
    have hzero : ∫⁻ p in X.region (Sum.inr j), ENNReal.ofReal (-(offModeDensity (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn (D.charges none) X.charges D.azimuthOrder ι v G H p * p.1)) = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [key, ae_restrict_mem hE.region_measurable] with p hp hpZ
      have hr : 0 < p.1 := (Set.mem_prod.mp (hE.region_sub hpZ)).1
      exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (mul_nonneg hp hr.le))
    rw [hzero]
    exact zero_le

open TailBand Internal.ExteriorNonneg in
theorem exteriorNonneg_of_sound_of_measurable (h₁ : ExteriorConditionSound) (h₂ : OffModeConditionSound)
    (h₃ : LabelFlipEvenHolds) :
    ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : ExteriorCover C nE nM),
      (∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
        ∀ ι, AEStronglyMeasurable (D.labelDensity q v G H ι) (volume.restrict (D.mesh.exterior ∩ halfPlane))) →
      FieldRegular D → TrueFieldRegular D →
      (∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
      Bridge.IsModeClass D.cert.symmetries D.azimuthOrder → IsCellMesh D.mesh → FormNegFinite D D.coercivity →
      (∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity) →
      IsExteriorCover D X → ExteriorStretchCharged D X.charges → ExteriorNonneg D := by
  intro k C nE nM D X hmeas _ _ hadm hmc _ hN hc hX hS q hq v G H g hv
  have hsub : D.mesh.exterior ∩ halfPlane ⊆ halfPlane := Set.inter_subset_right
  refine ⟨?_, ?_⟩
  · have hNq := hN q hq v G H g hv
    rw [formNeg_eq_withCoercivity D q (hc q hq)] at hNq
    refine lt_of_le_of_lt ?_ hNq
    unfold extNeg CellLayerData.formNeg
    exact add_le_add (ENNReal.tsum_le_tsum fun ι => lintegral_mono_set hsub) (lintegral_mono_set hsub)
  · obtain ⟨hfin, hle⟩ := hS q hq v G H g hv
    unfold extNeg extPos
    refine total_step ?_ hfin hle
    intro hb ι
    obtain ⟨hcc, hgc, hvc, hmcs⟩ := hX.charges_measurable
    obtain ⟨hcu, hpr, hgr, hln⟩ := hmcs ι
    have hg : AEMeasurable (fun p => exteriorChargeDensity D X.charges q v G H ι p * p.1)
        (volume.restrict (D.mesh.exterior ∩ halfPlane)) := by
      have e : (fun p => exteriorChargeDensity D X.charges q v G H ι p * p.1)
          = fun p => chargeGap (D.charges none) X.charges D.azimuthOrder ι v G p * p.1 :=
        funext fun p => by rw [chargeDensity_eq]
      rw [e]
      exact (aemeasurable_chargeGap hv (D.charges none) X.charges D.azimuthOrder ι _ hsub hcc hgc hvc
        hcu hpr hgr hln).mul measurable_fst.aemeasurable
    have hf : AEMeasurable (fun p => D.labelDensity q v G H ι p * p.1)
        (volume.restrict (D.mesh.exterior ∩ halfPlane)) :=
      (hmeas q hq v G H g hv ι).aemeasurable.mul measurable_fst.aemeasurable
    have ho := exteriorOffMode_balance h₁ h₂ h₃ D X hadm hmc hX hq hv ι
    have ho' : ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal
          (-(D.labelDensity q v G H ι p * p.1 - exteriorChargeDensity D X.charges q v G H ι p * p.1))
        ≤ ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal
          (D.labelDensity q v G H ι p * p.1 - exteriorChargeDensity D X.charges q v G H ι p * p.1) := by
      simp only [offMode_eq]
      exact ho
    have hbι : ∫⁻ p in D.mesh.exterior ∩ halfPlane, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1) ≠ ⊤ :=
      ne_top_of_le_ne_top hb (ENNReal.le_tsum (f := fun ι => ∫⁻ p in D.mesh.exterior ∩ halfPlane,
        ENNReal.ofReal (D.labelDensity q v G H ι p * p.1)) ι)
    have ha'ι : ∫⁻ p in D.mesh.exterior ∩ halfPlane,
        ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.add_lt_top.1 hfin).1.ne ?_
      exact ENNReal.le_tsum (f := fun ι => ∫⁻ p in D.mesh.exterior ∩ halfPlane,
        ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1))) ι
    exact mode_step hf hg ho' hbι ha'ι

end Assembly

end CertCell

end Breakdown
