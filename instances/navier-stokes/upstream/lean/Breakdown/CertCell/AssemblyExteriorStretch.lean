import Breakdown.CertCell.AssemblyExteriorStretchPointwise
import Breakdown.CertCell.AssemblyPotentialSharpPoint
import Breakdown.CertCell.AssemblyPotentialExpand

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCalculus

section ExteriorStretch

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def exteriorPointLoss (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  Internal.Sharp.pointLoss ((D.charges none).curl ι p) ((D.charges none).product ι p)
    ((D.charges none).gradient ι p) ((D.charges none).length ι p) (bandProfile D ι v G p)

end ExteriorStretch

def ExteriorPointBoundHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM),
    FieldRegular D → Bridge.IsModeClass D.cert.symmetries D.azimuthOrder →
    IsRegionChargeBound D.azimuthOrder (D.mesh.exterior ∩ halfPlane) D.given D.givenHess (D.charges none) →
    MeasurableSet (D.mesh.exterior ∩ halfPlane) →
    (∃ c : ℝ, ∀ p ∈ D.mesh.exterior ∩ halfPlane, ∀ ι, |(D.charges none).curl ι p| ≤ c ∧
      |(D.charges none).product ι p| ≤ c ∧ |(D.charges none).gradient ι p| ≤ c) →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      ∀ᵐ p ∂(volume.restrict (D.mesh.exterior ∩ halfPlane)),
        -D.meanStretch v G p ≤ ∑' ι : ℤ × ℤ, exteriorPointLoss D ι v G p

def MeanStretchTripleSumHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM),
    FieldRegular D → Bridge.IsModeClass D.cert.symmetries D.azimuthOrder →
    ∀ Hl : Finset (ℤ × ℤ), (∀ α, α ∈ Hl ↔ labelHarmonic D.azimuthOrder α ∈ D.givenLabels) →
    ∀ (P : ℝ) v G H g, IsPerturbation D.cert.symmetries P v G H g →
      ∀ᵐ p ∂(volume.restrict halfPlane), D.meanStretch v G p = ∑' ι : ℤ × ℤ, ∑ α ∈ Hl,
        (sesq12 (Internal.Sharp.tripleMatrix
            (modeGrad (labelHarmonic D.azimuthOrder α) (gradField D.given) 0 (planePoint p))
            (modeSecondDeriv (labelHarmonic D.azimuthOrder α) D.givenHess 0 (planePoint p)))
          (bandProfile D ι v G p) (bandProfile D (ι - α) v G p)).re


open Internal.ExteriorStretch in
theorem exteriorStretchCharged_of_point (hPt : ExteriorPointBoundHolds) : ExteriorStretchChargedHolds := by
  intro k C nE nM D X hF hTF hW hHE hB hκ hX q hq v G H g hv
  have hM := hF.mode_class
  obtain ⟨B, hWB⟩ := hW
  have hm1 : 1 ≤ D.azimuthOrder := hF.azimuth_pos
  have hZm : MeasurableSet (D.mesh.exterior ∩ halfPlane) := by
    have e : D.mesh.exterior ∩ halfPlane = ⋃ a ∈ X.parts 0, X.region a :=
      Subset.antisymm (hX.covers 0) (iUnion₂_subset fun a ha => hX.in_exterior 0 a ha)
    rw [e]
    exact Finset.measurableSet_biUnion _ fun a _ => hX.region_measurable a
  have hZH : D.mesh.exterior ∩ halfPlane ⊆ halfPlane := inter_subset_right
  have hμle : volume.restrict (D.mesh.exterior ∩ halfPlane) ≤ volume.restrict halfPlane :=
    Measure.restrict_mono hZH le_rfl
  obtain ⟨cb, hcb⟩ := hX.charges_bounded
  have hκ0 : 0 ≤ X.charges.stretchConst := (Real.sqrt_nonneg _).trans hκ
  obtain ⟨hmcc, hmgc, hmvc, hmch⟩ := hX.charges_measurable
  have hd : ∀ ι p, exteriorChargeDensity D X.charges q v G H ι p
      = gapValue ((D.charges none).curl ι p) (X.charges.curlCharge p) (X.charges.gradCharge p)
          (X.charges.velCharge p) ((D.charges none).product ι p) ((D.charges none).gradient ι p)
          ((D.charges none).length ι p) (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)))
          (cnormSq (labelGrad D.azimuthOrder ι G p)) (cnormSq (labelVel D.azimuthOrder ι v p))
          X.charges.stretchConst :=
    fun ι p => density_gap D q (D.charges none) X.charges ι v G H p
  have hpt : ∀ ι, ∀ p ∈ D.mesh.exterior ∩ halfPlane,
      -(2 * cb * cnormSq (labelGrad D.azimuthOrder ι G p)) ≤ exteriorChargeDensity D X.charges q v G H ι p ∧
      |exteriorChargeDensity D X.charges q v G H ι p|
        ≤ (4 * cb + cb ^ 2 + 2 * cb + cb ^ 2)
          * (cnormSq (labelGrad D.azimuthOrder ι G p) + cnormSq (labelVel D.azimuthOrder ι v p)) ∧
      -(2 * cb * cnormSq (labelGrad D.azimuthOrder ι G p)) ≤ exteriorPointLoss D ι v G p ∧
      exteriorPointLoss D ι v G p ≤ exteriorChargeDensity D X.charges q v G H ι p ∧ 0 ≤ cb := by
    intro ι p hp
    obtain ⟨hcc, hgc, hvc⟩ := hX.charges_nonneg p
    obtain ⟨hmg, hwg⟩ := hB.charges_nonneg ι p hp
    have hlen := hB.length_pos ι p hp
    obtain ⟨b1, b2, b3, b4, b5⟩ := hcb p hp
    obtain ⟨c1, c2, c3, c4, c5⟩ := b5 ι
    have hxo := cnormSq_nonneg' (curlOfGrad (labelGrad D.azimuthOrder ι G p))
    have hx1 := cnormSq_nonneg' (labelGrad D.azimuthOrder ι G p)
    have hx0 := cnormSq_nonneg' (labelVel D.azimuthOrder ι v p)
    have hxo2 := curl_cnormSq_le (labelGrad D.azimuthOrder ι G p)
    have hcb0 : 0 ≤ cb := (abs_nonneg _).trans c1
    have hloss : exteriorPointLoss D ι v G p
        = (D.charges none).curl ι p * cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p))
          + Real.sqrt (7 / 2) / 2 * (D.charges none).gradient ι p
            * ((D.charges none).length ι p * cnormSq (labelGrad D.azimuthOrder ι G p)
              + cnormSq (labelVel D.azimuthOrder ι v p) / (D.charges none).length ι p)
          + Real.sqrt (7 / 2) * (D.charges none).product ι p
            * (Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p))
              * Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p))) := by
      unfold exteriorPointLoss Internal.Sharp.pointLoss
      rw [gradOf_bandProfile, velOf_bandProfile]
      ring
    rw [hd ι p]
    refine ⟨gapValue_lower _ _ _ _ _ _ _ _ _ _ _ cb hxo hx1 hx0 hcc hgc hvc hmg hwg hlen hκ0 c1 hxo2,
      gapValue_abs_weighted _ _ _ _ _ _ _ _ _ _ _ cb hxo hx1 hx0 hcc hgc hvc hmg hwg hlen hκ0 c1 hxo2
        ((le_abs_self _).trans b1) ((le_abs_self _).trans b2) ((le_abs_self _).trans b3)
        ((le_abs_self _).trans c2) c4 c5 ((le_abs_self _).trans b4), ?_,
      ?_, hcb0⟩
    · rw [hloss]
      have h1 : -(cb * cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)))
          ≤ (D.charges none).curl ι p * cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)) := by
        have := neg_abs_le ((D.charges none).curl ι p)
        nlinarith
      have h2 : 0 ≤ Real.sqrt (7 / 2) / 2 * (D.charges none).gradient ι p
          * ((D.charges none).length ι p * cnormSq (labelGrad D.azimuthOrder ι G p)
            + cnormSq (labelVel D.azimuthOrder ι v p) / (D.charges none).length ι p) := by positivity
      have h3 : 0 ≤ Real.sqrt (7 / 2) * (D.charges none).product ι p
          * (Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p))
            * Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p))) := by positivity
      have h4 := mul_le_mul_of_nonneg_left hxo2 hcb0
      linarith
    · rw [hloss]
      exact loss_le_gapValue _ _ _ _ _ _ _ _ _ _ _ hxo hx1 hx0 hcc hgc hvc hmg hwg hlen hκ
  have hdm : ∀ ι, AEMeasurable (fun p => exteriorChargeDensity D X.charges q v G H ι p)
      (volume.restrict (D.mesh.exterior ∩ halfPlane)) := by
    intro ι
    obtain ⟨hLV, hLG, -⟩ := TailBand.aestronglyMeasurable_labelFields hv D.azimuthOrder ι
    have hLV' := hLV.mono_measure hμle
    have hLG' := hLG.mono_measure hμle
    have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => cnormSq (curlOfGrad x)) := by
      unfold cnormSq curlOfGrad
      fun_prop
    obtain ⟨m1, m2, m3, m4⟩ := hmch ι
    have hgap := aemeasurable_gapValue X.charges.stretchConst m1.aemeasurable
      hmcc.aemeasurable hmgc.aemeasurable hmvc.aemeasurable m2.aemeasurable m3.aemeasurable m4.aemeasurable
      (hcurl.comp_aestronglyMeasurable hLG').aemeasurable
      (Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable hLG').aemeasurable
      (Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable hLV').aemeasurable
    refine hgap.congr (Filter.Eventually.of_forall fun p => ?_)
    exact (hd ι p).symm
  have hPm : ∀ ι, AEMeasurable (fun p => ENNReal.ofReal (exteriorChargeDensity D X.charges q v G H ι p * p.1))
      (volume.restrict (D.mesh.exterior ∩ halfPlane)) :=
    fun ι => ((hdm ι).mul measurable_fst.aemeasurable).ennreal_ofReal
  have hNm : ∀ ι, AEMeasurable (fun p => ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1)))
      (volume.restrict (D.mesh.exterior ∩ halfPlane)) :=
    fun ι => ((hdm ι).mul measurable_fst.aemeasurable).neg.ennreal_ofReal
  have hms := ae_mode_summable hv D.azimuthOrder hm1
  obtain ⟨γ, -, hγ1, -⟩ := hM.flip
  have hq' := Bridge.Internal.StretchMeanParts.qmp_orbit γ.1 hγ1
  have hi := Bridge.Internal.StretchMeanParts.stretch_integrable hWB hv
  have h1 := hi.aestronglyMeasurable.comp_quasiMeasurePreserving hq'
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc, Measure.restrict_congr_set Ioc_ae_eq_Icc] at h1
  have hac : (volume.restrict (D.mesh.exterior ∩ halfPlane)).prod
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))
      ≪ (volume.restrict halfPlane).prod
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) :=
    Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le hμle) Measure.AbsolutelyContinuous.rfl
  have hs : AEStronglyMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      CoerciveWeak.stretchFormWith D.given D.givenHess v G z.2.1 (axialRot z.2.2 (planePoint z.1)))
      ((volume.restrict (D.mesh.exterior ∩ halfPlane)).prod
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))) :=
    h1.mono_ac hac
  have hsec := hs.prodMk_left
  have hSNZ : ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1 < ⊤ :=
    (lintegral_mono_set hZH).trans_lt (Internal.FormNegative.stretchNeg_lt_top D hWB hv)
  have hSNm : AEMeasurable (fun p => D.stretchNegMean v G p * ENNReal.ofReal p.1)
      (volume.restrict (D.mesh.exterior ∩ halfPlane)) := by
    have hA : AEMeasurable (fun p => ENNReal.ofReal (1 / (2 * Real.pi)) * (∫⁻ y, ENNReal.ofReal
        (-CoerciveWeak.stretchFormWith D.given D.givenHess v G y.1 (axialRot y.2 (planePoint p)))
        ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))) * ENNReal.ofReal p.1)
        (volume.restrict (D.mesh.exterior ∩ halfPlane)) :=
      ((hs.aemeasurable.neg.ennreal_ofReal.lintegral_prod_right').const_mul _).mul
        measurable_fst.ennreal_ofReal.aemeasurable
    refine hA.congr ?_
    filter_upwards [hsec] with p hp
    unfold CellLayerData.stretchNegMean
    rw [lintegral_prod (fun y : ℝ × ℝ => ENNReal.ofReal
      (-CoerciveWeak.stretchFormWith D.given D.givenHess v G y.1 (axialRot y.2 (planePoint p))))
      hp.aemeasurable.neg.ennreal_ofReal]
  have hSNae := ae_lt_top' hSNm hSNZ.ne
  have hPtae := hPt D hF hM hB hZm ⟨cb, fun p hp ι => ⟨((hcb p hp).2.2.2.2 ι).1, ((hcb p hp).2.2.2.2 ι).2.1,
    ((hcb p hp).2.2.2.2 ι).2.2.1⟩⟩ q hq v G H g hv
  have hptw : ∀ᵐ p ∂(volume.restrict (D.mesh.exterior ∩ halfPlane)),
      D.stretchNegMean v G p * ENNReal.ofReal p.1
          + ∑' ι, ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1))
        ≤ D.stretchPosMean v G p * ENNReal.ofReal p.1
          + ∑' ι, ENNReal.ofReal (exteriorChargeDensity D X.charges q v G H ι p * p.1) := by
    filter_upwards [ae_restrict_mem hZm, hsec, hSNae, hPtae, ae_restrict_of_ae_restrict_of_subset hZH hms]
      with p hpZ hps hpn hpl hpgv
    have hr : 0 < p.1 := hpZ.2.1
    obtain ⟨hgsum, hvsum⟩ := hpgv
    have hcb0 : 0 ≤ cb := (hpt 0 p hpZ).2.2.2.2
    have hdsum : Summable fun ι => exteriorChargeDensity D X.charges q v G H ι p :=
      Summable.of_norm_bounded ((hgsum.add hvsum).mul_left (4 * cb + cb ^ 2 + 2 * cb + cb ^ 2)) fun ι => by
        rw [Real.norm_eq_abs]; exact (hpt ι p hpZ).2.1
    have hlsum : Summable fun ι => exteriorPointLoss D ι v G p := by
      refine Summable.of_norm_bounded ((hgsum.add hvsum).mul_left
        (2 * cb + (4 * cb + cb ^ 2 + 2 * cb + cb ^ 2))) fun ι => ?_
      obtain ⟨a1, a2, a3, a4, -⟩ := hpt ι p hpZ
      have hx1 := cnormSq_nonneg' (labelGrad D.azimuthOrder ι G p)
      have hx0 := cnormSq_nonneg' (labelVel D.azimuthOrder ι v p)
      have hK : 0 ≤ 4 * cb + cb ^ 2 + 2 * cb + cb ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_le]
      have := le_abs_self (exteriorChargeDensity D X.charges q v G H ι p)
      constructor <;> nlinarith [mul_nonneg hcb0 hx0, mul_nonneg hK hx1, mul_nonneg hK hx0]
    have hsn : D.stretchNegMean v G p ≠ ⊤ := by
      intro h
      have hr0 : ENNReal.ofReal p.1 ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr
      rw [h, ENNReal.top_mul hr0] at hpn
      exact lt_irrefl _ hpn
    refine point_ennreal hdsum hr hsn fun hsp => ?_
    have hc0 : 0 < 1 / (2 * Real.pi) := by positivity
    have hcn : ENNReal.ofReal (1 / (2 * Real.pi)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc0
    have hP' : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p))) ≠ ⊤ := by
      intro h
      apply hsp
      unfold CellLayerData.stretchPosMean
      rw [h, ENNReal.mul_top hcn]
    have hN' : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p))) ≠ ⊤ := by
      intro h
      apply hsn
      unfold CellLayerData.stretchNegMean
      rw [h, ENNReal.mul_top hcn]
    have hmean := meanStretch_eq_parts D v G p hps hP' hN'
    have eP : (D.stretchPosMean v G p).toReal = 1 / (2 * Real.pi) * (∫⁻ τ in Icc (0 : ℝ) 1,
        ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal
          (CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))).toReal := by
      unfold CellLayerData.stretchPosMean
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le]
    have eN : (D.stretchNegMean v G p).toReal = 1 / (2 * Real.pi) * (∫⁻ τ in Icc (0 : ℝ) 1,
        ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal
          (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))).toReal := by
      unfold CellLayerData.stretchNegMean
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le]
    have hle : ∑' ι, exteriorPointLoss D ι v G p ≤ ∑' ι, exteriorChargeDensity D X.charges q v G H ι p :=
      hlsum.tsum_le_tsum (fun ι => (hpt ι p hpZ).2.2.2.1) hdsum
    rw [eP, eN]
    have e2 : 1 / (2 * Real.pi) * (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))).toReal
        - 1 / (2 * Real.pi) * (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))).toReal
        = -D.meanStretch v G p := by
      rw [hmean]; ring
    rw [e2]
    exact hpl.trans hle
  have hNfin : ∑' ι, ∫⁻ p in D.mesh.exterior ∩ halfPlane,
      ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1)) < ⊤ := by
    have hb : ∀ ι, ∫⁻ p in D.mesh.exterior ∩ halfPlane,
        ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1))
          ≤ ENNReal.ofReal (2 * |cb|) * ∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p)) * p.1) := by
      intro ι
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_trans ?_ (lintegral_mono_set hZH)
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hZm] with p hp
      obtain ⟨a1, -, -, -, a5⟩ := hpt ι p hp
      have hr : 0 < p.1 := hp.2.1
      rw [← ENNReal.ofReal_mul (by positivity), abs_of_nonneg a5]
      refine ENNReal.ofReal_le_ofReal ?_
      have e : cnormSq (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p))
          = cnormSq (labelGrad D.azimuthOrder ι G p) := rfl
      rw [e]
      nlinarith
    calc ∑' ι, ∫⁻ p in D.mesh.exterior ∩ halfPlane,
          ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1))
        ≤ ∑' ι, ENNReal.ofReal (2 * |cb|) * ∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p)) * p.1) :=
          ENNReal.tsum_le_tsum hb
      _ = ENNReal.ofReal (2 * |cb|) * ∑' ι, ∫⁻ p in halfPlane,
            ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p)) * p.1) :=
          ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Internal.FormNegative.gradient_sum_lt_top _ hm1 hv)
  refine ⟨ENNReal.add_lt_top.2 ⟨hNfin, hSNZ⟩, ?_⟩
  calc (∑' ι, ∫⁻ p in D.mesh.exterior ∩ halfPlane,
          ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1)))
        + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1
      = ∫⁻ p in D.mesh.exterior ∩ halfPlane, ((∑' ι,
          ENNReal.ofReal (-(exteriorChargeDensity D X.charges q v G H ι p * p.1)))
          + D.stretchNegMean v G p * ENNReal.ofReal p.1) := by
        rw [lintegral_add_left' (AEMeasurable.ennreal_tsum hNm), lintegral_tsum hNm]
    _ ≤ ∫⁻ p in D.mesh.exterior ∩ halfPlane, ((∑' ι,
          ENNReal.ofReal (exteriorChargeDensity D X.charges q v G H ι p * p.1))
          + D.stretchPosMean v G p * ENNReal.ofReal p.1) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hptw] with p hp
        rw [add_comm, add_comm _ (D.stretchPosMean v G p * ENNReal.ofReal p.1)]
        exact hp
    _ = (∑' ι, ∫⁻ p in D.mesh.exterior ∩ halfPlane,
          ENNReal.ofReal (exteriorChargeDensity D X.charges q v G H ι p * p.1))
        + ∫⁻ p in D.mesh.exterior ∩ halfPlane, D.stretchPosMean v G p * ENNReal.ofReal p.1 := by
        rw [lintegral_add_left' (AEMeasurable.ennreal_tsum hPm), lintegral_tsum hPm]

namespace Internal.ExteriorStretch

theorem sesq12_tripleMatrix_eq_coupling {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (α : ℤ × ℤ) (p : ℝ × ℝ) (U V : Fin 12 → ℂ) :
    sesq12 (Internal.Sharp.tripleMatrix
        (modeGrad (labelHarmonic D.azimuthOrder α) (gradField D.given) 0 (planePoint p))
        (modeSecondDeriv (labelHarmonic D.azimuthOrder α) D.givenHess 0 (planePoint p))) U V
      = sesq12 (trueCoupling D α p) U V := by
  rw [Internal.StretchPairs.sesq12_trueCoupling_eq D α p U V, Internal.Sharp.sesq12_tripleMatrix]
  rfl

end Internal.ExteriorStretch

theorem meanStretchTripleSum : MeanStretchTripleSumHolds := by
  intro k C nE nM D hF hM Hl hHl P v G H g hv
  refine (meanStretch_eq_labelSum_of_modeClass D hF.model_state hF.model_harmonics hF.azimuth_pos hM Hl hHl
    hv).mono fun p hp => ?_
  rw [hp.2]
  exact tsum_congr fun κ => Finset.sum_congr rfl fun α _ => by
    rw [Internal.ExteriorStretch.sesq12_tripleMatrix_eq_coupling]

open Internal.ExteriorStretch in
theorem exteriorPointBound_of_tripleSum (hS : MeanStretchTripleSumHolds) : ExteriorPointBoundHolds := by
  intro k C nE nM D hF hM hB hZm hC q hq v G H g hv
  obtain ⟨cb, hcb⟩ := hC
  obtain ⟨B, hWB⟩ := hF.model_state
  have hm1 := hF.azimuth_pos
  have hinj := Internal.NegativeModeSum.labelHarmonic_injective_of_pos hm1
  have hHl : ∀ α, α ∈ D.givenLabels.preimage (labelHarmonic D.azimuthOrder) hinj.injOn
      ↔ labelHarmonic D.azimuthOrder α ∈ D.givenLabels := fun α => Finset.mem_preimage
  have hZH : D.mesh.exterior ∩ halfPlane ⊆ halfPlane := inter_subset_right
  have e0 : labelHarmonic D.azimuthOrder (0, 0) = 0 := by
    simp [labelHarmonic, labelTime, labelAzimuth]
  have e2 : ∀ p a b, labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p (a, b)
      = modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (D.givenHess σ y)) 0 (planePoint p) (a, b) := by
    intro p a b
    unfold labelGrad
    rw [e0]
    rfl
  filter_upwards [ae_restrict_mem hZm, ae_restrict_of_ae_restrict_of_subset hZH (hS D hF hM _ hHl _ v G H g hv),
    ae_restrict_of_ae_restrict_of_subset hZH (givenSecond_frame hF.model_harmonics hWB),
    ae_restrict_of_ae_restrict_of_subset hZH (ae_mode_summable hv D.azimuthOrder hm1)] with p hpZ hsum hE2 hgv
  have hX : Summable fun ι => cnormSq (bandProfile D ι v G p) := by
    refine (hgv.1.add hgv.2).congr fun ι => ?_
    unfold bandProfile
    rw [cnormSq_pairVec]
    rfl
  have hbound := Internal.Sharp.point_bound D.azimuthOrder hm1 D.givenLabels _ hHl D.given D.givenHess
    (planePoint p) (fun τ φ a b => givenGrad_frame hF.model_harmonics hWB (planePoint p) τ φ a b) hE2
    (fun τ φ j l => Internal.vorticityGradFrame (D.givenHess τ (axialRot φ (planePoint p)))
      (fun u w => hF.hessian_symmetric τ _ u w) φ j l)
    hF.hessian_symmetric
    (fun ι => (D.charges none).curl ι p) (fun ι => (D.charges none).product ι p)
    (fun ι => (D.charges none).gradient ι p) ((D.charges none).length 0 p) cb (hB.length_pos 0 p hpZ)
    (fun ι τ φ u => by
      have h := hB.strain ι p hpZ τ φ u
      rw [← Bridge.Internal.PatchModeWeak.rot_plane p φ, inner_strain_eq] at h
      exact h)
    (fun ι => by
      have h := hB.mean_gradient ι p hpZ
      simp only [e2] at h
      exact h)
    (fun ι τ φ u => by
      have h := hB.wave_gradient ι p hpZ τ φ u
      rw [← Bridge.Internal.PatchModeWeak.rot_plane p φ] at h
      simp only [e2] at h
      exact h)
    (fun ι => (hB.charges_nonneg ι p hpZ).1) (fun ι => (hB.charges_nonneg ι p hpZ).2)
    (fun ι => ⟨(hcb p hpZ ι).1, (le_abs_self _).trans (hcb p hpZ ι).2.1, (le_abs_self _).trans (hcb p hpZ ι).2.2⟩)
    (fun ι => bandProfile D ι v G p) hX
  have hloss : ∀ ι, exteriorPointLoss D ι v G p = Internal.Sharp.pointLoss ((D.charges none).curl ι p)
      ((D.charges none).product ι p) ((D.charges none).gradient ι p) ((D.charges none).length 0 p)
      (bandProfile D ι v G p) := by
    intro ι
    unfold exteriorPointLoss
    rw [hB.length_common ι 0 p hpZ]
  rw [hsum]
  simp only [hloss]
  linarith

theorem exteriorStretchCharged : ExteriorStretchChargedHolds :=
  exteriorStretchCharged_of_point (exteriorPointBound_of_tripleSum meanStretchTripleSum)

end Assembly

end CertCell

end Breakdown
