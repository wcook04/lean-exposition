import Breakdown.CertCell.FormNegativeFinite
import Breakdown.CertCell.StretchMeanIntegral
import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsGiven
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsAlgebra
import Breakdown.CertCell.PatchModeWeak

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCalculus

namespace Internal.ExteriorStretch

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_sub_le a b
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem curl_cnormSq_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  have e0 : curlOfGrad g 0 = g (2, 1) - g (1, 2) := by
    simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]; norm_num; ring
  have e1 : curlOfGrad g 1 = g (0, 2) - g (2, 0) := by
    simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]; norm_num; ring
  have e2 : curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
    simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]; norm_num; ring
  unfold cnormSq
  rw [Fin.sum_univ_three, e0, e1, e2, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  nlinarith [norm_sub_sq_le (g (2, 1)) (g (1, 2)), norm_sub_sq_le (g (0, 2)) (g (2, 0)),
    norm_sub_sq_le (g (1, 0)) (g (0, 1)), sq_nonneg ‖g (0, 0)‖, sq_nonneg ‖g (1, 1)‖, sq_nonneg ‖g (2, 2)‖]

def gapValue (st cc gc vc mg wg len xo x1 x0 k : ℝ) : ℝ :=
  (st + cc) * Real.sqrt xo ^ 2 + (k * wg * len / 2 + gc) * Real.sqrt x1 ^ 2
    + (k * wg * len⁻¹ / 2 + vc) * Real.sqrt x0 ^ 2 + k * mg * (Real.sqrt x1 * Real.sqrt x0)

theorem gapValue_lower (st cc gc vc mg wg len xo x1 x0 k cb : ℝ) (hxo : 0 ≤ xo) (hx1 : 0 ≤ x1)
    (hx0 : 0 ≤ x0) (hcc : 0 ≤ cc) (hgc : 0 ≤ gc) (hvc : 0 ≤ vc) (hmg : 0 ≤ mg) (hwg : 0 ≤ wg)
    (hlen : 0 < len) (hk : 0 ≤ k) (hst : |st| ≤ cb) (hxo2 : xo ≤ 2 * x1) :
    -(2 * cb * x1) ≤ gapValue st cc gc vc mg wg len xo x1 x0 k := by
  unfold gapValue
  rw [Real.sq_sqrt hxo, Real.sq_sqrt hx1, Real.sq_sqrt hx0]
  have hcb : 0 ≤ cb := (abs_nonneg st).trans hst
  have h1 : -(cb * xo) ≤ st * xo := by
    have := neg_abs_le st
    nlinarith
  have h2 : 0 ≤ cc * xo := mul_nonneg hcc hxo
  have h3 : 0 ≤ (k * wg * len / 2 + gc) * x1 := by positivity
  have h4 : 0 ≤ (k * wg * len⁻¹ / 2 + vc) * x0 := by positivity
  have h5 : 0 ≤ k * mg * (Real.sqrt x1 * Real.sqrt x0) := by positivity
  have h6 : cb * xo ≤ cb * (2 * x1) := mul_le_mul_of_nonneg_left hxo2 hcb
  nlinarith

theorem gapValue_abs_weighted (st cc gc vc mg wg len xo x1 x0 k cb : ℝ) (hxo : 0 ≤ xo) (hx1 : 0 ≤ x1)
    (hx0 : 0 ≤ x0) (hcc : 0 ≤ cc) (hgc : 0 ≤ gc) (hvc : 0 ≤ vc) (hmg : 0 ≤ mg) (hwg : 0 ≤ wg)
    (hlen : 0 < len) (hk : 0 ≤ k) (hst : |st| ≤ cb) (hxo2 : xo ≤ 2 * x1) (hcc' : cc ≤ cb) (hgc' : gc ≤ cb)
    (hvc' : vc ≤ cb) (hmg' : mg ≤ cb) (hwl : wg * len ≤ cb) (hwli : wg * len⁻¹ ≤ cb) (hk' : k ≤ cb) :
    |gapValue st cc gc vc mg wg len xo x1 x0 k| ≤ (4 * cb + cb ^ 2 + 2 * cb + cb ^ 2) * (x1 + x0) := by
  have hcb : 0 ≤ cb := (abs_nonneg st).trans hst
  unfold gapValue
  rw [Real.sq_sqrt hxo, Real.sq_sqrt hx1, Real.sq_sqrt hx0]
  have hli : 0 ≤ len⁻¹ := inv_nonneg.2 hlen.le
  have t1 : |(st + cc) * xo| ≤ 4 * cb * x1 := by
    rw [abs_mul, abs_of_nonneg hxo]
    have : |st + cc| ≤ 2 * cb := by
      refine (abs_add_le st cc).trans ?_
      rw [abs_of_nonneg hcc]; linarith
    calc |st + cc| * xo ≤ (2 * cb) * (2 * x1) :=
          mul_le_mul this hxo2 hxo (by linarith)
      _ = 4 * cb * x1 := by ring
  have t2 : |(k * wg * len / 2 + gc) * x1| ≤ (cb ^ 2 / 2 + cb) * x1 := by
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ hx1
    have : k * wg * len ≤ cb * cb := by
      rw [mul_assoc]; exact mul_le_mul hk' hwl (mul_nonneg hwg hlen.le) hcb
    nlinarith
  have t3 : |(k * wg * len⁻¹ / 2 + vc) * x0| ≤ (cb ^ 2 / 2 + cb) * x0 := by
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ hx0
    have : k * wg * len⁻¹ ≤ cb * cb := by
      rw [mul_assoc]; exact mul_le_mul hk' hwli (mul_nonneg hwg hli) hcb
    nlinarith
  have t4 : |k * mg * (Real.sqrt x1 * Real.sqrt x0)| ≤ cb ^ 2 * (x1 + x0) := by
    rw [abs_of_nonneg (by positivity)]
    have hs : Real.sqrt x1 * Real.sqrt x0 ≤ x1 + x0 := by
      have a1 := Real.sq_sqrt hx1
      have a0 := Real.sq_sqrt hx0
      nlinarith [sq_nonneg (Real.sqrt x1 - Real.sqrt x0), Real.sqrt_nonneg x1, Real.sqrt_nonneg x0]
    have hkm : k * mg ≤ cb ^ 2 := by
      have := mul_le_mul hk' hmg' hmg hcb
      nlinarith
    exact mul_le_mul hkm hs (by positivity) (by positivity)
  have tt := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)
  refine tt.trans ?_
  nlinarith [mul_nonneg hcb hx1, mul_nonneg hcb hx0, mul_nonneg (pow_nonneg hcb 2) hx0, mul_nonneg (pow_nonneg hcb 2) hx1]

theorem loss_le_gapValue (st cc gc vc mg wg len xo x1 x0 k : ℝ) (hxo : 0 ≤ xo) (hx1 : 0 ≤ x1)
    (hx0 : 0 ≤ x0) (hcc : 0 ≤ cc) (hgc : 0 ≤ gc) (hvc : 0 ≤ vc) (hmg : 0 ≤ mg) (hwg : 0 ≤ wg)
    (hlen : 0 < len) (hk : Real.sqrt (7 / 2) ≤ k) :
    st * xo + Real.sqrt (7 / 2) / 2 * wg * (len * x1 + x0 / len)
        + Real.sqrt (7 / 2) * mg * (Real.sqrt x1 * Real.sqrt x0)
      ≤ gapValue st cc gc vc mg wg len xo x1 x0 k := by
  unfold gapValue
  rw [Real.sq_sqrt hxo, Real.sq_sqrt hx1, Real.sq_sqrt hx0]
  set κ := Real.sqrt (7 / 2)
  have hδ : 0 ≤ k - κ := by linarith
  have hli : 0 ≤ len⁻¹ := inv_nonneg.2 hlen.le
  have e : (st + cc) * xo + (k * wg * len / 2 + gc) * x1 + (k * wg * len⁻¹ / 2 + vc) * x0
        + k * mg * (Real.sqrt x1 * Real.sqrt x0)
      - (st * xo + κ / 2 * wg * (len * x1 + x0 / len) + κ * mg * (Real.sqrt x1 * Real.sqrt x0))
      = cc * xo + gc * x1 + vc * x0 + (k - κ) / 2 * wg * len * x1 + (k - κ) / 2 * wg * len⁻¹ * x0
        + (k - κ) * mg * (Real.sqrt x1 * Real.sqrt x0) := by
    rw [div_eq_mul_inv x0 len]; ring
  have : 0 ≤ cc * xo + gc * x1 + vc * x0 + (k - κ) / 2 * wg * len * x1 + (k - κ) / 2 * wg * len⁻¹ * x0
        + (k - κ) * mg * (Real.sqrt x1 * Real.sqrt x0) := by
    have a1 : 0 ≤ (k - κ) / 2 * wg * len * x1 := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hδ zero_le_two) hwg) hlen.le) hx1; exact this
    have a2 : 0 ≤ (k - κ) / 2 * wg * len⁻¹ * x0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hδ zero_le_two) hwg) hli) hx0
    have a3 : 0 ≤ (k - κ) * mg * (Real.sqrt x1 * Real.sqrt x0) :=
      mul_nonneg (mul_nonneg hδ hmg) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have := mul_nonneg hcc hxo
    have := mul_nonneg hgc hx1
    have := mul_nonneg hvc hx0
    linarith
  linarith


theorem integrable_of_pos_neg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total 0 (f x) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h), add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  simp_rw [e]
  rw [lintegral_add_left' hf.aemeasurable.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨hp.lt_top, hn.lt_top⟩

theorem density_gap {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (q : Fin k → ℝ)
    (mc : ModeCharges) (ec : TailBand.EntryCharges) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    D.labelDensity q v G H ι p - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn mc ec D.azimuthOrder ι v G H p
      = gapValue (mc.curl ι p) (ec.curlCharge p) (ec.gradCharge p) (ec.velCharge p) (mc.product ι p)
          (mc.gradient ι p) (mc.length ι p) (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)))
          (cnormSq (labelGrad D.azimuthOrder ι G p)) (cnormSq (labelVel D.azimuthOrder ι v p)) ec.stretchConst := by
  unfold CellLayerData.labelDensity
  rw [TailBand.modeTerm_eq_labelQuad]
  simp only [TailBand.offModeDensity, TailBand.labelQuad, TailBand.PointCoef.quad, TailBand.PointCoef.withStretch,
    gapValue]
  ring

theorem aemeasurable_gapValue {μ : Measure (ℝ × ℝ)} {st cc gc vc mg wg len xo x1 x0 : ℝ × ℝ → ℝ} (c : ℝ)
    (hst : AEMeasurable st μ) (hcc : AEMeasurable cc μ) (hgc : AEMeasurable gc μ) (hvc : AEMeasurable vc μ)
    (hmg : AEMeasurable mg μ) (hwg : AEMeasurable wg μ) (hlen : AEMeasurable len μ)
    (hxo : AEMeasurable xo μ) (hx1 : AEMeasurable x1 μ) (hx0 : AEMeasurable x0 μ) :
    AEMeasurable (fun p => gapValue (st p) (cc p) (gc p) (vc p) (mg p) (wg p) (len p) (xo p) (x1 p) (x0 p) c) μ := by
  have hs : ∀ {u : ℝ × ℝ → ℝ}, AEMeasurable u μ → AEMeasurable (fun p => Real.sqrt (u p)) μ :=
    fun h => Real.continuous_sqrt.measurable.comp_aemeasurable h
  unfold gapValue
  refine ((((hst.add hcc).mul ((hs hxo).pow_const 2)).add ?_).add ?_).add ?_
  · exact ((((aemeasurable_const.mul hwg).mul hlen).div_const 2).add hgc).mul ((hs hx1).pow_const 2)
  · exact ((((aemeasurable_const.mul hwg).mul hlen.inv).div_const 2).add hvc).mul ((hs hx0).pow_const 2)
  · exact (aemeasurable_const.mul hmg).mul ((hs hx1).mul (hs hx0))

theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem max_sub_max (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring

theorem point_ennreal {d : ℤ × ℤ → ℝ} (hd : Summable d) {sp sn : ℝ≥0∞} {r : ℝ} (hr : 0 < r)
    (hsn : sn ≠ ⊤) (hkey : sp ≠ ⊤ → sn.toReal - sp.toReal ≤ ∑' ι, d ι) :
    sn * ENNReal.ofReal r + ∑' ι, ENNReal.ofReal (-(d ι * r))
      ≤ sp * ENNReal.ofReal r + ∑' ι, ENNReal.ofReal (d ι * r) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr
  by_cases hsp : sp = ⊤
  · rw [hsp, ENNReal.top_mul hr0, top_add]; exact le_top
  have hdr : Summable fun ι => d ι * r := hd.mul_right r
  have hs1 : Summable fun ι => max (d ι * r) 0 :=
    Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
      (fun ι => max_le (le_abs_self _) (abs_nonneg _)) hdr.abs
  have hs2 : Summable fun ι => max (-(d ι * r)) 0 :=
    Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
      (fun ι => max_le (neg_le_abs _) (abs_nonneg _)) hdr.abs
  have e1 : ∑' ι, ENNReal.ofReal (d ι * r) = ENNReal.ofReal (∑' ι, max (d ι * r) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => le_max_right _ _) hs1]
    simp only [ofReal_max_zero]
  have e2 : ∑' ι, ENNReal.ofReal (-(d ι * r)) = ENNReal.ofReal (∑' ι, max (-(d ι * r)) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => le_max_right _ _) hs2]
    simp only [ofReal_max_zero]
  have e3 : sn * ENNReal.ofReal r = ENNReal.ofReal (sn.toReal * r) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hsn]
  have e4 : sp * ENNReal.ofReal r = ENNReal.ofReal (sp.toReal * r) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hsp]
  have hP0 : 0 ≤ ∑' ι, max (d ι * r) 0 := tsum_nonneg fun _ => le_max_right _ _
  have hN0 : 0 ≤ ∑' ι, max (-(d ι * r)) 0 := tsum_nonneg fun _ => le_max_right _ _
  rw [e1, e2, e3, e4, ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hr.le) hN0,
    ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hr.le) hP0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdiff : ∑' ι, max (d ι * r) 0 - ∑' ι, max (-(d ι * r)) 0 = (∑' ι, d ι) * r := by
    rw [← hs1.tsum_sub hs2, ← tsum_mul_right]
    congr 1
    funext ι
    exact max_sub_max _
  have hk := hkey hsp
  have hk' : (sn.toReal - sp.toReal) * r ≤ (∑' ι, d ι) * r := mul_le_mul_of_nonneg_right hk hr.le
  nlinarith

theorem ae_summable_of_lintegral {μ : Measure (ℝ × ℝ)} {f : ℤ × ℤ → ℝ × ℝ → ℝ}
    (hf0 : ∀ᵐ p ∂μ, ∀ ι, 0 ≤ f ι p) (hm : ∀ ι, AEMeasurable (fun p => ENNReal.ofReal (f ι p)) μ)
    (hfin : ∑' ι, ∫⁻ p, ENNReal.ofReal (f ι p) ∂μ ≠ ⊤) : ∀ᵐ p ∂μ, Summable fun ι => f ι p := by
  rw [← lintegral_tsum hm] at hfin
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hm) hfin, hf0] with p hp h0
  refine (ENNReal.summable_toReal hp.ne).congr fun ι => ?_
  exact ENNReal.toReal_ofReal (h0 ι)

end Internal.ExteriorStretch

namespace Internal.ExteriorStretch

theorem gradOf_pairVec (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    gradOf (pairVec s w) = fun ab => s ab.1 ab.2 := by
  funext ab
  rcases ab with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem velOf_pairVec (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) : velOf (pairVec s w) = w := by
  funext a
  fin_cases a <;> rfl

theorem gradOf_bandProfile {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    gradOf (bandProfile D ι v G p) = labelGrad D.azimuthOrder ι G p := by
  unfold bandProfile
  rw [gradOf_pairVec]
  rfl

theorem velOf_bandProfile {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    velOf (bandProfile D ι v G p) = labelVel D.azimuthOrder ι v p := by
  unfold bandProfile
  rw [velOf_pairVec]
  rfl

theorem meanStretch_eq_parts {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ)
    (hp : AEStronglyMeasurable (fun y : ℝ × ℝ =>
        CoerciveWeak.stretchFormWith D.given D.givenHess v G y.1 (axialRot y.2 (planePoint p)))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))))
    (hP : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p))) ≠ ⊤)
    (hN : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p))) ≠ ⊤) :
    D.meanStretch v G p = (1 / (2 * Real.pi)) *
      ((∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))).toReal
        - (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))).toReal) := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have eP := (lintegral_prod (fun y : ℝ × ℝ => ENNReal.ofReal
      (CoerciveWeak.stretchFormWith D.given D.givenHess v G y.1 (axialRot y.2 (planePoint p))))
    hp.aemeasurable.ennreal_ofReal).symm
  have eN := (lintegral_prod (fun y : ℝ × ℝ => ENNReal.ofReal
      (-CoerciveWeak.stretchFormWith D.given D.givenHess v G y.1 (axialRot y.2 (planePoint p))))
    hp.aemeasurable.neg.ennreal_ofReal).symm
  rw [eP] at hP ⊢
  rw [eN] at hN ⊢
  have hint := integrable_of_pos_neg hp hP hN
  have hval := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  rw [integral_prod _ hint] at hval
  unfold CellLayerData.meanStretch
  simp only [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le h2pi,
    ← integral_Icc_eq_integral_Ioc]
  rw [hval]

end Internal.ExteriorStretch

namespace Internal.ExteriorStretch

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal Coercive.RotationInternal

theorem decay_const_nonneg {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) : 0 ≤ B := by
  have h := (hW.decay 0 0).1
  rw [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem phase_neg_star (β : ℤ × ℤ) (τ φ : ℝ) : phase (-β) τ φ = (starRingEnd ℂ) (phase β τ φ) := by
  simp only [phase, waveArg]
  exact Coercive.Internal.MuSmooth.phase_neg β τ φ

theorem givenGrad_frame {S : Finset (ℤ × ℤ)} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ} (hE : Bridge.IsHarmonicExpansion S W HW)
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) (y : Space) (τ φ : ℝ) (a b : Fin 3) :
    ((fibGrad (gradField W) y τ φ a b : ℝ) : ℂ) = ∑ β ∈ S, phase β τ φ * modeGrad β (gradField W) 0 y (a, b) := by
  have hB := decay_const_nonneg hW
  have hgper : IsTimePeriodic (gradField W) := by
    intro σ z
    have e : W (σ + 1) = W σ := funext (hW.periodic σ)
    simp only [gradField, e]
  have hcont := continuous_gradField hW.smooth
  rw [frameGrad_expansion hE hgper y (fun τ' φ' x => ?_) τ φ a b]
  · refine Coercive.Internal.MuSmooth.re_sum_sym S hE.symmetric _ fun β => ?_
    rw [map_mul, phase_neg_star, Coercive.Internal.MuSmooth.modeGrad_neg]
  · have hc : Continuous (fun θ : ℝ × ℝ => gradField W (τ' + θ.1) (axialRot θ.2 (axialRot φ' y))) := by
      refine hcont.comp (f := fun θ : ℝ × ℝ => ((τ' + θ.1, axialRot θ.2 (axialRot φ' y)) : ℝ × Space)) ?_
      unfold axialRot
      fun_prop
    have h := integrable_shift_grad _ hc.aestronglyMeasurable B (fun θ => ?_) (0, 0) x
    · simpa only [add_zero] using h
    · refine (hW.decay _ _).2.1.trans (div_le_self hB (one_le_pow₀ ?_))
      linarith [norm_nonneg (axialRot θ.2 (axialRot φ' y))]

theorem givenSecond_frame {S : Finset (ℤ × ℤ)} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ} (hE : Bridge.IsHarmonicExpansion S W HW)
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) :
    ∀ᵐ p ∂(volume.restrict halfPlane), ∀ (τ φ : ℝ) (a b c : Fin 3),
      ((frameSecondDeriv HW (planePoint p) τ φ a b c : ℝ) : ℂ)
        = ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 (planePoint p) (a, b, c) := by
  have hB := decay_const_nonneg hW
  filter_upwards [ae_aestronglyMeasurable_orbit (u := fun z : ℝ × Space => HW z.1 z.2)
    hW.secondDeriv_measurable] with p hp τ φ a b c
  rw [frameSecondDeriv_expansion hE hW.secondDeriv_periodic (planePoint p) (fun τ' φ' x => ?_) τ φ a b c]
  · refine Coercive.Internal.MuSmooth.re_sum_sym S hE.symmetric _ fun β => ?_
    rw [map_mul, phase_neg_star]
    congr 1
    unfold modeSecondDeriv
    exact Coercive.Internal.MuSmooth.modeAverage_neg _ _ _
  · have h := integrable_shift_secondDeriv (fun θ : ℝ × ℝ => HW θ.1 (axialRot θ.2 (planePoint p))) hp B
      (fun θ => ?_) (τ', φ') x
    · refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Coercive.RotationInternal.axialRot_add]
      rw [add_comm θ.1 τ']
    · refine (hW.decay _ _).2.2.trans (div_le_self hB (one_le_pow₀ ?_))
      linarith [norm_nonneg (axialRot θ.2 (planePoint p))]

theorem inner_strain_eq (W : ℝ → Space → Space) (σ : ℝ) (y u : Space) :
    inner ℝ (strainOf W σ y u) u = inner ℝ u (gradField W σ y u) := by
  have h1 : inner ℝ u ((ContinuousLinearMap.adjoint (fderiv ℝ (W σ) y)) u) = inner ℝ u (fderiv ℝ (W σ) y u) := by
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  rw [real_inner_comm]
  simp only [strainOf, gradField]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_right, inner_add_right, h1]
  ring

theorem cnormSq_pairVec (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    cnormSq (pairVec s w) = cnormSq (fun ab : Fin 3 × Fin 3 => s ab.1 ab.2) + cnormSq w := by
  unfold cnormSq
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [pairVec]
  ring

end Internal.ExteriorStretch

namespace Internal.ExteriorStretch

theorem ae_mode_summable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (m : ℕ) (hm1 : 1 ≤ m) :
    ∀ᵐ p ∂(volume.restrict halfPlane), Summable (fun ι => cnormSq (labelGrad m ι G p)) ∧
      Summable (fun ι => cnormSq (labelVel m ι v p)) := by
  have hposH : ∀ᵐ p ∂(volume.restrict halfPlane), 0 < p.1 := by
    filter_upwards [ae_restrict_mem Bridge.Internal.StretchMeanParts.measurableSet_halfPlane] with p hp
    exact hp.1
  have hgs : ∀ᵐ p ∂(volume.restrict halfPlane),
      Summable fun ι => cnormSq (labelGrad m ι G p) * p.1 := by
    refine ae_summable_of_lintegral ?_ (fun ι => ?_) (Internal.FormNegative.gradient_sum_lt_top _ hm1 hv).ne
    · filter_upwards [hposH] with p hp ι
      exact mul_nonneg (cnormSq_nonneg' _) hp.le
    · obtain ⟨-, hLG, -⟩ := TailBand.aestronglyMeasurable_labelFields hv m ι
      exact ((Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable hLG).aemeasurable.mul
        measurable_fst.aemeasurable).ennreal_ofReal
  have hvs : ∀ᵐ p ∂(volume.restrict halfPlane),
      Summable fun ι => cnormSq (labelVel m ι v p) / (p.1 ^ 2 + p.2 ^ 2) * p.1 := by
    refine ae_summable_of_lintegral ?_ (fun ι => ?_)
      (Internal.FormNegative.velocity_inverse_sum_lt_top _ hm1 hv).ne
    · filter_upwards [hposH] with p hp ι
      exact mul_nonneg (div_nonneg (cnormSq_nonneg' _) (by positivity)) hp.le
    · obtain ⟨hLV, -, -⟩ := TailBand.aestronglyMeasurable_labelFields hv m ι
      refine (((Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable hLV).aemeasurable.div
        ?_).mul measurable_fst.aemeasurable).ennreal_ofReal
      exact ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).aemeasurable
  filter_upwards [hposH, hgs, hvs] with p hr hpg hpv
  have hr2 : 0 < p.1 ^ 2 + p.2 ^ 2 := by positivity
  exact ⟨(hpg.mul_right p.1⁻¹).congr fun ι => by field_simp,
    (hpv.mul_right ((p.1 ^ 2 + p.2 ^ 2) / p.1)).congr fun ι => by field_simp⟩

end Internal.ExteriorStretch

end Assembly

end CertCell

end Breakdown
