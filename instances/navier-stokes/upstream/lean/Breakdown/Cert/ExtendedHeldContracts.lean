import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldContracts

open scoped ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedHeldContracts

variable {k : ℕ} (d : ExtendedCertificateData k)

theorem heldRight_sub_fst (q : Fin k → ℝ) (u u' : XX) :
    (d.heldRight q u).1 - (d.heldRight q u').1 = -(productH u u - productH u' u') := by
  show (-(d.defectH q) - productH u u) - (-(d.defectH q) - productH u' u') = _
  abel

theorem sub_fst_eq (q : Fin k → ℝ) {u u' : XX}
    (hsub : productH u u - productH u' u' = productH (u - u') u + productH u' (u - u'))
    {g g' : HH × (Fin k → ℝ)} (hg : bordered d.toCertificateData q g = d.heldRight q u)
    (hg' : bordered d.toCertificateData q g' = d.heldRight q u') :
    (bordered d.toCertificateData q (g.1 - g'.1, g.2 - g'.2)).1 =
      -(productH (u - u') u + productH u' (u - u')) :=
  calc (bordered d.toCertificateData q (g.1 - g'.1, g.2 - g'.2)).1
        = (bordered d.toCertificateData q g - bordered d.toCertificateData q g').1 :=
        congrArg Prod.fst (HeldContracts.bordered_sub d.toCertificateData q g g')
    _ = (bordered d.toCertificateData q g).1 - (bordered d.toCertificateData q g').1 :=
        Prod.fst_sub _ _
    _ = (d.heldRight q u).1 - (d.heldRight q u').1 := congrArg₂ (fun a b => a.1 - b.1) hg hg'
    _ = -(productH u u - productH u' u') := heldRight_sub_fst d q u u'
    _ = -(productH (u - u') u + productH u' (u - u')) := congrArg Neg.neg hsub

theorem sub_pin_eq (q : Fin k → ℝ) {u u' : XX} {g g' : HH × (Fin k → ℝ)}
    (hg : bordered d.toCertificateData q g = d.heldRight q u)
    (hg' : bordered d.toCertificateData q g' = d.heldRight q u') :
    pinMap d.toCertificateData (freeInv (d.period q) (g.1 - g'.1)) = 0 :=
  calc pinMap d.toCertificateData (freeInv (d.period q) (g.1 - g'.1))
        = (bordered d.toCertificateData q (g.1 - g'.1, g.2 - g'.2)).2 :=
        (HeldContracts.bordered_snd d.toCertificateData q (g.1 - g'.1, g.2 - g'.2)).symm
    _ = (bordered d.toCertificateData q g - bordered d.toCertificateData q g').2 :=
        congrArg Prod.snd (HeldContracts.bordered_sub d.toCertificateData q g g')
    _ = (bordered d.toCertificateData q g).2 - (bordered d.toCertificateData q g').2 :=
        Prod.snd_sub _ _
    _ = (d.heldRight q u).2 - (d.heldRight q u').2 := congrArg₂ (fun a b => a.2 - b.2) hg hg'
    _ = d.targetGap q - d.targetGap q := rfl
    _ = 0 := sub_self _

theorem transferLoss_eq_zero (hN : IsNormalExtendedCertificate d) : d.transferLoss = 0 := by
  unfold ExtendedCertificateData.transferLoss
  rw [hN.gap_zero, mul_zero]

theorem coerciveSum_le (hN : IsNormalExtendedCertificate d) :
    d.coerciveL2 + d.rowBound ≤ d.coerciveTotal := by
  have h := hN.certificate.coerciveTotal_ge
  rwa [transferLoss_eq_zero d hN, sub_zero, one_mul] at h

theorem formBound_nonneg (hd : IsExtendedCertificate d) : 0 ≤ d.formBound :=
  (add_nonneg hd.modelFormBound_nonneg hd.formShift_nonneg).trans hd.formBound_ge

theorem coercive_part (hRow : RowNormHolds) (hN : IsNormalExtendedCertificate d)
    {F : ℝ → Space → Space} (hF : IsPeriodicField F) {Z φb : ℝ} (hFn : periodNorm F ≤ φb)
    {v : Fin k → ℝ} (hv : v = 0)
    (hZ0 : Z ≤ d.coerciveL2 * periodNorm F + d.rows F + d.coercivePin * vecNorm v) :
    Z ≤ d.coerciveTotal * φb := by
  have hd := hN.certificate
  have hrow : d.rows F ≤ d.rowBound * periodNorm F :=
    (hRow d.rowField d.rowWeight d.rowBound
      (fun a => ⟨hd.rowField_measurable a, hd.rowField_periodic a, hd.rowField_finite a⟩)
      hd.rowField_orthonormal hd.rowWeight_nonneg hd.rowWeight_le hd.rowBound_nonneg
      F F hF hF).2.2
  subst hv
  rw [HeldContracts.vecNorm_zero k, mul_zero, add_zero] at hZ0
  have hn := HeldContracts.periodNorm_nonneg F
  have hge := coerciveSum_le d hN
  calc Z ≤ d.coerciveL2 * periodNorm F + d.rows F := hZ0
    _ ≤ d.coerciveL2 * periodNorm F + d.rowBound * periodNorm F := add_le_add le_rfl hrow
    _ = (d.coerciveL2 + d.rowBound) * periodNorm F := (add_mul _ _ _).symm
    _ ≤ d.coerciveTotal * periodNorm F := mul_le_mul_of_nonneg_right hge hn
    _ ≤ d.coerciveTotal * φb := mul_le_mul_of_nonneg_left hFn hd.coerciveTotal_pos.le

theorem ratio_bound (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    (1 / d.weight + 2 * (d.period q / d.twist) * d.formBound)
        + 2 * (d.period q / d.twist) * d.actuatorBound + 2 * (d.period q / d.twist) / d.coerciveTotal
      ≤ (1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
        + 2 * (d.periodMax / d.twist) * d.actuatorBound
        + 2 * (d.periodMax / d.twist) / d.coerciveTotal := by
  have hT : (0 : ℝ) < d.twist := Nat.cast_pos.2 hd.twist_pos
  have hcm : 2 * (d.period q / d.twist) ≤ 2 * (d.periodMax / d.twist) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hd.period_le q hq) hT.le) zero_le_two
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hcm (formBound_nonneg d hd)))
    (mul_le_mul_of_nonneg_right hcm hd.actuatorBound_nonneg))
    (div_le_div_of_nonneg_right hcm hd.coerciveTotal_pos.le)

theorem small_second_unit (hN : IsNormalExtendedCertificate d) :
    4 * d.sizeBound ^ 2 * ((1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
      + 2 * (d.periodMax / d.twist) * d.actuatorBound
      + 2 * (d.periodMax / d.twist) / d.coerciveTotal) ≤ d.supBound ^ 2 := by
  have h := hN.certificate.small_second
  rwa [hN.unit_weight, div_one] at h

theorem sup_part (hN : IsNormalExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {v : XX} {κ : Fin k → ℝ} {f : HH} {φb : ℝ}
    (hS : (supGrad v).toReal ^ 2 ≤
      (1 / d.weight + 2 * (d.period q / d.twist) * d.formBound) * energyW d.weightFn v
        + 2 * (d.period q / d.twist) * (‖f‖ + d.actuatorBound * vecNorm κ)
          * Real.sqrt (energyW d.weightFn v))
    (hf : ‖f‖ ≤ φb) (hZ : sizeZ d.weightFn v κ ≤ d.coerciveTotal * φb) (hφ0 : 0 ≤ φb) :
    2 * d.sizeBound / d.supBound * (supGrad v).toReal ≤ d.coerciveTotal * φb := by
  have hd := hN.certificate
  have hw0 : ∀ z, 0 ≤ d.weightFn z := fun z => hd.weight_pos.le.trans (hd.weightFn_lower z)
  have hK : 0 < d.coerciveTotal := hd.coerciveTotal_pos
  have hT : (0 : ℝ) < d.twist := Nat.cast_pos.2 hd.twist_pos
  have hc : 0 ≤ d.period q / d.twist := (div_pos (hd.period_pos q hq) hT).le
  have hm : 0 ≤ 1 / d.weight + 2 * (d.period q / d.twist) * d.formBound :=
    add_nonneg (one_div_nonneg.2 hd.weight_pos.le)
      (mul_nonneg (mul_nonneg zero_le_two hc) (formBound_nonneg d hd))
  have hZ0 : 0 ≤ sizeZ d.weightFn v κ :=
    (Real.sqrt_nonneg _).trans (HeldContracts.sqrt_energyW_le_sizeZ d.weightFn v κ)
  have hVpos : 0 ≤ vecNorm κ := Real.sqrt_nonneg _
  have hs2 := HeldContracts.sq_bound hm hc hd.actuatorBound_nonneg hK hZ0
    (Real.sqrt_nonneg (energyW d.weightFn v)) hVpos (norm_nonneg f)
    (HeldContracts.energyW_le_sq hw0 v κ) (HeldContracts.sqrt_energyW_le_sizeZ d.weightFn v κ)
    (HeldContracts.vecNorm_le_sizeZ hw0 v κ) hf hZ hS
  exact HeldContracts.scaled_le hd.supBound_pos hd.sizeBound_nonneg ENNReal.toReal_nonneg
    (mul_nonneg hK.le hφ0) hs2 (ratio_bound d hd hq) (small_second_unit d hN)

theorem contract_core (h2 : ExtendedCoerciveBorderedHolds) (h3 : ExtendedSupBoundHolds)
    (h4 : ProductBoundHolds) (h5 : ProductPairingHolds) (h6 : ProductSubHolds)
    (hRow : RowNormHolds) (hN : IsNormalExtendedCertificate d) (q : Fin k → ℝ)
    (hq : q ∈ d.params) (x y : XX × (Fin k → ℝ)) (hxG : supGrad x.1 ≤ ENNReal.ofReal d.supBound)
    (hyS : sizeZ d.weightFn y.1 y.2 ≤ 2 * d.sizeBound)
    (hyG : supGrad y.1 ≤ ENNReal.ofReal d.supBound) (gx gy : HH × (Fin k → ℝ))
    (hgx1 : gx.1 ∈ invariantHH d.symmetries) (hgy1 : gy.1 ∈ invariantHH d.symmetries)
    (hgx2 : bordered d.toCertificateData q gx = d.heldRight q x.1)
    (hgy2 : bordered d.toCertificateData q gy = d.heldRight q y.1) :
    heldDist d.toCertificateData (freeInv (d.period q) gx.1, gx.2)
        (freeInv (d.period q) gy.1, gy.2) ≤
      2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound * heldDist d.toCertificateData x y := by
  have hd := hN.certificate
  have hw : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hAg : 0 ≤ supBoundFactor d.weight := by unfold supBoundFactor; positivity
  have hu : supGrad x.1 < ⊤ := lt_of_le_of_lt hxG ENNReal.ofReal_lt_top
  have hu' : supGrad y.1 < ⊤ := lt_of_le_of_lt hyG ENNReal.ofReal_lt_top
  have ha : supGrad (x.1 - y.1) < ⊤ := HeldContracts.supGrad_sub_lt_top hu hu'
  have hg1 : gx.1 - gy.1 ∈ invariantHH d.symmetries := Submodule.sub_mem _ hgx1 hgy1
  have hbg1 : (bordered d.toCertificateData q (gx.1 - gy.1, gx.2 - gy.2)).1 =
      -(productH (x.1 - y.1) x.1 + productH y.1 (x.1 - y.1)) :=
    sub_fst_eq d q (h6 x.1 y.1 hu hu').1 hgx2 hgy2
  have hpin : pinMap d.toCertificateData (freeInv (d.period q) (gx.1 - gy.1)) = 0 :=
    sub_pin_eq d q hgx2 hgy2
  have hEa : Real.sqrt (energyW d.weightFn (x.1 - y.1)) ≤ heldDist d.toCertificateData x y :=
    (HeldContracts.sqrt_energyW_le_sizeZ _ _ _).trans
      (HeldContracts.sizeZ_le_heldDist d.toCertificateData x y)
  have he0 : 0 ≤ heldDist d.toCertificateData x y := (Real.sqrt_nonneg _).trans hEa
  have hE' : Real.sqrt (energyW d.weightFn y.1) ≤ 2 * d.sizeBound :=
    (HeldContracts.sqrt_energyW_le_sizeZ _ _ y.2).trans hyS
  have hsu : (supGrad x.1).toReal ≤ d.supBound :=
    ENNReal.toReal_le_of_le_ofReal hd.supBound_pos.le hxG
  have hsa : 2 * d.sizeBound / d.supBound * (supGrad (x.1 - y.1)).toReal ≤
      heldDist d.toCertificateData x y :=
    HeldContracts.sup_le_heldDist d.toCertificateData x y
  have hb := HeldContracts.product_terms hAg hd.supBound_pos hEa hsa hE' hsu
  have hFper := HeldContracts.forcing_periodic h4 hw hu ha
  have hFnorm := HeldContracts.forcing_norm h4 hw hu ha hb.1 hb.2
  have hHnorm := HeldContracts.forcing_normH h4 hw hu ha hbg1 hb.1 hb.2
  have hZ0 := h2 d hN q hq (gx.1 - gy.1) hg1 (gx.2 - gy.2) _ hFper
    (HeldContracts.forcing_pairing h4 h5 hw hu ha hbg1)
  have hφ0 : 0 ≤ 2 * (supBoundFactor d.weight * d.supBound * heldDist d.toCertificateData x y) :=
    mul_nonneg zero_le_two (mul_nonneg (mul_nonneg hAg hd.supBound_pos.le) he0)
  have hZ := coercive_part d hRow hN hFper hFnorm hpin hZ0
  have hsup := sup_part d hN hq (h3 d hd q hq (gx.1 - gy.1) hg1 (gx.2 - gy.2)).2 hHnorm hZ hφ0
  have hfin : d.coerciveTotal * (2 * (supBoundFactor d.weight * d.supBound
      * heldDist d.toCertificateData x y)) =
      2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound
        * heldDist d.toCertificateData x y := by ring
  exact (HeldContracts.heldDist_step d.toCertificateData (d.period q) gx.1 gy.1 gx.2 gy.2).trans_le
    ((max_le hZ hsup).trans_eq hfin)

end Internal.ExtendedHeldContracts

theorem extendedHeldContractsHolds_of (h1 : ExtendedBorderedInvertibleHolds)
    (h2 : ExtendedCoerciveBorderedHolds) (h3 : ExtendedSupBoundHolds) (h4 : ProductBoundHolds)
    (h5 : ProductPairingHolds) (h6 : ProductSubHolds) (_h7 : ExtendedDataHolds)
    (h8 : ExtendedInvarianceHolds) (_h9 : FreeEquivariantHolds) (hRow : RowNormHolds) :
    ExtendedHeldContractsHolds := by
  intro k d hN q hq
  have hd := hN.certificate
  refine ⟨2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound, hd.small_first, ?_⟩
  intro x hx y hy
  obtain ⟨hxI, -, hxG⟩ := hx
  obtain ⟨hyI, hyS, hyG⟩ := hy
  have hE : ∃ T, BorderedInvSpec d.toCertificateData q T := (h1 d hN q hq).1
  have hspec : BorderedInvSpec d.toCertificateData q (borderedInv d.toCertificateData q) := by
    simp only [borderedInv, dif_pos hE]
    exact hE.choose_spec
  obtain ⟨hconv, -, hdef⟩ := h8 d hd q hq
  have hrx : (d.heldRight q x.1).1 ∈ invariantHH d.symmetries :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hdef) (hconv x.1 hxI).2
  have hry : (d.heldRight q y.1).1 ∈ invariantHH d.symmetries :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hdef) (hconv y.1 hyI).2
  obtain ⟨hgx1, hgx2⟩ := hspec _ hrx
  obtain ⟨hgy1, hgy2⟩ := hspec _ hry
  exact Internal.ExtendedHeldContracts.contract_core d h2 h3 h4 h5 h6 hRow hN q hq x y hxG hyS hyG
    _ _ hgx1 hgy1 hgx2 hgy2

end Breakdown.Cert
