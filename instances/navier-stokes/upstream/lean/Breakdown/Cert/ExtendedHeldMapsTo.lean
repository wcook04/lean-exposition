import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldMapsTo

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedHeldMapsTo

open Internal.HeldMapsTo

theorem size_arith_rows {Z cL cP N R vn dB dR A ρ cT rB af r : ℝ}
    (hZ : Z ≤ cL * N + R + cP * vn) (hN : N ≤ dB + A) (hR : R ≤ dR + rB * A)
    (hcL : 0 ≤ cL) (hsize : cL * dB + dR + cP * vn ≤ ρ)
    (hT : cL + rB ≤ cT) (hcT : 0 < cT) (hA0 : 0 ≤ A) (hA : A ≤ af * (2 * ρ) * r)
    (hsmall : 2 * cT * af * r < 1) (hρ : 0 ≤ ρ) : Z ≤ 2 * ρ := by
  have h1 := mul_le_mul_of_nonneg_left hN hcL
  have h3 : (cL + rB) * A ≤ cT * A := mul_le_mul_of_nonneg_right hT hA0
  have h4 : cT * A ≤ cT * (af * (2 * ρ) * r) := mul_le_mul_of_nonneg_left hA hcT.le
  have h5 : ρ * (2 * cT * af * r) ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsmall.le hρ
  have e : cT * (af * (2 * ρ) * r) = ρ * (2 * cT * af * r) := by ring
  linarith

theorem neg_periodic {F : ℝ → Space → Space} (h : IsPeriodicField F) :
    IsPeriodicField (fun σ y => -F σ y) := by
  refine ⟨h.1.neg, fun σ y => by simp only [h.2.1 σ y], ?_⟩
  simp only [norm_neg]
  exact h.2.2

theorem rows_neg_sub_le (h9 : RowNormHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hc : IsExtendedCertificate d) {D Pf : ℝ → Space → Space} (hD : IsPeriodicField D)
    (hP : IsPeriodicField Pf) :
    d.rows (fun σ y => -D σ y - Pf σ y) ≤ d.rows D + d.rowBound * periodNorm Pf := by
  have he : ∀ a, IsPeriodicField (d.rowField a) := fun a =>
    ⟨hc.rowField_measurable a, hc.rowField_periodic a, hc.rowField_finite a⟩
  have hR := h9 d.rowField d.rowWeight d.rowBound he hc.rowField_orthonormal hc.rowWeight_nonneg
    hc.rowWeight_le hc.rowBound_nonneg
  have e : (fun σ y => -D σ y - Pf σ y) = fun σ y => -D σ y + -Pf σ y := by
    funext σ y
    exact sub_eq_add_neg _ _
  have h1 := (hR (fun σ y => -D σ y) (fun σ y => -Pf σ y) (neg_periodic hD) (neg_periodic hP)).1
  have h2 := (hR D D hD hD).2.1
  have h3 := (hR Pf Pf hP hP).2.1
  have h4 := (hR Pf Pf hP hP).2.2
  unfold ExtendedCertificateData.rows
  rw [e]
  calc rowNorm d.rowField d.rowWeight (fun σ y => -D σ y + -Pf σ y)
      ≤ rowNorm d.rowField d.rowWeight (fun σ y => -D σ y)
        + rowNorm d.rowField d.rowWeight (fun σ y => -Pf σ y) := h1
    _ = rowNorm d.rowField d.rowWeight D + rowNorm d.rowField d.rowWeight Pf := by rw [h2, h3]
    _ ≤ rowNorm d.rowField d.rowWeight D + d.rowBound * periodNorm Pf := add_le_add le_rfl h4

theorem transferLoss_eq_zero {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsNormalExtendedCertificate d) : d.transferLoss = 0 := by
  unfold ExtendedCertificateData.transferLoss
  rw [hd.gap_zero, mul_zero]

theorem step_bounds (h2 : ExtendedCoerciveBorderedHolds) (h3 : ExtendedSupBoundHolds)
    (h9 : RowNormHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsNormalExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) (u : XX)
    (f : HH) (κ : Fin k → ℝ) (Pf : ℝ → Space → Space) (A : ℝ)
    (hf : f ∈ invariantHH d.symmetries)
    (hb : bordered d.toCertificateData q (f, κ) = d.heldRight q u)
    (hDF : IsPeriodicField (d.defect q)) (hPF : IsPeriodicField Pf)
    (hprodN : periodNorm Pf ≤ A) (hprodH : ‖productH u u‖ ≤ A) (hA0 : 0 ≤ A)
    (hAle : A ≤ supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound)
    (hdat1 : ∀ φ, IsSpaceTimeTestField φ → inner ℝ (d.defectH q) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2))
    (hdat2 : ‖d.defectH q‖ ≤ d.defectBound q)
    (h5 : ∀ φ, IsSpaceTimeTestField φ → inner ℝ (productH u u) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (Pf z.1 z.2) (φ z.1 z.2)) :
    sizeZ d.weightFn (freeInv (d.period q) f) κ ≤ 2 * d.sizeBound ∧
      supGrad (freeInv (d.period q) f) ≤ ENNReal.ofReal d.supBound := by
  have hc := hd.certificate
  have hP := hc.period_pos q hq
  have hw : ∀ y, 0 ≤ d.weightFn y := fun y => hc.weight_pos.le.trans (hc.weightFn_lower y)
  have hsup0 := hc.supBound_pos
  have hρ := hc.sizeBound_nonneg
  have hloss := transferLoss_eq_zero hd
  have hFP := neg_sub_periodic hDF hPF
  have hb1 : (bordered d.toCertificateData q (f, κ)).1 = -(d.defectH q) - productH u u :=
    congrArg Prod.fst hb
  have hpair : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (-d.defect q z.1 z.2 - Pf z.1 z.2) (φ z.1 z.2) =
        inner ℝ (bordered d.toCertificateData q (f, κ)).1 (testInHH φ) := by
    intro φ hφ
    have i1 := Internal.CoerciveBordered.integrable_inner_of_periodic hDF.1 hDF.2.1 hDF.2.2
      (Internal.CoerciveBordered.continuous_test hφ) hφ.2.1
    have i2 := Internal.CoerciveBordered.integrable_inner_of_periodic hPF.1 hPF.2.1 hPF.2.2
      (Internal.CoerciveBordered.continuous_test hφ) hφ.2.1
    have e : (fun z : ℝ × Space => inner ℝ (-d.defect q z.1 z.2 - Pf z.1 z.2) (φ z.1 z.2))
        = fun z => -(inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2)
          + inner ℝ (Pf z.1 z.2) (φ z.1 z.2)) := by
      funext z
      rw [inner_sub_left, inner_neg_left]
      ring
    have e2 : inner ℝ (bordered d.toCertificateData q (f, κ)).1 (testInHH φ) =
        -(inner ℝ (d.defectH q) (testInHH φ)) - inner ℝ (productH u u) (testInHH φ) :=
      (congrArg (fun v : HH => inner ℝ v (testInHH φ)) hb1).trans
        ((inner_sub_left (𝕜 := ℝ) (-(d.defectH q)) (productH u u) (testInHH φ)).trans
          (congrArg (fun a : ℝ => a - inner ℝ (productH u u) (testInHH φ))
            (inner_neg_left (𝕜 := ℝ) (d.defectH q) (testInHH φ))))
    have e3 : ∫ z : ℝ × Space, inner ℝ (-d.defect q z.1 z.2 - Pf z.1 z.2) (φ z.1 z.2) =
        -(inner ℝ (d.defectH q) (testInHH φ) + inner ℝ (productH u u) (testInHH φ)) :=
      (congrArg (fun g : ℝ × Space → ℝ => ∫ z, g z) e).trans ((integral_neg _).trans
        (congrArg Neg.neg ((integral_add i1 i2).trans
          (congrArg₂ (fun a b : ℝ => a + b) (hdat1 φ hφ).symm (h5 φ hφ).symm))))
    exact e3.trans ((neg_add' _ _).trans e2.symm)
  have hcoer := h2 d hd q hq f hf κ (fun σ y => -d.defect q σ y - Pf σ y) hFP.1 hpair
  have hpin : pinMap d.toCertificateData (freeInv (d.period q) f) = d.targetGap q :=
    (bordered_snd d.toCertificateData q f κ).symm.trans (congrArg Prod.snd hb)
  have hsz0 := hc.size q hq
  rw [hloss, sub_zero, one_mul] at hsz0
  have hsz : d.coerciveL2 * d.defectBound q + d.defectRowBound q
      + d.coercivePin * vecNorm (pinMap d.toCertificateData (freeInv (d.period q) f)) ≤
        d.sizeBound := by
    rw [hpin]
    exact hsz0
  have hT : d.coerciveL2 + d.rowBound ≤ d.coerciveTotal := by
    have h := hc.coerciveTotal_ge
    rw [hloss, sub_zero, one_mul] at h
    exact h
  have hDn : periodNorm (d.defect q) ≤ d.defectBound q :=
    periodNorm_le_of (hc.defect_nonneg q hq).1 (hc.defect_l2 q hq)
  have hN : periodNorm (fun σ y => -d.defect q σ y - Pf σ y) ≤ d.defectBound q + A :=
    hFP.2.trans (add_le_add hDn hprodN)
  have hR : d.rows (fun σ y => -d.defect q σ y - Pf σ y) ≤ d.defectRowBound q + d.rowBound * A :=
    (rows_neg_sub_le h9 hc hDF hPF).trans (add_le_add (hc.defect_rows q hq)
      (mul_le_mul_of_nonneg_left hprodN hc.rowBound_nonneg))
  have hZ : sizeZ d.weightFn (freeInv (d.period q) f) κ ≤ 2 * d.sizeBound :=
    size_arith_rows hcoer hN hR hc.coerciveL2_nonneg hsz hT hc.coerciveTotal_pos hA0 hAle
      hc.small_first hρ
  refine ⟨hZ, ?_⟩
  have hSB := h3 d hc q hq f hf κ
  have hlt := hSB.1
  have hsq := hSB.2
  have hn : ‖-(d.defectH q) - productH u u‖ ≤ ‖d.defectH q‖ + ‖productH u u‖ :=
    (norm_sub_le _ _).trans_eq (congrArg (fun a : ℝ => a + ‖productH u u‖) (norm_neg (d.defectH q)))
  have hAe : supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound =
      2 * supBoundFactor d.weight * d.sizeBound * d.supBound := by ring
  have hB : ‖(bordered d.toCertificateData q (f, κ)).1‖ ≤
      d.defectMax + 2 * supBoundFactor d.weight * d.sizeBound * d.supBound :=
    (congrArg norm hb1).trans_le (hn.trans (add_le_add (hdat2.trans (hc.defect_le q hq))
      (hprodH.trans (hAle.trans_eq hAe))))
  have htw : (0 : ℝ) < d.twist := Nat.cast_pos.2 hc.twist_pos
  have hfb : 0 ≤ d.formBound :=
    (add_nonneg hc.modelFormBound_nonneg hc.formShift_nonneg).trans hc.formBound_ge
  have hq0 : 0 ≤ d.period q / d.twist := div_nonneg hP.le htw.le
  have hqm : d.period q / d.twist ≤ d.periodMax / d.twist :=
    div_le_div_of_nonneg_right (hc.period_le q hq) htw.le
  have hc0 : 0 ≤ 1 / d.weight + 2 * (d.period q / d.twist) * d.formBound :=
    add_nonneg (one_div_pos.2 hc.weight_pos).le
      (mul_nonneg (mul_nonneg zero_le_two hq0) hfb)
  have hcm : 1 / d.weight + 2 * (d.period q / d.twist) * d.formBound ≤
      1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqm zero_le_two) hfb)
  have hsmall := hc.small_third
  rw [hd.unit_weight, div_one] at hsmall
  have hS := sup_arith hc0 hcm (energyW_nonneg hw _) (energy_le_sq hw _ κ hZ) hq0 hqm
    (norm_nonneg _) hB hc.actuatorBound_nonneg (Real.sqrt_nonneg _)
    ((vecNorm_le_sizeZ hw _ κ).trans hZ) (Real.sqrt_nonneg _)
    ((sqrt_energy_le_sizeZ _ _ κ).trans hZ) hρ hsq hsmall
  have hle : (supGrad (freeInv (d.period q) f)).toReal ≤ d.supBound :=
    (sq_le_sq₀ ENNReal.toReal_nonneg hsup0.le).1 hS
  calc supGrad (freeInv (d.period q) f) =
        ENNReal.ofReal (supGrad (freeInv (d.period q) f)).toReal :=
        (ENNReal.ofReal_toReal hlt.ne).symm
    _ ≤ ENNReal.ofReal d.supBound := ENNReal.ofReal_le_ofReal hle

end Internal.ExtendedHeldMapsTo

open Internal.HeldMapsTo Internal.ExtendedHeldMapsTo

theorem extendedHeldMapsToHolds_of (h1 : ExtendedBorderedInvertibleHolds)
    (h2 : ExtendedCoerciveBorderedHolds) (h3 : ExtendedSupBoundHolds) (h4 : ProductBoundHolds)
    (h5 : ProductPairingHolds) (h6 : ExtendedDataHolds) (h7 : ExtendedInvarianceHolds)
    (h8 : FreeEquivariantHolds) (h9 : RowNormHolds) : ExtendedHeldMapsToHolds := by
  intro k d hd q hq x hx
  have hc := hd.certificate
  simp only [heldSet, Set.mem_ofPred_eq] at hx
  obtain ⟨hxi, hxs, hxg⟩ := hx
  have hP := hc.period_pos q hq
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hc.weight_pos, hc.weightFn_measurable, hc.weightFn_lower, d.weightMax, hc.weightFn_upper⟩
  have hsup0 := hc.supBound_pos
  have hρ := hc.sizeBound_nonneg
  have hfin : supGrad x.1 < ⊤ := lt_of_le_of_lt hxg ENNReal.ofReal_lt_top
  have hsupu : (supGrad x.1).toReal ≤ d.supBound := ENNReal.toReal_le_of_le_ofReal hsup0.le hxg
  have hEu : Real.sqrt (energyW d.weightFn x.1) ≤ 2 * d.sizeBound :=
    (sqrt_energy_le_sizeZ _ _ x.2).trans hxs
  have haf : 0 ≤ supBoundFactor d.weight := by
    unfold supBoundFactor
    positivity
  obtain ⟨hprodF, hprodN, hprodH⟩ := h4 d.weightFn d.weight hadm x.1 x.1 hfin
  have hA0 : 0 ≤ supBoundFactor d.weight * Real.sqrt (energyW d.weightFn x.1) *
      (supGrad x.1).toReal :=
    mul_nonneg (mul_nonneg haf (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
  have hAle : supBoundFactor d.weight * Real.sqrt (energyW d.weightFn x.1) * (supGrad x.1).toReal ≤
      supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound :=
    mul_le_mul (mul_le_mul_of_nonneg_left hEu haf) hsupu ENNReal.toReal_nonneg
      (mul_nonneg haf (by linarith))
  obtain ⟨hinv1, -, hinv3⟩ := h7 d hc q hq
  have hyinv : (d.heldRight q x.1).1 ∈ invariantHH d.symmetries :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hinv3) (hinv1 x.1 hxi).2
  have hspec := borderedInv_spec (h1 d hd q hq).1 (d.heldRight q x.1) hyinv
  suffices H : ∀ z : HH × (Fin k → ℝ), z.1 ∈ invariantHH d.symmetries →
      bordered d.toCertificateData q z = d.heldRight q x.1 →
        (freeInv (d.period q) z.1, z.2) ∈ heldSet d.toCertificateData by
    exact H (borderedInv d.toCertificateData q (d.heldRight q x.1)) hspec.1 hspec.2
  intro z hz hb
  obtain ⟨f, κ⟩ := z
  have hf : f ∈ invariantHH d.symmetries := hz
  clear hz hspec
  simp only [heldSet, Set.mem_ofPred_eq]
  have hdat := h6 d hc q hq
  have hDF := hdat.1
  have hdat1 := hdat.2.1
  have hdat2 := hdat.2.2.1
  have hSB := step_bounds h2 h3 h9 hd hq x.1 f κ (productField x.1 x.1)
    (supBoundFactor d.weight * Real.sqrt (energyW d.weightFn x.1) * (supGrad x.1).toReal)
    hf hb hDF hprodF hprodN hprodH hA0 hAle hdat1 hdat2 (h5 x.1 x.1 hfin)
  exact ⟨h8 d.symmetries (d.period q) hP f hf, hSB.1, hSB.2⟩

end Breakdown.Cert
