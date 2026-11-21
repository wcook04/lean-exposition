import Breakdown.CertCell.ModeDensityBridgeLinksParts

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ModeDensityBridge

theorem lattice_reduction (hH : HalfPlaneReductionHolds) (hL : LabelArithmeticHolds) {mo : ℕ} (hmo : 1 ≤ mo)
    (K : ℤ × ℤ → Space → ℝ) (hK : ∀ ξ, AEStronglyMeasurable (K ξ) volume) (S : Set Space)
    (hSr : ∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) (hSa : ∀ᵐ y, y ∈ S)
    (hrot : ∀ ξ φ, ∀ y ∈ S, K ξ (axialRot φ y) = K ξ y)
    (hflip : ∀ ξ, ∀ᵐ y, K (flipLabel ξ) (flipPoint y) = K ξ y)
    (hzero : ∀ ξ, ¬ IsLatticeHarmonic mo ξ → ∀ᵐ y, K ξ y = 0) :
    ∫⁻ y, ∑' ξ, ENNReal.ofReal (K ξ y) = ENNReal.ofReal (4 * Real.pi) *
      ∑' ι, ∫⁻ p in halfPlane, ENNReal.ofReal (K (labelHarmonic mo ι) (planePoint p) * p.1) := by
  classical
  set g : ℤ × ℤ → Space → ℝ≥0∞ := fun ξ y => if IsLatticeHarmonic mo ξ then ENNReal.ofReal (K ξ y) else 0
    with hg
  have hon : ∀ ξ, IsLatticeHarmonic mo ξ → ∀ y, g ξ y = ENNReal.ofReal (K ξ y) := fun ξ hξ y => by
    simp only [hg, if_pos hξ]
  have hoff : ∀ ξ, ¬ IsLatticeHarmonic mo ξ → ∀ y, g ξ y = 0 := fun ξ hξ y => by
    simp only [hg, if_neg hξ]
  have step1 : ∫⁻ y, ∑' ξ, ENNReal.ofReal (K ξ y) = ∫⁻ y, ∑' ξ, g ξ y := by
    refine lintegral_congr_ae ?_
    have hall : ∀ᵐ y, ∀ ξ, ¬ IsLatticeHarmonic mo ξ → K ξ y = 0 := by
      rw [ae_all_iff]
      intro ξ
      by_cases hξ : IsLatticeHarmonic mo ξ
      · exact Filter.Eventually.of_forall fun y h => absurd hξ h
      · exact (hzero ξ hξ).mono fun y hy _ => hy
    filter_upwards [hall] with y hy
    refine tsum_congr fun ξ => ?_
    by_cases hξ : IsLatticeHarmonic mo ξ
    · rw [hon ξ hξ]
    · rw [hoff ξ hξ, hy ξ hξ, ENNReal.ofReal_zero]
  have hgm : ∀ ξ, AEMeasurable (g ξ) volume := by
    intro ξ
    by_cases hξ : IsLatticeHarmonic mo ξ
    · exact ((hK ξ).aemeasurable.ennreal_ofReal).congr (Filter.Eventually.of_forall fun y => (hon ξ hξ y).symm)
    · exact aemeasurable_const.congr (Filter.Eventually.of_forall fun y => (hoff ξ hξ y).symm)
  have hgrot : ∀ ξ φ, ∀ y ∈ S, g ξ (axialRot φ y) = g ξ y := by
    intro ξ φ y hy
    by_cases hξ : IsLatticeHarmonic mo ξ
    · rw [hon ξ hξ, hon ξ hξ, hrot ξ φ y hy]
    · rw [hoff ξ hξ, hoff ξ hξ]
  have hgflip : ∀ ξ, ∀ᵐ y, g (flipLabel ξ) (flipPoint y) = g ξ y := by
    intro ξ
    by_cases hξ : IsLatticeHarmonic mo ξ
    · have hξ' := (PinHalf.lattice_flip hL hmo ξ).2 hξ
      filter_upwards [hflip ξ] with y hy
      rw [hon _ hξ', hon ξ hξ, hy]
    · have hξ' : ¬ IsLatticeHarmonic mo (flipLabel ξ) := fun h => hξ ((PinHalf.lattice_flip hL hmo ξ).1 h)
      exact Filter.Eventually.of_forall fun y => by rw [hoff _ hξ', hoff ξ hξ]
  rw [step1, hH g hgm S hSr hSa hgrot hgflip]
  congr 1
  have hinj := (hL mo hmo).1
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun ι => ?_
    refine setLIntegral_congr_fun PinHalf.measurableSet_halfPlane fun p hp => ?_
    rw [hon _ ⟨ι, rfl⟩, ENNReal.ofReal_mul' (le_of_lt hp.1)]
  · intro ξ hξ
    by_contra hr
    apply hξ
    have hnl : ¬ IsLatticeHarmonic mo ξ := fun ⟨ι, hι⟩ => hr ⟨ι, hι⟩
    simp only [hoff ξ hnl, zero_mul, lintegral_zero]

theorem stretch_reduction (γ : Symmetry) (hγ1 : ∀ y, γ.1 y = flipPoint y)
    (f : ℝ × Space → ℝ≥0∞) (hf : AEMeasurable f volume)
    (hsym : ∀ᵐ σ, ∀ᵐ y, f (σ, flipPoint y) = f (σ, y)) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f (σ, y)) = ENNReal.ofReal (4 * Real.pi) *
      ∫⁻ p in halfPlane, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f (τ, axialRot φ (planePoint p))) * ENNReal.ofReal p.1 := by
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have hμ' : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμ, Measure.restrict_prod_eq_prod_univ, Measure.volume_eq_prod]
  have hfμ : AEMeasurable f μ := by
    rw [hμ']
    exact hf.restrict
  set ν : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := (volume.restrict halfPlane).prod
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) with hν
  have hq := StretchMeanParts.qmp_orbit γ.1 hγ1
  set f' := hfμ.mk f with hf'
  have hf'm : Measurable f' := hfμ.measurable_mk
  have hff' : f =ᵐ[μ] f' := hfμ.ae_eq_mk
  have hsym' : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y, f' (σ, flipPoint y) = f' (σ, y) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hff', ae_restrict_of_ae hsym] with σ h1 h2
    have h3 : ∀ᵐ y, f (σ, flipPoint y) = f' (σ, flipPoint y) := by
      have h4 := γ.1.measurePreserving.quasiMeasurePreserving.ae h1
      simpa only [hγ1] using h4
    filter_upwards [h1, h2, h3] with y a b c
    rw [← a, ← c, b]
  have hcomp : AEMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => f (w.2.1, axialRot w.2.2 (planePoint w.1))) ν :=
    hfμ.comp_quasiMeasurePreserving hq
  have hL1 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f (σ, y)) = ∫⁻ z, f z ∂μ := (lintegral_prod f hfμ).symm
  have hL2 := StretchMeanParts.lintegral_spacetime γ.1 hγ1 f' hf'm hsym'
  have hL3 : ∫⁻ w, ENNReal.ofReal w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1)) ∂ν
      = ∫⁻ w, ENNReal.ofReal w.1.1 * f (w.2.1, axialRot w.2.2 (planePoint w.1)) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hq.ae hff'] with w hw
    rw [hw]
  have hL4 : ∫⁻ w, ENNReal.ofReal w.1.1 * f (w.2.1, axialRot w.2.2 (planePoint w.1)) ∂ν
      = ∫⁻ p in halfPlane, ENNReal.ofReal p.1 * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f (τ, axialRot φ (planePoint p)) := by
    have hprodm : AEMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal w.1.1 * f (w.2.1, axialRot w.2.2 (planePoint w.1))) ν :=
      (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul hcomp
    rw [lintegral_prod _ hprodm]
    refine lintegral_congr_ae ?_
    filter_upwards [hcomp.aestronglyMeasurable.prodMk_left] with p hp
    show ∫⁻ s : ℝ × ℝ, ENNReal.ofReal p.1 * f (s.1, axialRot s.2 (planePoint p)) ∂_ = _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod _ hp.aemeasurable,
      Measure.restrict_congr_set Ioc_ae_eq_Icc, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hc : ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (1 / (2 * Real.pi)) = 2 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have e : 4 * Real.pi * (1 / (2 * Real.pi)) = 2 := by
      field_simp
      ring
    rw [e, ENNReal.ofReal_ofNat]
  have hR : (∫⁻ p in halfPlane, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f (τ, axialRot φ (planePoint p))) * ENNReal.ofReal p.1)
      = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ p in halfPlane, ENNReal.ofReal p.1 * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f (τ, axialRot φ (planePoint p)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    ring
  rw [hL1, lintegral_congr_ae hff', hL2, hL3, hL4, hR, ← mul_assoc, hc]

end Internal.ModeDensityBridge

open Internal.ModeDensityBridge in
theorem modeDensityBridge (hH : HalfPlaneReductionHolds) (hA : RotationAverageHolds)
    (hE : HessianEnergyIdentityHolds) (hS : ModeShiftRotateHolds)
    (hS' : ModeShiftRotateTensorHolds)
    (hF : ModeFlipHolds) (hC : ClassSupportHolds) (hL : LabelArithmeticHolds) (hT : ModeTermFlipHolds)
    (hW : StretchFlipHolds) : ModeDensityBridgeHolds := by
  have _ := hA
  have _ := hE
  have _ := hS
  have _ := hS'
  intro k C nE nM D D₀ hclass hI hWS hbd hflc q hq hadm v G H g hv
  obtain ⟨e₁, e₂, e₃, hadm⟩ := hadm
  obtain ⟨γ, hγΓ, hγ1, hγ2⟩ := hclass.flip
  have hfc := hflc q hq
  have hmb := hbd q hq
  have hvp := hv.periodic_velocity
  have hGp := hv.periodic_gradient
  have hHp := hv.periodic_secondDeriv
  set m := D.pieces q with hmdef
  set P := D.cert.period q with hPdef
  set hb := D.bounds q with hbdef
  set w := D.cert.weightFn with hwdef
  set T : ℤ × ℤ → Space → ℝ := fun ξ y => m.modeTerm P hb w v G H ξ 0 y with hTdef
  have hTm : ∀ ξ, AEStronglyMeasurable (T ξ) volume := fun ξ =>
    Internal.PinHalf.aesm_of_snd ((aesm_modeTerm m P hb w hadm hmb hv.measurable_velocity hv.measurable_gradient
      hv.measurable_secondDeriv ξ).congr (Filter.Eventually.of_forall fun z => modeTerm_shift m P hb w hvp hGp hHp ξ z.1 z.2))
  have hSa := ae_goodSet m P hb w hadm hfc hv
  have hrotT : ∀ ξ φ, ∀ y ∈ goodSet m P hb w v G H, T ξ (axialRot φ y) = T ξ y := fun ξ φ y hy => hy ξ φ
  have hflipT : ∀ ξ, ∀ᵐ y, T (flipLabel ξ) (flipPoint y) = T ξ y := fun ξ =>
    ae_modeTerm_flip hF hT m P hb w hfc hv ⟨γ, hγΓ, hγ1, hγ2⟩ ξ
  have hzeroT : ∀ ξ, ¬ IsLatticeHarmonic D.azimuthOrder ξ → ∀ᵐ y, T ξ y = 0 := fun ξ hξ =>
    ae_modeTerm_zero hC m P hb w hclass hv ξ hξ
  have hpos := lattice_reduction hH hL hclass.order_pos T hTm (goodSet m P hb w v G H) (goodSet_rot m P hb w v G H)
    hSa hrotT hflipT hzeroT
  have hneg := lattice_reduction hH hL hclass.order_pos (fun ξ y => -T ξ y) (fun ξ => (hTm ξ).neg)
    (goodSet m P hb w v G H) (goodSet_rot m P hb w v G H) hSa
    (fun ξ φ y hy => by simp only [hrotT ξ φ y hy])
    (fun ξ => (hflipT ξ).mono fun y hy => by simp only [hy])
    (fun ξ hξ => (hzeroT ξ hξ).mono fun y hy => by simp only [hy, neg_zero])
  simp only [neg_mul] at hneg
  set S : ℝ × Space → ℝ := fun z => CoerciveWeak.stretchFormWith D.given D.givenHess v G z.1 z.2 with hSdef
  have hSm : AEMeasurable S volume :=
    CoerciveWeak.Internal.AbsorbStep.aem_stretchFormWith (W := D.given) (v := v) (G := G) (HW := D.givenHess) hWS
      hv.measurable_velocity hv.measurable_gradient
  have hSf := Internal.StretchMeanParts.stretch_flip_ae hW hI hWS hv γ hγΓ hγ1 hγ2
  have hsp := stretch_reduction γ hγ1 (fun z => ENNReal.ofReal (S z)) hSm.ennreal_ofReal
    (hSf.mono fun σ h => h.mono fun y hy => by simp only [hSdef, hy])
  have hsn := stretch_reduction γ hγ1 (fun z => ENNReal.ofReal (-S z)) hSm.neg.ennreal_ofReal
    (hSf.mono fun σ h => h.mono fun y hy => by simp only [hSdef, hy])
  have hint : ∀ (F : Space → ℝ≥0∞) (Q : ℝ × Space → ℝ≥0∞), AEMeasurable F volume →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (F y + Q (σ, y)))
        = (∫⁻ y, F y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Q (σ, y) := by
    intro F Q hF'
    have e1 : ∀ σ, ∫⁻ y, (F y + Q (σ, y)) = (∫⁻ y, F y) + ∫⁻ y, Q (σ, y) := fun σ =>
      lintegral_add_left' hF' _
    simp_rw [e1]
    rw [lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      mul_one]
  have hsplitP : ∀ σ y, CoerciveWeak.densityPosWith m P hb w v G H D.given D.givenHess σ y
      = (∑' ξ, ENNReal.ofReal (T ξ y)) + ENNReal.ofReal (S (σ, y)) := by
    intro σ y
    unfold CoerciveWeak.densityPosWith
    congr 1
    exact tsum_congr fun ξ => by rw [modeTerm_shift m P hb w hvp hGp hHp ξ σ y]
  have hsplitN : ∀ σ y, CoerciveWeak.densityNegWith m P hb w v G H D.given D.givenHess σ y
      = (∑' ξ, ENNReal.ofReal (-T ξ y)) + ENNReal.ofReal (-S (σ, y)) := by
    intro σ y
    unfold CoerciveWeak.densityNegWith
    congr 1
    exact tsum_congr fun ξ => by rw [modeTerm_shift m P hb w hvp hGp hHp ξ σ y]
  have hAp : AEMeasurable (fun y => ∑' ξ, ENNReal.ofReal (T ξ y)) volume :=
    AEMeasurable.tsum fun ξ => (hTm ξ).aemeasurable.ennreal_ofReal
  have hAn : AEMeasurable (fun y => ∑' ξ, ENNReal.ofReal (-T ξ y)) volume :=
    AEMeasurable.tsum fun ξ => (hTm ξ).neg.aemeasurable.ennreal_ofReal
  refine ⟨?_, ?_⟩
  · simp_rw [hsplitP]
    rw [hint _ (fun z => ENNReal.ofReal (S z)) hAp, hpos, hsp, CellLayerData.formPos, mul_add]
    rfl
  · simp_rw [hsplitN]
    rw [hint _ (fun z => ENNReal.ofReal (-S z)) hAn, hneg, hsn, CellLayerData.formNeg, mul_add]
    rfl

end Bridge

end CertCell

end Breakdown
