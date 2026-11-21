import Breakdown.CertCell.BridgeStatements
import Breakdown.FracCell.LowEntry

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.HalfPlaneReduction

open CellCert.CellAnalysis.LowEntry.Internal (cylArg muU muU_def key qmp)

theorem cylArg_eq_rot (q : (ℝ × ℝ) × ℝ) : cylArg q = axialRot q.2 (planePoint q.1) := by
  ext i
  fin_cases i <;>
    simp [cylArg, planePoint, CellCert.CellAnalysis.cylPoint, axialRot, unitVector] <;> ring

theorem flipPoint_axialRot (φ : ℝ) (y : Space) :
    flipPoint (axialRot φ y) = axialRot (-φ) (flipPoint y) := by
  ext i
  fin_cases i <;> simp [flipPoint, axialRot, unitVector] <;> ring

theorem planePoint_neg_height (p : ℝ × ℝ) : planePoint (p.1, -p.2) = flipPoint (planePoint p) := by
  ext i
  fin_cases i <;> simp [planePoint, CellCert.CellAnalysis.cylPoint, flipPoint, unitVector]

theorem flipPoint_flipPoint (y : Space) : flipPoint (flipPoint y) = y := by
  ext i
  fin_cases i <;> simp [flipPoint, unitVector]

def flipLinear : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' a b := by
    ext i
    fin_cases i <;> simp [flipPoint, unitVector] <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [flipPoint, unitVector]

theorem flipPoint_preimage_null {Z : Set Space} (hZ : volume Z = 0) : volume (flipPoint ⁻¹' Z) = 0 := by
  have h := Measure.addHaar_preimage_continuousLinearEquiv (volume : Measure Space)
    (LinearEquiv.ofInvolutive flipLinear (fun y => flipPoint_flipPoint y)).toContinuousLinearEquiv Z
  rw [hZ, mul_zero] at h
  exact h

theorem plane_null (Z : Set Space) (hZ : volume Z = 0) (hrot : ∀ φ y, y ∈ Z → axialRot φ y ∈ Z) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), planePoint p ∉ Z := by
  have h0 : muU (cylArg ⁻¹' Z) = 0 := qmp.preimage_null hZ
  have hsub : {p : ℝ × ℝ | planePoint p ∈ Z} ×ˢ (univ : Set ℝ) ⊆ cylArg ⁻¹' Z := by
    rintro q ⟨hq, -⟩
    show cylArg q ∈ Z
    rw [cylArg_eq_rot]
    exact hrot _ _ hq
  have h1 := measure_mono_null hsub h0
  rw [muU_def, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Ioo] at h1
  have hne : ENNReal.ofReal (Real.pi - -Real.pi) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith [Real.pi_pos]
  exact measure_eq_zero_iff_ae_notMem.1 ((mul_eq_zero.1 h1).resolve_right hne)

theorem rotation_invariant_lintegral (G : Space → ℝ≥0∞) (hG : AEMeasurable G)
    (hrot : ∀ φ y, G (axialRot φ y) = G y) :
    ∫⁻ y, G y = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), G (planePoint p) * ENNReal.ofReal p.1 := by
  have hfun : (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal q.1.1 * G (cylArg q))
      = fun q => G (planePoint q.1) * ENNReal.ofReal q.1.1 := by
    funext q
    rw [cylArg_eq_rot, hrot, mul_comm]
  have hm : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => G (planePoint q.1) * ENNReal.ofReal q.1.1) muU := by
    rw [← hfun]
    exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
      (hG.comp_quasiMeasurePreserving qmp)
  rw [← key G, hfun]
  rw [muU_def] at hm ⊢
  rw [lintegral_prod _ hm]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  congr 2
  ring

theorem meridian_lintegral (f : Space → ℝ≥0∞) (hf : AEMeasurable f) (S : Set Space)
    (hSrot : ∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) (hS : ∀ᵐ y, y ∈ S) (hSc : volume Sᶜ = 0)
    (hfrot : ∀ φ, ∀ y ∈ S, f (axialRot φ y) = f y) :
    ∫⁻ y, f y = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), f (planePoint p) * ENNReal.ofReal p.1 := by
  have hae : S.indicator f =ᵐ[volume] f := hS.mono fun y hy => indicator_of_mem hy f
  have hrotI : ∀ φ y, S.indicator f (axialRot φ y) = S.indicator f y := by
    intro φ y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem ((hSrot φ y).2 hy), indicator_of_mem hy, hfrot φ y hy]
    · rw [indicator_of_notMem (fun h => hy ((hSrot φ y).1 h)), indicator_of_notMem hy]
  rw [← lintegral_congr_ae hae, rotation_invariant_lintegral _ (hf.congr hae.symm) hrotI]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [plane_null Sᶜ hSc (fun φ y hy => by simpa [hSrot] using hy)] with p hp
  rw [indicator_of_mem (by simpa using hp)]

theorem meridian_split (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), f p
      = (∫⁻ p in halfPlane, f p) + ∫⁻ p in halfPlane, f (p.1, -p.2) := by
  have hset : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ))
      =ᵐ[volume] (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ) ∪ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) := by
    have h1 : (univ : Set ℝ) =ᵐ[volume] (Iio 0 ∪ Ioi 0 : Set ℝ) := by
      rw [Set.Iio_union_Ioi]
      exact (ae_eq_univ.2 (by rw [compl_compl]; exact measure_singleton 0)).symm
    have h0 : (Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume] (Ioi (0 : ℝ) : Set ℝ) := ae_eq_refl _
    have h2 := Measure.set_prod_ae_eq h0 h1
    rw [Set.prod_union] at h2
    exact h2
  have hdisj : Disjoint (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro ⟨r, z⟩ ⟨-, hz⟩ ⟨-, hz'⟩
    simp only [mem_Iio, mem_Ioi] at hz hz'
    linarith
  have hH : halfPlane = Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := rfl
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)
  have hmp : MeasurePreserving e volume volume :=
    (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
  have hpre : e ⁻¹' (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)) = Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext ⟨r, z⟩
    show (0 < r ∧ -z < 0) ↔ (0 < r ∧ 0 < z)
    rw [neg_lt_zero]
  have hL : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ), f p = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), f (p.1, -p.2) := by
    rw [← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding f (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)), hpre]
    rfl
  rw [setLIntegral_congr hset, lintegral_union (measurableSet_Ioi.prod measurableSet_Ioi) hdisj, hL, hH,
    add_comm]

theorem flip_height_ae (g : ℤ × ℤ → Space → ℝ≥0∞) (S : Set Space)
    (hSrot : ∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) (hSc : volume Sᶜ = 0)
    (hgrot : ∀ ξ φ, ∀ y ∈ S, g ξ (axialRot φ y) = g ξ y) (ξ : ℤ × ℤ)
    (hgf : ∀ᵐ y, g (flipLabel ξ) (flipPoint y) = g ξ y) :
    ∀ᵐ p ∂(volume.restrict halfPlane), g (flipLabel ξ) (planePoint (p.1, -p.2)) = g ξ (planePoint p) := by
  set Z : Set Space := {y | ¬ (y ∈ S ∧ flipPoint y ∈ S ∧ g (flipLabel ξ) (flipPoint y) = g ξ y)} with hZ
  have hZnull : volume Z = 0 := by
    refine measure_mono_null (t := Sᶜ ∪ flipPoint ⁻¹' Sᶜ ∪ {y | g (flipLabel ξ) (flipPoint y) ≠ g ξ y})
      ?_ (measure_union_null (measure_union_null hSc (flipPoint_preimage_null hSc)) (ae_iff.1 hgf))
    intro y hy
    simp only [hZ, mem_ofPred_eq, not_and_or] at hy
    rcases hy with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hZrot : ∀ φ y, y ∈ Z → axialRot φ y ∈ Z := by
    intro φ y hy
    simp only [hZ, mem_ofPred_eq] at hy ⊢
    intro hw
    apply hy
    obtain ⟨h1, h2, h3⟩ := hw
    have hyS : y ∈ S := (hSrot φ y).1 h1
    rw [flipPoint_axialRot] at h2 h3
    have hfS : flipPoint y ∈ S := (hSrot (-φ) _).1 h2
    refine ⟨hyS, hfS, ?_⟩
    rw [← hgrot (flipLabel ξ) (-φ) _ hfS, h3, hgrot ξ φ y hyS]
  have hsub : halfPlane ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1, trivial⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (plane_null Z hZnull hZrot)] with p hp
  simp only [hZ, mem_ofPred_eq, not_not] at hp
  rw [planePoint_neg_height]
  exact hp.2.2

end Internal.HalfPlaneReduction

open Internal.HalfPlaneReduction in
theorem halfPlaneReduction : HalfPlaneReductionHolds := by
  intro g hg S hSrot hS hgrot hgflip
  have hSc : volume Sᶜ = 0 := ae_iff.1 hS
  have hflip : ∀ ξ, ∫⁻ p in halfPlane, g (flipLabel ξ) (planePoint (p.1, -p.2)) * ENNReal.ofReal p.1
      = ∫⁻ p in halfPlane, g ξ (planePoint p) * ENNReal.ofReal p.1 := fun ξ =>
    lintegral_congr_ae ((flip_height_ae g S hSrot hSc hgrot ξ (hgflip ξ)).mono fun p hp => congrArg (· * ENNReal.ofReal p.1) hp)
  let e : ℤ × ℤ ≃ ℤ × ℤ := Function.Involutive.toPerm flipLabel (fun ξ => by simp [flipLabel])
  have hsum : ∑' ξ, ∫⁻ p in halfPlane, g ξ (planePoint (p.1, -p.2)) * ENNReal.ofReal p.1
      = ∑' ξ, ∫⁻ p in halfPlane, g ξ (planePoint p) * ENNReal.ofReal p.1 :=
    (e.tsum_eq (fun η => ∫⁻ p in halfPlane, g η (planePoint (p.1, -p.2)) * ENNReal.ofReal p.1)).symm.trans
      (tsum_congr hflip)
  calc ∫⁻ y, ∑' ξ, g ξ y = ∑' ξ, ∫⁻ y, g ξ y := lintegral_tsum hg
    _ = ∑' ξ, ENNReal.ofReal (2 * Real.pi) *
          ((∫⁻ p in halfPlane, g ξ (planePoint p) * ENNReal.ofReal p.1)
            + ∫⁻ p in halfPlane, g ξ (planePoint (p.1, -p.2)) * ENNReal.ofReal p.1) := by
        refine tsum_congr fun ξ => ?_
        rw [meridian_lintegral (g ξ) (hg ξ) S hSrot hS hSc (hgrot ξ), meridian_split]
    _ = ENNReal.ofReal (2 * Real.pi) *
          ((∑' ξ, ∫⁻ p in halfPlane, g ξ (planePoint p) * ENNReal.ofReal p.1)
            + ∑' ξ, ∫⁻ p in halfPlane, g ξ (planePoint (p.1, -p.2)) * ENNReal.ofReal p.1) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact ENNReal.tsum_add
    _ = ENNReal.ofReal (4 * Real.pi) * ∑' ξ, ∫⁻ p in halfPlane, g ξ (planePoint p) * ENNReal.ofReal p.1 := by
        rw [hsum, ← two_mul, ← mul_assoc, show (4 : ℝ) * Real.pi = 2 * Real.pi * 2 by ring,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * Real.pi by positivity), ENNReal.ofReal_ofNat]

end Bridge

end CertCell

end Breakdown
