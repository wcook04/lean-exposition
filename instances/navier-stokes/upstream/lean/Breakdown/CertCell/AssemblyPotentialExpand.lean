import Breakdown.CertCell.AssemblyPotentialExpandLattice
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsGiven
import Breakdown.CertCell.PairingModeIdentity
import Breakdown.CertCell.ClassSupportLinks
import Breakdown.CertCell.ModeOffLattice
import Breakdown.CertCell.ModeShiftRotate
import Breakdown.CertCell.ModeShiftRotateTensor

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.StretchPairs

section Main

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem continuous_basis (L : CellLayout) (j l : ℕ) : Continuous (fun p : ℝ × ℝ => CellCert.CellEnergy.basisFn L.bases j l p) := by
  unfold CellCert.CellEnergy.basisFn CellBases.radialPoly CellBases.heightPoly
  fun_prop

theorem continuous_lowProfile (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (j : Fin 12) :
    Continuous (fun p => lowProfile D R K ι x p j) := by
  by_cases hj : j.val < 9
  · simp only [lowProfile, pairVec, dif_pos hj, lowGrad, lowStrainOf]
    have := continuous_basis ((R.layouts K).layout ι.1)
    fun_prop
  · simp only [lowProfile, pairVec, dif_neg hj, lowVel, lowVelocityOf]
    have := continuous_basis ((R.layouts K).layout ι.1)
    fun_prop

theorem good_upper (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K))
    (x : CellVars D R K → ℂ) : Good (D.mesh.box K).rect (upperProfiles D R K P x) := by
  have hcomp : IsCompact (D.mesh.box K).rect := isCompact_Icc.prod isCompact_Icc
  refine good_finite hcomp (fun ι j => ?_) (D.mesh.resolved K) (fun ι h p j => ?_)
  · by_cases h : ι ∈ D.mesh.resolved K
    · simp only [upperProfiles, lowAt, dif_pos h]
      exact continuous_lowProfile D R K ⟨ι, h⟩ _ j
    · simp only [upperProfiles, lowAt, dif_neg h]
      exact continuous_const
  · simp [upperProfiles, lowAt, dif_neg h]

theorem couplingOK_rect (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K))
    (hW : ∃ B, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) (Hs : Finset (ℤ × ℤ)) :
    CouplingOK (D.mesh.box K).rect Hs (trueCoupling D) := by
  refine ⟨measurableSet_Icc.prod measurableSet_Icc, fun p hp => hK.r_order.1.trans hp.1.1,
    fun α _ i j => (trueCoupling_meas D hW α i j).mono_ac (Internal.rect_ac_halfPlane _ hK), fun α _ => ?_⟩
  obtain ⟨c, hc⟩ := trueCoupling_bound D hW α
  exact ⟨c, fun p _ i j => hc p i j⟩

theorem good_true {K : Fin D.mesh.count} (hreg : CellProfileRegular D) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {κ : Fin k → ℝ} {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) :
    Good (D.mesh.box K).rect (trueProfiles D v G) := by
  obtain ⟨h1, h2⟩ := hreg K q v G H g κ F Pg ht
  exact ⟨fun ι j => (h1 ι).1 j, fun ι => (h1 ι).2, h2⟩

theorem harmonicLabels_neg {A : AssemblyEntry D R} {P : CouplingEntries D R} {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hc : PotentialConditions D R A P states)
    (K : Fin D.mesh.count) : ∀ α ∈ (P.potential K).harmonicLabels, -α ∈ (P.potential K).harmonicLabels := by
  intro α hα
  refine (hc.labels_iff K (-α)).2 ?_
  rw [labelHarmonic_neg]
  exact hc.model_harmonics.symmetric _ ((hc.labels_iff K α).1 hα)

theorem trueCoupling_sym (α : ℤ × ℤ) (p : ℝ × ℝ) (U V : Fin 12 → ℂ) :
    (sesq12 (trueCoupling D (-α) p) V U).re = (sesq12 (trueCoupling D α p) U V).re := by
  rw [sesq12_trueCoupling_neg, Complex.conj_re]

end Main

end Internal.StretchPairs

open Internal.StretchPairs in
theorem stretchSplit : StretchSplitHolds := by
  intro k C nE nM D R A P states hstates _ htf hc _ K q v G H g κ F Pg ht ζ η
  have hK : IsCellBox (D.mesh.box K) := hc.mesh_valid.box_valid K
  have hU0 : ∀ ι, ι ∉ D.mesh.resolved K → ∀ p,
      upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p = 0 := by
    intro ι h p
    simp [upperProfiles, lowAt, dif_neg h]
  exact split_core (couplingOK_rect D K hK hc.model_state _) (harmonicLabels_neg D R hc K) (trueCoupling_sym D)
    (trueProfiles D v G) (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
    (D.mesh.resolved K) (D.mesh.band K) hU0 (hc.mesh_valid.band_apart K) (good_true D htf.1 ht)
    (good_upper D R K _ _)

open Internal.StretchPairs in
theorem stretchExpansion_of_class (hMS : Bridge.MeanStretchModeSumHolds) (hC : Bridge.ClassSupportHolds) :
    ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
      (A : AssemblyEntry D R) (P : CouplingEntries D R) (states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D →
      PotentialConditions D R A P states → Bridge.IsModeClass D.cert.symmetries D.azimuthOrder → StretchExpansion D R P := by
  intro k C nE nM D R A P states _ htf hc hclass K q v G H g κ F Pg ht
  have hK : IsCellBox (D.mesh.box K) := hc.mesh_valid.box_valid K
  have hM := couplingOK_rect D K hK hc.model_state (P.potential K).harmonicLabels
  have hgood := good_true D htf.1 ht
  have hpt := meanStretch_eq_labelSum D hMS hC hc.model_state hc.model_harmonics hc.azimuth_pos hclass
    (P.potential K).harmonicLabels (hc.labels_iff K) ht.perturbation
  have hpt' := (Internal.rect_ac_halfPlane _ hK).ae_le hpt
  show ∫ p in (D.mesh.box K).rect, D.meanStretch v G p * p.1
    = pairSum (D.mesh.box K).rect (P.potential K).harmonicLabels (trueCoupling D) (trueProfiles D v G) (trueProfiles D v G)
  rw [← pairSum_integral hM hgood hgood]
  refine integral_congr_ae ?_
  filter_upwards [hpt'] with p hp
  rw [hp.2, ← tsum_mul_right]
  refine tsum_congr fun ι => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  unfold pairTerm
  rw [mul_comm]
  rfl

theorem stretchExpansion_of_modeClass :
    ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
      (A : AssemblyEntry D R) (P : CouplingEntries D R) (states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D →
      PotentialConditions D R A P states → Bridge.IsModeClass D.cert.symmetries D.azimuthOrder → StretchExpansion D R P :=
  stretchExpansion_of_class (Bridge.meanStretchModeSum Bridge.pairingModeIdentity)
    (Bridge.classSupport (Bridge.modeOffLattice Bridge.modeShiftRotate Bridge.modeShiftRotateTensor)
      Bridge.labelArithmetic)

theorem meanStretch_eq_labelSum_of_modeClass {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (hW : ∃ B, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B)
    (hE : Bridge.IsHarmonicExpansion D.givenLabels D.given D.givenHess) (hm : 1 ≤ D.azimuthOrder)
    {Γ : Set Symmetry} (hclass : Bridge.IsModeClass Γ D.azimuthOrder) (Hs : Finset (ℤ × ℤ))
    (hHs : ∀ α, α ∈ Hs ↔ labelHarmonic D.azimuthOrder α ∈ D.givenLabels)
    {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ p ∂(volume.restrict halfPlane),
      (∀ α ∈ Hs, Summable (fun κ : ℤ × ℤ =>
        (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re)) ∧
      D.meanStretch v G p = ∑' κ : ℤ × ℤ, ∑ α ∈ Hs,
        (sesq12 (trueCoupling D α p) (bandProfile D κ v G p) (bandProfile D (κ - α) v G p)).re :=
  meanStretch_eq_labelSum D (Bridge.meanStretchModeSum Bridge.pairingModeIdentity)
    (Bridge.classSupport (Bridge.modeOffLattice Bridge.modeShiftRotate Bridge.modeShiftRotateTensor)
      Bridge.labelArithmetic) hW hE hm hclass Hs hHs hv

end Assembly

end CertCell

end Breakdown
