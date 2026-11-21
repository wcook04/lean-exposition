import Breakdown.CertCell.AssemblyRowParts
import Breakdown.CertCell.OwnSolidOrbit
import Breakdown.CertCell.AssemblyRowExpansionLowLong
import Breakdown.CertCell.AssemblyRowExpansionLowRight
import Breakdown.CertCell.AssemblyRowExpansionLowAlgebra
import Breakdown.CertCell.AssemblyRowExpansionLowOffLabel
import Breakdown.CertCell.AssemblyRowExpansionLowResolved
import Breakdown.CertCell.LabelRowProfile
import Breakdown.CertCell.RowLowPart
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.HarmonicPressureLift
import Breakdown.CertCell.HarmonicSideData
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.SecondDerivEnergyIdentity
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower
import Breakdown.Cert.CoerciveSmoothPieceEpsBounds
import Breakdown.Cert.CoercivePairingSplit

open scoped ENNReal NNReal
open MeasureTheory Set Matrix

noncomputable section

namespace Breakdown.CertCell.Assembly

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis CellCert.CellFormula

namespace Internal.RowIdentity

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def pairTrue {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι' : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ)
    (crossTest (trueVelocity D (B.rowLabel i - ι') p) (trueVorticity D (B.rowLabel i - ι') p) (rowTestValue D K B i p) j)

def pairModel {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι' : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ)
    (crossTest (modelVelocity D K (B.rowLabel i - ι') p) (modelVorticity D K (B.rowLabel i - ι') p)
      (rowTestValue D K B i p) j)

def pairError {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι' : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j,
    bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest
      (fun a => trueVelocity D (B.rowLabel i - ι') p a - modelVelocity D K (B.rowLabel i - ι') p a
        - longVelocity D R K (B.rowLabel i - ι') p a)
      (fun a => trueVorticity D (B.rowLabel i - ι') p a - modelVorticity D K (B.rowLabel i - ι') p a
        - longVorticity D R K (B.rowLabel i - ι') p a)
      (rowTestValue D K B i p) j)

def pairLong {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι' : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ)
    (crossTest (longVelocity D R K (B.rowLabel i - ι') p) (longVorticity D R K (B.rowLabel i - ι') p)
      (rowTestValue D K B i p) j)

def pairShift {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (α : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j,
    bandProfile D (B.rowLabel i - α) v G p j * (starRingEnd ℂ)
      (crossTest (trueVelocity D α p) (trueVorticity D α p) (rowTestValue D K B i p) j)

def tailTerm {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι' : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect,
    ((D.mesh.box K).lineWeight p.1 : ℂ) * ∑ j, tailProfile D R K ι' v G p j * (starRingEnd ℂ) (B.rowTailTest i ι' p j)

def bandTerm {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι' : ℤ × ℤ) : ℂ :=
  ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ) (B.rowBand i ι' p j)

def lowRow (K : Fin D.mesh.count) (B : CellBlocks (CellVars D R K)) (i : Fin B.rowCount) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (ι' : ℤ × ℤ) : ℂ :=
  ∑ d, couplingRowVector ((R.layouts K).layout ι') (modelVelocity D K (B.rowLabel i - ι'))
      (modelVorticity D K (B.rowLabel i - ι')) (rowTestPoly D K B i) d
    * harmonicData ((R.layouts K).layout ι') (labelTime ι') v G H Pg d

theorem modelVelocity_eq_poly (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) (α : ℤ × ℤ) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) :
    modelVelocity D K α p = fun a => (D.model.velocity.comp K α a).eval (D.mesh.box K) p := by
  funext a
  have h2 : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  simp only [modelVelocity, CellVecField.planeValue, labelValueAt, if_pos h2]

theorem modelVorticity_eq_poly (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) (α : ℤ × ℤ) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) :
    modelVorticity D K α p = fun a => (D.model.vorticity.comp K α a).eval (D.mesh.box K) p := by
  funext a
  have h2 : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  simp only [modelVorticity, CellVecField.planeValue, labelValueAt, if_pos h2]

theorem pair_integrableOn {K : CellBox} (hK : IsCellBox K) {σ : ℝ × ℝ → Fin 12 → ℂ}
    (hσ : ∀ j, RectSquare K (fun p => σ p j)) {W Ω φ : ℝ × ℝ → Fin 3 → ℂ}
    (hW : ∃ W' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => W' p a) ∧ ∀ p ∈ K.rect, W p = W' p)
    (hΩ : ∃ Ω' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => Ω' p a) ∧ ∀ p ∈ K.rect, Ω p = Ω' p)
    (hφ : ∀ a, Continuous fun p => φ p a) :
    IntegrableOn (fun p => (p.1 : ℂ) * ∑ j, σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j)) K.rect := by
  obtain ⟨W', hW'c, hW'e⟩ := hW
  obtain ⟨Ω', hΩ'c, hΩ'e⟩ := hΩ
  have e : (fun p => (p.1 : ℂ) * ∑ j, σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j))
      = fun p => ∑ j, (p.1 : ℂ) * σ p j * (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j) := by
    funext p
    simp only [Finset.mul_sum, mul_assoc]
  rw [e]
  refine integrable_finsetSum _ fun j _ => ?_
  have hc : Continuous (fun p => (starRingEnd ℂ) (crossTest (W' p) (Ω' p) (φ p) j)) :=
    Complex.continuous_conj.comp (continuous_crossTest_comp hW'c hΩ'c hφ j)
  obtain ⟨hm, M, hM⟩ := rect_regular_of_eqOn hc (f := fun p => (starRingEnd ℂ) (crossTest (W p) (Ω p) (φ p) j))
    fun p hp => by simp only [hW'e p hp, hΩ'e p hp]
  exact rectSquare_pairing hK (hσ j) hm hM

theorem shift_sum {S T : Finset (ℤ × ℤ)} (ι : ℤ × ℤ) (f g : ℤ × ℤ → ℂ)
    (hfg : ∀ α, f α = g (ι - α)) (hz : ∀ ι' ∈ S, ι - ι' ∉ T → g ι' = 0) :
    ∑ α ∈ T, (if ι - α ∈ S then f α else 0) = ∑ ι' ∈ S, g ι' := by
  classical
  have h2 : ∑ ι' ∈ S, g ι' = ∑ ι' ∈ S with ι - ι' ∈ T, g ι' :=
    (Finset.sum_filter_of_ne (p := fun ι' => ι - ι' ∈ T) (fun ι' h hne => by
      by_contra hn; exact hne (hz ι' h hn))).symm
  rw [← Finset.sum_filter, h2]
  refine Finset.sum_nbij' (fun α => ι - α) (fun ι' => ι - ι') ?_ ?_ ?_ ?_ ?_
  · intro α hα
    rw [Finset.mem_filter] at hα ⊢
    exact ⟨hα.2, by rw [sub_sub_cancel]; exact hα.1⟩
  · intro ι' hι
    rw [Finset.mem_filter] at hι ⊢
    exact ⟨hι.2, by rw [sub_sub_cancel]; exact hι.1⟩
  · intro α _; simp
  · intro ι' _; simp
  · intro α _; exact hfg α

theorem integral_add_three {s : Set (ℝ × ℝ)} {f g h : ℝ × ℝ → ℂ} (hf : IntegrableOn f s) (hg : IntegrableOn g s)
    (hh : IntegrableOn h s) :
    ∫ p in s, (f p + g p + h p) = (∫ p in s, f p) + (∫ p in s, g p) + ∫ p in s, h p := by
  have e1 := integral_add (Integrable.add hf hg) hh
  have e2 := integral_add hf hg
  simp only [Pi.add_apply] at e1
  rw [e1, e2]

theorem rectSquare_mul_right {K : CellBox} (hK : IsCellBox K) {f c : ℝ × ℝ → ℂ} (hf : RectSquare K f)
    (hc : AEStronglyMeasurable c (volume.restrict K.rect)) {M : ℝ} (hM : ∀ p ∈ K.rect, ‖c p‖ ≤ M) :
    RectSquare K (fun p => f p * c p) := by
  have h := rectSquare_mul hK hf hc hM
  have e : (fun p => c p * f p) = fun p => f p * c p := funext fun p => mul_comm _ _
  rwa [e] at h

theorem norm_labelVel_le {X : ℝ → Space → Space} {C : ℝ} (hC : ∀ σ y, ‖X σ y‖ ≤ C) (m : ℕ) (ι : ℤ × ℤ)
    (p : ℝ × ℝ) (a : Fin 3) : ‖labelVel m ι X p a‖ ≤ C := by
  unfold labelVel modeVel
  refine Coercive.Internal.SmoothPieceEps.norm_modeAverage_le _ _ a fun τ φ => ?_
  have h1 : |axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p))) a| ≤ ‖axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p)))‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p)))) a
  rw [Coercive.PairingSplitInternal.norm_axialRot] at h1
  exact h1.trans (hC _ _)

theorem rectSquare_of_continuous {K : CellBox} (hK : IsCellBox K) {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    RectSquare K f := by
  obtain ⟨hm, M, hM⟩ := rect_regular_of_eqOn hf (f := f) fun _ _ => rfl
  exact rectSquare_bounded hK hm hM

end Internal.RowIdentity

open Internal.RowIdentity

theorem rowIdentity_entry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (P : CouplingEntries D R) (hReg : AssemblyRegular D R) (_hTF : TrueFieldRegular D)
    (hact : ∀ i, ∃ S : Finset (ℤ × ℤ), Instance.ActuatorShapeFacts D.azimuthOrder S (D.cert.actuator i))
    (hclass : Bridge.IsModeClass D.cert.symmetries D.azimuthOrder) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hPot : PotentialConditions D R A P states)
    (hC : RowConditions D R A) (hFun : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) (ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) (i : Fin (A.blocks K).rowCount) (hstates : CellStatesIn D R states) :
    rowMoment D K (A.blocks K) F i
        - rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G) i
        - tailRow D R K (A.blocks K) v G i
      = freqPiece D K (A.blocks K) (D.cert.period q) v i + errorPiece D R K (A.blocks K) (P.potential K) v G i
        + longPiece D R K (A.blocks K) (P.potential K) v G i
        + deactPiece D K (A.blocks K) (P.potential K).harmonicLabels v G i
        + actuatorPiece D K (A.blocks K) κ i := by
  set x := cellState D.mesh K (R.layouts K) v G H Pg κ ζ η with hxdef
  have hFR := hReg.field
  have hM : IsCellMesh D.mesh := hFR.mesh_valid
  have hK : IsCellBox (D.mesh.box K) := hM.box_valid K
  obtain ⟨Bw, hW⟩ := hFR.model_state
  have hS := hFR.model_harmonics
  have hCC := hFun.cell_conditions
  have hιt : (A.blocks K).rowLabel i ∈ D.mesh.tested K := hC.label_tested K i
  have hιr : (A.blocks K).rowLabel i ∈ D.mesh.resolved K := hM.tested_sub K hιt
  have hV : Bridge.VelocitySixthIntegralHolds := Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩
  have hv2 : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation hV Bridge.secondDerivEnergyIdentity _ _ v G H g ht.perturbation
  have hgradSq : ∀ ι' a b, RectSquare (D.mesh.box K) (fun p => gradAt D.azimuthOrder ι' G a b p) := by
    intro ι' a b
    obtain ⟨-, mG, -, -⟩ := CellCalculus.Internal.LabelRowProfile.profile_measurable _ hK D.azimuthOrder v G H Pg
      hv2 ht.pressure ι'
    have hI := CellCalculus.Internal.LabelRowProfile.profile_integrable harmonicLift_holds harmonicPressureLift_holds
      _ hK D.azimuthOrder v G H Pg hv2 ht.pressure ι'
    refine ⟨mG a b, CellCalculus.Internal.RowForm.comp_int hK hI (mG a b) fun p hp => ?_⟩
    have h0 := CellCalculus.Internal.RowForm.fst_nonneg hK hp
    refine mul_le_mul_of_nonneg_left ?_ h0
    have h1 : ‖gradAt D.azimuthOrder ι' G a b p‖ ^ 2 ≤ cnormSq (gradArray D.azimuthOrder ι' G p a) :=
      CellCalculus.Internal.RowForm.le_cnormSq (gradArray D.azimuthOrder ι' G p a) b
    have h2 : cnormSq (gradArray D.azimuthOrder ι' G p a) ≤ ∑ a' : Fin 3, cnormSq (gradArray D.azimuthOrder ι' G p a') :=
      Finset.single_le_sum (f := fun a' => cnormSq (gradArray D.azimuthOrder ι' G p a'))
        (fun _ _ => CellCalculus.Internal.RowForm.cnormSq_nonneg _) (Finset.mem_univ a)
    linarith [CellCalculus.Internal.RowForm.cnormSq_nonneg (velArray D.azimuthOrder ι' v p),
      CellCalculus.Internal.RowForm.cnormSq_nonneg (fun a => ∑ c : Fin 3, slopeAt D.azimuthOrder ι' H a c c p),
      CellCalculus.Internal.RowForm.cnormSq_nonneg (velArray D.azimuthOrder ι' Pg p)]
  have hvelSq : ∀ ι' a, RectSquare (D.mesh.box K) (fun p => velAt D.azimuthOrder ι' v a p) := by
    intro ι' a
    obtain ⟨mV, -, -, -⟩ := CellCalculus.Internal.LabelRowProfile.profile_measurable _ hK D.azimuthOrder v G H Pg
      hv2 ht.pressure ι'
    have hI := CellCalculus.Internal.LabelRowProfile.profile_integrable harmonicLift_holds harmonicPressureLift_holds
      _ hK D.azimuthOrder v G H Pg hv2 ht.pressure ι'
    refine ⟨mV a, CellCalculus.Internal.RowForm.comp_int hK hI (mV a) fun p hp => ?_⟩
    have h0 := CellCalculus.Internal.RowForm.fst_nonneg hK hp
    refine mul_le_mul_of_nonneg_left ?_ h0
    have h1 : ‖velAt D.azimuthOrder ι' v a p‖ ^ 2 ≤ cnormSq (velArray D.azimuthOrder ι' v p) :=
      CellCalculus.Internal.RowForm.le_cnormSq (velArray D.azimuthOrder ι' v p) a
    have h2 : 0 ≤ ∑ a' : Fin 3, cnormSq (gradArray D.azimuthOrder ι' G p a') :=
      Finset.sum_nonneg fun _ _ => CellCalculus.Internal.RowForm.cnormSq_nonneg _
    linarith [CellCalculus.Internal.RowForm.cnormSq_nonneg (fun a => ∑ c : Fin 3, slopeAt D.azimuthOrder ι' H a c c p),
      CellCalculus.Internal.RowForm.cnormSq_nonneg (velArray D.azimuthOrder ι' Pg p)]
  have hbandSq : ∀ ι' j, RectSquare (D.mesh.box K) (fun p => bandProfile D ι' v G p j) := by
    intro ι' j
    by_cases hj : j.val < 9
    · simp only [bandProfile, pairVec, dif_pos hj]
      exact hgradSq ι' _ _
    · simp only [bandProfile, pairVec, dif_neg hj]
      exact hvelSq ι' _
  have cW : Continuous (fun z : ℝ × Space => D.given z.1 z.2) := hW.smooth.continuous
  have cV : Continuous (fun z : ℝ × Space => vorticityOf D.given z.1 z.2) :=
    Internal.RemainderRegular.continuous_curlVec.comp (Internal.RemainderRegular.continuous_slice_fderiv hW.smooth)
  have ctv : ∀ α a, Continuous (fun p => trueVelocity D α p a) := fun α a => continuous_labelVel cW _ α a
  have ctw : ∀ α a, Continuous (fun p => trueVorticity D α p a) := fun α a => continuous_labelVel cV _ α a
  have cφ : ∀ a, Continuous (fun p => rowTestValue D K (A.blocks K) i p a) := fun a =>
    CellCalculus.Internal.RowForm.eval_cont _ _
  have rMv : ∀ α, ∃ W' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => W' p a) ∧
      ∀ p ∈ (D.mesh.box K).rect, modelVelocity D K α p = W' p := fun α =>
    ⟨_, fun a => CellCalculus.Internal.RowForm.eval_cont _ _, fun p hp => modelVelocity_eq_poly D K hK α hp⟩
  have rMw : ∀ α, ∃ W' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => W' p a) ∧
      ∀ p ∈ (D.mesh.box K).rect, modelVorticity D K α p = W' p := fun α =>
    ⟨_, fun a => CellCalculus.Internal.RowForm.eval_cont _ _, fun p hp => modelVorticity_eq_poly D K hK α hp⟩
  obtain ⟨cLv, cLw, -, -⟩ := (hCC.model_split K).long_regular
  have mLv : ∀ α a, AEStronglyMeasurable (fun p => longVelocity D R K α p a) (volume.restrict (D.mesh.box K).rect) :=
    fun α a => (CellCalculus.Internal.LabelRowProfile.vel_meas (aestronglyMeasurable_off_axis cLv) D.azimuthOrder α a).mono_measure
      (CellCalculus.Internal.LabelRowProfile.rect_le_half _ hK)
  have mLw : ∀ α a, AEStronglyMeasurable (fun p => longVorticity D R K α p a) (volume.restrict (D.mesh.box K).rect) :=
    fun α a => (CellCalculus.Internal.LabelRowProfile.vel_meas (aestronglyMeasurable_off_axis cLw) D.azimuthOrder α a).mono_measure
      (CellCalculus.Internal.LabelRowProfile.rect_le_half _ hK)
  have hLb : ∀ α, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ∀ a,
      ‖longVelocity D R K α p a‖ ≤ max (R.long K).errVelocity (R.long K).errVorticity ∧
      ‖longVorticity D R K α p a‖ ≤ max (R.long K).errVelocity (R.long K).errVorticity := by
    intro α
    filter_upwards [ae_own_point D.mesh hM K, ae_restrict_mem (CellCalculus.Internal.RowForm.rect_meas _)] with p hp hpr
    have horb : ∀ φ, axialRot φ (planePoint p) ∈ ownSolid D.mesh.box K :=
      orbit_mem_ownSolid D.mesh.box K hK p hpr hp.1 hp.2
    intro a
    exact ⟨norm_labelVel_le_orbit (fun σ φ => ((hCC.model_split K).velocity.long_bound σ _ (horb φ)).trans
        (le_max_left _ _)) _ _ a,
      norm_labelVel_le_orbit (fun σ φ => ((hCC.model_split K).vorticity.long_bound σ _ (horb φ)).trans
        (le_max_right _ _)) _ _ a⟩
  have rTv : ∀ α, ∃ W' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => W' p a) ∧
      ∀ p ∈ (D.mesh.box K).rect, trueVelocity D α p = W' p := fun α => ⟨_, ctv α, fun _ _ => rfl⟩
  have rTw : ∀ α, ∃ W' : ℝ × ℝ → Fin 3 → ℂ, (∀ a, Continuous fun p => W' p a) ∧
      ∀ p ∈ (D.mesh.box K).rect, trueVorticity D α p = W' p := fun α => ⟨_, ctw α, fun _ _ => rfl⟩
  set ownM : ℂ := ∑ d, ownRowVector ((R.layouts K).layout ((A.blocks K).rowLabel i)) (labelAzimuth D.azimuthOrder ((A.blocks K).rowLabel i) : ℝ)
      (2 * Real.pi * (labelTime ((A.blocks K).rowLabel i) : ℝ) * D.model.periodInverse) (rowTestPoly D K (A.blocks K) i) d
      * harmonicData ((R.layouts K).layout ((A.blocks K).rowLabel i)) (labelTime ((A.blocks K).rowLabel i)) v G H Pg d with hown
  set act : ℂ := ∑ l, (κ l : ℂ) * actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i) (D.cert.actuator l) with hact'
  set actB : ℂ := ∑ l, (κ l : ℂ) * actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i)
    ((A.blocks K).actuatorModel (l : ℕ)) with hactB'
  have EA : rowMoment D K (A.blocks K) F i = ownM + freqPiece D K (A.blocks K) (D.cert.period q) v i
      + ∑ α ∈ (P.potential K).harmonicLabels, pairShift D K (A.blocks K) i v G α + act := by
    obtain ⟨hsol, hreg, hshape, hdeg, hpres⟩ := hFun.tests_valid K i
    have hlay := (hCC.layouts_valid K).layout_valid _ hιr
    have hax : (D.mesh.box K).IsAxis → ((A.blocks K).rowLabel i).1 = 0 := fun h => hCC.axis_modes K h _ hιr
    obtain ⟨e1, e2, e3, hadm⟩ := hFR.admissible
    have hP : 0 < D.cert.period q := (hadm q ht.param).period_pos
    have hbm : ∀ l, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.actuator l z.1 z.2) volume :=
      fun l => (hact l).choose_spec.measurable
    have hbb : ∀ l, ∃ C : ℝ, ∀ σ y, ‖D.cert.actuator l σ y‖ ≤ C := fun l => by
      obtain ⟨B', R', h⟩ := (hact l).choose_spec.bounded_support
      exact ⟨B', fun σ y => (h σ y).1⟩
    have hdec := labelVel_right_plane ht.perturbation hP hclass hW hS (P.potential K).harmonicLabels
      (hPot.labels_iff K) hbm hbb κ ht.pressure ht.right_side ((A.blocks K).rowLabel i)
    have hRpv := labelRowProfile_valid harmonicLift_holds harmonicPressureLift_holds (D.mesh.box K) hK D.azimuthOrder
      v G H Pg hv2 ht.pressure ((A.blocks K).rowLabel i) hax
    have hcoupleSq : ∀ a, RectSquare (D.mesh.box K) (fun p => ∑ α ∈ (P.potential K).harmonicLabels, ∑ j : Fin 3,
        ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
          (curlComp (gradArray D.azimuthOrder ((A.blocks K).rowLabel i - α) G p) j * labelVel D.azimuthOrder α D.given p l
            + labelVel D.azimuthOrder α (vorticityOf D.given) p j
              * velAt D.azimuthOrder ((A.blocks K).rowLabel i - α) v l p)) := by
      intro a
      refine rectSquare_sum hK _ fun α _ => rectSquare_sum hK _ fun j _ => rectSquare_sum hK _ fun l _ => ?_
      refine rectSquare_const_mul hK (rectSquare_add hK ?_ ?_) _
      · have hc : RectSquare (D.mesh.box K)
            (fun p => curlComp (gradArray D.azimuthOrder ((A.blocks K).rowLabel i - α) G p) j) := by
          unfold curlComp
          refine rectSquare_sum hK _ fun j' _ => rectSquare_sum hK _ fun l' _ => ?_
          exact rectSquare_const_mul hK (hgradSq _ l' j') _
        obtain ⟨hm, M, hM⟩ := rect_regular_of_eqOn (ctv α l) (f := fun p => trueVelocity D α p l) fun _ _ => rfl
        exact rectSquare_mul_right hK hc hm hM
      · obtain ⟨hm, M, hM⟩ := rect_regular_of_eqOn (ctw α j) (f := fun p => trueVorticity D α p j) fun _ _ => rfl
        exact rectSquare_mul hK (hvelSq _ l) hm hM
    have hdriveSq : ∀ a, RectSquare (D.mesh.box K) (fun p => ∑ l, (κ l : ℂ) *
        labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p a) := by
      intro a
      refine rectSquare_sum hK _ fun l _ => rectSquare_const_mul hK ?_ _
      obtain ⟨C', hC'⟩ := hbb l
      exact rectSquare_bounded hK ((CellCalculus.Internal.LabelRowProfile.vel_meas (hbm l) D.azimuthOrder _ a).mono_measure
        (CellCalculus.Internal.LabelRowProfile.rect_le_half _ hK)) (M := C')
        fun p _ => norm_labelVel_le hC' _ _ p a
    have hcm : AEStronglyMeasurable (fun p => fun a => ∑ α ∈ (P.potential K).harmonicLabels, ∑ j : Fin 3,
        ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
          (curlComp (gradArray D.azimuthOrder ((A.blocks K).rowLabel i - α) G p) j * labelVel D.azimuthOrder α D.given p l
            + labelVel D.azimuthOrder α (vorticityOf D.given) p j
              * velAt D.azimuthOrder ((A.blocks K).rowLabel i - α) v l p)) (volume.restrict (D.mesh.box K).rect) :=
      (aemeasurable_pi_iff.2 fun a => (hcoupleSq a).1.aemeasurable).aestronglyMeasurable
    have hdm : AEStronglyMeasurable (fun p => fun a => ∑ l, (κ l : ℂ) *
        labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p a) (volume.restrict (D.mesh.box K).rect) :=
      (aemeasurable_pi_iff.2 fun a => (hdriveSq a).1.aemeasurable).aestronglyMeasurable
    have hcd : IntegrableOn (fun p => p.1 * (cnormSq (fun a => ∑ α ∈ (P.potential K).harmonicLabels, ∑ j : Fin 3,
        ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
          (curlComp (gradArray D.azimuthOrder ((A.blocks K).rowLabel i - α) G p) j * labelVel D.azimuthOrder α D.given p l
            + labelVel D.azimuthOrder α (vorticityOf D.given) p j
              * velAt D.azimuthOrder ((A.blocks K).rowLabel i - α) v l p))
        + cnormSq (fun a => ∑ l, (κ l : ℂ) *
          labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p a))) (D.mesh.box K).rect := by
      have h := (integrable_finsetSum Finset.univ fun a _ => (hcoupleSq a).2).add
        (integrable_finsetSum Finset.univ fun a _ => (hdriveSq a).2)
      refine h.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [cnormSq, Pi.add_apply, mul_add, Finset.mul_sum]
    have hLsq : ∀ l a, RectSquare (D.mesh.box K) (fun p => labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p a) := by
      intro l a
      obtain ⟨C', hC'⟩ := hbb l
      exact rectSquare_bounded hK ((CellCalculus.Internal.LabelRowProfile.vel_meas (hbm l) D.azimuthOrder _ a).mono_measure
        (CellCalculus.Internal.LabelRowProfile.rect_le_half _ hK)) (M := C')
        fun p _ => norm_labelVel_le hC' _ _ p a
    have hfm : labelTimeFreq (D.model.periodInverse)⁻¹ ((A.blocks K).rowLabel i) = (2 * Real.pi * (labelTime ((A.blocks K).rowLabel i) : ℝ) * D.model.periodInverse) := by
      unfold labelTimeFreq
      rw [div_inv_eq_mul]
    have hmodes : ((R.layouts K).layout ((A.blocks K).rowLabel i)).modes = {((A.blocks K).rowLabel i).1} := by
      obtain ⟨c, S', -, hSr, hcl⟩ := hlay
      exact hcl.modes_eq.trans hSr
    have hlay' : IsHarmonicLayout D.azimuthOrder (D.mesh.box K) (R.layouts K).bases ((R.layouts K).layout ((A.blocks K).rowLabel i)).modes
        ((R.layouts K).layout ((A.blocks K).rowLabel i)) := by
      rw [hmodes]; exact hlay
    have hlow := rowLowPart_holds harmonicLift_holds harmonicPressureLift_holds (harmonicSideData_holds harmonicLift_holds)
      D.azimuthOrder (D.mesh.box K) (R.layouts K).bases ((R.layouts K).layout ((A.blocks K).rowLabel i)) hlay' v G H Pg hv2 ht.pressure
      ((A.blocks K).rowLabel i) hmodes hax (D.model.periodInverse)⁻¹ (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg) hRpv
      (Filter.Eventually.of_forall fun p => ⟨rfl, rfl, rfl, rfl⟩) (rowTestPoly D K (A.blocks K) i) hsol hreg hshape hdeg hpres
    rw [hfm, ← hown] at hlow
    have hcrf := cellRowFormula_holds (D.mesh.box K) hK (labelAzimuth D.azimuthOrder ((A.blocks K).rowLabel i) : ℝ) (labelTimeFreq (D.cert.period q) ((A.blocks K).rowLabel i)) (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg) hRpv _ _ _ hcm hdm hcd (fun p _ => rfl) (rowTestPoly D K (A.blocks K) i) hsol hreg
    have hmom : rowMoment D K (A.blocks K) F i = rowPairing (D.mesh.box K) (fun p => fun a => ((((labelTimeFreq (D.cert.period q) ((A.blocks K).rowLabel i)) : ℝ) : ℂ) * Complex.I + 1 / 2) * (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg).vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg).grad p a 0 + (p.2 : ℂ) * (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg).grad p a 2)
          - (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg).lap p a + (∑ α ∈ (P.potential K).harmonicLabels, ∑ j : Fin 3,
        ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
          (curlComp (gradArray D.azimuthOrder (((A.blocks K).rowLabel i) - α) G p) j * labelVel D.azimuthOrder α D.given p l
            + labelVel D.azimuthOrder α (vorticityOf D.given) p j
              * velAt D.azimuthOrder (((A.blocks K).rowLabel i) - α) v l p)) + (∑ l, (κ l : ℂ) * labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p a) + (labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg).presGrad p a) (rowTestPoly D K (A.blocks K) i) := by
      show rowPairing (D.mesh.box K) (fun p => labelVel D.azimuthOrder ((A.blocks K).rowLabel i) F p) (rowTestPoly D K (A.blocks K) i) = _
      unfold rowPairing
      refine setIntegral_congr_ae (CellCalculus.Internal.RowForm.rect_meas _) ?_
      filter_upwards [hdec, CellCalculus.Internal.RowCouplingLow.fst_ne_zero_ae] with p hp hp0 hpr
      have hp1 : 0 < p.1 := lt_of_le_of_ne (CellCalculus.Internal.RowForm.fst_nonneg hK hpr) (Ne.symm hp0)
      congr 2
      funext a
      rw [hp hp1 a]
      rfl
    have hshift := rowVolume_freq_shift hK hRpv hreg (labelTimeFreq (D.cert.period q) ((A.blocks K).rowLabel i)) (2 * Real.pi * (labelTime ((A.blocks K).rowLabel i) : ℝ) * D.model.periodInverse)
    have hfreq : freqPiece D K (A.blocks K) (D.cert.period q) v i
        = ((((labelTimeFreq (D.cert.period q) ((A.blocks K).rowLabel i)) - (2 * Real.pi * (labelTime ((A.blocks K).rowLabel i) : ℝ) * D.model.periodInverse) : ℝ)) : ℂ) * Complex.I * ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * cdot3 ((labelRowProfile (D.mesh.box K) D.azimuthOrder ((A.blocks K).rowLabel i) v G H Pg).vel p) (testValue (D.mesh.box K) (rowTestPoly D K (A.blocks K) i) p) := by
      unfold freqPiece
      congr 3
      unfold labelTimeFreq
      ring
    have hdrive : rowPairing (D.mesh.box K) (fun p => fun a => ∑ l, (κ l : ℂ) * labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p a) (rowTestPoly D K (A.blocks K) i) = act := by
      rw [hact']
      unfold rowPairing actuatorRow
      have hI : ∀ l ∈ Finset.univ, IntegrableOn (fun p => (κ l : ℂ) * ((p.1 : ℂ) *
          ∑ c : Fin 3, labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p c
            * (starRingEnd ℂ) ((rowTestPoly D K (A.blocks K) i c).eval (D.mesh.box K) p))) (D.mesh.box K).rect :=
        fun l _ => (CellCalculus.Internal.RowForm.pair_int hK (rowTestPoly D K (A.blocks K) i)
          ((aemeasurable_pi_iff.2 fun a => (hLsq l a).1.aemeasurable).aestronglyMeasurable) fun a => (hLsq l a).2).const_mul _
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ hI]
      refine setIntegral_congr_fun (CellCalculus.Internal.RowForm.rect_meas _) fun p _ => ?_
      simp only [cdot3, testValue, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    have hcouple : rowPairing (D.mesh.box K) (fun p => fun a => ∑ α ∈ (P.potential K).harmonicLabels, ∑ j : Fin 3,
        ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
          (curlComp (gradArray D.azimuthOrder (((A.blocks K).rowLabel i) - α) G p) j * labelVel D.azimuthOrder α D.given p l
            + labelVel D.azimuthOrder α (vorticityOf D.given) p j
              * velAt D.azimuthOrder (((A.blocks K).rowLabel i) - α) v l p)) (rowTestPoly D K (A.blocks K) i)
        = ∑ α ∈ (P.potential K).harmonicLabels, pairShift D K (A.blocks K) i v G α := by
      unfold rowPairing pairShift
      rw [← integral_finsetSum _ fun α _ => pair_integrableOn hK (hbandSq _) (rTv α) (rTw α) cφ]
      refine setIntegral_congr_fun (CellCalculus.Internal.RowForm.rect_meas _) fun p _ => ?_
      have e : ∀ α, ∑ j, bandProfile D (((A.blocks K).rowLabel i) - α) v G p j * (starRingEnd ℂ) (crossTest (trueVelocity D α p)
          (trueVorticity D α p) (rowTestValue D K (A.blocks K) i p) j)
          = cdot3 (fun a => ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
            (curlComp (gradArray D.azimuthOrder (((A.blocks K).rowLabel i) - α) G p) j * labelVel D.azimuthOrder α D.given p l
              + labelVel D.azimuthOrder α (vorticityOf D.given) p j
                * velAt D.azimuthOrder (((A.blocks K).rowLabel i) - α) v l p)) (testValue (D.mesh.box K) (rowTestPoly D K (A.blocks K) i) p) :=
        fun α => cross_pairing _ _ _ _ _
      simp only [e]
      simp only [cdot3, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hmom, hcrf, hshift, hcouple, hdrive, hfreq]
    linear_combination hlow
  have hpz : ∀ ι', (A.blocks K).rowLabel i - ι' ∉ (P.potential K).harmonicLabels →
      pairTrue D K (A.blocks K) i v G ι' = 0 := by
    intro ι' hn
    have hh : labelHarmonic D.azimuthOrder ((A.blocks K).rowLabel i - ι') ∉ D.givenLabels :=
      fun h => hn ((hPot.labels_iff K _).2 h)
    have hz : ∀ p, crossTest (trueVelocity D ((A.blocks K).rowLabel i - ι') p)
        (trueVorticity D ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p) = 0 := by
      intro p
      obtain ⟨a1, a2⟩ := labelVel_given_off_label hW hS D.azimuthOrder hh p
      have e1 : trueVelocity D ((A.blocks K).rowLabel i - ι') p = 0 := funext fun a => congrFun a1 a
      have e2 : trueVorticity D ((A.blocks K).rowLabel i - ι') p = 0 := funext fun a => congrFun a2 a
      rw [e1, e2, crossTest_zero]
    unfold pairTrue
    simp only [hz, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, integral_zero]
  have hshift : ∀ α, pairShift D K (A.blocks K) i v G α
      = pairTrue D K (A.blocks K) i v G ((A.blocks K).rowLabel i - α) := by
    intro α
    unfold pairShift pairTrue
    simp only [sub_sub_cancel]
  have hdisj : Disjoint (D.mesh.resolved K ∪ D.mesh.band K) (deactSources D K (P.potential K)) := by
    rw [Finset.disjoint_right]
    intro ι h
    have h' := (Finset.mem_filter.1 h).2
    rw [Finset.mem_union, not_or]
    exact h'
  have hmemS : ∀ α ∈ (P.potential K).harmonicLabels, ((A.blocks K).rowLabel i - α ∈ deactSources D K (P.potential K) ↔
      (A.blocks K).rowLabel i - α ∉ D.mesh.resolved K ∧ (A.blocks K).rowLabel i - α ∉ D.mesh.band K) := by
    intro α hα
    constructor
    · intro h
      exact (Finset.mem_filter.1 h).2
    · intro h
      exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨((A.blocks K).rowLabel i, α), Finset.mem_product.2 ⟨hιt, hα⟩, rfl⟩, h⟩
  have EB : ∑ α ∈ (P.potential K).harmonicLabels, pairShift D K (A.blocks K) i v G α
      = ∑ ι' ∈ D.mesh.resolved K, pairTrue D K (A.blocks K) i v G ι' + ∑ ι' ∈ D.mesh.band K, pairTrue D K (A.blocks K) i v G ι'
        + ∑ ι' ∈ deactSources D K (P.potential K), pairTrue D K (A.blocks K) i v G ι' := by
    classical
    have hsplit : ∀ α ∈ (P.potential K).harmonicLabels, pairShift D K (A.blocks K) i v G α
        = ((if (A.blocks K).rowLabel i - α ∈ D.mesh.resolved K then pairShift D K (A.blocks K) i v G α else 0)
          + (if (A.blocks K).rowLabel i - α ∈ D.mesh.band K then pairShift D K (A.blocks K) i v G α else 0))
          + (if (A.blocks K).rowLabel i - α ∈ deactSources D K (P.potential K) then pairShift D K (A.blocks K) i v G α else 0) := by
      intro α hα
      have hm := hmemS α hα
      by_cases h1 : (A.blocks K).rowLabel i - α ∈ D.mesh.resolved K
      · have h2 : (A.blocks K).rowLabel i - α ∉ D.mesh.band K := Finset.disjoint_left.1 (hM.band_apart K) h1
        have h3 : (A.blocks K).rowLabel i - α ∉ deactSources D K (P.potential K) := fun h => (hm.1 h).1 h1
        simp [h1, h2, h3]
      · by_cases h2 : (A.blocks K).rowLabel i - α ∈ D.mesh.band K
        · have h3 : (A.blocks K).rowLabel i - α ∉ deactSources D K (P.potential K) := fun h => (hm.1 h).2 h2
          simp [h1, h2, h3]
        · have h3 : (A.blocks K).rowLabel i - α ∈ deactSources D K (P.potential K) := hm.2 ⟨h1, h2⟩
          simp [h1, h2, h3]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    congr 1
    · exact shift_sum _ _ _ hshift fun ι' _ hn => hpz ι' hn
    · exact shift_sum _ _ _ hshift fun ι' _ hn => hpz ι' hn
    · exact shift_sum _ _ _ hshift fun ι' _ hn => hpz ι' hn
  have EC : ∀ ι', pairTrue D K (A.blocks K) i v G ι' = pairModel D K (A.blocks K) i v G ι'
      + pairLong D R K (A.blocks K) i v G ι' + pairError D R K (A.blocks K) i v G ι' := by
    intro ι'
    have hpt : ∀ p : ℝ × ℝ, (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest (trueVelocity D ((A.blocks K).rowLabel i - ι') p) (trueVorticity D ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p) j)
        = (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest (modelVelocity D K ((A.blocks K).rowLabel i - ι') p) (modelVorticity D K ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p) j)
          + (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest (longVelocity D R K ((A.blocks K).rowLabel i - ι') p) (longVorticity D R K ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p) j)
          + (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest (fun a => trueVelocity D ((A.blocks K).rowLabel i - ι') p a - modelVelocity D K ((A.blocks K).rowLabel i - ι') p a - longVelocity D R K ((A.blocks K).rowLabel i - ι') p a) (fun a => trueVorticity D ((A.blocks K).rowLabel i - ι') p a - modelVorticity D K ((A.blocks K).rowLabel i - ι') p a - longVorticity D R K ((A.blocks K).rowLabel i - ι') p a) (rowTestValue D K (A.blocks K) i p) j) := by
      intro p
      have e : crossTest (trueVelocity D ((A.blocks K).rowLabel i - ι') p) (trueVorticity D ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p)
          = crossTest (modelVelocity D K ((A.blocks K).rowLabel i - ι') p) (modelVorticity D K ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p)
            + crossTest (longVelocity D R K ((A.blocks K).rowLabel i - ι') p) (longVorticity D R K ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p)
            + crossTest (fun a => trueVelocity D ((A.blocks K).rowLabel i - ι') p a - modelVelocity D K ((A.blocks K).rowLabel i - ι') p a - longVelocity D R K ((A.blocks K).rowLabel i - ι') p a) (fun a => trueVorticity D ((A.blocks K).rowLabel i - ι') p a - modelVorticity D K ((A.blocks K).rowLabel i - ι') p a - longVorticity D R K ((A.blocks K).rowLabel i - ι') p a) (rowTestValue D K (A.blocks K) i p) := by
        rw [← crossTest_add, ← crossTest_add]
        congr 1 <;> funext a <;> simp only [Pi.add_apply] <;> ring
      simp only [e, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    have hT := pair_integrableOn hK (hbandSq ι') (rTv ((A.blocks K).rowLabel i - ι')) (rTw ((A.blocks K).rowLabel i - ι')) cφ
    have hMi := pair_integrableOn hK (hbandSq ι') (rMv ((A.blocks K).rowLabel i - ι')) (rMw ((A.blocks K).rowLabel i - ι')) cφ
    have hLi := pair_integrableOn_ae hK (hbandSq ι') (mLv ((A.blocks K).rowLabel i - ι')) (mLw ((A.blocks K).rowLabel i - ι')) cφ (hLb ((A.blocks K).rowLabel i - ι'))
    have hEi : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ j, bandProfile D ι' v G p j * (starRingEnd ℂ) (crossTest (fun a => trueVelocity D ((A.blocks K).rowLabel i - ι') p a - modelVelocity D K ((A.blocks K).rowLabel i - ι') p a - longVelocity D R K ((A.blocks K).rowLabel i - ι') p a) (fun a => trueVorticity D ((A.blocks K).rowLabel i - ι') p a - modelVorticity D K ((A.blocks K).rowLabel i - ι') p a - longVorticity D R K ((A.blocks K).rowLabel i - ι') p a) (rowTestValue D K (A.blocks K) i p) j)) (D.mesh.box K).rect :=
      (Integrable.sub (Integrable.sub hT hMi) hLi).congr (Filter.Eventually.of_forall fun p => by
        simp only [Pi.sub_apply]
        rw [hpt p]
        ring)
    unfold pairTrue pairModel pairLong pairError
    rw [← integral_add_three hMi hLi hEi]
    exact setIntegral_congr_fun (CellCalculus.Internal.RowForm.rect_meas _) fun p _ => hpt p
  have ED : ∀ ι' ∈ D.mesh.resolved K,
      pairModel D K (A.blocks K) i v G ι' = lowRow D R K (A.blocks K) i v G H Pg ι' + tailTerm D R K (A.blocks K) i v G ι' := by
    intro ι' hr
    have hlay := (hCC.layouts_valid K).layout_valid ι' hr
    have hax : (D.mesh.box K).IsAxis → ι'.1 = 0 := fun h => hCC.axis_modes K h ι' hr
    have h := resolved_model_pairing D.azimuthOrder (D.mesh.box K) (R.layouts K).bases ((R.layouts K).layout ι') ι'
      hlay v G H Pg hv2 ht.pressure hax (modelVelocity D K ((A.blocks K).rowLabel i - ι'))
      (modelVorticity D K ((A.blocks K).rowLabel i - ι')) (rMv _) (rMw _) (rowTestPoly D K (A.blocks K) i)
    refine h.trans ?_
    unfold lowRow tailTerm
    congr 1
    refine setIntegral_congr_fun (CellCalculus.Internal.RowForm.rect_meas _) fun p hp => ?_
    simp only [tailProfile]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFun.row_tail K i ι' hr p hp j]
    rfl
  have EE : ∀ ι' ∈ D.mesh.band K, bandTerm D K (A.blocks K) i v G ι' = pairModel D K (A.blocks K) i v G ι' := by
    intro ι' hb
    unfold bandTerm pairModel
    refine setIntegral_congr_fun (CellCalculus.Internal.RowForm.rect_meas _) fun p hp => ?_
    simp only [hFun.row_band K i ι' hb p hp]
    rfl
  have hzM : ∀ ι' ∈ deactSources D K (P.potential K), (A.blocks K).rowLabel i - ι' ∉ (P.potential K).harmonicLabels →
      pairModel D K (A.blocks K) i v G ι' = 0 := by
    intro ι' _ hn
    have hz : ∀ p ∈ (D.mesh.box K).rect, modelVelocity D K ((A.blocks K).rowLabel i - ι') p = 0 ∧
        modelVorticity D K ((A.blocks K).rowLabel i - ι') p = 0 := fun p hp =>
      ⟨funext (hPot.model_labels_in K _ hn p hp).1, funext (hPot.model_labels_in K _ hn p hp).2⟩
    unfold pairModel
    rw [setIntegral_congr_fun (CellCalculus.Internal.RowForm.rect_meas _) (g := fun _ => (0 : ℂ)) fun p hp => by
      simp only [(hz p hp).1, (hz p hp).2, crossTest_zero, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]]
    exact integral_zero _ _
  have EDe : deactPiece D K (A.blocks K) (P.potential K).harmonicLabels v G i = ∑ ι' ∈ deactSources D K (P.potential K), pairModel D K (A.blocks K) i v G ι' := by
    rw [← shift_sum (S := deactSources D K (P.potential K)) (T := (P.potential K).harmonicLabels) ((A.blocks K).rowLabel i)
      (fun α => pairModel D K (A.blocks K) i v G ((A.blocks K).rowLabel i - α)) (pairModel D K (A.blocks K) i v G) (fun _ => rfl) hzM]
    unfold deactPiece
    refine Finset.sum_congr rfl fun α hα => ?_
    have hm := hmemS α hα
    by_cases h : (A.blocks K).rowLabel i - α ∈ deactSources D K (P.potential K)
    · rw [if_pos (hm.1 h), if_pos h]
      unfold pairModel
      simp only [sub_sub_cancel]
    · rw [if_neg (fun h' => h (hm.2 h')), if_neg h]
  have EF : rowVector D K (A.blocks K) x (fun ι => bandProfile D ι v G) i = ownM
      + ∑ ι' ∈ D.mesh.resolved K, lowRow D R K (A.blocks K) i v G H Pg ι' + actB
      + ∑ ι' ∈ D.mesh.band K, bandTerm D K (A.blocks K) i v G ι' := by
    show ((A.blocks K).rowMap *ᵥ x) i + _ = _
    rw [hFun.row_map K i x (hstates K q v G H g κ F Pg ht ζ η)]
    congr 1
    congr 1
    congr 1
    · rw [Fintype.sum_eq_single ⟨_, hιr⟩ fun b hb => if_neg fun h => hb (Subtype.ext h), if_pos rfl]
      rfl
    · exact Finset.sum_coe_sort (D.mesh.resolved K) (fun ι' => lowRow D R K (A.blocks K) i v G H Pg ι')
  have EG : tailRow D R K (A.blocks K) v G i = ∑ ι' ∈ D.mesh.resolved K, tailTerm D R K (A.blocks K) i v G ι' := rfl
  have EH : errorPiece D R K (A.blocks K) (P.potential K) v G i = ∑ ι' ∈ D.mesh.resolved K, pairError D R K (A.blocks K) i v G ι'
      + ∑ ι' ∈ D.mesh.band K, pairError D R K (A.blocks K) i v G ι' + ∑ ι' ∈ deactSources D K (P.potential K), pairError D R K (A.blocks K) i v G ι' := by
    show ∑ ι' ∈ D.mesh.resolved K ∪ D.mesh.band K ∪ deactSources D K (P.potential K), pairError D R K (A.blocks K) i v G ι' = _
    rw [Finset.sum_union hdisj, Finset.sum_union (hM.band_apart K)]
  have EL : longPiece D R K (A.blocks K) (P.potential K) v G i = ∑ ι' ∈ D.mesh.resolved K, pairLong D R K (A.blocks K) i v G ι'
      + ∑ ι' ∈ D.mesh.band K, pairLong D R K (A.blocks K) i v G ι' + ∑ ι' ∈ deactSources D K (P.potential K), pairLong D R K (A.blocks K) i v G ι' := by
    show ∑ ι' ∈ D.mesh.resolved K ∪ D.mesh.band K ∪ deactSources D K (P.potential K), pairLong D R K (A.blocks K) i v G ι' = _
    rw [Finset.sum_union hdisj, Finset.sum_union (hM.band_apart K)]
  have hsR : ∑ ι' ∈ D.mesh.resolved K, pairTrue D K (A.blocks K) i v G ι'
      = ∑ ι' ∈ D.mesh.resolved K, lowRow D R K (A.blocks K) i v G H Pg ι' + ∑ ι' ∈ D.mesh.resolved K, tailTerm D R K (A.blocks K) i v G ι'
        + ∑ ι' ∈ D.mesh.resolved K, pairLong D R K (A.blocks K) i v G ι'
        + ∑ ι' ∈ D.mesh.resolved K, pairError D R K (A.blocks K) i v G ι' := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ι' h => ?_
    rw [EC ι', ED ι' h]
  have hsB : ∑ ι' ∈ D.mesh.band K, pairTrue D K (A.blocks K) i v G ι'
      = ∑ ι' ∈ D.mesh.band K, bandTerm D K (A.blocks K) i v G ι' + ∑ ι' ∈ D.mesh.band K, pairLong D R K (A.blocks K) i v G ι'
        + ∑ ι' ∈ D.mesh.band K, pairError D R K (A.blocks K) i v G ι' := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ι' h => ?_
    rw [EC ι', EE ι' h]
  have hsD : ∑ ι' ∈ deactSources D K (P.potential K), pairTrue D K (A.blocks K) i v G ι'
      = ∑ ι' ∈ deactSources D K (P.potential K), pairModel D K (A.blocks K) i v G ι' + ∑ ι' ∈ deactSources D K (P.potential K), pairLong D R K (A.blocks K) i v G ι'
        + ∑ ι' ∈ deactSources D K (P.potential K), pairError D R K (A.blocks K) i v G ι' := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ι' _ => EC ι'
  have EAc : actuatorPiece D K (A.blocks K) κ i = act - actB := by
    simp only [actuatorPiece, hact', hactB', mul_sub, Finset.sum_sub_distrib]
  rw [EA, EF, EG, EH, EL, EB, hsR, hsB, hsD, EDe, EAc]
  ring

theorem rowIdentity_holds : RowIdentityHolds := by
  intro k C nE nM D R A P states hstates hReg hTF tauMax hT hact hclass hPot hC hFun K q v G H g κ F Pg ht ζ η
  funext i
  simp only [Pi.sub_apply, Pi.add_apply]
  exact rowIdentity_entry D R A P hReg hTF hact hclass hPot hC hFun K ht ζ η i hstates

end Breakdown.CertCell.Assembly
