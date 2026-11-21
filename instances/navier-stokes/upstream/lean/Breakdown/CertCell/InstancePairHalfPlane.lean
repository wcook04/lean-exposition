import Breakdown.CertCell.InstancePairStatements
import Breakdown.CertCell.PinHalfPlane
import Breakdown.CertCell.ModeFlip
import Breakdown.CertCell.HalfPlaneReduction
import Breakdown.CertCell.PairingModeIdentity
import Breakdown.CertCell.LabelArithmetic
import Breakdown.CertCell.TailAngularPlane

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

namespace Internal.PairHalf

open Coercive Bridge Bridge.Internal.PinHalf

def FlipModes (A : ℝ → Space → (Space →L[ℝ] Space)) : Prop :=
  ∀ ξ : ℤ × ℤ, ∀ᵐ z : ℝ × Space, modeGrad (flipLabel ξ) A z.1 (flipPoint z.2)
    = fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ A z.1 z.2 ab

theorem flipModes_of_ae {A : ℝ → Space → (Space →L[ℝ] Space)}
    (h : ∀ᵐ z : ℝ × Space, ∀ u : Space, A z.1 (flipPoint z.2) u = flipPoint (A z.1 z.2 (flipPoint u))) :
    FlipModes A := by
  intro ξ
  filter_upwards [Bridge.Internal.ModeFlip.ae_orbit h] with z hz
  exact Bridge.Internal.ModeFlip.modeGrad_flip_of ξ hz

theorem flipModes_of_perturbation (hX : ModeFlipHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hfl : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) : FlipModes G :=
  fun ξ => (hX Γ P v G H g hv hfl ξ).mono fun _ hz => hz.2.1

theorem ae_pairDensity_flip_modes {A B : ℝ → Space → (Space →L[ℝ] Space)} (hAp : IsTimePeriodic A)
    (hBp : IsTimePeriodic B) (hA : FlipModes A) (hB : FlipModes B) (ξ : ℤ × ℤ) :
    ∀ᵐ y, pairDensity (flipLabel ξ) A B 0 (flipPoint y) = pairDensity ξ A B 0 y := by
  refine ae_of_snd ?_
  filter_upwards [hA ξ, hB ξ] with z hzA hzB
  rw [← pairDensity_shift hAp hBp (flipLabel ξ) z.1 (flipPoint z.2), ← pairDensity_shift hAp hBp ξ z.1 z.2]
  exact pairDensity_flip_of hzA hzB

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pairDensity_self (ξ : ℤ × ℤ) (A : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    pairDensity ξ A A σ y = cnormSq (modeGrad ξ A σ y) := by
  unfold pairDensity cdotMat cnormSq
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem norm_cdotMat_le (x z : Fin 3 × Fin 3 → ℂ) : ‖cdotMat x z‖ ≤ cnormSq x + cnormSq z := by
  unfold cdotMat cnormSq
  rw [← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (x i), norm_nonneg (z i), sq_nonneg (‖x i‖ - ‖z i‖)]

theorem halfPlane_modeNorm_lt_top (hH : HalfPlaneReductionHolds) {A : ℝ → Space → (Space →L[ℝ] Space)}
    (hAm : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume) (hAp : IsTimePeriodic A)
    (hAf : periodLIntegral (fun σ y => matSq (A σ y)) < ⊤) (hA : FlipModes A) (ξ : ℤ × ℤ) :
    ∫⁻ p in halfPlane, ENNReal.ofReal (cnormSq (modeGrad ξ A 0 (planePoint p))) * ENNReal.ofReal p.1 < ⊤ := by
  have hl := locallyIntegrable_of_squareSum hAm hAp hAf
  have hmeas : ∀ ξ, AEMeasurable (fun y => ENNReal.ofReal (cnormSq (modeGrad ξ A 0 y))) volume :=
    fun ξ => aemeas_cnormSq_zero hAm hAp ξ
  have key := hH (fun ξ y => ENNReal.ofReal (cnormSq (modeGrad ξ A 0 y))) hmeas (goodSet A A) (goodSet_rot A A)
    (ae_goodSet hAp hAp hl hl) (fun ξ φ y hy => by
      simp only [← pairDensity_self]
      exact congrArg ENNReal.ofReal (hy ξ φ)) (fun ξ => by
      filter_upwards [ae_pairDensity_flip_modes hAp hAp hA hA ξ] with y hy
      simp only [← pairDensity_self]
      exact congrArg ENNReal.ofReal hy)
  beta_reduce at key
  rw [lintegral_tsum hmeas] at key
  have hfin := modeNorm_tsum_lt_top hAm hAp hAf
  rw [key] at hfin
  have h4 : ENNReal.ofReal (4 * Real.pi) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hT : ∑' ξ, ∫⁻ p in halfPlane, ENNReal.ofReal (cnormSq (modeGrad ξ A 0 (planePoint p)))
      * ENNReal.ofReal p.1 < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hT => ?_
    rw [hT, ENNReal.mul_top h4] at hfin
    exact lt_irrefl _ hfin
  exact lt_of_le_of_lt (ENNReal.le_tsum ξ) hT

open TailBand.Internal.AngularPlane Coercive.Internal.ModeRotation in
theorem aesm_labelGrad {B : ℝ → Space → (Space →L[ℝ] Space)}
    (hBm : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume) (m : ℕ) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (labelGrad m ι B) (volume.restrict halfPlane) := by
  refine aestronglyMeasurable_of_coord fun ij => ?_
  have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ij.2))) ij.1) := by
    unfold axialRot
    fun_prop
  have h := (aestronglyMeasurable_orbitAverage hBm (labelHarmonic m ι)
    (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ij.2))) ij.1) hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [labelGrad, modeGrad, modeAverage_eq, zero_add]

theorem aesm_cnormSq {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → Fin 3 × Fin 3 → ℂ} (h : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun p => cnormSq (f p)) μ := by
  unfold cnormSq
  exact Finset.aestronglyMeasurable_fun_sum _ fun ij _ =>
    (((continuous_apply ij).comp_aestronglyMeasurable h).norm).pow 2

theorem rot_plane_coords (p : ℝ × ℝ) (φ : ℝ) (hp : p ∈ halfPlane) :
    (Real.sqrt (axialRot φ (planePoint p) 0 ^ 2 + axialRot φ (planePoint p) 1 ^ 2),
      |axialRot φ (planePoint p) 2|) = p := by
  have h0 : axialRot φ (planePoint p) 0 = Real.cos φ * p.1 := by
    simp [axialRot, TailBand.Internal.AngularPlane.planePoint_eq, unitVector]
  have h1 : axialRot φ (planePoint p) 1 = Real.sin φ * p.1 := by
    simp [axialRot, TailBand.Internal.AngularPlane.planePoint_eq, unitVector]
  have h2 : axialRot φ (planePoint p) 2 = p.2 := by
    simp [axialRot, TailBand.Internal.AngularPlane.planePoint_eq, unitVector]
  have hs : (Real.cos φ * p.1) ^ 2 + (Real.sin φ * p.1) ^ 2 = p.1 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [h0, h1, h2, hs, Real.sqrt_sq hp.1.le, abs_of_pos hp.2]

theorem labelGrad_off {B : ℝ → Space → (Space →L[ℝ] Space)} {cells : Set (ℝ × ℝ)}
    (hsupp : ∀ σ y, B σ y ≠ 0 → (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), |y 2|) ∈ cells) (m : ℕ) (ι : ℤ × ℤ)
    {p : ℝ × ℝ} (hp : p ∈ halfPlane) (hpc : p ∉ cells) : labelGrad m ι B p = 0 := by
  have hz : ∀ τ φ, B τ (axialRot φ (planePoint p)) = 0 := by
    intro τ φ
    by_contra hne
    apply hpc
    have h := hsupp τ _ hne
    rwa [rot_plane_coords p φ hp] at h
  have h0 : ∀ φ, axialRot φ (0 : Space) = 0 := by
    intro φ
    ext i
    fin_cases i <;> simp [axialRot]
  funext ab
  simp only [labelGrad, modeGrad, modeAverage, zero_add, hz, zero_apply, h0]
  simp

end Internal.PairHalf

open Coercive Bridge Bridge.Internal.PinHalf Internal.PairHalf in
theorem halfPlanePairing_of (hP : PairingModeIdentityHolds) (hH : HalfPlaneReductionHolds)
    (hL : LabelArithmeticHolds) (hX : ModeFlipHolds) : HalfPlanePairing := by
  intro m Γ P labels v G H g B cells hclass hv hBm hBp hBf hBflip hmode hsupp
  have hGp := hv.periodic_gradient
  have hGm := hv.measurable_gradient
  have hGf := hv.gradient_finite
  have hGF : FlipModes G := flipModes_of_perturbation hX hv hclass.flip
  have hBF : FlipModes B := flipModes_of_ae hBflip
  have step1 : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (B σ y)
      = ∑' ξ, ∫ y, pairDensity ξ G B 0 y := by
    rw [(hP G B hGm hBm hGp hBp hGf hBf).2]
    exact tsum_congr fun ξ => term_eq hGp hBp ξ
  have hm : ∀ ξ, AEStronglyMeasurable (fun y => pairDensity ξ G B 0 y) volume :=
    fun ξ => aesm_pairDensity_zero hGm hBm hGp hBp ξ
  have hSa := ae_goodSet hGp hBp (locallyIntegrable_of_squareSum hGm hGp hGf)
    (locallyIntegrable_of_squareSum hBm hBp hBf)
  have hfin : ∑' ξ, ∫⁻ y, ENNReal.ofReal |pairDensity ξ G B 0 y| < ⊤ := by
    have hle : ∀ ξ, ∫⁻ y, ENNReal.ofReal |pairDensity ξ G B 0 y| ≤
        (∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G 0 y))) + ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ B 0 y)) := by
      intro ξ
      rw [← lintegral_add_left' (aemeas_cnormSq_zero hGm hGp ξ)]
      refine lintegral_mono fun y => ?_
      rw [← ENNReal.ofReal_add (cnormSq_nonneg' _) (cnormSq_nonneg' _)]
      exact ENNReal.ofReal_le_ofReal (abs_pair_le _ _)
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
    rw [ENNReal.tsum_add]
    exact ENNReal.add_lt_top.2 ⟨modeNorm_tsum_lt_top hGm hGp hGf, modeNorm_tsum_lt_top hBm hBp hBf⟩
  have hhp : ∀ ξ, AEStronglyMeasurable (fun p : ℝ × ℝ => pairDensity ξ G B 0 (planePoint p))
      (volume.restrict halfPlane) :=
    fun ξ => (aesm_plane (hm ξ) (goodSet G B) (goodSet_rot G B) hSa (fun φ y hy => hy ξ φ)).restrict
  have step2 := signed_reduction hH (fun ξ y => pairDensity ξ G B 0 y) hm (goodSet G B) (goodSet_rot G B) hSa
    (fun ξ φ y hy => hy ξ φ) (fun ξ => ae_pairDensity_flip_modes hGp hBp hGF hBF ξ) hfin hhp
  beta_reduce at step2
  have hinj := (hL m hclass.order_pos).1
  have hzero : ∀ ξ ∉ labels.image (labelHarmonic m),
      ∫ p in halfPlane, pairDensity ξ G B 0 (planePoint p) * p.1 = 0 := by
    intro ξ hξ
    have hne : ∀ ι ∈ labels, labelHarmonic m ι ≠ ξ := fun ι hι h => hξ (Finset.mem_image.2 ⟨ι, hι, h⟩)
    refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_halfPlane).2 ?_)
    filter_upwards [hmode ξ hne] with p hp hmem
    simp [pairDensity, hp hmem, cdotMat]
  have step3 : ∑' ξ, ∫ p in halfPlane, pairDensity ξ G B 0 (planePoint p) * p.1 =
      ∑ ι ∈ labels, ∫ p in halfPlane, pairDensity (labelHarmonic m ι) G B 0 (planePoint p) * p.1 := by
    rw [tsum_eq_sum hzero, Finset.sum_image fun x _ y _ h => hinj h]
  have step4 : ∀ ι ∈ labels, ∫ p in halfPlane, pairDensity (labelHarmonic m ι) G B 0 (planePoint p) * p.1 =
      (∫ p in cells ∩ halfPlane, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p)).re := by
    intro ι _
    set f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p) with hf
    have hfc : ∀ p, f p = (p.1 : ℂ) * cdotMat (labelGrad m ι G p) (labelGrad m ι B p) := by
      intro p
      simp only [hf, cdotMat, CellCalculus.gradAt, Fintype.sum_prod_type]
    have hfre : ∀ p, (f p).re = pairDensity (labelHarmonic m ι) G B 0 (planePoint p) * p.1 := by
      intro p
      rw [hfc, Complex.re_ofReal_mul, mul_comm]
      rfl
    have hoff : ∀ p ∈ halfPlane \ (cells ∩ halfPlane), f p = 0 := by
      intro p hp
      have hpc : p ∉ cells := fun h => hp.2 ⟨h, hp.1⟩
      rw [hfc, labelGrad_off hsupp m ι hp.1 hpc]
      simp [cdotMat]
    have hGl : AEStronglyMeasurable (labelGrad m ι G) (volume.restrict halfPlane) :=
      (TailBand.aestronglyMeasurable_labelFields hv m ι).2.1
    have hBl : AEStronglyMeasurable (labelGrad m ι B) (volume.restrict halfPlane) := aesm_labelGrad hBm m ι
    have hfm : AEStronglyMeasurable f (volume.restrict halfPlane) := by
      have e : f = fun p => (p.1 : ℂ) * cdotMat (labelGrad m ι G p) (labelGrad m ι B p) := funext hfc
      rw [e]
      refine (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul ?_
      unfold cdotMat
      refine Finset.aestronglyMeasurable_fun_sum _ fun ij _ => ?_
      exact ((continuous_apply ij).comp_aestronglyMeasurable hGl).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable ((continuous_apply ij).comp_aestronglyMeasurable hBl))
    have hint : Integrable f (volume.restrict halfPlane) := by
      refine ⟨hfm, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hbd : ∀ᵐ p ∂(volume.restrict halfPlane), ‖f p‖ₑ ≤
          ENNReal.ofReal (cnormSq (labelGrad m ι G p)) * ENNReal.ofReal p.1
            + ENNReal.ofReal (cnormSq (labelGrad m ι B p)) * ENNReal.ofReal p.1 := by
        refine (ae_restrict_iff' measurableSet_halfPlane).2 (Filter.Eventually.of_forall fun p hp => ?_)
        have h1 := cnormSq_nonneg' (labelGrad m ι G p)
        have h2 := cnormSq_nonneg' (labelGrad m ι B p)
        have hpos : 0 ≤ p.1 := le_of_lt hp.1
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
          ← ENNReal.ofReal_add (mul_nonneg h1 hpos) (mul_nonneg h2 hpos), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hfc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
        have hc := norm_cdotMat_le (labelGrad m ι G p) (labelGrad m ι B p)
        nlinarith
      refine lt_of_le_of_lt (lintegral_mono_ae hbd) ?_
      have hmeasG : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (cnormSq (labelGrad m ι G p))
          * ENNReal.ofReal p.1) (volume.restrict halfPlane) :=
        ((aesm_cnormSq hGl).aemeasurable.ennreal_ofReal).mul
          continuous_fst.measurable.ennreal_ofReal.aemeasurable
      rw [lintegral_add_left' hmeasG]
      exact ENNReal.add_lt_top.2 ⟨halfPlane_modeNorm_lt_top hH hGm hGp hGf hGF _,
        halfPlane_modeNorm_lt_top hH hBm hBp hBf hBF _⟩
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_halfPlane Set.inter_subset_right hoff]
    have e := integral_re hint
    rw [show (∫ p in halfPlane, f p).re = RCLike.re (∫ p in halfPlane, f p) from rfl, ← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact (hfre p).symm
  rw [step1, step2, step3]
  congr 1
  exact Finset.sum_congr rfl step4

open Bridge in
theorem halfPlanePairing : HalfPlanePairing :=
  halfPlanePairing_of pairingModeIdentity halfPlaneReduction labelArithmetic modeFlip

end InstancePair

end CertCell

end Breakdown
