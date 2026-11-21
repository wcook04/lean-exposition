import Breakdown.CertCell.TailSquareDensity
import Breakdown.CertCell.TailSquareSmooth
import Breakdown.CertCell.TailFlipDecay
import Breakdown.Cert.CoerciveRotation

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace Internal.SquareTransfer

open CellCert.CellAnalysis.LowEntry.Internal (cylArg muU key muU_def cylArg_meas qmp)
open Internal.FlipDecay (cylArg_eq)
open Coercive (axialRotationHolds_proof)
open Coercive.RotationInternal (axialRotEquiv axialRot_apply_zero axialRot_apply_one axialRot_apply_two
  axialRot_norm)

def rotL (θ : ℝ) : Space →L[ℝ] Space := (axialRotEquiv θ).toLinearIsometry.toContinuousLinearMap

theorem rotL_apply (θ : ℝ) (y : Space) : rotL θ y = axialRot θ y := rfl

theorem rot_neg_rot (θ : ℝ) (y : Space) : axialRot (-θ) (axialRot θ y) = y := by
  rw [← axialRotationHolds_proof.2.1, neg_add_cancel, axialRotationHolds_proof.2.2.1]

theorem rot_rot_neg (θ : ℝ) (y : Space) : axialRot θ (axialRot (-θ) y) = y := by
  rw [← axialRotationHolds_proof.2.1, add_neg_cancel, axialRotationHolds_proof.2.2.1]

def planeL : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (unitVector 0) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (unitVector 2)

theorem planePoint_eq (p : ℝ × ℝ) : planePoint p = planeL p := by
  ext i
  fin_cases i <;> simp [planePoint, planeL, CellCert.CellAnalysis.cylPoint, unitVector]

theorem planePoint_zero (p : ℝ × ℝ) : planePoint p 0 = p.1 := by
  simp [planePoint, CellCert.CellAnalysis.cylPoint]

theorem planePoint_one (p : ℝ × ℝ) : planePoint p 1 = 0 := by
  simp [planePoint, CellCert.CellAnalysis.cylPoint]

theorem planePoint_two (p : ℝ × ℝ) : planePoint p 2 = p.2 := by
  simp [planePoint, CellCert.CellAnalysis.cylPoint]

theorem planeL_fst : planeL (1, 0) = unitVector 0 := by
  simp [planeL]

theorem planeL_snd : planeL (0, 1) = unitVector 2 := by
  simp [planeL]

theorem measurableSet_planeSquare (R : ℝ) : MeasurableSet (planeSquareExterior R) := by
  have e : planeSquareExterior R = (Ioi 0 ×ˢ Ioi 0) ∩ ({p : ℝ × ℝ | R < p.1} ∪ {p | R < p.2}) := rfl
  rw [e]
  exact (measurableSet_Ioi.prod measurableSet_Ioi).inter
    ((measurableSet_lt measurable_const measurable_fst).union
      (measurableSet_lt measurable_const measurable_snd))

theorem measurableSet_spaceSquare (R : ℝ) : MeasurableSet (spaceSquareExterior R) := by
  have hc : Continuous (fun y : Space => (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), y 2)) := by fun_prop
  exact (measurableSet_planeSquare R).preimage hc.measurable

theorem planeSquare_sub (R : ℝ) : planeSquareExterior R ⊆ Ioi 0 ×ˢ univ :=
  fun _ hp => ⟨hp.1.1, mem_univ _⟩

theorem mem_spaceSquare_rot (R θ : ℝ) (y : Space) :
    axialRot θ y ∈ spaceSquareExterior R ↔ y ∈ spaceSquareExterior R := by
  have h : axialRot θ y 0 ^ 2 + axialRot θ y 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [axialRot_apply_zero, axialRot_apply_one]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ
  simp only [spaceSquareExterior, mem_ofPred_eq, h, axialRot_apply_two]

theorem planePoint_mem (R : ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    planePoint p ∈ spaceSquareExterior R ↔ p ∈ planeSquareExterior R := by
  simp only [spaceSquareExterior, mem_ofPred_eq, planePoint_zero, planePoint_one, planePoint_two]
  rw [show p.1 ^ 2 + (0 : ℝ) ^ 2 = p.1 ^ 2 by ring, Real.sqrt_sq hp.le]

theorem lintegral_cyl_ae {F : Space → ℝ≥0∞} (hF : AEMeasurable F)
    (hinv : ∀ᵐ y, ∀ θ, F (axialRot θ y) = F y) :
    ∫⁻ y, F y = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ univ, ENNReal.ofReal p.1 * F (planePoint p) := by
  have hm : Measurable (hF.mk F) := hF.measurable_mk
  have h1 : ∀ᵐ q ∂muU, hF.mk F (cylArg q) = F (planePoint q.1) := by
    filter_upwards [qmp.ae hF.ae_eq_mk, qmp.ae hinv] with q h1 h2
    rw [← h1, ← h2 (-q.2), cylArg_eq, rot_neg_rot]
  rw [muU_def] at h1
  have hmeas : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal q.1.1 * hF.mk F (cylArg q)) :=
    (measurable_fst.fst.ennreal_ofReal).mul (hm.comp cylArg_meas)
  rw [lintegral_congr_ae hF.ae_eq_mk, ← key, muU_def, lintegral_prod _ hmeas.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with p hp
  have e : ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (p, θ).1.1 * hF.mk F (cylArg (p, θ)) =
      ∫⁻ _θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * F (planePoint p) :=
    lintegral_congr_ae (hp.mono fun θ hθ => by beta_reduce; rw [hθ])
  rw [e, setLIntegral_const, Real.volume_Ioo, mul_comm]
  congr 2
  ring

theorem pointPlane_rot (θ : ℝ) (y : Space) : pointPlane (axialRot θ y) = pointPlane y := by
  have h : axialRot θ y 0 ^ 2 + axialRot θ y 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [axialRot_apply_zero, axialRot_apply_one]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ
  simp only [pointPlane, h, axialRot_apply_two]

theorem pointPlane_planePoint {p : ℝ × ℝ} (hp : 0 ≤ p.1) : pointPlane (planePoint p) = p := by
  simp only [pointPlane, planePoint_zero, planePoint_one, planePoint_two]
  rw [show p.1 ^ 2 + (0 : ℝ) ^ 2 = p.1 ^ 2 by ring, Real.sqrt_sq hp]

theorem measurable_pointPlane : Measurable pointPlane := by
  unfold pointPlane
  fun_prop

theorem rot_pointAngle (y : Space) : axialRot (pointAngle y) (planePoint (pointPlane y)) = y := by
  have hn : ‖(y 0 : ℂ) + (y 1 : ℂ) * Complex.I‖ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) :=
    Complex.norm_add_mul_I _ _
  have hc := Complex.norm_mul_cos_arg ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)
  have hs := Complex.norm_mul_sin_arg ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)
  rw [hn] at hc hs
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im] at hc hs
  simp only [mul_one, mul_zero, add_zero, sub_zero, zero_add] at hc hs
  apply Coercive.RotationInternal.space_ext
  · rw [axialRot_apply_zero, planePoint_zero, planePoint_one]
    simp only [pointPlane, pointAngle]
    linear_combination hc
  · rw [axialRot_apply_one, planePoint_zero, planePoint_one]
    simp only [pointPlane, pointAngle]
    linear_combination hs
  · rw [axialRot_apply_two, planePoint_two]
    rfl

theorem ae_ne_line : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
  have e : {p : ℝ × ℝ | ¬p.1 ≠ 0} = {0} ×ˢ univ := by
    ext p
    simp
  rw [ae_iff, e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem ae_pointPlane {Q : ℝ × ℝ → Prop}
    (h : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ univ)), Q p) : ∀ᵐ y : Space, Q (pointPlane y) := by
  have h' : ∀ᵐ p : ℝ × ℝ, 0 ≤ p.1 → Q p := by
    filter_upwards [(ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).1 h, ae_ne_line]
      with p hp hp0 hle
    exact hp ⟨lt_of_le_of_ne hle hp0.symm, mem_univ _⟩
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h')
  have hN3m : MeasurableSet (pointPlane ⁻¹' N) := measurable_pointPlane hNm
  have hN3 : volume (pointPlane ⁻¹' N) = 0 := by
    rw [← lintegral_indicator_one hN3m, lintegral_cyl_ae (F := (pointPlane ⁻¹' N).indicator 1)
      (measurable_one.indicator hN3m).aemeasurable (ae_of_all _ fun y θ => by
        have e : axialRot θ y ∈ pointPlane ⁻¹' N ↔ y ∈ pointPlane ⁻¹' N := by
          rw [mem_preimage, mem_preimage, pointPlane_rot]
        by_cases hy : y ∈ pointPlane ⁻¹' N
        · rw [indicator_of_mem hy, indicator_of_mem (e.2 hy)]
          rfl
        · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (e.1 h))])]
    have e : ∫⁻ p in Ioi (0 : ℝ) ×ˢ univ, ENNReal.ofReal p.1 *
        (pointPlane ⁻¹' N).indicator 1 (planePoint p) = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN0),
        ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp hpA
      have hp1 : 0 ≤ p.1 := le_of_lt hpA.1
      rw [indicator_of_notMem (by rw [mem_preimage, pointPlane_planePoint hp1]; exact hp), mul_zero]
    rw [e, mul_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN3] with y hy
  by_contra hq
  exact hy (hsub fun hQ => hq (hQ (Real.sqrt_nonneg _)))

theorem ae_planePoint_of_ae {Q : Space → Prop} (hQ : ∀ᵐ y, Q y)
    (hinv : ∀ θ y, Q y → Q (axialRot θ y)) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ univ)), Q (planePoint p) := by
  have h := qmp.ae hQ
  rw [muU_def] at h
  have hne : (ae (volume.restrict (Ioo (-Real.pi) Real.pi))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Ioo]
    simp [Real.pi_pos]
  filter_upwards [Measure.ae_ae_of_ae_prod h] with p hp
  obtain ⟨θ, hθ⟩ := hp.exists
  have h2 := hinv (-θ) _ hθ
  rwa [cylArg_eq, rot_neg_rot] at h2

theorem lintegral_spaceSquare_ae {F : Space → ℝ≥0∞} (hF : AEMeasurable F)
    (hinv : ∀ᵐ y, ∀ θ, F (axialRot θ y) = F y) (R : ℝ) :
    ∫⁻ y in spaceSquareExterior R, F y =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ p in planeSquareExterior R, ENNReal.ofReal p.1 * F (planePoint p) := by
  have hS : MeasurableSet (spaceSquareExterior R) := measurableSet_spaceSquare R
  have hind : ∀ᵐ y, ∀ θ, (spaceSquareExterior R).indicator F (axialRot θ y) =
      (spaceSquareExterior R).indicator F y := by
    filter_upwards [hinv] with y hy θ
    by_cases h : y ∈ spaceSquareExterior R
    · rw [indicator_of_mem h, indicator_of_mem ((mem_spaceSquare_rot R θ y).mpr h), hy]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((mem_spaceSquare_rot R θ y).mp h'))]
  rw [← lintegral_indicator hS, lintegral_cyl_ae (hF.indicator hS) hind]
  congr 1
  have hP : ∫⁻ p in planeSquareExterior R, ENNReal.ofReal p.1 * F (planePoint p) =
      ∫⁻ p in Ioi 0 ×ˢ univ, (planeSquareExterior R).indicator
        (fun p => ENNReal.ofReal p.1 * F (planePoint p)) p := by
    rw [setLIntegral_indicator (measurableSet_planeSquare R), inter_eq_left.mpr (planeSquare_sub R)]
  rw [hP]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) ?_
  intro p hp
  have hp1 : 0 < p.1 := hp.1
  show ENNReal.ofReal p.1 * (spaceSquareExterior R).indicator F (planePoint p) = _
  by_cases hP : p ∈ planeSquareExterior R
  · rw [indicator_of_mem ((planePoint_mem R hp1).mpr hP), indicator_of_mem hP]
  · rw [indicator_of_notMem (fun h => hP ((planePoint_mem R hp1).mp h)), indicator_of_notMem hP, mul_zero]

theorem continuous_matSq_map : Continuous matSq :=
  continuous_finsetSum _ fun _ _ => ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem continuous_planeRadius : Continuous planeRadius := by
  unfold planeRadius
  fun_prop

theorem norm_sq_coord (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem matSq_three (A : Space →L[ℝ] Space) :
    matSq A = ‖A (unitVector 0)‖ ^ 2 + ‖A (unitVector 1)‖ ^ 2 + ‖A (unitVector 2)‖ ^ 2 := by
  simp [matSq, Fin.sum_univ_three]

theorem rot_neg_e0 (θ : ℝ) :
    axialRot (-θ) (unitVector 0) = Real.cos θ • unitVector 0 - Real.sin θ • unitVector 1 := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector]

theorem rot_neg_e1 (θ : ℝ) :
    axialRot (-θ) (unitVector 1) = Real.sin θ • unitVector 0 + Real.cos θ • unitVector 1 := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector]

theorem rot_neg_e2 (θ : ℝ) : axialRot (-θ) (unitVector 2) = unitVector 2 := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector]

theorem matSq_conj (θ : ℝ) (A : Space →L[ℝ] Space) :
    matSq ((rotL θ).comp (A.comp (rotL (-θ)))) = matSq A := by
  have hn : ∀ x, ‖rotL θ x‖ = ‖x‖ := fun x => (axialRotEquiv θ).norm_map x
  rw [matSq_three, matSq_three]
  simp only [ContinuousLinearMap.comp_apply, hn]
  simp only [rotL_apply, rot_neg_e0, rot_neg_e1, rot_neg_e2, map_sub, map_add, map_smul]
  set a := A (unitVector 0)
  set b := A (unitVector 1)
  simp only [norm_sq_coord, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) *
    Real.sin_sq_add_cos_sq θ

theorem fderiv_rot {w : Space → Space} (hw : Differentiable ℝ w)
    (hrot : ∀ ψ y, w (axialRot ψ y) = axialRot ψ (w y)) (θ : ℝ) (y : Space) :
    fderiv ℝ w (axialRot θ y) = (rotL θ).comp ((fderiv ℝ w y).comp (rotL (-θ))) := by
  have e : w = fun z => rotL θ (w (rotL (-θ) z)) := by
    funext z
    rw [rotL_apply, rotL_apply, ← hrot, rot_rot_neg]
  have h : HasFDerivAt (fun z => rotL θ (w (rotL (-θ) z)))
      ((rotL θ).comp ((fderiv ℝ w (rotL (-θ) (axialRot θ y))).comp (rotL (-θ)))) (axialRot θ y) :=
    (rotL θ).hasFDerivAt.comp _ ((hw _).hasFDerivAt.comp _ (rotL (-θ)).hasFDerivAt)
  rw [← e, rotL_apply, rot_neg_rot] at h
  exact h.fderiv

theorem hasDerivAt_rot (y : Space) :
    HasDerivAt (fun ψ => axialRot ψ y) ((-y 1) • unitVector 0 + y 0 • unitVector 1) 0 := by
  have h0 := ((Real.hasDerivAt_cos 0).mul_const (y 0)).sub ((Real.hasDerivAt_sin 0).mul_const (y 1))
  have h1 := ((Real.hasDerivAt_sin 0).mul_const (y 0)).add ((Real.hasDerivAt_cos 0).mul_const (y 1))
  have h := ((h0.smul_const (unitVector 0)).add (h1.smul_const (unitVector 1))).add_const
    (y 2 • unitVector 2)
  have hd : (-Real.sin 0 * y 0 - Real.cos 0 * y 1) • unitVector 0 +
      (Real.cos 0 * y 0 + -Real.sin 0 * y 1) • unitVector 1 = (-y 1) • unitVector 0 + y 0 • unitVector 1 := by
    simp
  rw [hd] at h
  exact h

theorem fderiv_perp {w : Space → Space} (hw : Differentiable ℝ w)
    (hrot : ∀ ψ y, w (axialRot ψ y) = axialRot ψ (w y)) (y : Space) :
    fderiv ℝ w y ((-y 1) • unitVector 0 + y 0 • unitVector 1) =
      (-w y 1) • unitVector 0 + w y 0 • unitVector 1 := by
  have h1 : HasDerivAt (fun ψ => w (axialRot ψ y))
      (fderiv ℝ w y ((-y 1) • unitVector 0 + y 0 • unitVector 1)) 0 := by
    have h := (hw (axialRot 0 y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rot y)
    rw [axialRotationHolds_proof.2.2.1] at h
    exact h
  have e : (fun ψ => w (axialRot ψ y)) = fun ψ => axialRot ψ (w y) := funext fun ψ => hrot ψ y
  rw [e] at h1
  exact h1.unique (hasDerivAt_rot (w y))

theorem col_one {w : Space → Space} (hw : Differentiable ℝ w)
    (hrot : ∀ ψ y, w (axialRot ψ y) = axialRot ψ (w y)) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ‖fderiv ℝ w (planePoint p) (unitVector 1)‖ ^ 2 =
      (w (planePoint p) 0 ^ 2 + w (planePoint p) 1 ^ 2) / p.1 ^ 2 := by
  have h := fderiv_perp hw hrot (planePoint p)
  rw [planePoint_one, planePoint_zero, neg_zero, zero_smul, zero_add, map_smul] at h
  have h' : fderiv ℝ w (planePoint p) (unitVector 1) =
      p.1⁻¹ • ((-w (planePoint p) 1) • unitVector 0 + w (planePoint p) 0 • unitVector 1) := by
    rw [← h, smul_smul, inv_mul_cancel₀ hp, one_smul]
  rw [h', norm_sq_coord]
  simp [unitVector]
  field_simp
  ring

theorem plane_comp (w : Space → Space) (a : Fin 3) :
    (fun x => w (planePoint x) a) = fun x => EuclideanSpace.proj a (w (planeL x)) := by
  funext x
  rw [planePoint_eq]
  rfl

theorem fderiv_plane {w : Space → Space} (hw : Differentiable ℝ w) (a : Fin 3) (p q : ℝ × ℝ) :
    fderiv ℝ (fun x => w (planePoint x) a) p q = fderiv ℝ w (planePoint p) (planeL q) a := by
  have h := (EuclideanSpace.proj a : Space →L[ℝ] ℝ).hasFDerivAt.comp p
    ((hw (planeL p)).hasFDerivAt.comp p planeL.hasFDerivAt)
  rw [plane_comp, show (fun x => (EuclideanSpace.proj a : Space →L[ℝ] ℝ) (w (planeL x))) =
    ⇑(EuclideanSpace.proj a : Space →L[ℝ] ℝ) ∘ w ∘ ⇑planeL from rfl, h.fderiv, planePoint_eq]
  rfl

theorem contDiff_plane {w : Space → Space} (hw : ContDiff ℝ 1 w) (a : Fin 3) :
    ContDiff ℝ 1 (fun x => w (planePoint x) a) := by
  rw [plane_comp]
  exact (EuclideanSpace.proj a).contDiff.comp (hw.comp planeL.contDiff)

theorem compact_plane {w : Space → Space} (hw : HasCompactSupport w) (a : Fin 3) :
    HasCompactSupport (fun x => w (planePoint x) a) := by
  have hK : IsCompact ((fun y : Space => (y 0, y 2)) '' tsupport w) :=
    IsCompact.image hw (by fun_prop)
  refine HasCompactSupport.intro hK ?_
  intro x hx
  have h : planePoint x ∉ tsupport w := fun h =>
    hx ⟨planePoint x, h, by show (planePoint x 0, planePoint x 2) = x; rw [planePoint_zero, planePoint_two]⟩
  simp [image_eq_zero_of_notMem_tsupport h]

theorem flipPoint_two (v : Space) : flipPoint v 2 = -v 2 := by
  simp [flipPoint, unitVector]

theorem axial_zero {w : Space → Space} (hflip : ∀ y, w (flipPoint y) = flipPoint (w y)) (x : ℝ) :
    (fun q => w (planePoint q) 2) (x, 0) = 0 := by
  have hy : flipPoint (planePoint (x, 0)) = planePoint (x, 0) := by
    ext i
    fin_cases i <;> simp [flipPoint, planePoint, CellCert.CellAnalysis.cylPoint, unitVector]
  have h := congrArg (fun v : Space => v 2) (hflip (planePoint (x, 0)))
  simp only [hy, flipPoint_two] at h
  show w (planePoint (x, 0)) 2 = 0
  linarith

theorem rot_pi_axis (z : ℝ) : axialRot Real.pi (planePoint (0, z)) = planePoint (0, z) := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector]

theorem trans_zero {w : Space → Space} (hrot : ∀ ψ y, w (axialRot ψ y) = axialRot ψ (w y))
    (z : ℝ) : w (planePoint (0, z)) 0 = 0 ∧ w (planePoint (0, z)) 1 = 0 := by
  have h := hrot Real.pi (planePoint (0, z))
  rw [rot_pi_axis] at h
  have h0 := congrArg (fun v : Space => v 0) h
  have h1 := congrArg (fun v : Space => v 1) h
  simp only [axialRot_apply_zero, axialRot_apply_one, Real.cos_pi, Real.sin_pi] at h0 h1
  constructor <;> linarith

theorem measurable_square_term {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (f p ^ 2 / planeRadius p ^ 2 * p.1)) :=
  (((hf.measurable.pow_const 2).div (continuous_planeRadius.measurable.pow_const 2)).mul
    measurable_fst).ennreal_ofReal

theorem three_le {c a0 a1 a2 b0 b1 b2 : ℝ≥0∞} (h0 : ENNReal.ofReal 2 * a0 ≤ b0)
    (h1 : ENNReal.ofReal 2 * a1 ≤ b1) (h2 : ENNReal.ofReal 2 * a2 ≤ b2) :
    ENNReal.ofReal 2 * (c * (a0 + a1 + a2)) ≤ c * (b0 + b1 + b2) := by
  calc ENNReal.ofReal 2 * (c * (a0 + a1 + a2))
      = c * (ENNReal.ofReal 2 * a0 + ENNReal.ofReal 2 * a1 + ENNReal.ofReal 2 * a2) := by ring
    _ ≤ c * (b0 + b1 + b2) := by gcongr

end Internal.SquareTransfer

open Internal.SquareTransfer in
theorem squareExteriorSpaceSmooth_of (h : SquareExteriorSmoothStatement) :
    SquareExteriorSpaceSmoothStatement := by
  intro R hR w hw hc hf
  obtain ⟨hrot, hflip⟩ := hf
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hA := h.1 R hR _ (contDiff_plane hw 2) (compact_plane hc 2) (axial_zero hflip)
  have hT0 := h.2 R hR _ (contDiff_plane hw 0) (compact_plane hc 0) fun z => (trans_zero hrot z).1
  have hT1 := h.2 R hR _ (contDiff_plane hw 1) (compact_plane hc 1) fun z => (trans_zero hrot z).2
  simp only [fderiv_plane hd, planeL_fst, planeL_snd] at hA hT0 hT1
  have hF1m : Measurable (fun y => ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)) :=
    ((hw.continuous.measurable.norm.pow_const 2).div (measurable_norm.pow_const 2)).ennreal_ofReal
  have hF1r : ∀ θ y, ENNReal.ofReal (‖w (axialRot θ y)‖ ^ 2 / ‖axialRot θ y‖ ^ 2) =
      ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2) := by
    intro θ y
    rw [hrot, Coercive.RotationInternal.axialRot_norm, Coercive.RotationInternal.axialRot_norm]
  have hF2m : Measurable (fun y => ENNReal.ofReal (matSq (fderiv ℝ w y))) :=
    (continuous_matSq_map.measurable.comp (measurable_fderiv ℝ w)).ennreal_ofReal
  have hF2r : ∀ θ y, ENNReal.ofReal (matSq (fderiv ℝ w (axialRot θ y))) =
      ENNReal.ofReal (matSq (fderiv ℝ w y)) := by
    intro θ y
    rw [fderiv_rot hd hrot, matSq_conj]
  rw [lintegral_spaceSquare_ae hF1m.aemeasurable (ae_of_all _ fun y θ => hF1r θ y),
    lintegral_spaceSquare_ae hF2m.aemeasurable (ae_of_all _ fun y θ => hF2r θ y)]
  have hcont : ∀ a : Fin 3, Continuous (fun p : ℝ × ℝ => w (planePoint p) a) :=
    fun a => (contDiff_plane hw a).continuous
  have hpp : Continuous planePoint := by
    rw [show planePoint = planeL from funext planePoint_eq]
    exact planeL.continuous
  have hdc : ∀ (a : Fin 3) (v : Space),
      Continuous (fun p : ℝ × ℝ => fderiv ℝ w (planePoint p) v a) := fun a v =>
    (EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp
      (((hw.continuous_fderiv (by norm_num)).comp hpp).clm_apply continuous_const)
  have eL : ∫⁻ p in planeSquareExterior R,
      ENNReal.ofReal p.1 * ENNReal.ofReal (‖w (planePoint p)‖ ^ 2 / ‖planePoint p‖ ^ 2) =
      (∫⁻ p in planeSquareExterior R, ENNReal.ofReal (w (planePoint p) 0 ^ 2 / planeRadius p ^ 2 * p.1)) +
      (∫⁻ p in planeSquareExterior R, ENNReal.ofReal (w (planePoint p) 1 ^ 2 / planeRadius p ^ 2 * p.1)) +
      ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (w (planePoint p) 2 ^ 2 / planeRadius p ^ 2 * p.1) := by
    rw [← lintegral_add_left (measurable_square_term (hcont 0)),
      ← lintegral_add_right _ (measurable_square_term (hcont 2))]
    refine setLIntegral_congr_fun (measurableSet_planeSquare R) ?_
    intro p hp
    have hp1 : 0 < p.1 := hp.1.1
    have hρ : planeRadius p ^ 2 = p.1 ^ 2 + p.2 ^ 2 := Real.sq_sqrt (by positivity)
    have hn : ‖planePoint p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [norm_sq_coord, planePoint_zero, planePoint_one, planePoint_two]
      ring
    have t : ∀ a : Fin 3, 0 ≤ w (planePoint p) a ^ 2 / planeRadius p ^ 2 * p.1 := fun a =>
      mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) hp1.le
    beta_reduce
    rw [← ENNReal.ofReal_mul hp1.le, ← ENNReal.ofReal_add (t 0) (t 1),
      ← ENNReal.ofReal_add (add_nonneg (t 0) (t 1)) (t 2), norm_sq_coord (w _), hn, hρ]
    congr 1
    ring
  have hJ : ∀ a : Fin 3, Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ w (planePoint p) (unitVector 0) a ^ 2 + fderiv ℝ w (planePoint p) (unitVector 2) a ^ 2
        + w (planePoint p) a ^ 2 / p.1 ^ 2) * p.1)) := fun a =>
    (((((hdc a _).measurable.pow_const 2).add ((hdc a _).measurable.pow_const 2)).add
      (((hcont a).measurable.pow_const 2).div (measurable_fst.pow_const 2))).mul
        measurable_fst).ennreal_ofReal
  have eR : ∫⁻ p in planeSquareExterior R,
      ENNReal.ofReal p.1 * ENNReal.ofReal (matSq (fderiv ℝ w (planePoint p))) =
      (∫⁻ p in planeSquareExterior R, ENNReal.ofReal
        ((fderiv ℝ w (planePoint p) (unitVector 0) 0 ^ 2 + fderiv ℝ w (planePoint p) (unitVector 2) 0 ^ 2
          + w (planePoint p) 0 ^ 2 / p.1 ^ 2) * p.1)) +
      (∫⁻ p in planeSquareExterior R, ENNReal.ofReal
        ((fderiv ℝ w (planePoint p) (unitVector 0) 1 ^ 2 + fderiv ℝ w (planePoint p) (unitVector 2) 1 ^ 2
          + w (planePoint p) 1 ^ 2 / p.1 ^ 2) * p.1)) +
      ∫⁻ p in planeSquareExterior R, ENNReal.ofReal
        ((fderiv ℝ w (planePoint p) (unitVector 0) 2 ^ 2 + fderiv ℝ w (planePoint p) (unitVector 2) 2 ^ 2)
          * p.1) := by
    have hJ2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
        ((fderiv ℝ w (planePoint p) (unitVector 0) 2 ^ 2 + fderiv ℝ w (planePoint p) (unitVector 2) 2 ^ 2)
          * p.1)) :=
      ((((hdc 2 _).measurable.pow_const 2).add ((hdc 2 _).measurable.pow_const 2)).mul
        measurable_fst).ennreal_ofReal
    rw [← lintegral_add_left (hJ 0), ← lintegral_add_right _ hJ2]
    refine setLIntegral_congr_fun (measurableSet_planeSquare R) ?_
    intro p hp
    have hp1 : 0 < p.1 := hp.1.1
    have t : ∀ a : Fin 3, 0 ≤ (fderiv ℝ w (planePoint p) (unitVector 0) a ^ 2
        + fderiv ℝ w (planePoint p) (unitVector 2) a ^ 2 + w (planePoint p) a ^ 2 / p.1 ^ 2) * p.1 :=
      fun a => mul_nonneg (by positivity) hp1.le
    have t2 : 0 ≤ (fderiv ℝ w (planePoint p) (unitVector 0) 2 ^ 2
        + fderiv ℝ w (planePoint p) (unitVector 2) 2 ^ 2) * p.1 := mul_nonneg (by positivity) hp1.le
    beta_reduce
    rw [← ENNReal.ofReal_mul hp1.le, ← ENNReal.ofReal_add (t 0) (t 1),
      ← ENNReal.ofReal_add (add_nonneg (t 0) (t 1)) t2, matSq_three, col_one hd hrot hp1.ne',
      norm_sq_coord, norm_sq_coord]
    congr 1
    field_simp
    ring
  rw [eL, eR]
  exact three_le hT0 hT1 hA

end TailBand

end CertCell

end Breakdown
