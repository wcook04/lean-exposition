import Breakdown.CertCell.AssemblyPotentialStage

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal

theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := mul_self_le_mul_self (norm_nonneg (a - b)) (norm_sub_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem curlOfGrad_apply (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad g 0 = g (2, 1) - g (1, 2) ∧ curlOfGrad g 1 = g (0, 2) - g (2, 0) ∧
      curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [curlOfGrad, alternatingSymbol, Fin.sum_univ_three] <;> ring

theorem curlComp_apply (s : Fin 3 → Fin 3 → ℂ) :
    curlComp s 0 = s 2 1 - s 1 2 ∧ curlComp s 1 = s 0 2 - s 2 0 ∧ curlComp s 2 = s 1 0 - s 0 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp (config := {decide := true}) [curlComp, CellCert.permSign, Fin.sum_univ_three] <;> ring

theorem cnormSq_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  obtain ⟨h0, h1, h2⟩ := curlOfGrad_apply g
  unfold cnormSq
  rw [Fin.sum_univ_three, h0, h1, h2, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  have e1 := norm_sub_sq_le (g (2, 1)) (g (1, 2))
  have e2 := norm_sub_sq_le (g (0, 2)) (g (2, 0))
  have e3 := norm_sub_sq_le (g (1, 0)) (g (0, 1))
  nlinarith [sq_nonneg ‖g (0, 0)‖, sq_nonneg ‖g (1, 1)‖, sq_nonneg ‖g (2, 2)‖]

theorem curlSq_le_two (s : Fin 3 → Fin 3 → ℂ) : curlSq s ≤ 2 * sumSq s := by
  obtain ⟨h0, h1, h2⟩ := curlComp_apply s
  unfold curlSq sumSq
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [Fin.sum_univ_three]
  have e1 := norm_sub_sq_le (s 2 1) (s 1 2)
  have e2 := norm_sub_sq_le (s 0 2) (s 2 0)
  have e3 := norm_sub_sq_le (s 1 0) (s 0 1)
  nlinarith [sq_nonneg ‖s 0 0‖, sq_nonneg ‖s 1 1‖, sq_nonneg ‖s 2 2‖]

theorem pairVec_sq (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    ∑ j, ‖pairVec s v j‖ ^ 2 = sumSq s + vecSq v := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pairVec, sumSq, vecSq]
  norm_num
  simp only [show ∀ h : 2 < 3, (⟨2, h⟩ : Fin 3) = 2 from fun _ => rfl]
  ring

theorem inv_abs_le {c x : ℝ} (h1 : c⁻¹ ≤ x) (h2 : x ≤ c) : |x⁻¹| ≤ |c| + |c⁻¹| := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hx : x < 0 := lt_of_le_of_lt h2 hc
    have : |x⁻¹| ≤ |c⁻¹| := by
      rw [abs_inv, abs_inv, abs_of_neg hx, abs_of_neg hc]
      exact inv_anti₀ (by linarith) (by linarith)
    linarith [abs_nonneg c]
  · subst hc
    simp only [_root_.inv_zero] at h1
    have : x = 0 := le_antisymm h2 h1
    simp [this]
  · have hci : 0 < c⁻¹ := inv_pos.2 hc
    have hx : 0 < x := lt_of_lt_of_le hci h1
    have : |x⁻¹| ≤ |c| := by
      rw [abs_of_pos (inv_pos.2 hx), abs_of_pos hc]
      calc x⁻¹ ≤ (c⁻¹)⁻¹ := inv_anti₀ hci h1
        _ = c := inv_inv c
    linarith [abs_nonneg c⁻¹]

theorem abs_le_of_between {c x : ℝ} (h1 : c⁻¹ ≤ x) (h2 : x ≤ c) : |x| ≤ |c| + |c⁻¹| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le c⁻¹, abs_nonneg c]
  · linarith [le_abs_self c, abs_nonneg c⁻¹]

theorem abs_mul_term {a y A L S : ℝ} (ha : |a| ≤ A) (hy : |y| ≤ L * S) : |a * y| ≤ A * (L * S) := by
  rw [abs_mul]
  exact mul_le_mul ha hy (abs_nonneg y) ((abs_nonneg a).trans ha)

end Internal

namespace Internal

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def profileSq (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ j, ‖bandProfile D ι v G p j‖ ^ 2

theorem profileSq_eq (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    profileSq D ι v G p = sumSq (gradArray D.azimuthOrder ι G p) + vecSq (velArray D.azimuthOrder ι v p) :=
  pairVec_sq _ _

theorem sumSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s := by
  unfold sumSq
  positivity

theorem vecSq_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecSq v := by
  unfold vecSq
  positivity

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x := by
  unfold cnormSq
  positivity

theorem cnormSq_labelGrad (m : ℕ) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    cnormSq (labelGrad m ι G p) = sumSq (gradArray m ι G p) := by
  unfold cnormSq sumSq
  rw [Fintype.sum_prod_type]
  rfl

theorem cnormSq_labelVel (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (p : ℝ × ℝ) :
    cnormSq (labelVel m ι v p) = vecSq (velArray m ι v p) := rfl

theorem gradAt_eq_profile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (a b : Fin 3) (p : ℝ × ℝ) :
    gradAt D.azimuthOrder ι G a b p = gradOf (bandProfile D ι v G p) (a, b) := by
  unfold bandProfile
  rw [gradOf_pairVec]
  rfl

theorem velAt_eq_profile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (a : Fin 3) (p : ℝ × ℝ) :
    velAt D.azimuthOrder ι v a p = velOf (bandProfile D ι v G p) a := by
  unfold bandProfile
  rw [velOf_pairVec]
  rfl

def chargeDiff (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  (D.charges (some K)).curl ι p * Real.sqrt (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p))) ^ 2
    + (R.entryCharges K ι).stretchConst * (D.charges (some K)).gradient ι p * (D.charges (some K)).length ι p / 2
      * Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p)) ^ 2
    + (R.entryCharges K ι).stretchConst * (D.charges (some K)).gradient ι p * ((D.charges (some K)).length ι p)⁻¹ / 2
      * Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p)) ^ 2
    + (R.entryCharges K ι).stretchConst * (D.charges (some K)).product ι p
      * (Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p)) * Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p)))
    + (R.entryCharges K ι).curlCharge p
      * (Real.sqrt (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p))) ^ 2 - modeCurlSq D ι G p)
    + (R.entryCharges K ι).gradCharge p * (Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p)) ^ 2 - modeStrainSq D ι G p)
    + (R.entryCharges K ι).velCharge p * (Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p)) ^ 2 - modeVelSq D ι v p)

theorem chargeDiff_eq (K : Fin D.mesh.count) (q : Fin k → ℝ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    D.labelDensity q v G H ι p
        - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (R.entryCharges K ι) D.azimuthOrder ι v G H p
        - extraChargeDensity D R K ι v G p
      = chargeDiff D R K ι v G p := by
  simp only [CellLayerData.labelDensity, TailBand.modeTerm_eq_labelQuad, TailBand.offModeDensity, TailBand.labelQuad,
    TailBand.PointCoef.quad, TailBand.PointCoef.withStretch, extraChargeDensity, chargeDiff]
  ring

end Internal

namespace Internal

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def curlPart (U : Fin 12 → ℂ) : ℝ := Real.sqrt (cnormSq (curlOfGrad (gradOf U))) ^ 2

def gradPart (U : Fin 12 → ℂ) : ℝ := Real.sqrt (cnormSq (gradOf U)) ^ 2

def velPart (U : Fin 12 → ℂ) : ℝ := Real.sqrt (cnormSq (velOf U)) ^ 2

def crossPart (U : Fin 12 → ℂ) : ℝ := Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))

theorem continuous_curlPart : Continuous curlPart := by
  unfold curlPart cnormSq curlOfGrad gradOf
  fun_prop

theorem continuous_gradPart : Continuous gradPart := by
  unfold gradPart cnormSq gradOf
  fun_prop

theorem continuous_velPart : Continuous velPart := by
  unfold velPart cnormSq velOf
  fun_prop

theorem continuous_crossPart : Continuous crossPart := by
  unfold crossPart cnormSq gradOf velOf
  fun_prop

theorem continuous_curlSqPart : Continuous (fun U : Fin 12 → ℂ => curlSq (strainOfVec U)) := by
  unfold curlSq curlComp strainOfVec gradOf
  fun_prop

theorem continuous_sumSqPart : Continuous (fun U : Fin 12 → ℂ => sumSq (strainOfVec U)) := by
  unfold sumSq strainOfVec gradOf
  fun_prop

theorem continuous_vecSqPart : Continuous (fun U : Fin 12 → ℂ => vecSq (velOf U)) := by
  unfold vecSq velOf
  fun_prop

theorem labelGrad_eq_profile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ) : labelGrad D.azimuthOrder ι G p = gradOf (bandProfile D ι v G p) := by
  unfold bandProfile
  rw [gradOf_pairVec]
  rfl

theorem labelVel_eq_profile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ) : labelVel D.azimuthOrder ι v p = velOf (bandProfile D ι v G p) := by
  unfold bandProfile
  rw [velOf_pairVec]
  rfl

theorem gradArray_eq_profile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ) : gradArray D.azimuthOrder ι G p = strainOfVec (bandProfile D ι v G p) := by
  unfold bandProfile
  rw [strainOfVec_pairVec]

theorem velArray_eq_profile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ) : velArray D.azimuthOrder ι v p = velOf (bandProfile D ι v G p) := by
  unfold bandProfile
  rw [velOf_pairVec]

theorem chargeDiff_profile (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    chargeDiff D R K ι v G p
      = (D.charges (some K)).curl ι p * curlPart (bandProfile D ι v G p)
        + (R.entryCharges K ι).stretchConst * (D.charges (some K)).gradient ι p * (D.charges (some K)).length ι p / 2
          * gradPart (bandProfile D ι v G p)
        + (R.entryCharges K ι).stretchConst * (D.charges (some K)).gradient ι p * ((D.charges (some K)).length ι p)⁻¹ / 2
          * velPart (bandProfile D ι v G p)
        + (R.entryCharges K ι).stretchConst * (D.charges (some K)).product ι p * crossPart (bandProfile D ι v G p)
        + (R.entryCharges K ι).curlCharge p
          * (curlPart (bandProfile D ι v G p) - curlSq (strainOfVec (bandProfile D ι v G p)))
        + (R.entryCharges K ι).gradCharge p
          * (gradPart (bandProfile D ι v G p) - sumSq (strainOfVec (bandProfile D ι v G p)))
        + (R.entryCharges K ι).velCharge p
          * (velPart (bandProfile D ι v G p) - vecSq (velOf (bandProfile D ι v G p))) := by
  have e5 : modeCurlSq D ι G p = curlSq (strainOfVec (bandProfile D ι v G p)) := by
    rw [← gradArray_eq_profile D ι v G p]
    rfl
  have e6 : modeStrainSq D ι G p = sumSq (strainOfVec (bandProfile D ι v G p)) := by
    rw [← gradArray_eq_profile D ι v G p]
    rfl
  have e7 : modeVelSq D ι v p = vecSq (velOf (bandProfile D ι v G p)) := by
    rw [← velArray_eq_profile D ι v G p]
    rfl
  unfold chargeDiff curlPart gradPart velPart crossPart
  rw [labelGrad_eq_profile D ι v G p, labelVel_eq_profile D ι v G p, e5, e6, e7]

theorem extraCharge_profile (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    extraChargeDensity D R K ι v G p
      = (R.entryCharges K ι).curlCharge p * curlSq (strainOfVec (bandProfile D ι v G p))
        + (R.entryCharges K ι).gradCharge p * sumSq (strainOfVec (bandProfile D ι v G p))
        + (R.entryCharges K ι).velCharge p * vecSq (velOf (bandProfile D ι v G p)) := by
  unfold extraChargeDensity
  rw [← gradArray_eq_profile D ι v G p, ← velArray_eq_profile D ι v G p]
  rfl

theorem profile_aemeasurable {μ : Measure (ℝ × ℝ)} (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (h : ∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) μ)
    (Φ : (Fin 12 → ℂ) → ℝ) (hΦ : Continuous Φ) : AEMeasurable (fun p => Φ (bandProfile D ι v G p)) μ :=
  hΦ.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 (fun j => (h j).aemeasurable))

theorem chargeDiff_aemeasurable (hE : EntryChargesRegular D R) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (h : ∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect)) :
    AEStronglyMeasurable (fun p => chargeDiff D R K ι v G p * p.1) (volume.restrict (D.mesh.box K).rect) := by
  obtain ⟨hcc, hgc, hvc, hmc, hmp, hmg, hml⟩ := hE.measurable K ι
  have a1 := profile_aemeasurable D ι v G h _ continuous_curlPart
  have a2 := profile_aemeasurable D ι v G h _ continuous_gradPart
  have a3 := profile_aemeasurable D ι v G h _ continuous_velPart
  have a4 := profile_aemeasurable D ι v G h _ continuous_crossPart
  have a5 := profile_aemeasurable D ι v G h _ continuous_curlSqPart
  have a6 := profile_aemeasurable D ι v G h _ continuous_sumSqPart
  have a7 := profile_aemeasurable D ι v G h _ continuous_vecSqPart
  have hcc' := hcc.aemeasurable
  have hgc' := hgc.aemeasurable
  have hvc' := hvc.aemeasurable
  have hmc' := hmc.aemeasurable
  have hmp' := hmp.aemeasurable
  have hmg' := hmg.aemeasurable
  have hml' := hml.aemeasurable
  have hmli : AEMeasurable (fun p => ((D.charges (some K)).length ι p)⁻¹) (volume.restrict (D.mesh.box K).rect) :=
    hml'.inv
  simp only [chargeDiff_profile]
  refine AEMeasurable.aestronglyMeasurable ?_
  fun_prop

theorem extraCharge_aemeasurable (hE : EntryChargesRegular D R) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (h : ∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect)) :
    AEStronglyMeasurable (fun p => extraChargeDensity D R K ι v G p * p.1) (volume.restrict (D.mesh.box K).rect) := by
  obtain ⟨hcc, hgc, hvc, -, -, -, -⟩ := hE.measurable K ι
  have a5 := profile_aemeasurable D ι v G h _ continuous_curlSqPart
  have a6 := profile_aemeasurable D ι v G h _ continuous_sumSqPart
  have a7 := profile_aemeasurable D ι v G h _ continuous_vecSqPart
  have hcc' := hcc.aemeasurable
  have hgc' := hgc.aemeasurable
  have hvc' := hvc.aemeasurable
  simp only [extraCharge_profile]
  refine AEMeasurable.aestronglyMeasurable ?_
  fun_prop

end Internal

namespace Internal

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem part_bounds (U : Fin 12 → ℂ) :
    0 ≤ curlPart U ∧ curlPart U ≤ 2 * ∑ j, ‖U j‖ ^ 2 ∧ 0 ≤ gradPart U ∧ gradPart U ≤ ∑ j, ‖U j‖ ^ 2 ∧
    0 ≤ velPart U ∧ velPart U ≤ ∑ j, ‖U j‖ ^ 2 ∧ 0 ≤ crossPart U ∧ crossPart U ≤ ∑ j, ‖U j‖ ^ 2 ∧
    0 ≤ curlSq (strainOfVec U) ∧ curlSq (strainOfVec U) ≤ 2 * ∑ j, ‖U j‖ ^ 2 ∧
    0 ≤ sumSq (strainOfVec U) ∧ sumSq (strainOfVec U) ≤ ∑ j, ‖U j‖ ^ 2 ∧
    0 ≤ vecSq (velOf U) ∧ vecSq (velOf U) ≤ ∑ j, ‖U j‖ ^ 2 := by
  have hU : U = pairVec (strainOfVec U) (velOf U) := by
    funext j
    fin_cases j <;> rfl
  have hsum : ∑ j, ‖U j‖ ^ 2 = sumSq (strainOfVec U) + vecSq (velOf U) := by
    conv_lhs => rw [hU]
    exact pairVec_sq _ _
  have hg : cnormSq (gradOf U) = sumSq (strainOfVec U) := by
    unfold cnormSq sumSq
    rw [Fintype.sum_prod_type]
    rfl
  have hv : cnormSq (velOf U) = vecSq (velOf U) := rfl
  have hs0 := sumSq_nonneg (strainOfVec U)
  have hv0 := vecSq_nonneg (velOf U)
  have hgn := cnormSq_nonneg' (gradOf U)
  have hvn := cnormSq_nonneg' (velOf U)
  have hc0 := cnormSq_nonneg' (curlOfGrad (gradOf U))
  have hcl := cnormSq_curlOfGrad_le (gradOf U)
  have hcs := curlSq_le_two (strainOfVec U)
  have hcs0 : 0 ≤ curlSq (strainOfVec U) := by
    unfold curlSq
    positivity
  have hcp : curlPart U = cnormSq (curlOfGrad (gradOf U)) := Real.sq_sqrt hc0
  have hgp : gradPart U = sumSq (strainOfVec U) := by rw [gradPart, Real.sq_sqrt hgn, hg]
  have hvp : velPart U = vecSq (velOf U) := by rw [velPart, Real.sq_sqrt hvn, hv]
  have hxp : crossPart U ≤ ∑ j, ‖U j‖ ^ 2 := by
    unfold crossPart
    have h1 := Real.sq_sqrt hgn
    have h2 := Real.sq_sqrt hvn
    nlinarith [sq_nonneg (Real.sqrt (cnormSq (gradOf U)) - Real.sqrt (cnormSq (velOf U))),
      Real.sqrt_nonneg (cnormSq (gradOf U)), Real.sqrt_nonneg (cnormSq (velOf U))]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcs0, ?_, hs0, ?_, hv0, ?_⟩
  · rw [hcp]; exact hc0
  · rw [hcp, hsum]; rw [hg] at hcl; linarith
  · rw [hgp]; exact hs0
  · rw [hgp, hsum]; linarith
  · rw [hvp]; exact hv0
  · rw [hvp, hsum]; linarith
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact hxp
  · rw [hsum]; linarith
  · rw [hsum]; linarith
  · rw [hsum]; linarith

theorem coef_bound3 {x y z B : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) (hz : |z| ≤ B) : |x * y * z / 2| ≤ B ^ 3 := by
  have hB : 0 ≤ B := (abs_nonneg x).trans hx
  have h1 : |x| * |y| ≤ B * B := mul_le_mul hx hy (abs_nonneg y) hB
  have h2 : |x| * |y| * |z| ≤ B * B * B := mul_le_mul h1 hz (abs_nonneg z) (mul_nonneg hB hB)
  rw [abs_div, abs_mul, abs_mul, abs_two]
  have h3 : 0 ≤ |x| * |y| * |z| := by positivity
  nlinarith

theorem coef_bound2 {x y B : ℝ} (hB : 1 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) : |x * y| ≤ B ^ 3 := by
  have h1 : |x| * |y| ≤ B * B := mul_le_mul hx hy (abs_nonneg y) (by linarith)
  rw [abs_mul]
  nlinarith

theorem coef_bound1 {x B : ℝ} (hB : 1 ≤ B) (hx : |x| ≤ B) : |x| ≤ B ^ 3 := by
  have h2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have h3 : B ≤ B ^ 3 := by
    calc B = B * 1 := (mul_one B).symm
      _ ≤ B * B ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = B ^ 3 := by ring
  linarith

theorem chargeDiff_bound (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) {c : ℝ}
    (hc : |(R.entryCharges K ι).curlCharge p| ≤ c ∧ |(R.entryCharges K ι).gradCharge p| ≤ c ∧
      |(R.entryCharges K ι).velCharge p| ≤ c ∧ |(R.entryCharges K ι).stretchConst| ≤ c ∧
      |(D.charges (some K)).curl ι p| ≤ c ∧ |(D.charges (some K)).product ι p| ≤ c ∧
      |(D.charges (some K)).gradient ι p| ≤ c ∧ c⁻¹ ≤ (D.charges (some K)).length ι p ∧
      (D.charges (some K)).length ι p ≤ c) :
    |chargeDiff D R K ι v G p| ≤ 14 * (|c| + |c⁻¹| + 1) ^ 3 * profileSq D ι v G p ∧
      |extraChargeDensity D R K ι v G p| ≤ 14 * (|c| + |c⁻¹| + 1) ^ 3 * profileSq D ι v G p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc
  set B := |c| + |c⁻¹| + 1 with hBdef
  have hB1 : 1 ≤ B := by have := abs_nonneg c; have := abs_nonneg c⁻¹; linarith
  have hcB : c ≤ B := by have := le_abs_self c; have := abs_nonneg c⁻¹; linarith
  have hlen : |(D.charges (some K)).length ι p| ≤ B := (abs_le_of_between h8 h9).trans (by linarith)
  have hleni : |((D.charges (some K)).length ι p)⁻¹| ≤ B := (inv_abs_le h8 h9).trans (by linarith)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14⟩ := part_bounds (bandProfile D ι v G p)
  set S := profileSq D ι v G p with hSdef
  have hS : ∑ j, ‖bandProfile D ι v G p j‖ ^ 2 = S := rfl
  rw [hS] at p2 p4 p6 p8 p10 p12 p14
  have hA := pow_nonneg (zero_le_one.trans hB1) 3
  have t1 := abs_mul_term (L := 2) (S := S) (coef_bound1 hB1 (h5.trans hcB))
    (y := curlPart (bandProfile D ι v G p)) (by rw [abs_of_nonneg p1]; linarith)
  have t2 := abs_mul_term (L := 1) (S := S) (coef_bound3 (h4.trans hcB) (h7.trans hcB) hlen)
    (y := gradPart (bandProfile D ι v G p)) (by rw [abs_of_nonneg p3]; linarith)
  have t3 := abs_mul_term (L := 1) (S := S) (coef_bound3 (h4.trans hcB) (h7.trans hcB) hleni)
    (y := velPart (bandProfile D ι v G p)) (by rw [abs_of_nonneg p5]; linarith)
  have t4 := abs_mul_term (L := 1) (S := S) (coef_bound2 hB1 (h4.trans hcB) (h6.trans hcB))
    (y := crossPart (bandProfile D ι v G p)) (by rw [abs_of_nonneg p7]; linarith)
  have t5 := abs_mul_term (L := 4) (S := S) (coef_bound1 hB1 (h1.trans hcB))
    (y := curlPart (bandProfile D ι v G p) - curlSq (strainOfVec (bandProfile D ι v G p)))
    (by rw [abs_le]; constructor <;> linarith)
  have t6 := abs_mul_term (L := 2) (S := S) (coef_bound1 hB1 (h2.trans hcB))
    (y := gradPart (bandProfile D ι v G p) - sumSq (strainOfVec (bandProfile D ι v G p)))
    (by rw [abs_le]; constructor <;> linarith)
  have t7 := abs_mul_term (L := 2) (S := S) (coef_bound1 hB1 (h3.trans hcB))
    (y := velPart (bandProfile D ι v G p) - vecSq (velOf (bandProfile D ι v G p)))
    (by rw [abs_le]; constructor <;> linarith)
  have u5 := abs_mul_term (L := 2) (S := S) (coef_bound1 hB1 (h1.trans hcB))
    (y := curlSq (strainOfVec (bandProfile D ι v G p))) (by rw [abs_of_nonneg p9]; linarith)
  have u6 := abs_mul_term (L := 1) (S := S) (coef_bound1 hB1 (h2.trans hcB))
    (y := sumSq (strainOfVec (bandProfile D ι v G p))) (by rw [abs_of_nonneg p11]; linarith)
  have u7 := abs_mul_term (L := 1) (S := S) (coef_bound1 hB1 (h3.trans hcB))
    (y := vecSq (velOf (bandProfile D ι v G p))) (by rw [abs_of_nonneg p13]; linarith)
  have hS0 : 0 ≤ S := by linarith
  have hAS : 0 ≤ B ^ 3 * S := mul_nonneg hA hS0
  rw [abs_le] at t1 t2 t3 t4 t5 t6 t7 u5 u6 u7
  constructor
  · rw [chargeDiff_profile, abs_le]
    constructor <;> linarith
  · rw [extraCharge_profile, abs_le]
    constructor <;> linarith

end Internal

namespace Internal

theorem dominated_on {f : ℝ × ℝ → ℝ} {S : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {M : ℝ}
    (hS : IntegrableOn (fun p => p.1 * S p) s) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hb : ∀ p ∈ s, ‖f p‖ ≤ M * (p.1 * S p)) :
    IntegrableOn f s ∧ ‖∫ p in s, f p‖ ≤ M * ∫ p in s, p.1 * S p := by
  have hg : Integrable (fun p => M * (p.1 * S p)) (volume.restrict s) := hS.const_mul M
  have hae : ∀ᵐ p ∂(volume.restrict s), ‖f p‖ ≤ M * (p.1 * S p) :=
    (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall hb)
  refine ⟨hg.mono' hf hae, ?_⟩
  calc ‖∫ p in s, f p‖ ≤ ∫ p in s, M * (p.1 * S p) := norm_integral_le_of_norm_le hg hae
    _ = M * ∫ p in s, p.1 * S p := integral_const_mul M _

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem offCharge_split (hM : IsCellMesh D.mesh) (hE : EntryChargesRegular D R) (K : Fin D.mesh.count)
    (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hreg : (∀ ι, (∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect)) ∧
      IntegrableOn (fun p => p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) (D.mesh.box K).rect) ∧
      Summable (fun ι : ℤ × ℤ => ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2)) :
    offChargeAmount D R K q v G H = stretchChargeAmount D R K q v G H + chargeSurplus D R K v G := by
  obtain ⟨c, hc⟩ := hE.bounded K
  set M := 14 * (|c| + |c⁻¹| + 1) ^ 3 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hmeas := rect_measurable (D.mesh.box K)
  have hpos : ∀ p ∈ (D.mesh.box K).rect, 0 ≤ p.1 := fun p hp => fst_nonneg_of_mem _ (hM.box_valid K) hp
  have hpiece : ∀ ι, (IntegrableOn (fun p => chargeDiff D R K ι v G p * p.1) (D.mesh.box K).rect ∧
        ‖∫ p in (D.mesh.box K).rect, chargeDiff D R K ι v G p * p.1‖
          ≤ M * ∫ p in (D.mesh.box K).rect, p.1 * profileSq D ι v G p) ∧
      (IntegrableOn (fun p => extraChargeDensity D R K ι v G p * p.1) (D.mesh.box K).rect ∧
        ‖∫ p in (D.mesh.box K).rect, extraChargeDensity D R K ι v G p * p.1‖
          ≤ M * ∫ p in (D.mesh.box K).rect, p.1 * profileSq D ι v G p) := by
    intro ι
    refine ⟨dominated_on hmeas (hreg.1 ι).2 (chargeDiff_aemeasurable D R hE K ι v G (hreg.1 ι).1) (fun p hp => ?_),
      dominated_on hmeas (hreg.1 ι).2 (extraCharge_aemeasurable D R hE K ι v G (hreg.1 ι).1) (fun p hp => ?_)⟩
    · have hb := (chargeDiff_bound D R K ι v G p (hc ι p hp)).1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos p hp)]
      calc |chargeDiff D R K ι v G p| * p.1 ≤ (M * profileSq D ι v G p) * p.1 :=
            mul_le_mul_of_nonneg_right hb (hpos p hp)
        _ = M * (p.1 * profileSq D ι v G p) := by ring
    · have hb := (chargeDiff_bound D R K ι v G p (hc ι p hp)).2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos p hp)]
      calc |extraChargeDensity D R K ι v G p| * p.1 ≤ (M * profileSq D ι v G p) * p.1 :=
            mul_le_mul_of_nonneg_right hb (hpos p hp)
        _ = M * (p.1 * profileSq D ι v G p) := by ring
  have hsumm : Summable (fun ι => M * ∫ p in (D.mesh.box K).rect, p.1 * profileSq D ι v G p) :=
    hreg.2.mul_left M
  have hnn : ∀ ι, 0 ≤ M * ∫ p in (D.mesh.box K).rect, p.1 * profileSq D ι v G p := fun ι =>
    mul_nonneg hM0 (setIntegral_nonneg hmeas (fun p hp => mul_nonneg (hpos p hp) (by unfold profileSq; positivity)))
  have hfun : ∀ ι, (fun p => (D.labelDensity q v G H ι p
      - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (R.entryCharges K ι) D.azimuthOrder ι v G H p
      - extraChargeDensity D R K ι v G p) * p.1) = fun p => chargeDiff D R K ι v G p * p.1 := fun ι =>
    funext fun p => by rw [chargeDiff_eq]
  have sA : Summable (fun ι : ℤ × ℤ => if ι ∈ D.mesh.resolved K then (0 : ℝ) else ∫ p in (D.mesh.box K).rect,
      (D.labelDensity q v G H ι p
        - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
            (R.entryCharges K ι) D.azimuthOrder ι v G H p
        - extraChargeDensity D R K ι v G p) * p.1) := by
    refine Summable.of_norm_bounded hsumm (fun ι => ?_)
    split_ifs
    · simpa using hnn ι
    · rw [hfun ι]
      exact (hpiece ι).1.2
  have sB : Summable (fun ι : ℤ × ℤ => if ι ∈ D.mesh.resolved K then (0 : ℝ) else
      ∫ p in (D.mesh.box K).rect, extraChargeDensity D R K ι v G p * p.1) := by
    refine Summable.of_norm_bounded hsumm (fun ι => ?_)
    split_ifs
    · simpa using hnn ι
    · exact (hpiece ι).2.2
  unfold offChargeAmount stretchChargeAmount chargeSurplus
  rw [← sA.tsum_add sB]
  refine tsum_congr (fun ι => ?_)
  split_ifs
  · simp
  · have hi : IntegrableOn (fun p => (D.labelDensity q v G H ι p
        - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
            (R.entryCharges K ι) D.azimuthOrder ι v G H p
        - extraChargeDensity D R K ι v G p) * p.1) (D.mesh.box K).rect := by
      rw [hfun ι]
      exact (hpiece ι).1.1
    rw [← integral_add hi (hpiece ι).2.1]
    congr 1
    funext p
    ring

end Internal

end Assembly

end CertCell

end Breakdown
