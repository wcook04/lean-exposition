import Breakdown.CellReduction.InstFieldPotentialStream

open scoped ContDiff RealInnerProductSpace Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

namespace FieldPot

open Coercive.RotationInternal

def timeC (κ : FieldKey) (σ : ℝ) : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I)

def typeTwoPot (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) (v : Space) : Space :=
  realPartVec (timeC κ σ • (radialAmpField P κ.phaseIndex A.highOrder (streamF P A) turnL v +
    radialAmpField P κ.phaseIndex A.highOrder (swirlF A) (ContinuousLinearMap.id ℝ Space) v))

theorem phase_hasDerivAt {P : ShapeParams} (hP : IsShapeParams P) (y : Space) :
    HasDerivAt P.radialPhase (deriv P.radialPhase (‖y‖ ^ 2)) (‖y‖ ^ 2) := by
  obtain ⟨δ, hδ, hs⟩ := hP.phase.smooth
  have hmem : ‖y‖ ^ 2 ∈ Set.Ioi (-δ) := by
    simp only [Set.mem_Ioi]
    nlinarith [sq_nonneg ‖y‖]
  exact ((hs.differentiableOn (by norm_num) _ hmem).differentiableAt (isOpen_Ioi.mem_nhds hmem)).hasDerivAt

theorem typeTwo_curl_ne {P : ShapeParams} (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp) (h0 : κ.label.1 = 0)
    (hs : IsJoinedSpline 2 2 A.stream) (hw : IsJoinedSpline 1 1 A.swirl) (σ : ℝ) {y : Space} (hy : y ≠ 0) :
    AdjointDefect.curlAt (typeTwoPot P κ A σ) y = realPartVec (keyVector P κ A σ y) := by
  have hL := hP.chartLength_pos
  have ht1 := chartCoord_lt_one P hL y
  have hr0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hΦ := phase_hasDerivAt hP y
  have hpd : DifferentiableAt ℝ (fun s : ℝ => s ^ 1 * (1 - s) ^ A.highOrder) (chartCoord P y) := by fun_prop
  have hsT : HasFDerivAt (streamF P A) (fderiv ℝ (streamF P A) (chartCoord P y, CellCert.GivenFields.heightRatio y))
      (chartCoord P y, CellCert.GivenFields.heightRatio y) :=
    ((streamF_smooth hP hs).differentiable (by norm_num) _).hasFDerivAt
  have hsW : HasFDerivAt (swirlF A) (fderiv ℝ (swirlF A) (chartCoord P y, CellCert.GivenFields.heightRatio y))
      (chartCoord P y, CellCert.GivenFields.heightRatio y) :=
    ((swirlF_smooth A hw).differentiable (by norm_num) _).hasFDerivAt
  obtain ⟨ψ', hψ, hψv⟩ := scalar_grad P hL κ.phaseIndex A.highOrder (streamF P A) _ hy _ _ hΦ hpd.hasDerivAt hsT
  obtain ⟨h', hh, hhv⟩ := scalar_grad P hL κ.phaseIndex A.highOrder (swirlF A) _ hy _ _ hΦ hpd.hasDerivAt hsW
  have key := curl_scalarPair hψ hh _ _ _ _ (timeC κ σ) hψv hhv
  have hfun : typeTwoPot P κ A σ = fun v => realPartVec (timeC κ σ •
      ((Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        CellCert.GivenFields.weightPoly 1 A.highOrder (chartCoord P v) *
          streamF P A (chartCoord P v, CellCert.GivenFields.heightRatio v)) • ofRealL (turnL v) +
      (Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        CellCert.GivenFields.weightPoly 1 A.highOrder (chartCoord P v) *
          swirlF A (chartCoord P v, CellCert.GivenFields.heightRatio v)) • ofRealL v)) := by
    funext v
    rfl
  have hc0 : reducedComps P κ A (chartCoord P y) (CellCert.GivenFields.heightRatio y) 0 =
      -(((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) *
        ((((-2 * CellCert.GivenFields.heightRatio y : ℝ)) : ℂ) *
            streamF P A (chartCoord P y, CellCert.GivenFields.heightRatio y) +
          (((1 - CellCert.GivenFields.heightRatio y ^ 2 : ℝ)) : ℂ) *
            fderiv ℝ (streamF P A) (chartCoord P y, CellCert.GivenFields.heightRatio y) (0, 1))) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_zero]
    rw [streamHeight_deriv P hP A hs ht1]
    simp [CellCert.GivenFields.weightPoly]
  have hc1 : reducedComps P κ A (chartCoord P y) (CellCert.GivenFields.heightRatio y) 1 =
      -((((chartCoord P y * (1 - chartCoord P y) : ℝ)) : ℂ) *
          (((deriv (fun s : ℝ => s ^ 1 * (1 - s) ^ A.highOrder) (chartCoord P y) : ℝ) : ℂ) *
              streamF P A (chartCoord P y, CellCert.GivenFields.heightRatio y) +
            ((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) *
              fderiv ℝ (streamF P A) (chartCoord P y, CellCert.GivenFields.heightRatio y) (1, 0)) +
        Complex.I * ((((κ.phaseIndex : ℝ) * (2 * ‖y‖ ^ 2 * deriv P.radialPhase (‖y‖ ^ 2)) : ℝ)) : ℂ) *
          (((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) *
            streamF P A (chartCoord P y, CellCert.GivenFields.heightRatio y)) +
        2 * (((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) *
            streamF P A (chartCoord P y, CellCert.GivenFields.heightRatio y))) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_one, Matrix.cons_val_zero, shiftedScale,
      CellCert.GivenFields.radialScale]
    rw [streamRadial_deriv P hP A hs A.highOrder ht1, streamF_eq P hP A ht1, phaseSlope, chartRadius_coord P hL]
    simp [CellCert.GivenFields.weightPoly]
  have hc2 : reducedComps P κ A (chartCoord P y) (CellCert.GivenFields.heightRatio y) 2 =
      ((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) *
        fderiv ℝ (swirlF A) (chartCoord P y, CellCert.GivenFields.heightRatio y) (0, 1) := by
    rw [swirlF_second A hw]
    simp [reducedComps, if_pos h0, CellCert.GivenFields.weightPoly]
  rw [hfun, key, keyVector_typeTwo P κ A σ y h0, hc0, hc1, hc2]
  congr 1
  have htc : Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) = timeC κ σ := rfl
  rw [htc]
  generalize timeC κ σ = c
  have hw1 : CellCert.GivenFields.weightPoly 1 A.highOrder (chartCoord P y) =
      ((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) := by
    simp [CellCert.GivenFields.weightPoly]
  beta_reduce
  simp only [hw1]
  generalize Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) = E
  generalize deriv P.radialPhase (‖y‖ ^ 2) = Φ'
  generalize ((chartCoord P y * (1 - chartCoord P y) ^ A.highOrder : ℝ) : ℂ) = p
  generalize deriv (fun s : ℝ => s ^ 1 * (1 - s) ^ A.highOrder) (chartCoord P y) = p1
  generalize streamF P A (chartCoord P y, CellCert.GivenFields.heightRatio y) = sT
  generalize fderiv ℝ (streamF P A) (chartCoord P y, CellCert.GivenFields.heightRatio y) (1, 0) = Ft
  generalize fderiv ℝ (streamF P A) (chartCoord P y, CellCert.GivenFields.heightRatio y) (0, 1) = Fx
  generalize fderiv ℝ (swirlF A) (chartCoord P y, CellCert.GivenFields.heightRatio y) (0, 1) = Fw
  have hrel : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_three]
  have hrc : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hrL : ((‖y‖ : ℝ) : ℂ) + ((P.chartLength : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ‖y‖ + P.chartLength ≠ 0)
  have hc : chartCoord P y = ‖y‖ / (‖y‖ + P.chartLength) := rfl
  have hx : CellCert.GivenFields.heightRatio y = y 2 / ‖y‖ := rfl
  rw [hc, hx]
  funext i
  fin_cases i
  · simp [CellCert.GivenFields.radialVec, CellCert.GivenFields.polarVecQ, CellCert.GivenFields.azimVecQ,
      CellCert.GivenFields.qOf, CellCert.GivenFields.heightRatio]
    field_simp
    ring
  · simp [CellCert.GivenFields.radialVec, CellCert.GivenFields.polarVecQ, CellCert.GivenFields.azimVecQ,
      CellCert.GivenFields.qOf, CellCert.GivenFields.heightRatio]
    field_simp
    ring
  · have hrelc : ((y 0 : ℝ) : ℂ) ^ 2 + ((y 1 : ℝ) : ℂ) ^ 2 = ((‖y‖ : ℝ) : ℂ) ^ 2 - ((y 2 : ℝ) : ℂ) ^ 2 := by
      have : y 0 ^ 2 + y 1 ^ 2 = ‖y‖ ^ 2 - y 2 ^ 2 := by linarith
      exact_mod_cast this
    simp [CellCert.GivenFields.radialVec, CellCert.GivenFields.polarVecQ, CellCert.GivenFields.azimVecQ,
      CellCert.GivenFields.qOf, CellCert.GivenFields.heightRatio, hrelc]
    field_simp
    ring

theorem realPartVec_norm (w : Fin 3 → ℂ) : ‖realPartVec w‖ ≤ 3 * ‖w‖ := by
  have hw : realPartVec w = (w 0).re • unitVector 0 + (w 1).re • unitVector 1 + (w 2).re • unitVector 2 := by
    apply space_ext <;> simp [realPartVec, unit_apply]
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  have hc : ∀ i : Fin 3, |(w i).re| ≤ ‖w‖ := fun i => (Complex.abs_re_le_norm _).trans (norm_le_pi_norm w i)
  rw [hw]
  refine (norm_add₃_le).trans ?_
  simp only [norm_smul, hu, mul_one, Real.norm_eq_abs]
  linarith [hc 0, hc 1, hc 2]

theorem realPartVec_opNorm : ‖realPartVec‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) realPartVec_norm

theorem timeC_norm (κ : FieldKey) (σ : ℝ) : ‖timeC κ σ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem timeC_periodic (κ : FieldKey) (σ : ℝ) : timeC κ (σ + 1) = timeC κ σ := by
  unfold timeC
  have e : (((2 * Real.pi * (labelTime κ.label : ℝ) * (σ + 1) : ℝ)) : ℂ) * Complex.I =
      (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ)) : ℂ) * Complex.I +
        ((labelTime κ.label : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem timeC_hasDerivAt (κ : FieldKey) (σ : ℝ) :
    HasDerivAt (timeC κ) (timeC κ σ * (((2 * Real.pi * (labelTime κ.label : ℝ) : ℝ) : ℂ) * Complex.I)) σ := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * Real.pi * (labelTime κ.label : ℝ) * s) (2 * Real.pi * (labelTime κ.label : ℝ)) σ := by
    simpa using (hasDerivAt_id σ).const_mul (2 * Real.pi * (labelTime κ.label : ℝ))
  exact (h1.ofReal_comp.mul_const Complex.I).cexp

theorem timeC_contDiff (κ : FieldKey) : ContDiff ℝ 1 (timeC κ) := by
  unfold timeC
  have h : ContDiff ℝ 1 (fun s : ℝ => (((2 * Real.pi * (labelTime κ.label : ℝ) * s : ℝ)) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
  exact h.cexp

theorem curlAt_continuous {f : Space → Space} (hf : ContDiff ℝ 1 f) : Continuous (fun y => AdjointDefect.curlAt f y) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hc : ∀ (j i : Fin 3), Continuous (fun y => fderiv ℝ f y (unitVector j) i) := fun j i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (hd.clm_apply continuous_const)
  unfold AdjointDefect.curlAt
  exact ((((hc 1 2).sub (hc 2 1)).smul continuous_const).add (((hc 2 0).sub (hc 0 2)).smul continuous_const)).add
    (((hc 0 1).sub (hc 1 0)).smul continuous_const)

theorem typeTwoKey_pack {P : ShapeParams} (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp) (h0 : κ.label.1 = 0)
    (hs : IsJoinedSpline 2 2 A.stream) (hw : IsJoinedSpline 1 1 A.swirl) (he : 3 ≤ A.highOrder)
    (hsmooth : ∀ σ, ContDiff ℝ 1 (keyVector P κ A σ)) :
    ∃ C, PotentialPack (fun σ y => realPartVec (keyVector P κ A σ y)) (typeTwoPot P κ A) C := by
  obtain ⟨hb1, C1, hC1⟩ := radialAmpField_regular P κ.phaseIndex A.highOrder (streamF P A) turnL hP he
    (streamF_smooth hP hs) turnL_norm
  obtain ⟨hb2, C2, hC2⟩ := radialAmpField_regular P κ.phaseIndex A.highOrder (swirlF A)
    (ContinuousLinearMap.id ℝ Space) hP he (swirlF_smooth A hw) ContinuousLinearMap.norm_id_le
  set b : Space → Fin 3 → ℂ := fun v => radialAmpField P κ.phaseIndex A.highOrder (streamF P A) turnL v +
    radialAmpField P κ.phaseIndex A.highOrder (swirlF A) (ContinuousLinearMap.id ℝ Space) v with hbdef
  have hb : ContDiff ℝ 1 b := hb1.add hb2
  have hpot : typeTwoPot P κ A = fun σ v => realPartVec (timeC κ σ • b v) := rfl
  have hC10 : 0 ≤ C1 := by
    have h := (hC1 0).1
    simp only [norm_zero, add_zero, one_pow, div_one] at h
    exact (norm_nonneg _).trans h
  have hC20 : 0 ≤ C2 := by
    have h := (hC2 0).1
    simp only [norm_zero, add_zero, one_pow, div_one] at h
    exact (norm_nonneg _).trans h
  have hbb : ∀ y, ‖b y‖ ≤ (C1 + C2) / (1 + ‖y‖) ^ 2 := fun y => by
    rw [add_div]
    exact (norm_add_le _ _).trans (add_le_add (hC1 y).1 (hC2 y).1)
  have hbd : ∀ y, ‖fderiv ℝ b y‖ ≤ (C1 + C2) / (1 + ‖y‖) ^ 3 := fun y => by
    have e : fderiv ℝ b y = fderiv ℝ (radialAmpField P κ.phaseIndex A.highOrder (streamF P A) turnL) y +
        fderiv ℝ (radialAmpField P κ.phaseIndex A.highOrder (swirlF A) (ContinuousLinearMap.id ℝ Space)) y :=
      fderiv_add (hb1.differentiable (by norm_num) y) (hb2.differentiable (by norm_num) y)
    rw [e, add_div]
    exact (norm_add_le _ _).trans (add_le_add (hC1 y).2 (hC2 y).2)
  set ℓ : ℝ := 2 * Real.pi * (labelTime κ.label : ℝ) with hℓ
  refine ⟨3 * (1 + |ℓ|) * (C1 + C2), ⟨?_, fun σ y => ?_, fun σ y => ?_, fun σ y => ?_⟩⟩
  · rw [hpot]
    exact realPartVec.contDiff.comp (((timeC_contDiff κ).comp contDiff_fst).smul (hb.comp contDiff_snd))
  · simp only [hpot, timeC_periodic]
  · have hcont1 : Continuous (fun v => AdjointDefect.curlAt (typeTwoPot P κ A σ) v) := by
      apply curlAt_continuous
      rw [hpot]
      exact realPartVec.contDiff.comp (hb.const_smul (timeC κ σ))
    have hcont2 : Continuous (fun v => realPartVec (keyVector P κ A σ v)) :=
      realPartVec.continuous.comp (hsmooth σ).continuous
    have hext := Continuous.ext_on (dense_compl_singleton (0 : Space)) hcont1 hcont2
      (fun v hv => typeTwo_curl_ne hP κ A h0 hs hw σ hv)
    exact congrFun hext y
  · have hr := norm_nonneg y
    have h1y : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith
    have hK : 0 ≤ C1 + C2 := by linarith
    have hbase : ‖realPartVec (timeC κ σ • b y)‖ ≤ 3 * (C1 + C2) / (1 + ‖y‖) ^ 2 := by
      calc ‖realPartVec (timeC κ σ • b y)‖ ≤ 3 * ‖timeC κ σ • b y‖ := realPartVec_norm _
        _ = 3 * ‖b y‖ := by rw [norm_smul, timeC_norm, one_mul]
        _ ≤ 3 * ((C1 + C2) / (1 + ‖y‖) ^ 2) := by gcongr; exact hbb y
        _ = 3 * (C1 + C2) / (1 + ‖y‖) ^ 2 := by ring
    have hmono : 3 * (C1 + C2) / (1 + ‖y‖) ^ 2 ≤ 3 * (1 + |ℓ|) * (C1 + C2) / (1 + ‖y‖) ^ 2 := by
      gcongr
      nlinarith [abs_nonneg ℓ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hpot]
      exact hbase.trans hmono
    · have hd : HasDerivAt (fun s => typeTwoPot P κ A s y)
          (realPartVec ((timeC κ σ * ((ℓ : ℂ) * Complex.I)) • b y)) σ := by
        rw [hpot]
        exact realPartVec.hasFDerivAt.comp_hasDerivAt σ ((timeC_hasDerivAt κ σ).smul_const (b y))
      rw [hd.deriv]
      calc ‖realPartVec ((timeC κ σ * ((ℓ : ℂ) * Complex.I)) • b y)‖
          ≤ 3 * ‖(timeC κ σ * ((ℓ : ℂ) * Complex.I)) • b y‖ := realPartVec_norm _
        _ = 3 * |ℓ| * ‖b y‖ := by
            rw [norm_smul, norm_mul, timeC_norm, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
            ring
        _ ≤ 3 * |ℓ| * ((C1 + C2) / (1 + ‖y‖) ^ 2) := by gcongr; exact hbb y
        _ ≤ 3 * (1 + |ℓ|) * (C1 + C2) / (1 + ‖y‖) ^ 2 := by
            rw [mul_div_assoc]
            gcongr
            linarith
    · have hd : HasFDerivAt (typeTwoPot P κ A σ) (realPartVec.comp (timeC κ σ • fderiv ℝ b y)) y := by
        rw [hpot]
        exact realPartVec.hasFDerivAt.comp y (((hb.differentiable (by norm_num) y).hasFDerivAt).const_smul (timeC κ σ))
      rw [hd.fderiv]
      calc ‖realPartVec.comp (timeC κ σ • fderiv ℝ b y)‖ ≤ ‖realPartVec‖ * ‖timeC κ σ • fderiv ℝ b y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 3 * ‖fderiv ℝ b y‖ := by
            rw [norm_smul, timeC_norm, one_mul]
            gcongr
            exact realPartVec_opNorm
        _ ≤ 3 * ((C1 + C2) / (1 + ‖y‖) ^ 3) := by gcongr; exact hbd y
        _ ≤ 3 * (1 + |ℓ|) * (C1 + C2) / (1 + ‖y‖) ^ 3 := by
            rw [← mul_div_assoc]
            gcongr
            nlinarith [abs_nonneg ℓ]

theorem pack_congr {F F' A : ℝ → Space → Space} {C : ℝ} (h : PotentialPack F A C) (e : ∀ σ y, F σ y = F' σ y) :
    PotentialPack F' A C :=
  ⟨h.smooth, h.periodic, fun σ y => (h.curl σ y).trans (e σ y), h.bound⟩

theorem typeTwo_group {P : ShapeParams} {D : TimeFieldData} (hP : IsShapeParams P) (hD : IsTimeFieldData D)
    (h0 : ∀ κ ∈ D.keys, κ.label.1 = 0) (hi : ∀ κ ∈ D.keys, 3 ≤ (D.amp κ).highOrder) :
    ∃ (A : ℝ → Space → Space) (C : ℝ), PotentialPack (shapeInfoField P D) A C := by
  have h : ∀ κ ∈ D.keys, ∃ C, PotentialPack (fun σ y => realPartVec (keyVector P κ (D.amp κ) σ y))
      (typeTwoPot P κ (D.amp κ)) C := fun κ hκ =>
    typeTwoKey_pack hP κ (D.amp κ) (h0 κ hκ) (hD.stream_class κ hκ (h0 κ hκ)) (hD.swirl_class κ hκ (h0 κ hκ))
      (hi κ hκ) (fun σ => (shapeParts_closed.type_two_smooth P D κ σ hP hD hκ (h0 κ hκ)).smooth)
  choose! C hC using h
  refine ⟨_, _, pack_congr (pack_sum D.keys _ _ C hC) fun σ y => ?_⟩
  simp only [shapeInfoField, complexField, map_sum]

end FieldPot

end Internal

end Instantiation

end CellReduction

end Breakdown
