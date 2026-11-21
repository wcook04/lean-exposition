import Breakdown.CertCell.AssemblyStatements
import Breakdown.FracCell.MeshGaugeLinearParts
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace BaseStateInternal

open CellCalculus

theorem modeVel_of_zero (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : modeVel ι (fun _ _ => (0 : Space)) σ y = 0 := by
  funext i
  simp [modeVel, modeAverage, axialRot]

theorem modeGrad_of_zero (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeGrad ι (fun _ _ => (0 : Space →L[ℝ] Space)) σ y = 0 := by
  funext i
  simp [modeGrad, modeAverage, axialRot]

theorem modeHess_of_zero (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeSecondDeriv ι (fun _ _ => (0 : Space →L[ℝ] Space →L[ℝ] Space)) σ y = 0 := by
  funext i
  simp [modeSecondDeriv, modeAverage, axialRot]

theorem labelDensity_of_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (q : Fin k → ℝ)
    (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    D.labelDensity q (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ι p = 0 := by
  unfold CellLayerData.labelDensity PieceWeights.modeTerm PieceWeights.modeDensity
  rw [modeVel_of_zero, modeGrad_of_zero, modeHess_of_zero]
  simp [cnormSq, curlOfGrad, curlGradOfSecondDeriv]

theorem stretch_of_zero (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) :
    CoerciveWeak.stretchFormWith W HW (fun _ _ => 0) (fun _ _ => 0) σ y = 0 := by
  simp [CoerciveWeak.stretchFormWith, curlVec]

theorem formPos_of_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (q : Fin k → ℝ) :
    D.formPos q (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) = 0 := by
  unfold CellLayerData.formPos CellLayerData.stretchPosMean
  simp [labelDensity_of_zero, stretch_of_zero]

theorem rows_of_zero {k : ℕ} (d : ExtendedCertificateData k) : d.rows (fun _ _ => (0 : Space)) = 0 := by
  simp [ExtendedCertificateData.rows, rowNorm, periodPairing]

theorem scalar_of_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (cκ : ℝ) (q : Fin k → ℝ) :
    D.formScalarWith cκ q (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) 0 (fun _ _ => 0) = 0 := by
  simp [CellLayerData.formScalarWith, rows_of_zero, vecNorm, pinValue, matInner]

theorem value_of_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {q : Fin k → ℝ}
    (x : AdmissibleTuple D D.coercivity q) (hv : x.v = 0) (hG : x.G = 0) (hH : x.H = 0) (hκ : x.κ = 0)
    (hF : x.F = 0) : x.value D.coercivity ≤ 0 := by
  unfold AdmissibleTuple.value formValueWith
  rw [hv, hG, hH, hκ, hF]
  have h1 := formPos_of_zero (D.withFormCoercivity D.coercivity) q
  have h2 := scalar_of_zero D D.coercivity q
  simp only [Pi.zero_def] at h1 h2 ⊢
  rw [h1, h2]
  simp


open CellCalculus CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellCoordinates

theorem chosenPressure_of_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {q : Fin k → ℝ}
    (x : AdmissibleTuple D D.coercivity q) (hv : x.v = 0) (hG : x.G = 0) (hH : x.H = 0) (hg : x.g = 0)
    (hκ : x.κ = 0) (hF : x.F = 0) : chosenPressure D x = 0 := by
  funext σ y
  simp [chosenPressure, flipAverage, couplingField, secondDerivTrace, hv, hG, hH, hg, hκ, hF, CellCalculus.crossVec, curlVec,
    flipPoint]

theorem harmonicCos_of_zero {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (ν : ℤ) :
    harmonicCos ν (0 : ℝ → Space → β) = 0 := by
  funext y
  simp [harmonicCos]

theorem harmonicSin_of_zero {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (ν : ℤ) :
    harmonicSin ν (0 : ℝ → Space → β) = 0 := by
  funext y
  simp [harmonicSin]

theorem cosTuple_of_zero (ν : ℤ) : cosTuple ν 0 0 0 0 = ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) := by
  simp only [cosTuple, harmonicCos_of_zero]

theorem sinTuple_of_zero (ν : ℤ) : sinTuple ν 0 0 0 0 = ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) := by
  simp only [sinTuple, harmonicSin_of_zero]

theorem gradientField_zero : SteadyCert.IsGradientField (0 : Space → Space) := by
  refine ⟨0, ?_, ?_, aestronglyMeasurable_const, ?_⟩
  · intro K _
    simp
  · intro K _
    simp
  · intro φ _ j
    simp

theorem moment_of_zero (S : FaceSegment) (w : Bool) (d : ℕ) :
    S.moment w (fun _ => 0) (fun _ => 0) (fun _ => 0) d = 0 := by
  unfold FaceSegment.moment radialStripMoment heightStripMoment
  split_ifs <;> simp

theorem moment_congr_ae (S : FaceSegment) (w : Bool) {F F' : ℝ × ℝ → ℂ} (dFr dFz : ℝ × ℝ → ℂ)
    (h : F =ᵐ[volume] F') (d : ℕ) : S.moment w F dFr dFz d = S.moment w F' dFr dFz d := by
  unfold FaceSegment.moment radialStripMoment heightStripMoment
  split_ifs
  all_goals
    congr 1
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with p hp
    rw [hp]

theorem ballMean_of_const {C : ℝ} (hC : potentialOf (0 : Space → Space) =ᵐ[volume] fun _ => C) :
    ⨍ z in Metric.ball (0 : Space) 1, potentialOf (0 : Space → Space) z = C := by
  rw [setAverage_congr_fun measurableSet_ball (hC.mono fun y hy _ => hy)]
  exact setAverage_const (Metric.measure_ball_pos volume (0 : Space) one_pos).ne' measure_ball_lt_top.ne C

theorem headPressure_of_zero (L : CellLayout) (n : ℤ) :
    headPressure L n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) =ᵐ[volume] fun _ => 0 := by
  obtain ⟨C, hC⟩ := MeshGaugeLinearPotential.potential_affine 0 0 gradientField_zero gradientField_zero 0 0
  have hA := MeshDataAffineModes.gradient_modes_affine L.order 0 0 gradientField_zero gradientField_zero 0 0 C 0 0
    (⨍ z in Metric.ball (0 : Space) 1, potentialOf (0 : Space → Space) z) hC n
  simp only [zero_smul, add_zero, zero_mul, zero_add] at hC hA
  have hB := ballMean_of_const hC
  rw [hB] at hA
  filter_upwards [hA] with p hp
  have h1 := hp.1
  simp only [sub_self, Complex.ofReal_zero, zero_mul, add_zero] at h1
  have e : headPotential (0 : Space → Space) = fun y => potentialOf (0 : Space → Space) y - C := by
    funext y
    unfold headPotential
    rw [hB]
  simp only [headPressure]
  rw [e]
  exact h1

section Layout

variable (L : CellLayout)

theorem velMode_of_zero (n : ℤ) (a : Fin 3) :
    L.velMode n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a = fun _ => 0 := by
  funext p
  fin_cases a <;> simp [CellLayout.velMode, modeVec, frameVec]

theorem gradModeOf_of_zero (n : ℤ) (a b : Fin 3) :
    L.gradModeOf n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a b = fun _ => 0 := by
  funext p
  simp [CellLayout.gradModeOf, gradMode, modeMat, frameMat]

theorem secondModeOf_of_zero (n : ℤ) (a b c : Fin 3) :
    L.secondModeOf n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a b c = fun _ => 0 := by
  funext p
  simp [CellLayout.secondModeOf, modeThird, frameThird]

theorem pressureGradMode_of_zero (n : ℤ) (a : Fin 3) :
    L.pressureGradMode n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a = fun _ => 0 := by
  funext p
  fin_cases a <;> simp [CellLayout.pressureGradMode, modeVec, frameVec]

theorem keyValue_of_zero (key : SkeletonKey) :
    keyValue L ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) key = 0 := by
  cases key with
  | velocity n rad lev lo hi t a d =>
      simp only [keyValue, velMode_of_zero, gradModeOf_of_zero, moment_of_zero]
  | gradient n rad lev lo hi t a d =>
      simp only [keyValue, gradModeOf_of_zero, secondModeOf_of_zero, moment_of_zero, ite_self]
  | pressure n rad lev lo hi t d =>
      simp only [keyValue]
      rw [moment_congr_ae _ _ _ _ (headPressure_of_zero L n), pressureGradMode_of_zero, pressureGradMode_of_zero,
        moment_of_zero]
  | corner n p a =>
      simp only [keyValue]
      rw [velMode_of_zero, gradModeOf_of_zero, gradModeOf_of_zero, secondModeOf_of_zero]
      simp [cornerMoment]
  | stream p =>
      simp only [keyValue]
      rw [velMode_of_zero, gradModeOf_of_zero]
      simp [heightStripMoment]
  | private_ =>
      simp [keyValue]

theorem headData_of_zero (d : L.Datum) : headData L ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) d = 0 := by
  rcases d with d | d | d | d | d | d | d | d
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, gradModeOf_of_zero]
    simp [CellBases.coef]
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, velMode_of_zero]
    simp [CellBases.coef]
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, velMode_of_zero, gradModeOf_of_zero,
      moment_of_zero]
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, gradModeOf_of_zero, secondModeOf_of_zero,
      moment_of_zero, ite_self]
  · simp only [headData]
    rw [moment_congr_ae _ _ _ _ (headPressure_of_zero L _), pressureGradMode_of_zero, pressureGradMode_of_zero,
      moment_of_zero]
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, velMode_of_zero, gradModeOf_of_zero,
      secondModeOf_of_zero]
    simp [cornerMoment]
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, velMode_of_zero, gradModeOf_of_zero]
    simp [heightStripMoment]
  · simp only [headData, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, CellLayout.extraValue, velMode_of_zero,
      gradModeOf_of_zero]
    simp [heightStripMoment, radialStripMoment]

end Layout

theorem headHarmonic_of_zero (L : CellLayout) (ν : ℤ) (d : L.Datum) : headHarmonic L ν 0 0 0 0 d = 0 := by
  simp only [headHarmonic, cosTuple_of_zero, sinTuple_of_zero, headData_of_zero, mul_zero, add_zero]

theorem keyHarmonic_of_zero (L : CellLayout) (ν : ℤ) (key : SkeletonKey) : keyHarmonic L ν 0 0 0 0 key = 0 := by
  simp only [keyHarmonic, cosTuple_of_zero, sinTuple_of_zero, keyValue_of_zero, mul_zero, add_zero]

section Tree

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}

theorem fieldGauge_of_zero (T : TreeEntry D R) (c : Fin T.gauge.count) : T.fieldGauge c 0 0 0 0 = 0 := by
  simp [TreeEntry.fieldGauge, keyHarmonic_of_zero]

theorem trueData_of_zero (T : TreeEntry D R) {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q)
    (hv : x.v = 0) (hG : x.G = 0) (hH : x.H = 0) (hg : x.g = 0) (hκ : x.κ = 0) (hF : x.F = 0) :
    T.trueData x = 0 := by
  funext a
  have hP := chosenPressure_of_zero D x hv hG hH hg hκ hF
  simp only [TreeEntry.trueData, TreeEntry.fieldData, hP, hv, hG, hH, hκ]
  rcases h1 : T.evalCell a with _ | ⟨K, d⟩
  · rcases h2 : T.evalKappa a with _ | i
    · rcases h3 : T.skelKey a with _ | ⟨ι, key⟩
      · simp
      · simp [TreeEntry.fieldKey, keyHarmonic_of_zero, fieldGauge_of_zero]
    · simp
  · simp [TreeEntry.fieldShifted, TreeEntry.fieldHead, headHarmonic_of_zero, fieldGauge_of_zero]

end Tree

end BaseStateInternal

end Assembly

end CertCell

end Breakdown
