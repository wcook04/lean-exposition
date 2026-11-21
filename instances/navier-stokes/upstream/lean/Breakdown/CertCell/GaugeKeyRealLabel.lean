import Breakdown.CertCell.GaugeKeyStatements
import Breakdown.FracCell.ConjugateData
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CertCell

namespace RealLabelZeroInternal

open CellCert CellCert.CellCoordinates CellCert.CellFormula CellCert.CellAnalysis
open CellCert.CellFormula.ConjugateDataInternal

theorem conj_presMode (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) :
    conj (presMode m n P r z) = presMode m (-n) P r z := by
  unfold presMode
  exact conj_angle m n (fun θ => P (cylPoint r θ z))

section Layout

variable (L : CellLayout) {j : ℕ} (x : Assembly.FieldTuple j)

theorem velMode_real (a : Fin 3) : (fun p => conj (L.velMode 0 x a p)) = L.velMode 0 x a := by
  have h := velMode_neg L x 0 a
  rw [neg_zero] at h
  exact h.symm

theorem gradModeOf_real (a b : Fin 3) : (fun p => conj (L.gradModeOf 0 x a b p)) = L.gradModeOf 0 x a b := by
  have h := gradModeOf_neg L x 0 a b
  rw [neg_zero] at h
  exact h.symm

theorem secondModeOf_real (a b c : Fin 3) :
    (fun p => conj (L.secondModeOf 0 x a b c p)) = L.secondModeOf 0 x a b c := by
  have h := secondModeOf_neg L x 0 a b c
  rw [neg_zero] at h
  exact h.symm

theorem pressureGradMode_real (a : Fin 3) :
    (fun p => conj (L.pressureGradMode 0 x a p)) = L.pressureGradMode 0 x a := by
  have h := pressureGradMode_neg L x 0 a
  rw [neg_zero] at h
  exact h.symm

theorem headPressure_real : (fun p => conj (headPressure L 0 x p)) = headPressure L 0 x := by
  funext p
  simp only [headPressure]
  rw [conj_presMode, neg_zero]

theorem keyValue_real (key : SkeletonKey) (h : GaugeKey.keyMode key = some 0) :
    conj (keyValue L x key) = keyValue L x key := by
  cases key with
  | velocity n rad lev lo hi t a d =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue]
      rw [conj_segMoment, velMode_real, gradModeOf_real, gradModeOf_real]
  | gradient n rad lev lo hi t a d =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue]
      split_ifs
      · rw [conj_segMoment, gradModeOf_real, secondModeOf_real, secondModeOf_real]
      · rw [conj_segMoment, gradModeOf_real, secondModeOf_real, secondModeOf_real]
  | pressure n rad lev lo hi t d =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue]
      rw [conj_segMoment, headPressure_real, pressureGradMode_real, pressureGradMode_real]
  | corner n p a =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue]
      rw [conj_corner, velMode_real, gradModeOf_real, gradModeOf_real, secondModeOf_real]
  | stream p =>
      simp only [keyValue]
      rw [conj_heightStrip, velMode_real, gradModeOf_real]
  | private_ =>
      simp [keyValue]

end Layout

theorem harmonicSin_zero_label {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (f : ℝ → Space → β) :
    CellCalculus.harmonicSin 0 f = 0 := by
  funext y
  simp [CellCalculus.harmonicSin]

theorem sinTuple_zero_label (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) :
    CellCalculus.sinTuple 0 v G H Pg = ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) := by
  simp only [CellCalculus.sinTuple, harmonicSin_zero_label]

theorem zero_gradientField : SteadyCert.IsGradientField (0 : Space → Space) := by
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

theorem moment_ae_congr (S : FaceSegment) (w : Bool) {F F' : ℝ × ℝ → ℂ} (dFr dFz : ℝ × ℝ → ℂ)
    (h : F =ᵐ[volume] F') (d : ℕ) : S.moment w F dFr dFz d = S.moment w F' dFr dFz d := by
  unfold FaceSegment.moment radialStripMoment heightStripMoment
  split_ifs
  all_goals
    congr 1
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with p hp
    rw [hp]

theorem ballMean_potential_zero {C : ℝ} (hC : potentialOf (0 : Space → Space) =ᵐ[volume] fun _ => C) :
    ⨍ z in Metric.ball (0 : Space) 1, potentialOf (0 : Space → Space) z = C := by
  rw [setAverage_congr_fun measurableSet_ball (hC.mono fun y hy _ => hy)]
  exact setAverage_const (Metric.measure_ball_pos volume (0 : Space) one_pos).ne' measure_ball_lt_top.ne C

theorem headPressure_zero (L : CellLayout) (n : ℤ) :
    headPressure L n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) =ᵐ[volume] fun _ => 0 := by
  obtain ⟨C, hC⟩ := MeshGaugeLinearPotential.potential_affine 0 0 zero_gradientField zero_gradientField 0 0
  have hA := MeshDataAffineModes.gradient_modes_affine L.order 0 0 zero_gradientField zero_gradientField 0 0 C 0 0
    (⨍ z in Metric.ball (0 : Space) 1, potentialOf (0 : Space → Space) z) hC n
  simp only [zero_smul, add_zero, zero_mul, zero_add] at hC hA
  have hB := ballMean_potential_zero hC
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

section ZeroLayout

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
      rw [moment_ae_congr _ _ _ _ (headPressure_zero L n), pressureGradMode_of_zero, pressureGradMode_of_zero,
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

end ZeroLayout

theorem keyHarmonic_label_zero_im (L : CellLayout) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (key : SkeletonKey)
    (h : GaugeKey.keyMode key = some 0) : (keyHarmonic L 0 v G H Pg key).im = 0 := by
  simp only [keyHarmonic, sinTuple_zero_label, keyValue_of_zero, mul_zero, add_zero]
  exact Complex.conj_eq_iff_im.mp (keyValue_real L _ key h)

end RealLabelZeroInternal

namespace TreeEntry

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D}

theorem fieldRealLabelZero_holds (T : TreeEntry D R) : T.FieldRealLabelZero :=
  fun v G H Pg key h => RealLabelZeroInternal.keyHarmonic_label_zero_im T.keyLayout v G H Pg key h

end TreeEntry

end CertCell

end Breakdown
