import Breakdown.CertCell.GaugeKeyStatements
import Breakdown.FracCell.ConjugateData
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CertCell

namespace KeyConjInternal

open SteadyCert CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Breakdown.FracInternal.MeshDataAffineModes

theorem harmonicCos_negFreq (ν : ℤ) {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (f : ℝ → Space → β) :
    harmonicCos (-ν) f = harmonicCos ν f := by
  funext y
  simp only [harmonicCos, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

theorem harmonicSin_negFreq (ν : ℤ) {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (f : ℝ → Space → β) :
    harmonicSin (-ν) f = -harmonicSin ν f := by
  funext y
  simp only [harmonicSin, Pi.neg_apply, Int.cast_neg, mul_neg, neg_mul, Real.sin_neg, neg_smul, integral_neg]

theorem cosTuple_negFreq (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) :
    cosTuple (-ν) v G H Pg = cosTuple ν v G H Pg := by
  simp only [cosTuple, harmonicCos_negFreq]

theorem sinTuple_negFreq (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) :
    sinTuple (-ν) v G H Pg = -sinTuple ν v G H Pg := by
  simp only [sinTuple, harmonicSin_negFreq, Prod.neg_mk, neg_zero]

theorem frameVec_negVec (θ : ℝ) (u : Space) : frameVec θ (-u) = -frameVec θ u := by
  funext a
  fin_cases a <;> simp [frameVec, inner_neg_left]

theorem modeVec_negField (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) :
    modeVec m n (-v) r z = -modeVec m n v r z := by
  funext a
  simp only [modeVec, Pi.neg_apply, frameVec_negVec, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]

theorem modeMat_negField (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) :
    modeMat m n (-G) r z = -modeMat m n G r z := by
  funext a b
  simp only [modeMat, frameMat, Pi.neg_apply, _root_.neg_apply, inner_neg_left, Complex.ofReal_neg,
    mul_neg, intervalIntegral.integral_neg]

theorem modeThird_negField (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) :
    modeThird m n (-H) a b c = -modeThird m n H a b c := by
  funext p
  simp only [modeThird, frameThird, Pi.neg_apply, _root_.neg_apply, inner_neg_left, Complex.ofReal_neg,
    mul_neg, intervalIntegral.integral_neg]

theorem radialStripMoment_negField (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    radialStripMoment c o lo hi (-F) (-dF) t = -radialStripMoment c o lo hi F dF t := by
  unfold radialStripMoment
  rw [← mul_neg, ← integral_neg]
  congr 2
  funext p
  simp only [Pi.neg_apply]
  ring

theorem heightStripMoment_negField (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    heightStripMoment c o lo hi wt (-F) (-dF) t = -heightStripMoment c o lo hi wt F dF t := by
  unfold heightStripMoment
  rw [← mul_neg, ← integral_neg]
  congr 2
  funext p
  simp only [Pi.neg_apply]
  ring

theorem cornerMoment_negField (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz (-F) (-Fr) (-Fz) (-Frz) = -cornerMoment cr orr cz oz F Fr Fz Frz := by
  unfold cornerMoment
  rw [← mul_neg, ← integral_neg]
  congr 2
  funext p
  simp only [Pi.neg_apply]
  ring

theorem moment_negField (S : FaceSegment) (w : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (d : ℕ) :
    S.moment w (-F) (-dFr) (-dFz) d = -S.moment w F dFr dFz d := by
  unfold FaceSegment.moment
  split_ifs <;> first
    | exact radialStripMoment_negField _ _ _ _ _ _ _
    | exact heightStripMoment_negField _ _ _ _ _ _ _ _

theorem moment_congr_ae (S : FaceSegment) (w : Bool) {F F' : ℝ × ℝ → ℂ} (hF : ∀ᵐ p ∂volume, F' p = F p)
    (dFr dFz : ℝ × ℝ → ℂ) (d : ℕ) : S.moment w F' dFr dFz d = S.moment w F dFr dFz d := by
  unfold FaceSegment.moment radialStripMoment heightStripMoment
  split_ifs <;>
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hF] with p hp
    rw [hp]

section Layout

variable (L : CellLayout) {k : ℕ} (x : CellCert.Assembly.FieldTuple k)

theorem velMode_negField (n : ℤ) (a : Fin 3) : L.velMode n (-x) a = -L.velMode n x a := by
  funext p
  simp only [CellLayout.velMode, Prod.fst_neg, modeVec_negField, Pi.neg_apply]

theorem gradModeOf_negField (n : ℤ) (a b : Fin 3) : L.gradModeOf n (-x) a b = -L.gradModeOf n x a b := by
  funext p
  simp only [CellLayout.gradModeOf, gradMode, Prod.snd_neg, Prod.fst_neg, modeMat_negField, Pi.neg_apply]

theorem secondModeOf_negField (n : ℤ) (a b c : Fin 3) :
    L.secondModeOf n (-x) a b c = -L.secondModeOf n x a b c := by
  simp only [CellLayout.secondModeOf, Prod.snd_neg, Prod.fst_neg, modeThird_negField]

theorem pressureGradMode_negField (n : ℤ) (a : Fin 3) :
    L.pressureGradMode n (-x) a = -L.pressureGradMode n x a := by
  funext p
  simp only [CellLayout.pressureGradMode, Prod.snd_neg, modeVec_negField, Pi.neg_apply]

end Layout

theorem isPotentialOf_neg {Q : Space → Space} {q : Space → ℝ} (h : IsPotentialOf Q q) :
    IsPotentialOf (-Q) (fun y => -q y) := by
  obtain ⟨hm, hs, hi⟩ := h
  refine ⟨hm.neg, ?_, ?_⟩
  · simpa only [neg_sq] using hs
  · intro φ hφ j
    simp only [mul_neg, Pi.neg_apply, inner_neg_left, integral_neg, hi φ hφ j]

theorem test_mul_integrable {q : Space → ℝ} (hq : LocallyIntegrable q volume) (φ : Space → ℝ) (hφ : IsTestScalar φ)
    (j : Fin 3) : Integrable (fun y => fderiv ℝ φ y (unitVector j) * q y) := by
  have hc : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.2.fderiv ℝ).comp_left (g := fun A : Space →L[ℝ] ℝ => A (unitVector j)) (by simp)
  simpa [smul_eq_mul] using hq.integrable_smul_left_of_hasCompactSupport hc hs

theorem potential_unique {Q : Space → Space} {q₁ q₂ : Space → ℝ} (h₁ : IsPotentialOf Q q₁)
    (h₂ : IsPotentialOf Q q₂) : ∃ C : ℝ, q₁ =ᵐ[volume] fun y => q₂ y + C := by
  have l₁ := pot_locInt h₁
  have l₂ := pot_locInt h₂
  obtain ⟨C, hC⟩ := MeshGaugeLinearPotential.const_of_zero_grad (fun y => q₁ y - q₂ y) (l₁.sub l₂)
    (fun φ hφ j => by
      have e : (fun y => fderiv ℝ φ y (unitVector j) * (q₁ y - q₂ y)) =
          fun y => fderiv ℝ φ y (unitVector j) * q₁ y - fderiv ℝ φ y (unitVector j) * q₂ y := by
        funext y; ring
      rw [e, integral_sub (test_mul_integrable l₁ φ hφ j) (test_mul_integrable l₂ φ hφ j),
        h₁.2.2 φ hφ j, h₂.2.2 φ hφ j, sub_self])
  refine ⟨C, ?_⟩
  filter_upwards [hC] with y hy
  have hy' : q₁ y - q₂ y = C := hy
  linarith

theorem potentialOf_spec_of_exists {Q : Space → Space} (h : ∃ q, IsPotentialOf Q q) :
    IsPotentialOf Q (potentialOf Q) := by
  unfold potentialOf
  rw [dif_pos h]
  exact h.choose_spec

theorem potentialOf_of_not_exists {Q : Space → Space} (h : ¬ ∃ q, IsPotentialOf Q q) :
    potentialOf Q = fun _ => 0 := by
  unfold potentialOf
  rw [dif_neg h]

theorem headPotential_negField (Q : Space → Space) :
    headPotential (-Q) =ᵐ[volume] fun y => -headPotential Q y := by
  by_cases hex : ∃ q, IsPotentialOf Q q
  · have h₁ := potentialOf_spec_of_exists hex
    have h₂ := potentialOf_spec_of_exists (⟨_, isPotentialOf_neg h₁⟩ : ∃ q, IsPotentialOf (-Q) q)
    obtain ⟨C, hC⟩ := potential_unique h₂ (isPotentialOf_neg h₁)
    have hint : Integrable (potentialOf Q) (volume.restrict (Metric.ball (0 : Space) 1)) :=
      ((pot_locInt h₁).integrableOn_isCompact (isCompact_closedBall 0 1)).mono_set Metric.ball_subset_closedBall
    have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have : NeZero (volume.restrict (Metric.ball (0 : Space) 1)) :=
      ⟨by rw [Ne, Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos volume (0 : Space) one_pos).ne'⟩
    have hmean : ⨍ z in Metric.ball (0 : Space) 1, potentialOf (-Q) z =
        -(⨍ z in Metric.ball (0 : Space) 1, potentialOf Q z) + C := by
      rw [average_congr (ae_restrict_of_ae hC)]
      have e : ⨍ z in Metric.ball (0 : Space) 1, (-potentialOf Q z + C) =
          (⨍ z in Metric.ball (0 : Space) 1, -potentialOf Q z) + ⨍ _z in Metric.ball (0 : Space) 1, C := by
        have hneg : Integrable (fun z => -potentialOf Q z) (volume.restrict (Metric.ball (0 : Space) 1)) := hint.neg
        rw [average_eq, average_eq, average_eq, integral_add hneg (integrable_const C), smul_add]
      rw [e, average_neg, average_const]
    filter_upwards [hC] with y hy
    simp only [headPotential, hy, hmean]
    ring
  · have hex' : ¬ ∃ q, IsPotentialOf (-Q) q := by
      rintro ⟨q, hq⟩
      apply hex
      refine ⟨fun y => -q y, ?_⟩
      simpa only [neg_neg] using isPotentialOf_neg hq
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [headPotential, potentialOf_of_not_exists hex, potentialOf_of_not_exists hex', sub_zero, neg_zero,
      MeasureTheory.average_zero]

theorem presMode_ae_negPot {P P' : Space → ℝ} (h : P' =ᵐ[volume] fun y => -P y) (m : ℕ) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ, presMode m n P' p.1 p.2 = -presMode m n P p.1 p.2 := by
  obtain ⟨C, hC⟩ := pres_refl m n
  refine ae_transfer (F := fun p : ℝ × ℝ => presMode m n P' p.1 p.2 = -presMode m n P p.1 p.2) ?_ (fun p hp => ?_)
  · filter_upwards [ae_circle_eq h] with p hp h0
    show presMode m n P' p.1 p.2 = -presMode m n P p.1 p.2
    rw [pres_ioo, pres_ioo, ← mul_neg, ← integral_neg]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hp h0] with θ hθ
    simp only [hθ, presKernel, Complex.ofReal_neg, mul_neg]
  · have hp' : presMode m n P' (-p.1) p.2 = -presMode m n P (-p.1) p.2 := hp
    show presMode m n P' p.1 p.2 = -presMode m n P p.1 p.2
    rw [hC P' p, hC P p, hp']
    ring

theorem headPressure_negField (L : CellLayout) {k : ℕ} (x : CellCert.Assembly.FieldTuple k) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ, headPressure L n (-x) p = (-headPressure L n x) p := by
  filter_upwards [presMode_ae_negPot (headPotential_negField x.2.2.2.2) L.order n] with p hp
  exact hp

theorem keyValue_negField (L : CellLayout) {k : ℕ} (x : CellCert.Assembly.FieldTuple k)
    (key : CellCert.CellCoordinates.SkeletonKey) : keyValue L (-x) key = -keyValue L x key := by
  cases key with
  | velocity n rad lev lo hi t a d =>
      simp only [keyValue, velMode_negField, gradModeOf_negField, moment_negField]
  | gradient n rad lev lo hi t a d =>
      simp only [keyValue, gradModeOf_negField, secondModeOf_negField, moment_negField]
      split_ifs <;> rfl
  | pressure n rad lev lo hi t d =>
      simp only [keyValue]
      rw [moment_congr_ae _ _ (headPressure_negField L x n), pressureGradMode_negField, pressureGradMode_negField,
        moment_negField]
  | corner n p a =>
      simp only [keyValue, velMode_negField, gradModeOf_negField, secondModeOf_negField, cornerMoment_negField]
  | stream p =>
      simp only [keyValue, velMode_negField, gradModeOf_negField, heightStripMoment_negField]
  | private_ =>
      simp [keyValue]

section Real

variable (L : CellLayout) {k : ℕ} (x : CellCert.Assembly.FieldTuple k)

theorem velMode_zero_conj (a : Fin 3) : (fun p => conj (L.velMode 0 x a p)) = L.velMode 0 x a := by
  have h := ConjugateDataInternal.velMode_neg L x 0 a
  rw [neg_zero] at h
  exact h.symm

theorem gradModeOf_zero_conj (a b : Fin 3) : (fun p => conj (L.gradModeOf 0 x a b p)) = L.gradModeOf 0 x a b := by
  have h := ConjugateDataInternal.gradModeOf_neg L x 0 a b
  rw [neg_zero] at h
  exact h.symm

theorem secondModeOf_zero_conj (a b c : Fin 3) :
    (fun p => conj (L.secondModeOf 0 x a b c p)) = L.secondModeOf 0 x a b c := by
  have h := ConjugateDataInternal.secondModeOf_neg L x 0 a b c
  rw [neg_zero] at h
  exact h.symm

theorem pressureGradMode_zero_conj (a : Fin 3) :
    (fun p => conj (L.pressureGradMode 0 x a p)) = L.pressureGradMode 0 x a := by
  have h := ConjugateDataInternal.pressureGradMode_neg L x 0 a
  rw [neg_zero] at h
  exact h.symm

theorem presMode_conj (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) :
    conj (presMode m n P r z) = presMode m (-n) P r z := by
  unfold presMode
  rw [ConjugateDataInternal.conj_angle]

theorem headPressure_zero_conj : (fun p => conj (headPressure L 0 x p)) = headPressure L 0 x := by
  funext p
  simp only [headPressure]
  rw [presMode_conj, neg_zero]

theorem keyValue_conj_of_modeZero (key : CellCert.CellCoordinates.SkeletonKey) (h : GaugeKey.keyMode key = some 0) :
    conj (keyValue L x key) = keyValue L x key := by
  cases key with
  | velocity n rad lev lo hi t a d =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue, ConjugateDataInternal.conj_segMoment, velMode_zero_conj, gradModeOf_zero_conj]
  | gradient n rad lev lo hi t a d =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue]
      split_ifs <;>
        simp only [ConjugateDataInternal.conj_segMoment, gradModeOf_zero_conj, secondModeOf_zero_conj]
  | pressure n rad lev lo hi t d =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue, ConjugateDataInternal.conj_segMoment, headPressure_zero_conj, pressureGradMode_zero_conj]
  | corner n p a =>
      simp only [GaugeKey.keyMode, Option.some.injEq] at h
      subst h
      simp only [keyValue, ConjugateDataInternal.conj_corner, velMode_zero_conj, gradModeOf_zero_conj,
        secondModeOf_zero_conj]
  | stream p =>
      simp only [keyValue, ConjugateDataInternal.conj_heightStrip, velMode_zero_conj, gradModeOf_zero_conj]
  | private_ =>
      simp [keyValue]

end Real

end KeyConjInternal

open KeyConjInternal in
theorem keyHarmonic_negFreq_eq_conj (L : CellCert.CellFormula.CellLayout) (ν : ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (key : CellCert.CellCoordinates.SkeletonKey) (h : GaugeKey.keyMode key = some 0) :
    keyHarmonic L (-ν) v G H Pg key = conj (keyHarmonic L ν v G H Pg key) := by
  unfold keyHarmonic
  rw [cosTuple_negFreq, sinTuple_negFreq, keyValue_negField, map_add, map_mul, Complex.conj_I,
    keyValue_conj_of_modeZero L _ key h, keyValue_conj_of_modeZero L _ key h]
  ring

namespace TreeEntry

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D}
  (T : TreeEntry D R)

theorem fieldKeyConj_holds : T.FieldKeyConjHolds :=
  fun ν v G H Pg key h => keyHarmonic_negFreq_eq_conj T.keyLayout ν v G H Pg key h

theorem fieldGaugeConj_holds (hG : T.gauge.Conditions) : T.FieldGaugeConj :=
  T.fieldGaugeConj_of hG (fieldKeyConj_holds T)

end TreeEntry

end CertCell

end Breakdown
