import Breakdown.Cert.FreePerturbation
import Breakdown.Cert.HalfOrderGraphMem
import Breakdown.Cert.TimeModulusSliceBound

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.TimeModulus

theorem slice_local_bound (R : ℝ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x k : Freq.X, IsHalfSspOf x k → ∀ j : Fin 3,
      ∫⁻ y in Metric.closedBall (0 : Space) R, ‖(partialX j x : Space → Space) y‖ₑ ^ 2 ≤
        ENNReal.ofReal M * ((∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
          ‖(velocity x : Space → Space) y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * ‖k‖ₑ +
          ∫⁻ y in Metric.closedBall (0 : Space) (R + 1), ‖(velocity x : Space → Space) y‖ₑ ^ 2) :=
  SliceBound.slice_local_bound_holds R hR

namespace GradientShift

theorem enorm_sq_le_of_norm_le {E : Type*} [NormedAddCommGroup E] {x : E} {c : ℝ} (h : ‖x‖ ≤ c) :
    ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

theorem ofReal_sq_norm_eq {E : Type*} [NormedAddCommGroup E] (a : E) :
    ENNReal.ofReal (‖a‖ ^ 2) = ‖a‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem ae_shift {p : ℝ → Prop} (h : ∀ᵐ σ : ℝ, p σ) (δ : ℝ) : ∀ᵐ σ : ℝ, p (σ + δ) :=
  (measurePreserving_add_right volume δ).quasiMeasurePreserving.ae h

theorem ae_shift_circle {p : TimeCircle → Prop} (h : ∀ᵐ t : TimeCircle, p t) (a : TimeCircle) :
    ∀ᵐ t : TimeCircle, p (t + a) :=
  (measurePreserving_add_right volume a).quasiMeasurePreserving.ae h

def shiftDiff (u : XX) (δ σ : ℝ) : XBar :=
  (u : TimeCircle → XBar) ((σ + δ : ℝ) : TimeCircle) - (u : TimeCircle → XBar) (σ : TimeCircle)

def shiftBallEnergy (v : VelField) (δ r σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖v (σ + δ) y - v σ y‖ ^ 2)

def shiftSecondNorm (u : XX) (δ σ : ℝ) : ℝ≥0∞ := ‖secondPart (shiftDiff u δ σ)‖ₑ

theorem velocity_shiftDiff_ae (u : XX) (δ σ : ℝ) :
    (velocity (gradPart (shiftDiff u δ σ)) : Space → Space) =ᵐ[volume]
      fun y => (velocity (gradPart ((u : TimeCircle → XBar) ((σ + δ : ℝ) : TimeCircle))) : Space → Space) y -
        (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y := by
  have e : velocity (gradPart (shiftDiff u δ σ)) =
      velocity (gradPart ((u : TimeCircle → XBar) ((σ + δ : ℝ) : TimeCircle))) -
        velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) :=
    (congrArg velocity (gradPart.map_sub _ _)).trans (velocity.map_sub _ _)
  exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun y =>
    congrFun (congrArg (fun w : L6R => (w : Space → Space)) e) y) (Lp.coeFn_sub _ _)

theorem partialX_shiftDiff_ae (j : Fin 3) (u : XX) (δ σ : ℝ) :
    (partialX j (gradPart (shiftDiff u δ σ)) : Space → Space) =ᵐ[volume]
      fun y => (partialX j (gradPart ((u : TimeCircle → XBar) ((σ + δ : ℝ) : TimeCircle))) : Space → Space) y -
        (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y := by
  have e : partialX j (gradPart (shiftDiff u δ σ)) =
      partialX j (gradPart ((u : TimeCircle → XBar) ((σ + δ : ℝ) : TimeCircle))) -
        partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) :=
    (congrArg (partialX j) (gradPart.map_sub _ _)).trans ((partialX j).map_sub _ _)
  exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun y =>
    congrFun (congrArg (fun w : L2R => (w : Space → Space)) e) y) (Lp.coeFn_sub _ _)

theorem slice_diff_velocity {u : XX} {v : VelField}
    (hv : ∀ᵐ σ : ℝ, v σ =ᵐ[volume] (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
    (δ : ℝ) :
    ∀ᵐ σ : ℝ, (fun y => v (σ + δ) y - v σ y) =ᵐ[volume]
        (velocity (gradPart (shiftDiff u δ σ)) : Space → Space) := by
  filter_upwards [hv, ae_shift hv δ] with σ a1 a2
  filter_upwards [a1, a2, velocity_shiftDiff_ae u δ σ] with y e1 e2 e3
  exact (congrArg₂ (fun a b : Space => a - b) e2 e1).trans e3.symm

theorem slice_diff_column {u : XX} {v : VelField} {G : GradField}
    (hv : ∀ᵐ σ : ℝ, v σ =ᵐ[volume] (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
    (hw : ∀ᵐ σ : ℝ, IsWeakGradient (v σ) (G σ)) (δ : ℝ) (j : Fin 3) :
    ∀ᵐ σ : ℝ, (fun y => gradColumn G j (σ + δ) y - gradColumn G j σ y) =ᵐ[volume]
        (partialX j (gradPart (shiftDiff u δ σ)) : Space → Space) := by
  filter_upwards [hv, ae_shift hv δ, hw, ae_shift hw δ] with σ a1 a2 b1 b2
  filter_upwards [Internal.FreePerturbation.column_ae_eq_partialX _ b1 a1 j,
    Internal.FreePerturbation.column_ae_eq_partialX _ b2 a2 j,
    partialX_shiftDiff_ae j u δ σ] with y e1 e2 e3
  exact (congrArg₂ (fun a b : Space => a - b) e2 e1).trans e3.symm

theorem shiftLp_eq (δ : ℝ) (s : HH) :
    shiftLp δ s = Lp.compMeasurePreserving (fun t : TimeCircle => t + (δ : TimeCircle))
      (measurePreserving_add_right volume (δ : TimeCircle)) s := rfl

theorem shiftLp_norm (δ : ℝ) (s : HH) : ‖shiftLp δ s‖ = ‖s‖ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (δ : TimeCircle))
    (measurePreserving_add_right volume (δ : TimeCircle))).norm_map s

theorem shift_sub_norm_le (δ : ℝ) (s : HH) : ‖shiftLp δ s - s‖ ≤ 2 * ‖s‖ := by
  calc ‖shiftLp δ s - s‖ ≤ ‖shiftLp δ s‖ + ‖s‖ := norm_sub_le _ _
    _ = 2 * ‖s‖ := by rw [shiftLp_norm]; ring

theorem shift_sub_ae (u : XX) (δ : ℝ) :
    ∀ᵐ σ : ℝ, ((shiftLp δ (secondCLM u) - secondCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle) =
      secondPart (shiftDiff u δ σ) := by
  have hsa : ∀ᵐ t : TimeCircle, (secondCLM u : TimeCircle → HBar) t = secondPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ u
  have hsh : (shiftLp δ (secondCLM u) : TimeCircle → HBar) =ᵐ[volume]
      fun t => (secondCLM u : TimeCircle → HBar) (t + (δ : TimeCircle)) :=
    Lp.coeFn_compMeasurePreserving (secondCLM u) (measurePreserving_add_right volume (δ : TimeCircle))
  have hpt : ∀ᵐ t : TimeCircle, ((shiftLp δ (secondCLM u) - secondCLM u : HH) : TimeCircle → HBar) t =
      secondPart ((u : TimeCircle → XBar) (t + (δ : TimeCircle))) - secondPart ((u : TimeCircle → XBar) t) := by
    filter_upwards [Lp.coeFn_sub (shiftLp δ (secondCLM u)) (secondCLM u), hsh, hsa,
      ae_shift_circle hsa (δ : TimeCircle)] with t e1 e2 e3 e4
    exact e1.trans (congrArg₂ (fun a b : HBar => a - b) (e2.trans e4) e3)
  filter_upwards [(ae_coe_iff _).1 hpt] with σ hσ
  have e : ((σ + δ : ℝ) : TimeCircle) = (σ : TimeCircle) + (δ : TimeCircle) := rfl
  exact hσ.trans ((congrArg (fun t => secondPart ((u : TimeCircle → XBar) t) -
    secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))) e.symm).trans (secondPart.map_sub _ _).symm)

theorem second_shift_lintegral (u : XX) (δ : ℝ) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, shiftSecondNorm u δ σ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((2 * ‖secondCLM u‖) ^ 2) := by
  have hm : AEMeasurable (fun t : TimeCircle =>
      ‖((shiftLp δ (secondCLM u) - secondCLM u : HH) : TimeCircle → HBar) t‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable _).enorm.pow_const 2
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, shiftSecondNorm u δ σ ^ (2 : ℝ)
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1,
          ‖((shiftLp δ (secondCLM u) - secondCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle)‖ₑ ^ 2 := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [shift_sub_ae u δ] with σ hσ
        rw [hσ, shiftSecondNorm, ENNReal.rpow_two]
    _ = ∫⁻ t, ‖((shiftLp δ (secondCLM u) - secondCLM u : HH) : TimeCircle → HBar) t‖ₑ ^ 2 :=
        lintegral_Icc_coe _ hm
    _ = ‖(shiftLp δ (secondCLM u) - secondCLM u : HH)‖ₑ ^ 2 :=
        Internal.FreePerturbation.lintegral_enorm_sq_Lp _
    _ ≤ _ := enorm_sq_le_of_norm_le (shift_sub_norm_le δ _)

theorem second_shift_aemeasurable (u : XX) (δ : ℝ) :
    AEMeasurable (shiftSecondNorm u δ) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have g : AEMeasurable (fun t : TimeCircle =>
      ‖((shiftLp δ (secondCLM u) - secondCLM u : HH) : TimeCircle → HBar) t‖ₑ) volume :=
    (Lp.aestronglyMeasurable _).enorm
  have hmeas : Measurable fun σ : ℝ => g.mk _ (σ : TimeCircle) :=
    g.measurable_mk.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable
  refine ⟨fun σ : ℝ => g.mk _ (σ : TimeCircle), hmeas, ae_restrict_of_ae ?_⟩
  filter_upwards [shift_sub_ae u δ, (ae_coe_iff _).1 g.ae_eq_mk] with σ h1 h2
  exact (congrArg (fun z : HBar => ‖z‖ₑ) h1.symm).trans h2

theorem velocity_diff_aemeasurable {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (δ r : ℝ) :
    AEMeasurable (shiftBallEnergy v δ r) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hmp : MeasurePreserving (fun z : ℝ × Space => (z.1 + δ, z.2)) volume volume :=
    (measurePreserving_add_right volume δ).prod (MeasurePreserving.id volume)
  have h1 : AEStronglyMeasurable (fun z : ℝ × Space => v (z.1 + δ) z.2) volume :=
    hr.measurable_velocity.comp_measurePreserving hmp
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => v (z.1 + δ) z.2 - v z.1 z.2) volume :=
    h1.sub hr.measurable_velocity
  have e : (volume : Measure ℝ).prod ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) r)) =
      ((volume : Measure ℝ).prod volume).restrict (Set.univ ×ˢ Metric.closedBall (0 : Space) r) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖v (z.1 + δ) z.2 - v z.1 z.2‖ ^ 2))
      ((volume : Measure ℝ).prod ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) r))) := by
    rw [e]
    exact (hF.restrict.norm.aemeasurable.pow_const 2).ennreal_ofReal
  exact hf.lintegral_prod_right'.restrict

theorem final_algebra {M X S : ℝ} (hM : 0 ≤ M) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    ENNReal.ofReal M * (ENNReal.ofReal X * ENNReal.ofReal (2 * S) + ENNReal.ofReal (X ^ 2)) ≤
      ENNReal.ofReal (2 * M * (X * S + X ^ 2)) := by
  rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hM]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg hM (sq_nonneg X), mul_nonneg (mul_nonneg hM hX) hS]

theorem sqrt_bound {a : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (h : a ≤ ENNReal.ofReal (c ^ 2)) :
    a ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c := by
  refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_pow hc, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem rpow_half_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a := by
  rw [← ENNReal.rpow_mul]
  norm_num

theorem pointwise_shift_bound {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {R M : ℝ} (δ : ℝ) (j : Fin 3)
    (hMb : ∀ x k : Freq.X, IsHalfSspOf x k → ∀ j : Fin 3,
      ∫⁻ y in Metric.closedBall (0 : Space) R, ‖(partialX j x : Space → Space) y‖ₑ ^ 2 ≤
        ENNReal.ofReal M * ((∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
          ‖(velocity x : Space → Space) y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * ‖k‖ₑ +
          ∫⁻ y in Metric.closedBall (0 : Space) (R + 1), ‖(velocity x : Space → Space) y‖ₑ ^ 2)) :
    ∀ᵐ σ : ℝ, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖gradColumn G j (σ + δ) y - gradColumn G j σ y‖ ^ 2) ≤
        ENNReal.ofReal M * (shiftBallEnergy v δ (R + 1) σ ^ (1 / 2 : ℝ) * shiftSecondNorm u δ σ +
          shiftBallEnergy v δ (R + 1) σ) := by
  filter_upwards [slice_diff_velocity hr.velocity_eq δ,
    slice_diff_column hr.velocity_eq hr.weak_gradient δ j] with σ h1 h2
  have eY : shiftBallEnergy v δ (R + 1) σ = ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
      ‖(velocity (gradPart (shiftDiff u δ σ)) : Space → Space) y‖ₑ ^ 2 := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h1] with y hy
    exact (congrArg (fun w : Space => ENNReal.ofReal (‖w‖ ^ 2)) hy).trans (ofReal_sq_norm_eq _)
  have eA : ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖gradColumn G j (σ + δ) y - gradColumn G j σ y‖ ^ 2) =
      ∫⁻ y in Metric.closedBall (0 : Space) R,
        ‖(partialX j (gradPart (shiftDiff u δ σ)) : Space → Space) y‖ₑ ^ 2 := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h2] with y hy
    exact (congrArg (fun w : Space => ENNReal.ofReal (‖w‖ ^ 2)) hy).trans (ofReal_sq_norm_eq _)
  refine eA.trans_le ((hMb _ _ (halfSsp_of_xbar (shiftDiff u δ σ)) j).trans_eq ?_)
  exact congrArg (fun Z => ENNReal.ofReal M * (Z ^ (1 / 2 : ℝ) * ‖secondPart (shiftDiff u δ σ)‖ₑ + Z)) eY.symm

theorem integrated_bound {A Y K : ℝ → ℝ≥0∞} {M X S : ℝ} (hM : 0 ≤ M) (hX : 0 ≤ X) (hS : 0 ≤ S)
    (hYm : AEMeasurable Y (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hKm : AEMeasurable K (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hpt : ∀ᵐ σ : ℝ, A σ ≤ ENNReal.ofReal M * (Y σ ^ (1 / 2 : ℝ) * K σ + Y σ))
    (hY : ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ ≤ ENNReal.ofReal (X ^ 2))
    (hK : ∫⁻ σ in Set.Icc (0 : ℝ) 1, K σ ^ (2 : ℝ) ≤ ENNReal.ofReal ((2 * S) ^ 2)) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, A σ ≤ ENNReal.ofReal (2 * M * (X * S + X ^ 2)) := by
  have hCst := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) 1))
    Real.HolderConjugate.two_two (hYm.pow_const (1 / 2 : ℝ)) hKm
  have hYY : ∫⁻ σ in Set.Icc (0 : ℝ) 1, (Y σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ :=
    lintegral_congr fun σ => rpow_half_sq (Y σ)
  have hprod : ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ ^ (1 / 2 : ℝ) * K σ ≤
      ENNReal.ofReal X * ENNReal.ofReal (2 * S) := by
    refine hCst.trans ?_
    rw [hYY]
    have h1 := sqrt_bound hX hY
    have h2 := sqrt_bound (by positivity) hK
    norm_num at h1 h2 ⊢
    exact mul_le_mul' h1 h2
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, A σ
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal M * (Y σ ^ (1 / 2 : ℝ) * K σ + Y σ) :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ENNReal.ofReal M * ((∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ ^ (1 / 2 : ℝ) * K σ) +
          ∫⁻ σ in Set.Icc (0 : ℝ) 1, Y σ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right' _ hYm]
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal X * ENNReal.ofReal (2 * S) + ENNReal.ofReal (X ^ 2)) :=
        mul_le_mul' le_rfl (add_le_add hprod hY)
    _ ≤ _ := final_algebra hM hX hS

end GradientShift

open GradientShift in
theorem gradient_shift_bound (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : XX) (v : VelField) (G : GradField) (H : SecondField),
      IsReadingOf u v G H → ∀ (δ X : ℝ) (j : Fin 3), 0 ≤ X →
        periodBallLIntegral (R + 1) (fun σ y => ‖v (σ + δ) y - v σ y‖ ^ 2) ≤ ENNReal.ofReal (X ^ 2) →
        periodBallLIntegral R (fun σ y => ‖gradColumn G j (σ + δ) y - gradColumn G j σ y‖ ^ 2) ≤
          ENNReal.ofReal (C * (X * ‖secondCLM u‖ + X ^ 2)) := by
  choose M hM hMb using slice_local_bound R hR
  refine ⟨2 * M, by positivity, fun u v G H hr δ X j hX hY => ?_⟩
  exact integrated_bound hM hX (norm_nonneg _) (velocity_diff_aemeasurable hr δ (R + 1))
    (second_shift_aemeasurable u δ) (pointwise_shift_bound hr δ j hMb) hY (second_shift_lintegral u δ)

end Internal.TimeModulus

end Breakdown.Cert
