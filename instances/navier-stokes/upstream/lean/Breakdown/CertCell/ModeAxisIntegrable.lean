import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.CertCell.PatchModeWeak
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoercivePairingSplit

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SideTrace

namespace Internal.AxisWeighted

open CellCert.CellAnalysis (cylPoint)
open Bridge.Internal.PatchModeWeak (orbitMode aesm_orbitMode enorm_orbitMode_le lintegral_period_shift cyl_period
  prod_restrict_right slab_lintegral_lt_top rot_plane)
open CellCert.CellFormula.Internal.RelTrace (region cylF lintegral_cyl qmp_region)

def timePhase (k : ℤ) (τ : ℝ) : ℂ := Complex.exp (-(((2 * Real.pi * k * τ : ℝ) : ℂ) * Complex.I))

def velEval (n : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) : ℂ :=
  Complex.exp (-(((n * θ : ℝ) : ℂ) * Complex.I)) * ((axialRot (-θ) u a : ℝ) : ℂ)

def gradEval (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-(((n * θ : ℝ) : ℂ) * Complex.I)) * ((axialRot (-θ) (M (axialRot θ (unitVector b))) a : ℝ) : ℂ)

def slopeEval (n : ℤ) (a j l : Fin 3) (θ : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-(((n * θ : ℝ) : ℂ) * Complex.I)) *
    ((axialRot (-θ) (B (axialRot θ (unitVector j)) (axialRot θ (unitVector l))) a : ℝ) : ℂ)

theorem phase_norm_one (t : ℝ) : ‖Complex.exp (-((t : ℂ) * Complex.I))‖ = 1 := by
  rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem timePhase_cont (k : ℤ) : Continuous (timePhase k) := by
  unfold timePhase
  fun_prop

theorem enorm_timePhase (k : ℤ) (τ : ℝ) : ‖timePhase k τ‖ₑ = 1 := by
  rw [← ofReal_norm, timePhase, phase_norm_one, ENNReal.ofReal_one]

theorem rot_unit_norm (θ : ℝ) (b : Fin 3) : ‖axialRot θ (unitVector b)‖ = 1 := by
  rw [Coercive.RotationInternal.axialRot_norm, Coercive.Internal.PerturbationFacts.norm_unitVector_eq]

theorem rot_comp_le (θ : ℝ) (w : Space) (a : Fin 3) : ‖(((axialRot θ w a : ℝ)) : ℂ)‖ ≤ ‖w‖ := by
  rw [Complex.norm_real, ← Coercive.RotationInternal.axialRot_norm θ w]
  exact PiLp.norm_apply_le _ a

theorem velEval_le (n : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) : ‖velEval n a θ u‖ ≤ ‖u‖ := by
  rw [velEval, norm_mul, phase_norm_one, one_mul]
  exact rot_comp_le _ _ _

theorem gradEval_le (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) : ‖gradEval n a b θ M‖ ≤ ‖M‖ := by
  rw [gradEval, norm_mul, phase_norm_one, one_mul]
  refine (rot_comp_le _ _ _).trans ?_
  calc ‖M (axialRot θ (unitVector b))‖ ≤ ‖M‖ * ‖axialRot θ (unitVector b)‖ := M.le_opNorm _
    _ = ‖M‖ := by rw [rot_unit_norm, mul_one]

theorem slopeEval_le (n : ℤ) (a j l : Fin 3) (θ : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖slopeEval n a j l θ B‖ ≤ ‖B‖ := by
  rw [slopeEval, norm_mul, phase_norm_one, one_mul]
  refine (rot_comp_le _ _ _).trans ?_
  calc ‖B (axialRot θ (unitVector j)) (axialRot θ (unitVector l))‖
      ≤ ‖B‖ * ‖axialRot θ (unitVector j)‖ * ‖axialRot θ (unitVector l)‖ := B.le_opNorm₂ _ _
    _ = ‖B‖ := by rw [rot_unit_norm, rot_unit_norm, mul_one, mul_one]

theorem phase_pair_cont (n : ℤ) :
    Continuous (fun θ : ℝ => Complex.exp (-(((n * θ : ℝ) : ℂ) * Complex.I))) := by
  fun_prop

theorem velEval_cont (n : ℤ) (a : Fin 3) : Continuous (fun q : ℝ × Space => velEval n a q.1 q.2) := by
  unfold velEval
  exact ((phase_pair_cont n).comp continuous_fst).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp
      (Coercive.PairingSplitInternal.continuous_axialRot continuous_fst.neg continuous_snd)))

theorem gradEval_cont (n : ℤ) (a b : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space) => gradEval n a b q.1 q.2) := by
  unfold gradEval
  exact ((phase_pair_cont n).comp continuous_fst).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp
      (Coercive.PairingSplitInternal.continuous_axialRot continuous_fst.neg
        (continuous_snd.clm_apply
          (Coercive.PairingSplitInternal.continuous_axialRot continuous_fst continuous_const)))))

theorem slopeEval_cont (n : ℤ) (a j l : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => slopeEval n a j l q.1 q.2) := by
  unfold slopeEval
  exact ((phase_pair_cont n).comp continuous_fst).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp
      (Coercive.PairingSplitInternal.continuous_axialRot continuous_fst.neg
        ((continuous_snd.clm_apply
          (Coercive.PairingSplitInternal.continuous_axialRot continuous_fst continuous_const)).clm_apply
          (Coercive.PairingSplitInternal.continuous_axialRot continuous_fst continuous_const)))))

theorem strip_orbit_le {h : Space → ℝ≥0∞} (hh : AEMeasurable h volume) (hi zlo zhi : ℝ) :
    ∫⁻ p in Icc (0 : ℝ) hi ×ˢ Icc zlo zhi,
        ENNReal.ofReal p.1 * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), h (cylPoint p.1 θ p.2)
      ≤ ∫⁻ y in Metric.closedBall (0 : Space) (2 * |hi| + (|zlo| + |zhi|)), h y := by
  set H : Space → ℝ≥0∞ := (Metric.closedBall (0 : Space) (2 * |hi| + (|zlo| + |zhi|))).indicator h with hH
  set J : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * H (cylPoint p.1 θ p.2) with hJ
  have step : ∀ p ∈ Icc (0 : ℝ) hi ×ˢ Icc zlo zhi,
      ENNReal.ofReal p.1 * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), h (cylPoint p.1 θ p.2)
        ≤ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator J p := by
    intro p hp
    rcases eq_or_lt_of_le hp.1.1 with h0 | h0
    · rw [← h0, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
    · rw [indicator_of_mem (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨h0, mem_univ _⟩), hJ]
      rw [lintegral_period_shift (fun θ => h (cylPoint p.1 θ p.2)) (fun θ => by simp only [cyl_period]),
        setLIntegral_congr Ioo_ae_eq_Ioc.symm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun θ => ?_
      have hz : |p.2| ≤ |zlo| + |zhi| :=
        abs_le.2 ⟨by linarith [neg_abs_le zlo, abs_nonneg zhi, hp.2.1],
          by linarith [le_abs_self zhi, abs_nonneg zlo, hp.2.2]⟩
      have hr : |p.1| ≤ |hi| := by
        rw [abs_of_pos h0]
        exact hp.1.2.trans (le_abs_self hi)
      have hmem : cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) (2 * |hi| + (|zlo| + |zhi|)) :=
        CellCert.CellEnergy.Internal.CircleWeak.cyl_mem (by linarith)
      rw [hH, indicator_of_mem hmem]
  have hS : MeasurableSet (Icc (0 : ℝ) hi ×ˢ Icc zlo zhi) := measurableSet_Icc.prod measurableSet_Icc
  calc ∫⁻ p in Icc (0 : ℝ) hi ×ˢ Icc zlo zhi,
        ENNReal.ofReal p.1 * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), h (cylPoint p.1 θ p.2)
      ≤ ∫⁻ p in Icc (0 : ℝ) hi ×ˢ Icc zlo zhi, (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator J p :=
        setLIntegral_mono' hS step
    _ ≤ ∫⁻ p, (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator J p := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), J p :=
        lintegral_indicator (measurableSet_Ioi.prod MeasurableSet.univ) _
    _ ≤ ∫⁻ x in region, ENNReal.ofReal x.1.1 * H (cylF x) := by
        have e : volume.restrict region =
            (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
          rw [Measure.prod_restrict]
          rfl
        have hm : AEMeasurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * H (cylF x))
            (volume.restrict region) :=
          (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
            ((hh.indicator Metric.isClosed_closedBall.measurableSet).comp_quasiMeasurePreserving qmp_region)
        rw [e] at hm ⊢
        rw [lintegral_prod _ hm]
        exact le_rfl
    _ = ∫⁻ y, H y := lintegral_cyl H
    _ = ∫⁻ y in Metric.closedBall (0 : Space) (2 * |hi| + (|zlo| + |zhi|)), h y :=
        lintegral_indicator Metric.isClosed_closedBall.measurableSet _

theorem weighted_orbit_integrable {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hXl : LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) (k : ℤ) (hi zlo zhi : ℝ) :
    Integrable (fun x : (ℝ × ℝ) × ℝ =>
        (Icc (0 : ℝ) hi ×ˢ Icc zlo zhi).indicator (fun p : ℝ × ℝ => (p.1 : ℂ)) x.1
          * (timePhase k x.2 * orbitMode X R x))
      ((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) hi ×ˢ Icc zlo zhi with hSdef
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  refine ⟨?_, ?_⟩
  · rw [prod_restrict_right]
    refine AEStronglyMeasurable.restrict ?_
    have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => S.indicator (fun p : ℝ × ℝ => (p.1 : ℂ)) p) volume :=
      ((Complex.measurable_ofReal.comp measurable_fst).indicator hS).aestronglyMeasurable
    exact (hw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (((timePhase_cont k).comp continuous_snd).aestronglyMeasurable.mul (aesm_orbitMode hXm hR))
  rw [hasFiniteIntegral_iff_enorm]
  set B : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun x => S.indicator (fun p : ℝ × ℝ =>
    ENNReal.ofReal p.1 * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖X x.2 (cylPoint p.1 θ p.2)‖ₑ) x.1 with hB
  have hpt : ∀ x : (ℝ × ℝ) × ℝ,
      ‖S.indicator (fun p : ℝ × ℝ => (p.1 : ℂ)) x.1 * (timePhase k x.2 * orbitMode X R x)‖ₑ ≤ B x := by
    intro x
    by_cases hx : x.1 ∈ S
    · simp only [hB, indicator_of_mem hx]
      have e1 : ‖(x.1.1 : ℂ)‖ₑ = ENNReal.ofReal x.1.1 := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx.1.1]
      rw [enorm_mul, enorm_mul, e1, enorm_timePhase, one_mul]
      exact mul_le_mul' le_rfl (enorm_orbitMode_le X hRb x)
    · simp only [hB, indicator_of_notMem hx, zero_mul, enorm_zero]
      exact le_rfl
  have hslice : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) 1)), AEMeasurable (fun y => ‖X τ y‖ₑ) volume := by
    have h := hXm.prodMk_left
    exact ae_restrict_of_ae (h.mono fun τ hτ => hτ.enorm)
  calc ∫⁻ x, ‖S.indicator (fun p : ℝ × ℝ => (p.1 : ℂ)) x.1 * (timePhase k x.2 * orbitMode X R x)‖ₑ
        ∂((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1)))
      ≤ ∫⁻ x, B x ∂((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := lintegral_mono hpt
    _ = ∫⁻ x, B x.swap ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure (ℝ × ℝ))) :=
        (lintegral_prod_swap B).symm
    _ ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ p, B (p, τ) := lintegral_prod_le _
    _ ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) (2 * |hi| + (|zlo| + |zhi|)), ‖X τ y‖ₑ := by
        refine lintegral_mono_ae (hslice.mono fun τ hτ => ?_)
        simp only [hB]
        rw [lintegral_indicator hS]
        exact strip_orbit_le hτ hi zlo zhi
    _ < ⊤ := slab_lintegral_lt_top hXm hXl _

theorem weighted_mode_integrableOn {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hXl : LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) (k : ℤ) (hi zlo zhi : ℝ)
    (M : ℝ × ℝ → ℂ)
    (hM : ∀ p, M p = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, timePhase k τ * orbitMode X R (p, τ)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * M p) (Icc (0 : ℝ) hi ×ˢ Icc zlo zhi) := by
  have hS : MeasurableSet (Icc (0 : ℝ) hi ×ˢ Icc zlo zhi) := measurableSet_Icc.prod measurableSet_Icc
  have hK := (weighted_orbit_integrable hXm hXl hR hRb k hi zlo zhi).integral_prod_left
  rw [← integrable_indicator_iff hS]
  refine (hK.const_mul (1 / (2 * Real.pi) : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only
  by_cases hp : p ∈ Icc (0 : ℝ) hi ×ˢ Icc zlo zhi
  · rw [indicator_of_mem hp, indicator_of_mem hp, hM, integral_const_mul,
      intervalIntegral.integral_of_le zero_le_one]
    ring
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]
    simp

theorem vel_orbit (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    planeVelocity ξ v a p = (1 / (2 * Real.pi) : ℂ) *
      ∫ τ in (0 : ℝ)..1, timePhase ξ.1 τ * orbitMode v (velEval ξ.2 a) (p, τ) := by
  simp only [planeVelocity, modeVel, modeAverage, orbitMode, velEval]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [zero_add, rot_plane, timePhase]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem grad_orbit (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    planeGrad ξ G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ τ in (0 : ℝ)..1, timePhase ξ.1 τ * orbitMode G (gradEval ξ.2 a b) (p, τ) := by
  simp only [planeGrad, modeGrad, modeAverage, orbitMode, gradEval]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [zero_add, rot_plane, timePhase]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem slope_orbit (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) (p : ℝ × ℝ) :
    planeSlope ξ H a b c p = (1 / (2 * Real.pi) : ℂ) *
      ∫ τ in (0 : ℝ)..1, timePhase ξ.1 τ * orbitMode H (slopeEval ξ.2 a c b) (p, τ) := by
  simp only [planeSlope, modeSecondDeriv, modeAverage, orbitMode, slopeEval]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [zero_add, rot_plane, timePhase]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Internal.AxisWeighted

open Internal.AxisWeighted in
theorem modeAxisIntegrable (hE : Bridge.HessianEnergyIdentityHolds) : ModeAxisIntegrableHolds := by
  intro Γ P v G H g hv ξ a b c hi zlo zhi _ _
  refine ⟨?_, ?_, ?_⟩
  · exact weighted_mode_integrableOn hv.measurable_velocity
      (Coercive.Internal.PerturbationFacts.velocity_locallyIntegrable hv) (velEval_cont ξ.2 a)
      (velEval_le ξ.2 a) ξ.1 hi zlo zhi (planeVelocity ξ v a) (vel_orbit ξ v a)
  · exact weighted_mode_integrableOn hv.measurable_gradient
      (Coercive.Internal.PerturbationFacts.gradient_locallyIntegrable hv) (gradEval_cont ξ.2 a b)
      (gradEval_le ξ.2 a b) ξ.1 hi zlo zhi (planeGrad ξ G a b) (grad_orbit ξ G a b)
  · exact weighted_mode_integrableOn hv.measurable_secondDeriv
      (Coercive.Internal.PerturbationFacts.secondDeriv_locallyIntegrable hv) (slopeEval_cont ξ.2 a c b)
      (slopeEval_le ξ.2 a c b) ξ.1 hi zlo zhi (planeSlope ξ H a b c) (slope_orbit ξ H a b c)

end Breakdown.CertCell.SideTrace
