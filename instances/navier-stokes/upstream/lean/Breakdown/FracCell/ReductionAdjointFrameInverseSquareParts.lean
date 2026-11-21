import Breakdown.FracCell.StWeightedInverseSquare
import Breakdown.FracCell.ReductionAdjointFrameMirrorLeaves

open scoped ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace FracInternal

namespace FrameInverseSquareParts

open SteadyCert CellCert.Reduction FrameMirrorLeaves

def modeWeightedSide (v : Space → Space) (k : ℤ) : ENNReal :=
  ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
    ENNReal.ofReal (2 * Real.pi * q.1 *
      ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart v) k q.1 q.2‖ ^ 2
        + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart v) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))

def modeGradientSide (G : Space → (Space →L[ℝ] Space)) (k : ℤ) : ENNReal :=
  ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 * frameModeSq G k q.1 q.2)

def SmoothModeBoundStatement : Prop :=
  ∀ u : Space → Space, ContDiff ℝ ∞ u → HasCompactSupport u → (∀ y, u (mirror y) = mirror (u y)) →
    ∀ k : ℤ, modeWeightedSide u k ≤ modeGradientSide (fun y => fderiv ℝ u y) k

def MirrorApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
    ∃ u : ℕ → Space → Space,
      (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n) ∧ ∀ y, u n (mirror y) = mirror (u n y)) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (u n) y - G y))) atTop (𝓝 0) ∧
      ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖u n y - v y‖ ^ 2)) atTop (𝓝 0)

def ModeWeightedLowerStatement : Prop :=
  ∀ (v : Space → Space) (u : ℕ → Space → Space), AEStronglyMeasurable v volume → (∀ n, Continuous (u n)) →
    (∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖u n y - v y‖ ^ 2)) atTop (𝓝 0)) →
    ∀ k : ℤ, modeWeightedSide v k ≤ liminf (fun n => modeWeightedSide (u n) k) atTop

def ModeGradientLimitStatement : Prop :=
  ∀ (G : Space → (Space →L[ℝ] Space)) (Gn : ℕ → Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable G volume → (∀ n, AEStronglyMeasurable (Gn n) volume) →
    Integrable (fun y => entrySq (G y)) →
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (Gn n y - G y))) atTop (𝓝 0) →
    ∀ k : ℤ, Tendsto (fun n => modeGradientSide (Gn n) k) atTop (𝓝 (modeGradientSide G k))


def FrameModeCalculusStatement : Prop :=
  ∀ u : Space → Space, ContDiff ℝ ∞ u → HasCompactSupport u → ∀ k : ℤ,
    (ContDiff ℝ 1 (fun p : ℝ × ℝ => angularMode (horizontalPart u) k p.1 p.2) ∧
      HasCompactSupport (fun p : ℝ × ℝ => angularMode (horizontalPart u) k p.1 p.2)) ∧
    (ContDiff ℝ 1 (fun p : ℝ × ℝ => angularMode (verticalPart u) k p.1 p.2) ∧
      HasCompactSupport (fun p : ℝ × ℝ => angularMode (verticalPart u) k p.1 p.2)) ∧
    ∀ ρ z : ℝ, 0 < ρ →
      frameModeSq (fun y => fderiv ℝ u y) k ρ z =
        ‖fderiv ℝ (fun p : ℝ × ℝ => angularMode (horizontalPart u) k p.1 p.2) (ρ, z) (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun p : ℝ × ℝ => angularMode (horizontalPart u) k p.1 p.2) (ρ, z) (0, 1)‖ ^ 2 +
          (k : ℝ) ^ 2 * ‖angularMode (horizontalPart u) k ρ z‖ ^ 2 / ρ ^ 2 +
        (‖fderiv ℝ (fun p : ℝ × ℝ => angularMode (verticalPart u) k p.1 p.2) (ρ, z) (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun p : ℝ × ℝ => angularMode (verticalPart u) k p.1 p.2) (ρ, z) (0, 1)‖ ^ 2 +
          (k : ℝ) ^ 2 * ‖angularMode (verticalPart u) k ρ z‖ ^ 2 / ρ ^ 2)

def HalfPlaneBoundStatement : Prop :=
  ∀ (a : ℝ × ℝ → ℂ) (k : ℤ) (s : ℝ), ContDiff ℝ 1 a → HasCompactSupport a →
    (s = ((|k| : ℤ) : ℝ) + 1 / 2 ∨ (s = ((|k| : ℤ) : ℝ) + 3 / 2 ∧ ∀ p : ℝ × ℝ, a (p.1, -p.2) = -a p)) →
    ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 * (s ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) ≤
      ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
        (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2))

theorem verticalMode_odd (u : Space → Space) (hmir : ∀ y, u (mirror y) = mirror (u y)) (k : ℤ) (p : ℝ × ℝ) :
    angularMode (verticalPart u) k p.1 (-p.2) = -angularMode (verticalPart u) k p.1 p.2 := by
  have e : ∀ θ : ℝ, (u (ringPoint p.1 θ (-p.2)) 2 : ℂ) = -(u (ringPoint p.1 θ p.2) 2 : ℂ) := by
    intro θ
    have hm : ringPoint p.1 θ (-p.2) = mirror (ringPoint p.1 θ p.2) := by
      ext i
      fin_cases i <;> simp [ringPoint, mirror]
    rw [hm, hmir]
    simp [mirror]
  unfold angularMode verticalPart
  simp_rw [e, mul_neg, intervalIntegral.integral_neg, mul_neg]

theorem smoothModeBound_of (hC : FrameModeCalculusStatement) (hH : HalfPlaneBoundStatement) :
    SmoothModeBoundStatement := by
  intro u hu hs hmir k
  obtain ⟨⟨hac, has⟩, ⟨hbc, hbs⟩, hfr⟩ := hC u hu hs k
  have hodd := verticalMode_odd u hmir k
  set a : ℝ × ℝ → ℂ := fun p => angularMode (horizontalPart u) k p.1 p.2 with ha
  set b : ℝ × ℝ → ℂ := fun p => angularMode (verticalPart u) k p.1 p.2 with hb
  have h1 := hH a k _ hac has (Or.inl rfl)
  have h2 := hH b k _ hbc hbs (Or.inr ⟨rfl, fun p => hodd p⟩)
  have hS : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hacm := hac.continuous.measurable
  have hbcm := hbc.continuous.measurable
  have hdac : Continuous (fun q => fderiv ℝ a q) := hac.continuous_fderiv one_ne_zero
  have hdbc : Continuous (fun q => fderiv ℝ b q) := hbc.continuous_fderiv one_ne_zero
  have mA : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (2 * Real.pi * q.1 *
      ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))) := by
    refine Measurable.ennreal_ofReal ?_
    exact ((measurable_const.mul measurable_fst).mul (measurable_const.mul (hacm.norm.pow_const 2))).div
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
  have mR : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (2 * Real.pi * q.1 *
      (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2))) := by
    refine Measurable.ennreal_ofReal ?_
    have e1 : Continuous (fun q => fderiv ℝ a q (1, 0)) := hdac.clm_apply continuous_const
    have e2 : Continuous (fun q => fderiv ℝ a q (0, 1)) := hdac.clm_apply continuous_const
    exact (measurable_const.mul measurable_fst).mul
      (((e1.measurable.norm.pow_const 2).add (e2.measurable.norm.pow_const 2)).add
        ((measurable_const.mul (hacm.norm.pow_const 2)).div (measurable_fst.pow_const 2)))
  unfold modeWeightedSide modeGradientSide
  calc ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
        ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖angularMode (horizontalPart u) k q.1 q.2‖ ^ 2
          + (((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖angularMode (verticalPart u) k q.1 q.2‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))
      ≤ ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), (ENNReal.ofReal (2 * Real.pi * q.1 *
          ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) +
          ENNReal.ofReal (2 * Real.pi * q.1 *
          ((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖b q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))) := by
        refine lintegral_mono fun q => ?_
        refine le_trans (le_of_eq ?_) ENNReal.ofReal_add_le
        congr 1
        simp only [ha, hb]
        ring
    _ = (∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
          ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2))) +
        ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
          ((((|k| : ℤ) : ℝ) + 3 / 2) ^ 2 * ‖b q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) :=
        lintegral_add_left mA _
    _ ≤ (∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
          (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2))) +
        ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
          (‖fderiv ℝ b q (1, 0)‖ ^ 2 + ‖fderiv ℝ b q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖b q‖ ^ 2 / q.1 ^ 2)) :=
        add_le_add h1 h2
    _ = ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), (ENNReal.ofReal (2 * Real.pi * q.1 *
          (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2)) +
        ENNReal.ofReal (2 * Real.pi * q.1 *
          (‖fderiv ℝ b q (1, 0)‖ ^ 2 + ‖fderiv ℝ b q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖b q‖ ^ 2 / q.1 ^ 2))) :=
        (lintegral_add_left mR _).symm
    _ ≤ _ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS] with q hq
        have hρ : 0 < q.1 := hq.1
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        rw [hfr q.1 q.2 hρ]
        simp only [ha, hb]
        ring


private def axisA : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

private def axisB : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))

private def axisC : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))

private def ringLin (θ : ℝ) : ℝ × ℝ →L[ℝ] Space := Real.cos θ • axisA + Real.sin θ • axisB + axisC

private theorem ringLin_apply (θ : ℝ) (p : ℝ × ℝ) : ringLin θ p = ringPoint p.1 θ p.2 := by
  ext i
  fin_cases i <;> simp [ringLin, axisA, axisB, axisC, ringPoint] <;> ring

private theorem ringLin_cont : Continuous ringLin := by
  unfold ringLin
  fun_prop

private theorem ringLin_norm_le (θ : ℝ) : ‖ringLin θ‖ ≤ ‖axisA‖ + ‖axisB‖ + ‖axisC‖ := by
  unfold ringLin
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) le_rfl)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)

private theorem ringLin_norm_sq (θ : ℝ) (p : ℝ × ℝ) : ‖ringLin θ p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [ringLin_apply, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [ringPoint, Real.norm_eq_abs, sq_abs]
  simp only [mul_pow, sq_abs]
  linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq θ

private theorem norm_le_ringLin (θ : ℝ) (p : ℝ × ℝ) : ‖p‖ ≤ ‖ringLin θ p‖ := by
  have hn : ‖ringLin θ p‖ = Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
    rw [← ringLin_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hn, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (Real.abs_le_sqrt (by nlinarith [sq_nonneg p.2])) (Real.abs_le_sqrt (by nlinarith [sq_nonneg p.1]))

private def wave (k : ℤ) (θ : ℝ) : ℂ := Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))

private theorem wave_cont (k : ℤ) : Continuous (wave k) := by
  unfold wave
  fun_prop

private theorem wave_norm (k : ℤ) (θ : ℝ) : ‖wave k θ‖ = 1 := by
  unfold wave
  rw [show -((k : ℂ) * (θ : ℂ) * Complex.I) = ((-((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private def modeInt (h : Space → ℂ) (k : ℤ) (p : ℝ × ℝ) : ℂ :=
  ∫ θ in (-Real.pi)..Real.pi, wave k θ * h (ringLin θ p)

private theorem angularMode_eq (h : Space → ℂ) (k : ℤ) (p : ℝ × ℝ) :
    angularMode h k p.1 p.2 = (1 / (2 * Real.pi) : ℂ) * modeInt h k p := by
  simp only [angularMode, modeInt, wave, ringLin_apply]

private def modeDer (h : Space → ℂ) (k : ℤ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  ∫ θ in (-Real.pi)..Real.pi, wave k θ • (fderiv ℝ h (ringLin θ p)).comp (ringLin θ)

private theorem modeDer_cont {h : Space → ℂ} (hc : ContDiff ℝ 1 h) (k : ℤ) : Continuous (modeDer h k) := by
  have hdc : Continuous (fderiv ℝ h) := hc.continuous_fderiv one_ne_zero
  unfold modeDer
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  show Continuous (fun q : (ℝ × ℝ) × ℝ => wave k q.2 • (fderiv ℝ h (ringLin q.2 q.1)).comp (ringLin q.2))
  exact ((wave_cont k).comp continuous_snd).smul
    ((hdc.comp ((ringLin_cont.comp continuous_snd).clm_apply continuous_fst)).clm_comp
      (ringLin_cont.comp continuous_snd))

private theorem modeInt_hasFDerivAt {h : Space → ℂ} (hc : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (k : ℤ)
    (p : ℝ × ℝ) : HasFDerivAt (modeInt h k) (modeDer h k p) p := by
  have hdc : Continuous (fderiv ℝ h) := hc.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hs.fderiv (𝕜 := ℝ))
  have hhc : Continuous h := hc.continuous
  have hF : ∀ x : ℝ × ℝ, Continuous (fun θ => wave k θ * h (ringLin θ x)) := fun x =>
    (wave_cont k).mul (hhc.comp (ringLin_cont.clm_apply continuous_const))
  have hF' : ∀ x : ℝ × ℝ, Continuous (fun θ => wave k θ • (fderiv ℝ h (ringLin θ x)).comp (ringLin θ)) :=
    fun x => (wave_cont k).smul ((hdc.comp (ringLin_cont.clm_apply continuous_const)).clm_comp ringLin_cont)
  unfold modeInt modeDer
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (F := fun x θ => wave k θ * h (ringLin θ x))
    (F' := fun x θ => wave k θ • (fderiv ℝ h (ringLin θ x)).comp (ringLin θ))
    (bound := fun _ => C * (‖axisA‖ + ‖axisB‖ + ‖axisC‖)) Filter.univ_mem
    (Eventually.of_forall fun x => (hF x).aestronglyMeasurable) ((hF p).intervalIntegrable _ _)
    (hF' p).aestronglyMeasurable (ae_of_all _ fun θ _ x _ => ?_) intervalIntegrable_const
    (ae_of_all _ fun θ _ x _ => ?_)
  · rw [norm_smul, wave_norm, one_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hC _) (ringLin_norm_le θ) (norm_nonneg _) ((norm_nonneg _).trans (hC 0)))
  · have hd : HasFDerivAt h (fderiv ℝ h (ringLin θ x)) (ringLin θ x) :=
      (hc.differentiable one_ne_zero (ringLin θ x)).hasFDerivAt
    exact (hd.comp x (ringLin θ).hasFDerivAt).const_mul (wave k θ)

private theorem mode_eq_fun (h : Space → ℂ) (k : ℤ) :
    (fun p : ℝ × ℝ => angularMode h k p.1 p.2) = fun p => (1 / (2 * Real.pi) : ℂ) * modeInt h k p :=
  funext fun p => angularMode_eq h k p

private theorem mode_hasFDerivAt {h : Space → ℂ} (hc : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (k : ℤ)
    (p : ℝ × ℝ) : HasFDerivAt (fun p : ℝ × ℝ => angularMode h k p.1 p.2)
      ((1 / (2 * Real.pi) : ℂ) • modeDer h k p) p := by
  rw [mode_eq_fun]
  exact (modeInt_hasFDerivAt hc hs k p).const_mul _

private theorem mode_contDiff {h : Space → ℂ} (hc : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (k : ℤ) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => angularMode h k p.1 p.2) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun p => (mode_hasFDerivAt hc hs k p).differentiableAt, ?_⟩
  have e : fderiv ℝ (fun p : ℝ × ℝ => angularMode h k p.1 p.2) =
      fun p => (1 / (2 * Real.pi) : ℂ) • modeDer h k p :=
    funext fun p => (mode_hasFDerivAt hc hs k p).fderiv
  rw [e]
  exact (modeDer_cont hc k).const_smul (1 / (2 * Real.pi) : ℂ)

private theorem mode_compact {h : Space → ℂ} (hs : HasCompactSupport h) (k : ℤ) :
    HasCompactSupport (fun p : ℝ × ℝ => angularMode h k p.1 p.2) := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) R) fun p hp => ?_
  have hp' : R < ‖p‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hp
  have hz : (fun θ => wave k θ * h (ringLin θ p)) = fun _ => 0 := by
    funext θ
    have hn : ringLin θ p ∉ tsupport h := by
      intro hm
      have := hR hm
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd (lt_of_lt_of_le hp' (norm_le_ringLin θ p)) (not_lt.2 this)
    rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  show angularMode h k p.1 p.2 = 0
  rw [angularMode_eq, modeInt, hz]
  simp


private theorem angularMode_eq' (h : Space → ℂ) (k : ℤ) (ρ z : ℝ) :
    angularMode h k ρ z = (1 / (2 * Real.pi) : ℂ) * modeInt h k (ρ, z) :=
  angularMode_eq h k (ρ, z)

private theorem fderiv_clm_comp {u : Space → Space} (hu : ContDiff ℝ ∞ u) (Λ : Space →L[ℝ] ℂ) (y : Space) :
    fderiv ℝ (fun x => Λ (u x)) y = Λ.comp (fderiv ℝ u y) :=
  (Λ.hasFDerivAt.comp y ((hu.differentiable (by simp)) y).hasFDerivAt).fderiv

private theorem ringRadius_ring {ρ : ℝ} (hρ : 0 < ρ) (θ z : ℝ) : ringRadius (ringPoint ρ θ z) = ρ := by
  have e0 : ringPoint ρ θ z 0 = ρ * Real.cos θ := by simp [ringPoint]
  have e1 : ringPoint ρ θ z 1 = ρ * Real.sin θ := by simp [ringPoint]
  rw [ringRadius, e0, e1, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hρ.le]

private theorem frame0_ring {ρ : ℝ} (hρ : 0 < ρ) (z θ : ℝ) : ringFrame 0 (ringPoint ρ θ z) = ringLin θ (1, 0) := by
  rw [ringLin_apply]
  simp only [ringFrame, ringRadius_ring hρ]
  ext i
  fin_cases i <;> simp [ringPoint, hρ.ne']

private theorem frame2_ring (ρ z θ : ℝ) : ringFrame 2 (ringPoint ρ θ z) = ringLin θ (0, 1) := by
  rw [ringLin_apply]
  simp only [ringFrame]
  ext i
  fin_cases i <;> simp [ringPoint]

private theorem frame1_ring {ρ : ℝ} (hρ : 0 < ρ) (z θ : ℝ) :
    ρ • ringFrame 1 (ringPoint ρ θ z) = -Real.sin θ • axisA (ρ, z) + Real.cos θ • axisB (ρ, z) := by
  simp only [ringFrame, ringRadius_ring hρ]
  ext i
  fin_cases i <;> simp [ringPoint, axisA, axisB, hρ.ne'] <;> field_simp

private theorem radial_height_mode {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u)
    (Λ : Space →L[ℝ] ℂ) (k : ℤ) (ρ z : ℝ) (c : Fin 3) (w : ℝ × ℝ)
    (hw : ∀ θ, ringFrame c (ringPoint ρ θ z) = ringLin θ w) :
    fderiv ℝ (fun p : ℝ × ℝ => angularMode (fun y => Λ (u y)) k p.1 p.2) (ρ, z) w =
      angularMode (fun y => Λ (fderiv ℝ u y (ringFrame c y))) k ρ z := by
  have hh : ContDiff ℝ 1 (fun y => Λ (u y)) := (Λ.contDiff.comp hu).of_le (by simp)
  have hhs : HasCompactSupport (fun y => Λ (u y)) := hs.comp_left Λ.map_zero
  have hdc : Continuous (fderiv ℝ (fun y => Λ (u y))) := hh.continuous_fderiv one_ne_zero
  have hF' : Continuous (fun θ => wave k θ • (fderiv ℝ (fun y => Λ (u y)) (ringLin θ (ρ, z))).comp (ringLin θ)) :=
    (wave_cont k).smul ((hdc.comp (ringLin_cont.clm_apply continuous_const)).clm_comp ringLin_cont)
  rw [(mode_hasFDerivAt hh hhs k (ρ, z)).fderiv, angularMode_eq', FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold modeDer modeInt
  rw [ContinuousLinearMap.intervalIntegral_apply (hF'.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, fderiv_clm_comp hu]
  rw [← hw θ, ringLin_apply]

private theorem wave_hasDerivAt (k : ℤ) (t : ℝ) : HasDerivAt (wave k) (wave k t * -((k : ℂ) * Complex.I)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by simpa using (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (wave k) (Complex.exp (-((k : ℂ) * (t : ℂ) * Complex.I)) * -((k : ℂ) * 1 * Complex.I)) t :=
    (((h1.const_mul (k : ℂ)).mul_const Complex.I).neg).cexp
  rw [mul_one] at h2
  exact h2

private theorem wave_period (k : ℤ) : wave k Real.pi = wave k (-Real.pi) := by
  unfold wave
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  ring

private theorem ringLin_period : ringLin Real.pi = ringLin (-Real.pi) := by
  simp [ringLin, Real.cos_neg, Real.sin_neg]

private theorem turn_mode {u : Space → Space} (hu : ContDiff ℝ ∞ u) (Λ : Space →L[ℝ] ℂ) (k : ℤ) {ρ : ℝ}
    (hρ : 0 < ρ) (z : ℝ) :
    angularMode (fun y => Λ (fderiv ℝ u y (ringFrame 1 y))) k ρ z =
      ((k : ℂ) * Complex.I / (ρ : ℂ)) * angularMode (fun y => Λ (u y)) k ρ z := by
  set p : ℝ × ℝ := (ρ, z) with hp
  set h : Space → ℂ := fun y => Λ (u y) with hhdef
  have hh : ContDiff ℝ ∞ h := Λ.contDiff.comp hu
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by simp)
  set d : ℝ → Space := fun t => -Real.sin t • axisA p + Real.cos t • axisB p with hd
  have hdcont : Continuous d := by
    rw [hd]
    fun_prop
  have hdd : ∀ t, HasDerivAt (fun t => ringLin t p) (d t) t := by
    intro t
    have e : (fun t => ringLin t p) = fun t => Real.cos t • axisA p + Real.sin t • axisB p + axisC p := by
      funext t
      simp [ringLin]
    rw [e]
    exact (((Real.hasDerivAt_cos t).smul_const (axisA p)).add ((Real.hasDerivAt_sin t).smul_const (axisB p))).add_const _
  have hg : ∀ t, HasDerivAt (fun t => h (ringLin t p)) (fderiv ℝ h (ringLin t p) (d t)) t := fun t =>
    ((hh.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t (hdd t)
  have hgc : Continuous (fun t => fderiv ℝ h (ringLin t p) (d t)) :=
    (hdc.comp (ringLin_cont.clm_apply continuous_const)).clm_apply hdcont
  have hwc : Continuous (fun t => wave k t * -((k : ℂ) * Complex.I)) := (wave_cont k).mul continuous_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -Real.pi) (b := Real.pi)
    (fun t _ => wave_hasDerivAt k t) (fun t _ => hg t) (hwc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
  rw [wave_period, ringLin_period, sub_self, zero_sub] at hibp
  have hpt : ∀ t, Λ (fderiv ℝ u (ringLin t p) (ringFrame 1 (ringLin t p))) =
      (ρ : ℂ)⁻¹ * fderiv ℝ h (ringLin t p) (d t) := by
    intro t
    have e1 : d t = ρ • ringFrame 1 (ringLin t p) := by
      rw [ringLin_apply, frame1_ring hρ]
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [hhdef, fderiv_clm_comp hu, ContinuousLinearMap.comp_apply, e1, map_smul, map_smul, Complex.real_smul,
      ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]
  have e2 : modeInt (fun y => Λ (fderiv ℝ u y (ringFrame 1 y))) k p =
      (ρ : ℂ)⁻¹ * ∫ t in (-Real.pi)..Real.pi, wave k t * fderiv ℝ h (ringLin t p) (d t) := by
    unfold modeInt
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hpt]
    ring
  have e3 : ∫ t in (-Real.pi)..Real.pi, wave k t * -((k : ℂ) * Complex.I) * h (ringLin t p) =
      -((k : ℂ) * Complex.I) * modeInt h k p := by
    unfold modeInt
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [angularMode_eq', angularMode_eq', e2, hibp, e3]
  ring

private def horizLin : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 3)) +
    Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 3))

private def vertLin : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))

private theorem horiz_eq (F : Space → Space) : horizontalPart F = fun y => horizLin (F y) := by
  funext y
  simp [horizontalPart, horizLin]

private theorem vert_eq (F : Space → Space) : verticalPart F = fun y => vertLin (F y) := by
  funext y
  simp [verticalPart, vertLin]

private theorem turn_norm {k : ℤ} {ρ : ℝ} (hρ : 0 < ρ) (A : ℂ) :
    ‖((k : ℂ) * Complex.I / (ρ : ℂ)) * A‖ ^ 2 = (k : ℝ) ^ 2 * ‖A‖ ^ 2 / ρ ^ 2 := by
  rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_of_nonneg hρ.le,
    div_mul_eq_mul_div, div_pow, mul_pow, sq_abs]

theorem frameModeCalculus : FrameModeCalculusStatement := by
  intro u hu hs k
  have hh1 : ContDiff ℝ 1 (fun y => horizLin (u y)) := (horizLin.contDiff.comp hu).of_le (by simp)
  have hv1 : ContDiff ℝ 1 (fun y => vertLin (u y)) := (vertLin.contDiff.comp hu).of_le (by simp)
  have hhs : HasCompactSupport (fun y => horizLin (u y)) := hs.comp_left horizLin.map_zero
  have hvs : HasCompactSupport (fun y => vertLin (u y)) := hs.comp_left vertLin.map_zero
  rw [horiz_eq u, vert_eq u]
  refine ⟨⟨mode_contDiff hh1 hhs k, mode_compact hhs k⟩, ⟨mode_contDiff hv1 hvs k, mode_compact hvs k⟩,
    fun ρ z hρ => ?_⟩
  unfold frameModeSq
  simp only [Fin.sum_univ_three, horiz_eq, vert_eq]
  rw [radial_height_mode hu hs horizLin k ρ z 0 (1, 0) (frame0_ring hρ z),
    radial_height_mode hu hs horizLin k ρ z 2 (0, 1) (frame2_ring ρ z),
    radial_height_mode hu hs vertLin k ρ z 0 (1, 0) (frame0_ring hρ z),
    radial_height_mode hu hs vertLin k ρ z 2 (0, 1) (frame2_ring ρ z),
    turn_mode hu horizLin k hρ z, turn_mode hu vertLin k hρ z, turn_norm hρ, turn_norm hρ]
  ring

private theorem mirror_mirror' (y : Space) : mirror (mirror y) = y := by
  ext i
  fin_cases i <;> simp [mirror]

private theorem norm_mirror' (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror]

private def mirrorLin' : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mirror] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mirror]

private def mirrorEquiv : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨mirrorLin', norm_mirror'⟩ rfl

private def mirrorCL : Space →L[ℝ] Space := mirrorEquiv.toContinuousLinearEquiv.toContinuousLinearMap

private theorem mirrorCL_apply (y : Space) : mirrorCL y = mirror y := rfl

private theorem mirrorEquiv_apply (y : Space) : mirrorEquiv y = mirror y := rfl

private def conj (A : Space →L[ℝ] Space) : Space →L[ℝ] Space := mirrorCL.comp (A.comp mirrorCL)

private theorem conj_apply (A : Space →L[ℝ] Space) (w : Space) : conj A w = mirror (A (mirror w)) := rfl

private theorem conj_sub (A B : Space →L[ℝ] Space) : conj (A - B) = conj A - conj B := by
  simp [conj, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]

private theorem entrySq_conj (A : Space →L[ℝ] Space) : entrySq (conj A) = entrySq A := by
  have h0 : mirror (unitVector 0) = unitVector 0 := by
    ext i
    fin_cases i <;> simp [mirror, unitVector]
  have h1 : mirror (unitVector 1) = unitVector 1 := by
    ext i
    fin_cases i <;> simp [mirror, unitVector]
  have h2 : mirror (unitVector 2) = -unitVector 2 := by
    ext i
    fin_cases i <;> simp [mirror, unitVector]
  simp only [entrySq, Fin.sum_univ_three, conj_apply, h0, h1, h2, map_neg, norm_mirror', norm_neg]

private theorem half_sq_le (a b : Space) : ‖(1 / 2 : ℝ) • (a + b)‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h : ‖(1 / 2 : ℝ) • (a + b)‖ ≤ (1 / 2) * (‖a‖ + ‖b‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    exact mul_le_mul_of_nonneg_left (norm_add_le a b) (by norm_num)
  have h0 := norm_nonneg ((1 / 2 : ℝ) • (a + b))
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

private theorem entrySq_half_le (A B : Space →L[ℝ] Space) :
    entrySq ((1 / 2 : ℝ) • (A + B)) ≤ entrySq A + entrySq B := by
  unfold entrySq
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using half_sq_le (A (unitVector i)) (B (unitVector i))

private theorem entrySq_nonneg_aux (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem entrySq_cont : Continuous entrySq := by
  unfold entrySq
  fun_prop

private theorem mirror_half (a b : Space) :
    mirror ((1 / 2 : ℝ) • (a + b)) = (1 / 2 : ℝ) • (mirror a + mirror b) := by
  ext i
  fin_cases i <;> simp [mirror] <;> ring

private theorem mirror_sub' (a b : Space) : mirror (a - b) = mirror a - mirror b := by
  ext i
  fin_cases i <;> simp [mirror] <;> ring

private theorem lintegral_mirror (F : Space → ENNReal) : ∫⁻ y, F (mirror y) = ∫⁻ y, F y :=
  mirrorEquiv.measurePreserving.lintegral_comp_emb mirrorEquiv.toHomeomorph.measurableEmbedding F

private theorem ball_lintegral_mirror (R : ℝ) (F : Space → ENNReal) :
    ∫⁻ y in Metric.ball (0 : Space) R, F (mirror y) = ∫⁻ y in Metric.ball (0 : Space) R, F y := by
  have hB : MeasurableSet (Metric.ball (0 : Space) R) := measurableSet_ball
  have hmem : ∀ y, mirror y ∈ Metric.ball (0 : Space) R ↔ y ∈ Metric.ball (0 : Space) R := by
    intro y
    simp [Metric.mem_ball, dist_zero_right, norm_mirror']
  rw [← lintegral_indicator hB, ← lintegral_indicator hB]
  have e : (Metric.ball (0 : Space) R).indicator (fun y => F (mirror y)) =
      fun y => (Metric.ball (0 : Space) R).indicator F (mirror y) := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Space) R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hmem y).2 hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy ((hmem y).1 h))]
  rw [e]
  exact lintegral_mirror _

theorem mirrorApprox_of (hT : TestGradientApproxStatement) (hM : GradientMirrorStatement) :
    MirrorApproxStatement := by
  intro m v G H hv
  obtain ⟨w, hws, hgrad, hball⟩ := hT m v G H hv
  have hGm := hM m v G H hv
  have hvm : ∀ᵐ y ∂volume, v (mirror y) = mirror (v y) := hv.symmetric.2
  have hGc : ∀ᵐ y ∂volume, G y = conj (G (mirror y)) := by
    filter_upwards [hGm] with y hy
    ext1 z
    rw [conj_apply, hy, mirror_mirror']
  have hd : ∀ n y, HasFDerivAt (fun y => (1 / 2 : ℝ) • (w n y + mirrorCL (w n (mirrorCL y))))
      ((1 / 2 : ℝ) • (fderiv ℝ (w n) y + conj (fderiv ℝ (w n) (mirror y)))) y := by
    intro n y
    have hdiff := (hws n).1.differentiable (by simp)
    have h1 : HasFDerivAt (w n) (fderiv ℝ (w n) y) y := (hdiff y).hasFDerivAt
    have h2 : HasFDerivAt (fun y => mirrorCL (w n (mirrorCL y))) (conj (fderiv ℝ (w n) (mirror y))) y :=
      mirrorCL.hasFDerivAt.comp y ((hdiff (mirrorCL y)).hasFDerivAt.comp y mirrorCL.hasFDerivAt)
    exact (h1.add h2).const_smul (1 / 2 : ℝ)
  have hF : ∀ n, AEMeasurable (fun y => ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) volume := by
    intro n
    have hc : Continuous (fderiv ℝ (w n)) := (hws n).1.continuous_fderiv (by simp)
    exact (entrySq_cont.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.sub hv.measurable_gradient)).aemeasurable.ennreal_ofReal
  refine ⟨fun n y => (1 / 2 : ℝ) • (w n y + mirrorCL (w n (mirrorCL y))), fun n => ⟨?_, ?_, fun y => ?_⟩, ?_, ?_⟩
  · exact ((hws n).1.add (mirrorCL.contDiff.comp ((hws n).1.comp mirrorCL.contDiff))).const_smul _
  · have h1 := (hws n).2
    have h2 : HasCompactSupport (fun y => mirrorCL (w n (mirrorCL y))) :=
      (h1.comp_homeomorph mirrorEquiv.toHomeomorph).comp_left (map_zero mirrorCL)
    exact (h1.add h2).comp_left (g := fun x : Space => (1 / 2 : ℝ) • x) (smul_zero _)
  · simp only [mirrorCL_apply]
    rw [mirror_half, mirror_mirror', mirror_mirror', add_comm]
  · have hbd : ∀ n, ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun y => (1 / 2 : ℝ) • (w n y + mirrorCL (w n (mirrorCL y)))) y - G y)) ≤
        (∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) +
          ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y)) := by
      intro n
      calc _ ≤ ∫⁻ y, (ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y)) +
            ENNReal.ofReal (entrySq (fderiv ℝ (w n) (mirror y) - G (mirror y)))) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hGc] with y hy
            rw [(hd n y).fderiv, ← ENNReal.ofReal_add (entrySq_nonneg_aux _) (entrySq_nonneg_aux _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have e : (1 / 2 : ℝ) • (fderiv ℝ (w n) y + conj (fderiv ℝ (w n) (mirror y))) - G y =
                (1 / 2 : ℝ) • ((fderiv ℝ (w n) y - G y) + conj (fderiv ℝ (w n) (mirror y) - G (mirror y))) := by
              rw [conj_sub, ← hy]
              module
            rw [e]
            refine (entrySq_half_le _ _).trans_eq ?_
            rw [entrySq_conj]
        _ = _ := by
            rw [lintegral_add_left' (hF n)]
            congr 1
            exact lintegral_mirror (fun y => ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y)))
    have h0 : Tendsto (fun n => (∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) +
        ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) atTop (𝓝 0) := by
      simpa using hgrad.add hgrad
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hbd
  · intro R
    have hF2 : ∀ n, AEMeasurable (fun y => ENNReal.ofReal (‖w n y - v y‖ ^ 2))
        (volume.restrict (Metric.ball (0 : Space) R)) := by
      intro n
      exact ((((hws n).1.continuous.aestronglyMeasurable.sub hv.measurable_velocity).norm.pow 2).aemeasurable.ennreal_ofReal).restrict
    have hbd : ∀ n, ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖(1 / 2 : ℝ) • (w n y + mirrorCL (w n (mirrorCL y))) - v y‖ ^ 2) ≤
        (∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖w n y - v y‖ ^ 2)) +
          ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖w n y - v y‖ ^ 2) := by
      intro n
      calc _ ≤ ∫⁻ y in Metric.ball (0 : Space) R, (ENNReal.ofReal (‖w n y - v y‖ ^ 2) +
            ENNReal.ofReal (‖w n (mirror y) - v (mirror y)‖ ^ 2)) := by
            refine lintegral_mono_ae (ae_restrict_of_ae ?_)
            filter_upwards [hvm] with y hy
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have e : (1 / 2 : ℝ) • (w n y + mirrorCL (w n (mirrorCL y))) - v y =
                (1 / 2 : ℝ) • ((w n y - v y) + mirror (w n (mirror y) - v (mirror y))) := by
              rw [mirror_sub', hy, mirror_mirror', mirrorCL_apply, mirrorCL_apply]
              module
            rw [e]
            refine (half_sq_le _ _).trans_eq ?_
            rw [norm_mirror']
        _ = _ := by
            rw [lintegral_add_left' (hF2 n)]
            congr 1
            exact ball_lintegral_mirror R (fun y => ENNReal.ofReal (‖w n y - v y‖ ^ 2))
    have h0 := (hball R).add (hball R)
    rw [add_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hbd

theorem mirrorApprox : MirrorApproxStatement :=
  mirrorApprox_of testGradientApprox gradientMirror

end FrameInverseSquareParts

end FracInternal

end Breakdown
