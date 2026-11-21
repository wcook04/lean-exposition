import Breakdown.FracCell.ReductionLossRowModeGradient
import Breakdown.Frac.PAxial
import Breakdown.FracCert.DriftWeakLimit
import Breakdown.FracCell.RowTurnPair

open MeasureTheory Filter Topology
open scoped Interval Convolution ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def RotationSmoothStatement : Prop :=
  ∀ w : Space → Space, ContDiff ℝ 1 w → ∀ S : Set Space, MeasurableSet S → Bornology.IsBounded S →
    (∀ (φ : ℝ) y, y ∈ S ↔ turnBy φ y ∈ S) → ∀ φ : ℝ,
      eLpNorm (fun y => w (turnBy φ y) - w y) 2 (volume.restrict S) ≤
        ENNReal.ofReal |φ| * eLpNorm (fun y => fderiv ℝ w y (axialTurn y)) 2 (volume.restrict S)

def RotationApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ K : Set Space, IsCompact K → ∃ w : ℕ → Space → Space, (∀ n, ContDiff ℝ 1 (w n)) ∧
      Filter.Tendsto (fun n => eLpNorm (fun y => w n y - v y) 2 (volume.restrict K)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => eLpNorm (fun y => fderiv ℝ (w n) y (axialTurn y) - G y (axialTurn y)) 2
        (volume.restrict K)) Filter.atTop (nhds 0)

def MollifierStatement : Prop :=
  ∃ ρ : ℕ → Space → ℝ, (∀ n, ContDiff ℝ ∞ (ρ n)) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
    (∀ n y, ρ n y ≠ 0 → ‖y‖ ≤ 1) ∧ ∀ f : Space → Space, MemLp f 2 volume →
      Tendsto (fun n => eLpNorm (fun x => (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume)
        atTop (𝓝 0)

def ConvGradientStatement : Prop :=
  ∀ ρ : Space → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ → (∀ y, ρ y ≠ 0 → ‖y‖ ≤ 1) →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), LocallyIntegrable v volume →
      (∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume) → IsWeakGradientOf v G →
      ∀ B : Set Space, MeasurableSet B → ∀ y, Metric.closedBall y 1 ⊆ B → ∀ j : Fin 3,
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] B.indicator v) y (unitVector j) =
          (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] B.indicator (fun z => G z (unitVector j))) y

namespace RotationLeavesInternal

theorem rot_eq (φ : ℝ) (y : Space) : axialRotation φ y = turnBy φ y := by
  rw [FracInternal.Axial.axialRotation_eq_formula]
  rfl

theorem turn_fun (φ : ℝ) : turnBy φ = axialRotation φ := funext fun y => (rot_eq φ y).symm

theorem turn_mp (φ : ℝ) : MeasurePreserving (turnBy φ) volume volume := by
  rw [turn_fun]
  exact (axialRotation φ).measurePreserving

theorem turn_embedding (φ : ℝ) : MeasurableEmbedding (turnBy φ) := by
  rw [turn_fun]
  exact (axialRotation φ).toHomeomorph.measurableEmbedding

theorem turn_mp_restrict {S : Set Space} (hS : MeasurableSet S)
    (hinv : ∀ (φ : ℝ) y, y ∈ S ↔ turnBy φ y ∈ S) (φ : ℝ) :
    MeasurePreserving (turnBy φ) (volume.restrict S) (volume.restrict S) := by
  have h := (turn_mp φ).restrict_preimage hS
  have hpre : turnBy φ ⁻¹' S = S := by
    ext y
    exact (hinv φ y).symm
  rwa [hpre] at h

theorem norm_turn (φ : ℝ) (y : Space) : ‖turnBy φ y‖ = ‖y‖ := by
  rw [← rot_eq]
  exact LinearIsometryEquiv.norm_map _ _

theorem turn_zero (y : Space) : turnBy 0 y = y := by
  ext i
  fin_cases i <;> simp [turnBy]

theorem turn_hasDerivAt (s : ℝ) (y : Space) :
    HasDerivAt (fun t => turnBy t y) (axialTurn (turnBy s y)) s := by
  have h := FracInternal.Axial.axialRotation_hasDerivAt s y
  simp only [rot_eq] at h
  exact h

theorem single_cont (i : Fin 3) : Continuous (fun a : ℝ => (EuclideanSpace.single i a : Space)) := by
  have h : (fun a : ℝ => (EuclideanSpace.single i a : Space)) =
      fun a => a • (EuclideanSpace.single i (1 : ℝ) : Space) := by
    funext a
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [h]
  fun_prop

theorem turn_joint : Continuous (fun p : Space × ℝ => turnBy p.2 p.1) := by
  have h0 := single_cont 0
  have h1 := single_cont 1
  have h2 := single_cont 2
  unfold turnBy
  fun_prop

theorem sq_integral_le {μ : Measure ℝ} [IsFiniteMeasure μ] (f : ℝ → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun s => f s ^ 2) μ) :
    (∫ s, f s ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ s, f s ^ 2 ∂μ := by
  set F := ∫ s, f s ∂μ with hF
  set t := μ.real Set.univ with ht
  have h0 : 0 ≤ ∫ s, (t * f s - F) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ s, (t * f s - F) ^ 2 ∂μ = t ^ 2 * (∫ s, f s ^ 2 ∂μ) - 2 * t * F * F + t * F ^ 2 := by
    have e : (fun s => (t * f s - F) ^ 2) = fun s => (t ^ 2 * f s ^ 2 - (2 * t * F) * f s) + F ^ 2 := by
      funext s
      ring
    rw [e, integral_add (f := fun s => t ^ 2 * f s ^ 2 - (2 * t * F) * f s) (g := fun _ => F ^ 2)
      (by exact (hf2.const_mul _).sub (hf.const_mul _)) (integrable_const _),
      integral_sub (f := fun s => t ^ 2 * f s ^ 2) (g := fun s => (2 * t * F) * f s)
        (hf2.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul, integral_const,
      smul_eq_mul]
  have ht0 : 0 ≤ t := measureReal_nonneg
  rcases ht0.lt_or_eq with htp | htz
  · nlinarith
  · have hu : μ Set.univ = 0 := by
      have h := htz.symm
      rw [ht, measureReal_eq_zero_iff (measure_ne_top μ _)] at h
      exact h
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.1 hu
    have hF0 : F = 0 := by simp [hF, hμ]
    rw [hF0, ← htz]
    simp

theorem fd_cont {w : Space → Space} (hw : ContDiff ℝ 1 w) :
    Continuous (fun z => fderiv ℝ w z (axialTurn z)) :=
  (hw.continuous_fderiv (by norm_num)).clm_apply SteadyCert.Internal.DriftWeakLimit.continuous_turn

theorem orbit_cont (y : Space) : Continuous (fun s : ℝ => turnBy s y) := by
  have h0 := single_cont 0
  have h1 := single_cont 1
  have h2 := single_cont 2
  unfold turnBy
  fun_prop

theorem ftc_orbit {w : Space → Space} (hw : ContDiff ℝ 1 w) (y : Space) (φ : ℝ) :
    ∫ s in (0 : ℝ)..φ, fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y)) = w (turnBy φ y) - w y := by
  have hgc : Continuous (fun s => fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))) :=
    (fd_cont hw).comp (orbit_cont y)
  have hdiff : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hderiv : ∀ s, HasDerivAt (fun t => w (turnBy t y))
      (fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))) s := fun s =>
    (hdiff (turnBy s y)).hasFDerivAt.comp_hasDerivAt s (turn_hasDerivAt s y)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hgc.intervalIntegrable _ _),
    turn_zero]

theorem uIoc_finite (φ : ℝ) : volume (Ι (0 : ℝ) φ) ≠ ⊤ := by
  rw [Real.volume_uIoc]
  exact ENNReal.ofReal_ne_top

theorem uIoc_real (φ : ℝ) : (volume.restrict (Ι (0 : ℝ) φ)).real Set.univ = |φ| := by
  rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_uIoc, sub_zero,
    ENNReal.toReal_ofReal (abs_nonneg _)]

theorem point_bound {w : Space → Space} (hw : ContDiff ℝ 1 w) (y : Space) (φ : ℝ) :
    ‖w (turnBy φ y) - w y‖ ^ 2 ≤
      |φ| * ∫ s in Ι 0 φ, ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ ^ 2 := by
  have hgc : Continuous (fun s => fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))) :=
    (fd_cont hw).comp (orbit_cont y)
  have h1 : ‖w (turnBy φ y) - w y‖ ≤ ∫ s in Ι 0 φ, ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ := by
    rw [← ftc_orbit hw y φ]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc
  have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) φ)) := isFiniteMeasure_restrict.2 (uIoc_finite φ)
  have h2 := sq_integral_le (μ := volume.restrict (Ι (0 : ℝ) φ))
    (fun s => ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖)
    hgc.norm.integrableOn_uIoc ((hgc.norm.pow 2).integrableOn_uIoc)
  rw [uIoc_real] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem sq_int_eq (F : Space → Space) (μ : Measure Space) (hF : AEStronglyMeasurable F μ) :
    (∫ y, ‖F y‖ ^ 2 ∂μ) = ((eLpNorm F 2 μ) ^ 2).toReal := by
  have h1 : eLpNorm F 2 μ ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := F) (p := 2) two_ne_zero
    simpa using this
  rw [h1, integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖F y‖ ^ 2)
    (Eventually.of_forall fun y => by positivity) (by exact hF.norm.pow 2)]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem fd_bound {w : Space → Space} (hw : ContDiff ℝ 1 w) (r : ℝ) :
    ∃ M, ∀ z ∈ Metric.closedBall (0 : Space) r, ‖fderiv ℝ w z (axialTurn z)‖ ^ 2 ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) r).exists_bound_of_continuousOn
    (((fd_cont hw).norm.pow 2).continuousOn)
  refine ⟨M, fun z hz => ?_⟩
  have h := hM z hz
  rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h

theorem smooth_integral_le {w : Space → Space} (hw : ContDiff ℝ 1 w) {S : Set Space} (hSm : MeasurableSet S)
    (hSb : Bornology.IsBounded S) (hinv : ∀ (φ : ℝ) y, y ∈ S ↔ turnBy φ y ∈ S) (φ : ℝ) :
    (∫ y in S, ‖w (turnBy φ y) - w y‖ ^ 2) ≤ φ ^ 2 * ∫ y in S, ‖fderiv ℝ w y (axialTurn y)‖ ^ 2 := by
  obtain ⟨r, hr⟩ := hSb.subset_closedBall 0
  obtain ⟨M, hM⟩ := fd_bound hw r
  have hfS : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSb.measure_lt_top.ne
  have hfI : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) φ)) := isFiniteMeasure_restrict.2 (uIoc_finite φ)
  have hKc : Continuous (fun p : Space × ℝ =>
      ‖fderiv ℝ w (turnBy p.2 p.1) (axialTurn (turnBy p.2 p.1))‖ ^ 2) :=
    ((fd_cont hw).comp turn_joint).norm.pow 2
  have hKint : Integrable (fun p : Space × ℝ =>
      ‖fderiv ℝ w (turnBy p.2 p.1) (axialTurn (turnBy p.2 p.1))‖ ^ 2)
      ((volume.restrict S).prod (volume.restrict (Ι (0 : ℝ) φ))) := by
    refine Integrable.of_bound hKc.aestronglyMeasurable M ?_
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (hSm.prod measurableSet_uIoc) fun p hp => ?_
    have hz : turnBy p.2 p.1 ∈ Metric.closedBall (0 : Space) r := by
      have h := hr hp.1
      simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
      rw [norm_turn]
      exact h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hM _ hz
  have hpt : ∀ y, ‖w (turnBy φ y) - w y‖ ^ 2 ≤
      |φ| * ∫ s in Ι 0 φ, ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ ^ 2 :=
    fun y => point_bound hw y φ
  have hinner : ∀ s, ∫ y in S, ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ ^ 2 =
      ∫ y in S, ‖fderiv ℝ w y (axialTurn y)‖ ^ 2 := fun s =>
    (turn_mp_restrict hSm hinv s).integral_comp (turn_embedding s)
      (fun z => ‖fderiv ℝ w z (axialTurn z)‖ ^ 2)
  calc (∫ y in S, ‖w (turnBy φ y) - w y‖ ^ 2)
      ≤ ∫ y in S, |φ| * ∫ s in Ι 0 φ, ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
          (hKint.integral_prod_left.const_mul _) (Eventually.of_forall hpt)
    _ = |φ| * ∫ s in Ι 0 φ, ∫ y in S, ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ ^ 2 := by
        rw [integral_const_mul,
          integral_integral_swap (f := fun y s => ‖fderiv ℝ w (turnBy s y) (axialTurn (turnBy s y))‖ ^ 2) hKint]
    _ = φ ^ 2 * ∫ y in S, ‖fderiv ℝ w y (axialTurn y)‖ ^ 2 := by
        simp_rw [hinner]
        rw [integral_const, smul_eq_mul, uIoc_real, ← mul_assoc, ← sq, sq_abs]

theorem turn_norm_le (y : Space) : ‖axialTurn y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, FracInternal.Axial.turn_zero_coord,
    FracInternal.Axial.turn_one_coord, FracInternal.Axial.turn_two_coord]
  nlinarith [sq_nonneg (y 2)]

theorem fderiv_zero_far {ρ : Space → ℝ} (hρ1 : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ 1) {u : Space} (hu : 1 < ‖u‖) :
    fderiv ℝ ρ u = 0 := by
  have h : ρ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hu] with x hx
    by_contra hne
    exact absurd (hρ1 x hne) (not_le.2 hx)
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

theorem shift_fderiv {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (y z e : Space) :
    fderiv ℝ (fun z => ρ (y - z)) z e = -fderiv ℝ ρ (y - z) e := by
  have hk : DifferentiableAt ℝ ρ (y - z) := hρ.differentiable (by simp) _
  have h1 : HasFDerivAt (fun z => ρ (y - z))
      ((fderiv ℝ ρ (y - z)).comp (-(ContinuousLinearMap.id ℝ Space))) z :=
    hk.hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub y)
  rw [h1.fderiv]
  simp

end RotationLeavesInternal

open RotationLeavesInternal in
theorem rotationSmooth : RotationSmoothStatement := by
  intro w hw S hSm hSb hinv φ
  obtain ⟨r, hr⟩ := hSb.subset_closedBall 0
  have hmain := smooth_integral_le hw hSm hSb hinv φ
  have hRc : Continuous (turnBy φ) := by
    rw [turn_fun]
    exact (axialRotation φ).continuous
  have hFc : Continuous (fun y => w (turnBy φ y) - w y) := (hw.continuous.comp hRc).sub hw.continuous
  have memS : ∀ g : Space → Space, Continuous g → MemLp g 2 (volume.restrict S) := fun g hg =>
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
      (((hg.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set hr)
  have eA := sq_int_eq (fun y => w (turnBy φ y) - w y) (volume.restrict S) hFc.aestronglyMeasurable
  have eB := sq_int_eq (fun y => fderiv ℝ w y (axialTurn y)) (volume.restrict S) (fd_cont hw).aestronglyMeasurable
  beta_reduce at eA eB
  rw [eA, eB] at hmain
  have hFf := (memS _ hFc).eLpNorm_ne_top
  have hHf := (memS _ (fd_cont hw)).eLpNorm_ne_top
  have h2 : eLpNorm (fun y => w (turnBy φ y) - w y) 2 (volume.restrict S) ^ 2 ≤
      (ENNReal.ofReal |φ| * eLpNorm (fun y => fderiv ℝ w y (axialTurn y)) 2 (volume.restrict S)) ^ 2 := by
    rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hFf),
      ← ENNReal.ofReal_toReal (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHf))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow, ENNReal.toReal_mul, ENNReal.toReal_pow (ENNReal.ofReal |φ|),
      ENNReal.toReal_ofReal (abs_nonneg _), sq_abs]
    exact hmain
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2

open RotationLeavesInternal in
theorem rotationApprox_of (hM : MollifierStatement) (hD : ConvGradientStatement) : RotationApproxStatement := by
  obtain ⟨ρ, hρs, hρc, hρ1, hρl⟩ := hM
  intro m v G H hv K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hBm : MeasurableSet (Metric.closedBall (0 : Space) (R + 1)) := measurableSet_closedBall
  have hBf : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (R + 1))) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hv2 : MemLp ((Metric.closedBall (0 : Space) (R + 1)).indicator v) 2 volume := by
    rw [memLp_indicator_iff_restrict hBm]
    exact (hv.velocity_six.restrict _).mono_exponent (by norm_num)
  have hcol : ∀ j : Fin 3, MemLp (fun y => G y (unitVector j)) 2 volume := fun j => by
    have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
      hv.measurable_gradient.apply_continuousLinearMap (unitVector j)
    refine (memLp_two_iff_integrable_sq_norm hmj).2
      (hv.gradient_two.mono' (hmj.norm.pow 2) (Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hg2 : ∀ j : Fin 3, MemLp ((Metric.closedBall (0 : Space) (R + 1)).indicator
      (fun y => G y (unitVector j))) 2 volume := fun j => (hcol j).indicator hBm
  have hvl : LocallyIntegrable ((Metric.closedBall (0 : Space) (R + 1)).indicator v) volume :=
    hv2.locallyIntegrable (by norm_num)
  have hvl0 : LocallyIntegrable v volume := hv.velocity_six.locallyIntegrable (by norm_num)
  have hGl : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (hcol j).locallyIntegrable (by norm_num)
  have hsmooth : ∀ n, ContDiff ℝ ∞ (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (Metric.closedBall (0 : Space) (R + 1)).indicator v) := fun n =>
    (hρc n).contDiff_convolution_left _ (hρs n) hvl
  refine ⟨fun n => ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Metric.closedBall (0 : Space) (R + 1)).indicator v,
    fun n => (hsmooth n).of_le (by exact_mod_cast le_top), ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hρl _ hv2) (fun _ => zero_le)
      (fun n => ?_)
    calc eLpNorm (fun y => (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator v) y - v y) 2 (volume.restrict K)
        = eLpNorm (fun y => (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator v) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator v y) 2 (volume.restrict K) := by
          refine eLpNorm_congr_ae ((ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun y hy => ?_))
          have hyB : y ∈ Metric.closedBall (0 : Space) (R + 1) :=
            Metric.closedBall_subset_closedBall (by linarith) (hR hy)
          simp only [Set.indicator_of_mem hyB]
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  · have hlim : Tendsto (fun n => ENNReal.ofReal R * ∑ j : Fin 3,
        eLpNorm (fun y => (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j)) y) 2 volume)
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (tendsto_finsetSum Finset.univ fun j _ => hρl _ (hg2 j))
        (Or.inr (ENNReal.ofReal_ne_top (r := R)))
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) (fun n => ?_)
    have hdm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j)) y) volume := fun j =>
      ((hρc n).contDiff_convolution_left _ (hρs n) ((hg2 j).locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable.sub
        (hg2 j).1
    have hpt : ∀ᵐ y ∂(volume.restrict K),
        ‖fderiv ℝ (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator v) y (axialTurn y) - G y (axialTurn y)‖ ≤
          R * ‖∑ j : Fin 3, ‖(ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j)) y‖‖ := by
      refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun y hy => ?_)
      have hyR : ‖y‖ ≤ R := by simpa using hR hy
      have hball : Metric.closedBall y 1 ⊆ Metric.closedBall (0 : Space) (R + 1) := fun z hz => by
        rw [Metric.mem_closedBall, dist_eq_norm] at hz
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith
      have hyB : y ∈ Metric.closedBall (0 : Space) (R + 1) := hball (Metric.mem_closedBall_self zero_le_one)
      have hder := fun j => hD (ρ n) (hρs n) (hρc n) (hρ1 n) v G hvl0 hGl hv.weak_gradient _ hBm y hball j
      rw [SteadyCert.Internal.DriftWeakLimit.clm_decomp (fderiv ℝ _ y) (axialTurn y),
        SteadyCert.Internal.DriftWeakLimit.clm_decomp (G y) (axialTurn y), ← Finset.sum_sub_distrib]
      simp only [hder, ← smul_sub]
      calc _ ≤ ∑ j : Fin 3, ‖axialTurn y j • ((ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            G y (unitVector j))‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin 3, R * ‖(ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j)) y‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [norm_smul, Set.indicator_of_mem hyB]
            exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (axialTurn y) j).trans
              ((turn_norm_le y).trans hyR)) (norm_nonneg _)
        _ = _ := by
            rw [← Finset.mul_sum, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
    have hsum : (fun y => ∑ j : Fin 3, ‖(ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j)) y‖) =
        ∑ j : Fin 3, (fun y => ‖(ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j))) y -
            (Metric.closedBall (0 : Space) (R + 1)).indicator (fun z => G z (unitVector j)) y‖) := by
      funext y
      simp [Finset.sum_apply]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2).trans (mul_le_mul_right ?_ _)
    rw [hsum]
    refine (eLpNorm_sum_le (fun j _ => (hdm j).norm.restrict) (by norm_num)).trans
      (Finset.sum_le_sum fun j _ => ?_)
    rw [eLpNorm_norm]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

theorem rotationMollifier : MollifierStatement :=
  ⟨FracInternal.RowTurnPair.kern, FracInternal.RowTurnPair.kern_contDiff, FracInternal.RowTurnPair.kern_compact,
    fun n _ hy => FracInternal.RowTurnPair.kern_support n hy, fun _ hf => FracInternal.RowTurnPair.kern_approx hf⟩

open RotationLeavesInternal in
theorem convGradient : ConvGradientStatement := by
  intro ρ hρ hc hρ1 v G hvl hGl hw B hB y hball j
  have hvB : LocallyIntegrable (B.indicator v) volume := hvl.indicator hB
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hρ.of_le (by exact_mod_cast le_top)) hvB y
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space) (hρ.continuous_fderiv (by simp)) hvB y
  have hstep : fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] B.indicator v) y (unitVector j) =
      ((fun t => fderiv ℝ ρ t (unitVector j)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] B.indicator v) y := by
    rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
    simp
  have hfar : ∀ z, z ∉ B → 1 < ‖y - z‖ := fun z hz => by
    by_contra hle
    push Not at hle
    exact hz (hball (by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hle))
  rw [hstep, convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]
  have e1 : (fun z => fderiv ℝ ρ (y - z) (unitVector j) • B.indicator v z) =
      fun z => fderiv ℝ ρ (y - z) (unitVector j) • v z := by
    funext z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
    · rw [fderiv_zero_far hρ1 (hfar z hz)]
      simp
  have e2 : (fun z => ρ (y - z) • B.indicator (fun z => G z (unitVector j)) z) =
      fun z => ρ (y - z) • G z (unitVector j) := by
    funext z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
    · have h0 : ρ (y - z) = 0 := by
        by_contra hne
        exact absurd (hρ1 _ hne) (not_le.2 (hfar z hz))
      rw [h0]
      simp
  rw [e1, e2]
  have hweak := hw (fun z => ρ (y - z))
    ⟨hρ.comp (contDiff_const.sub contDiff_id), hc.comp_homeomorph (Homeomorph.subLeft y)⟩ j
  simp only [shift_fderiv hρ, neg_smul, integral_neg, neg_inj] at hweak
  exact hweak

theorem rotationApprox : RotationApproxStatement :=
  rotationApprox_of rotationMollifier convGradient

end Reduction

end CellCert

end Breakdown
