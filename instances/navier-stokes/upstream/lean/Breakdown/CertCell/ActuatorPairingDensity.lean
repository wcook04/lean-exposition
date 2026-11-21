import Breakdown.CertCell.TopStatements
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoerciveSquareSum
import Breakdown.Cert.CoerciveTorus
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.ActuatorPairingDensity

open Coercive.ModeL2Internal (IsSquareField weightedModeTerm slab)

theorem prodVolume_addInvariant : (volume : Measure (ℝ × Space)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

attribute [local instance] prodVolume_addInvariant

theorem prodVolume_isNegInvariant : (volume : Measure (ℝ × Space)).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular volume

attribute [local instance] prodVolume_isNegInvariant

def bumpSeq (m : ℕ) : ContDiffBump (0 : ℝ × Space) :=
  ⟨1 / ((m : ℝ) + 2), 1 / ((m : ℝ) + 1), by positivity, by
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith⟩

def kernel (m : ℕ) : ℝ × Space → ℝ := (bumpSeq m).normed volume

def smoothed (ψ : ℝ → Space → Space) (m : ℕ) (σ : ℝ) (y : Space) : Space :=
  convolution (kernel m) (fun z : ℝ × Space => ψ z.1 z.2) (ContinuousLinearMap.lsmul ℝ ℝ) volume (σ, y)

def componentMap (i : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space (unitVector i))

theorem componentMap_apply (i : Fin 3) (A : Space →L[ℝ] Space) : componentMap i A = A (unitVector i) i := rfl

theorem kernel_nonneg (m : ℕ) (w : ℝ × Space) : 0 ≤ kernel m w := (bumpSeq m).nonneg_normed w

theorem kernel_integrable (m : ℕ) : Integrable (kernel m) := (bumpSeq m).integrable_normed

theorem kernel_integral (m : ℕ) : ∫ w, kernel m w = 1 := (bumpSeq m).integral_normed

theorem kernel_continuous (m : ℕ) : Continuous (kernel m) :=
  ((bumpSeq m).contDiff_normed (n := 0)).continuous

theorem kernel_eq_zero (m : ℕ) {w : ℝ × Space} (hw : 1 ≤ ‖w.2‖) : kernel m w = 0 := by
  by_contra h
  have hmem : w ∈ Function.support ((bumpSeq m).normed volume) := h
  rw [(bumpSeq m).support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (bumpSeq m).rOut ≤ 1 := by
    show 1 / ((m : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    linarith
  have h2 := norm_snd_le w
  linarith

theorem rOut_tendsto : Filter.Tendsto (fun m => (bumpSeq m).rOut) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem smoothed_eq (ψ : ℝ → Space → Space) (m : ℕ) (σ : ℝ) (y : Space) :
    smoothed ψ m σ y = ∫ w : ℝ × Space, kernel m w • ψ (σ - w.1) (y - w.2) := by
  unfold smoothed
  rw [convolution_def]
  rfl

theorem exists_bound_of_periodic {E : Type*} [NormedAddCommGroup E] {K : ℝ → Space → E}
    (hc : Continuous (fun z : ℝ × Space => K z.1 z.2)) (hp : IsTimePeriodic K)
    {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → K σ y = 0) : ∃ C, 0 ≤ C ∧ ∀ σ y, ‖K σ y‖ ≤ C := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun σ y => ?_⟩
  by_cases hy : R < ‖y‖
  · rw [hs σ y hy, norm_zero]
    exact le_max_right _ _
  · have hper : Function.Periodic (fun s => K s y) 1 := fun s => hp s y
    have e : K σ y = K (Int.fract σ) y := by
      have h := hper.sub_int_mul_eq (x := σ) ⌊σ⌋
      rw [mul_one] at h
      exact h.symm
    rw [e]
    refine (hC (Int.fract σ, y) ⟨⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩, ?_⟩).trans (le_max_left _ _)
    simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.1 hy

theorem integrable_kernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ)
    {K : ℝ × Space → E} (hc : Continuous K) {C : ℝ} (hC : ∀ z, ‖K z‖ ≤ C) (z : ℝ × Space) :
    Integrable (fun w => kernel m w • K (z - w)) := by
  refine Integrable.mono' ((kernel_integrable m).mul_const C) ?_ (ae_of_all _ fun w => ?_)
  · exact ((kernel_continuous m).smul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg m w)]
    exact mul_le_mul_of_nonneg_left (hC _) (kernel_nonneg m w)

theorem norm_kernel_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ)
    {K : ℝ × Space → E} {C : ℝ} (hC : ∀ z, ‖K z‖ ≤ C) (z : ℝ × Space) :
    ‖∫ w, kernel m w • K (z - w)‖ ≤ C := by
  refine (norm_integral_le_of_norm_le ((kernel_integrable m).mul_const C) (ae_of_all _ fun w => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg m w)]
    exact mul_le_mul_of_nonneg_left (hC _) (kernel_nonneg m w)
  · rw [integral_mul_const, kernel_integral, one_mul]

theorem slice_differentiableAt {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2))
    (s : ℝ) (x : Space) : DifferentiableAt ℝ (ψ s) x := by
  have h := (hψ.differentiable one_ne_zero (s, x)).comp x
    ((differentiableAt_const s).prodMk differentiableAt_id)
  exact h

theorem gradField_continuous {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradField ψ z.1 z.2) :=
  (Coercive.PairingSplitInternal.contDiff_slice (V := ψ) (n := 0) hψ (by norm_num)).continuous

theorem smoothed_hasFDerivAt {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2))
    {C Cg : ℝ} (hC : ∀ σ y, ‖ψ σ y‖ ≤ C) (hCg : ∀ σ y, ‖gradField ψ σ y‖ ≤ Cg) (m : ℕ) (σ : ℝ) (y : Space) :
    HasFDerivAt (smoothed ψ m σ) (∫ w : ℝ × Space, kernel m w • gradField ψ (σ - w.1) (y - w.2)) y := by
  have e : smoothed ψ m σ = fun y' => ∫ w : ℝ × Space, kernel m w • ψ (σ - w.1) (y' - w.2) :=
    funext fun y' => smoothed_eq ψ m σ y'
  rw [e]
  have hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2) := hψ.continuous
  have hg := gradField_continuous hψ
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (F := fun y' w => kernel m w • ψ (σ - w.1) (y' - w.2))
    (F' := fun y' w => kernel m w • gradField ψ (σ - w.1) (y' - w.2)) (bound := fun w => kernel m w * Cg)
    Filter.univ_mem (Filter.Eventually.of_forall fun y' => ?_) ?_ ?_ (ae_of_all _ fun w y' _ => ?_)
    ((kernel_integrable m).mul_const Cg) (ae_of_all _ fun w y' _ => ?_)
  · exact (integrable_kernel_smul m hc (fun z => hC z.1 z.2) (σ, y')).aestronglyMeasurable
  · exact integrable_kernel_smul m hc (fun z => hC z.1 z.2) (σ, y)
  · exact (integrable_kernel_smul m hg (fun z => hCg z.1 z.2) (σ, y)).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg m w)]
    exact mul_le_mul_of_nonneg_left (hCg _ _) (kernel_nonneg m w)
  · have h1 : HasFDerivAt (fun y'' : Space => y'' - w.2) (ContinuousLinearMap.id ℝ Space) y' :=
      (hasFDerivAt_id y').sub_const w.2
    have h2 := ((slice_differentiableAt hψ (σ - w.1) (y' - w.2)).hasFDerivAt.comp y' h1).const_smul (kernel m w)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2

theorem smoothed_fderiv {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2))
    {C Cg : ℝ} (hC : ∀ σ y, ‖ψ σ y‖ ≤ C) (hCg : ∀ σ y, ‖gradField ψ σ y‖ ≤ Cg) (m : ℕ) (σ : ℝ) (y : Space) :
    fderiv ℝ (smoothed ψ m σ) y = ∫ w : ℝ × Space, kernel m w • gradField ψ (σ - w.1) (y - w.2) :=
  (smoothed_hasFDerivAt hψ hC hCg m σ y).fderiv

theorem smoothed_contDiff {ψ : ℝ → Space → Space} (hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2)) (m : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => smoothed ψ m z.1 z.2) :=
  HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (bumpSeq m).hasCompactSupport_normed (bumpSeq m).contDiff_normed hc.locallyIntegrable

theorem smoothed_periodic {ψ : ℝ → Space → Space} (hp : IsTimePeriodic ψ) (m : ℕ) :
    IsTimePeriodic (smoothed ψ m) := by
  intro σ y
  rw [smoothed_eq, smoothed_eq]
  congr 1
  funext w
  rw [show σ + 1 - w.1 = (σ - w.1) + 1 by ring, hp]

theorem smoothed_far {ψ : ℝ → Space → Space} {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → ψ σ y = 0) (m : ℕ) :
    ∀ σ y, R + 1 < ‖y‖ → smoothed ψ m σ y = 0 := by
  intro σ y hy
  rw [smoothed_eq]
  have e : (fun w : ℝ × Space => kernel m w • ψ (σ - w.1) (y - w.2)) = fun _ => 0 := by
    funext w
    by_cases hw : ‖w.2‖ < 1
    · have h := norm_sub_norm_le y w.2
      rw [hs _ _ (by linarith), smul_zero]
    · rw [kernel_eq_zero m (not_lt.1 hw), zero_smul]
  rw [e, integral_zero]

theorem smoothed_divergence {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2))
    {C Cg : ℝ} (hC : ∀ σ y, ‖ψ σ y‖ ≤ C) (hCg : ∀ σ y, ‖gradField ψ σ y‖ ≤ Cg)
    (hdiv : ∀ σ y, divergenceAt (ψ σ) y = 0) (m : ℕ) (σ : ℝ) (y : Space) :
    divergenceAt (smoothed ψ m σ) y = 0 := by
  have hI : Integrable (fun w : ℝ × Space => kernel m w • gradField ψ (σ - w.1) (y - w.2)) :=
    integrable_kernel_smul m (gradField_continuous hψ) (fun z => hCg z.1 z.2) (σ, y)
  have e : ∀ i : Fin 3, (fderiv ℝ (smoothed ψ m σ) y (unitVector i)) i
      = ∫ w : ℝ × Space, componentMap i (kernel m w • gradField ψ (σ - w.1) (y - w.2)) := by
    intro i
    rw [smoothed_fderiv hψ hC hCg m σ y, ← componentMap_apply, ContinuousLinearMap.integral_comp_comm _ hI]
  unfold divergenceAt
  simp_rw [e]
  rw [← integral_finsetSum _ fun i _ => (componentMap i).integrable_comp hI]
  have hz : ∀ w : ℝ × Space, ∑ i : Fin 3, componentMap i (kernel m w • gradField ψ (σ - w.1) (y - w.2)) = 0 := by
    intro w
    have h0 := hdiv (σ - w.1) (y - w.2)
    unfold divergenceAt at h0
    simp only [map_smul, smul_eq_mul, componentMap_apply, gradField]
    rw [← Finset.mul_sum, h0, mul_zero]
  simp_rw [hz]
  exact integral_zero _ _

theorem smoothed_testField {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2))
    (hp : IsTimePeriodic ψ) {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → ψ σ y = 0)
    {C Cg : ℝ} (hC : ∀ σ y, ‖ψ σ y‖ ≤ C) (hCg : ∀ σ y, ‖gradField ψ σ y‖ ≤ Cg)
    (hdiv : ∀ σ y, divergenceAt (ψ σ) y = 0) (m : ℕ) : IsPeriodicTestField (smoothed ψ m) :=
  ⟨smoothed_contDiff hψ.continuous m, smoothed_periodic hp m, ⟨R + 1, smoothed_far hs m⟩,
    smoothed_divergence hψ hC hCg hdiv m⟩


theorem continuous_curlVec : Continuous curlVec := by
  unfold curlVec
  exact continuous_finsetSum _ fun i _ => (continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun l _ => continuous_const.mul
      ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp
        (continuous_id.clm_apply continuous_const))).smul continuous_const

theorem continuous_secondDerivTrace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem curlVec_bound (Cg : ℝ) : ∃ K, 0 ≤ K ∧ ∀ A : Space →L[ℝ] Space, ‖A‖ ≤ Cg → ‖curlVec A‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space →L[ℝ] Space) Cg).exists_bound_of_continuousOn
    continuous_curlVec.continuousOn
  exact ⟨max K 0, le_max_right _ _, fun A hA => (hK A (by
    simpa [Metric.mem_closedBall, dist_zero_right] using hA)).trans (le_max_left _ _)⟩

theorem periodLIntegral_tendsto_zero {f : ℕ → ℝ → Space → Space}
    (hc : ∀ m, Continuous (fun z : ℝ × Space => f m z.1 z.2)) {R C : ℝ}
    (hs : ∀ m σ y, R < ‖y‖ → f m σ y = 0) (hb : ∀ m σ y, ‖f m σ y‖ ≤ C)
    (hl : ∀ σ y, Filter.Tendsto (fun m => f m σ y) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => periodLIntegral (fun σ y => ‖f m σ y‖ ^ 2)) Filter.atTop (nhds 0) := by
  have e : ∀ m, periodLIntegral (fun σ y => ‖f m σ y‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖f m z.1 z.2‖ ^ 2) ∂slab :=
    fun m => Coercive.ModeL2Internal.periodLIntegral_eq_slab _ ((hc m).norm.pow 2).aestronglyMeasurable
  simp_rw [e]
  set S : Set (ℝ × Space) := Set.univ ×ˢ Metric.closedBall (0 : Space) R with hS
  have hSm : MeasurableSet S := MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet
  have hlim : Filter.Tendsto (fun m => ∫⁻ z, ENNReal.ofReal (‖f m z.1 z.2‖ ^ 2) ∂slab) Filter.atTop
      (nhds (∫⁻ _z, (0 : ℝ≥0∞) ∂slab)) := by
    refine tendsto_lintegral_of_dominated_convergence (S.indicator (fun _ => ENNReal.ofReal (C ^ 2)))
      (fun m => ((hc m).norm.pow 2).measurable.ennreal_ofReal) (fun m => ae_of_all _ fun z => ?_) ?_
      (ae_of_all _ fun z => ?_)
    · show ENNReal.ofReal (‖f m z.1 z.2‖ ^ 2) ≤ S.indicator (fun _ => ENNReal.ofReal (C ^ 2)) z
      by_cases hz : ‖z.2‖ ≤ R
      · have hzS : z ∈ S := ⟨trivial, by simpa [Metric.mem_closedBall, dist_zero_right] using hz⟩
        rw [Set.indicator_of_mem hzS]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb m z.1 z.2) 2)
      · rw [hs m z.1 z.2 (lt_of_not_ge hz)]
        simp
    · rw [lintegral_indicator_const hSm, hS, Measure.prod_prod]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ measure_closedBall_lt_top.ne)
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · have h1 := ((continuous_norm.tendsto 0).comp (hl z.1 z.2)).pow 2
      have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
      simpa [Function.comp_def] using h2
  simpa using hlim

theorem smoothed_tendsto {ψ : ℝ → Space → Space} (hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (σ : ℝ) (y : Space) : Filter.Tendsto (fun m => smoothed ψ m σ y) Filter.atTop (nhds (ψ σ y)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous rOut_tendsto hc (σ, y)

theorem smoothed_fderiv_tendsto {ψ : ℝ → Space → Space} (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2))
    {C Cg : ℝ} (hC : ∀ σ y, ‖ψ σ y‖ ≤ C) (hCg : ∀ σ y, ‖gradField ψ σ y‖ ≤ Cg) (σ : ℝ) (y : Space) :
    Filter.Tendsto (fun m => fderiv ℝ (smoothed ψ m σ) y) Filter.atTop (nhds (gradField ψ σ y)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) rOut_tendsto
    (gradField_continuous hψ) (σ, y)
  refine h.congr fun m => ?_
  rw [smoothed_fderiv hψ hC hCg m σ y, convolution_def]
  rfl


def epsWeight {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ∑ β : Fin nE, PieceWeights.sgn (w.epsP β).modes ι * (w.epsP β).wt y

def muWeight {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ∑ β : Fin nM, PieceWeights.sgn (w.muP β).modes ι * (w.muP β).wt y

def curlOf (X : ℝ → Space → Space) : ℝ → Space → Space := fun σ y => curlVec (fderiv ℝ (X σ) y)

def gradCurl (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ → Space → Space := fun σ y => curlVec (G σ y)

def modeIntegral {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (X : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    ((∑ β : Fin nE, (Complex.I * ((PieceWeights.sgn (w.epsP β).modes ι * (w.epsP β).wt y : ℝ) : ℂ)
        * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField X) σ y))).re)
      + ∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (w.muP β).modes ι * (w.muP β).wt y : ℝ) : ℂ)
        * cdot (modeVel ι v σ y) (modeVel ι X σ y)).re)

theorem multiplierRight_eq {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (X : ℝ → Space → Space) :
    multiplierRight w v G H X
      = periodPairing (fun σ y => -secondDerivTrace (H σ y)) X + ∑' ι, modeIntegral w v G X ι := rfl

theorem abs_sgn_le (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : |PieceWeights.sgn T ι| ≤ 1 := by
  unfold PieceWeights.sgn
  split_ifs <;> norm_num

section Weights

variable {C : Type} {nE nM : ℕ} {w : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {wt : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}

theorem epsWeight_abs_le (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio)
    (ι : ℤ × ℤ) (y : Space) : |epsWeight w ι y| ≤ epsSup := by
  unfold epsWeight
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun β _ => ?_).trans (hw.eps_sum_le y))
  rw [abs_mul, abs_of_nonneg (hw.eps_wt_nonneg β y)]
  exact mul_le_of_le_one_left (hw.eps_wt_nonneg β y) (abs_sgn_le _ _)

theorem muWeight_bound (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio) :
    ∃ B, ∀ ι y, |muWeight w ι y| ≤ B := by
  obtain ⟨B, hB⟩ := hw.mu_decay
  refine ⟨∑ _β : Fin nM, B, fun ι y => ?_⟩
  unfold muWeight
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [abs_mul, abs_of_nonneg (hw.mu_wt_nonneg β y)]
  exact (mul_le_of_le_one_left (hw.mu_wt_nonneg β y) (abs_sgn_le _ _)).trans (hB β y).1

theorem epsWeight_measurable (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio)
    (ι : ℤ × ℤ) : Measurable (epsWeight w ι) := by
  have hc : Continuous (epsWeight w ι) := by
    unfold epsWeight
    exact continuous_finsetSum _ fun β _ => continuous_const.mul (hw.eps_increment β).choose_spec.continuous
  exact hc.measurable

theorem muWeight_measurable (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio)
    (ι : ℤ × ℤ) : Measurable (muWeight w ι) := by
  have hc : Continuous (muWeight w ι) := by
    unfold muWeight
    exact continuous_finsetSum _ fun β _ => continuous_const.mul (hw.mu_increment β).choose_spec.continuous
  exact hc.measurable

end Weights

theorem gradCurl_square {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) : IsSquareField (gradCurl G) := by
  refine ⟨continuous_curlVec.comp_aestronglyMeasurable hv.measurable_gradient, fun σ y => ?_, ?_⟩
  · show curlVec (G (σ + 1) y) = curlVec (G σ y)
    rw [hv.periodic_gradient σ y]
  · show periodLIntegral (fun σ y => ‖curlVec (G σ y)‖ ^ 2) < ⊤
    rw [Coercive.periodLIntegral_curlVec_sq_eq hv]
    exact hv.gradient_finite

theorem ballPart_square {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (R : ℝ) :
    IsSquareField (Coercive.Internal.FieldModes.ballPart R v) := by
  have hb := Coercive.Internal.FieldModes.isSquareField_ballPart
    Coercive.perturbationLocalSquareIntegrabilityHolds_proof hv R
  exact ⟨hb.1, hb.2.1, hb.2.2⟩

theorem re_sum_weight {n : ℕ} (c : Fin n → ℝ) (Z : ℂ) :
    ∑ β, (Complex.I * ((c β : ℝ) : ℂ) * Z).re = (Complex.I * ((∑ β, c β : ℝ) : ℂ) * Z).re := by
  rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]


section ModeSums

variable {C : Type} {nE nM : ℕ} {w : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {wt : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}
  {Γ : Set Symmetry} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}

theorem modeIntegral_eq (hPars : Coercive.ModeSquareSumHolds)
    (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio)
    (hv : IsPerturbation Γ P v G H g) {X : ℝ → Space → Space}
    (hX : ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2)) (hXp : IsTimePeriodic X) {R : ℝ}
    (hXs : ∀ σ y, R < ‖y‖ → X σ y = 0) (ι : ℤ × ℤ) :
    modeIntegral w v G X ι = weightedModeTerm (epsWeight w) (gradCurl G) (curlOf X) ι
      + weightedModeTerm (muWeight w) (Coercive.Internal.FieldModes.ballPart R v) X ι := by
  obtain ⟨BM, hBM⟩ := muWeight_bound hw
  have hU1 := gradCurl_square hv
  have hU2 := ballPart_square hv R
  have hX1 : IsSquareField (curlOf X) := Coercive.PairingSplitInternal.curl_square hX hXp ⟨R, hXs⟩
  have hX2 : IsSquareField X := Coercive.ModeL2Internal.isSquareField_of_continuous hX.continuous hXp ⟨R, hXs⟩
  have i1 := Coercive.ModeL2Internal.integrable_weightedMode hPars (epsWeight w) (epsWeight_measurable hw)
    (epsWeight_abs_le hw) hU1 hX1 ι
  have i2 := Coercive.ModeL2Internal.integrable_weightedMode hPars (muWeight w) (muWeight_measurable hw)
    hBM hU2 hX2 ι
  have hae : (fun z : ℝ × Space =>
      (∑ β : Fin nE, (Complex.I * ((PieceWeights.sgn (w.epsP β).modes ι * (w.epsP β).wt z.2 : ℝ) : ℂ)
        * cdot (curlOfGrad (modeGrad ι G z.1 z.2)) (curlOfGrad (modeGrad ι (gradField X) z.1 z.2))).re)
      + ∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (w.muP β).modes ι * (w.muP β).wt z.2 : ℝ) : ℂ)
        * cdot (modeVel ι v z.1 z.2) (modeVel ι X z.1 z.2)).re) =ᵐ[slab]
      fun z => (Complex.I * (epsWeight w ι z.2 : ℂ)
          * cdot (modeVel ι (gradCurl G) z.1 z.2) (modeVel ι (curlOf X) z.1 z.2)).re
        + (Complex.I * (muWeight w ι z.2 : ℂ)
          * cdot (modeVel ι (Coercive.Internal.FieldModes.ballPart R v) z.1 z.2) (modeVel ι X z.1 z.2)).re := by
    filter_upwards [Coercive.ModeL2Internal.slab_ac.ae_le (Coercive.ae_curlOfGrad_modeGrad hv ι)] with z hz
    have hmv : cdot (modeVel ι v z.1 z.2) (modeVel ι X z.1 z.2)
        = cdot (modeVel ι (Coercive.Internal.FieldModes.ballPart R v) z.1 z.2) (modeVel ι X z.1 z.2) := by
      by_cases hy : ‖z.2‖ ≤ R
      · rw [Coercive.Internal.FieldModes.modeVel_ballPart v ι z.1 hy]
      · rw [Coercive.Internal.FieldModes.modeVel_eq_zero hXs ι z.1 (lt_of_not_ge hy)]
        simp [cdot]
    rw [hz, Coercive.PairingSplitInternal.curlOfGrad_modeGrad hX ι z.1 z.2, hmv,
      re_sum_weight (fun β => PieceWeights.sgn (w.epsP β).modes ι * (w.epsP β).wt z.2),
      re_sum_weight (fun β => PieceWeights.sgn (w.muP β).modes ι * (w.muP β).wt z.2)]
    rfl
  have hI := (i1.add i2).congr hae.symm
  unfold modeIntegral
  rw [Coercive.ModeL2Internal.weightedModeTerm_eq hPars _ (epsWeight_measurable hw) (epsWeight_abs_le hw) hU1 hX1,
    Coercive.ModeL2Internal.weightedModeTerm_eq hPars _ (muWeight_measurable hw) hBM hU2 hX2,
    ← integral_add i1 i2, ← integral_congr_ae hae]
  exact (integral_prod _ hI).symm


theorem modeSum_tendsto (hPars : Coercive.ModeSquareSumHolds)
    (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio)
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} {ψs : ℕ → ℝ → Space → Space}
    (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2)) (hψp : IsTimePeriodic ψ) {R : ℝ}
    (hψs : ∀ σ y, R < ‖y‖ → ψ σ y = 0)
    (hn : ∀ m, ContDiff ℝ 1 (fun z : ℝ × Space => ψs m z.1 z.2)) (hnp : ∀ m, IsTimePeriodic (ψs m))
    (hns : ∀ m σ y, R < ‖y‖ → ψs m σ y = 0)
    (h1 : Filter.Tendsto (fun m => periodLIntegral (fun σ y => ‖ψs m σ y - ψ σ y‖ ^ 2)) Filter.atTop (nhds 0))
    (h2 : Filter.Tendsto (fun m => periodLIntegral (fun σ y => ‖curlOf (ψs m) σ y - curlOf ψ σ y‖ ^ 2))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => ∑' ι, modeIntegral w v G (ψs m) ι) Filter.atTop
      (nhds (∑' ι, modeIntegral w v G ψ ι)) := by
  obtain ⟨BM, hBM⟩ := muWeight_bound hw
  obtain ⟨K1, hK1⟩ := Coercive.ModeL2Internal.weightedMode_bound hPars (epsWeight w) (epsWeight_measurable hw)
    (epsWeight_abs_le hw) (gradCurl_square hv)
  obtain ⟨K2, hK2⟩ := Coercive.ModeL2Internal.weightedMode_bound hPars (muWeight w) (muWeight_measurable hw)
    hBM (ballPart_square hv R)
  have c1 : ∀ m, IsSquareField (curlOf (ψs m)) := fun m =>
    Coercive.PairingSplitInternal.curl_square (hn m) (hnp m) ⟨R, hns m⟩
  have c1' : IsSquareField (curlOf ψ) := Coercive.PairingSplitInternal.curl_square hψ hψp ⟨R, hψs⟩
  have c2 : ∀ m, IsSquareField (ψs m) := fun m =>
    Coercive.ModeL2Internal.isSquareField_of_continuous (hn m).continuous (hnp m) ⟨R, hns m⟩
  have c2' : IsSquareField ψ := Coercive.ModeL2Internal.isSquareField_of_continuous hψ.continuous hψp ⟨R, hψs⟩
  have ea : ∀ m ι, modeIntegral w v G (ψs m) ι
      = weightedModeTerm (epsWeight w) (gradCurl G) (curlOf (ψs m)) ι
        + weightedModeTerm (muWeight w) (Coercive.Internal.FieldModes.ballPart R v) (ψs m) ι :=
    fun m ι => modeIntegral_eq hPars hw hv (hn m) (hnp m) (hns m) ι
  have ec : ∀ ι, modeIntegral w v G ψ ι
      = weightedModeTerm (epsWeight w) (gradCurl G) (curlOf ψ) ι
        + weightedModeTerm (muWeight w) (Coercive.Internal.FieldModes.ballPart R v) ψ ι :=
    fun ι => modeIntegral_eq hPars hw hv hψ hψp hψs ι
  simp_rw [ea, ec]
  have hpt : ∀ a1 a2 c1 c2 : ℝ, |(a1 + a2) - (c1 + c2)| ≤ |a1 - c1| + |a2 - c2| := fun a1 a2 c1 c2 => by
    rw [show (a1 + a2) - (c1 + c2) = (a1 - c1) + (a2 - c2) by ring]
    exact abs_add_le _ _
  refine Coercive.PairingSplitInternal.tsum_tendsto_of_bound
    (g := fun m => K1 * Real.sqrt (periodLIntegral (fun σ y => ‖curlOf (ψs m) σ y - curlOf ψ σ y‖ ^ 2)).toReal
      + K2 * Real.sqrt (periodLIntegral (fun σ y => ‖ψs m σ y - ψ σ y‖ ^ 2)).toReal)
    (fun m => (hK1 _ _ (c1 m) c1').1.add (hK2 _ _ (c2 m) c2').1)
    ((hK1 _ _ c1' c1').1.add (hK2 _ _ c2' c2').1) (fun m => ?_) (fun m => ?_) ?_
  · exact Summable.of_nonneg_of_le (fun ι => abs_nonneg _) (fun ι => hpt _ _ _ _)
      ((hK1 _ _ (c1 m) c1').2.1.add (hK2 _ _ (c2 m) c2').2.1)
  · have s1 := (hK1 _ _ (c1 m) c1').2.1
    have s2 := (hK2 _ _ (c2 m) c2').2.1
    refine ((Summable.of_nonneg_of_le (fun ι => abs_nonneg _) (fun ι => hpt _ _ _ _) (s1.add s2)).tsum_le_tsum
      (fun ι => hpt _ _ _ _) (s1.add s2)).trans ?_
    rw [s1.tsum_add s2]
    exact add_le_add (hK1 _ _ (c1 m) c1').2.2 (hK2 _ _ (c2 m) c2').2.2
  · have t := ((Coercive.PairingSplitInternal.sqrt_toReal_tendsto h2).const_mul K1).add
      ((Coercive.PairingSplitInternal.sqrt_toReal_tendsto h1).const_mul K2)
    simpa using t

end ModeSums

end Internal.ActuatorPairingDensity

open Internal.ActuatorPairingDensity in
theorem multiplierField_pairing_of_solenoidal {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (wt : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) {w₀ epsSup epsGradSup ratio : ℝ}
    (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (M : ℝ → Space → Space)
    (hM : w.IsMultiplierField v G H M) (ψ : ℝ → Space → Space)
    (hψ : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2)) (hper : IsTimePeriodic ψ)
    (hsupp : ∃ R, ∀ σ y, R < ‖y‖ → ψ σ y = 0) (hdiv : ∀ σ y, divergenceAt (ψ σ) y = 0) :
    periodPairing ψ M = multiplierRight w v G H ψ := by
  obtain ⟨R, hR⟩ := hsupp
  have hPars := Coercive.modeSquareSumHolds_of Coercive.torusSquareSumHolds_proof Coercive.axialRotationHolds_proof
  obtain ⟨C0, -, hC⟩ := exists_bound_of_periodic hψ.continuous hper hR
  obtain ⟨Cg, -, hCg⟩ := exists_bound_of_periodic (gradField_continuous hψ)
    (Coercive.Internal.FieldModes.gradField_periodic hper) (Coercive.Internal.FieldModes.gradField_eq_zero hR)
  obtain ⟨Kc, -, hKc⟩ := curlVec_bound Cg
  have hT : ∀ m, IsPeriodicTestField (smoothed ψ m) := smoothed_testField hψ hper hR hC hCg hdiv
  have hT1 : ∀ m, ContDiff ℝ 1 (fun z : ℝ × Space => smoothed ψ m z.1 z.2) := fun m =>
    (hT m).1.of_le (by norm_cast)
  have hfar : ∀ m σ y, R + 1 < ‖y‖ → smoothed ψ m σ y = 0 := smoothed_far hR
  have hR1 : ∀ σ y, R + 1 < ‖y‖ → ψ σ y = 0 := fun σ y hy => hR σ y (by linarith)
  have h1 : Filter.Tendsto (fun m => periodLIntegral (fun σ y => ‖smoothed ψ m σ y - ψ σ y‖ ^ 2))
      Filter.atTop (nhds 0) := by
    refine periodLIntegral_tendsto_zero (R := R + 1) (C := C0 + C0)
      (fun m => (hT m).1.continuous.sub hψ.continuous) (fun m σ y hy => ?_) (fun m σ y => ?_) (fun σ y => ?_)
    · show smoothed ψ m σ y - ψ σ y = 0
      rw [hfar m σ y hy, hR1 σ y hy, sub_zero]
    · show ‖smoothed ψ m σ y - ψ σ y‖ ≤ C0 + C0
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hC σ y))
      rw [smoothed_eq]
      exact norm_kernel_integral_le m (fun z => hC z.1 z.2) (σ, y)
    · show Filter.Tendsto (fun m => smoothed ψ m σ y - ψ σ y) Filter.atTop (nhds 0)
      simpa using (smoothed_tendsto hψ.continuous σ y).sub_const (ψ σ y)
  have h2 : Filter.Tendsto (fun m => periodLIntegral (fun σ y => ‖curlOf (smoothed ψ m) σ y - curlOf ψ σ y‖ ^ 2))
      Filter.atTop (nhds 0) := by
    refine periodLIntegral_tendsto_zero (R := R + 1) (C := Kc + Kc)
      (fun m => (Coercive.PairingSplitInternal.continuous_curl (hT1 m)).sub
        (Coercive.PairingSplitInternal.continuous_curl hψ)) (fun m σ y hy => ?_) (fun m σ y => ?_) (fun σ y => ?_)
    · show curlVec (fderiv ℝ (smoothed ψ m σ) y) - curlVec (fderiv ℝ (ψ σ) y) = 0
      rw [Coercive.PairingSplitInternal.fderiv_eq_zero_far (hfar m σ) hy,
        Coercive.PairingSplitInternal.fderiv_eq_zero_far (hR1 σ) hy, sub_self]
    · show ‖curlVec (fderiv ℝ (smoothed ψ m σ) y) - curlVec (fderiv ℝ (ψ σ) y)‖ ≤ Kc + Kc
      refine (norm_sub_le _ _).trans (add_le_add (hKc _ ?_) (hKc _ (hCg σ y)))
      rw [smoothed_fderiv hψ hC hCg m σ y]
      exact norm_kernel_integral_le m (fun z => hCg z.1 z.2) (σ, y)
    · show Filter.Tendsto (fun m => curlVec (fderiv ℝ (smoothed ψ m σ) y) - curlVec (fderiv ℝ (ψ σ) y))
        Filter.atTop (nhds 0)
      have t := ((continuous_curlVec.tendsto _).comp (smoothed_fderiv_tendsto hψ hC hCg σ y)).sub_const
        (curlVec (gradField ψ σ y))
      simpa [Function.comp_def, gradField] using t
  have hMs : Coercive.ModeL2Internal.IsSquareField M := ⟨hM.1, hM.2.1, hM.2.2.1⟩
  have hψsq : Coercive.ModeL2Internal.IsSquareField ψ := Coercive.ModeL2Internal.isSquareField_of_continuous hψ.continuous hper ⟨R, hR⟩
  have hψmsq : ∀ m, Coercive.ModeL2Internal.IsSquareField (smoothed ψ m) := fun m =>
    Coercive.ModeL2Internal.isSquareField_of_continuous (hT m).1.continuous (hT m).2.1 ⟨R + 1, hfar m⟩
  have hHs : Coercive.ModeL2Internal.IsSquareField (fun σ y => -secondDerivTrace (H σ y)) := by
    refine ⟨(continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv).neg, fun σ y => ?_, ?_⟩
    · show -secondDerivTrace (H (σ + 1) y) = -secondDerivTrace (H σ y)
      rw [hv.periodic_secondDeriv σ y]
    · simpa only [norm_neg] using hv.sumSecondPartials_finite
  have t1 := Coercive.PairingSplitInternal.pairing_tendsto hMs hψsq hψmsq h1
  have t2 := Coercive.PairingSplitInternal.pairing_tendsto hHs hψsq hψmsq h1
  have t3 := modeSum_tendsto hPars hw hv hψ hper hR1 hT1 (fun m => (hT m).2.1) hfar h1 h2
  have t4 : Filter.Tendsto (fun m => periodPairing M (smoothed ψ m)) Filter.atTop
      (nhds (multiplierRight w v G H ψ)) := by
    rw [multiplierRight_eq]
    refine (t2.add t3).congr fun m => ?_
    rw [← multiplierRight_eq]
    exact (hM.2.2.2.2 _ (hT m)).symm
  rw [Coercive.PairingSplitInternal.pairing_comm hψsq hMs]
  exact tendsto_nhds_unique t1 t4

end CertCell

end Breakdown
